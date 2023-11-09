#include "duckdb.hpp"

#include "sqlite_constants.hpp"
#include "sqlite_db.hpp"
#include "sqlite_stmt.hpp"
#include "sqlite_scanner.hpp"
#include "sqlite_filter_pushdown.hpp"
#include <stdint.h>
#include "duckdb/parser/parser.hpp"
#include "duckdb/parser/expression/cast_expression.hpp"
#include "duckdb/common/types/date.hpp"
#include "duckdb/common/types/timestamp.hpp"
#include "duckdb/storage/table/row_group.hpp"
#include "duckdb/main/client_context.hpp"
#include "duckdb/main/config.hpp"
#include "duckdb/storage/storage_extension.hpp"
#include "duckdb/planner/expression/bound_operator_expression.hpp"
#include "duckdb/planner/expression/bound_constant_expression.hpp"
#include "duckdb/planner/operator/logical_get.hpp"

#include <cmath>
#include <iostream>
#if SQLITE_SCANNER_IN_FILTER_PUSHDOWN
#include <sstream>
#endif

namespace duckdb {

struct SqliteLocalState : public LocalTableFunctionState {
	SQLiteDB *db;
	SQLiteDB owned_db;
	SQLiteStatement stmt;
	bool done = false;
	vector<column_t> column_ids;
	optional_ptr<TableFilterSet> filters;
	bool disqualify_rowid_index;

	~SqliteLocalState() {
	}
};

struct SqliteGlobalState : public GlobalTableFunctionState {
	SqliteGlobalState(idx_t max_threads) : max_threads(max_threads) {
	}

	mutex lock;
	idx_t position = 0;
	idx_t max_threads;
	bool disqualify_rowid_index = false;
	bool log_queries = false;

	idx_t MaxThreads() const override {
		return max_threads;
	}
};

static unique_ptr<FunctionData> SqliteBind(ClientContext &context, TableFunctionBindInput &input,
                                           vector<LogicalType> &return_types, vector<string> &names) {

	auto result = make_uniq<SqliteBindData>();
	result->file_name = input.inputs[0].GetValue<string>();
	result->table_name = input.inputs[1].GetValue<string>();

	SQLiteDB db;
	SQLiteStatement stmt;
	db = SQLiteDB::Open(result->file_name);

	ColumnList columns;
	vector<unique_ptr<Constraint>> constraints;

	result->all_varchar = false;
	Value sqlite_all_varchar;
	if (context.TryGetCurrentSetting("sqlite_all_varchar", sqlite_all_varchar)) {
		result->all_varchar = BooleanValue::Get(sqlite_all_varchar);
	}
	db.GetTableInfo(result->table_name, columns, constraints, result->all_varchar);
	for (auto &column : columns.Logical()) {
		names.push_back(column.GetName());
		return_types.push_back(column.GetType());
	}

	if (names.empty()) {
		throw std::runtime_error("no columns for table " + result->table_name);
	}

	if (!db.GetMaxRowId(result->table_name, result->max_rowid)) {
		result->max_rowid = idx_t(-1);
		result->rows_per_group = idx_t(-1);
	}

	result->names = names;
	result->types = return_types;

	return std::move(result);
}

static void SqliteInitInternal(ClientContext &context, const SqliteBindData &bind_data, SqliteLocalState &local_state,
                               idx_t rowid_min, idx_t rowid_max, bool log_query) {
	D_ASSERT(rowid_min <= rowid_max);

	local_state.done = false;
	// we may have leftover statements or connections from a previous call to this
	// function
	local_state.stmt.Close();
	if (!local_state.db) {
		local_state.owned_db = SQLiteDB::Open(bind_data.file_name.c_str());
		local_state.db = &local_state.owned_db;
	}

	string filter_string;
	if (local_state.filters) {
		filter_string = SqliteFilterPushdown::TransformFilters(local_state.column_ids, local_state.filters, bind_data.names);
	}

#if SQLITE_SCANNER_IN_FILTER_PUSHDOWN
	for (auto &filter : bind_data.in_values_filters) {
		auto &values = filter->values;
		std::ostringstream stream;
        
        for (auto it = values->begin(); it != values->end(); ++it) {
            if (it != values->begin()) {
                stream << ",";
            }
            
            stream << static_cast<int64_t>(*it);
        }

		auto in_clause = StringUtil::Format("%s IN (%s)", bind_data.names[filter->column_index], stream.str());

		if (!filter_string.empty()) {
			filter_string += " AND ";
		}

		filter_string += in_clause;
	}
#endif

	auto col_names = StringUtil::Join(
	    local_state.column_ids.data(), local_state.column_ids.size(), ", ", [&](const idx_t column_id) {
		    return column_id == (column_t)-1 ? "ROWID"
		                                     : '"' + SQLiteUtils::SanitizeIdentifier(bind_data.names[column_id]) + '"';
	    });

	auto sql =
	    StringUtil::Format("SELECT %s FROM \"%s\"", col_names, SQLiteUtils::SanitizeIdentifier(bind_data.table_name));
	if (bind_data.rows_per_group != idx_t(-1)) {
		// we are scanning a subset of the rows - generate a WHERE clause based on
		// the rowid
		auto rowid = local_state.disqualify_rowid_index ? "+ROWID" : "ROWID";
		auto where_clause = StringUtil::Format(" WHERE %s BETWEEN %d AND %d", rowid, rowid_min, rowid_max);
		sql += where_clause;
		if (!filter_string.empty()) {
			sql += " AND " + filter_string;
		}
	} else {
		// we are scanning the entire table - no need for a WHERE clause
		D_ASSERT(rowid_min == 0);
		if (!filter_string.empty()) {
			sql += " WHERE " + filter_string;
		}
	}
	if (log_query) {
		std::cerr << sql << std::endl;
	}
	local_state.stmt = local_state.db->Prepare(sql.c_str());
}

#if SQLITE_SCANNER_IN_FILTER_PUSHDOWN
static bool PushdownFilter(unique_ptr<Expression> &filter, SqliteBindData &bind_data, vector<column_t> &column_ids)
{
	if (filter->type != ExpressionType::COMPARE_IN) {
		return false;
	}

	auto &func = filter->Cast<BoundOperatorExpression>();
	auto in_values = make_uniq<vector<hugeint_t>>();

	D_ASSERT(func.children.size() > 1);

	if (func.children[0]->expression_class != ExpressionClass::BOUND_COLUMN_REF) {
		return false;
	}

	auto &column_ref = func.children[0]->Cast<BoundColumnRefExpression>();
	auto column_index = column_ids[column_ref.binding.column_index];
	
	if (column_index == COLUMN_IDENTIFIER_ROW_ID) {
		return false;
	}
	
	//! check if all children are const expr
	bool children_constant = true;
	for (size_t i {1}; i < func.children.size(); i++) {
		if (func.children[i]->type != ExpressionType::VALUE_CONSTANT) {
			children_constant = false;
		}
	}
	
	if (!children_constant) {
		return false;
	}
	
	auto &fst_const_value_expr = func.children[1]->Cast<BoundConstantExpression>();
	auto &type = fst_const_value_expr.value.type();
	
	if (!type.IsIntegral()) {
		return false;
	}

	for (idx_t i = 1; i < func.children.size(); i++) {
		auto &const_value_expr = func.children[i]->Cast<BoundConstantExpression>();
		if (const_value_expr.value.IsNull()) {
			return false;
		}

		in_values->push_back(const_value_expr.value.GetValue<hugeint_t>());
	}

	if (in_values->empty()) {
		return false;
	}

	auto new_filter = make_uniq<SqliteInValuesFilter>(column_index, std::move(in_values));
	bind_data.in_values_filters.emplace_back(std::move(new_filter));
	return true;
} 

static void SqliteComplexFilterPushdown(ClientContext &context, LogicalGet &get, FunctionData *bind_data_p,
                                     vector<unique_ptr<Expression>> &filters) {
	auto &data = bind_data_p->Cast<SqliteBindData>();
	vector<unique_ptr<Expression>> pruned_filters;

	for (auto &filter : filters) {
		auto filter_copy = filter->Copy();

		if (!PushdownFilter(filter_copy, data, get.column_ids)) {
			pruned_filters.emplace_back(std::move(filter_copy));
		}
	}

	filters = std::move(pruned_filters);
}
#endif

static unique_ptr<NodeStatistics> SqliteCardinality(ClientContext &context, const FunctionData *bind_data_p) {
	D_ASSERT(bind_data_p);
	auto &bind_data = bind_data_p->Cast<SqliteBindData>();
	return make_uniq<NodeStatistics>(bind_data.max_rowid);
}

static idx_t SqliteMaxThreads(ClientContext &context, const FunctionData *bind_data_p) {
	D_ASSERT(bind_data_p);
	auto &bind_data = bind_data_p->Cast<SqliteBindData>();
	if (bind_data.global_db) {
		return 1;
	}
	return bind_data.max_rowid / bind_data.rows_per_group;
}

static bool SqliteParallelStateNext(ClientContext &context, const SqliteBindData &bind_data, SqliteLocalState &lstate,
                                    SqliteGlobalState &gstate) {
	lock_guard<mutex> parallel_lock(gstate.lock);
	if (gstate.position < bind_data.max_rowid) {
		auto start = gstate.position;
		auto end = start + bind_data.rows_per_group - 1;
		SqliteInitInternal(context, bind_data, lstate, start, end, gstate.log_queries);
		gstate.position = end + 1;
		return true;
	}
	return false;
}

static unique_ptr<LocalTableFunctionState>
SqliteInitLocalState(ExecutionContext &context, TableFunctionInitInput &input, GlobalTableFunctionState *global_state) {
	auto &bind_data = input.bind_data->Cast<SqliteBindData>();
	auto &gstate = global_state->Cast<SqliteGlobalState>();
	auto result = make_uniq<SqliteLocalState>();
	result->column_ids = input.column_ids;
	result->filters = input.filters;
	result->db = bind_data.global_db;
	result->disqualify_rowid_index = gstate.disqualify_rowid_index;
	if (!SqliteParallelStateNext(context.client, bind_data, *result, gstate)) {
		result->done = true;
	}
	return std::move(result);
}

static unique_ptr<GlobalTableFunctionState> SqliteInitGlobalState(ClientContext &context,
                                                                  TableFunctionInitInput &input) {
	auto result = make_uniq<SqliteGlobalState>(SqliteMaxThreads(context, input.bind_data.get()));
	result->position = 0;
	Value disqualify;
	if (context.TryGetCurrentSetting("sqlite_disqualify_rowid_index", disqualify)) {
		result->disqualify_rowid_index = BooleanValue::Get(disqualify);
	}
	else {
		result->disqualify_rowid_index = false;
	}
	Value log_queries;
	if (context.TryGetCurrentSetting("sqlite_log_queries", log_queries)) {
		result->log_queries = BooleanValue::Get(log_queries);
	}
	else {
		result->log_queries = false;
	}

	return std::move(result);
}

static void SqliteScan(ClientContext &context, TableFunctionInput &data, DataChunk &output) {
	auto &state = data.local_state->Cast<SqliteLocalState>();
	auto &gstate = data.global_state->Cast<SqliteGlobalState>();
	auto &bind_data = data.bind_data->Cast<SqliteBindData>();

	while (output.size() == 0) {
		if (state.done) {
			if (!SqliteParallelStateNext(context, bind_data, state, gstate)) {
				return;
			}
		}

		idx_t out_idx = 0;
		while (true) {
			if (out_idx == STANDARD_VECTOR_SIZE) {
				output.SetCardinality(out_idx);
				return;
			}
			auto &stmt = state.stmt;
			auto has_more = stmt.Step();
			if (!has_more) {
				state.done = true;
				output.SetCardinality(out_idx);
				break;
			}
			for (idx_t col_idx = 0; col_idx < output.ColumnCount(); col_idx++) {
				auto &out_vec = output.data[col_idx];
				auto sqlite_column_type = stmt.GetType(col_idx);
				if (sqlite_column_type == SQLITE_NULL) {
					auto &mask = FlatVector::Validity(out_vec);
					mask.Set(out_idx, false);
					continue;
				}

				auto val = stmt.GetValue<sqlite3_value *>(col_idx);
				switch (out_vec.GetType().id()) {
				case LogicalTypeId::BIGINT:
					stmt.CheckTypeMatches(bind_data, val, sqlite_column_type, SQLITE_INTEGER, col_idx);
					FlatVector::GetData<int64_t>(out_vec)[out_idx] = sqlite3_value_int64(val);
					break;
				case LogicalTypeId::DOUBLE:
					stmt.CheckTypeIsFloatOrInteger(val, sqlite_column_type, col_idx);
					FlatVector::GetData<double>(out_vec)[out_idx] = sqlite3_value_double(val);
					break;
				case LogicalTypeId::VARCHAR:
					stmt.CheckTypeMatches(bind_data, val, sqlite_column_type, SQLITE_TEXT, col_idx);
					FlatVector::GetData<string_t>(out_vec)[out_idx] = StringVector::AddString(
					    out_vec, (const char *)sqlite3_value_text(val), sqlite3_value_bytes(val));
					break;
				case LogicalTypeId::DATE:
					stmt.CheckTypeMatches(bind_data, val, sqlite_column_type, SQLITE_TEXT, col_idx);
					FlatVector::GetData<date_t>(out_vec)[out_idx] =
					    Date::FromCString((const char *)sqlite3_value_text(val), sqlite3_value_bytes(val));
					break;
				case LogicalTypeId::TIMESTAMP:
					stmt.CheckTypeMatches(bind_data, val, sqlite_column_type, SQLITE_TEXT, col_idx);
					FlatVector::GetData<timestamp_t>(out_vec)[out_idx] =
					    Timestamp::FromCString((const char *)sqlite3_value_text(val), sqlite3_value_bytes(val));
					break;
				case LogicalTypeId::BLOB:
					FlatVector::GetData<string_t>(out_vec)[out_idx] = StringVector::AddStringOrBlob(
					    out_vec, (const char *)sqlite3_value_blob(val), sqlite3_value_bytes(val));
					break;
				default:
					throw std::runtime_error(out_vec.GetType().ToString());
				}
			}
			out_idx++;
		}
	}
}

static string SqliteToString(const FunctionData *bind_data_p) {
	D_ASSERT(bind_data_p);
	auto &bind_data = bind_data_p->Cast<SqliteBindData>();
	return StringUtil::Format("%s:%s", bind_data.file_name, bind_data.table_name);
}

/*
static unique_ptr<BaseStatistics>
SqliteStatistics(ClientContext &context, const FunctionData *bind_data_p,
                 column_t column_index) {
  auto &bind_data = (SqliteBindData &)*bind_data_p;
  auto stats = BaseStatistics::CreateEmpty(bind_data.types[column_index]);
  stats->validity_stats =
      make_uniq<ValidityStatistics>(!bind_data.not_nulls[column_index]);
  return stats;
}
*/

SqliteScanFunction::SqliteScanFunction()
    : TableFunction("sqlite_scan", {LogicalType::VARCHAR, LogicalType::VARCHAR}, SqliteScan, SqliteBind,
                    SqliteInitGlobalState, SqliteInitLocalState) {
	cardinality = SqliteCardinality;
	to_string = SqliteToString;
#if SQLITE_SCANNER_IN_FILTER_PUSHDOWN
	pushdown_complex_filter = SqliteComplexFilterPushdown;
#endif
	projection_pushdown = true;
	filter_pushdown = true;
}

struct AttachFunctionData : public TableFunctionData {
	AttachFunctionData() {
	}

	bool finished = false;
	bool overwrite = false;
	string file_name = "";
};

static unique_ptr<FunctionData> AttachBind(ClientContext &context, TableFunctionBindInput &input,
                                           vector<LogicalType> &return_types, vector<string> &names) {

	auto result = make_uniq<AttachFunctionData>();
	result->file_name = input.inputs[0].GetValue<string>();

	for (auto &kv : input.named_parameters) {
		if (kv.first == "overwrite") {
			result->overwrite = BooleanValue::Get(kv.second);
		}
	}

	return_types.emplace_back(LogicalType::BOOLEAN);
	names.emplace_back("Success");
	return std::move(result);
}

static void AttachFunction(ClientContext &context, TableFunctionInput &data_p, DataChunk &output) {
	auto &data = data_p.bind_data->CastNoConst<AttachFunctionData>();
	if (data.finished) {
		return;
	}

	SQLiteDB db = SQLiteDB::Open(data.file_name);
	auto dconn = Connection(context.db->GetDatabase(context));
	{
		auto tables = db.GetTables();
		for (auto &table_name : tables) {
			dconn.TableFunction("sqlite_scan", {Value(data.file_name), Value(table_name)})
			    ->CreateView(table_name, data.overwrite, false);
		}
	}
	{
		SQLiteStatement stmt = db.Prepare("SELECT sql FROM sqlite_master WHERE type='view'");
		while (stmt.Step()) {
			auto view_sql = stmt.GetValue<string>(0);
			dconn.Query(view_sql);
		}
	}
	data.finished = true;
}

SqliteAttachFunction::SqliteAttachFunction()
    : TableFunction("sqlite_attach", {LogicalType::VARCHAR}, AttachFunction, AttachBind) {
	named_parameters["overwrite"] = LogicalType::BOOLEAN;
}

} // namespace duckdb
