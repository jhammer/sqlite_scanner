//===----------------------------------------------------------------------===//
//                         DuckDB
//
// sqlite_scanner.hpp
//
//
//===----------------------------------------------------------------------===//

#pragma once

#include "duckdb.hpp"
#include "sqlite_constants.hpp"

namespace duckdb {
class SQLiteDB;

struct SqliteInValuesFilter {
	idx_t column_index;
	unique_ptr<vector<hugeint_t>> values;

	SqliteInValuesFilter(idx_t column_index, unique_ptr<vector<hugeint_t>> values) : column_index(column_index), values(std::move(values)) {
	}
};

struct SqliteBindData : public TableFunctionData {
	string file_name;
	string table_name;

	vector<string> names;
	vector<LogicalType> types;

	idx_t max_rowid = 0;
	bool all_varchar = false;
#if SQLITE_SCANNER_IN_FILTER_PUSHDOWN
	vector<unique_ptr<SqliteInValuesFilter>> in_values_filters;
#endif

	idx_t rows_per_group = 122880;
	SQLiteDB *global_db;
};

class SqliteScanFunction : public TableFunction {
public:
	SqliteScanFunction();
};

class SqliteAttachFunction : public TableFunction {
public:
	SqliteAttachFunction();
};

} // namespace duckdb
