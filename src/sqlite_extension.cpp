#ifndef DUCKDB_BUILD_LOADABLE_EXTENSION
#define DUCKDB_BUILD_LOADABLE_EXTENSION
#endif
#include "duckdb.hpp"

#include "sqlite_scanner.hpp"
#include "sqlite_storage.hpp"
#include "sqlite_scanner_extension.hpp"

#include "duckdb/catalog/catalog.hpp"
#include "duckdb/main/extension_util.hpp"
#include "duckdb/parser/parsed_data/create_table_function_info.hpp"

using namespace duckdb;

extern "C" {

static void LoadInternal(DatabaseInstance &db) {
	SqliteScanFunction sqlite_fun;
	ExtensionUtil::RegisterFunction(db, sqlite_fun);

	SqliteAttachFunction attach_func;
	ExtensionUtil::RegisterFunction(db, attach_func);

	auto &config = DBConfig::GetConfig(db);
	config.AddExtensionOption("sqlite_all_varchar", "Load all SQLite columns as VARCHAR columns", LogicalType::BOOLEAN);
	config.AddExtensionOption("sqlite_disqualify_rowid_index", "Disqualify using the ROWID index when loading data", LogicalType::BOOLEAN);
	config.AddExtensionOption("sqlite_log_queries", "Log SQL queries to STDERR", LogicalType::BOOLEAN);

	config.storage_extensions["sqlite_scanner"] = make_uniq<SQLiteStorageExtension>();
}

void SqliteScannerExtension::Load(DuckDB &db) {
	LoadInternal(*db.instance);
}

DUCKDB_EXTENSION_API void sqlite_scanner_init(duckdb::DatabaseInstance &db) {
	LoadInternal(db);
}

DUCKDB_EXTENSION_API const char *sqlite_scanner_version() {
	return DuckDB::LibraryVersion();
}

DUCKDB_EXTENSION_API void sqlite_scanner_storage_init(DBConfig &config) {
	config.storage_extensions["sqlite_scanner"] = make_uniq<SQLiteStorageExtension>();
}
}
