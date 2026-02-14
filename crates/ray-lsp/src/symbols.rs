// Legacy symbol resolution module — removed.
//
// Symbol resolution is now handled by queries in ray-frontend:
// - `symbol_targets(db, node_id)` for go-to-definition targets
// - `find_at_position(db, file_id, line, col)` for position lookup
