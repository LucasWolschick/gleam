## On-demand, query-based code generation with delayed codegen.

1) Visit the AST on-demand, and not all at once. Whenever an entity is referenced that's not defined yet, visit the corresponding source tree, generate and return result. Do this query-based (lookup name in module, compile definition, etc etc).
2) Dump all indices; indices are an implementation detail. Use a slab allocator or something of the sort and keep references.
3) Generate a proto-Wasm IR. Something fully in-memory, close to Wasm but with high-level aspects. Something that lets me reference functions and types by type instead of index. Translation to Wasm => Take proto-Wasm and replace references by indices. Define an adequate level of abstraction; global minimum of complexity on either side of the IR.
4) Abandon completely three-pass approach. There should be one pass (get Wasm from program).

Try to sketch out an architecture for this.