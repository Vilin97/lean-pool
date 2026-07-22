"""Static exposition-site generator for the Lean Pool.

Turns the extractor dump (JSONL, one line per human-written declaration)
into the static site described in ``SCHEMA.md``: per-project data shards
with layered dependency layouts, a pool-wide index, an all-declarations
index, and instantiated per-project pages.
"""
