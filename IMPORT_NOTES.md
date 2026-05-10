# Import notes: `kakeyafinitefields`

Vendored from <https://github.com/math-inc/KakeyaFiniteFields> into
`LeanPool/KakeyaFiniteFields/`.

## What was imported

- `KakeyaFiniteFields/Main.lean` → `LeanPool/KakeyaFiniteFields/Main.lean`,
  re-namespaced under `LeanPool.KakeyaFiniteFields`. This is the entire Lean
  development in the upstream repository (≈300 lines): the finite-field Kakeya
  lower bound, `LeanPool.KakeyaFiniteFields.kakeya_set_bound`, following the
  polynomial method (Dvir 2008).
- `KakeyaFiniteFields.lean` (the upstream entry point) → folded into
  `LeanPool/KakeyaFiniteFields.lean`, which also carries the generated project
  card and the mathematical overview.

The upstream `blueprint/` and `home_page/` directories are project tooling, not
Lean content, so they were not vendored.

## Changes made during the port

- Added the Lean Pool file header (Apache-2.0, 2026, Math Inc.).
- Replaced the upstream `import Mathlib` with the specific Mathlib modules used.
- Removed `set_option`s (they were in the upstream `lakefile.toml`, not the Lean
  file; lean-pool sets its package-wide options in `lakefile.toml`).
- Wrapped lines to satisfy the 100-character text-style linter and restructured
  the tail of `step4` so the wrapped term parses; the proof content is
  unchanged.
- Renamed the local lemma `coeff_top_eval₂_linear_hc_lt` to
  `coeff_top_eval_linear_hc_lt`: the repository quality tooling parses
  declaration names with an ASCII-only regex, and the subscript `₂` made it
  read a truncated, non-existent name.
- Ported from Lean `v4.26.0-rc2` to lean-pool's `v4.30.0-rc2` (no proof changes
  were needed for the Mathlib API drift).

No file depended on `sorry`, `admit`, a new `axiom`/`constant`, `unsafe`,
`partial`, `opaque`, or `@[extern]`; nothing was excluded.

## Licensing

**The upstream repository does not ship a `LICENSE` file**, and GitHub reports
no detected license for `math-inc/KakeyaFiniteFields`. The repository is
publicly published by Math Inc. as an AI-assisted formalization (their README
invites use and links to <https://www.math.inc/>), and the mathematics is Zeev
Dvir's 2008 theorem, but there is no explicit grant.

Lean Pool is Apache-2.0. The vendored files here carry an Apache-2.0 header
attributing Math Inc., consistent with how Lean Pool records provenance, but
this is **pending confirmation** that the upstream authors intend their code to
be redistributable under those terms. If Math Inc. objects or specifies an
incompatible license, this import should be removed.
