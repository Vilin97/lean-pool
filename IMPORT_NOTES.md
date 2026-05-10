# Import notes — OSforGFF

Source: <https://github.com/mrdouglasny/OSforGFF> (Osterwalder–Schrader axioms for the
massive Gaussian Free Field in 4 dimensions, Lean 4 / Mathlib).

## What was vendored

The source repository depends on three external Lean libraries that lean-pool does not carry as
dependencies (and `lakefile.toml` may not be modified to add them), so all of them were vendored
under `LeanPool/OSforGFF/`:

- `OSforGFF/**` (47 files) → `LeanPool/OSforGFF/**` (module path `LeanPool.OSforGFF.…`).
- `bochner` (the `BochnerMinlos` package, rev `1b56973`) — the `Minlos` and `Bochner` libraries
  → `LeanPool/OSforGFF/Minlos/**`, `LeanPool/OSforGFF/Bochner/**`.
- `gaussian-field` (the `GaussianField` package, rev `24b26ef`) — only the transitive closure of
  `SchwartzNuclear.HermiteNuclear` and `Nuclear.NuclearSpace` (10 files)
  → `LeanPool/OSforGFF/GaussianField/Nuclear/**`, `LeanPool/OSforGFF/GaussianField/SchwartzNuclear/**`.
- `kolmogorov_extension4` (rev `5ba9202`, the pre-module-system version pinned by both `bochner`
  and `OSforGFF`) → `LeanPool/OSforGFF/KolmogorovExtension4/**`.

All four projects are Apache-2.0 (compatible with lean-pool). File headers rewritten to the
lean-pool four-line format (year 2026, upstream authors); `set_option` directives and diagnostic
commands stripped; internal imports remapped to `LeanPool.OSforGFF.…`; directory index files added;
`LeanPool/projects.yml` gained an `osforgff` entry; `LeanPool.lean` regenerated via `mk_all`.

## v4.30.0-rc2 bump notes

The source was on `leanprover/lean4:v4.29.0`; bumped to lean-pool's `v4.30.0-rc2`. Notable fixes:

- `Mathlib.Topology.Algebra.Module.WeakDual` moved to `Mathlib.Topology.Algebra.Module.Spaces.WeakDual`.
- New doc-string rules: content must not directly abut `/--`/`-/` (single space/newline required).
- `LinearPMap.mkSpanSingleton` needs an explicit `→ₗ.[ℝ]` type ascription in `Nuclear/NuclearSpace.lean`.
- All `set_option maxHeartbeats N in` directives were removed; the proofs that genuinely needed more
  were split into smaller lemmas (`L2_process_covariance_fubini_integrable` in `L2TimeIntegral.lean`,
  `bochner_theorem` in `Bochner/Main.lean`).
- Two proofs that upstream guarded with `set_option backward.isDefEq.respectTransparency false in`
  (`bochner_theorem`'s `bochner_mem_tight` step and `charFun_eq_GJGeneratingFunctional` in
  `Measure/Construct.lean`) were restructured to avoid the slow `isDefEq` (split the anonymous
  constructor against `Set` membership into per-component `refine ⟨…, ?_, ?_, …⟩` goals after
  `rw [Set.mem_setOf_eq]`; replaced `simp`/`congr` chains with explicit rewrites).
