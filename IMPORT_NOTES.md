# Import notes — OSforGFF

Source: <https://github.com/mrdouglasny/OSforGFF> (Osterwalder–Schrader axioms for the
massive Gaussian Free Field in 4 dimensions, Lean 4 / Mathlib).

## What was vendored

The source repository depends on three external Lean libraries that lean-pool does not
carry as dependencies (and `lakefile.toml` may not be modified to add them), so all of
them were vendored under `LeanPool/OSforGFF/`:

- `OSforGFF/**` (47 files) → `LeanPool/OSforGFF/**` (module path `LeanPool.OSforGFF.…`).
- `bochner` (the `BochnerMinlos` package, rev `1b56973`) — the `Minlos` and `Bochner` libraries
  → `LeanPool/OSforGFF/Minlos/**`, `LeanPool/OSforGFF/Bochner/**`.
- `gaussian-field` (the `GaussianField` package, rev `24b26ef`) — only the transitive closure of
  `SchwartzNuclear.HermiteNuclear` and `Nuclear.NuclearSpace` (10 files) was vendored
  → `LeanPool/OSforGFF/GaussianField/Nuclear/**`, `LeanPool/OSforGFF/GaussianField/SchwartzNuclear/**`.
- `kolmogorov_extension4` (rev `5ba9202`, the pre-module-system version pinned by both
  `bochner` and `OSforGFF`) → `LeanPool/OSforGFF/KolmogorovExtension4/**`.

All four projects are Apache-2.0 (compatible with lean-pool); file headers were rewritten to the
lean-pool four-line format with year 2026 and the upstream authors; `set_option` directives and
diagnostic commands were stripped; internal imports were rewritten to the `LeanPool.OSforGFF.…`
namespace; the `Mathlib.Topology.Algebra.Module.WeakDual` import was updated to its v4.30 location
(`Mathlib.Topology.Algebra.Module.Spaces.WeakDual`). Import-only index files were added for every
directory and `LeanPool/projects.yml` gained an `osforgff` entry.

## Blocking issue (v4.30 bump): `isDefEq` timeout in `Bochner/Main.lean`

`LeanPool/OSforGFF/Bochner/Main.lean` fails to build under `leanprover/lean4:v4.30.0-rc2`. The
proof of Bochner's theorem (`bochner_theorem`, originally guarded by `set_option maxHeartbeats
400000 in` upstream) was split into several private lemmas (`bochner_mu_eps`, `bochner_charFun_eq`,
`bochner_mu_seq`, `bochner_mem_tight`, `bochner_S_tight`, `bochner_existence`). Most of those build,
but `bochner_mem_tight` (and the lemmas downstream of it) hit `(deterministic) timeout at isDefEq,
maximum number of heartbeats (200000)` even though the comparison in question is between
syntactically identical expressions involving `MeasureTheory.charFun` and `gaussianRegularize`.

Upstream avoids this exact class of slowdown with `set_option backward.isDefEq.respectTransparency
false in` (Mathlib does the same in `Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`,
and the OSforGFF source uses it in `OSforGFF/Measure/Construct.lean`). lean-pool forbids `set_option`
anywhere in committed files (and `lakefile.toml` may not be edited), so this workaround is
unavailable. I tried, without success: splitting the proof into ~7 lemmas; replacing
`Measurable.comp` with `fun_prop`; `Classical.indefiniteDescription`/`choose`-based construction;
`@[reducible]`/`@[irreducible]` on `gaussianRegularize`; explicit/implicit argument variations;
`change`/`show`/`refine` rewordings; eta-expansion of the offending term.

Because `Bochner/Main.lean` is imported (transitively) by `Minlos/*`, `Measure/*`, `OS/*` and the
master theorem `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms`, this blocks the whole library
from building. The same `backward.isDefEq.respectTransparency` issue is expected to recur in
`OSforGFF/Measure/Construct.lean` (`charFun_eq_GJGeneratingFunctional`) once the upstream blocker is
cleared.

## Other remaining work (not yet done because the build is blocked above)

- ~800 linter warnings (the `linter.style.*` / `linter.flexible` set is enforced for downstream
  files via `weak.linter.mathlibStandardSet`): long lines, `show` → `change`, flexible `simp`,
  `multiGoal`, `commandStart` whitespace, `push_neg` deprecation, `cases'`/`induction'`,
  `unusedSimpArgs`, and ~48 `unusedSectionVars` warnings introduced by removing
  `set_option linter.unusedSectionVars false`.
- ~12 further `set_option maxHeartbeats N in` proofs were stripped; only `L2TimeIntegral.lean`'s
  `L2_process_covariance_fubini_integrable` was confirmed fixed (by splitting and using `fun_prop`
  for the swap-coordinate measurability); the rest (in `General/HadamardExp.lean`,
  `Bochner/FejerPD.lean`, `GaussianField/SchwartzNuclear/HermiteFunctions.lean`,
  `HermiteTensorProduct.lean`, `SchwartzHermiteExpansion.lean`) were not reached by the build and
  may need similar splitting/optimisation.
- ~8 proof bodies exceed the 200-line cap (`quality.py`) and need to be split into lemmas.
- ~9 `def Foo.bar` declarations sit inside `namespace N` blocks, which breaks `quality.py`'s
  `#print axioms` audit; they need to be wrapped in a nested `namespace Foo`.
