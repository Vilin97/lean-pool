/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Finiteness.Schwartz
import LeanPool.JacobianDiffgeo.Finiteness.BddHolo
import LeanPool.JacobianDiffgeo.Finiteness.CompactRestrict
import LeanPool.JacobianDiffgeo.Finiteness.Chain
import LeanPool.JacobianDiffgeo.Finiteness.TradeBounded
import LeanPool.JacobianDiffgeo.Finiteness.H1Finite
import LeanPool.JacobianDiffgeo.Finiteness.Chi

/-!
# finiteness-and-chi: `FiniteDimensional H¹(X, O_D)` via Schwartz/Montel (namespace
`RS`/`RS.Finiteness`)

API summary (see `docs/design/finiteness-and-chi.md`). **Unit COMPLETE**: all 7 design files are
written, zero sorries, `scripts/check.sh Jacobian/Finiteness` passes. No file uses the
forbidden tactic.

* **`Schwartz.lean`** (namespace `RS`, pure Banach — zero project imports):
  `schwartz_finite_cospan` (the L. Schwartz perturbation lemma, cospan/span form: a compact
  perturbation of a surjective `CLM` between Banach spaces has finite-codimensional range),
  `finiteDimensional_of_cospan` (consumer wrapper), `FiniteDimensional.of_linearMap_ker_range`
  (finite-kernel + finite-codomain ⇒ finite domain — the extension helper reused everywhere
  downstream). Mirrors mathlib's own `ContinuousLinearMap.exists_preimage_norm_le` proof texture.

* **`BddHolo.lean`** (namespace `RS.Finiteness`): `BddHoloOn S` (bounded-holomorphic functions on
  `↥S` as a *closed* `Submodule` of `↥S →ᵇ ℂ` — `isClosed_bddHoloOn` via a chart-local
  uniform-limit argument, hence `CompleteSpace (BddHoloOn S)`), `restrictCLM` (norm `≤ 1`,
  presheaf law `restrictCLM_restrictCLM`), the germ bridges `toGerm`/`evalAt_toGerm`/
  `toGerm_restrict_comm` (germification into `LinSysOn 0`) and `restrictGerm`/
  `toGerm_restrictGerm`/`restrictGerm_toGerm` (de-germification via `holoRepr` on `S' ⋐ S`,
  `[T2Space X] [CompactSpace X]`).

* **`CompactRestrict.lean`**: `isCompactOperator_restrictCLM` — Montel's theorem: for
  `S' ⋐ S ⊆ source (chartAt ℂ x₀)`, `restrictCLM : BddHoloOn S → BddHoloOn S'` is a compact
  operator (built from `Jacobian/Forms/Montel.lean`'s `isCompact_closure_montelFamily`). Also
  `isCompactOperator_of_isCompactOperator_val` (Compat: a `CLM` into a *closed* submodule is
  compact once its ambient-valued composite is, via `Subtype.isCompact_iff`).

* **`Chain.lean`**: `ShrinkChain X` (Forster's `𝔚 ⋐ 𝔙 ⋐ 𝔘 ⋐ 𝔘*` same-index-set chain, D3) with
  `ShrinkChain.nonempty` (existence on `[T2Space X] [CompactSpace X]`), the four induced
  `Cech.FinCover ⊤`s (`coverStar`/`coverU`/`coverV`/`coverW`) and refinement facts
  (`good_star`, `ref_star_U`/`ref_star_V`/`ref_star_W`/`ref_U_V`/`ref_V_W`/`ref_U_W`, all `τ = id`);
  the Banach cochain layer at one level (`NC0`/`NC1`, `deltaCLM`, `NZ1` — bounded cocycles as a
  `ContinuousLinearMap.ker`, closed and complete for free — `resNC0`/`resNC1`/`resZ`, and the
  cocycle-relation workhorse `NZ1.rel_res`/`resNC1_mapsTo_NZ1`); and Forster's 14.6(b) Banach
  geometry: `tradeDefect` (the defect CLM on `Z¹(𝔘) × Z¹(𝔙) × C⁰(𝔚)`), `tradeSpace` (Forster's
  subspace `L` as its `ContinuousLinearMap.ker`, complete + normed instances registered),
  `mem_tradeSpace_iff`/`mem_tradeSpace_iff_eq`, and the two Schwartz-cospan projections
  `tradePi`/`tradeCompact`.

* **`TradeBounded.lean`** (the gated centerpiece): `isCompactOperator_resZ_UV`/
  `isCompactOperator_tradeCompact` (§4.4's finite-`Pi` Montel assembly, closing out `Chain.lean`'s
  deferred obligation); the Banach ↔ Čech germ bridges `toGermZ1`/`boundZ1`/`boundZ1C0` (D5,
  via `coverOfP` — a `rfl`-equal stand-in for `T.coverU`/`T.coverV`/`T.coverW` that sidesteps a
  hard `isDefEq` wall on nested `LinSysOn`/`MeroGermOn` ascriptions, see the file's docstrings on
  `starPairMem`/`starPairGerm`/`cC1`/`wPairMem` for the general pattern); `trade_evalAt` (the
  "repr_cocycle" pointwise evaluation of `exists_trade`'s conclusion); **`tradePi_surjective`**
  (Forster 14.6(a) upgraded to the Banach layer — the Schwartz surjectivity input); `classMap`
  (§5 step 8) with its two Schwartz-consumer properties `classMap_tradeDiff_eq_zero` and
  **`classMap_surjective`** (§5 step 9).

* **`H1Finite.lean`**: `finiteDimensional_h1Cover_W` (the Schwartz cospan assembly at a fixed
  `ShrinkChain`) ⇒ **`finiteDimensional_H1_zero`** (`FiniteDimensional ℂ (H1 (0 : Divisor X))`,
  Forster §14's headline) ⇒ **`finiteDimensional_H1`** (`FiniteDimensional ℂ (H1 D)` for ALL `D`,
  §7, via cech's six-term skyscraper fragment — decision D2, NOT twisted norms). Records the
  `addCommGroupH1` Compat instance (`AddCommGroup (H1 D)` does not resolve by plain
  `inferInstance` in this codebase — a documented cech gotcha; supplied explicitly via
  `Module.DirectLimit.addCommGroup`).

* **`Chi.lean`**: `finiteDimensional_linSys` (`FiniteDimensional ℂ (LinSys D)` for ALL `D`, same
  six-term recipe applied to `windowMap`); the χ ledger `h1 D`/`chi D := (l D : ℤ) − (h1 D : ℤ)`;
  `sixterm_ranks` (the shared rank-nullity bookkeeping); `chi_of_le`/`chi_single_add`/
  `chi_eq_chi_zero_add_degree` (the ledger identities); **`chi_zero_add_degree_le_l`**/
  **`exists_ne_zero_mem_linSys`** (the Riemann-inequality seed, exact names canonical-forms' §D9
  Existence gate consumes); `l_mono`/`l_le_l_add_degree`/`h1_le_of_le`/`h1_le_h1_add_degree`
  (monotonicity corollaries).
-/
