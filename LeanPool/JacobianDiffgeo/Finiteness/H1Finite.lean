/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Finiteness.Schwartz
import LeanPool.JacobianDiffgeo.Finiteness.TradeBounded
import LeanPool.JacobianDiffgeo.Cech.SixTerm

/-!
# `FiniteDimensional ℂ (H1 D)` for all `D` (`finiteness-and-chi`, gated file 2/3)

Unit: finiteness-and-chi (`docs/design/finiteness-and-chi.md` §6.4/§6.5, §7).

* `toH1_coverW_surjective`: every `H1 (0 : Divisor X)`-class has a `T.coverW`-level
  representative (Leray at the good cover `T.coverStar`, pushed down along `T.ref_star_W`).
* `finiteDimensional_h1Cover_W`: `H1Cover 0 T.coverW` is finite-dimensional — the Schwartz
  cospan assembly (§6.5), consuming `TradeBounded.lean`'s `tradePi_surjective`,
  `isCompactOperator_tradeCompact`, `classMap_tradeDiff_eq_zero`, `classMap_surjective`.
* `finiteDimensional_H1_zero`: **the unit's headline instance**, `FiniteDimensional ℂ
  (H1 (0 : Divisor X))`.
* `finiteDimensional_H1`: `FiniteDimensional ℂ (H1 D)` for ALL `D` (§7, decision D2 — via
  cech's six-term skyscraper fragment, NOT twisted norms).
-/

open scoped ContDiff Manifold BoundedContinuousFunction
open Set Filter Topology TopologicalSpace Metric RS.Cech

namespace RS.Finiteness

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable [T1Space X] [T2Space X] [CompactSpace X]

/-! ### §6.5: assembly at a fixed `ShrinkChain` -/

omit [T1Space X] in
/-- Every `H1 (0 : Divisor X)`-class already has a representative on `T.coverW` (push Leray's
`T.coverStar`-level surjectivity down along the same-index refinement `T.ref_star_W`). -/
theorem toH1_coverW_surjective (T : ShrinkChain X) :
    Function.Surjective (toH1 (0 : RS.Divisor X) T.coverW) := by
  intro ξ
  obtain ⟨η, hη⟩ := toH1_surjective_of_isGood (0 : RS.Divisor X) T.good_star ξ
  refine ⟨resH1 (𝒰 := T.coverStar) (𝒱 := T.coverW) (0 : RS.Divisor X) id T.ref_star_W η, ?_⟩
  rw [toH1_resH1, hη]

omit [T1Space X] in
/-- **§6.5's assembly**: the Schwartz cospan lemma finishes off `H1Cover 0 T.coverW`. -/
theorem finiteDimensional_h1Cover_W (T : ShrinkChain X) :
    FiniteDimensional ℂ (H1Cover (0 : RS.Divisor X) T.coverW) :=
  finiteDimensional_of_cospan (tradePi T) (tradeCompact T) (tradePi_surjective T)
    (isCompactOperator_tradeCompact T) (classMap T) (classMap_tradeDiff_eq_zero T)
    (classMap_surjective T)

/-- Compat: `AddCommGroup (H1 D)` does not resolve by plain `inferInstance` in this codebase (a
higher-order-instance gap resolving `∀ 𝒰, AddCommGroup (H1Cover D 𝒰)` for
`Module.DirectLimit.addCommGroup`, per cech's own recorded gotcha) — supply it explicitly. -/
noncomputable instance addCommGroupH1 (D : RS.Divisor X) : AddCommGroup (H1 D) :=
  Module.DirectLimit.addCommGroup (fun 𝒰 : FinCover (⊤ : Opens X) => H1Cover D 𝒰)
    (fun _ _ h => resH1' D h)

/-- **The unit's headline instance**: `H¹(X, 𝒪)` is finite-dimensional (Forster §14). -/
instance finiteDimensional_H1_zero : FiniteDimensional ℂ (H1 (0 : RS.Divisor X)) := by
  obtain ⟨T⟩ := ShrinkChain.nonempty (X := X)
  have := finiteDimensional_h1Cover_W T
  exact Module.Finite.of_surjective (toH1 (0 : RS.Divisor X) T.coverW) (toH1_coverW_surjective T)

/-! ### §7: all-`D` finiteness (the six-term skyscraper fragment, decision D2) -/

/-- **All-`D` finiteness** (§7): `H¹(D)` is finite-dimensional for every divisor `D`. With
`D' := D ⊔ 0`: `H¹(D')` is finite (surjective image of `H¹(0)` via `H1Incl_surjective`); the
inclusion `H¹(D) ↪ H¹(D')` has finite-dimensional kernel (`= range (windowConnect h)` by
cech's six-term exactness `exact_windowConnect_H1Incl`, itself finite since `Window D D'` is)
and finite-dimensional codomain `H¹(D')`, so `H¹(D)` is finite by
`FiniteDimensional.of_linearMap_ker_range`. -/
instance finiteDimensional_H1 (D : RS.Divisor X) : FiniteDimensional ℂ (H1 D) := by
  set D' := D ⊔ 0 with hD'_def
  have h0 : (0 : RS.Divisor X) ≤ D' := le_sup_right
  have h : D ≤ D' := le_sup_left
  have hD'fin : FiniteDimensional ℂ (H1 D') :=
    Module.Finite.of_surjective (H1Incl (0 : RS.Divisor X) h0) (H1Incl_surjective h0)
  have hWfin : FiniteDimensional ℂ (Window D D') := finiteDimensional_window D D' h
  have hrangefin : FiniteDimensional ℂ (LinearMap.range (windowConnect h)) :=
    LinearMap.finiteDimensional_range _
  have hexact : LinearMap.ker (H1Incl D h) = LinearMap.range (windowConnect h) :=
    (LinearMap.exact_iff).1 (exact_windowConnect_H1Incl h)
  have : FiniteDimensional ℂ (LinearMap.ker (H1Incl D h)) := hexact ▸ hrangefin
  exact FiniteDimensional.of_linearMap_ker_range (H1Incl D h)

end RS.Finiteness
