/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.Basic
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Layer 2a of the Hasse–Minkowski development: local isotropy

Hasse–Minkowski says that a quadratic form over `ℚ` is isotropic if and only if it becomes
isotropic after extending scalars to every completion of `ℚ`, namely `ℝ` and the `p`-adic
fields `ℚ_[p]` for all primes `p`.  This file supplies the local side of the statement:

* `EverywhereLocallyIsotropic Q`: `Q` is isotropic over every completion.
* `isotropic_everywhereLocallyIsotropic`: the easy implication, by base-changing an isotropic
  vector along `1 ⊗ₜ x`.
* `baseChange_weightedSumSquares`: base change commutes with the concrete form
  `weightedSumSquares`, a fact Mathlib 4.33 lacks and which the rank-two case below needs.

The tensor-product object `Q.baseChange A` is Mathlib's `QuadraticForm.baseChange A Q`, a form
on `A ⊗[ℚ] V`.
-/

public section

open Module QuadraticMap TensorProduct

namespace HasseMinkowski

/-! ### Base change of a weighted sum of squares

Mathlib has no statement relating `(weightedSumSquares R w).baseChange A` to a weighted sum of
squares over `A`.  The canonical identification is `A ⊗[R] (ι → R) ≃ₗ[A] (ι → A)`
(`TensorProduct.piScalarRight`), under which the two forms agree.  We prove agreement by
`baseChange_ext`, which reduces to the pure tensors `1 ⊗ₜ y`. -/

section BaseChangeWeightedSumSquares

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [Invertible (2 : R)]
  [Fintype ι]

-- Theorem: base change sends a weighted sum of squares to the weighted sum of squares with
-- the base-changed weights.
theorem baseChange_weightedSumSquares (w : ι → R) :
    (QuadraticForm.baseChange A (weightedSumSquares R w)).Equivalent
      (weightedSumSquares A (fun i => algebraMap R A (w i))) := by
  classical
  refine ⟨⟨TensorProduct.piScalarRight R A A ι, ?_⟩⟩
  have hcomp : (weightedSumSquares A (fun i => algebraMap R A (w i))).comp
      (TensorProduct.piScalarRight R A A ι) =
      QuadraticForm.baseChange A (weightedSumSquares R w) := by
    apply baseChange_ext
    intro y
    simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, weightedSumSquares_apply,
      QuadraticForm.baseChange_tmul, mul_one, map_sum, map_mul, Algebra.smul_def,
      Algebra.algebraMap_self_apply]
  intro x
  exact congr_fun hcomp x

end BaseChangeWeightedSumSquares

/-! ### Base change preserves isotropy

The forward implication of Hasse–Minkowski is easy: if `x ≠ 0` is isotropic for `Q`, then
`1 ⊗ₜ x` is isotropic for the base change.  The only point to check is `1 ⊗ₜ x ≠ 0`, which
holds because a nontrivial algebra over a field is faithfully flat. -/

section BaseChangeIsotropic

variable {R A V : Type*} [Field R] [CommRing A] [Algebra R A] [Nontrivial A]
  [AddCommGroup V] [Module R V] [Invertible (2 : R)]

-- Theorem: base change to a nontrivial algebra over a field preserves isotropy.
theorem isotropic_baseChange {Q : QuadraticForm R V} (hQ : Isotropic Q) :
    Isotropic (QuadraticForm.baseChange A Q) := by
  obtain ⟨x, hx, hQx⟩ := hQ
  refine ⟨(1 : A) ⊗ₜ[R] x, ?_, ?_⟩
  · intro h
    exact hx ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := R) (M := V) (A := A) x).mp h)
  · rw [QuadraticForm.baseChange_tmul, hQx]
    simp

end BaseChangeIsotropic

/-! ### Everywhere local isotropy -/

section EverywhereLocally

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A quadratic form over `ℚ` is *everywhere locally isotropic* if it is isotropic over every
completion of `ℚ`: over `ℝ` and over every `p`-adic field `ℚ_[p]`. -/
def EverywhereLocallyIsotropic (Q : QuadraticForm ℚ V) : Prop :=
  (∀ (p : ℕ) [Fact (Nat.Prime p)], Isotropic (QuadraticForm.baseChange ℚ_[p] Q)) ∧
    Isotropic (QuadraticForm.baseChange ℝ Q)

-- Theorem: a globally isotropic form is everywhere locally isotropic.
theorem isotropic_everywhereLocallyIsotropic {Q : QuadraticForm ℚ V} (hQ : Isotropic Q) :
    EverywhereLocallyIsotropic Q :=
  ⟨fun p _ => isotropic_baseChange (A := ℚ_[p]) hQ,
    isotropic_baseChange (A := ℝ) hQ⟩

end EverywhereLocally

/-! ### Dot-notation alias

Mirrors the aliases in `Basic.lean`, so that `Q.EverywhereLocallyIsotropic` works for a
quadratic form `Q`. -/

namespace QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Dot-notation alias for `HasseMinkowski.EverywhereLocallyIsotropic`: the quadratic form is
isotropic over `ℝ` and over every `p`-adic field `ℚ_[p]`. -/
abbrev EverywhereLocallyIsotropic (Q : QuadraticForm ℚ V) : Prop :=
  HasseMinkowski.EverywhereLocallyIsotropic Q

end QuadraticMap

end HasseMinkowski
