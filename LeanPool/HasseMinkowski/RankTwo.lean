/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.Locally
public import LeanPool.HasseMinkowski.RatSquares
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Layer 2b of the Hasse–Minkowski development: ranks one and two

This file proves the Hasse–Minkowski principle in ranks one and two: a quadratic form over `ℚ`
that becomes isotropic over every completion of `ℚ` is already isotropic over `ℚ`.  Both proofs
are direct adaptations of the classical arguments.

* **Rank one.** In dimension one a nonzero quadratic form is anisotropic over any field, so real
  isotropy forces the base-changed form to be zero; evaluating at `1 ⊗ m` shows the original form
  vanishes on every vector.
* **Rank two.** By `equivalent_weightedSumSquares_units_of_nondegenerate'` a nondegenerate form is
  isometric to a weighted sum of squares `w₀ y₀² + w₁ y₁²` with nonzero rational weights.  Real
  isotropy makes the ratio `-w₀⁻¹ w₁` nonnegative, while each `p`-adic completion gives it an even
  `p`-adic valuation; the square criterion `isSquare_of_nonneg_of_even_padicValRat` then produces
  the isotropic vector `![x, 1]`.

## Main results

* `isotropic_of_rank_one`, `isotropic_of_rank_two`.
* `QuadraticMap.Equivalent.represents_iff`: equivalent forms represent the same values.
-/

@[expose] public section

open Module QuadraticMap TensorProduct

/-! ### Representation transfers along isometries -/

namespace QuadraticMap

namespace Equivalent

-- Theorem: equivalent quadratic forms represent exactly the same values.
theorem represents_iff {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂] {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (h : Q₁.Equivalent Q₂) (a : R) :
    HasseMinkowski.represents Q₁ a ↔ HasseMinkowski.represents Q₂ a := by
  obtain ⟨e⟩ := h
  constructor
  · rintro ⟨x, hx, hxQ⟩
    refine ⟨e x, ?_, ?_⟩
    · intro h0
      exact hx (by simpa using congrArg (⇑e.symm) h0)
    · rw [e.map_app x, hxQ]
  · rintro ⟨x, hx, hxQ⟩
    refine ⟨e.symm x, ?_, ?_⟩
    · intro h0
      exact hx (by simpa using congrArg (⇑e) h0)
    · rw [e.symm.map_app x, hxQ]

end Equivalent

end QuadraticMap

namespace HasseMinkowski

/-! ### Rank one -/

section RankOne

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

-- Theorem: rank-one Hasse–Minkowski.
lemma isotropic_of_rank_one (Q : QuadraticForm ℚ V) (hr : Module.finrank ℚ V = 1)
    (hQ' : EverywhereLocallyIsotropic Q) : Isotropic Q := by
  have : FiniteDimensional ℚ V :=
    FiniteDimensional.of_finrank_pos (by rw [hr]; norm_num)
  have : FiniteDimensional ℝ (ℝ ⊗[ℚ] V) :=
    FiniteDimensional.of_finrank_pos (by rw [Module.finrank_baseChange, hr]; norm_num)
  refine (isotropic_iff_zero_of_rank_one Q hr).mpr ?_
  have hzero : QuadraticForm.baseChange ℝ Q = 0 :=
    (isotropic_iff_zero_of_rank_one (QuadraticForm.baseChange ℝ Q)
      (by rw [Module.finrank_baseChange, hr])).mp hQ'.2
  ext m
  have hm : QuadraticForm.baseChange ℝ Q ((1 : ℝ) ⊗ₜ[ℚ] m) = 0 := by rw [hzero]; rfl
  rw [QuadraticForm.baseChange_tmul] at hm
  have hm' : ((Q m : ℚ) : ℝ) = 0 := by simpa [Rat.smul_def] using hm
  exact Rat.cast_eq_zero.mp hm'

end RankOne

/-! ### Rank two -/

section RankTwo

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

-- Theorem: if a nonzero rational `w₀ x₀² + w₁ x₁² = 0` holds over a characteristic-zero field
-- with `x₁ ≠ 0`, then `-w₀⁻¹ w₁` is the square `(x₁⁻¹ x₀)²`.
private lemma coeff_ratio_isSquare_of_represents_zero {K : Type*} [Field K] [CharZero K]
    {w : Fin 2 → ℚ} {x : Fin 2 → K} (hw0 : w 0 ≠ 0) (hx1 : x 1 ≠ 0)
    (h : (w 0 : K) * x 0 ^ 2 + (w 1 : K) * x 1 ^ 2 = 0) :
    (((-(w 0)⁻¹ * w 1 : ℚ)) : K) = ((x 1)⁻¹ * x 0) ^ 2 := by
  have hw0K : (w 0 : K) ≠ 0 := Rat.cast_ne_zero.mpr hw0
  have hx1K : (x 1 : K) ≠ 0 := hx1
  have hx1sq : (x 1 : K) ^ 2 ≠ 0 := pow_ne_zero 2 hx1K
  have hw1eq : (w 1 : K) * x 1 ^ 2 = -(w 0 : K) * x 0 ^ 2 := by
    linear_combination h
  rw [Rat.cast_mul, Rat.cast_neg, Rat.cast_inv]
  have hb : (w 0 : K) * x 1 ^ 2 ≠ 0 := mul_ne_zero hw0K hx1sq
  have key : (-(w 0 : K)⁻¹ * (w 1 : K)) * ((w 0 : K) * x 1 ^ 2) =
      ((x 1)⁻¹ * x 0) ^ 2 * ((w 0 : K) * x 1 ^ 2) := by
    rw [show (-(w 0 : K)⁻¹ * (w 1 : K)) * ((w 0 : K) * x 1 ^ 2) =
      -((w 1 : K) * x 1 ^ 2) by field_simp [hw0K]]
    rw [hw1eq]
    field_simp [hw0K, hx1K]
  exact mul_right_cancel₀ hb key

-- Theorem: a representation of zero by a weighted sum of squares with nonzero weights has both
-- coordinates nonzero.
private lemma comp_ne_zero_of_nondegenerate {K : Type*} [Field K] [CharZero K]
    {w : Fin 2 → ℚ} (hw0 : w 0 ≠ 0) (hw1 : w 1 ≠ 0) {x : Fin 2 → K} (hx : x ≠ 0)
    (h : (w 0 : K) * x 0 ^ 2 + (w 1 : K) * x 1 ^ 2 = 0) : x 0 ≠ 0 ∧ x 1 ≠ 0 := by
  have hw0K : (w 0 : K) ≠ 0 := Rat.cast_ne_zero.mpr hw0
  have hw1K : (w 1 : K) ≠ 0 := Rat.cast_ne_zero.mpr hw1
  constructor
  · intro h0
    apply hx
    have hx1 : x 1 = 0 := by
      have h' : (w 1 : K) * x 1 ^ 2 = 0 := by
        have := h
        rw [h0] at this
        simpa using this
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h').resolve_left hw1K)
    funext i
    fin_cases i <;> simp [h0, hx1]
  · intro h1
    apply hx
    have hx0 : x 0 = 0 := by
      have h' : (w 0 : K) * x 0 ^ 2 = 0 := by
        have := h
        rw [h1] at this
        simpa using this
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h').resolve_left hw0K)
    funext i
    fin_cases i <;> simp [hx0, h1]

-- Theorem: rank-two Hasse–Minkowski.
lemma isotropic_of_rank_two (Q : QuadraticForm ℚ V)
    (hr : Module.finrank ℚ V = 2) (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) :
    Isotropic Q := by
  obtain ⟨hQ'f, hQ'R⟩ := hQ'
  have hsep : (QuadraticMap.associated (R := ℚ) Q).SeparatingLeft :=
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  -- Reindex the weighted sum of squares from `Fin (finrank ℚ V)` to `Fin 2`.
  obtain ⟨w₀, hw₀⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
  have hw2 : ∃ w : Fin 2 → ℚˣ,
      Q.Equivalent (weightedSumSquares ℚ (fun i => (w i : ℚ))) := by
    revert w₀ hw₀
    rw [hr]
    exact fun w hw => ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hw2
  let wq : Fin 2 → ℚ := fun i => (w i : ℚ)
  have hwq0 : wq 0 ≠ 0 := by simp [wq]
  have hwq1 : wq 1 ≠ 0 := by simp [wq]
  have hw' : Q.Equivalent (weightedSumSquares ℚ wq) := by simpa only [wq] using hw
  rw [← represents_zero_iff_isotropic]
  rw [hw'.represents_iff]
  have heqR : (Q.baseChange ℝ).Equivalent
      (weightedSumSquares ℝ (fun i => algebraMap ℚ ℝ (wq i))) :=
    (hw'.baseChange (A := ℝ)).trans
      (baseChange_weightedSumSquares (R := ℚ) (A := ℝ) (w := wq))
  have heqf (p : ℕ) [Fact (Nat.Prime p)] :
      (Q.baseChange ℚ_[p]).Equivalent
        (weightedSumSquares ℚ_[p] (fun i => algebraMap ℚ ℚ_[p] (wq i))) :=
    (hw'.baseChange (A := ℚ_[p])).trans
      (baseChange_weightedSumSquares (R := ℚ) (A := ℚ_[p]) (w := wq))
  rw [← represents_zero_iff_isotropic] at hQ'R
  rw [heqR.represents_iff] at hQ'R
  have hQ'fw (p : ℕ) [Fact (Nat.Prime p)] :
      represents (weightedSumSquares ℚ_[p] (fun i => algebraMap ℚ ℚ_[p] (wq i))) 0 :=
    ((heqf p).represents_iff 0).mp ((represents_zero_iff_isotropic _).mpr (hQ'f p))
  simp only [represents, weightedSumSquares_apply, Fin.sum_univ_two, ← pow_two, smul_eq_mul]
    at hQ'R hQ'fw ⊢
  have hR' : 0 ≤ -(wq 0)⁻¹ * wq 1 := by
    obtain ⟨x, hx, hx0⟩ := hQ'R
    rw [← Rat.cast_nonneg (K := ℝ), ← Real.isSquare_iff, isSquare_iff_exists_sq]
    exact ⟨(x 1)⁻¹ * x 0,
      coeff_ratio_isSquare_of_represents_zero hwq0
        (comp_ne_zero_of_nondegenerate hwq0 hwq1 hx hx0).2 hx0⟩
  have hf (p : ℕ) (hp : p.Prime) : Even (padicValRat p (-(wq 0)⁻¹ * wq 1)) := by
    have : Fact (Nat.Prime p) := ⟨hp⟩
    obtain ⟨x, hx, hx0⟩ := hQ'fw p
    rw [← Padic.valuation_ratCast,
      coeff_ratio_isSquare_of_represents_zero hwq0
        (comp_ne_zero_of_nondegenerate hwq0 hwq1 hx hx0).2 hx0]
    rw [Padic.valuation_pow]
    exact even_two_mul _
  obtain ⟨x, hx⟩ := isSquare_of_nonneg_of_even_padicValRat hR' hf
  refine ⟨![x, 1], ?_, ?_⟩
  · intro h
    have h1 := congr_fun h 1
    simp at h1
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pow_two]
    rw [← hx]
    field_simp [hwq0]
    ring

end RankTwo

end HasseMinkowski
