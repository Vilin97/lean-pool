/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Opening.CyclotomicDefect
public import LeanPool.MarkoffModP.BGS.Markoff.Opening.PeriodicSemisimple

/-!
# Torsion eigenvalue traces force the complex Markoff origin

This is the characteristic-zero contradiction at the heart of the opening.  Once each
coordinate of a complex normalized Markoff point is represented by a torsion eigenvalue and its
reciprocal, the unit-circle defect argument forces all three coordinates to vanish.
-/

@[expose] public section

namespace BGS.Markoff

/-- A finite-order complex unit has norm one. -/
theorem norm_coe_eq_one_of_isOfFinOrder (w : ℂˣ) (hw : IsOfFinOrder w) :
    ‖(w : ℂ)‖ = 1 := by
  rw [isOfFinOrder_iff_pow_eq_one] at hw
  obtain ⟨n, hn, hpower⟩ := hw
  have hpowerComplex : (w : ℂ) ^ n = 1 := by
    exact congrArg Units.val hpower
  exact Complex.norm_eq_one_of_pow_eq_one hpowerComplex hn.ne'

/-- A complex normalized Markoff point whose three coordinates are reciprocal traces of torsion
eigenvalues is the origin. -/
theorem complex_normalizedMarkoff_eq_origin_of_torsion_traces
    (x : NormalizedPoint ℂ) (hx : IsNormalizedMarkoff x)
    (h₁ : ∃ w₁ : ℂˣ, IsOfFinOrder w₁ ∧ x.u1 = splitTorusTrace w₁)
    (h₂ : ∃ w₂ : ℂˣ, IsOfFinOrder w₂ ∧ x.u2 = splitTorusTrace w₂)
    (h₃ : ∃ w₃ : ℂˣ, IsOfFinOrder w₃ ∧ x.u3 = splitTorusTrace w₃) :
    x = normalizedOrigin := by
  obtain ⟨w₁, hw₁, hx₁⟩ := h₁
  obtain ⟨w₂, hw₂, hx₂⟩ := h₂
  obtain ⟨w₃, hw₃, hx₃⟩ := h₃
  have hn₁ := norm_coe_eq_one_of_isOfFinOrder w₁ hw₁
  have hn₂ := norm_coe_eq_one_of_isOfFinOrder w₂ hw₂
  have hn₃ := norm_coe_eq_one_of_isOfFinOrder w₃ hw₃
  have ht₁' : cyclotomicTrace (w₁ : ℂ) = x.u1 := by
    rw [hx₁]
    simp [cyclotomicTrace, splitTorusTrace]
  have ht₂' : cyclotomicTrace (w₂ : ℂ) = x.u2 := by
    rw [hx₂]
    simp [cyclotomicTrace, splitTorusTrace]
  have ht₃' : cyclotomicTrace (w₃ : ℂ) = x.u3 := by
    rw [hx₃]
    simp [cyclotomicTrace, splitTorusTrace]
  have hdefect : cyclotomicDefect (w₁ : ℂ) (w₂ : ℂ) (w₃ : ℂ) = 0 := by
    calc
      cyclotomicDefect (w₁ : ℂ) (w₂ : ℂ) (w₃ : ℂ) = normalizedPolynomial x := by
        rw [cyclotomicDefect, ht₁', ht₂', ht₃']
        rfl
      _ = 0 := hx
  obtain ⟨ht₁, ht₂, ht₃⟩ :=
    cyclotomicTrace_eq_zero_of_defect_eq_zero hn₁ hn₂ hn₃ hdefect
  apply NormalizedPoint.ext
  · change x.u1 = 0
    rw [← ht₁']
    exact ht₁
  · change x.u2 = 0
    rw [← ht₂']
    exact ht₂
  · change x.u3 = 0
    rw [← ht₃']
    exact ht₃

end BGS.Markoff
