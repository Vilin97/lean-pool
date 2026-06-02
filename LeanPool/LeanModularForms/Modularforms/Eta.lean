/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.E2
public import LeanPool.LeanModularForms.Modularforms.Csqrt
public import LeanPool.LeanModularForms.Modularforms.Upperhalfplane
public import Mathlib.NumberTheory.ModularForms.DedekindEta

/-! # Eta -/


@[expose] public section


open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma


/- The eta function. Lean 4.29+ no longer allows η as an identifier name.
   We rely on mathlib's `scoped[ModularForm] notation "η" => eta`, brought into
   scope by `open ModularForm` above. -/

lemma eta_logDeriv_eql (z : ℍ) : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
  (logDeriv ((csqrt) * η)) z := by
  have h0 : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
            ((z :ℂ)^(2 : ℤ))⁻¹ *
              (logDeriv η) (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    rw [logDeriv_comp, mul_comm]
    · congr
      conv =>
        enter [1,1]
        intro z
        rw [neg_div]
        simp
      simp only [deriv.fun_neg', deriv_inv', neg_neg, inv_inj]
      norm_cast
    · simpa [ModularForm.eta] using
        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := (-1 / (z : ℂ)))
          (by simpa using pnat_div_upper 1 z))
    conv =>
      enter [2]
      ext z
      rw [neg_div]
      simp
    apply DifferentiableAt.neg
    apply DifferentiableAt.inv
    · simp only [differentiableAt_fun_id]
    · exact ne_zero z
  rw [h0, show ((csqrt) * η) = (fun x => (csqrt) x * η x) by rfl, logDeriv_mul]
  · nth_rw 2 [logDeriv_apply]
    unfold csqrt
    have := csqrt_deriv z
    rw [this]
    simp only [one_div, neg_mul, smul_eq_mul]
    nth_rw 2 [div_eq_mul_inv]
    · rw [← Complex.exp_neg,
          show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
               (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)))* 2⁻¹ by ring,
          ← Complex.exp_add, ← sub_eq_add_neg,
          show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring,
          Complex.exp_neg, Complex.exp_log,
          show logDeriv η z = (π * Complex.I / 12) * E₂ z by
            simpa [ModularForm.eta, E₂] using (ModularForm.logDeriv_eta_eq_E2 z)]
      · have Rb : logDeriv η (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) =
          (π * Complex.I / 12) * E₂ (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
          simpa [ModularForm.eta, E₂] using
            (ModularForm.logDeriv_eta_eq_E2 (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ))
        rw [Rb]
        have E := E₂_transform z
        simp only [one_div, neg_mul, smul_eq_mul, SL_slash_def, modular_S_smul,
                   ModularGroup.denom_S, Int.reduceNeg, zpow_neg] at *
        have h00 : UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos =
                   (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
          simp
          ring_nf
        rw [h00] at E
        rw [← mul_assoc, mul_comm, ← mul_assoc]
        rw [E, add_mul, add_comm]
        congr 1
        · have hzne := ne_zero z
          have hI : Complex.I ≠ 0 := I_ne_zero
          have hpi : (π : ℂ) ≠ 0 := by
            simp only [ne_eq, ofReal_eq_zero]
            exact Real.pi_ne_zero
          field_simp
          ring
        rw [mul_comm]
      simpa only [UpperHalfPlane.coe, ne_eq] using (ne_zero z)
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · simpa [ModularForm.eta] using (ModularForm.eta_ne_zero (z := (z : ℂ)) z.2)
  · exact csqrt_differentiableAt z
  · simpa [ModularForm.eta] using
      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := (z : ℂ)) z.2)

lemma eta_logderivs : {z : ℂ | 0 < z.im}.EqOn (logDeriv (η ∘ (fun z : ℂ => -1/z)))
  (logDeriv ((csqrt) * η)) := by
  intro z hz
  have := eta_logDeriv_eql ⟨z, hz⟩
  exact this

lemma eta_logderivs_const : ∃ z : ℂ, z ≠ 0 ∧ {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
  (z • ((csqrt) * η)) := by
  have h := eta_logderivs
  rw [logDeriv_eqOn_iff] at h
  · exact h
  · apply DifferentiableOn.comp
    pick_goal 4
    · use ({z : ℂ | 0 < z.im})
    · rw [DifferentiableOn]
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      simpa [ModularForm.eta] using
        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := x) hx)
    · apply DifferentiableOn.div
      · fun_prop
      · fun_prop
      intro x hx
      have hx2 := ne_zero (⟨x, hx⟩ : ℍ)
      norm_cast at *
    · intro y hy
      simp only [mem_setOf_eq]
      have := UpperHalfPlane.im_inv_neg_coe_pos (⟨y, hy⟩ : ℍ)
      conv =>
        enter [2,1]
        rw [neg_div]
        rw [div_eq_mul_inv]
        simp
      simp only [inv_neg, neg_im, inv_im, Left.neg_pos_iff] at *
      exact this
  · apply DifferentiableOn.mul
    · simp only [DifferentiableOn, mem_setOf_eq]
      intro x hx
      apply (csqrt_differentiableAt ⟨x, hx⟩).differentiableWithinAt
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    have hηx : DifferentiableAt ℂ η x := by
      simpa [ModularForm.eta] using
        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := x) hx)
    exact hηx.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_im
  · apply Convex.isPreconnected
    exact convex_halfSpace_im_gt 0
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨ ?_ , by simpa [ModularForm.eta] using (ModularForm.eta_ne_zero (z := x) hx)⟩
    unfold csqrt
    simp only [one_div, Complex.exp_ne_zero, not_false_eq_true]
  · intro x hx
    simp only [comp_apply, ne_eq]
    have := ModularForm.eta_ne_zero (z := (-1 / x))
      (by simpa using pnat_div_upper 1 ⟨x, hx⟩)
    simpa only [ne_eq] using this

lemma eta_equality : {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
   ((csqrt (Complex.I))⁻¹ • ((csqrt) * η)) := by
  have h := eta_logderivs_const
  obtain ⟨z, hz, h⟩ := h
  intro x hx
  have h2 := h hx
  have hI : (Complex.I) ∈ {z : ℂ | 0 < z.im} := by
    simp only [mem_setOf_eq, Complex.I_im, zero_lt_one]
  have h3 := h hI
  simp only [comp_apply, div_I, neg_mul, one_mul, neg_neg, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul] at h3
  conv at h3 =>
    enter [2]
    rw [← mul_assoc]
  have he : η Complex.I ≠ 0 := by
    simpa [ModularForm.eta] using (ModularForm.eta_ne_zero (z := (Complex.I : ℂ)) (by simp))
  have hcd := (mul_eq_right₀ he).mp (_root_.id (Eq.symm h3))
  rw [mul_eq_one_iff_inv_eq₀ hz] at hcd
  rw [@inv_eq_iff_eq_inv] at hcd
  rw [hcd] at h2
  exact h2
