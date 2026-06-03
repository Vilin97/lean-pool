/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.Modularforms.E2
import LeanPool.LeanModularForms.Modularforms.Csqrt
import LeanPool.LeanModularForms.Modularforms.LogDerivLems
import LeanPool.LeanModularForms.Modularforms.ExpLems
import LeanPool.LeanModularForms.Modularforms.Upperhalfplane

/-! # EtaCleanup -/


open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction

local notation "𝕢" => Periodic.qParam

local notation "𝕢₁" => Periodic.qParam 1

/-- The `n`-th factor `q ^ (n + 1)` appearing in the eta product expansion. -/
noncomputable abbrev etaQ (n : ℕ) (z : ℂ) := (𝕢₁ z) ^ (n + 1)

lemma eta_q_eq_exp (n : ℕ) (z : ℂ) : etaQ n z = cexp (2 * π * Complex.I * (n + 1) * z) := by
  simp [etaQ, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

lemma eta_q_eq_pow (n : ℕ) (z : ℂ) : etaQ n z = cexp (2 * π * Complex.I * z) ^ (n + 1) := by
  simp [etaQ, Periodic.qParam]

theorem qParam_lt_one (z : ℍ) (r : ℝ) (hr : 0 < r) : ‖𝕢 r z‖ < 1 := by
  simp only [Periodic.qParam, norm_exp, div_ofReal_re, mul_re, re_ofNat, ofReal_re, im_ofNat,
    ofReal_im, mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one,
    sub_self, coe_re, coe_im, zero_sub, Real.exp_lt_one_iff]
  rw [neg_div, neg_lt_zero]
  positivity

lemma one_sub_qParam_ne_zero (r : ℝ) (hr : 0 < r) (z : ℍ) : 1 - 𝕢 r z ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have := qParam_lt_one z r
  rw [← h] at this
  simp [lt_self_iff_false] at *
  linarith

lemma one_add_eta_q_ne_zero (n : ℕ) (z : ℍ) : 1 - etaQ n z ≠ 0 := by
  rw [eta_q_eq_exp, sub_ne_zero]
  intro h
  have := exp_upperHalfPlane_lt_one_nat z n
  rw [← h] at this
  simp only [norm_one, lt_self_iff_false] at *

/-- The infinite product `∏ (1 - q ^ (n + 1))` in the eta function. -/
noncomputable abbrev etaProdTerm (z : ℂ) := ∏' (n : ℕ), (1 - etaQ n z)

local notation "ηₚ" => etaProdTerm

/-- The Dedekind eta function, defined on all of `ℂ` so that its logarithmic derivative
can be taken. -/
noncomputable def dedekindEtaFun' (z : ℂ) := (𝕢 24 z) * ηₚ z

local notation "η" => dedekindEtaFun'


theorem Summable_eta_q (z : ℍ) : Summable fun n : ℕ ↦ ‖-etaQ n z‖ := by
    simp_rw  [etaQ, eta_q_eq_pow, norm_neg, norm_pow, summable_nat_add_iff 1]
    simp only [summable_geometric_iff_norm_lt_one, norm_norm]
    apply exp_upperHalfPlane_lt_one z

@[fun_prop]
lemma qParam_differentiable (n : ℝ) : Differentiable ℂ (𝕢 n) := by
    rw [show 𝕢 n = fun x => exp (2 * π * Complex.I * x / n)  by rfl]
    fun_prop

@[fun_prop]
lemma qParam_ContDiff (n : ℝ) (m : WithTop ℕ∞) : ContDiff ℂ m (𝕢 n) := by
    rw [show 𝕢 n = fun x => exp (2 * π * Complex.I * x / n)  by rfl]
    fun_prop

lemma hasProdLocallyUniformlyOn_eta :
    HasProdLocallyUniformlyOn (fun n a ↦ 1 - etaQ n a) ηₚ {x | 0 < x.im} := by
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact
    (isOpen_lt continuous_const Complex.continuous_im)
  intro K hK hcK
  by_cases hN : ¬ Nonempty K
  · rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    simpa [not_nonempty_iff_eq_empty'.mp hN] using tendstoUniformlyOn_empty
  have hc : ContinuousOn (fun x ↦ ‖cexp (2 * ↑π * Complex.I * x)‖) K := by fun_prop
  obtain ⟨z, hz, hB, HB⟩ := IsCompact.exists_sSup_image_eq_and_ge hcK
    (Set.nonempty_coe_sort.mp (not_not.mp hN)) hc
  apply Summable.hasProdUniformlyOn_nat_one_add hcK (Summable_eta_q ⟨z, by simpa using (hK hz)⟩)
  · filter_upwards with n x hx
    simpa only [etaQ, eta_q_eq_pow n x, norm_neg, norm_pow, UpperHalfPlane.coe_mk,
        eta_q_eq_pow n (⟨z, hK hz⟩ : ℍ)] using
        pow_le_pow_left₀ (by simp [norm_nonneg]) (HB x hx) (n + 1)
  · simp_rw [etaQ, Periodic.qParam]
    fun_prop

lemma tprod_ne_zero' {ι α : Type*} (x : α) (f : ι → α → ℂ) (hf : ∀ i x, 1 + f i x ≠ 0)
  (hu : ∀ x : α, Summable fun n => f n x) : (∏' i : ι, (1 + f i) x) ≠ 0 := by
  simp only [Pi.add_apply, Pi.one_apply, ne_eq]
  rw [← Complex.cexp_tsum_eq_tprod (f := fun n => 1 + f n x) (fun n => hf n x)]
  · simp only [exp_ne_zero, not_false_eq_true]
  · exact Complex.summable_log_one_add_of_summable (hu x)

theorem etaProdTerm_ne_zero (z : ℍ) : ηₚ z ≠ 0 := by
  simp only [etaProdTerm, etaQ, ne_eq]
  refine tprod_ne_zero' z (fun n x => -etaQ n x) ?_ ?_
  · refine fun i x => by simpa [sub_eq_add_neg] using one_add_eta_q_ne_zero i x
  · intro x
    simpa [etaQ, ←summable_norm_iff] using Summable_eta_q x

/-- Eta is non-vanishing! -/
lemma dedekindEtaFun'_ne_zero (z : ℍ) : η z ≠ 0 := by
  simpa [dedekindEtaFun', Periodic.qParam] using etaProdTerm_ne_zero z

/-
lemma differentiable_eta_q (n : ℕ) : Differentiable ℂ (etaQ n) := by
  rw [show etaQ n = fun x => -exp (2 * π * Complex.I * x) ^ (n + 1) by
      ext z; exact eta_q_eq_pow n z]
  fun_prop -/

lemma logDeriv_one_sub_cexp (r : ℂ) : logDeriv (fun z ↦ 1 - r * cexp z) =
    fun z ↦ -r * cexp z / (1 - r * cexp ( z)) := by
  ext z
  simp [logDeriv]

lemma logDeriv_one_sub_mul_cexp_comp (r : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    logDeriv ((fun z ↦ 1 - r * cexp z) ∘ g) =
    fun z ↦ -r * (deriv g z) * cexp (g z) / (1 - r * cexp (g z)) := by
  ext y
  rw [logDeriv_comp (by fun_prop) (hg y), logDeriv_one_sub_exp]
  ring


theorem one_add_eta_logDeriv_eq (z : ℂ) (i : ℕ) :
  logDeriv (fun x ↦ 1 - etaQ i x) z
    = 2 * ↑π * Complex.I * (↑i + 1) * -etaQ i z / (1 - etaQ i z) := by
  have h2 : (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) =
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by aesop
  have h3 : deriv (fun x : ℂ ↦ (2 * π * Complex.I * (i + 1) * x)) =
        fun _ ↦ 2 * π * Complex.I * (i + 1) := by
      ext y
      simp [deriv_const_mul (2 * π * Complex.I * (i + 1)) (d := fun (x : ℂ) => x) (x := y)]
  simp_rw [eta_q_eq_exp, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x => (2 * π * Complex.I * (i + 1) * x)) (by fun_prop), h3]
  simp

lemma tsum_log_deriv_eta_q (z : ℂ) :
  ∑' (i : ℕ), logDeriv (fun x ↦ 1 - etaQ i x) z =
  ∑' n : ℕ, (2 * ↑π * Complex.I * (n + 1)) * (-etaQ n z) / (1  - etaQ n z) := by
  refine tsum_congr (fun i => ?_)
  apply one_add_eta_logDeriv_eq

lemma tsum_log_deriv_eta_q' (z : ℂ) :
  ∑' (i : ℕ), logDeriv (fun x ↦ 1 - etaQ i x) z =
   (2 * ↑π * Complex.I) * ∑' n : ℕ, (n + 1) * (-etaQ n z) / (1  - etaQ n z) := by
  rw [tsum_log_deriv_eta_q z, ← tsum_mul_left]
  congr 1
  ext i
  ring

lemma logDeriv_q' (n : ℝ) (z : ℂ) : logDeriv (𝕢 n) z = 2 * ↑π * Complex.I / n := by
  have : (𝕢 n) = (fun z ↦ cexp (z)) ∘ (fun z => (2 * ↑π * Complex.I / n) * z)  := by
    ext y
    simp only [Periodic.qParam, comp_apply]
    ring_nf
  rw [this, logDeriv_comp (by fun_prop) (by fun_prop), deriv_const_mul _ (by fun_prop)]
  simp only [logDeriv_exp, Pi.one_apply, deriv_id'', mul_one, one_mul]

lemma logDeriv_z_term' (z : ℍ) : logDeriv (𝕢 24) ↑z  =  2 * ↑π * Complex.I / 24 := by
  have : (𝕢 24) = (fun z ↦ cexp (z)) ∘ (fun z => (2 * ↑π * Complex.I / 24) * z)  := by
    ext y
    simp only [Periodic.qParam, ofReal_ofNat, comp_apply]
    ring_nf
  rw [this, logDeriv_comp, deriv_const_mul]
  · simp only [logDeriv_exp, Pi.one_apply, deriv_id'', mul_one, one_mul]
  all_goals {fun_prop}

theorem etaProdTerm_differentiableAt (z : ℍ) : DifferentiableAt ℂ ηₚ ↑z := by
  have hD := hasProdLocallyUniformlyOn_eta.tendstoLocallyUniformlyOn_finsetRange.differentiableOn ?_
    (isOpen_lt continuous_const Complex.continuous_im)
  · rw [DifferentiableOn] at hD
    apply (hD z (by apply z.2)).differentiableAt
    · apply IsOpen.mem_nhds  (isOpen_lt continuous_const Complex.continuous_im) z.2
  · filter_upwards with b y
    apply (DifferentiableOn.finsetProd (u := Finset.range b)
      (f := fun i x => 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))
      (by fun_prop)).congr
    intro x hx
    simp [sub_eq_add_neg, eta_q_eq_exp]

lemma eta_DifferentiableAt_UpperHalfPlane' (z : ℍ) : DifferentiableAt ℂ dedekindEtaFun' z := by
  apply DifferentiableAt.mul (by fun_prop) (etaProdTerm_differentiableAt z)

lemma eta_logDeriv' (z : ℍ) : logDeriv dedekindEtaFun' z = (π * Complex.I / 12) * E₂ z := by
  unfold dedekindEtaFun' etaProdTerm
  rw [logDeriv_mul (UpperHalfPlane.coe z) _ (etaProdTerm_ne_zero z) _
    (etaProdTerm_differentiableAt z)]
  · have HG := logDeriv_tprod_eq_tsum2 (isOpen_lt continuous_const Complex.continuous_im)
      ⟨(z : ℂ), z.2⟩ (fun n x => 1 - etaQ n x)
      (fun i ↦ one_add_eta_q_ne_zero i z) ?_ ?_ ?_ (etaProdTerm_ne_zero z)
    · rw [show (⟨(z : ℂ), z.2⟩ : {b : ℂ | 0 < b.im}).1 = UpperHalfPlane.coe z by rfl] at HG
      rw [HG]
      simp only [tsum_log_deriv_eta_q' z, E₂, logDeriv_z_term' z, mul_neg]
      rw [show E2 z = E₂ z from rfl, E₂_eq z, mul_sub, sub_eq_add_neg]
      conv_rhs => rw [show (∑' (n : ℕ+), ↑↑n * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z) /
          (1 - cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) = ∑' (n : ℕ),
          (↑(n + 1 : ℕ) * cexp (2 * ↑π * Complex.I * ↑(n + 1 : ℕ) * ↑z) /
          (1 - cexp (2 * ↑π * Complex.I * ↑(n + 1 : ℕ) * ↑z))) from by
        rw [← Equiv.pnatEquivNat.symm.tsum_eq]; simp]
      simp_rw [eta_q_eq_exp]
      congr 1
      · ring
      · rw [← tsum_mul_left, ← neg_eq_iff_eq_neg]
        conv_rhs => rw [← tsum_mul_left, ← tsum_mul_left]
        rw [← tsum_neg]
        apply tsum_congr; intro n; push_cast; ring
    · intro i x hx
      simp_rw [eta_q_eq_exp]
      fun_prop
    · simp only [one_add_eta_logDeriv_eq]
      apply ((summable_nat_add_iff 1).mpr ((logDeriv_q_expo_summable (𝕢₁ z)
        (by simpa [Periodic.qParam] using exp_upperHalfPlane_lt_one z)).mul_left
          (-2 * π * Complex.I))).congr
      intro b
      have := one_add_eta_q_ne_zero b z
      simp only [ne_eq, neg_mul, Nat.cast_add, Nat.cast_one, mul_neg] at *
      field_simp
    · exact hasProdLocallyUniformlyOn_eta.multipliableLocallyUniformlyOn
  · simp [ne_eq, exp_ne_zero, not_false_eq_true, Periodic.qParam]
  · fun_prop

lemma eta_logDeriv_eql' (z : ℍ) : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
  (logDeriv ((csqrt) * η)) z := by
  have h0 : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z = ((z :ℂ)^(2 : ℤ))⁻¹ * (logDeriv η) (⟨-1 / z,
    by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    rw [logDeriv_comp, mul_comm]
    · congr
      conv =>
        enter [1,1]
        intro z
        rw [neg_div]
        simp
      simp only [deriv.fun_neg', deriv_inv', neg_neg, inv_inj]
      norm_cast
    · simpa only using
        eta_DifferentiableAt_UpperHalfPlane' (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
    · conv =>
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
    rw [← Complex.exp_neg,
      show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
        (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z))) * 2⁻¹ by ring,
      ← Complex.exp_add, ← sub_eq_add_neg,
      show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring,
      Complex.exp_neg,
      Complex.exp_log (by simpa only [UpperHalfPlane.coe, ne_eq] using (ne_zero z)),
      eta_logDeriv' z]
    have Rb := eta_logDeriv' (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
    simp only [] at Rb
    rw [Rb]
    have E := E₂_transform z
    simp only [one_div, neg_mul, smul_eq_mul, SL_slash_def,
      modular_S_smul,
      ModularGroup.denom_S, Int.reduceNeg, zpow_neg] at *
    have h00 :  (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) = (⟨-1 / z,
      by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
      simp
      ring_nf
    rw [h00] at E
    rw [← mul_assoc, mul_comm, ← mul_assoc]
    rw [E, add_mul, add_comm]
    congr 1
    · have hzne := ne_zero z
      have hI : Complex.I ≠ 0 := by
        exact I_ne_zero
      have hpi : (π : ℂ) ≠ 0 := by
        simp only [ne_eq, ofReal_eq_zero]
        exact Real.pi_ne_zero
      simp at hzne ⊢
      field_simp
      ring
    · rw [mul_comm]
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · apply dedekindEtaFun'_ne_zero z
  · unfold csqrt
    rw [show (fun a ↦ cexp (1 / 2 * Complex.log a)) = cexp ∘ (fun a ↦ 1 / 2 * Complex.log a) by rfl]
    apply DifferentiableAt.comp
    · simp
    · apply DifferentiableAt.const_mul
      apply Complex.differentiableAt_log
      rw [@mem_slitPlane_iff]
      right
      have hz := z.2
      simp only [coe_im] at hz
      exact Ne.symm (ne_of_lt hz)
  · apply eta_DifferentiableAt_UpperHalfPlane' z

lemma eta_logderivs' : {z : ℂ | 0 < z.im}.EqOn (logDeriv (η ∘ (fun z : ℂ => -1/z)))
  (logDeriv ((csqrt) * η)) := by
  intro z hz
  have := eta_logDeriv_eql' ⟨z, hz⟩
  exact this

lemma eta_logderivs_const' : ∃ z : ℂ, z ≠ 0 ∧ {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
  (z • ((csqrt) * η)) := by
  have h := eta_logderivs'
  rw [logDeriv_eqOn_iff] at h
  · exact h
  · apply DifferentiableOn.comp
    pick_goal 4
    · use ({z : ℂ | 0 < z.im})
    · rw [DifferentiableOn]
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      apply eta_DifferentiableAt_UpperHalfPlane' ⟨x, hx⟩
    · apply DifferentiableOn.div
      · fun_prop
      · fun_prop
      · intro x hx
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
    · simp only [DifferentiableOn, mem_setOf_eq]
      intro x hx
      apply (eta_DifferentiableAt_UpperHalfPlane' ⟨x, hx⟩).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_im
  · haveI : IsBoundedSMul ℝ ℂ := NormedSpace.toIsBoundedSMul
    refine Convex.isPreconnected ?_
    exact convex_halfSpace_im_gt 0
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨ ?_ , by apply dedekindEtaFun'_ne_zero ⟨x, hx⟩⟩
    unfold csqrt
    simp only [one_div, Complex.exp_ne_zero, not_false_eq_true]
  · intro x hx
    simp only [comp_apply, ne_eq]
    have := dedekindEtaFun'_ne_zero ⟨-1 / x, by simpa using pnat_div_upper 1 ⟨x, hx⟩⟩
    simpa only [ne_eq, coe_mk] using this

lemma eta_equality' : {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
   ((csqrt (Complex.I))⁻¹ • ((csqrt) * η)) := by
  have h := eta_logderivs_const'
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
    have h:=  dedekindEtaFun'_ne_zero UpperHalfPlane.I
    convert h
  have hcd := (mul_eq_right₀ he).mp (_root_.id (Eq.symm h3))
  rw [mul_eq_one_iff_inv_eq₀ hz] at hcd
  rw [@inv_eq_iff_eq_inv] at hcd
  rw [hcd] at h2
  exact h2
