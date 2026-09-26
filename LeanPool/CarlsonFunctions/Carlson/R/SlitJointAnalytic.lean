/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SlitContinuation
public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegralAnalytic

/-!
# Joint slit-plane continuation: Carlson's Theorem 6.8-2

The regularized function is jointly holomorphic for all complex exponents and Dirichlet
parameters and all nodes in the product slit plane. The interval integral supplies the
convergent seed; the two associated relations propagate its joint analyticity without
division by parameter factors. This proves the continuation assertion of Theorem 6.8-2,
but not Carlson's additional contour representation (6.8-7).
-/

open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private theorem analyticAt_regCarlsonRSlit_comp_of_strip
    {U : Set (κ → ℂ)} {t : (κ → ℂ) → ℂ} {b z : (κ → ℂ) → ι → ℂ}
    (hU : IsOpen U) (ht : AnalyticOnNhd ℂ t U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hslit : ∀ q ∈ U, z q ∈ carlsonRSlitDomain)
    {p : κ → ℂ} (hp : p ∈ U) (htp : (t p).re < 0)
    (hbp : 0 < ((∑ i, b p i) + t p).re) :
    AnalyticAt ℂ (fun q => regCarlsonRSlit (t q) (b q) (z q)) p := by
  let A : (κ → ℂ) → ℂ := fun q => -t q
  let B : (κ → ℂ) → ℂ := fun q => (∑ i, b q i) + t q
  have hA : AnalyticOnNhd ℂ A U := fun q hq => (ht q hq).neg
  have hB : AnalyticOnNhd ℂ B U := fun q hq =>
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp (hb q hq)) i).add (ht q hq)
  have hevent : ∀ᶠ q in nhds p, q ∈ U ∧ 0 < (A q).re ∧ 0 < (B q).re := by
    filter_upwards [hU.mem_nhds hp,
      (Complex.continuous_re.continuousAt.comp (hA p hp).continuousAt).eventually_const_lt
        (show 0 < (A p).re by simpa [A] using neg_pos.mpr htp),
      (Complex.continuous_re.continuousAt.comp (hB p hp).continuousAt).eventually_const_lt hbp]
      with q hq hqa hqb
    exact ⟨hq, hqa, hqb⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hsub : Metric.ball p r ⊆ U := fun q hq => (hball hq).1
  have hI := analyticOnNhd_carlsonRUnitIntervalIntegral_comp Metric.isOpen_ball
    (hA.mono hsub) (hB.mono hsub) (hb.mono hsub) (hz.mono hsub)
    (fun q hq => (hball hq).2) (fun q hq => hslit q (hsub hq))
  have hΓA := (differentiable_one_div_Gamma.analyticAt (A p)).comp_of_eq (hA p hp) rfl
  have hΓB := (differentiable_one_div_Gamma.analyticAt (B p)).comp_of_eq (hB p hp) rfl
  apply ((hI p (Metric.mem_ball_self hr)).mul (hΓA.mul hΓB)).congr
  filter_upwards [Metric.ball_mem_nhds p hr] with q hq
  symm
  change regCarlsonRSlit (t q) (b q) (z q) =
    carlsonRUnitIntervalIntegral (A q) (B q) (b q) (z q) *
      ((Gamma (A q))⁻¹ * (Gamma (B q))⁻¹)
  rw [carlsonRUnitIntervalIntegral_eq_gamma_mul_slit (hball hq).2.1 (hball hq).2.2
    (show A q + B q = ∑ i, b q i by dsimp [A, B]; ring) (hslit q (hsub hq))]
  have hga := Gamma_ne_zero_of_re_pos (hball hq).2.1
  have hgb := Gamma_ne_zero_of_re_pos (hball hq).2.2
  have hneg : -A q = t q := by simp [A]
  rw [hneg]
  field_simp

open scoped Classical in
/-- Analytic substitutions in all arguments of the slit-plane continuation. No restrictions
are imposed on the exponent or Dirichlet parameters. -/
theorem analyticOnNhd_regCarlsonRSlit_comp
    {U : Set (κ → ℂ)} {t : (κ → ℂ) → ℂ} {b z : (κ → ℂ) → ι → ℂ}
    (hU : IsOpen U) (ht : AnalyticOnNhd ℂ t U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hslit : ∀ p ∈ U, z p ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun p => regCarlsonRSlit (t p) (b p) (z p)) U := by
  have hraise {b : (κ → ℂ) → ι → ℂ} (hb : AnalyticOnNhd ℂ b U) (i : ι) :
      AnalyticOnNhd ℂ (fun q => addDirichletUnit (b q) i) U := by
    intro p hp
    apply analyticAt_pi_iff.mpr
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [addDirichletUnit, Function.update_self] using!
        ((analyticAt_pi_iff.mp (hb p hp)) i).add analyticAt_const
    · simpa only [addDirichletUnit, Function.update_of_ne hji] using
        (analyticAt_pi_iff.mp (hb p hp)) j
  have hshift (n m : ℕ) : ∀ (t : (κ → ℂ) → ℂ) (b : (κ → ℂ) → ι → ℂ),
      AnalyticOnNhd ℂ t U → AnalyticOnNhd ℂ b U → ∀ p ∈ U,
      (t p).re < n → 0 < ((∑ i, b p i) + t p).re + m →
      AnalyticAt ℂ (fun q => regCarlsonRSlit (t q) (b q) (z q)) p := by
    induction n with
    | zero =>
      induction m with
      | zero =>
        intro t b ht hb p hp htp hbp
        exact analyticAt_regCarlsonRSlit_comp_of_strip hU ht hb hz hslit hp
          (by simpa using htp) (by simpa using hbp)
      | succ m ih =>
        intro t b ht hb p hp htp hbp
        have hterm (i : ι) : AnalyticAt ℂ
            (fun q => regCarlsonRSlit (t q) (addDirichletUnit (b q) i) (z q)) p := by
          apply ih t _ ht (hraise hb i) p hp htp
          simp only [sum_addDirichletUnit, add_re, one_re, Nat.cast_add, Nat.cast_one] at *
          linarith
        apply (Finset.analyticAt_fun_sum Finset.univ fun i _ =>
          ((analyticAt_pi_iff.mp (hb p hp)) i).mul (hterm i)).congr
        filter_upwards [hU.mem_nhds hp] with q hq
        exact (regCarlsonRSlit_eq_sum_addDirichletUnit (t q) (b q) (hslit q hq)).symm
    | succ n ih =>
      intro t b ht hb p hp htp hbp
      have hterm (i : ι) : AnalyticAt ℂ
          (fun q => regCarlsonRSlit (t q - 1) (addDirichletUnit (b q) i) (z q)) p := by
        apply ih _ _ (fun q hq => (ht q hq).sub analyticAt_const) (hraise hb i) p hp
        · simp only [Pi.sub_apply, sub_re, one_re, Nat.cast_add, Nat.cast_one] at *
          linarith
        · simp only [sum_addDirichletUnit, Pi.sub_apply, add_re, sub_re, one_re] at *
          linarith
      apply (Finset.analyticAt_fun_sum Finset.univ fun i _ =>
        (((analyticAt_pi_iff.mp (hb p hp)) i).mul
          ((analyticAt_pi_iff.mp (hz p hp)) i)).mul (hterm i)).congr
      filter_upwards [hU.mem_nhds hp] with q hq
      simpa using (regCarlsonRSlit_add_one_eq_sum_mul_addDirichletUnit
        (t q - 1) (b q) (hslit q hq)).symm
  intro p hp
  obtain ⟨n, hn⟩ := exists_nat_gt (t p).re
  obtain ⟨m, hm⟩ := exists_nat_gt (-((∑ i, b p i) + t p).re)
  exact hshift n m t b ht hb p hp hn (by linarith)

/-- The exponent is `none`, parameters are `some (inl i)`, and nodes are `some (inr i)`.
This is the full joint holomorphy assertion of Carlson's Theorem 6.8-2. -/
theorem analyticOnNhd_regCarlsonRSlit_joint :
    AnalyticOnNhd ℂ (fun p : Option (ι ⊕ ι) → ℂ =>
      regCarlsonRSlit (p none) (fun i => p (some (.inl i))) (fun i => p (some (.inr i))))
      {p | (fun i => p (some (.inr i))) ∈ carlsonRSlitDomain} := by
  apply analyticOnNhd_regCarlsonRSlit_comp
    (isOpen_carlsonRSlitDomain.preimage (by fun_prop))
  · exact fun p _ => (ContinuousLinearMap.proj none : (Option (ι ⊕ ι) → ℂ) →L[ℂ] ℂ).analyticAt p
  · intro p _
    exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (some (Sum.inl i : ι ⊕ ι)) : (Option (ι ⊕ ι) → ℂ) →L[ℂ]
        ℂ).analyticAt p
  · intro p _
    exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (some (Sum.inr i : ι ⊕ ι)) : (Option (ι ⊕ ι) → ℂ) →L[ℂ]
        ℂ).analyticAt p
  · exact fun _ hp => hp

/-- At any fixed slit-plane node vector, regularization makes `R` entire jointly in
the exponent and Dirichlet parameters. -/
theorem analyticOnNhd_regCarlsonRSlit_exponent_parameters {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun p : Option ι → ℂ =>
      regCarlsonRSlit (p none) (fun i => p (some i)) z) univ := by
  apply analyticOnNhd_regCarlsonRSlit_comp isOpen_univ
  · exact fun p _ => (ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p
  · intro p _
    exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p
  · exact analyticOnNhd_const
  · exact fun _ _ => hz

/-- A pointwise composition interface for arbitrary complex normed parameter spaces. -/
theorem analyticAt_regCarlsonRSlit_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) :
    AnalyticAt ℂ (fun q => regCarlsonRSlit (t q) (b q) (z q)) p := by
  let f : E → Option (ι ⊕ ι) → ℂ := fun q k =>
    k.elim (t q) (Sum.elim (b q) (z q))
  have hf : AnalyticAt ℂ f p := by
    apply analyticAt_pi_iff.mpr
    intro k
    cases k with
    | none => exact ht
    | some k =>
      cases k with
      | inl i => exact (analyticAt_pi_iff.mp hb) i
      | inr i => exact (analyticAt_pi_iff.mp hz) i
  exact (analyticOnNhd_regCarlsonRSlit_joint (f p) hslit).comp_of_eq hf rfl

/-- The ordinary, unregularized function is jointly analytic wherever the total parameter
avoids the Gamma poles. The regularized theorem above has no such exclusion. -/
theorem analyticAt_carlsonRSlit_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (hc : ∀ n : ℕ, (∑ i, b p i) ≠ -n) :
    AnalyticAt ℂ (fun q => carlsonRSlit (t q) (b q) (z q)) p := by
  have hsum : AnalyticAt ℂ (fun q => ∑ i, b q i) p :=
    Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i
  have hrecip := (differentiable_one_div_Gamma.analyticAt (∑ i, b p i)).comp_of_eq hsum rfl
  have hgamma : AnalyticAt ℂ (fun q => Gamma (∑ i, b q i)) p := by
    have h := hrecip.inv (inv_ne_zero (Gamma_ne_zero hc))
    change AnalyticAt ℂ (fun q => ((Gamma (∑ i, b q i))⁻¹)⁻¹) p at h
    simpa only [inv_inv] using h
  exact hgamma.mul (analyticAt_regCarlsonRSlit_comp ht hb hz hslit)

end DirichletTransform
