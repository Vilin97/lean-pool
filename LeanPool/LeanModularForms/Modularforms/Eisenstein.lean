/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.Eisensteinqexpansions
public import LeanPool.LeanModularForms.Modularforms.IsCuspForm
public import LeanPool.LeanModularForms.Modularforms.SummableLems

/-! # Eisenstein -/


@[expose] public section

open ModularForm hiding E₄ E₆
open LevelOneEisenstein
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

noncomputable section

/-! ## Helper lemmas for dimension-one arguments -/

/-- In a rank-one module, every element is a scalar multiple of any nonzero element. -/
lemma exists_smul_eq_of_rank_one {M : Type*} [AddCommGroup M] [Module ℂ M]
    (hrank : Module.rank ℂ M = 1) {e : M} (he : e ≠ 0) (f : M) : ∃ c : ℂ, f = c • e := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' e he).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) f
  exact ⟨c, hc.symm⟩


/-- Symmetric version: `c • e = f` instead of `f = c • e`. -/
lemma exists_smul_eq_of_rank_one' {M : Type*} [AddCommGroup M] [Module ℂ M]
    (hrank : Module.rank ℂ M = 1) {e : M} (he : e ≠ 0) (f : M) : ∃ c : ℂ, c • e = f :=
  (finrank_eq_one_iff_of_nonzero' e he).mp (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) f

/-- Convert smul equality of modular forms to pointwise equality. -/
lemma smul_modularForm_eq_pointwise {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f g : ModularForm Γ k}
    {c : ℂ} (h : f = c • g) (z : ℍ) : (f : ℍ → ℂ) z = c * (g : ℍ → ℂ) z := by
  simpa [ModularForm.coe_smul, smul_eq_mul] using
    congrFun (congrArg (↑· : ModularForm _ _ → ℍ → ℂ) h) z

section Definitions

/- The Eisenstein Series E₄ and E₆ -/

/-- The normalized weight-4 Eisenstein series `E₄`. -/
def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  (1/2 : ℂ) • eisensteinSeriesMF (by norm_num) standardcongruencecondition /-they need 1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/

/-- The normalized weight-6 Eisenstein series `E₆`. -/
def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  (1/2 : ℂ) • eisensteinSeriesMF (by norm_num) standardcongruencecondition

lemma E4_eq : E₄ = E 4 (by norm_num) := rfl

lemma E6_eq : E₆ = E 6 (by norm_num) := rfl

lemma E4_apply (z : ℍ) : E₄ z = E 4 (by norm_num) z := rfl

lemma E6_apply (z : ℍ) : E₆ z = E 6 (by norm_num) z := rfl

/-- E₄ is 1-periodic: E₄(z + 1) = E₄(z). This follows from E₄ being a modular form for Γ(1). -/
lemma E₄_periodic (z : ℍ) : E₄ ((1 : ℝ) +ᵥ z) = E₄ z := by
  simpa using SlashInvariantForm.vAdd_width_periodic 1 4 1 E₄.toSlashInvariantForm z

/-- E₆ is 1-periodic: E₆(z + 1) = E₆(z). This follows from E₆ being a modular form for Γ(1). -/
lemma E₆_periodic (z : ℍ) : E₆ ((1 : ℝ) +ᵥ z) = E₆ z := by
  simpa using SlashInvariantForm.vAdd_width_periodic 1 6 1 E₆.toSlashInvariantForm z

/-- A level-one modular form transforms under `S` as `g(-1/z) = z^k · g(z)`. -/
private lemma modularForm_gammaOne_S_transform {k : ℕ}
    (g : ModularForm (CongruenceSubgroup.Gamma 1) k) (z : ℍ) :
    g (ModularGroup.S • z) = z ^ k * g z := by
  have h : (g.toFun ∣[(k : ℤ)] ModularGroup.S) z = g.toFun z := by
    apply congrFun
    apply g.slash_action_eq'
    simp only [Subgroup.mem_map, CongruenceSubgroup.mem_Gamma_one]
    use ModularGroup.S
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg, ModularForm.toFun_eq_coe] at h
  field_simp [ne_zero z] at h
  exact h

/-- E₄ transforms under S as: E₄(-1/z) = z⁴ · E₄(z) -/
lemma E₄_S_transform (z : ℍ) : E₄ (ModularGroup.S • z) = z ^ (4 : ℕ) * E₄ z :=
  modularForm_gammaOne_S_transform E₄ z

/-- E₆ transforms under S as: E₆(-1/z) = z⁶ · E₆(z) -/
lemma E₆_S_transform (z : ℍ) : E₆ (ModularGroup.S • z) = z ^ (6 : ℕ) * E₆ z :=
  modularForm_gammaOne_S_transform E₆ z

variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)

end Definitions

open Complex Real

noncomputable section

/- φ₀, φ₋₂ and φ₋₄, except we can't use - signs in subscripts for definitions... -/
/-- The auxiliary quotient `((E₂ E₄ - E₆) ^ 2) / Δ` on the upper half-plane. -/
def φ₀ (z : ℍ) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)
/-- The auxiliary quotient `E₄ (E₂ E₄ - E₆) / Δ` on the upper half-plane. -/
def φ₂' (z : ℍ) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)
/-- The auxiliary quotient `E₄ ^ 2 / Δ` on the upper half-plane. -/
def φ₄' (z : ℍ) := ((E₄ z) ^ 2) / (Δ z)
/- We extend these definitions to ℂ for convenience. -/
/-- The extension of `φ₀` to all of `ℂ`, set to `0` off the upper half-plane. -/
def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0
/-- The extension of `φ₂'` to all of `ℂ`, set to `0` off the upper half-plane. -/
def φ₂'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₂' ⟨z, hz⟩ else 0
/-- The extension of `φ₄'` to all of `ℂ`, set to `0` off the upper half-plane. -/
def φ₄'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₄' ⟨z, hz⟩ else 0

lemma φ₀''_def {z : ℂ} (hz : 0 < z.im) : φ₀'' z = φ₀ ⟨z, hz⟩ := by simp [φ₀'', hz]

lemma φ₀''_mem_upperHalfPlane {z : ℂ} (hz : z ∈ upperHalfPlaneSet) : φ₀'' z = φ₀ ⟨z, hz⟩ :=
  φ₀''_def hz

lemma φ₀''_coe_upperHalfPlane (z : ℍ) : φ₀'' (z : ℂ) = φ₀ z := by
  simpa using (φ₀''_def (z := (z : ℂ)) (UpperHalfPlane.im_pos z))

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

local notation "𝕢" => Periodic.qParam

theorem cuspfunc_lim_coef {k : ℤ} {F : Type u_1} [inst : FunLike F ℍ ℂ] (n : ℕ) (c : ℕ → ℂ) (f : F)
  [inst_1 : ModularFormClass F Γ(n) k] [inst_2 : NeZero n] (hf : ∀ (τ : ℍ), HasSum (fun m ↦ c m • 𝕢
    ↑n ↑τ ^ m) (f τ))
  (q : ℂ) (hq : ‖q‖ < 1) (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction n f q) := by
  have hq2 := Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := n)
    (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) hq hq1
  have hft := hf ⟨(Periodic.invQParam (↑n) q), hq2⟩
  have := eq_cuspFunction (h := n) (f := ⇑f)
    ⟨(Periodic.invQParam (↑n) q), hq2⟩ (by simp [inst_2.1])
    (SlashInvariantFormClass.periodic_comp_ofComplex f (by simp))
  simp only [smul_eq_mul, ne_eq] at *
  rw [Function.Periodic.qParam_right_inv] at this hft
  · rw [← this] at hft
    exact hft
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne n
  · exact hq1
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne n
  · exact hq1

theorem summable_zero_pow {G : Type*} [NormedField G] (f : ℕ → G) :
    Summable fun m ↦ f m * 0 ^ m := by
  simp [← summable_nat_add_iff 1]

lemma tsum_zero_pow (f : ℕ → ℂ) : (∑' m, f m * 0 ^ m) = f 0 := by
  simp [Summable.tsum_eq_zero_add (summable_zero_pow f)]

lemma cuspfunc_Zero [hn : NeZero n] [ModularFormClass F Γ(n) k] : cuspFunction n f 0 =
    (qExpansion n f).coeff 0 := by
  have hnpos : (0 : ℝ) < n := by have := hn.1; positivity
  have hΓ : (↑n : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(n)).strictPeriods := by
    simp
  haveI : Fact (IsCusp OnePoint.infty
      (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(n))) :=
    ⟨(Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(n)).isCusp_of_mem_strictPeriods
      hnpos hΓ⟩
  have := UpperHalfPlane.hasSum_qExpansion_of_norm_lt (h := n) (q := 0)
    hnpos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) (by simp)
  simp only [smul_eq_mul] at this
  rw [Summable.hasSum_iff] at this
  · rw [tsum_zero_pow] at this
    apply this.symm
  exact summable_zero_pow _

lemma modfom_q_exp_cuspfunc (c : ℕ → ℂ) (f : F) [ModularFormClass F Γ(n) k] [NeZero n]
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 n τ ^ m) (f τ)) : ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun m : ℕ ↦ c m • q ^ m) (cuspFunction n f q) := by
  intro q hq
  by_cases hq1 : q ≠ 0
  · apply cuspfunc_lim_coef n c f hf q hq hq1
  · have h2 : cuspFunction n f 0 = c 0 := by
      rw [cuspFunction, Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
      apply Filter.Tendsto.limUnder_eq
      have := cuspfunc_lim_coef n c f hf
      rw [cuspFunction] at this
      have htt : Tendsto (fun q => ∑' m, c m * q ^ m) (𝓝[≠] 0) (𝓝 (c 0)) := by
        have hD := tendsto_tsum_of_dominated_convergence (𝓕 := (𝓝[≠] (0 : ℂ)))
          (f := fun q : ℂ => fun m : ℕ => c m * q ^ m) (g := fun m : ℕ => c m * 0 ^ m)
          (bound := fun m => ‖c m‖ * (1 / 2 ) ^ m ) ?_ ?_ ?_
        · convert hD
          rw [tsum_zero_pow]
        · have ht3 := (this (1/2) (by norm_num)
            (by apply one_div_ne_zero; exact Ne.symm (NeZero.ne' 2))).summable.norm
          simpa using ht3
        · intro k
          apply Tendsto.const_mul
          have := ((continuous_pow k (M := ℂ) ).tendsto) 0
          apply Filter.Tendsto.mono_left this
          exact nhdsWithin_le_nhds
        rw [eventually_iff_exists_mem]
        use {z | (z : ℂ) ≠ 0 ∧ ‖z‖ < 1 / 2}
        constructor
        · rw [@mem_nhdsWithin_iff]
          refine ⟨1/2, by norm_num, ?_⟩
          intro y hy
          simp only [smul_eq_mul, ne_eq, Decidable.not_not, one_div,
            mem_inter_iff, mem_ball, dist_zero_right, mem_compl_iff, mem_singleton_iff,
            mem_setOf_eq] at *
          refine ⟨hy.2, hy.1⟩
        · intro y hy k
          simp only [norm_mul, norm_pow, one_div, inv_pow]
          gcongr
          have hy2 := hy.2.le
          rw [← inv_pow]
          gcongr
          simpa only [ one_div] using hy2
      apply htt.congr'
      rw [@eventuallyEq_nhdsWithin_iff, eventually_nhds_iff_ball]
      use 1
      simp only [gt_iff_lt, zero_lt_one, mem_ball, dist_zero_right,
        mem_compl_iff, mem_singleton_iff, true_and]
      intro y hy hy0
      exact (this y hy hy0).tsum_eq
    simp only [ne_eq, Decidable.not_not] at hq1
    simp_rw [hq1]
    rw [h2]
    simp only [smul_eq_mul]
    rw [Summable.hasSum_iff]
    · apply tsum_zero_pow
    exact summable_zero_pow _


lemma qParam_surj_onto_ball (r : ℝ) (hr : 0 < r) (hr2 : r < 1) [NeZero n] : ∃ (z : ℍ), ‖𝕢 n z‖ = r
    := by
  use ⟨(Periodic.invQParam n r), ?_⟩
  · have hq := Function.Periodic.qParam_right_inv (h := n) (q := r) ?_ ?_
    · rw [hq]
      simp [hr.le]
    · exact Ne.symm (NeZero.ne' _)
    simpa only [ne_eq, ofReal_eq_zero] using ne_of_gt hr
  rw [Function.Periodic.im_invQParam]
  simp only [norm_real, norm_eq_abs, log_abs]
  rw [mul_pos_iff]
  right
  constructor
  · refine div_neg_of_neg_of_pos ?_ ?_
    · simp only [Left.neg_neg_iff, Nat.cast_pos]
      exact Nat.pos_of_neZero n
    exact two_pi_pos
  rw [propext (log_neg_iff hr)]
  exact hr2


lemma q_exp_unique (c : ℕ → ℂ) (f : ModularForm Γ(n) k) [hn : NeZero n]
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 n τ ^ m) (f τ)) :
    c = (fun m => (qExpansion n f).coeff m) := by
  ext m
  have hnpos : (0 : ℝ) < n := by have := hn.1; positivity
  have h := hasFPowerSeries_cuspFunction (h := n) (c := c) f hnpos
    (ModularFormClass.analyticAt_cuspFunction_zero f hnpos (by simp)) hf
  let qExpansion2 : PowerSeries ℂ := .mk fun m ↦ c m
  let qq : FormalMultilinearSeries ℂ ℂ ℂ :=
    fun m ↦ (qExpansion2).coeff m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m _
  have hqq2 : ∀ m , ‖qq m‖ = ‖(qExpansion2).coeff m‖ := by
    intro m
    simp only [qq]
    rw [
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
    simp only [_root_.map_smul, smul_eq_mul, norm_mul,
      LinearIsometryEquiv.norm_map, ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
  have H2 : HasFPowerSeriesOnBall (cuspFunction n f) qq 0 1 := by
    have H21 : 1 ≤ qq.radius := by
        refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
        lift r to NNReal using hr.ne_top
        apply FormalMultilinearSeries.le_radius_of_summable
        conv =>
          enter [1]
          intro n
          rw [hqq2]
        simp only [PowerSeries.coeff_mk, qExpansion2]
        by_cases hr0 : r = 0
        · rw [hr0]
          apply summable_zero_pow
        obtain ⟨z, hz⟩ := qParam_surj_onto_ball n r
          (by simp only [NNReal.coe_pos]; exact pos_iff_ne_zero.mpr hr0)
          (by simpa using hr)
        rw [← hz]
        have hfz := summable_norm_iff.mpr (hf z).summable
        simpa using hfz
    refine ⟨H21 , zero_lt_one, ?_⟩
    intro y hy
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff, ←
      NNReal.coe_lt_one,
    coe_nnnorm] at hy
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, zero_add]
    have := modfom_q_exp_cuspfunc n c f hf y hy
    apply this.congr
    intro S
    congr
    ext b
    simp only [smul_eq_mul, PowerSeries.coeff_mk, qq, qExpansion2]
    rw [mul_comm]
    congr
    rw [FormalMultilinearSeries.coeff.eq_1 ]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      smul_eq_mul]
    rw [@Fin.prod_ofFn]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
  have h3 : HasFPowerSeriesAt (cuspFunction n f) qq 0 := by
    rw [HasFPowerSeriesAt]
    use 1
  have h4 : HasFPowerSeriesAt (cuspFunction n f) (qExpansionFormalMultilinearSeries n f) 0 := by
    rw [HasFPowerSeriesAt]
    use 1
  have := HasFPowerSeriesAt.eq_formalMultilinearSeries h3 h4
  rw [@FormalMultilinearSeries.ext_iff] at this
  have h5 := this m
  simp only [PowerSeries.coeff_mk, qExpansionFormalMultilinearSeries, qq, qExpansion2] at h5
  have htv : c m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ =
      (PowerSeries.coeff m) (qExpansion n f) • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ := by
    calc
      _ = FormalMultilinearSeries.ofScalars ℂ (fun m ↦ (PowerSeries.coeff m) (qExpansion n f)) m :=
          h5
      _ = (PowerSeries.coeff m) (qExpansion n f) • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ :=
          by simp [FormalMultilinearSeries.ofScalars]
  have h6 := congrArg
    (fun g : ContinuousMultilinearMap ℂ (fun _ : Fin m => ℂ) ℂ => g (fun _ => (1 : ℂ))) htv
  simpa [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply]
    using h6

lemma deriv_mul_eq (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    deriv (f * g) = deriv f * g + f * deriv g :=
  funext fun y => deriv_mul (hf y) (hg y)

lemma auxasdf (n : ℕ) : (PowerSeries.coeff n) ((qExpansion 1 E₄) * (qExpansion 1 E₆)) =
    ∑ p ∈ Finset.antidiagonal n, (PowerSeries.coeff p.1)
    ((qExpansion 1 E₄)) * (PowerSeries.coeff p.2) ((qExpansion 1 E₆)) := by
  apply PowerSeries.coeff_mul

lemma sigma_bound (k n : ℕ) : σ k n ≤ n ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_apply]
  have : ∑ d ∈ n.divisors, d ^ k ≤ ∑ d ∈ n.divisors, n ^ k := by
    apply Finset.sum_le_sum
    intro i hi
    gcongr
    exact Nat.divisor_le hi
  apply le_trans this
  simp only [Finset.sum_const, smul_eq_mul]
  rw [pow_add, mul_comm]
  gcongr
  simpa only [pow_one] using Nat.card_divisors_le_self n

/-- The `q`-expansion coefficients of the weight-`k` Eisenstein series. -/
def EkQ (k : ℕ) : ℕ → ℂ := fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m)

lemma qexpsummable (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
  Summable fun m ↦ EkQ k m • 𝕢 ↑1 ↑z ^ m := by
  rw [← summable_nat_add_iff 1]
  simp only [EkQ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, one_div, neg_mul,
    Periodic.qParam, ofReal_one, div_one, smul_eq_mul]
  conv =>
    enter [1]
    ext m
    rw [mul_assoc]
  apply Summable.mul_left
  rw [ArithmeticFunction.sigma]
  simp only [ArithmeticFunction.coe_mk, Nat.cast_sum, Nat.cast_pow]
  apply Summable.of_norm
  have hs : Summable fun a : ℕ ↦ ((a + 1) ^ k) * ‖cexp (2 * ↑π * Complex.I * ↑z) ^ (a + 1)‖ := by
    conv =>
      enter [1]
      ext a
      rw [show ((a : ℝ) + 1) = ((a + 1) : ℕ) by simp]
    have := summable_nat_add_iff 1
        (f := fun a : ℕ ↦ (((a) : ℝ) ^ k) * ‖cexp (2 * ↑π * Complex.I * ↑z) ^ (a)‖)
    simp only [Nat.ofNat_le_cast, Nat.cast_add, Nat.cast_one, norm_pow] at *
    rw [this]
    have ht : ‖cexp (2 * ↑π * Complex.I * ↑z)‖ < 1 := norm_exp_two_pi_I_lt_one z
    have := summable_norm_pow_mul_geometric_of_norm_lt_one k ht
    simp only [Complex.norm_mul, norm_pow, RCLike.norm_natCast] at *
    apply this
  apply Summable.of_nonneg_of_le _ _ hs
  · simp
  intro b
  simp only [Nat.ofNat_le_cast, norm_pow, Complex.norm_mul, norm_pos_iff, ne_eq,
    Complex.exp_ne_zero, not_false_eq_true, pow_succ_pos, mul_le_mul_iff_left₀] at *
  have hr : ‖∑ x ∈ (b + 1).divisors, (x : ℂ) ^ (k - 1)‖ ≤
    ‖∑ x ∈ (b + 1).divisors, ((b + 1) : ℂ) ^ (k - 1)‖ := by
    apply le_trans (norm_sum_le (b + 1).divisors _ )
    simp only [norm_pow, Complex.norm_natCast, Finset.sum_const, nsmul_eq_mul, Complex.norm_mul]
    have h2 : ∑ x ∈ (b + 1).divisors, (x : ℝ) ^ (k - 1) ≤
      ∑ x ∈ (b + 1).divisors, (b + 1) ^ (k - 1) := by
      norm_cast
      apply Finset.sum_le_sum
      intro i hi
      simp only [Nat.mem_divisors, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, and_true] at *
      refine Nat.pow_le_pow_left ?_ (k - 1)
      apply Nat.le_of_dvd _ hi
      omega
    apply le_trans h2
    simp only [Finset.sum_const, smul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, Nat.cast_pos, Finset.card_pos, Nat.nonempty_divisors, ne_eq,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, mul_le_mul_iff_right₀]
    norm_cast
  apply le_trans hr
  simp only [Finset.sum_const, nsmul_eq_mul, Complex.norm_mul, RCLike.norm_natCast, norm_pow]
  norm_cast
  nth_rw 2 [show k = 1 + (k - 1) by omega]
  rw [pow_add]
  gcongr
  simp
  simpa using Nat.card_divisors_le_self (b + 1)


/-- The `EkQ`-style coefficients give the `q`-expansion `HasSum` for `E k hk`. -/
private lemma Ek_hasSum (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    HasSum (fun m : ℕ ↦ (if m = 0 then 1 else
      (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m)) •
      𝕢 ((1 : ℕ) : ℝ) ↑z ^ m) (E k hk z) := by
  let c : ℕ → ℂ := fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m)
  change HasSum (fun m : ℕ ↦ c m • 𝕢 ((1 : ℕ) : ℝ) ↑z ^ m) (E k hk z)
  have := E_k_q_expansion k hk hk2 z
  rw [Summable.hasSum_iff]
  · simp only [one_div, neg_mul] at this
    rw [this, tsum_eq_zero_add']
    · have V := tsum_pnat_eq_tsum_succ (f := fun b => c (b) • 𝕢 ↑1 ↑z ^ (b))
      simp only [smul_eq_mul, Nat.cast_one, pow_zero, mul_one] at *
      rw [← V]
      simp only [one_div, neg_mul, ↓reduceIte, PNat.ne_zero, add_right_inj, c]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro b
      ring_nf
      field_simp
      congr
      rw [Function.Periodic.qParam, ← Complex.exp_nsmul]
      congr
      simp
      ring
    have hr := (summable_nat_add_iff 1 (f := fun n : ℕ ↦ c (n) • 𝕢 (1 : ℝ) ↑z ^ (n)))
    simp only [smul_eq_mul, Nat.cast_one] at *
    rw [hr]
    have := qexpsummable k hk z
    simp only [one_div, neg_mul, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, ite_mul,
      one_mul, EkQ, smul_eq_mul, c] at *
    apply this
  have := qexpsummable k hk z
  simp only [one_div, neg_mul, EkQ, smul_eq_mul, ite_mul, one_mul, Nat.cast_one, c] at *
  apply this

lemma Ek_q_exp_zero (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : (qExpansion 1 (E k hk)).coeff 0 =
    1 := by
  let c : ℕ → ℂ := fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m)
  have h := q_exp_unique 1 c (E k hk) (fun z => Ek_hasSum k hk hk2 z)
  have hc := congr_fun h 0
  rw [Nat.cast_one] at hc
  simp [← hc, c]

lemma Ek_q_exp (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    (fun m => (qExpansion 1 (E k hk)).coeff m) =
    fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m) := by
  let c : ℕ → ℂ := fun m => if m = 0 then 1 else
      (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m)
  have h := q_exp_unique 1 c (E k hk) (fun z => Ek_hasSum k hk hk2 z)
  rw [← Nat.cast_one (R := ℝ), ← h]

lemma E4_q_exp : (fun m => (qExpansion 1 E₄).coeff m) =
    fun m => if m = 0 then 1 else (240 : ℂ) * (σ 3 m) := by
  have HH := Ek_q_exp 4 (by norm_num) (Nat.even_iff.mpr rfl)
  rw [E4_eq]
  simp only [Nat.cast_ofNat, one_div, neg_mul, Nat.add_one_sub_one] at *
  rw [HH]
  have Z := riemannZeta_two_mul_nat (k := 2) (by norm_num)
  simp only [Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceMul, Nat.add_one_sub_one] at Z
  rw [ show 2 * 2 = (4 : ℂ) by ring] at Z
  rw [Z]
  ext m
  simp_all only [inv_div]
  split
  next h =>
    subst h
    simp_all only
  next h =>
    simp_all only [mul_eq_mul_right_iff, Nat.cast_eq_zero]
    left
    simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, mul_one, Nat.reduceMul,
      Nat.cast_ofNat, bernoulli, bernoulli'_four, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
      Rat.cast_one, Rat.cast_div, Rat.cast_ofNat]
    ring_nf
    rw [Complex.I_pow_four ]
    have pin : (π : ℂ) ≠ 0 := by simp
    field_simp

lemma E4_q_exp_zero : (qExpansion 1 E₄).coeff 0 = 1 := by simpa using congr_fun E4_q_exp 0

@[simp]
theorem Complex.I_pow_six : Complex.I ^ 6 = -1 := by
  rw [(by norm_num : 6 = 2 * 3), pow_mul, I_sq]
  ring

@[simp]
theorem bernoulli'_five : bernoulli' 5 = 0 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    show Nat.choose 5 2 = 10 from by decide]

@[simp]
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h1 : Nat.choose 6 4 = 15 := by decide -- shrug
  have h2 : Nat.choose 6 2 = 15 := by decide -- shrug
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, h1, h2]

lemma E6_q_exp : (fun m => (qExpansion 1 E₆).coeff m) =
    fun m => if m = 0 then 1 else -(504 : ℂ) * (σ 5 m) := by
  have HH := Ek_q_exp 6 (by norm_num) (Nat.even_iff.mpr rfl)
  rw [E6_eq]
  simp only [Nat.cast_ofNat, one_div, neg_mul, Nat.add_one_sub_one] at *
  rw [HH]
  have Z := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  simp only [Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceMul, Nat.add_one_sub_one] at Z
  rw [ show 2 * 3 = (6 : ℂ) by ring] at Z
  rw [Z]
  ext m
  simp_all only [inv_div]
  split
  · rfl
  simp only [bernoulli, bernoulli'_six, one_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, Rat.cast_inv, Rat.cast_ofNat, Nat.factorial,
    Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, mul_one, Nat.reduceMul, Nat.cast_ofNat]
  ring_nf
  rw [Complex.I_pow_six ]
  have pin : (π : ℂ) ≠ 0 := by simp
  field_simp

lemma E6_q_exp_zero : (qExpansion 1 E₆).coeff 0 = 1 := by simpa using congr_fun E6_q_exp 0

theorem E4E6_coeff_zero_eq_zero :
  (PowerSeries.coeff 0)
      (qExpansion 1
        ((1 / 1728 : ℂ) • ((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3 - (DirectSum.of (ModularForm
          Γ(1)) 6) E₆ ^ 2) 12)) =
    0 := by
  simp only [one_div, DirectSum.sub_apply]
  have hsub :
      qExpansion (1 : ℕ)
        ⇑((((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) -
          (((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12)) =
      qExpansion 1 (((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) -
        qExpansion 1 (((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12) := by
    simpa using
      (ModularForm.qExpansion_sub (h := (1 : ℕ))
        (hh := by positivity) (hΓ := by simp)
        ((((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12))
        ((((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12)))
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2, hsub]
  simp only [_root_.map_smul, map_sub, smul_eq_mul,
    mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  have hds : (((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) = E₄.mul (E₄.mul E₄) := by
    ext z
    rw [pow_three, @DirectSum.of_mul_of, DirectSum.of_mul_of]
    change (((DirectSum.of (ModularForm Γ(1)) 12)
        (GradedMonoid.GMul.mul E₄ (GradedMonoid.GMul.mul E₄ E₄))) 12) z = _
    rw [DirectSum.of_eq_same]; rfl
  have hd6 : ((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12 = E₆.mul E₆ := by
    ext z
    rw [pow_two, @DirectSum.of_mul_of]
    change (((DirectSum.of (ModularForm Γ(1)) 12)
        (GradedMonoid.GMul.mul E₆ E₆)) 12) z = _
    rw [DirectSum.of_eq_same]; rfl
  have hq4 : qExpansion 1 ⇑(((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) =
      qExpansion 1 (E₄.mul (E₄.mul E₄)) := congrArg _ (congrArg _ hds)
  have hq6 : qExpansion 1 ⇑(((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12) =
      qExpansion 1 (E₆.mul E₆) := congrArg _ (congrArg _ hd6)
  rw [hq4, hq6, ← Nat.cast_one (R := ℝ),
    qExpansion_mul_coeff, qExpansion_mul_coeff, qExpansion_mul_coeff, PowerSeries.coeff_mul,
    PowerSeries.coeff_mul]
  simp only [Finset.antidiagonal_zero, Prod.mk_zero_zero, Finset.sum_singleton, Prod.fst_zero,
    Prod.snd_zero]
  rw [Nat.cast_one]
  simp_rw [E4_q_exp_zero, E6_q_exp_zero]
  rw [PowerSeries.coeff_mul]
  simp only [Finset.antidiagonal_zero, Prod.mk_zero_zero, Finset.sum_singleton, Prod.fst_zero,
    Prod.snd_zero, one_mul, mul_one]
  rw [E4_q_exp_zero]
  simp

/-- The discriminant cusp form built from `E₄` and `E₆` via `(E₄ ^ 3 - E₆ ^ 2) / 1728`. -/
def DeltaE4E6Aux : CuspForm (CongruenceSubgroup.Gamma 1) 12 :=
  let F := DirectSum.of _ 4 E₄
  let G := DirectSum.of _ 6 E₆
  cuspFormOfCoeffZero ((1 / 1728 : ℂ) • (F ^ 3 - G ^ 2) 12) E4E6_coeff_zero_eq_zero

lemma Delta_cuspFuntion_eq : Set.EqOn (cuspFunction 1 Delta)
     (fun y => (y : ℂ) * ∏' i, ((1 : ℂ) - y ^ (i + 1)) ^ 24) (Metric.ball 0 (1/2)) := by
  rw [cuspFunction]
  intro y hy
  by_cases hyn0 : y = 0
  · rw [hyn0]
    simp
    have := CuspFormClass.cuspFunction_apply_zero (h := 1) Delta zero_lt_one (by simp)
    rw [cuspFunction] at this
    simpa using this
  · rw [Function.Periodic.cuspFunction_eq_of_nonzero]
    · simp only [comp_apply]
      have hz := Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := 1) (by exact
        Real.zero_lt_one) (q := y) ?_ ?_
      · rw [ofComplex_apply_of_im_pos hz]
        rw [Delta_apply, Δ]
        have hq := Function.Periodic.qParam_right_inv (h := 1) ?_ (q := y) hyn0
        · have : cexp (2 * ↑π * Complex.I * Periodic.invQParam 1 y) = y := by
            nth_rw 2 [← hq]
            congr 1
            simp
          rw [this]
          congr
          ext n
          congr
          have : cexp (2 * ↑π * Complex.I * (↑n + 1) * Periodic.invQParam 1 y) =
            (cexp (2 * ↑π * Complex.I * Periodic.invQParam 1 y)) ^ (n+1) := by
            rw [← Complex.exp_nsmul]
            congr
            ring
          rw [this]
          congr
        exact Ne.symm (zero_ne_one' ℝ)
      · simp only [one_div, mem_ball, dist_zero_right] at hy
        apply lt_trans hy
        linarith
      · exact hyn0
    exact hyn0

lemma Delta_ne_zero : Delta ≠ 0 :=
  DFunLike.ne_iff.mpr ⟨UpperHalfPlane.I, Δ_ne_zero UpperHalfPlane.I⟩

lemma asdf : TendstoLocallyUniformlyOn
    (fun n : ℕ ↦ fun y : ℂ => ∏ x ∈ Finset.range n, (1 - y ^ (x + 1)))
    (fun x : ℂ ↦ ∏' i, (1 - x ^ (i + 1))) atTop
    (Metric.ball (0 : ℂ) (1/2 : ℝ))
      := by
  have hclosed :
      TendstoUniformlyOn (fun n : ℕ ↦ fun y : ℂ => ∏ x ∈ Finset.range n, (1 - y ^ (x + 1)))
        (fun x : ℂ ↦ ∏' i, (1 - x ^ (i + 1))) atTop (Metric.closedBall (0 : ℂ) (1/2 : ℝ)) := by
    have hsum : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
      rw [@summable_nat_add_iff, summable_geometric_iff_norm_lt_one]
      simpa only [one_div, norm_inv, Real.norm_ofNat] using two_inv_lt_one
    simpa [sub_eq_add_neg] using
      (hsum.hasProdUniformlyOn_nat_one_add (f := fun n : ℕ => fun y : ℂ => -y ^ (n + 1))
        (hK := isCompact_closedBall (0 : ℂ) (1 / 2))
        (h := Filter.Eventually.of_forall (fun n (x : ℂ) hx => by
          have hx' : ‖x‖ ≤ (1 / 2 : ℝ) := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
          calc
            ‖-x ^ (n + 1)‖ = ‖x‖ ^ (n + 1) := by simp
            _ ≤ (1 / 2 : ℝ) ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg x) hx' _))
        (hcts := fun n => by fun_prop)).tendstoUniformlyOn_finsetRange
  exact TendstoLocallyUniformlyOn.mono (s := Metric.closedBall (0 : ℂ) (1/2 : ℝ))
    hclosed.tendstoLocallyUniformlyOn ball_subset_closedBall

theorem diffwithinat_prod_1 :
    DifferentiableWithinAt ℂ (fun (y : ℂ) ↦ ∏' (i : ℕ), (1 - y ^ (i + 1)) ^ 24) (ball 0 (1 / 2)) 0
    := by
  suffices DifferentiableWithinAt ℂ (fun (n : ℂ) ↦ (∏' (i : ℕ), (1 - n ^ (i + 1))) ^ 24) (ball 0 (1
    / 2)) 0 by
    apply this.congr
    · intro x hx
      rw [← tprod_pow _ (by
        apply multipliable_lt_one x
          (by
            simp only [one_div, mem_ball, dist_zero_right] at *
            apply lt_trans hx
            exact two_inv_lt_one))]
    simp
  apply DifferentiableWithinAt.pow
  have hu := asdf.differentiableOn ?_ ?_
  · apply hu
    simp
  · simp only [one_div, eventually_atTop]
    use 0
    intro b hb
    simpa [Finset.prod_fn] using
      (DifferentiableOn.finsetProd (u := Finset.range b)
        (f := fun x : ℕ => fun y : ℂ => 1 - y ^ (x + 1))
        (s := Metric.ball 0 (1 / 2)) (by
          intro i hi
          fun_prop))
  exact isOpen_ball


lemma Delta_q_one_term : (qExpansion 1 Delta).coeff 1 = 1 := by
  rw [qExpansion_coeff]
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, iteratedDeriv_one, one_mul]
  rw [← derivWithin_of_isOpen (s := Metric.ball 0 (1 / 2 : ℝ)) (isOpen_ball) (by simp),
    derivWithin_congr Delta_cuspFuntion_eq]
  · rw [derivWithin_fun_mul]
    · simp only [one_div, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, sub_zero, one_pow, tprod_one, mul_one, zero_mul, add_zero]
      have := derivWithin_id' ( 0 * ∏' (i : ℕ), (1 - 0 ^ (i + 1)) ^ 24 : ℂ)
        (Metric.ball 0 (1 / 2 : ℝ)) ?_
      · simp only [one_div, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, sub_zero, one_pow, tprod_one, mul_one] at *
        rw [this]
      simp only [one_div, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, sub_zero, one_pow, tprod_one, mul_one]
      apply IsOpen.uniqueDiffWithinAt
      · exact isOpen_ball
      refine mem_ball_self (by norm_num)
    · exact differentiableWithinAt_fun_id
    apply diffwithinat_prod_1
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    sub_zero, one_pow, tprod_one, mul_one]
  exact CuspFormClass.cuspFunction_apply_zero (h := 1) Delta zero_lt_one (by simp)

variable {α β γ : Type*}

variable [CommMonoid α] [TopologicalSpace α] [UniformSpace α]

lemma E4_q_exp_one : (qExpansion 1 E₄).coeff 1 = 240 := by
  have H := congr_fun E4_q_exp 1
  simpa only [one_ne_zero, ↓reduceIte, ArithmeticFunction.sigma_one, Nat.cast_one, mul_one] using H

lemma E6_q_exp_one : (qExpansion 1 E₆).coeff 1 = -504 := by
  have H := congr_fun E6_q_exp 1
  simpa only [one_ne_zero, ↓reduceIte, ArithmeticFunction.sigma_one, Nat.cast_one, mul_one] using H

lemma antidiagonal_one : Finset.antidiagonal 1 = {(1,0), (0,1)} := by
  decide

lemma E4_pow_q_exp_one : (qExpansion 1 ((E₄).mul ((E₄).mul E₄))).coeff 1 = 3 * 240 := by
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff, qExpansion_mul_coeff,
    PowerSeries.coeff_mul, antidiagonal_one]
  simp only [Nat.cast_one, Finset.mem_singleton, Prod.mk.injEq, one_ne_zero, zero_ne_one, and_self,
    not_false_eq_true, Finset.sum_insert, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    Finset.sum_singleton]
  rw [PowerSeries.coeff_mul, antidiagonal_one]
  have := E4_q_exp_zero
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, Finset.mem_singleton, Prod.mk.injEq,
    one_ne_zero, zero_ne_one, and_self, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton] at *
  simp_rw [E4_q_exp_one, this]
  ring

lemma Ek_ne_zero (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : E k hk ≠ 0 := by
  have hq := Ek_q_exp_zero k hk hk2
  intro h
  have hcoeff : PowerSeries.constantCoeff (qExpansion 1 (0 : ℍ → ℂ)) = 1 := by simpa [h] using hq
  have hqzero : PowerSeries.constantCoeff (qExpansion 1 (0 : ℍ → ℂ)) = 0 := by
    simpa using congrArg (fun p : PowerSeries ℂ => p.coeff 0)
      ((qExpansion_zero (h := (1 : ℕ))) : qExpansion 1 (0 : ℍ → ℂ) = 0)
  have : (0 : ℂ) = 1 := by simp [hqzero] at hcoeff
  exact zero_ne_one this

/-This is in the mod forms repo-/
lemma E4_ne_zero : E₄ ≠ 0 := Ek_ne_zero 4 (by norm_num) (Nat.even_iff.mpr rfl)

lemma E6_ne_zero : E₆ ≠ 0 := Ek_ne_zero 6 (by norm_num) (Nat.even_iff.mpr rfl)

lemma modularForm_normalise (f : ModularForm Γ(1) k) (hf : ¬ IsCuspForm Γ(1) k f) :
    (qExpansion 1 (((qExpansion 1 f).coeff 0)⁻¹ • f)).coeff 0 = 1 := by
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2, Nat.cast_one]
  refine inv_mul_cancel₀ ?_
  intro h
  rw [← (IsCuspForm_iff_coeffZero_eq_zero k f)] at h
  exact hf h

lemma PowerSeries.coeff_add (f g : PowerSeries ℂ) (n : ℕ) :
    (f + g).coeff n = (f.coeff n) + (g.coeff n) := rfl

open ArithmeticFunction

/-!
## Imaginary Axis Properties

Properties of Eisenstein series when restricted to the positive imaginary axis z = I*t.
-/

section ImagAxisProperties

open _root_.Complex hiding I

/-- `(-2πi)^k` is real for even k. -/
lemma neg_two_pi_I_pow_even_real (k : ℕ) (hk : Even k) :
    ((-2 * Real.pi * Complex.I) ^ k : ℂ).im = 0 := by
  have h : (-2 * Real.pi * Complex.I) ^ k = (-(2 * Real.pi) : ℂ) ^ k * Complex.I ^ k := by ring
  rw [h]
  have h1 : ((-(2 * Real.pi)) ^ k : ℂ).im = 0 := by norm_cast
  have h2 : (Complex.I ^ k : ℂ).im = 0 := by
    obtain ⟨m, rfl⟩ := hk
    simp only [← two_mul, pow_mul, I_sq]
    -- (-1)^m is real: ±1
    rcases m.even_or_odd with hm | hm <;> simp [hm.neg_one_pow]
  simp [Complex.mul_im, h1, h2]

/-- On imaginary axis z = I*t, the q-expansion exponent 2πi·n·z reduces to -(2πnt).
This is useful for reusing the same algebraic simplification across `E₂`, `E₄`, `E₆`. -/
lemma exp_imag_axis_arg (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    2 * Real.pi * Complex.I * (⟨Complex.I * t, by simp [ht]⟩ : ℍ) * n =
    (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
  push_cast
  ring_nf
  simp only [I_sq]
  ring

/-- `E_k(it)` is real for all `t > 0` when `k` is even and `k ≥ 4`.
This is the generalized theorem from which `E₄_imag_axis_real` and `E₆_imag_axis_real` follow. -/
theorem E_even_imag_axis_real (k : ℕ) (hk : (3 : ℤ) ≤ k) (hk2 : Even k) :
    ResToImagAxis.Real (E k hk).toFun := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E k hk z).im = 0
  have hq := E_k_q_expansion k hk hk2 z
  rw [hq]
  simp only [add_im, one_im, zero_add]
  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    intro n
    have hexp_arg : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      simpa [z] using exp_imag_axis_arg (t := t) ht n
    rw [hexp_arg]
    -- Using simp only: `simp` gives false positive linter warning but args are needed
    simp only [mul_im, exp_ofReal_im, natCast_im, mul_zero, zero_mul, add_zero]
  -- Step 2: Summability of the series
  have hsum : Summable fun n : ℕ+ => ↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    · intro n
      calc ‖↑((ArithmeticFunction.sigma (k - 1)) ↑n) * cexp (2 * ↑Real.pi * Complex.I * z * n)‖
          = ‖(↑((ArithmeticFunction.sigma (k - 1)) ↑n) : ℂ)‖ *
            ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := norm_mul _ _
        _ ≤ ‖(↑n : ℂ) ^ k‖ * ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
          apply mul_le_mul_of_nonneg_right
          · rw [Complex.norm_natCast, Complex.norm_pow, Complex.norm_natCast]
            have hbound := sigma_bound (k - 1) n
            have hk' : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
            rw [hk'] at hbound
            exact_mod_cast hbound
          · exact norm_nonneg _
        _ = ‖(↑n : ℂ) ^ k * cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := (norm_mul _ _).symm
    · have := a33 k 1 z
      simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at this
      exact summable_norm_iff.mpr this
  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    rw [im_tsum hsum]
    simp [hterm_im]
  -- Step 4: Show the coefficient is real and product with sum is real
  have hpow_im : ((-2 * Real.pi * Complex.I) ^ k : ℂ).im = 0 :=
    neg_two_pi_I_pow_even_real k hk2
  have hfact_im : ((k - 1).factorial : ℂ).im = 0 := by simp
  -- For ζ(k) when k ≥ 4, it's real (mathlib: riemannZeta_im_eq_zero_of_one_lt)
  have hzeta_im : (riemannZeta k).im = 0 := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) from by push_cast; ring]
    exact riemannZeta_im_eq_zero_of_one_lt (by exact_mod_cast show 1 < (k : ℤ) by omega)
  have hinv_zeta_im : (1 / riemannZeta k).im = 0 := by simp [hzeta_im]
  simp only [mul_im, div_im, hinv_zeta_im, hsum_im, hpow_im, hfact_im]
  ring

/-- `E₄(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₄_imag_axis_real : ResToImagAxis.Real E₄.toFun :=
  E_even_imag_axis_real 4 (by norm_num) (by decide)

/-- `E₆(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₆_imag_axis_real : ResToImagAxis.Real E₆.toFun :=
  E_even_imag_axis_real 6 (by norm_num) (by decide)

/-- `E₂(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₂_imag_axis_real : ResToImagAxis.Real E₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E₂ z).im = 0
  have hq := E₂_eq z
  rw [hq]
  simp only [sub_im, one_im, zero_sub]
  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    intro n
    have hexp_arg : 2 * ↑Real.pi * Complex.I * n * z = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      have h1 : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
        simpa [z] using exp_imag_axis_arg (t := t) ht n
      simpa [mul_assoc, mul_left_comm, mul_comm] using h1
    -- Using simp only: `simp` gives false positive linter warning but args are needed
    have hone_sub_real : (1 - cexp (2 * ↑Real.pi * Complex.I * ↑↑n * ↑z)).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im, hexp_arg, exp_ofReal_im, sub_zero]
    have hnum_real : (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z)).im = 0 := by
      simp only [mul_im, natCast_im, hexp_arg, exp_ofReal_im, mul_zero, zero_mul, add_zero]
    simp [Complex.div_im, hnum_real, hone_sub_real]
  -- Step 2: Summability of the series
  have hsum : Summable fun n : ℕ+ => ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z)) := by
    set r : ℂ := cexp (2 * ↑Real.pi * Complex.I * z) with hr
    have hr_norm : ‖r‖ < 1 := by simpa [hr] using exp_upperHalfPlane_lt_one z
    have hs : Summable fun n : ℕ => (n : ℂ) * r ^ n / (1 - r ^ n) := by
      simpa [pow_one] using
        (summable_norm_pow_mul_geometric_div_one_sub (k := 1) (r := r) hr_norm)
    refine (hs.comp_injective PNat.coe_injective).congr ?_
    intro n
    have hpow : r ^ (n : ℕ) = cexp (2 * ↑Real.pi * Complex.I * (↑n : ℂ) * z) := by
      rw [hr]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.exp_nat_mul (2 * ↑Real.pi * Complex.I * z) (n : ℕ)).symm
    simp [hpow]
  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    rw [Complex.im_tsum hsum]
    simp [hterm_im]
  -- Step 4: 24 * sum is real, so -(24 * sum).im = 0
  simp [Complex.mul_im, hsum_im]

end ImagAxisProperties

/-! ## Boundedness of E₂ -/

/-- For im(z) ≥ 1, ‖exp(2πiz)‖ ≤ exp(-2π).

This bound on the q-parameter is useful for estimating q-expansions when im(z) ≥ 1. -/
lemma norm_exp_two_pi_I_le_exp_neg_two_pi (z : ℍ) (hz : 1 ≤ z.im) :
    ‖cexp (2 * π * Complex.I * z)‖ ≤ Real.exp (-2 * π) := by
  have h : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
    rw [show (2 : ℂ) * ↑π * Complex.I * z = Complex.I * (2 * π * z) by ring]
    simp [Complex.I_re, Complex.I_im, mul_comm]
  rw [Complex.norm_exp, h, Real.exp_le_exp]
  nlinarith [Real.pi_pos]

/-- Bound on the q-series ∑ n·qⁿ/(1-qⁿ) that appears in E₂.

For ‖q‖ < 1, we have ‖∑ₙ₌₁ n·qⁿ/(1-qⁿ)‖ ≤ ‖q‖/(1-‖q‖)³.

The key estimates are:
- |1-qⁿ| ≥ 1-|q|ⁿ ≥ 1-|q| for n ≥ 1
- |n·qⁿ/(1-qⁿ)| ≤ n·|q|ⁿ/(1-|q|)
- ∑ n·rⁿ = r/(1-r)², so ∑ n·rⁿ/(1-r) = r/(1-r)³ -/
lemma norm_tsum_logDeriv_expo_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := by
  set r : ℝ := ‖q‖
  have hr_norm_lt_one : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg q)]
  have hsumm_nat : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm_lt_one
  have hsumm_majorant : Summable (fun n : ℕ+ => (n : ℝ) * r ^ (n : ℕ) / (1 - r)) := by
    simpa [div_eq_mul_inv] using
      (hsumm_nat.comp_injective PNat.coe_injective).mul_right (1 - r)⁻¹
  have hterm_bound : ∀ n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      n * r ^ (n : ℕ) / (1 - r) := fun n => by
    rw [norm_div, norm_mul, Complex.norm_natCast]
    have hdenom_lower : 1 - r ≤ ‖1 - q ^ (n : ℕ)‖ := calc
      1 - r ≤ 1 - r ^ (n : ℕ) := by
        have : r ^ (n : ℕ) ≤ r := pow_le_of_le_one (norm_nonneg _) hq.le n.ne_zero
        linarith
      _ = 1 - ‖q ^ (n : ℕ)‖ := by rw [norm_pow]
      _ ≤ ‖1 - q ^ (n : ℕ)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (q ^ (n : ℕ)); simp only [norm_one] at this; linarith
    calc ↑n * ‖q ^ (n : ℕ)‖ / ‖1 - q ^ (n : ℕ)‖ ≤ ↑n * ‖q ^ (n : ℕ)‖ / (1 - r) := by
          exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
            (sub_pos.mpr hq) hdenom_lower
      _ = ↑n * r ^ (n : ℕ) / (1 - r) := by rw [norm_pow]
  have hsumm_norms : Summable (fun n : ℕ+ => ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) hterm_bound hsumm_majorant
  calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ ∑' n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ := norm_tsum_le_tsum_norm hsumm_norms
    _ ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) :=
        hsumm_norms.tsum_le_tsum hterm_bound hsumm_majorant
    _ = r / (1 - r) ^ 3 := by
        simp only [div_eq_mul_inv, tsum_mul_right, tsum_pnat_coe_mul_geometric hr_norm_lt_one,
          pow_succ]
        field_simp

/-- Monotone version of `norm_tsum_logDeriv_expo_le`: if ‖q‖ ≤ r < 1, then
‖∑ n·qⁿ/(1-qⁿ)‖ ≤ r/(1-r)³. Useful when we have a uniform bound on ‖q‖. -/
lemma norm_tsum_logDeriv_expo_le_of_norm_le {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r < 1) :
    ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ r / (1 - r) ^ 3 := by
  have hq : ‖q‖ < 1 := lt_of_le_of_lt hqr hr
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg _) hqr
  calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := norm_tsum_logDeriv_expo_le hq
    _ ≤ r / (1 - r) ^ 3 := by
        have := sub_pos.mpr hr
        have := sub_pos.mpr hq
        gcongr

/-- E₂ is bounded at infinity.

Uses `E₂_eq`: E₂(z) = 1 - 24·Σₙ₌₁ n·qⁿ/(1-qⁿ) where q = exp(2πiz).
For im(z) ≥ 1, |q| ≤ exp(-2π), so by `norm_tsum_logDeriv_expo_le`,
|E₂| ≤ 1 + 24·exp(-2π)/(1-exp(-2π))³. -/
lemma E₂_isBoundedAtImInfty : IsBoundedAtImInfty E₂ := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  set r₀ : ℝ := Real.exp (-2 * π)
  have hr₀_lt_one : r₀ < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  refine ⟨1 + 24 * (r₀ / (1 - r₀) ^ 3), 1, fun z hz => ?_⟩
  rw [E₂_eq]
  set q : ℂ := cexp (2 * π * Complex.I * z)
  have hq_bound : ‖q‖ ≤ r₀ := norm_exp_two_pi_I_le_exp_neg_two_pi z hz
  -- Rewrite sum in terms of q^n
  set S := ∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))
  have hS_eq : ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z)) = S := by
    congr 1; ext n
    have : cexp (2 * π * Complex.I * n * z) = q ^ (n : ℕ) := by
      change _ = (cexp (2 * π * Complex.I * z)) ^ (n : ℕ)
      rw [← Complex.exp_nat_mul]; ring_nf
    simp [this]
  calc ‖1 - 24 * ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
          (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖
      = ‖1 - 24 * S‖ := by rw [hS_eq]
    _ ≤ 1 + 24 * ‖S‖ := by
        calc _ ≤ ‖(1 : ℂ)‖ + ‖24 * S‖ := norm_sub_le _ _
          _ = _ := by simp
    _ ≤ 1 + 24 * (r₀ / (1 - r₀) ^ 3) := by
        gcongr; exact norm_tsum_logDeriv_expo_le_of_norm_le hq_bound hr₀_lt_one

/-- E₄ is bounded at infinity (as a modular form). -/
lemma E₄_isBoundedAtImInfty : IsBoundedAtImInfty E₄.toFun :=
  ModularFormClass.bdd_at_infty E₄

/-- The product E₂ · E₄ is bounded at infinity. -/
lemma E₂_mul_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (E₂ * E₄.toFun) :=
  E₂_isBoundedAtImInfty.mul E₄_isBoundedAtImInfty
