/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.FlowForErgodicBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowBoundsAtScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.TimeIncrement.FlowBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.FlowGrad

/-! # Flow near-identity on `supp ξ_{m,k}` (`e.Xm.bound.1`, `e.Xm.bound.2`)

For `t` in the support of `ξ_{m,k}` the flow time `t - l_k τ''_m` is at most `τ''_m`, which is
at most `2^{-25} ε_{m-1}^{2-β+2δ}`. The Section 2 flow bounds at level `m - 1` therefore give
`‖∇X⁻¹ - I‖, ‖∇X - I‖ ≤ 2^{23} |t - l_k τ''_m| a_{m-1} ≤ ε_{m-1}^{2δ} / 4`, entrywise, together
with the second-derivative bound `2^16 ε_{m-1}⁻¹` for the flow slice.

All statements are unconditional: only `IsStreamSeq I Φ` is assumed.
-/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Construction

theorem LeadingErrorFlow.eps_pos {β : ℝ} (I : Ingredients β) (n : ℕ) : 0 < epsilon β I.Λ n :=
  Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt (by exact_mod_cast I.two_pow_seven_le)

theorem LeadingErrorFlow.xiMK_ne_zero_abs_le
    {β : ℝ} (I : Ingredients β) (m : ℕ) {k : ℤ} {t : ℝ}
    (hne : I.xiMK m k t ≠ 0) :
    |t - (k : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m := by
  have hτ := I.tau_pos' m
  set u := (t - k * tau β I.Λ m) / tau β I.Λ m with hu
  have hmem : u ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) := by
    by_contra hnot
    apply hne
    have h1 := I.xi_le_ind u
    have h2 := I.ind_le_xi u
    rw [indIcc_eq_zero_of_not_mem hnot] at h1
    have h3 := indIcc_nonneg' (-(3 / 4)) (3 / 4) u
    exact le_antisymm h1 (h3.trans h2)
  have habs : |u| ≤ 5 / 4 := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [hu, abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at habs
  linarith

/-- Refined window: on `supp ξ_{m,k}`, `|t - l_k τ''_m| ≤ τ''_m`. -/
theorem xi_flow_time_window_tauPP {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) :
    |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤ tauPP β I.Λ m := by
  have hτ := I.tau_pos' m
  have hnear := LeadingErrorFlow.xiMK_ne_zero_abs_le I m hξ
  have hcell := Infra.Ingredients.taum_prime_supp
    (β := β) (Λ := I.Λ) k I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le) (by omega : 1 ≤ m)
  have hleftmem : (k : ℝ) * tau β I.Λ m - tau β I.Λ m / 2 ∈
    Set.Icc ((k : ℝ) * tau β I.Λ m - tau β I.Λ m / 2)
        ((k : ℝ) * tau β I.Λ m + tau β I.Λ m / 2) := by
    simp only [Set.mem_Icc]
    constructor <;> linarith [hτ.le]
  have hrightmem : (k : ℝ) * tau β I.Λ m + tau β I.Λ m / 2 ∈
    Set.Icc ((k : ℝ) * tau β I.Λ m - tau β I.Λ m / 2)
        ((k : ℝ) * tau β I.Λ m + tau β I.Λ m / 2) := by
    simp only [Set.mem_Icc]
    constructor <;> linarith [hτ.le]
  have hleft := hcell hleftmem
  have hright := hcell hrightmem
  have hcenter :
      |(k : ℝ) * tau β I.Λ m -
          (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤
        tauPP β I.Λ m / 2 - tau β I.Λ m / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hleft.1, hright.2]
  have hfactor : 5 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    unfold Infra.Ingredients.tauCellFactor
    have hceilpos : 0 <
        ⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ := by
      apply Nat.ceil_pos.mpr
      exact Real.rpow_pos_of_pos (LeadingErrorFlow.eps_pos I _) _
    have hceil : 1 ≤
        (⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hceilpos)
    nlinarith
  have hratio := Infra.Ingredients.tauPP_eq_cellFactor_sq_mul_tau
    (β := β) (Λ := I.Λ) (m := m) (by omega : 1 ≤ m)
  have hsmall : tau β I.Λ m ≤ tauPP β I.Λ m / 25 := by
    have hF2 : 25 ≤ (Infra.Ingredients.tauCellFactor β I.Λ m) ^ 2 := by
      nlinarith [sq_nonneg (Infra.Ingredients.tauCellFactor β I.Λ m - 5)]
    have h25 : 25 * tau β I.Λ m ≤ tauPP β I.Λ m := by
      calc
        25 * tau β I.Λ m ≤
            Infra.Ingredients.tauCellFactor β I.Λ m ^ 2 * tau β I.Λ m :=
          mul_le_mul_of_nonneg_right hF2 hτ.le
        _ = tauPP β I.Λ m := hratio.symm
    nlinarith
  have hnearBounds := abs_le.mp hnear
  have hcenterBounds := abs_le.mp hcenter
  have hsum : t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m =
      (t - (k : ℝ) * tau β I.Λ m) +
        ((k : ℝ) * tau β I.Λ m -
          (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m) := by ring
  have hsumAbs :
      |(t - (k : ℝ) * tau β I.Λ m) +
        ((k : ℝ) * tau β I.Λ m -
          (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)| ≤
        tauPP β I.Λ m / 2 + 3 / 4 * tau β I.Λ m := by
    rw [abs_le]
    constructor <;> nlinarith [hnearBounds.1, hnearBounds.2,
      hcenterBounds.1, hcenterBounds.2]
  calc
    _ = |(t - (k : ℝ) * tau β I.Λ m) +
        ((k : ℝ) * tau β I.Λ m -
          (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)| := by rw [hsum]
    _ ≤ tauPP β I.Λ m / 2 + 3 / 4 * tau β I.Λ m := hsumAbs
    _ ≤ tauPP β I.Λ m := by nlinarith [hsmall]

/-- Abstract-real scale arithmetic: if `x ≤ 2^{-25} e^{2-b+2δ}` then `2^23 x e^{b-2} ≤ e^{2δ}/4`. -/
theorem LeadingErrorFlow.scale_arith {e b x d : ℝ} (he : 0 < e)
    (hx : x ≤ 2 ^ (-25 : ℤ) * e ^ (2 - b + 2 * d)) :
    2 ^ 23 * x * e ^ (b - 2) ≤ e ^ (2 * d) / 4 := by
  have hmul : e ^ (2 - b + 2 * d) * e ^ (b - 2) = e ^ (2 * d) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  have hpos : 0 ≤ e ^ (b - 2) := (Real.rpow_pos_of_pos he _).le
  have h2 : (2 : ℝ) ^ 23 * 2 ^ (-25 : ℤ) = 1 / 4 := by norm_num
  calc
    2 ^ 23 * x * e ^ (b - 2)
        ≤ 2 ^ 23 * (2 ^ (-25 : ℤ) * e ^ (2 - b + 2 * d)) * e ^ (b - 2) := by gcongr
    _ = ((2 : ℝ) ^ 23 * 2 ^ (-25 : ℤ)) * (e ^ (2 - b + 2 * d) * e ^ (b - 2)) := by ring
    _ = e ^ (2 * d) / 4 := by rw [h2, hmul]; ring

/-- Abstract-real scale arithmetic: `2^{-25} e^{2-b+2δ} ≤ 2^{-25} (e^{b-2})⁻¹` for `e ≤ 1`,
`0 ≤ δ`. -/
theorem LeadingErrorFlow.scale_window {e b x d : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hd : 0 ≤ d)
    (hx : x ≤ 2 ^ (-25 : ℤ) * e ^ (2 - b + 2 * d)) :
    x ≤ 2 ^ (-25 : ℤ) * (e ^ (b - 2))⁻¹ := by
  have hpow : e ^ (2 - b + 2 * d) ≤ e ^ (2 - b) :=
    Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith)
  have hinv : (e ^ (b - 2))⁻¹ = e ^ (2 - b) := by
    rw [show 2 - b = -(b - 2) by ring, Real.rpow_neg he.le]
  rw [hinv]
  exact hx.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- Flow-time window and the resulting smallness `2^23 |t - l_kτ''| a_{m-1} ≤ ε_{m-1}^{2δ}/4`. -/
theorem LeadingErrorFlow.flow_window_scale {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) :
    |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤
        2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ ∧
      2 ^ 23 * |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| * a β I.Λ (m - 1) ≤
        epsilon β I.Λ (m - 1) ^ (2 * delta β) / 4 := by
  have hwin := xi_flow_time_window_tauPP I hm k hξ
  have hpp := Infra.Ingredients.tauPP_bounds I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le) (by omega : 1 ≤ m)
  have hx := hwin.trans hpp.2
  have he := LeadingErrorFlow.eps_pos I (m - 1)
  have he1 : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
      (by exact_mod_cast I.two_pow_seven_le)
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  exact ⟨LeadingErrorFlow.scale_window he he1 hδ.le hx, LeadingErrorFlow.scale_arith he hx⟩

theorem LeadingErrorFlow.basisVec_norm_le_one (i : Fin 2) : ‖basisVec i‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp [basisVec]
  · simp [basisVec, h]

/-- Entry bound for a continuous linear map on `Vec 2`. -/
theorem LeadingErrorFlow.clm_entry_le (A : Vec 2 →L[ℝ] Vec 2) (i j : Fin 2) :
    |A (basisVec i) j| ≤ ‖A‖ := by
  calc
    |A (basisVec i) j| = ‖A (basisVec i) j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖A (basisVec i)‖ := norm_le_pi_norm _ j
    _ ≤ ‖A‖ * ‖basisVec i‖ := A.le_opNorm _
    _ ≤ ‖A‖ * 1 := by gcongr; exact LeadingErrorFlow.basisVec_norm_le_one i
    _ = ‖A‖ := mul_one _

theorem LeadingErrorFlow.fderiv_coord {F : Vec 2 → Vec 2} (hF : Differentiable ℝ F) (x : Vec 2)
    (j : Fin 2) (v : Vec 2) :
    fderiv ℝ (fun y => F y j) x v = fderiv ℝ F x v j := by
  have h := (hasFDerivAt_pi'.mp (hF x).hasFDerivAt) j
  rw [h.fderiv]
  rfl

/-- `gradMatrix` minus identity as a Jacobian entry. -/
theorem LeadingErrorFlow.gradMatrix_sub_one_apply {F : Vec 2 → Vec 2} (hF : Differentiable ℝ F)
    (x : Vec 2) (i j : Fin 2) :
    (gradMatrix F x - 1) i j = (fderiv ℝ F x - ContinuousLinearMap.id ℝ (Vec 2)) (basisVec i) j :=
        by
  have h := LeadingErrorFlow.fderiv_coord hF x j (basisVec i)
  simp only [Matrix.sub_apply, gradMatrix, Matrix.of_apply, spaceGrad, h,
    sub_apply, ContinuousLinearMap.id_apply, Pi.sub_apply]
  by_cases hij : i = j
  · subst hij; simp [basisVec]
  · simp [basisVec, hij, Ne.symm hij]

section Bridge

variable {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem LeadingErrorFlow.xFlow_slice_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    (fun y => I.xFlow hΦ m l t y) = fun y =>
      constructionFlow hΦ (m - 1) (((l : ℝ) * tauPP β I.Λ m) + (t - (l : ℝ) * tauPP β I.Λ m))
        y ((l : ℝ) * tauPP β I.Λ m) := by
  funext y
  rw [add_sub_cancel]
  rfl

theorem LeadingErrorFlow.xFlowInv_slice_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    (fun y => I.xFlowInv hΦ m l t y) = fun y =>
      constructionFlowInv hΦ (m - 1)
        (((l : ℝ) * tauPP β I.Λ m) + (t - (l : ℝ) * tauPP β I.Λ m))
        y ((l : ℝ) * tauPP β I.Λ m) := by
  funext y
  rw [add_sub_cancel]
  rfl

theorem LeadingErrorFlow.xFlow_diff (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    Differentiable ℝ (fun y => I.xFlow hΦ m l t y) :=
  (AVenhance.Infra.Section5.LeftToShow.xFlowDiffeo I hΦ m l t).contDiff_toFun.differentiable
    (by simp)

theorem LeadingErrorFlow.xFlowInv_diff (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    Differentiable ℝ (fun y => I.xFlowInv hΦ m l t y) :=
  (AVenhance.Infra.Section5.LeftToShow.xFlowDiffeo I hΦ m l t).contDiff_invFun.differentiable
    (by simp)

end Bridge

section Main

variable {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `e.Xm.bound.1` for the inverse flow, entrywise, on `supp ξ_{m,k}`. -/
theorem gradMatrix_xFlowInv_sub_one_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) (x : Vec 2) (i j : Fin 2) :
    |(gradMatrix (fun y => I.xFlowInv hΦ m (lIdx β I.Λ m k) t y) x - 1) i j| ≤
      epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
  obtain ⟨ht, hB⟩ := LeadingErrorFlow.flow_window_scale I hm k hξ
  set s : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m with hs
  have hscales := section2Scales_canonical I
  have happB2 := appB2InverseFlowData_of_smoothPeriodicFlow hΦ hscales
  have hind := section2_stream_induction hscales happB2
  have hbar := section2_flow_inverse_regbounds_from_previous hscales happB2 (m - 1)
    (by omega) (hind (m - 1 - 1)) s (t - s) ht 0
  have hcomp : barNorm 0 (2 ^ 11 * (epsilon β I.Λ (m - 1))⁻¹)
      (fun y => (constructionFlowInvJacobian hΦ (m - 1) (t - s) s y -
        ContinuousLinearMap.id ℝ (Vec 2)) (basisVec i) j) ≤
        ENNReal.ofReal (2 ^ 23 * |t - s| * a β I.Λ (m - 1)) := by
    refine le_trans ?_ hbar
    unfold flowJacobianBarNorm
    refine le_iSup_of_le j ?_
    refine le_iSup_of_le i ?_
    exact le_rfl
  have hcont : Continuous (fun y => (constructionFlowInvJacobian hΦ (m - 1) (t - s) s y -
        ContinuousLinearMap.id ℝ (Vec 2)) (basisVec i) j) := by
    have h := constructionFlowInvJacobian_entry_continuous hΦ (m - 1) s (t - s) j i
    change Continuous (fun y => constructionFlowInvJacobian hΦ (m - 1) (t - s) s y
      (basisVec i) j - (ContinuousLinearMap.id ℝ (Vec 2)) (basisVec i) j)
    exact h.sub continuous_const
  have ha : 0 < a β I.Λ (m - 1) :=
    Real.rpow_pos_of_pos (LeadingErrorFlow.eps_pos I _) _
  have hB0 : 0 ≤ 2 ^ 23 * |t - s| * a β I.Λ (m - 1) := by positivity
  have hpt := barNorm_zero_pointwise hcont hB0 hcomp x
  have hdiff := LeadingErrorFlow.xFlowInv_diff (I := I) hΦ m (lIdx β I.Λ m k) t
  rw [LeadingErrorFlow.gradMatrix_sub_one_apply hdiff]
  have hF : fderiv ℝ (fun y => I.xFlowInv hΦ m (lIdx β I.Λ m k) t y) x =
      constructionFlowInvJacobian hΦ (m - 1) (t - s) s x := by
    rw [LeadingErrorFlow.xFlowInv_slice_eq]
    rfl
  rw [hF]
  have hepow : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
    (Real.rpow_pos_of_pos (LeadingErrorFlow.eps_pos I _) _).le
  have h1 : |(constructionFlowInvJacobian hΦ (m - 1) (t - s) s x -
      ContinuousLinearMap.id ℝ (Vec 2)) (basisVec i) j| ≤
      2 ^ 23 * |t - s| * a β I.Λ (m - 1) := by
    simpa using hpt
  linarith

/-- `e.Xm.bound.1` for the forward flow pulled back (the `flowGrad`), entrywise. -/
theorem flowGrad_sub_one_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) (x : Vec 2) (i j : Fin 2) :
    |(I.flowGrad hΦ m (lIdx β I.Λ m k) t x - 1) i j| ≤
      epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
  obtain ⟨ht, hB⟩ := LeadingErrorFlow.flow_window_scale I hm k hξ
  set s : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m with hs
  have hscales := section2Scales_canonical I
  have happB2 := appB2InverseFlowData_of_smoothPeriodicFlow hΦ hscales
  have hind := section2_stream_induction hscales happB2
  have hclose := (section2_flow_close_from_previous hscales happB2 (m - 1) (by omega)
    (hind (m - 1 - 1)) s (t - s) ht (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).1
  have hdiff := LeadingErrorFlow.xFlow_diff (I := I) hΦ m (lIdx β I.Λ m k) t
  unfold Ingredients.flowGrad
  rw [LeadingErrorFlow.gradMatrix_sub_one_apply hdiff]
  have hF : fderiv ℝ (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) =
      constructionFlowJacobian hΦ (m - 1) (t - s) s (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) := by
    rw [LeadingErrorFlow.xFlow_slice_eq]
    rfl
  rw [hF]
  have hepow : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
    (Real.rpow_pos_of_pos (LeadingErrorFlow.eps_pos I _) _).le
  exact (LeadingErrorFlow.clm_entry_le _ i j).trans (hclose.trans (by linarith))

/-- Second spatial derivatives of the flow slice (`e.Xm.bound.2` / `e.flow.for.ergodic`,
`n = 2`). -/
theorem xFlow_second_deriv_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) (x : Vec 2) (i j l : Fin 2) :
    |iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y l) x
        ![basisVec i, basisVec j]| ≤
      2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹ := by
  obtain ⟨ht, -⟩ := LeadingErrorFlow.flow_window_scale I hm k hξ
  set s : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m with hs
  have hscales := section2Scales_canonical I
  have happB2 := appB2InverseFlowData_of_smoothPeriodicFlow hΦ hscales
  have hind := section2_stream_induction hscales happB2
  have hhigh := section2_flow_higher_derivative_from_previous hscales happB2 (m - 1)
    (by omega) 2 (by norm_num) (hind (m - 1 - 1)) s (t - s) ht x ![i, j]
  have hX : (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y) = fun y =>
      constructionFlow hΦ (m - 1) (s + (t - s)) y s := LeadingErrorFlow.xFlow_slice_eq hΦ m _ t
  have hvec : (fun r : Fin 2 => basisVec (![i, j] r)) = ![basisVec i, basisVec j] := by
    funext r
    fin_cases r <;> rfl
  rw [← hX, hvec] at hhigh
  have hsmooth : ContDiff ℝ 2 (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y) :=
    ((AVenhance.Infra.Section5.LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k)
      t).contDiff_toFun).of_le (by simp)
  have hcomp : (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y l) =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) l) ∘
        (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y) := rfl
  have hit : iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y l) x
        ![basisVec i, basisVec j] =
      iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y) x
        ![basisVec i, basisVec j] l := by
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ hsmooth.contDiffAt le_rfl]
    rfl
  rw [hit]
  have h2 : (2 : ℝ) * (Nat.factorial 2 : ℕ) * (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (2 - 1) =
      2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹ := by
    norm_num [Nat.factorial]
    ring
  calc
    _ = ‖iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y) x
        ![basisVec i, basisVec j] l‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y) x
        ![basisVec i, basisVec j]‖ := norm_le_pi_norm _ l
    _ ≤ _ := by rw [← h2]; exact hhigh

end Main

end AVenhance.Infra.Section5.RelativeError

end
