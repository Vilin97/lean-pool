/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticWindow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialWords

/-! # All-order word bounds for the matrix entries `Q`, `A`, `Y'` of the slow factors

For `t` in the support of `ξ_{m,k}` the Section 2 bar-norm bounds
(`section2_flow_jacobian_composed_from_previous`, `section2_flow_inverse_regbounds_from_previous`)
bound all spatial derivatives of the entries of `Q = ∇X ∘ X⁻¹ - I` (constant `40`, rate `2^10/ε`)
and of `A = ∇X⁻¹ - I` (constant `2^23 |t - s| a_{m-1}`, rate `2^11/ε`).  They are converted to
the ordered spatial word bounds of `SlowFactorBoundsComposition`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Construction AVenhance.Infra.Section5
open AVenhance.Infra.Section4

/-! ### Generic calculus -/

theorem sdj_contDiff_gradMatrix_entry {F : Vec 2 → Vec 2} (hF : ContDiff ℝ ∞ F) (a b : Fin 2) :
    ContDiff ℝ ∞ (fun y => gradMatrix F y a b) :=
  Integration.contDiff_spaceGrad_component (f := fun y => F y b) (contDiff_pi.1 hF b) a

theorem sdj_word_sub_const (c : ℝ) (f : Vec 2 → ℝ) (i : Fin 2) (α : List (Fin 2)) :
    amnrSpaceWord (i :: α) (fun y => f y - c) = amnrSpaceWord (i :: α) f := by
  induction α generalizing i with
  | nil =>
    funext x
    simp only [amnrSpaceWord]
    rw [fderiv_sub_const]
  | cons j α ih =>
    funext x
    change fderiv ℝ (amnrSpaceWord (j :: α) fun y => f y - c) x (basisVec i) =
      fderiv ℝ (amnrSpaceWord (j :: α) f) x (basisVec i)
    rw [ih j]

/-- A bar-norm bound at every order gives the pointwise ordered word bound. -/
theorem sdj_word_le_of_barNorm {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) {R B : ℝ} (hR : 0 < R)
    (hB : 0 ≤ B) (hb : ∀ n : ℕ, barNorm n R f ≤ ENNReal.ofReal B) (w : List (Fin 2)) (x : Vec 2) :
    |amnrSpaceWord w f x| ≤ B * w.length.factorial * R ^ w.length := by
  have h := amnrSpaceWord_norm_le_of_barNorm hf w hR hB (hb w.length) x
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  have hn : (1 : ℝ) ≤ ((w.length : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    nlinarith
  exact div_le_self (by positivity) hn

theorem sdj_rate_mono {B R L : ℝ} (hB : 0 ≤ B) (hR : R ≤ L) (hR0 : 0 ≤ R) (n : ℕ) :
    B * n.factorial * R ^ n ≤ B * n.factorial * L ^ n := by
  have : R ^ n ≤ L ^ n := pow_le_pow_left₀ hR0 hR n
  have h0 : 0 ≤ B * n.factorial := by positivity
  exact mul_le_mul_of_nonneg_left this h0

/-! ### Jacobian entries -/

section Entries

variable {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem TermCenteredAnalyticJets.sdj_basisVec_norm_le_one (i : Fin 2) : ‖basisVec i‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp [basisVec]
  · simp [basisVec, h]

theorem TermCenteredAnalyticJets.sdj_fderiv_coord {F : Vec 2 → Vec 2} (hF : Differentiable ℝ F) (x
    : Vec 2)
    (j : Fin 2) (v : Vec 2) :
    fderiv ℝ (fun y => F y j) x v = fderiv ℝ F x v j := by
  have h := (hasFDerivAt_pi'.mp (hF x).hasFDerivAt) j
  rw [h.fderiv]
  rfl

/-- `gradMatrix` minus identity as a Jacobian entry. -/
theorem sdj_gradMatrix_sub_one_apply {F : Vec 2 → Vec 2} (hF : Differentiable ℝ F)
    (x : Vec 2) (i j : Fin 2) :
    (gradMatrix F x - 1) i j = (fderiv ℝ F x - ContinuousLinearMap.id ℝ (Vec 2)) (basisVec i) j :=
        by
  have h := TermCenteredAnalyticJets.sdj_fderiv_coord hF x j (basisVec i)
  simp only [Matrix.sub_apply, gradMatrix, Matrix.of_apply, spaceGrad, h,
    sub_apply, ContinuousLinearMap.id_apply, Pi.sub_apply]
  by_cases hij : i = j
  · subst hij; simp [basisVec]
  · simp [basisVec, hij, Ne.symm hij]

theorem sdj_contDiff_flowGrad_entry (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ)
    (a b : Fin 2) : ContDiff ℝ ∞ (fun y => I.flowGrad hΦ m l t y a b) :=
  (sdj_contDiff_gradMatrix_entry (RelativeError.contDiff_xFlow_slice I hΦ m l t) a b).comp
    (RelativeError.contDiff_xFlowInv_slice I hΦ m l t)

theorem sdj_contDiff_invGrad_sub_one_entry (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ)
    (a b : Fin 2) :
    ContDiff ℝ ∞ (fun y => (gradMatrix (fun z => I.xFlowInv hΦ m l t z) y - 1) a b) := by
  have h := (sdj_contDiff_gradMatrix_entry (RelativeError.contDiff_xFlowInv_slice I hΦ m l t) a
      b).sub
    (contDiff_const (c := (1 : Matrix (Fin 2) (Fin 2) ℝ) a b))
  simpa only [Matrix.sub_apply] using h

/-- The pulled forward Jacobian minus identity is the composed Section 2 Jacobian. -/
theorem sdj_flowGrad_sub_one_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (y : Vec 2)
    (a b : Fin 2) :
    (I.flowGrad hΦ m l t y - 1) a b =
      (constructionComposedFlowJacobian hΦ (m - 1) ((l : ℝ) * tauPP β I.Λ m)
        (t - (l : ℝ) * tauPP β I.Λ m) y - ContinuousLinearMap.id ℝ (Vec 2)) (basisVec a) b := by
  have hdiff : Differentiable ℝ (fun z => I.xFlow hΦ m l t z) :=
    (RelativeError.contDiff_xFlow_slice I hΦ m l t).differentiable (by simp)
  unfold Ingredients.flowGrad
  rw [sdj_gradMatrix_sub_one_apply hdiff]
  have hinv : I.xFlowInv hΦ m l t y = constructionFlowInv hΦ (m - 1)
      (((l : ℝ) * tauPP β I.Λ m) + (t - (l : ℝ) * tauPP β I.Λ m)) y
      ((l : ℝ) * tauPP β I.Λ m) := congrFun (sdw_xFlowInv_slice_eq hΦ m l t) y
  have hF : fderiv ℝ (fun z => I.xFlow hΦ m l t z) (I.xFlowInv hΦ m l t y) =
      constructionComposedFlowJacobian hΦ (m - 1) ((l : ℝ) * tauPP β I.Λ m)
        (t - (l : ℝ) * tauPP β I.Λ m) y := by
    unfold constructionComposedFlowJacobian constructionFlowJacobian
    rw [← hinv, sdw_xFlow_slice_eq]
  rw [hF]

/-- The inverse Jacobian minus identity is the Section 2 inverse Jacobian. -/
theorem sdj_invGrad_sub_one_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (y : Vec 2)
    (a b : Fin 2) :
    (gradMatrix (fun z => I.xFlowInv hΦ m l t z) y - 1) a b =
      (constructionFlowInvJacobian hΦ (m - 1) (t - (l : ℝ) * tauPP β I.Λ m)
        ((l : ℝ) * tauPP β I.Λ m) y - ContinuousLinearMap.id ℝ (Vec 2)) (basisVec a) b := by
  have hdiff : Differentiable ℝ (fun z => I.xFlowInv hΦ m l t z) :=
    (RelativeError.contDiff_xFlowInv_slice I hΦ m l t).differentiable (by simp)
  rw [sdj_gradMatrix_sub_one_apply hdiff]
  have hF : fderiv ℝ (fun z => I.xFlowInv hΦ m l t z) y =
      constructionFlowInvJacobian hΦ (m - 1) (t - (l : ℝ) * tauPP β I.Λ m)
        ((l : ℝ) * tauPP β I.Λ m) y := by
    unfold constructionFlowInvJacobian
    rw [sdw_xFlowInv_slice_eq]
  rw [hF]

end Entries

/-! ### Bar-norm and word bounds -/

section Bounds

variable {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem sdj_flowGrad_sub_one_barNorm (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) (a b : Fin 2) (n : ℕ) :
    barNorm n (2 ^ 10 * (epsilon β I.Λ (m - 1))⁻¹)
      (fun y => (I.flowGrad hΦ m (lIdx β I.Λ m k) t y - 1) a b) ≤ ENNReal.ofReal 40 := by
  obtain ⟨ht, -⟩ := sdw_flow_window_scale I hm k hξ
  have hscales := section2Scales_canonical I
  have happB2 := appB2InverseFlowData_of_smoothPeriodicFlow hΦ hscales
  have hind := section2_stream_induction hscales happB2
  have hbar := section2_flow_jacobian_composed_from_previous hscales happB2 (m - 1)
    (by omega) n (hind (m - 1 - 1)) ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)
    (t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m) ht
  have hfun : (fun y => (I.flowGrad hΦ m (lIdx β I.Λ m k) t y - 1) a b) =
      fun y => (constructionComposedFlowJacobian hΦ (m - 1)
        ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)
        (t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m) y -
          ContinuousLinearMap.id ℝ (Vec 2)) (basisVec a) b :=
    funext fun y => sdj_flowGrad_sub_one_eq hΦ m _ t y a b
  rw [hfun]
  refine le_trans ?_ hbar
  unfold flowJacobianBarNorm
  exact le_iSup_of_le b (le_iSup_of_le a le_rfl)

theorem sdj_invGrad_sub_one_barNorm (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) (a b : Fin 2) (n : ℕ) :
    barNorm n (2 ^ 11 * (epsilon β I.Λ (m - 1))⁻¹)
      (fun y => (gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) y - 1) a b) ≤
      ENNReal.ofReal (2 ^ 23 * |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| *
        AVenhance.a β I.Λ (m - 1)) := by
  obtain ⟨ht, -⟩ := sdw_flow_window_scale I hm k hξ
  have hscales := section2Scales_canonical I
  have happB2 := appB2InverseFlowData_of_smoothPeriodicFlow hΦ hscales
  have hind := section2_stream_induction hscales happB2
  have hbar := section2_flow_inverse_regbounds_from_previous hscales happB2 (m - 1)
    (by omega) (hind (m - 1 - 1)) ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)
    (t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m) ht n
  have hfun : (fun y => (gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) y - 1) a b) =
      fun y => (constructionFlowInvJacobian hΦ (m - 1)
        (t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)
        ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m) y -
          ContinuousLinearMap.id ℝ (Vec 2)) (basisVec a) b :=
    funext fun y => sdj_invGrad_sub_one_eq hΦ m _ t y a b
  rw [hfun]
  refine le_trans ?_ hbar
  unfold flowJacobianBarNorm
  exact le_iSup_of_le b (le_iSup_of_le a le_rfl)

theorem sdj_eps_inv_pos (I : Ingredients β) (n : ℕ) :
    0 < 2 ^ 10 * (epsilon β I.Λ n)⁻¹ := by
  have := sdw_eps_pos I n
  positivity

/-- All-order word bound for `Q - 1` (the pulled forward Jacobian minus identity). -/
theorem sdj_Q_sub_one_word (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) (a b : Fin 2) (w : List (Fin 2)) (x : Vec 2) :
    |amnrSpaceWord w (fun y => (I.flowGrad hΦ m (lIdx β I.Λ m k) t y - 1) a b) x| ≤
      40 * w.length.factorial * (2 ^ 10 * (epsilon β I.Λ (m - 1))⁻¹) ^ w.length := by
  have hsm : ContDiff ℝ ∞ (fun y => (I.flowGrad hΦ m (lIdx β I.Λ m k) t y - 1) a b) := by
    have h := (sdj_contDiff_flowGrad_entry hΦ m (lIdx β I.Λ m k) t a b).sub
      (contDiff_const (c := (1 : Matrix (Fin 2) (Fin 2) ℝ) a b))
    simpa only [Matrix.sub_apply] using h
  exact sdj_word_le_of_barNorm hsm (sdj_eps_inv_pos I _) (by norm_num)
    (sdj_flowGrad_sub_one_barNorm hΦ hm k hξ a b) w x

/-- All-order word bound for `A = ∇X⁻¹ - I`, with the sharp amplitude. -/
theorem sdj_A_word_sharp (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) (a b : Fin 2) (w : List (Fin 2)) (x : Vec 2) :
    |amnrSpaceWord w (fun y =>
        (gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) y - 1) a b) x| ≤
      (2 ^ 23 * |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| * AVenhance.a β I.Λ (m - 1)) *
        w.length.factorial * (2 ^ 11 * (epsilon β I.Λ (m - 1))⁻¹) ^ w.length := by
  have he := sdw_eps_pos I (m - 1)
  have ha : 0 < AVenhance.a β I.Λ (m - 1) := Real.rpow_pos_of_pos he _
  exact sdj_word_le_of_barNorm (sdj_contDiff_invGrad_sub_one_entry hΦ m _ t a b)
    (by positivity) (by positivity) (sdj_invGrad_sub_one_barNorm hΦ hm k hξ a b) w x

theorem sdj_one_entry_abs_le (p q : Fin 2) : |(1 : Matrix (Fin 2) (Fin 2) ℝ) p q| ≤ 1 := by
  by_cases h : p = q <;> simp [Matrix.one_apply, h]

theorem sdj_rate_chain {β : ℝ} (I : Ingredients β) (n : ℕ) {L : ℝ}
    (hL : 2 ^ 11 * (epsilon β I.Λ n)⁻¹ ≤ L) : 2 ^ 10 * (epsilon β I.Λ n)⁻¹ ≤ L := by
  have := (sdj_eps_inv_pos I n).le
  linarith

/-- All-order word bounds of the entries of `Q = ∇X ∘ X⁻¹` (`hQb` of the composed lemma). -/
theorem sdj_Q_word (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) {L : ℝ} (hL : 2 ^ 11 * (epsilon β I.Λ (m - 1))⁻¹ ≤ L)
    (a b : Fin 2) (w : List (Fin 2)) (x : Vec 2) :
    |amnrSpaceWord w (fun y => I.flowGrad hΦ m (lIdx β I.Λ m k) t y a b) x| ≤
      41 * w.length.factorial * L ^ w.length := by
  have hR := sdj_rate_chain I _ hL
  have hR0 := (sdj_eps_inv_pos I (m - 1)).le
  have h := sdj_Q_sub_one_word hΦ hm k hξ a b w x
  simp only [Matrix.sub_apply] at h
  have hmono := sdj_rate_mono (B := 40) (by norm_num) hR hR0 w.length
  have hLn : 0 ≤ (w.length.factorial : ℝ) * L ^ w.length := by
    have := hR0.trans hR
    positivity
  cases w with
  | nil =>
    simp only [amnrSpaceWord, List.length_nil, Nat.factorial_zero, Nat.cast_one, pow_zero,
      mul_one] at h hmono ⊢
    have h1 := sdj_one_entry_abs_le a b
    calc |I.flowGrad hΦ m (lIdx β I.Λ m k) t x a b|
        = |(I.flowGrad hΦ m (lIdx β I.Λ m k) t x a b - (1 : Matrix (Fin 2) (Fin 2) ℝ) a b) +
            (1 : Matrix (Fin 2) (Fin 2) ℝ) a b| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add_le _ _
      _ ≤ 41 := by linarith
  | cons i α =>
    rw [← sdj_word_sub_const ((1 : Matrix (Fin 2) (Fin 2) ℝ) a b)
      (fun y => I.flowGrad hΦ m (lIdx β I.Λ m k) t y a b) i α]
    refine h.trans (hmono.trans ?_)
    have : 40 * ((i :: α).length.factorial : ℝ) * L ^ (i :: α).length =
        40 * ((↑(i :: α).length.factorial) * L ^ (i :: α).length) := by ring
    rw [this]
    nlinarith [hLn]

end Bounds

end AVenhance.Infra.Section5.Contracts
end
