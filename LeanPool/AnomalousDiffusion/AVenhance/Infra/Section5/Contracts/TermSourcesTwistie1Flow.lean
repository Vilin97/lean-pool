/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ErgodicParams

/-! # Flow facts on `supp ξ_{m,k}` for the `twistie1` source contract

Everything is stated for the flow slice `X_{m-1,l_k}(t)` at a time where `ξ_{m,k}(t) ≠ 0`:

* the time window `|t - l_k τ''_m| ≤ 2^{-25} a_{m-1}^{-1}` (`se_window`);
* the all-order derivative bound of the flow slice (`se_xFlow_jet_le`, `e.Xm.bound.4`);
* the all-order jets of the flow gradient (`se_flowGrad_word_le`, window form of
  `iterate_flowGrad_word_bound`, which assumes `ξ̂_{m,l}(t) ≠ 0` instead);
* the near-identity condition of the App C flow lemma (`se_nearIdentity`). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Construction AVenhance.Infra.Section4

/-- The source time window on the support of `ξ_{m,k}`. -/
theorem se_window {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 2 ≤ m) (k : ℤ) {t : ℝ}
    (hξ : I.xiMK m k t ≠ 0) :
    |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤ (2 : ℝ) ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by
  have hdist := RelativeError.xi_flow_time_window_tauPP I hm k hξ
  set e := epsilon β I.Λ (m - 1) with he_def
  have he : 0 < e := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  have he1 : e ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hpow : e ^ (2 - β + 2 * delta β) ≤ e ^ (2 - β) :=
    Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith)
  have hpp := Infra.Ingredients.tauPP_bounds I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le) (by omega : 1 ≤ m)
  have haInv : (a β I.Λ (m - 1))⁻¹ = e ^ (2 - β) := by
    dsimp [e, a]
    rw [show 2 - β = -(β - 2) by ring, Real.rpow_neg he.le]
  have hppWidth : tauPP β I.Λ m ≤ 2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by
    calc tauPP β I.Λ m ≤ 2 ^ (-25 : ℤ) * e ^ (2 - β + 2 * delta β) := hpp.2
      _ ≤ 2 ^ (-25 : ℤ) * e ^ (2 - β) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by rw [haInv]
  exact hdist.trans hppWidth

/-- All-order derivative bound of the flow slice on the support of `ξ_{m,k}`
(`e.Xm.bound.4`, coordinate form). -/
theorem se_xFlow_jet_le {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ) {t : ℝ} (hξ : I.xiMK m k t ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (J : Fin n → Fin 2) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (I.xFlow hΦ m (lIdx β I.Λ m k) t) x (fun j => basisVec (J j))‖ ≤
      2 * n.factorial * (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (n - 1) := by
  have hscales := section2Scales_canonical I
  have happB2 := appB2InverseFlowData_of_smoothPeriodicFlow hΦ hscales
  have hind := section2_stream_induction hscales happB2
  have ht := se_window I hm k hξ
  set start : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m with hstart
  have h := section2_flow_higher_derivative_from_previous hscales happB2 (m - 1) (by omega) n hn
    (hind (m - 1 - 1)) start (t - start) (by simpa [start] using ht) x J
  change ‖iteratedFDeriv ℝ n
    (fun y : Vec 2 => constructionFlow hΦ (m - 1) t y start) x (fun j => basisVec (J j))‖ ≤ _
  simpa [start, add_sub_cancel_left] using h

/-- Window form of `iterate_flowGrad_barNorm`. -/
theorem se_flowGrad_barNorm {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {l : ℤ} {t : ℝ}
    (hwin : |t - (l : ℝ) * tauPP β I.Λ m| ≤ (2 : ℝ) ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹)
    (n : ℕ) (i j : Fin 2) :
    barNorm n (2 ^ 10 * (epsilon β I.Λ (m - 1))⁻¹)
      (fun x => (I.flowGrad hΦ m l t x - 1) i j) ≤ ENNReal.ofReal 40 := by
  let scales := section2Scales_canonical I
  let data := appB2InverseFlowData_of_smoothPeriodicFlow hΦ scales
  have hind := section2_stream_induction scales data
  have hb := section2_flow_jacobian_composed_from_previous scales data
    (m - 1) (by omega) n (hind ((m - 1) - 1))
    ((l : ℝ) * tauPP β I.Λ m) (t - (l : ℝ) * tauPP β I.Λ m) hwin
  have he := (le_iSup_of_le j (le_iSup_of_le i le_rfl)).trans hb
  simpa only [flowJacobianBarNorm, ← iterate_flowGrad_entry_eq_composed] using he

/-- Window form of `iterate_flowGrad_word_bound`: the jets of `∇X ∘ X⁻¹ - 1`. -/
theorem se_flowGrad_word_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {l : ℤ} {t : ℝ}
    (hwin : |t - (l : ℝ) * tauPP β I.Λ m| ≤ (2 : ℝ) ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹)
    (w : List (Fin 2)) (x : Vec 2) (i j : Fin 2) :
    |iterateSpatialWord w (fun y => (I.flowGrad hΦ m l t y - 1) i j) x| ≤
      40 * (w.length.factorial : ℝ) * (2 ^ 10 / epsilon β I.Λ (m - 1)) ^ w.length := by
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => (I.flowGrad hΦ m l t y - 1) i j) := by
    have h := (amnr_flowGrad_joint_contDiff_infty I hΦ m l i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
    exact h.sub contDiff_const
  have hb := iterate_word_abs_factorial_bound_of_barNorm hs (by positivity)
    (by norm_num : (0 : ℝ) ≤ 40) w (se_flowGrad_barNorm I hΦ hm hwin w.length i j) x
  have hd : 1 ≤ ((w.length : ℝ) + 1) ^ 2 := by
    have h := Nat.cast_nonneg (α := ℝ) w.length
    nlinarith only [h]
  have hdrop := div_le_self (by positivity : 0 ≤
    40 * (w.length.factorial : ℝ) *
      (2 ^ 10 * (epsilon β I.Λ (m - 1))⁻¹) ^ w.length) hd
  simpa only [div_eq_mul_inv] using hb.trans hdrop

/-- Adding a constant does not change a nonempty ordered derivative word. -/
theorem se_amnrSpaceWord_add_const (f : Vec 2 → ℝ) (c : ℝ) :
    ∀ w : List (Fin 2), w ≠ [] → amnrSpaceWord w (fun y => f y + c) = amnrSpaceWord w f := by
  intro w
  induction w with
  | nil => intro h; exact absurd rfl h
  | cons i α ih =>
    intro _
    funext x
    by_cases hα : α = []
    · subst hα
      simp only [amnrSpaceWord]
      rw [fderiv_add_const]
    · simp only [amnrSpaceWord]
      rw [ih hα]

/-- Jets of the entries of the flow gradient itself (order zero: `|∇X ∘ X⁻¹| ≤ 2`). -/
theorem se_flowGrad_entry_jet_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ) {t : ℝ} (hξ : I.xiMK m k t ≠ 0)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1) {L : ℝ}
    (hL : 2 ^ 10 / epsilon β I.Λ (m - 1) ≤ L) (w : List (Fin 2)) (x : Vec 2) (i j : Fin 2) :
    |amnrSpaceWord w (fun y => I.flowGrad hΦ m (lIdx β I.Λ m k) t y i j) x| ≤
      40 * (w.length.factorial : ℝ) * L ^ w.length := by
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  by_cases hw : w = []
  · subst hw
    have h0 := RelativeError.flowGrad_sub_one_le hΦ hm k hξ x i j
    simp only [amnrSpaceWord, List.length_nil, Nat.factorial_zero, Nat.cast_one, pow_zero,
      mul_one]
    have h1 : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      simp only [Matrix.one_apply]; split_ifs <;> norm_num
    have h2 : |I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j| ≤ 1 + 1 := by
      have := abs_sub_abs_le_abs_sub (I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j)
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
      have h3 : |I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j -
          (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
        simpa [Matrix.sub_apply] using h0.trans hsmall
      linarith
    linarith
  · have hwin := se_window I hm k hξ
    have hshift : (fun y => I.flowGrad hΦ m (lIdx β I.Λ m k) t y i j) =
        fun y => (I.flowGrad hΦ m (lIdx β I.Λ m k) t y - 1) i j +
          (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
      funext y; simp [Matrix.sub_apply]
    rw [hshift, se_amnrSpaceWord_add_const _ _ w hw, ←
        RelativeError.iterateSpatialWord_eq_amnrSpaceWord]
    refine (se_flowGrad_word_le I hΦ hm hwin w x i j).trans ?_
    gcongr

/-- The operator norm of a map on `Vec 2` (sup norm) is at most twice the largest matrix entry. -/
theorem se_opNorm_le_of_entries (A : Vec 2 →L[ℝ] Vec 2) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i j, |A (basisVec i) j| ≤ b) : ‖A‖ ≤ 2 * b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hrepr : v = ∑ i : Fin 2, v i • basisVec i := by
    ext j
    classical
    simp only [Finset.sum_apply, Pi.smul_apply, basisVec_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hne
      simp [Ne.symm hne]
    · intro hj
      simp at hj
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  have hAv : A v = ∑ i : Fin 2, v i • A (basisVec i) := by
    conv_lhs => rw [hrepr]
    simp only [map_sum, map_smul]
  rw [hAv, Finset.sum_apply, Fin.sum_univ_two]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h0 : |v 0 * A (basisVec 0) j| ≤ ‖v‖ * b := by
    rw [abs_mul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v 0) (h 0 j)
      (abs_nonneg _) (norm_nonneg _)
  have h1 : |v 1 * A (basisVec 1) j| ≤ ‖v‖ * b := by
    rw [abs_mul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v 1) (h 1 j)
      (abs_nonneg _) (norm_nonneg _)
  calc _ ≤ |v 0 * A (basisVec 0) j| + |v 1 * A (basisVec 1) j| := abs_add_le _ _
    _ ≤ ‖v‖ * b + ‖v‖ * b := add_le_add h0 h1
    _ = 2 * b * ‖v‖ := by ring

theorem se_gradMatrix_apply {F : Vec 2 → Vec 2} (hF : Differentiable ℝ F) (x : Vec 2)
    (i j : Fin 2) : gradMatrix F x i j = (fderiv ℝ F x (basisVec i)) j := by
  unfold gradMatrix spaceGrad
  change fderiv ℝ (fun y => F y j) x (basisVec i) = _
  rw [fderiv_apply (hF x) j]
  rfl

/-- Near-identity of the flow slice on the support of `ξ_{m,k}` (the hypothesis of the App C flow
lemma): `ε_{m-1}^{2δ} ≤ 1/8` gives `‖∇X - I‖ + ‖∇X⁻¹ - I‖ ≤ 1/2`. -/
theorem se_nearIdentity {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ) {t : ℝ} (hξ : I.xiMK m k t ≠ 0)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 8) :
    Infra.Ergodic.FlowDerivativeNearIdentity
      (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t) := by
  intro x
  set X := LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t with hX
  have he0 : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
    (Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le) _).le
  have hdX : Differentiable ℝ X.toFun := X.contDiff_toFun.differentiable (by simp)
  have hdI : Differentiable ℝ X.invFun := X.contDiff_invFun.differentiable (by simp)
  have hfwd : ‖fderiv ℝ X.toFun x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
      2 * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    apply se_opNorm_le_of_entries _ he0
    intro i j
    have h1 := RelativeError.flowGrad_sub_one_le hΦ hm k hξ (X.toFun x) i j
    have h2 : I.flowGrad hΦ m (lIdx β I.Λ m k) t (X.toFun x) =
        gradMatrix X.toFun x := by
      unfold Ingredients.flowGrad
      have := X.left_inv x
      change gradMatrix (fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y)
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t (I.xFlow hΦ m (lIdx β I.Λ m k) t x)) = _
      rw [show I.xFlowInv hΦ m (lIdx β I.Λ m k) t (I.xFlow hΦ m (lIdx β I.Λ m k) t x) = x
        from this]
      rfl
    rw [h2, Matrix.sub_apply, se_gradMatrix_apply hdX] at h1
    simpa [Matrix.one_apply, basisVec, Pi.single_apply, eq_comm] using h1
  have hinv : ‖fderiv ℝ X.invFun x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
      2 * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    apply se_opNorm_le_of_entries _ he0
    intro i j
    have h1 := RelativeError.gradMatrix_xFlowInv_sub_one_le hΦ hm k hξ x i j
    rw [Matrix.sub_apply, show (fun y => I.xFlowInv hΦ m (lIdx β I.Λ m k) t y) = X.invFun from rfl,
      se_gradMatrix_apply hdI] at h1
    simpa [Matrix.one_apply, basisVec, Pi.single_apply, eq_comm] using h1
  linarith

end AVenhance.Infra.Section5.Contracts
end
