/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicFlow

/-! # Near-identity of the actual flow slice on `supp ξ_{m,k}`

The forward Jacobian is within `B = 2^23 |t - s| a_{m-1} ≤ ε_{m-1}^{2δ}/4` of the identity in
operator norm (`section2_flow_close_from_previous`), the inverse Jacobian entrywise (hence within
`2B` in operator norm); with `ε_{m-1}^{2δ} ≤ 1/4` the sum is at most `3/16 ≤ 1/2`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Construction AVenhance.Infra.Section5
open AVenhance.Infra.Section4

/-- The operator norm on `Vec 2` (sup norm) is at most twice the largest matrix entry. -/
theorem sdn_opNorm_le_of_entries {A : Vec 2 →L[ℝ] Vec 2} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |A (basisVec i) j| ≤ c) : ‖A‖ ≤ 2 * c := by
  refine A.opNorm_le_bound (by positivity) fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  have hAv : A v j = v 0 * A (basisVec 0) j + v 1 * A (basisVec 1) j := by
    conv_lhs => rw [hv]
    simp
  rw [Real.norm_eq_abs, hAv]
  have h0 : |v 0| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v 1
  calc |v 0 * A (basisVec 0) j + v 1 * A (basisVec 1) j|
      ≤ |v 0 * A (basisVec 0) j| + |v 1 * A (basisVec 1) j| := abs_add_le _ _
    _ = |v 0| * |A (basisVec 0) j| + |v 1| * |A (basisVec 1) j| := by rw [abs_mul, abs_mul]
    _ ≤ ‖v‖ * c + ‖v‖ * c :=
        add_le_add (mul_le_mul h0 (h 0 j) (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul h1 (h 1 j) (abs_nonneg _) (norm_nonneg _))
    _ = 2 * c * ‖v‖ := by ring

/-- Near-identity of the actual flow slice on the support of `ξ_{m,k}`. -/
theorem sdn_flow_nearIdentity {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 4)
    {t : ℝ} {k : ℤ} (hξ : I.xiMK m k t ≠ 0) :
    Infra.Ergodic.FlowDerivativeNearIdentity
      (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t) := by
  obtain ⟨ht, hB⟩ := sdw_flow_window_scale I hm k hξ
  set s : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m with hs
  set B : ℝ := 2 ^ 23 * |t - s| * AVenhance.a β I.Λ (m - 1) with hBdef
  have hB16 : B ≤ 1 / 16 := by linarith
  have hscales := section2Scales_canonical I
  have happB2 := appB2InverseFlowData_of_smoothPeriodicFlow hΦ hscales
  have hind := section2_stream_induction hscales happB2
  have hB0 : 0 ≤ B := by
    have he := sdw_eps_pos I (m - 1)
    have ha : 0 < AVenhance.a β I.Λ (m - 1) := Real.rpow_pos_of_pos he _
    positivity
  intro x
  -- forward Jacobian
  have hfwd : ‖fderiv ℝ (I.xFlow hΦ m (lIdx β I.Λ m k) t) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
      B := by
    have hclose := (section2_flow_close_from_previous hscales happB2 (m - 1) (by omega)
      (hind (m - 1 - 1)) s (t - s) ht x).1
    have hF : fderiv ℝ (I.xFlow hΦ m (lIdx β I.Λ m k) t) x =
        constructionFlowJacobian hΦ (m - 1) (t - s) s x := by
      have := sdw_xFlow_slice_eq hΦ m (lIdx β I.Λ m k) t
      unfold constructionFlowJacobian
      rw [show I.xFlow hΦ m (lIdx β I.Λ m k) t = fun y => I.xFlow hΦ m (lIdx β I.Λ m k) t y from
        rfl, this]
    rw [hF]
    exact hclose
  -- inverse Jacobian
  have hinvdiff : Differentiable ℝ (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) :=
    (RelativeError.contDiff_xFlowInv_slice I hΦ m (lIdx β I.Λ m k) t).differentiable (by simp)
  have hinv : ‖fderiv ℝ (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 * B := by
    refine sdn_opNorm_le_of_entries hB0 fun i j => ?_
    have h := sdj_A_word_sharp hΦ hm k hξ i j [] x
    simp only [amnrSpaceWord, List.length_nil, Nat.factorial_zero, Nat.cast_one, pow_zero,
      mul_one] at h
    rw [sdj_gradMatrix_sub_one_apply hinvdiff] at h
    exact h
  simp only [LeftToShow.xFlowDiffeo_toFun, LeftToShow.xFlowDiffeo_invFun]
  linarith

end AVenhance.Infra.Section5.Contracts
end
