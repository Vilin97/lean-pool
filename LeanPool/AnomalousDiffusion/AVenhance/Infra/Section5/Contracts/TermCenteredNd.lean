/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredErgodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo

/-! # Generic centered ergodic bound for a locally finite sum of fast-slow products

At a fixed time `t`, a nondivergence part `Nd = Σ_{k,a,j} (fast_{kaj} ∘ X_k⁻¹) · slow_{kaj}` with
at most three active odd `k` and four components `(a,j)` has centered `HDot⁻¹` norm at most
`144 · Cd · (Gm/N · ‖slow‖ + Cf Gm e^{-rN/4096})`: Minkowski over the at most twelve components and
the centered App C flow estimate (`sd_component_bound`) for each. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Ergodic

theorem hMinusOneNorm_zero_fun : hMinusOneNorm (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
  unfold hMinusOneNorm
  simp

theorem sd_centerCell_zero : Integration.centerCell (fun _ : Vec 2 => (0 : ℝ)) =
    fun _ => (0 : ℝ) := by
  funext x
  simp [Integration.centerCell]

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- **Generic nondivergence bound.** -/
theorem sd_nd_centered_bound (hΦ : IsStreamSeq I Φ) {m : ℕ} (t : ℝ)
    (fast slow : {k : ℤ // Odd k} → Fin 2 → Fin 2 → Vec 2 → ℝ) (Nd : Vec 2 → ℝ)
    (hNd : ∀ S : Finset {k : ℤ // Odd k}, (∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 → k ∈ S) →
      ∀ x, Nd x = ∑ k ∈ S, ∑ a : Fin 2, ∑ j : Fin 2,
        fast k a j (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) * slow k a j x)
    (hzero : ∀ k a j, I.xiMK m k.1 t = 0 → slow k a j = fun _ => 0)
    (hslow : ∀ k a j, ContDiff ℝ (⊤ : ℕ∞) (slow k a j) ∧ IsZPeriodic (slow k a j))
    (hfast_c : ∀ k a j, Continuous (fast k a j))
    (hfast_p : ∀ k a j, IsFastPeriodic (ergodicFrequency β I.Λ m) (fast k a j))
    (hfast_m : ∀ k a j, cellAverage (fast k a j) = 0)
    {Gm Cf r F2sq : ℝ} (hGm : ∀ k a j y, |fast k a j y| ≤ Gm)
    (hder : ∀ k a j, I.xiMK m k.1 t ≠ 0 →
      HasCoordinateAnalyticL2Bounds
        (fun x => ((slow k a j (I.xFlow hΦ m (lIdx β I.Λ m k.1) t x) : ℝ) : ℂ)) Cf r)
    (hnear : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 →
      FlowDerivativeNearIdentity (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k.1) t))
    (hCf : 0 ≤ Cf) (hr : 0 < r) (hNpos : 0 < ergodicFrequency β I.Λ m)
    (hNr : 2 ≤ r * (ergodicFrequency β I.Λ m : ℝ))
    (hF2 : ∀ k a j, I.xiMK m k.1 t ≠ 0 → cellAverage (fun x => |slow k a j x| ^ 2) ≤ F2sq) :
    hMinusOneNorm (Integration.centerCell Nd) ≤
      ENNReal.ofReal (144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ) * Real.sqrt F2sq * Gm +
        sdCd * Cf * Gm * Real.exp (-r * (ergodicFrequency β I.Λ m : ℝ) / 4096))) := by
  classical
  obtain ⟨S, hcard, hS⟩ := sb_odd_support_card I m t
  have hG0 : 0 ≤ Gm := (abs_nonneg _).trans (hGm ⟨1, by decide⟩ 0 0 0)
  set N := ergodicFrequency β I.Λ m with hN
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 3 * (2 : ℝ) ^ 2 *
    (sdCd / (N : ℝ) * Real.sqrt F2sq * Gm + sdCd * Cf * Gm * Real.exp (-r * (N : ℝ) / 4096)) :=
    ⟨_, rfl⟩
  -- each component
  let h : {k : ℤ // Odd k} × Fin 2 × Fin 2 → Vec 2 → ℝ := fun c x =>
    fast c.1 c.2.1 c.2.2 (I.xFlowInv hΦ m (lIdx β I.Λ m c.1.1) t x) * slow c.1 c.2.1 c.2.2 x
  have hcont : ∀ c ∈ S ×ˢ (Finset.univ ×ˢ Finset.univ), Continuous (h c) := by
    intro c _
    have hY : Continuous (I.xFlowInv hΦ m (lIdx β I.Λ m c.1.1) t) :=
      (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m c.1.1) t).contDiff_invFun.continuous
    exact ((hfast_c c.1 c.2.1 c.2.2).comp hY).mul (hslow c.1 c.2.1 c.2.2).1.continuous
  have hcomp : ∀ c ∈ S ×ˢ (Finset.univ ×ˢ Finset.univ),
      hMinusOneNorm (Integration.centerCell (h c)) ≤ ENNReal.ofReal b := by
    intro c _
    have hb0 : 0 ≤ b := by
      have := sdCd_pos
      have := Real.sqrt_nonneg F2sq
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
      have := Real.exp_pos (-r * (N : ℝ) / 4096)
      rw [hb]
      positivity
    by_cases hξ : I.xiMK m c.1.1 t = 0
    · have hz : h c = fun _ => (0 : ℝ) := by
        funext x
        simp only [h, hzero c.1 c.2.1 c.2.2 hξ, mul_zero]
      rw [hz, sd_centerCell_zero, hMinusOneNorm_zero_fun]
      exact zero_le
    · set X := LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m c.1.1) t with hX
      have hcm : h c = fun x => slow c.1 c.2.1 c.2.2 x * fast c.1 c.2.1 c.2.2 (X.invFun x) := by
        funext x
        simp only [h, hX, LeftToShow.xFlowDiffeo_invFun, mul_comm]
      rw [hcm]
      refine (sd_component_bound hNpos X (hslow c.1 c.2.1 c.2.2).1 (hslow c.1 c.2.1 c.2.2).2
        hCf hr (hder c.1 c.2.1 c.2.2 hξ) (hfast_c c.1 c.2.1 c.2.2) (hfast_p c.1 c.2.1 c.2.2)
        hNr (hnear c.1 hξ) (hfast_m c.1 c.2.1 c.2.2) (hGm c.1 c.2.1 c.2.2)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hF : (cellAverage (fun x => |slow c.1 c.2.1 c.2.2 x| ^ 2)) ^ (1 / 2 : ℝ) ≤
          Real.sqrt F2sq := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow (by
          rw [cellAverage_eq_unitCellIntegral]
          exact integral_nonneg fun x => by positivity)
          (hF2 c.1 c.2.1 c.2.2 hξ) (by norm_num)
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hCd := sdCd_pos
      rw [hb]
      gcongr
  have hsum : Nd = fun x => ∑ c ∈ S ×ˢ (Finset.univ ×ˢ Finset.univ), h c x := by
    funext x
    rw [hNd S hS x, Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_product]
  have hcardle : (S ×ˢ ((Finset.univ : Finset (Fin 2)) ×ˢ (Finset.univ : Finset (Fin 2)))).card ≤
      12 := by
    rw [Finset.card_product, Finset.card_product]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  rw [hsum]
  refine (sd_centered_finset_sum_bound _ h (fun _ => ENNReal.ofReal b) hcont hcomp).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hb0 : 0 ≤ b := by
    have := sdCd_pos
    have := Real.sqrt_nonneg F2sq
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
    have := Real.exp_pos (-r * (N : ℝ) / 4096)
    rw [hb]
    positivity
  calc ((S ×ˢ ((Finset.univ : Finset (Fin 2)) ×ˢ (Finset.univ : Finset (Fin 2)))).card : ℝ≥0∞) *
        ENNReal.ofReal b ≤ (12 : ℝ≥0∞) * ENNReal.ofReal b := by
        gcongr
        exact_mod_cast hcardle
    _ = ENNReal.ofReal (12 * b) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ = _ := by
        congr 1
        rw [hb]
        ring

end AVenhance.Infra.Section5.Contracts
end
