/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNd
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredSplit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredFast
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalytic

/-! # Per-time centered bounds for the nondivergence parts -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Ergodic

theorem sd_cellAverage_sq_le {f : Vec 2 → ℝ} (hf : Continuous f) {V₀ V₁ V₂ : Vec 2 → Vec 2}
    (h₀ : Continuous V₀) (h₁ : Continuous V₁) (h₂ : Continuous V₂) {k₀ k₁ : ℝ}
    (hpt : ∀ x, f x ^ 2 ≤ k₀ ^ 2 * vecNormSq (V₀ x) +
      k₁ ^ 2 * (vecNormSq (V₁ x) + vecNormSq (V₂ x))) :
    cellAverage (fun x => |f x| ^ 2) ≤
      k₀ ^ 2 * gradNormSq V₀ + k₁ ^ 2 * (gradNormSq V₁ + gradNormSq V₂) := by
  rw [← LeftToShow.spaceAvg_eq_cellAverage]
  have hc (V : Vec 2 → Vec 2) (hV : Continuous V) : IntegrableOn (fun x => vecNormSq (V x))
      unitCube := LeftToShow.integrableOn_unitCube_of_continuous
    (LeftToShow.continuous_vecNormSq_two.comp hV)
  have hfi : IntegrableOn (fun x => |f x| ^ 2) unitCube :=
    LeftToShow.integrableOn_unitCube_of_continuous (by fun_prop)
  have hr : IntegrableOn (fun x => k₀ ^ 2 * vecNormSq (V₀ x) +
      k₁ ^ 2 * (vecNormSq (V₁ x) + vecNormSq (V₂ x))) unitCube :=
    ((hc V₀ h₀).const_mul _).add (((hc V₁ h₁).add (hc V₂ h₂)).const_mul _)
  unfold spaceAvg
  calc ∫ x in unitCube, |f x| ^ 2
      ≤ ∫ x in unitCube, (k₀ ^ 2 * vecNormSq (V₀ x) +
          k₁ ^ 2 * (vecNormSq (V₁ x) + vecNormSq (V₂ x))) :=
        integral_mono hfi hr fun x => by simpa [sq_abs] using hpt x
    _ = _ := by
        have e1 := integral_add (μ := volume.restrict unitCube)
          (f := fun x => k₀ ^ 2 * vecNormSq (V₀ x))
          (g := fun x => k₁ ^ 2 * (vecNormSq (V₁ x) + vecNormSq (V₂ x)))
          ((hc V₀ h₀).const_mul _) (((hc V₁ h₁).add (hc V₂ h₂)).const_mul _)
        have e2 := integral_add (μ := volume.restrict unitCube)
          (f := fun x => vecNormSq (V₁ x)) (g := fun x => vecNormSq (V₂ x))
          (hc V₁ h₁) (hc V₂ h₂)
        rw [e1, integral_const_mul, integral_const_mul, e2]
        rfl

theorem section5SlowChoice2_zero {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ) (a j : Fin 2)
    (h : I.xiMK m k t = 0) : section5SlowChoice2 I hΦ m κ T k t a j = fun _ => 0 := by
  funext x
  simp [section5SlowChoice2, h]

theorem section5SlowChoice3_zero {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ) (a j : Fin 2)
    (h : I.xiMK m k t = 0) : section5SlowChoice3 I hΦ m T k t a j = fun _ => 0 := by
  funext x
  simp [section5SlowChoice3, h]

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- **Centered bound of the nondivergence part of `twistie4` at a fixed time**
    (`e.monster.est.8b`). -/
theorem sd_nd4_centered_bound (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t))
    (hTp : IsZ2Periodic (T t)) {Cf r k₀ k₁ : ℝ} {V₀ V₁ V₂ : Vec 2 → Vec 2}
    (h₀ : Continuous V₀) (h₁ : Continuous V₁) (h₂ : Continuous V₂)
    (hpt : ∀ (k : ℤ) (a j : Fin 2) (x : Vec 2), section5SlowChoice2 I hΦ m κm T k t a j x ^ 2 ≤
      k₀ ^ 2 * vecNormSq (V₀ x) + k₁ ^ 2 * (vecNormSq (V₁ x) + vecNormSq (V₂ x)))
    (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hder : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 → ∀ a j : Fin 2,
      HasCoordinateAnalyticL2Bounds (fun x =>
        ((section5SlowChoice2 I hΦ m κm T k.1 t a j (I.xFlow hΦ m (lIdx β I.Λ m k.1) t x) : ℝ) : ℂ))
        Cf r)
    (hnear : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 →
      FlowDerivativeNearIdentity (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k.1) t))
    (hNr : 2 ≤ r * (ergodicFrequency β I.Λ m : ℝ)) :
    hMinusOneNorm (Integration.centerCell (twistie4Nd I hΦ m κm T t)) ≤
      ENNReal.ofReal (144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ) *
        Real.sqrt (k₀ ^ 2 * gradNormSq V₀ + k₁ ^ 2 * (gradNormSq V₁ + gradNormSq V₂)) *
          (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) +
        sdCd * Cf * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) *
          Real.exp (-r * (ergodicFrequency β I.Λ m : ℝ) / 4096))) := by
  have hm1 : 1 ≤ m := by omega
  have hNpos : 0 < ergodicFrequency β I.Λ m :=
    ergodicFrequency_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  refine sd_nd_centered_bound I hΦ t (fun k a j => sdFast4 I κm m k.1 t a j)
    (fun k a j => section5SlowChoice2 I hΦ m κm T k.1 t a j) (twistie4Nd I hΦ m κm T t)
    (fun S hS x => twistie4Nd_eq_sum I hΦ hm1 κm T t S hS x)
    (fun k a j hk => section5SlowChoice2_zero I hΦ m κm T k.1 t a j hk)
    (fun k a j => sd_slow2_smooth_periodic I hΦ m κm T hTt hTp k.1 a j)
    (fun k a j => sdFast4_continuous I m κm k.1 t a j)
    (fun k a j => sdFast4_isFastPeriodic I hm1 κm k.1 t a j)
    (fun k a j => sdFast4_cellAverage I hm1 κm k.1 t a j)
    (fun k a j y => sdFast4_abs_le I hm1 hκm k.1 t a j y)
    (fun k a j hk => hder k hk a j) hnear hCf hr hNpos hNr ?_
  intro k a j _
  exact sd_cellAverage_sq_le (sd_slow2_smooth_periodic I hΦ m κm T hTt hTp k.1 a j).1.continuous
    h₀ h₁ h₂ (hpt k.1 a j)

/-- **Centered bound of the nondivergence part of `twistie5` at a fixed time** (choice 3). -/
theorem sd_nd5_centered_bound (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t))
    (hTp : IsZ2Periodic (T t)) {Cf r k₀ k₁ : ℝ} {V₀ V₁ V₂ : Vec 2 → Vec 2}
    (h₀ : Continuous V₀) (h₁ : Continuous V₁) (h₂ : Continuous V₂)
    (hpt : ∀ (k : ℤ) (a j : Fin 2) (x : Vec 2), section5SlowChoice3 I hΦ m T k t a j x ^ 2 ≤
      k₀ ^ 2 * vecNormSq (V₀ x) + k₁ ^ 2 * (vecNormSq (V₁ x) + vecNormSq (V₂ x)))
    (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hder : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 → ∀ a j : Fin 2,
      HasCoordinateAnalyticL2Bounds (fun x =>
        ((section5SlowChoice3 I hΦ m T k.1 t a j (I.xFlow hΦ m (lIdx β I.Λ m k.1) t x) : ℝ) : ℂ))
        Cf r)
    (hnear : ∀ k : {k : ℤ // Odd k}, I.xiMK m k.1 t ≠ 0 →
      FlowDerivativeNearIdentity (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k.1) t))
    (hNr : 2 ≤ r * (ergodicFrequency β I.Λ m : ℝ)) :
    hMinusOneNorm (Integration.centerCell (twistie5Nd I hΦ m κm T t)) ≤
      ENNReal.ofReal (144 * (sdCd / (ergodicFrequency β I.Λ m : ℝ) *
        Real.sqrt (k₀ ^ 2 * gradNormSq V₀ + k₁ ^ 2 * (gradNormSq V₁ + gradNormSq V₂)) *
          (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2)) +
        sdCd * Cf * (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2)) *
          Real.exp (-r * (ergodicFrequency β I.Λ m : ℝ) / 4096))) := by
  have hm1 : 1 ≤ m := by omega
  have hNpos : 0 < ergodicFrequency β I.Λ m :=
    ergodicFrequency_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  refine sd_nd_centered_bound I hΦ t (fun k a j => sdFast5 I κm m k.1 t a j)
    (fun k a j => section5SlowChoice3 I hΦ m T k.1 t a j) (twistie5Nd I hΦ m κm T t)
    (fun S hS x => twistie5Nd_eq_sum I hΦ hm1 κm T t S hS x)
    (fun k a j hk => section5SlowChoice3_zero I hΦ m T k.1 t a j hk)
    (fun k a j => sd_slow3_smooth_periodic I hΦ m T hTt hTp k.1 a j)
    (fun k a j => sdFast5_continuous I m κm k.1 t a j)
    (fun k a j => sdFast5_isFastPeriodic I hm1 κm k.1 t a j)
    (fun k a j => sdFast5_cellAverage I hm1 κm k.1 t a j)
    (fun k a j y => sdFast5_abs_le I hm1 hκm k.1 t a j y)
    (fun k a j hk => hder k hk a j) hnear hCf hr hNpos hNr ?_
  intro k a j _
  exact sd_cellAverage_sq_le (sd_slow3_smooth_periodic I hΦ m T hTt hTp k.1 a j).1.continuous
    h₀ h₁ h₂ (hpt k.1 a j)

end AVenhance.Infra.Section5.Contracts
end
