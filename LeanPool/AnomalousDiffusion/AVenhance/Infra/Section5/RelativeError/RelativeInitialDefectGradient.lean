/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorHGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectGradientPositive

/-! The previous-diffusivity normalization retained in the Hm gradient
calculation. This conditional source-scale helper sharpens the public
sqrt(kappa_m) conclusion to sqrt(kappa_{m-1}), for signed flux pairing. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section4
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section5.RelativeError

/-- The source-scale calculation supports the previous diffusivity in front
of the gradient norm. All upstream AMNR and regularity inputs stay explicit. -/
theorem relative_initial_Hm_gradient_sharp_of_amnr_scales {β C₀ CA K C ν S : ℝ} (hCA : 0 ≤ CA) (hS
    : 0 ≤ S)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (I : Ingredients β) (hz : I.Czeta ≤ C₀)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m)
    {κ : ℝ} (T : ℝ → Vec 2 → ℝ) (hκ : 0 < κ) (hκν : κ ≤ ν)
    (hratio : epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) ≤ 1)
    (hτ : 8 * tau β I.Λ m / tauP β I.Λ m ≤ 1 / 2)
    (hX : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ ≤ K * ν)
    (hν : ν ≤ C * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)))
    (hat : a β I.Λ (m - 1) * tau β I.Λ m ≤
      (2 : ℝ) ^ (-28 : ℤ) * epsilon β I.Λ (m - 1) ^ (4 * delta β))
    (hHessEntryMeas : ∀ r ∈ Finset.range (Jcut β), ∀ n ∈ Finset.range (Nstar β),
      ∀ i j k p : Fin 2,
        AEStronglyMeasurable
          (fun z : ℝ × Vec 2 => amnrSpatialDivergenceGradientTensor
            I hΦ m κ T n r z i j k p) (volume.restrict timeCube))
    (hGradientMeas : ∀ r ∈ Finset.range (Jcut β), AEStronglyMeasurable
      (fun z : ℝ × Vec 2 =>
        spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) (volume.restrict timeCube))
    (hD1 : ∀ r ∈ Finset.range (Jcut β), ∀ n ∈ Finset.range (Nstar β),
      ∀ i j k : Fin 2, ∀ t, 0 < t → ∀ x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x)
    (hD2 : ∀ r ∈ Finset.range (Jcut β), ∀ n ∈ Finset.range (Nstar β),
      ∀ i j k : Fin 2, ∀ t, 0 < t → ∀ x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => spaceGrad
            (fun x => I.Amnr hΦ m κ n T r t x i j k) y i) x)
    (hHmrD : ∀ r ∈ Finset.range (Jcut β), ∀ t, 0 < t → ∀ x,
      DifferentiableAt ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x)
    (hAmnr : ∀ r₀ ∈ Finset.range (Jcut β), ∀ n ∈ Finset.range (Nstar β),
      eLpNorm (amnrSpatialDivergenceGradientTensor I hΦ m κ T n r₀) 2
          (volume.restrict timeCube) ≤
        ENNReal.ofReal (CA * S * (epsilon β I.Λ m ^ 2 / κ) / Real.sqrt ν *
          (epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ 2 *
          ((tauP β I.Λ m)⁻¹) ^ r₀)) :
    Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (fun s x =>
        spaceGrad (I.Hm hΦ m κ T s) x)) ≤
      (256 * Real.sqrt 2 * (Nstar β : ℝ) * (4 * Real.pi ^ 2 * C₀) * CA * K * C *
        (2 : ℝ) ^ (-28 : ℤ)) * epsilon β I.Λ (m - 1) ^ (4 * delta β) * S := by
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hΛ := I.two_pow_seven_le
  have hC₀ : 0 ≤ C₀ := le_trans (by linarith [I.one_le_Czeta]) hz
  have hν0 : 0 < ν := lt_of_lt_of_le hκ hκν
  have hε : 0 < epsilon β I.Λ m := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hE : 0 < epsilon β I.Λ (m - 1) := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hτ0 : 0 < tau β I.Λ m := Infra.Ingredients.tau_pos hβ hβ' hΛ
  have hτ'0 : 0 < tauP β I.Λ m := Infra.Cutoff.tauP_pos hβ hβ' hΛ
  have ha : 0 < a β I.Λ m := Infra.Cutoff.a_pos hβ hβ' hΛ
  -- shorthand
  set L2 : ℝ := (epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ 2 with hL2
  set Z : ℝ := CA * S * (epsilon β I.Λ m ^ 2 / κ) / Real.sqrt ν * L2 with hZ
  set c0 : ℝ := 4 * Real.pi ^ 2 * C₀ with hc0
  set P : ℝ := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 with hP
  have hL20 : 0 ≤ L2 := sq_nonneg _
  have hZ0 : 0 ≤ Z := by positivity
  have hc00 : 0 ≤ c0 := by positivity
  have hN0 : (0 : ℝ) ≤ (Nstar β : ℝ) := Nat.cast_nonneg _
  -- the termwise bound
  have hterm : ∀ r ∈ Finset.range (Jcut β),
      eLpNorm (fun z : ℝ × Vec 2 =>
        spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2 (volume.restrict timeCube) ≤
        ENNReal.ofReal ((16 * (Nstar β : ℝ) * Z * c0 * P * (8 * tau β I.Λ m)) *
          (8 * tau β I.Λ m / tauP β I.Λ m) ^ r) := by
    intro r hr
    have hAr : 0 ≤ Z * ((tauP β I.Λ m)⁻¹) ^ r := by positivity
    have h := relative_initial_hmr_gradient_L2 (C₀ := C₀)
      (A := Z * ((tauP β I.Λ m)⁻¹) ^ r) I hΦ m κ T r
      (μ := volume.restrict timeCube)
      (Measure.absolutelyContinuous_of_le (Measure.restrict_mono
        (show timeCube ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) from
          fun z hz => ⟨hz.1.1, Set.mem_univ _⟩) le_rfl)) hz (by omega) hκ hAr hratio
      (fun n hn => hAmnr r hr n hn) (fun n hn => hHessEntryMeas r hr n hn)
      (hGradientMeas r hr) (fun n hn => hD1 r hr n hn) (fun n hn => hD2 r hr n hn)
    refine h.trans (le_of_eq ?_)
    congr 1
    simp only [hmrGradientQbase]
    rw [← leh_term_eq]
  have hDnn : 0 ≤ 16 * (Nstar β : ℝ) * Z * c0 * P * (8 * tau β I.Λ m) := by positivity
  have hBnn : ∀ r : ℕ, 0 ≤ (16 * (Nstar β : ℝ) * Z * c0 * P * (8 * tau β I.Λ m)) *
      (8 * tau β I.Λ m / tauP β I.Λ m) ^ r := fun r => by positivity
  have hsum := relative_initial_Hm_gradient_L2_sum_positive I hΦ m κ T hHmrD hBnn hterm
  have hgeo := leh_sum_le (Jcut β) hDnn (by positivity) hτ
  have hH : eLpNorm (fun z : ℝ × Vec 2 =>
      spaceGrad (fun x => I.Hm hΦ m κ T z.1 x) z.2) 2 (volume.restrict timeCube) ≤
      ENNReal.ofReal (2 * (16 * (Nstar β : ℝ) * Z * c0 * P * (8 * tau β I.Λ m))) :=
    hsum.trans (ENNReal.ofReal_le_ofReal hgeo)
  have heuc := sqrt_spaceTimeGradNormSq_le_of_eLpNorm_le
    (fun s x => spaceGrad (I.Hm hΦ m κ T s) x) (by positivity) hH
  -- the scale chain
  set D : ℝ := 2 * (16 * (Nstar β : ℝ) * Z * c0 * P * (8 * tau β I.Λ m)) with hD
  have hDeq : D = 2 * ((128 * (Nstar β : ℝ) * c0 * CA) * (S / Real.sqrt ν) *
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) * tau β I.Λ m * L2) := by
    simp only [hD, hZ, hP]
    ring
  have hL := leh_rpow_neg_sq_mul (g := gamma β) hE
  have hνt := leh_nu_t_L2_le (ν := ν) hC hτ0.le hL20 hν hL hat
  have hX0 : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ := by positivity
  have hfin := leh_final_real (N := (Nstar β : ℝ)) (c := c0) (CA := CA) (K := K) (S := S)
    (μ := ν) (ν := ν) (t := tau β I.Λ m) (L2 := L2)
    (X := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ)
    (Cn := C * ((2 : ℝ) ^ (-28 : ℤ) * epsilon β I.Λ (m - 1) ^ (4 * delta β)))
    hN0 hc00 hCA hK hS hν0 le_rfl hτ0.le hL20 hX0 hX hνt
  calc
    Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (fun s x =>
        spaceGrad (I.Hm hΦ m κ T s) x))
        ≤ Real.sqrt ν * (Real.sqrt 2 * D) :=
      mul_le_mul_of_nonneg_left heuc (Real.sqrt_nonneg _)
    _ = Real.sqrt ν * (Real.sqrt 2 * (2 * ((128 * (Nstar β : ℝ) * c0 * CA) *
          (S / Real.sqrt ν) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          tau β I.Λ m * L2))) := by rw [hDeq]
    _ ≤ _ := hfin
    _ = _ := by ring

end AVenhance.Infra.Section5.RelativeError
