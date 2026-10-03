/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorBoundCoeff
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.MaterialAmnrAdapters
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HmAdapter
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity

/-! # The `S`-amplitude AMNR Hessian tensor from per-iterate jets

Equation (5).  The AMNR tensors are linear in
`∇T`, so the amplitude `G = Cg * S / √κ_{m-1}` of the temperature-gradient jets passes through the
recursion unchanged: the conclusion is exactly the tensor premise of `relative_Hm_gradient`.  The
primitive coefficient, velocity-gradient and seed constants are the `I`-uniform ones of
`ATensorBoundCoeff`, so `CA` and `Λ₀` depend only on `β, C₀, Cg, Cl`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Set
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.LeftToShow

/-- Abstract-real: `ε ≤ Λ⁻¹` and `D^{1/e} ≤ Λ` give `ε^e ≤ D⁻¹`. -/
theorem atb_rpow_le_inv_of_large {ε Λ e D : ℝ} (hε : 0 < ε) (hεΛ : ε ≤ Λ⁻¹) (he : 0 < e)
    (hD : 0 < D) (hΛ : D ^ (1 / e) ≤ Λ) : ε ^ e ≤ D⁻¹ := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (Real.rpow_pos_of_pos hD _) hΛ
  have h1 : ε ^ e ≤ (Λ⁻¹) ^ e := Real.rpow_le_rpow hε.le hεΛ he.le
  have h2 : D ≤ Λ ^ e := by
    have := Real.rpow_le_rpow (Real.rpow_pos_of_pos hD _).le hΛ he.le
    rwa [← Real.rpow_mul hD.le, one_div, inv_mul_cancel₀ he.ne', Real.rpow_one] at this
  rw [Real.inv_rpow hΛ0.le] at h1
  exact h1.trans (inv_anti₀ hD h2)

/-- The `I`-uniform amplitude constant of the relative AMNR Hessian. -/
def atbConstant (β C₀ Cg Cl C : ℝ) : ℝ :=
  128 * Cl ^ 2 * (2 : ℝ) ^ (AVenhance.Nstar β + 1) * uniSeedA0Plus β C₀ * Cg *
    relativeMixedTemperatureConstant β (uniCoeff β C₀) (uniCb β C₀) (Cl ^ 2 * C) ^
      AVenhance.Nstar β *
    (1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * uniCb β C₀) ^ AVenhance.Jcut β

/-- Fixed-`I` core of the relative AMNR Hessian estimate, with the `I`-uniform constant. -/
theorem atb_core {β Creg C₀ c C Cg Cl : ℝ} (hCg : 0 ≤ Cg) (hCl : 1 ≤ Cl)
    (I : Ingredients β) (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) (hc : 0 < c) (hcC : c < C)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (hreg : StreamRegularityBounds Creg I Φ)
    {κ : ℝ} (hκ : 0 < κ) {M : ℕ} (hperm : κ ∈ permittedInterval β I.Λ M)
    (hA5 : (∀ m : ℕ, 1 ≤ m → m < M →
        c * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)) ≤ I.kappaAt κ m (M - m) ∧
        I.kappaAt κ m (M - m) ≤ C * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β))) ∧
      (∀ m : ℕ, 2 ≤ m → m < M →
        c * epsilon β I.Λ (m - 1) ^ (4 * delta β) ≤
          epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) ∧
        epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) ≤
          C * epsilon β I.Λ (m - 1) ^ (4 * delta β)))
    {m : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M)
    (hsm1 : amnrSourceRatioConstant β C * epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 2)
    (hsm2 : Section3.lAmtOneStepConstant β C₀ *
        (amnrSourceRatioConstant β C * epsilon β I.Λ (m - 1) ^ (2 * delta β) +
          epsilon β I.Λ (m - 1) ^ delta β) ≤ 9 / 160)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1))
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T)
    {S : ℝ} (hS : 0 ≤ S)
    (hjets : ∀ i, i ≤ Nstar β → ∀ (p : Fin 2) (α : List (Fin 2)), α.length ≤ Nstar β →
      eLpNorm (Infra.Section4.amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
          (α.map some) (Infra.Section4.amnrTGradient (T i) p)) 2
        ((volume.restrict (Set.uIoc 0 1)).prod (volume.restrict unitCube)) ≤
      ENNReal.ofReal (Cg * S / Real.sqrt (I.kappaSeq κ M (m - 1)) *
        (Cl * epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ α.length))
    {r₀ : ℕ} (hr₀ : r₀ ∈ Finset.range (Jcut β)) {n : ℕ} (hn : n ∈ Finset.range (Nstar β)) :
    eLpNorm (Infra.Section4.amnrSpatialDivergenceGradientTensor I hΦ m (I.kappaSeq κ M m)
        (T (Nstar β)) n r₀) 2 (volume.restrict timeCube) ≤
      ENNReal.ofReal (atbConstant β C₀ Cg Cl C * S * (epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m) /
        Real.sqrt (I.kappaSeq κ M (m - 1)) *
        (epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ 2 * ((tauP β I.Λ m)⁻¹) ^ r₀) := by
  have hN := Finset.mem_range.mp hn
  have hr₀' := Finset.mem_range.mp hr₀
  have hJ : 2 + r₀ ≤ Nstar β := by unfold Jcut at hr₀'; omega
  have hbud : 2 ≤ Nstar β - 2 * r₀ := amnr_hm_second_derivative_budget hr₀
  have hr₀le : r₀ ≤ Jcut β := hr₀'.le
  have hCl0 : 0 < Cl := by linarith
  have hC0 : 0 < C := hc.trans hcC
  have hE : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hS' : 0 < epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)) := Real.rpow_pos_of_pos hE _
  have hτ : 0 < tauP β I.Λ m := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hQ : 0 < (tauP β I.Λ m)⁻¹ := inv_pos.mpr hτ
  have hκm : 0 < I.kappaSeq κ M m := Infra.Section3.kappaAt_pos I hκ m (M - m)
  have hκprev : 0 < I.kappaSeq κ M (m - 1) := Infra.Section3.kappaAt_pos I hκ (m - 1) (M - (m - 1))
  -- abbreviations
  set κm := I.kappaSeq κ M m with hκm_def
  set κprev := I.kappaSeq κ M (m - 1) with hκprev_def
  set S' := epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)) with hS'_def
  set Q := (tauP β I.Λ m)⁻¹ with hQ_def
  set Lr := Cl * S' with hLr_def
  have hL : 0 < Lr := mul_pos hCl0 hS'
  have hSL : S' ≤ Lr := by
    have := mul_le_mul_of_nonneg_right hCl hS'.le
    simpa [hLr_def] using this
  -- uniform primitive bounds
  have hCoeff := uni_temperatureCoefficient_mixed_bounds_through_top I hz hh hc hcC hΦ hreg
    κ M hκ hperm hA5 m hm hmM hsm1 hsm2
  have hVel := uni_velocityGradient_mixed_bounds I hz hh hΦ hreg
  have hSeedU := uni_seedMultiplierA0Plus_mixed_bounds I hz hh hΦ hreg
  have hRate0 : κprev * S' ^ 2 ≤ C * Q :=
    amnr_diffusion_rate_le hE (hA5.1 (m - 1) (by omega) (by omega)).2
      (amnr_physical_rates I (by omega)).2 hC0.le
  have hRate : κprev * Lr ^ 2 ≤ (Cl ^ 2 * C) * Q := by
    have := mul_le_mul_of_nonneg_left hRate0 (sq_nonneg Cl)
    calc κprev * Lr ^ 2 = Cl ^ 2 * (κprev * S' ^ 2) := by rw [hLr_def]; ring
      _ ≤ Cl ^ 2 * (C * Q) := this
      _ = _ := by ring
  have hCb0 : 0 ≤ uniCb β C₀ := by linarith [one_le_uniCb β C₀]
  have hCoeff0 : 0 ≤ uniCoeff β C₀ := by
    have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Czeta]
    have := uniFlowGrad_nonneg β C₀
    have hAplus : 0 ≤ uniFlowAvgA0Plus β C₀ := by
      unfold uniFlowAvgA0Plus
      positivity
    have hQk : 0 ≤ amnrKmatStepConstant β C₀ := by
      unfold amnrKmatStepConstant; positivity
    unfold uniCoeff uniFlowAvg uniFlowAvgA0Plus
    positivity
  have hSeed0 : 0 ≤ uniSeedA0Plus β C₀ := by
    have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Czeta]
    have := uniFlowGrad_nonneg β C₀
    have hMem : 0 ≤ amnrMemoryConstant β C₀ := by unfold amnrMemoryConstant; positivity
    have hAplus : 0 ≤ uniFlowAvgA0Plus β C₀ := by
      unfold uniFlowAvgA0Plus
      positivity
    unfold uniSeedA0Plus
    positivity
  -- the actual joint regularity and measurability
  let U : Set AmnrSpace := Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))
  let μ : Measure AmnrSpace :=
    (volume.restrict (Set.uIoc 0 1)).prod (volume.restrict unitCube)
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hμ : μ ≪ volume.restrict U := amnr_time_cell_product_absolutelyContinuous (by norm_num)
  let b := fun y : AmnrSpace => streamVel (Φ (m - 1)) y.1 y.2
  have hbInf : ContDiff ℝ (⊤ : ℕ∞) b :=
    contDiff_infty.mpr (fun N => amnr_previous_velocity_contDiff I hΦ (by omega) N)
  have hb2 : ContDiffOn ℝ 2 b U := (hbInf.of_le (by simp)).contDiffOn
  have hreg2 (a j k : Fin 2) : ContDiffOn ℝ 2
      (fun z : AmnrSpace => I.Amnr hΦ m κm n (T (Nstar β)) r₀ z.1 z.2 a j k) U :=
    amnr_actual_contDiffOn I hΦ (by omega) hκm hθprev hT n r₀ 2 hJ a j k
  -- the engine, for each fixed coordinate pair
  let Cd := Cl ^ 2 * C
  let F := uniSeedA0Plus β C₀ * (epsilon β I.Λ m ^ 2 / κm)
  let G := Cg * S / Real.sqrt κprev
  have hF : 0 ≤ F := mul_nonneg hSeed0 (div_nonneg (sq_nonneg _) hκm.le)
  have hG : 0 ≤ G := div_nonneg (mul_nonneg hCg hS) (Real.sqrt_nonneg _)
  have hCd : 0 ≤ Cd := by positivity
  have hcoords (p i : Fin 2) (a j k : Fin 2) :
      eLpNorm (amnrWord b (amnrMixedWord [p, i] 0)
        (fun y => I.Amnr hΦ m κm n (T (Nstar β)) r₀ y.1 y.2 a j k)) 2 μ ≤
      ENNReal.ofReal (relativeAmnrRecursionConstant β F
          (G * relativeMixedTemperatureConstant β (uniCoeff β C₀) (uniCb β C₀) Cd ^ Nstar β)
          (uniCb β C₀) * Lr ^ ([p, i] : List (Fin 2)).length * Q ^ (0 + r₀)) := by
    refine relative_Amnr_mixed_bounds_of_spatial_profiles I hΦ (by omega) hκm hκprev hθprev hT
      n j k hμ (L := Lr) (Q := Q) (G := G) (Ccoeff := uniCoeff β C₀) (Cb := uniCb β C₀)
      (Cd := Cd) (F := F) hL hQ hG hCoeff0 hCb0 hCd hF hRate ?_ ?_ ?_ ?_ r₀ hr₀le [p, i] 0
      (by simpa using hbud) a
    · intro a' p' w hw hbudw z
      refine (hCoeff a' p' w hw hbudw z).trans ?_
      exact mul_le_mul_of_nonneg_left
        (amnrWeight_mono hS'.le hQ.le hSL le_rfl w) (mul_nonneg hCoeff0 hκprev.le)
    · intro a' p' α' r' hbudw z
      have hvel := hVel m (by omega) a' p' (amnrMixedWord α' r') (amnrMixedWord_mixed α' r')
        (by rw [amnrMixedWord_budget]; exact hbudw) z
      refine hvel.trans ?_
      exact mul_le_mul_of_nonneg_left
        (amnrWeight_mono hS'.le hQ.le hSL le_rfl _) (mul_nonneg hCb0 hQ.le)
    · intro i' hi' p' α' hα'
      exact hjets i' hi' p' α' hα'
    · intro a' p' w hw hbudw z _
      refine (hSeedU m (by omega) κm hκm n hN.le j k a' p' w hw hbudw z).trans ?_
      exact mul_le_mul_of_nonneg_left
        (amnrWeight_mono hS'.le hQ.le hSL le_rfl w) hF
  -- assemble the three-index tensor for each pair of spatial letters
  set V : ℝ := relativeAmnrRecursionConstant β F
      (G * relativeMixedTemperatureConstant β (uniCoeff β C₀) (uniCb β C₀) Cd ^ Nstar β)
      (uniCb β C₀) * Lr ^ 2 * Q ^ r₀ with hV_def
  have hBound : ∀ p i : Fin 2,
      eLpNorm (fun z : AmnrSpace => fun a j k : Fin 2 =>
        amnrWord b (amnrMixedWord [p, i] 0)
          (fun y => I.Amnr hΦ m κm n (T (Nstar β)) r₀ y.1 y.2 a j k) z) 2
        ((volume.restrict (uIoc 0 1)).prod (volume.restrict unitCube)) ≤
          ENNReal.ofReal (8 * V) := by
    intro p i
    have hmeas (a j k : Fin 2) : AEStronglyMeasurable
        (amnrWord b (amnrMixedWord [p, i] 0)
          (fun y => I.Amnr hΦ m κm n (T (Nstar β)) r₀ y.1 y.2 a j k)) μ :=
      ((amnrWord_contDiffOn hU hb2 (hreg2 a j k) (amnrMixedWord [p, i] 0) (n := 0)
        (by simp [amnrMixedWord])).continuousOn.aestronglyMeasurable hU.measurableSet
          (μ := volume)).mono_ac hμ
    have htensor : AEStronglyMeasurable (fun z : AmnrSpace => fun a j k : Fin 2 =>
        amnrWord b (amnrMixedWord [p, i] 0)
          (fun y => I.Amnr hΦ m κm n (T (Nstar β)) r₀ y.1 y.2 a j k) z) μ :=
      (aemeasurable_pi_iff.mpr (fun a => aemeasurable_pi_iff.mpr
        (fun j => aemeasurable_pi_iff.mpr
          (fun k => (hmeas a j k).aemeasurable)))).aestronglyMeasurable
    refine amnr_tensor_L2_le_eight htensor (fun a j k => ?_)
    simpa only [hV_def, List.length_cons, List.length_nil, zero_add] using hcoords p i a j k
  refine (amnr_hm_hessian_of_mixed_bound I hΦ m κm (T (Nstar β)) n r₀
    (fun a j k => hreg2 a j k) hBound).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  simp only [hV_def, relativeAmnrRecursionConstant, F, G, Lr, atbConstant, Cd]
  ring

/-- **Hessian tensor bound** (equation (5)): the `S`-amplitude AMNR Hessian tensor from the
per-iterate temperature-gradient jets. -/
theorem relative_Amnr_tensor_of_jets (β C₀ Cg Cl : ℝ) (hCg : 0 ≤ Cg) (hCl : 1 ≤ Cl) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∃ Λ₀ : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λ₀ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
      ∀ S : ℝ, 0 ≤ S →
        -- positive S-normalised spatial jets of the gradient of every partial iterate
        (∀ i, i ≤ Nstar β → ∀ (p : Fin 2) (α : List (Fin 2)), α.length ≤ Nstar β →
          eLpNorm (Infra.Section4.amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
              (α.map some) (Infra.Section4.amnrTGradient (T i) p)) 2
            ((volume.restrict (Set.uIoc 0 1)).prod (volume.restrict unitCube)) ≤
          ENNReal.ofReal (Cg * S / Real.sqrt (I.kappaSeq κ M (m - 1)) *
            (Cl * epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ α.length)) →
      ∀ r₀ ∈ Finset.range (Jcut β), ∀ n ∈ Finset.range (Nstar β),
        eLpNorm (Infra.Section4.amnrSpatialDivergenceGradientTensor I hΦ m (I.kappaSeq κ M m)
            (T (Nstar β)) n r₀) 2 (volume.restrict timeCube) ≤
          ENNReal.ofReal (CA * S * (epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m) /
            Real.sqrt (I.kappaSeq κ M (m - 1)) *
            (epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ 2 * ((tauP β I.Λ m)⁻¹) ^ r₀) := by
  by_cases hC₀1 : 1 ≤ C₀
  swap
  · exact ⟨0, le_rfl, 0, fun I hz => absurd (I.one_le_Czeta.trans hz) hC₀1⟩
  have hC₀ : 0 ≤ C₀ := by linarith
  obtain ⟨Creg, -, hregU⟩ := stream_regularity β
  obtain ⟨c, C, hc, hcC, hA5U⟩ := l_recurse β C₀
  have hC0 : 0 < C := hc.trans hcC
  have hCl0 : 0 < Cl := by linarith
  let Lc := Section3.lAmtOneStepConstant β C₀
  let P := amnrSourceRatioConstant β C
  let D : ℝ := (2 + 320 * (Lc + 1) * (P + 1)) ^ 2
  refine ⟨atbConstant β C₀ Cg Cl C, ?_, D ^ (1 / (2 * delta β)), ?_⟩
  · have hCb := one_le_uniCb β C₀
    have hseed : 0 ≤ uniSeedA0Plus β C₀ := by
      have := uniFlowGrad_nonneg β C₀
      have hMem : 0 ≤ amnrMemoryConstant β C₀ := by unfold amnrMemoryConstant; positivity
      have hAplus : 0 ≤ uniFlowAvgA0Plus β C₀ := by
        unfold uniFlowAvgA0Plus
        positivity
      unfold uniSeedA0Plus
      positivity
    have hCoeff0 : 0 ≤ uniCoeff β C₀ := by
      have := uniFlowGrad_nonneg β C₀
      have hAplus : 0 ≤ uniFlowAvgA0Plus β C₀ := by
        unfold uniFlowAvgA0Plus
        positivity
      have hQk : 0 ≤ amnrKmatStepConstant β C₀ := by
        unfold amnrKmatStepConstant; positivity
      unfold uniCoeff uniFlowAvg uniFlowAvgA0Plus
      positivity
    have hCb0 : 0 ≤ uniCb β C₀ := by linarith
    have hCd : 0 ≤ Cl ^ 2 * C := by positivity
    have hmix : 0 ≤ relativeMixedTemperatureConstant β (uniCoeff β C₀) (uniCb β C₀) (Cl ^ 2 * C)
        := by
      have hK : 0 ≤ amnrNormalOrderConstant (Nstar β) (uniCb β C₀) (Nstar β) :=
        (le_trans (by norm_num) (amnrNormalOrderConstant_one_le hCb0 _))
      unfold relativeMixedTemperatureConstant
      positivity
    unfold atbConstant
    positivity
  intro I hz hx hh hΛ₀ Φ hΦ κ hκp M hM hperm m hm hmM θ₀ θprev T hθprev hT S hS hjets r₀ hr₀ n hn
  have hreg := hregU I Φ hΦ
  have hA5 := hA5U I hz hx hh κ hκp M hM hperm
  have hκ : 0 < κ := (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (Real.rpow_pos_of_pos
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) _)).trans_le hperm.1
  have hδ := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hE := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hP : 0 ≤ P := amnrSourceRatioConstant_nonneg I hC0.le
  have hL : 0 ≤ Lc := by
    dsimp [Lc, Section3.lAmtOneStepConstant]
    positivity
  have hDpos : 0 < D := by
    have : 0 < 2 + 320 * (Lc + 1) * (P + 1) := by positivity
    positivity
  have hεΛ := epsilon_le_inv_Lambda I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1) (by omega)
  have hSmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ D⁻¹ :=
    atb_rpow_le_inv_of_large hE hεΛ (by positivity) hDpos hΛ₀
  have hpow : (epsilon β I.Λ (m - 1) ^ delta β) ^ 2 = epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
    congr 1
    ring
  have hs : (epsilon β I.Λ (m - 1) ^ delta β) ^ 2 ≤
      ((2 + 320 * (Lc + 1) * (P + 1)) ^ 2)⁻¹ := by
    rw [hpow]
    exact hSmall
  obtain ⟨hsRatio, hsAvg⟩ := amnr_source_smallness_threshold hL hP
    (Real.rpow_nonneg hE.le _) hs
  rw [hpow] at hsRatio hsAvg
  exact atb_core hCg hCl I hz hh hc hcC hΦ hreg hκ hperm hA5 hm hmM hsRatio hsAvg hθprev hT hS
    hjets hr₀ hn

end AVenhance.Infra.Section5.RelativeError
