/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorBound

/-! # `SourceErrorDContract`: the terminal `A_{m,n,Jcut}` tensor in `L²`

The tail of `d_m` is `Σ_n A_{m,n,Jcut} q_{m,n,Jcut}`.  Its `L²` norm needs the AMNR tensor itself
at level `Jcut` (no derivatives), which is the case `α = []`, `ℓ = 0`, `ρ = Jcut` of the
amplitude-generic recursion `relative_Amnr_mixed_bounds_of_spatial_profiles`.  The constants are
`I`-uniform (the same primitive bounds as `RelativeError.relative_Amnr_tensor_of_jets`), the
    amplitude `S`
is abstract, and the temperature input is the positive-order spatial jets of `∇T_i`
(`RelativeError.relative_iterate_gradient_jets`). -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Set
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.RelativeError
  AVenhance.Infra.Section5.LeftToShow

/-- The `I`-uniform constant of the terminal AMNR tensor. -/
def sedTailConstant (β C₀ Cg Cl C : ℝ) : ℝ :=
  8 * (2 * (2 : ℝ) ^ (Nstar β) * uniSeedA0Plus β C₀ * Cg *
    relativeMixedTemperatureConstant β (uniCoeff β C₀) (uniCb β C₀) (Cl ^ 2 * C) ^ Nstar β *
    (1 + (2 : ℝ) ^ (Nstar β + 1) * uniCb β C₀) ^ Jcut β)

/-- Fixed-`I` core of the terminal AMNR tensor estimate. -/
theorem sed_tail_core {β Creg C₀ c C Cg Cl : ℝ} (hCg : 0 ≤ Cg) (hCl : 1 ≤ Cl)
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
    {n : ℕ} (hn : n ∈ Finset.range (Nstar β)) :
    eLpNorm (fun z : AmnrSpace =>
        I.Amnr hΦ m (I.kappaSeq κ M m) n (T (Nstar β)) (Jcut β) z.1 z.2) 2
        (volume.restrict timeCube) ≤
      ENNReal.ofReal (sedTailConstant β C₀ Cg Cl C * S *
        (epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m) / Real.sqrt (I.kappaSeq κ M (m - 1)) *
        ((tauP β I.Λ m)⁻¹) ^ Jcut β) := by
  have hN := Finset.mem_range.mp hn
  have hJ : 0 + Jcut β ≤ Nstar β := by
    have := Infra.Section4.Jcut_budget (β := β) (by omega)
    omega
  have hbud : ([] : List (Fin 2)).length + 2 * 0 ≤ Nstar β - 2 * Jcut β := by simp
  have hCl0 : 0 < Cl := by linarith
  have hC0 : 0 < C := hc.trans hcC
  have hE : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hS' : 0 < epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)) := Real.rpow_pos_of_pos hE _
  have hτ : 0 < tauP β I.Λ m := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hQ : 0 < (tauP β I.Λ m)⁻¹ := inv_pos.mpr hτ
  have hκm : 0 < I.kappaSeq κ M m := Infra.Section3.kappaAt_pos I hκ m (M - m)
  have hκprev : 0 < I.kappaSeq κ M (m - 1) := Infra.Section3.kappaAt_pos I hκ (m - 1) (M - (m - 1))
  set κm := I.kappaSeq κ M m with hκm_def
  set κprev := I.kappaSeq κ M (m - 1) with hκprev_def
  set S' := epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)) with hS'_def
  set Q := (tauP β I.Λ m)⁻¹ with hQ_def
  set Lr := Cl * S' with hLr_def
  have hL : 0 < Lr := mul_pos hCl0 hS'
  have hSL : S' ≤ Lr := by
    have := mul_le_mul_of_nonneg_right hCl hS'.le
    simpa [hLr_def] using this
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
  let U : Set AmnrSpace := Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))
  let μ : Measure AmnrSpace :=
    (volume.restrict (Set.uIoc 0 1)).prod (volume.restrict unitCube)
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hμ : μ ≪ volume.restrict U := amnr_time_cell_product_absolutelyContinuous (by norm_num)
  let b := fun y : AmnrSpace => streamVel (Φ (m - 1)) y.1 y.2
  have hbInf : ContDiff ℝ (⊤ : ℕ∞) b :=
    contDiff_infty.mpr (fun N => amnr_previous_velocity_contDiff I hΦ (by omega) N)
  have hb0 : ContDiffOn ℝ 0 b U := (hbInf.of_le (by simp)).contDiffOn
  have hreg0 (a j k : Fin 2) : ContDiffOn ℝ 0
      (fun z : AmnrSpace => I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) z.1 z.2 a j k) U :=
    amnr_actual_contDiffOn I hΦ (by omega) hκm hθprev hT n (Jcut β) 0 hJ a j k
  let Cd := Cl ^ 2 * C
  let F := uniSeedA0Plus β C₀ * (epsilon β I.Λ m ^ 2 / κm)
  let G := Cg * S / Real.sqrt κprev
  have hF : 0 ≤ F := mul_nonneg hSeed0 (div_nonneg (sq_nonneg _) hκm.le)
  have hG : 0 ≤ G := div_nonneg (mul_nonneg hCg hS) (Real.sqrt_nonneg _)
  have hCd : 0 ≤ Cd := by positivity
  have hcoords (a j k : Fin 2) :
      eLpNorm (amnrWord b (amnrMixedWord [] 0)
        (fun y => I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) y.1 y.2 a j k)) 2 μ ≤
      ENNReal.ofReal (relativeAmnrRecursionConstant β F
          (G * relativeMixedTemperatureConstant β (uniCoeff β C₀) (uniCb β C₀) Cd ^ Nstar β)
          (uniCb β C₀) * Lr ^ ([] : List (Fin 2)).length * Q ^ (0 + Jcut β)) := by
    refine relative_Amnr_mixed_bounds_of_spatial_profiles I hΦ (by omega) hκm hκprev hθprev hT
      n j k hμ (L := Lr) (Q := Q) (G := G) (Ccoeff := uniCoeff β C₀) (Cb := uniCb β C₀)
      (Cd := Cd) (F := F) hL hQ hG hCoeff0 hCb0 hCd hF hRate ?_ ?_ ?_ ?_ (Jcut β) le_rfl [] 0
      hbud a
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
  have hmeasU (a j k : Fin 2) : AEStronglyMeasurable
      (fun z : AmnrSpace => I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) z.1 z.2 a j k) μ :=
    ((hreg0 a j k).continuousOn.aestronglyMeasurable hU.measurableSet (μ := volume)).mono_ac hμ
  have htensor : AEStronglyMeasurable (fun z : AmnrSpace => fun a j k : Fin 2 =>
      I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) z.1 z.2 a j k) μ :=
    (aemeasurable_pi_iff.mpr (fun a => aemeasurable_pi_iff.mpr
      (fun j => aemeasurable_pi_iff.mpr
        (fun k => (hmeasU a j k).aemeasurable)))).aestronglyMeasurable
  set V : ℝ := relativeAmnrRecursionConstant β F
      (G * relativeMixedTemperatureConstant β (uniCoeff β C₀) (uniCb β C₀) Cd ^ Nstar β)
      (uniCb β C₀) * Lr ^ 0 * Q ^ (0 + Jcut β) with hV_def
  have hbound := amnr_tensor_L2_le_eight htensor (B := V) (fun a j k => by
    simpa only [hV_def, List.length_nil, amnrMixedWord, List.map_nil, List.replicate_zero,
      List.append_nil, amnrWord] using hcoords a j k)
  have hmu : μ = volume.restrict timeCube := amnr_product_measure_eq_timeCube
  rw [← hmu]
  refine hbound.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  simp only [hV_def, relativeAmnrRecursionConstant, F, G, sedTailConstant, Cd, pow_zero, mul_one,
    zero_add, pow_succ]
  ring

/-- **Terminal AMNR tensor at amplitude `S`** from the per-iterate temperature-gradient jets, with
`I`-uniform constants. -/
theorem sed_tail_amnr_of_jets (β C₀ Cg Cl : ℝ) (hCg : 0 ≤ Cg) (hCl : 1 ≤ Cl) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∃ Λ₀ : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λ₀ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
      ∀ S : ℝ, 0 ≤ S →
        (∀ i, i ≤ Nstar β → ∀ (p : Fin 2) (α : List (Fin 2)), α.length ≤ Nstar β →
          eLpNorm (Infra.Section4.amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
              (α.map some) (Infra.Section4.amnrTGradient (T i) p)) 2
            ((volume.restrict (Set.uIoc 0 1)).prod (volume.restrict unitCube)) ≤
          ENNReal.ofReal (Cg * S / Real.sqrt (I.kappaSeq κ M (m - 1)) *
            (Cl * epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ α.length)) →
      ∀ n ∈ Finset.range (Nstar β),
        eLpNorm (fun z : AmnrSpace =>
            I.Amnr hΦ m (I.kappaSeq κ M m) n (T (Nstar β)) (Jcut β) z.1 z.2) 2
            (volume.restrict timeCube) ≤
          ENNReal.ofReal (CA * S * (epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m) /
            Real.sqrt (I.kappaSeq κ M (m - 1)) * ((tauP β I.Λ m)⁻¹) ^ Jcut β) := by
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
  refine ⟨sedTailConstant β C₀ Cg Cl C, ?_, D ^ (1 / (2 * delta β)), ?_⟩
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
    unfold sedTailConstant
    positivity
  intro I hz hx hh hΛ₀ Φ hΦ κ hκp M hM hperm m hm hmM θ₀ θprev T hθprev hT S hS hjets n hn
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
  exact sed_tail_core hCg hCl I hz hh hc hcC hΦ hreg hκ hperm hA5 hm hmM hsRatio hsAvg hθprev hT
    hS hjets hn

end AVenhance.Infra.Section5.Contracts

end
