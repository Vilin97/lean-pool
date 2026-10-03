/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.SourceErrorDBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.SourceErrorDMeas
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.SourceErrorDScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.SourceErrorDTail
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.SourceErrorDTheta
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersV
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.ThetaProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorJets

/-! # `SourceErrorDContract` producers

`sourceErrorD_of_jets_contract` produces `SourceErrorDContract` at an abstract amplitude `B`,
conditionally on the three existing contracts at that amplitude: `ThetaProfileContract`,
`VIncrementContract`, `TGradientContract`.  `sourceErrorD_contract` is the exact unconditional
producer at the big-bound/step-down part (i) amplitude `B = ‖θ₀‖`.

Route (paper `p.dm.bounds` with `N_*` large):
* the first summand `Σ_l ξ̂_{m,l} F_lᵀ (JHat_m - J_m) F_l ∇T` is bounded in `L²` by
  `2 F_gap · 4 L² ‖∇T‖` with `L = 2` (stream-function flow Jacobian bound on active windows,
  `dm_flowGrad_norm_le_two_of_A3`; `‖∇T‖_{L²}` by the T profile through the time clamp,
  `sed_Tgrad_eLpNorm_le`), where `F_gap` is the flux gap bound (`flux_sub_Jhat_norm_le`);
* the tail `Σ_n A_{m,n,Jcut} q_{m,n,Jcut}` uses the terminal AMNR tensor (`sed_tail_amnr_of_jets`,
  from the `∇T_i` jets of `relative_iterate_gradient_jets`) and the geometric `qMNR` bound;
* both are of the paper scale `√κ_{m-1} (C ε_{m-1}^{δ/2})^{Jcut}`, which is at most
  `C ε_{m-1}^{2δ} √κ_m` because `δ Jcut / 2 ≥ 2δ + qβ` and `ε_m^{2β} ≤ K κ_{m-1} κ_m`
  (`sed_final_scale`). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.Integration
  AVenhance.Infra.Section5

/-- `a_m² ε_m⁴ = ε_m^{2β}`, hence `a_m² ε_m⁴/κ_m ≤ K κ_{m-1}` gives `ε_m^{2β} ≤ K κ_{m-1} κ_m`. -/
theorem sed_K2_rpow {β : ℝ} (I : Ingredients β) (m : ℕ) {κm κp K : ℝ} (hκm : 0 < κm)
    (h : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm ≤ K * κp) :
    epsilon β I.Λ m ^ (2 * β) ≤ K * κp * κm := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have h1 : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 = epsilon β I.Λ m ^ (2 * β) := by
    unfold a
    rw [sc_rpow_sq hε, ← Real.rpow_natCast (epsilon β I.Λ m) 4, ← Real.rpow_add hε]
    congr 1
    push_cast
    ring
  rw [h1, div_le_iff₀ hκm] at h
  linarith

/-- **`SourceErrorDContract` producer**, abstract amplitude `B`, conditional on the θ profile, the
`V` increments and the integrated `T` gradient at that amplitude. -/
theorem sourceErrorD_of_jets_contract (β C₀ Cs A : ℝ) (hCs : 0 < Cs) (hA : 0 ≤ A) :
    ∃ Cd C₁ : ℝ, 0 ≤ Cd ∧
      OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m θprev T =>
        ∀ B : ℝ, 0 ≤ B → ∀ Rθ : ℝ, epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ →
          ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs B →
          VIncrementContract I m (I.kappaSeq κ M (m - 1)) T Cs Rθ B →
          TGradientContract β (I.kappaSeq κ M (m - 1)) T A B →
          SourceErrorDContract I hΦ m (I.kappaSeq κ M m) T Cd B) := by
  by_cases hb : 1 < β ∧ β < 4 / 3
  swap
  · refine ⟨0, 0, le_rfl, ?_⟩
    intro I
    exact absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb
  obtain ⟨K, hK1, hK⟩ := LeftToShow.left_to_show_scales β C₀
  obtain ⟨Cg, hCg, Λa, hJets⟩ := RelativeError.relative_iterate_gradient_jets β Cs hCs
  obtain ⟨CA, hCA, Λb, hTail⟩ := sed_tail_amnr_of_jets β C₀ Cg (max Cs 1) hCg (le_max_right _ _)
  obtain ⟨Creg, -, hregU⟩ := stream_regularity β
  have hδ0 : 0 < delta β := Infra.Ingredients.delta_pos hb.1 hb.2
  have hK0 : 0 ≤ K := by linarith
  set C₀' : ℝ := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  let Nn : ℝ := (Nstar β : ℝ)
  let Cb : ℝ := K ^ 3 + 2 + 1
  let Ctot : ℝ := (2 * (4 * Real.pi ^ 2 * C₀' * Nn * 2 ^ Nstar β) * K * 16) +
    Nn * (8 * (4 * Real.pi ^ 2 * C₀') * CA * K)
  let Cd : ℝ := 2 * (Ctot * ((1 + A) * Cb ^ Jcut β * 2 ^ β * K * Real.sqrt K))
  have hCb0 : 0 ≤ Cb := by positivity
  have hCtot0 : 0 ≤ Ctot := by positivity
  refine ⟨Cd, max (max Λa Λb) (K ^ (1 / (2 * delta β))), by positivity, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκp M hM hperm R hR θ₀ hs hp hmz ha m hm hmM θprev T hθprev hT
    B hB Rθ hRθ hTheta hV hTG
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  obtain ⟨-, hmono, hκpK, hK2, hK3, -, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm2 hmM
  have hκp0 : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hmono
  have hΛa : Λa ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛ
  have hΛb : Λb ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛ
  have hΛK : K ^ (1 / (2 * delta β)) ≤ (I.Λ : ℝ) := le_trans (le_max_right _ _) hΛ
  -- the jets of `∇T_i` and the terminal AMNR tensor
  have hjets := hJets I hΛa Φ hΦ κ M m hm2 θ₀ θprev T hκm hκp0 hθprev hT B Rθ hB hRθ hTheta hV
  have hAmnr := hTail I hz hx hh hΛb Φ hΦ κ hκp M hM hperm m hm2 hmM θ₀ θprev T hθprev hT B hB
    hjets
  -- notation
  set κm := I.kappaSeq κ M m with hκm_def
  set κp := I.kappaSeq κ M (m - 1) with hκp_def
  set x := epsilon β I.Λ (m - 1) with hxdef
  set εm := epsilon β I.Λ m with hεm_def
  have hx0 : 0 < x := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hx1 : x ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  have hεm0 : 0 < εm := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hQ : 0 < (tauP β I.Λ m)⁻¹ :=
    inv_pos.mpr (Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hsqκp : 0 < Real.sqrt κp := Real.sqrt_pos.2 hκp0
  -- the amplitude `Θ`
  set Θ : ℝ := (1 + A) * B with hΘ
  have hΘ0 : 0 ≤ Θ := by positivity
  have hBΘ : B ≤ Θ := by
    have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 1 + A) hB
    linarith
  -- classical solution and gradient continuity
  obtain ⟨F, hF⟩ := amnr_tIterates_classical_family I hΦ hθprev hT (Nstar β) le_rfl
  have hc := sed_gradient_continuousOn hF
  have hTΘ : Real.sqrt κp * Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (T (Nstar β) t))) ≤ Θ := by
    have h := hTG
    unfold TGradientContract at h
    have hAB : A * B ≤ Θ := by
      have : A * B ≤ (1 + A) * B := mul_le_mul_of_nonneg_right (by linarith) hB
      exact this
    exact le_trans h hAB
  have hflow := dm_flowGrad_norm_le_two_of_A3 I hΦ (hregU I Φ hΦ) (by omega : 1 ≤ m)
  have hTgrad := sed_Tgrad_eLpNorm_le hc hκp0 hTΘ
  -- measurability
  have hfirst := sed_firstMeas I hΦ (m := m) (by omega) hκm hc
  have hAentry := fun n (_ : n ∈ Finset.range (Nstar β)) i j k =>
    sed_amnrEntry_meas I hΦ (m := m) (by omega) hκm hθprev hT n i j k
  have hcoord := fun n (hn : n ∈ Finset.range (Nstar β)) i j k =>
    sed_coordinate_meas I hΦ m κm (T (Nstar β)) n i j k (hAentry n hn i j k)
  have hdmeas := sed_sourceErrorD_meas I hΦ m κm (T (Nstar β)) hfirst hcoord
  -- scale data
  have hratio : εm ^ 2 / (κm * tau β I.Λ m) ≤ 1 := by
    have hεΛ := LeftToShow.epsilon_le_inv_Lambda I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (m := m - 1) (by omega)
    have hsmall : x ^ (2 * delta β) ≤ K⁻¹ :=
      RelativeError.atb_rpow_le_inv_of_large hx0 hεΛ (by positivity) (by linarith) hΛK
    refine hK3.trans ?_
    calc K * x ^ (2 * delta β) ≤ K * K⁻¹ := mul_le_mul_of_nonneg_left hsmall hK0
      _ = 1 := mul_inv_cancel₀ (by linarith)
  have hcut : 2 ≤ Jcut β := by
    have h := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    unfold Jcut
    omega
  have hTimeRatio := (time_ratio_bounds I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (by omega : 1 ≤ m)).2
  have hA' : 0 ≤ CA * B * (εm ^ 2 / κm) / Real.sqrt κp * ((tauP β I.Λ m)⁻¹) ^ Jcut β ∧
      CA * B * (εm ^ 2 / κm) / Real.sqrt κp * ((tauP β I.Λ m)⁻¹) ^ Jcut β ≤
        CA * Θ * (εm ^ 2 / κm) * (Real.sqrt κp)⁻¹ * x ^ (-(2 + gamma β)) *
          ((tauP β I.Λ m)⁻¹) ^ Jcut β := by
    have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
    have hone : 1 ≤ x ^ (-(2 + gamma β)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx1 (by linarith)
    have hF0 : 0 ≤ εm ^ 2 / κm := by positivity
    constructor
    · positivity
    · have hP : 0 ≤ CA * (εm ^ 2 / κm) * (Real.sqrt κp)⁻¹ * ((tauP β I.Λ m)⁻¹) ^ Jcut β := by
        positivity
      calc CA * B * (εm ^ 2 / κm) / Real.sqrt κp * ((tauP β I.Λ m)⁻¹) ^ Jcut β
          = (CA * (εm ^ 2 / κm) * (Real.sqrt κp)⁻¹ * ((tauP β I.Λ m)⁻¹) ^ Jcut β) * B * 1 := by
            field_simp
        _ ≤ (CA * (εm ^ 2 / κm) * (Real.sqrt κp)⁻¹ * ((tauP β I.Λ m)⁻¹) ^ Jcut β) * Θ *
              x ^ (-(2 + gamma β)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hBΘ hP) hone (by norm_num)
              (mul_nonneg hP hΘ0)
        _ = _ := by ring
  have hbound := sed_eLpNorm_le (C₀ := C₀') (Csrc := CA) (Cprod := K) (Cexpr := K) (Θ := Θ)
    (κprev := κp) (A := CA * B * (εm ^ 2 / κm) / Real.sqrt κp * ((tauP β I.Λ m)⁻¹) ^ Jcut β)
    I hΦ (m := m) (by omega) κm (T (Nstar β)) (hz.trans (le_max_left _ _)) hκm hκp0 hC₀'0 hCA
    hK0 hK1 (by linarith [I.one_le_Czeta]) hΘ0 hK2 hK3 hTimeRatio hA' hflow hTgrad hfirst hAmnr
    (fun n hn i j k => hAentry n hn i j k) hcoord hratio hcut
  have hpow : x ^ q β ≤ 2 * εm := by
    have := LeftToShow.epsilon_pred_pow_q_div_two_le hb.1 hb.2 I.two_pow_seven_le hm2
    linarith
  have hε : εm ^ (2 * β) ≤ K * κp * κm := sed_K2_rpow I m hκm hK2
  have hscale := sed_final_scale (x := x) (εm := εm) (κm := κm) (κp := κp) (K := K) (Θ := Θ)
    (Cb := Cb) (δ := delta β) (q := q β) (β := β) (J := Jcut β) hx0 hx1 hεm0 hκm hκp0 hK1 hκpK
    (by linarith [hb.1]) hpow hε (sed_jcut_budget hb.1 hb.2) hΘ0 hCb0
  have hCz : I.Czeta ≤ C₀' := hz.trans (le_max_left _ _)
  have hCtot : (2 * (4 * Real.pi ^ 2 * I.Czeta * (Nstar β : ℝ) * 2 ^ Nstar β) * K * 16) +
      (Nstar β : ℝ) * (8 * (4 * Real.pi ^ 2 * C₀') * CA * K) ≤ Ctot := by
    have := I.one_le_Czeta
    dsimp only [Ctot, Nn]
    gcongr
  unfold SourceErrorDContract
  refine (sed_lhs_le_eLpNorm (sourceErrorD I hΦ m κm (T (Nstar β))) hdmeas).trans ?_
  have hX : ∀ X : ℝ, eLpNorm (fun z : ℝ × Vec 2 => sourceErrorD I hΦ m κm (T (Nstar β)) z.1 z.2) 2
      (volume.restrict timeCube) ≤ ENNReal.ofReal X →
      X ≤ Cd * x ^ (2 * delta β) * Real.sqrt κm * B / 2 →
      2 * eLpNorm (fun z : ℝ × Vec 2 => sourceErrorD I hΦ m κm (T (Nstar β)) z.1 z.2) 2
        (volume.restrict timeCube) ≤ ENNReal.ofReal (Cd * x ^ (2 * delta β) * Real.sqrt κm * B) :=
            by
    intro X hXb hXle
    calc 2 * eLpNorm (fun z : ℝ × Vec 2 => sourceErrorD I hΦ m κm (T (Nstar β)) z.1 z.2) 2
          (volume.restrict timeCube) ≤ 2 * ENNReal.ofReal X := by gcongr
      _ = ENNReal.ofReal (2 * X) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  refine hX _ hbound ?_
  have h1 : 0 ≤ Real.sqrt κp * Θ * (Cb * x ^ (delta β / 2)) ^ Jcut β := by positivity
  have h2 := mul_le_mul hCtot hscale h1 hCtot0
  have h3 : (((2 * (4 * Real.pi ^ 2 * I.Czeta * (Nstar β : ℝ) * 2 ^ Nstar β) * K * 16) +
              (Nstar β : ℝ) * (8 * (4 * Real.pi ^ 2 * C₀') * CA * K)) *
              (Real.sqrt κp * Θ) * ((K ^ 3 + 2 + 1) * x ^ (delta β / 2)) ^ Jcut β)
            = ((2 * (4 * Real.pi ^ 2 * I.Czeta * (Nstar β : ℝ) * 2 ^ Nstar β) * K * 16) +
              (Nstar β : ℝ) * (8 * (4 * Real.pi ^ 2 * C₀') * CA * K)) *
              (Real.sqrt κp * Θ * (Cb * x ^ (delta β / 2)) ^ Jcut β) := by
    simp only [Cb]; ring
  rw [h3]
  calc _ ≤ Ctot * ((Θ * Cb ^ Jcut β * 2 ^ β * K * Real.sqrt K) * x ^ (2 * delta β) *
              Real.sqrt κm) := h2
    _ = Cd * x ^ (2 * delta β) * Real.sqrt κm * B / 2 := by
        simp only [Cd, Θ]; ring

/-- **`SourceErrorDContract` producer, exact unconditional form** at the big-bound/step-down part
    (i) amplitude
`B = ‖θ₀‖_{L²}` (`e.monster.est.11.a.d`).  Constants (`Cd`, the Λ-threshold) depend only on
`β, C₀`. -/
theorem sourceErrorD_contract (β C₀ : ℝ) :
    ∃ Cd C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
      SourceErrorDContract I hΦ m (I.kappaSeq κ M m) T Cd (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨cv, Cv, hcv, hcvC, hv⟩ := iterate_V_upgrade_of_theta β C₀
  obtain ⟨Cθ, hθ⟩ := sed_thetaProfile_A7 β C₀
  obtain ⟨A, C₁A, hTG⟩ := tGradient_contract β C₀
  let Cs : ℝ := max (max (iterateReducedSourceConstant β C₀ cv Cv 40 (2 ^ 10) 1) Cθ) 1
  have hCs1 : 1 ≤ Cs := le_max_right _ _
  have hCsV : iterateReducedSourceConstant β C₀ cv Cv 40 (2 ^ 10) 1 ≤ Cs :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hCsθ : Cθ ≤ Cs := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨C₁s, hscale⟩ := iterate_contract_scales β Cs hCs1
  obtain ⟨Cd, C₁d, hCd0, hcond⟩ := sourceErrorD_of_jets_contract β C₀ Cs (max A 0)
    (by linarith) (le_max_right _ _)
  refine ⟨2 * Cd, max (max C₁d C₁s) (max C₁A 0), ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκp M hM hperm R hR θ₀ hs hp hmz ha m hm hmM θprev T hθprev hT
  have hΛd : C₁d ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛ
  have hΛs : C₁s ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛ
  have hΛA : C₁A ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΛ
  obtain ⟨hm2, hradius, hsmall⟩ := hscale I hΛs R hR m hm
  have hTheta := hθ Cs hCsθ I hz hx hh (Nat.cast_nonneg _) Φ hΦ κ hκp M hM hperm R hR θ₀ hs hp
    hmz ha m hm hmM θprev T hθprev hT
  have hN0 : 0 ≤ 2 * Real.sqrt (l2NormSq θ₀) := by positivity
  have hVinc : VIncrementContract I m (I.kappaSeq κ M (m - 1)) T Cs R
      (2 * Real.sqrt (l2NormSq θ₀)) :=
    hv I hz hx hh hΦ κ M hT hθprev hm2 hmM hperm 1 R Cs _ hN0 hR hCsV hradius hsmall hTheta
  have hTG' := hTG I hz hx hh hΛA Φ hΦ κ hκp M hM hperm R hR θ₀ hs hp hmz ha m hm hmM θprev T
    hθprev hT
  have hs0 : 0 ≤ Real.sqrt (l2NormSq θ₀) := Real.sqrt_nonneg _
  have hTGc : TGradientContract β (I.kappaSeq κ M (m - 1)) T (max A 0)
      (2 * Real.sqrt (l2NormSq θ₀)) := by
    unfold TGradientContract at hTG' ⊢
    refine hTG'.trans ?_
    have h1 : A ≤ max A 0 := le_max_left _ _
    have h2 : 0 ≤ max A 0 := le_max_right _ _
    nlinarith
  have h := hcond I hz hx hh hΛd Φ hΦ κ hκp M hM hperm R hR θ₀ hs hp hmz ha m hm hmM θprev T
    hθprev hT (2 * Real.sqrt (l2NormSq θ₀)) hN0 R hradius hTheta hVinc hTGc
  unfold SourceErrorDContract at h ⊢
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

end AVenhance.Infra.Section5.Contracts

end
