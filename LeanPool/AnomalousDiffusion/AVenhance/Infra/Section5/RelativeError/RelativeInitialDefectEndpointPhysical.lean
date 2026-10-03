/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectEndpointScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectEndpointJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityHm

/-! The actual positive-time endpoint source at the physical amplitude scale.
All regularity is proved from the T iterates. The quantitative gradient profile
is the output of EndpointJets, including the terminal one-letter level. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section4
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

/-- The physical endpoint is L2 with amplitude sqrt(kappa_prev)*L*S, at every
level through Jcut. No initial-time Amnr or Hm value is used. -/
theorem relative_initial_endpoint_L2_of_gradient_profile {β C₀ CA K L S : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm ν : ℝ} (hκm : 0 < κm) (hν : 0 < ν)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) ν (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm ν g θprev T)
    (hz : I.Czeta ≤ C₀) (hCA : 0 ≤ CA) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hRatio : epsilon β I.Λ m ^ 2 / (κm * tau β I.Λ m) ≤ 1)
    (hTime : 8 * tau β I.Λ m / tauP β I.Λ m ≤ 1)
    (hX : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm ≤ K * ν)
    {r : ℕ} (hr : r ≤ Jcut β)
    (hAmnr : ∀ n ∈ Finset.range (Nstar β),
      eLpNorm (amnrSpatialGradientTensor I hΦ m κm (T (Nstar β)) n r) 2
        (volume.restrict timeCube) ≤
      ENNReal.ofReal (CA * S * (epsilon β I.Λ m ^ 2 / κm) / Real.sqrt ν * L *
        ((tauP β I.Λ m)⁻¹) ^ r)) :
    eLpNorm (fun z : ℝ × Vec 2 => hmEndpoint I hΦ m κm (T (Nstar β)) r z.1 z.2) 2
      (volume.restrict timeCube) ≤
    ENNReal.ofReal ((Nstar β : ℝ) * (8 * (4 * Real.pi ^ 2 * C₀) * CA * K *
      Real.sqrt ν * L * S)) := by
  have hbud : 1 ≤ Nstar β - 2 * r := relative_initial_endpoint_budget I hr
  have hμ : volume.restrict timeCube ≪ volume.restrict
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    Measure.absolutelyContinuous_of_le (Measure.restrict_mono
      (show timeCube ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) from
        fun z hz => ⟨hz.1.1, Set.mem_univ _⟩) le_rfl)
  have hreg (n : ℕ) (i j k : Fin 2) : ContDiffOn ℝ 1
      (fun z : AmnrSpace => I.Amnr hΦ m κm n (T (Nstar β)) r z.1 z.2 i j k)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    amnr_actual_contDiffOn I hΦ hm hκm hθ hT n r 1 (by omega) i j k
  have hmGrad (n : ℕ) (i j k p : Fin 2) : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => spaceGrad
        (fun x => I.Amnr hΦ m κm n (T (Nstar β)) r z.1 x i j k) z.2 p)
      (volume.restrict timeCube) := by
    have hs := contDiffOn_spaceGrad_slice_Ioi
      (F := fun t x => I.Amnr hΦ m κm n (T (Nstar β)) r t x i j k)
      (amnr_contDiffOn_Ioi_top I hΦ hm hκm hθ hT n r i j k) p
    exact (hs.continuousOn.aestronglyMeasurable (isOpen_Ioi.prod isOpen_univ).measurableSet
      (μ := volume)).mono_ac hμ
  have hD (n : ℕ) (i j k : Fin 2) (t : ℝ) (ht : 0 < t) (x : Vec 2) :
      DifferentiableAt ℝ (fun y : Vec 2 =>
        I.Amnr hΦ m κm n (T (Nstar β)) r t y i j k) x := by
    have h := (hreg n i j k).contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (show (t, x) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) from
          ⟨ht, Set.mem_univ x⟩))
    exact ((h.differentiableAt (by norm_num)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right t x)).differentiableAt
  have hbound := relative_initial_endpoint_L2_of_Amnr_gradient I hΦ m κm (T (Nstar β)) r
    hμ hz hm hκm hAmnr (fun n _ => hmGrad n) (fun n _ => hD n)
  have he : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  have hτP : 0 < tauP β I.Λ m :=
    Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hC₀ : 0 ≤ C₀ := le_trans (by linarith only [I.one_le_Czeta]) hz
  exact hbound.trans (relative_initial_endpoint_coefficient_sum_le he hκm hν hτ hτP
    (by positivity : 0 ≤ 4 * Real.pi ^ 2 * C₀) hCA hL hS hRatio hTime hX (Nstar β) r)

/-- The actual material source is the terminal endpoint minus the zeroth
endpoint. Both estimates use only one spatial letter at their respective levels. -/
theorem relative_initial_material_source_L2_of_gradient_profiles {β C₀ CA K L S : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm ν : ℝ} (hκm : 0 < κm) (hν : 0 < ν)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) ν (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm ν g θprev T)
    (hz : I.Czeta ≤ C₀) (hCA : 0 ≤ CA) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hRatio : epsilon β I.Λ m ^ 2 / (κm * tau β I.Λ m) ≤ 1)
    (hTime : 8 * tau β I.Λ m / tauP β I.Λ m ≤ 1)
    (hX : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm ≤ K * ν)
    (hAmnr : ∀ r, r ≤ Jcut β → ∀ n ∈ Finset.range (Nstar β),
      eLpNorm (amnrSpatialGradientTensor I hΦ m κm (T (Nstar β)) n r) 2
        (volume.restrict timeCube) ≤
      ENNReal.ofReal (CA * S * (epsilon β I.Λ m ^ 2 / κm) / Real.sqrt ν * L *
        ((tauP β I.Λ m)⁻¹) ^ r)) :
    eLpNorm (fun z : ℝ × Vec 2 =>
      hmEndpoint I hΦ m κm (T (Nstar β)) (Jcut β) z.1 z.2 -
        hmEndpoint I hΦ m κm (T (Nstar β)) 0 z.1 z.2) 2
      (volume.restrict timeCube) ≤
    ENNReal.ofReal (2 * ((Nstar β : ℝ) *
      (8 * (4 * Real.pi ^ 2 * C₀) * CA * K * Real.sqrt ν * L * S))) := by
  have hbound (r : ℕ) (hr : r ≤ Jcut β) :=
    relative_initial_endpoint_L2_of_gradient_profile I hΦ hm hκm hν hθ hT
      hz hCA hL hS hRatio hTime hX hr (hAmnr r hr)
  have hE : 0 ≤ (Nstar β : ℝ) *
      (8 * (4 * Real.pi ^ 2 * C₀) * CA * K * Real.sqrt ν * L * S) := by
    have hK : 0 ≤ K := by
      have hx0 : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm := by positivity
      exact nonneg_of_mul_nonneg_left (hx0.trans hX) hν
    have hC₀ : 0 ≤ C₀ := le_trans (by linarith only [I.one_le_Czeta]) hz
    positivity
  calc
    _ ≤ _ + _ := eLpNorm_sub_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ _ + _ := add_le_add (hbound (Jcut β) le_rfl) (hbound 0 (Nat.zero_le _))
    _ = _ := by rw [← ENNReal.ofReal_add hE hE]; congr 1; ring

end AVenhance.Infra.Section5.RelativeError
