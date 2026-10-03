/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxesSlice
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFluxL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFluxPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFluxScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmExtension
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityPeriodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales

/-! # Source contracts of the divergence-form terms `twistie3`, `normie1`, `normie2`

Producers of `Twistie3SourceContract`, `Normie1SourceContract` and `Normie2SourceContract` in the
abstract-amplitude form (`B` free), conditional on the input contracts at the same amplitude `B`:

* `twistie3Source_contract` from `TGradientContract` (source `e.monster.est.7`);
* `normie1Source_contract` from `FirstOrderGradJetContract` and `TGradientContract`
  (source `e.monster.est.10`);
* `normie2Source_contract` from `HmGradientContract` (source `e.monster.est.11`).

The proofs use the flux L² bound `|flux|² ≤ ∑ c_j |V_j|²` pointwise (`TermSourcesFluxPointwise`),
the space-time transfer `saTimeL2_le_of_pointwise` and the scale package `left_to_show_scales`. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
  AVenhance.Infra.Section5.RelativeError

/-! ### Continuity inputs -/

theorem sa_gradT_cont {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
  (continuousOn_spaceGrad_joint hT i).mono (Set.prod_mono Set.Icc_subset_Ici_self le_rfl)

theorem sa_hess_cont {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (q i : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      spaceGrad (Infra.Section4.iterateSpatialWord [q] (T p.1)) p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
  (continuousOn_spaceHess_joint hT i q).mono (Set.prod_mono Set.Icc_subset_Ici_self le_rfl)

/-- `∇HTilde_m` extends continuously to `[0,∞) × ℝ²`. -/
theorem sa_Hm_grad_extends {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ∃ Gh : ℝ × Vec 2 → Vec 2,
      (∀ i, ContinuousOn (fun p => Gh p i) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) ∧
      ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)),
        spaceGrad (I.Hm hΦ m κm (T (Nstar β)) p.1) p.2 = Gh p := by
  obtain ⟨Hhat, hHhat, hHeq⟩ := Hm_extends_Ici I hΦ hm hκm hθprev hT
  refine ⟨fun p => spaceGrad (fun y => Hhat (p.1, y)) p.2, fun i => ?_, ?_⟩
  · exact (contDiffOn_spaceGrad_slice (F := fun t y => Hhat (t, y)) hHhat i).continuousOn
  · rintro ⟨t, x⟩ ⟨ht, -⟩
    have hfun : I.Hm hΦ m κm (T (Nstar β)) t = fun y => Hhat (t, y) := by
      funext y
      exact hHeq (t, y) ⟨ht, trivial⟩
    change spaceGrad (I.Hm hΦ m κm (T (Nstar β)) t) x = spaceGrad (fun y => Hhat (t, y)) x
    rw [hfun]

/-! ### `twistie3` -/

theorem twistie3Source_contract (β C₀ A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      ∀ B : ℝ, 0 ≤ B → TGradientContract β (I.kappaSeq κ M (m - 1)) T A B →
        Twistie3SourceContract I hΦ m (I.kappaSeq κ M m) T C B) := by
  obtain ⟨K, hK1, hK⟩ := LeftToShow.left_to_show_scales β C₀
  have hK0 : 0 ≤ K := by linarith
  refine ⟨6 * (1 + Real.sqrt K) * A, by positivity, 0, ?_⟩
  intro I hz hx hh _ Φ hΦ κ hκ M hM hperm R hR θ₀ _ _ _ _ m hm hmM θprev T hθprev hT B hB hTG
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  obtain ⟨-, hmono, -, h4, -, -, -⟩ := hK I hz hx hh κ hκ M hM hperm m hm2 hmM
  have hκp : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hmono
  have hTjoint := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  have hμ := sa_mu_le (a_nonneg' I m) hκm hmono hK0 h4
  have hε := epsilon_pos' I (m - 1)
  have hε1 := epsilon_le_one' I (m - 1)
  have hδ := delta_pos' I
  have he : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ epsilon β I.Λ (m - 1) ^ delta β :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have he0 : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) := (Real.rpow_pos_of_pos hε _).le
  have hL2 := saTimeL2_le_of_pointwise
    (F := twistie3Flux I hΦ m (I.kappaSeq κ M m) (T (Nstar β)))
    (V₀ := fun t x => spaceGrad (T (Nstar β) t) x) (V₁ := fun t x => spaceGrad (T (Nstar β) t) x)
    (V₂ := fun t x => spaceGrad (T (Nstar β) t) x)
    (k₀ := 6 * ((I.kappaSeq κ M m + a β I.Λ m * epsilon β I.Λ m ^ 2) *
      epsilon β I.Λ (m - 1) ^ (2 * delta β))) (k₁ := 0) (k₂ := 0)
    (by have := a_nonneg' I m; positivity) le_rfl le_rfl
    (sa_gradT_cont hTjoint) (sa_gradT_cont hTjoint) (sa_gradT_cont hTjoint)
    (fun t ht => (tf_twistie3Flux_slice I hΦ (by omega) _ (T (Nstar β)) t
      (Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le)
      (Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.1.le)).1.continuous)
    (fun t ht x => by
      have h := sa_twistie3Flux_vecNormSq_le I hΦ hm2 hκm
        (Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le) x
      refine h.trans (le_of_eq ?_)
      ring)
  have hs0 := Real.sqrt_nonneg (spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x))
  have hsm := Real.sqrt_nonneg (I.kappaSeq κ M m)
  have harith := sa_twistie3_arith (μ := I.kappaSeq κ M m + a β I.Λ m * epsilon β I.Λ m ^ 2)
    (e := epsilon β I.Λ (m - 1) ^ (2 * delta β)) hμ hs0 he0 hsm hTG
  refine hL2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hfin : 0 ≤ 6 * (1 + Real.sqrt K) * A * Real.sqrt (I.kappaSeq κ M m) * B := by positivity
  calc _ ≤ 6 * (1 + Real.sqrt K) * A * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
        Real.sqrt (I.kappaSeq κ M m) * B := by linarith
    _ ≤ 6 * (1 + Real.sqrt K) * A * epsilon β I.Λ (m - 1) ^ delta β *
        Real.sqrt (I.kappaSeq κ M m) * B := by gcongr
    _ = _ := by ring

/-! ### `normie1` -/

theorem normie1Source_contract (β C₀ A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      ∀ B : ℝ, 0 ≤ B →
        FirstOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A B →
        TGradientContract β (I.kappaSeq κ M (m - 1)) T A B →
        Normie1SourceContract I hΦ m (I.kappaSeq κ M m) T C B) := by
  obtain ⟨K, hK1, hK⟩ := LeftToShow.left_to_show_scales β C₀
  have hK0 : 0 ≤ K := by linarith
  refine ⟨(80 * 2 ^ 16 * A + 40 * A ^ 2) * ((1 + Real.sqrt K) * (2 * Real.pi * K ^ 2)),
    by positivity, 0, ?_⟩
  intro I hz hx hh _ Φ hΦ κ hκ M hM hperm R hR θ₀ _ _ _ _ m hm hmM θprev T hθprev hT B hB hJet hTG
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  obtain ⟨-, hmono, -, h4, -, h6, h7⟩ := hK I hz hx hh κ hκ M hM hperm m hm2 hmM
  have hκp : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hmono
  have hTjoint := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  have hμ := sa_mu_le (a_nonneg' I m) hκm hmono hK0 h4
  have hε := epsilon_pos' I (m - 1)
  have hε1 := epsilon_le_one' I (m - 1)
  have hεm := epsilon_pos' I m
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hγ := Infra.Ingredients.gamma_pos hβ hβ'
  have hρ : 0 < epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) := Real.rpow_pos_of_pos hε _
  have hρe : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ epsilon β I.Λ (m - 1) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hε hε1
      (show (1 : ℝ) ≤ 1 + gamma β / 2 by linarith)
    simpa using h
  have hD : 2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹ ≤
      2 ^ 16 * (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2))⁻¹ :=
    mul_le_mul_of_nonneg_left (inv_anti₀ hρ hρe) (by positivity)
  have hc0 : 0 ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m := by
    have := a_nonneg' I m
    positivity
  have hcρ := sa_chi_ratio hβ hβ' hK1 hε hε1 hεm hc0 h6 h7
  have hL2 := saTimeL2_le_of_pointwise
    (F := normie1Flux I hΦ m (I.kappaSeq κ M m) (T (Nstar β)))
    (V₀ := fun t x => spaceGrad (T (Nstar β) t) x)
    (V₁ := fun t x => spaceGrad (Infra.Section4.iterateSpatialWord [0] (T (Nstar β) t)) x)
    (V₂ := fun t x => spaceGrad (Infra.Section4.iterateSpatialWord [1] (T (Nstar β) t)) x)
    (k₀ := 40 * (2 * ((I.kappaSeq κ M m + a β I.Λ m * epsilon β I.Λ m ^ 2) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m))) *
        (2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹)))
    (k₁ := 10 * (2 * ((I.kappaSeq κ M m + a β I.Λ m * epsilon β I.Λ m ^ 2) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m)))))
    (k₂ := 10 * (2 * ((I.kappaSeq κ M m + a β I.Λ m * epsilon β I.Λ m ^ 2) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m)))))
    (by have := a_nonneg' I m; positivity) (by have := a_nonneg' I m; positivity)
    (by have := a_nonneg' I m; positivity)
    (sa_gradT_cont hTjoint) (sa_hess_cont hTjoint 0) (sa_hess_cont hTjoint 1)
    (fun t ht => (tf_normie1Flux_slice I hΦ (by omega) _ (T (Nstar β)) t
      (Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le)
      (Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.1.le)).1.continuous)
    (fun t ht x =>
      sa_normie1Flux_vecNormSq_le I hΦ hm2 hκm
        (Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le) x)
  refine hL2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hμ0 : 0 ≤ I.kappaSeq κ M m + a β I.Λ m * epsilon β I.Λ m ^ 2 := by
    have := a_nonneg' I m
    positivity
  have harith := sa_normie1_arith (μ := I.kappaSeq κ M m + a β I.Λ m * epsilon β I.Λ m ^ 2)
    (cχ := epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m))
    (D := 2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹)
    (ρ := epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2))
    (sp := Real.sqrt (I.kappaSeq κ M (m - 1))) (sm := Real.sqrt (I.kappaSeq κ M m))
    (e := epsilon β I.Λ (m - 1) ^ delta β) hK1
    (Real.rpow_nonneg hε.le _) hμ0 (mul_nonneg hεm.le hc0) hρ (Real.sqrt_pos.2 hκp)
    (Real.sqrt_nonneg _) hD (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hμ hcρ hTG (hJet 0) (hJet 1)
  refine le_trans (le_of_eq ?_) (harith.trans (le_of_eq ?_))
  · ring
  · ring

/-! ### `normie2` -/

theorem normie2Source_contract (β C₀ CH : ℝ) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      ∀ B : ℝ, 0 ≤ B →
        HmGradientContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T CH B →
        Normie2SourceContract I hΦ m (I.kappaSeq κ M m) T C B) := by
  obtain ⟨K, hK1, hK⟩ := LeftToShow.left_to_show_scales β C₀
  have hK0 : 0 ≤ K := by linarith
  refine ⟨3 * (1 + Real.sqrt K) * CH, by positivity, 0, ?_⟩
  intro I hz hx hh _ Φ hΦ κ hκ M hM hperm R hR θ₀ _ _ _ _ m hm hmM θprev T hθprev hT B hB hHG
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  obtain ⟨-, hmono, -, h4, -, -, -⟩ := hK I hz hx hh κ hκ M hM hperm m hm2 hmM
  have hμ := sa_mu_le (a_nonneg' I m) hκm hmono hK0 h4
  have hε := epsilon_pos' I (m - 1)
  have hε1 := epsilon_le_one' I (m - 1)
  have hδ := delta_pos' I
  have he : epsilon β I.Λ (m - 1) ^ (4 * delta β) ≤ epsilon β I.Λ (m - 1) ^ delta β :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  obtain ⟨Gh, hGhc, hGh⟩ := sa_Hm_grad_extends I hΦ (by omega : 1 ≤ m) hκm hθprev hT
  have hGhc' : ∀ i, ContinuousOn (fun p : ℝ × Vec 2 => (fun (t : ℝ) (x : Vec 2) => Gh (t, x)) p.1
      p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := fun i =>
    (hGhc i).mono (Set.prod_mono Set.Icc_subset_Ici_self le_rfl)
  have hL2 := saTimeL2_le_of_pointwise
    (F := normie2Flux I hΦ m (I.kappaSeq κ M m) (T (Nstar β)))
    (V₀ := fun t x => Gh (t, x)) (V₁ := fun t x => Gh (t, x)) (V₂ := fun t x => Gh (t, x))
    (k₀ := 3 * (I.kappaSeq κ M m + a β I.Λ m * epsilon β I.Λ m ^ 2)) (k₁ := 0) (k₂ := 0)
    (by have := a_nonneg' I m; positivity) le_rfl le_rfl hGhc' hGhc' hGhc'
    (fun t ht => (tf_normie2Flux_slice I hΦ m _ (T (Nstar β)) t
      (Hm_slice_contDiff_pos I hΦ (by omega) hκm hθprev hT ht.1)
      (Hm_periodic_pos I hΦ (by omega) hκm hθprev hT ht.1)).1.continuous)
    (fun t ht x => by
      have h := sa_normie2Flux_vecNormSq_le I hΦ hm2 hκm (T (Nstar β)) t x
      have hg : spaceGrad (fun z => I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t z) x =
          Gh (t, x) := hGh (t, x) ⟨ht.1, trivial⟩
      rw [hg] at h
      refine h.trans (le_of_eq ?_)
      ring)
  have heq : spaceTimeGradNormSq (fun t x => Gh (t, x)) =
      spaceTimeGradNormSq (fun s x => spaceGrad (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)
          := by
    unfold spaceTimeGradNormSq
    refine MeasureTheory.setIntegral_congr_fun measurableSet_timeCube fun p hp => ?_
    have hp' : p ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) := ⟨hp.1.1, trivial⟩
    simp only
    rw [hGh p hp']
  refine hL2.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [heq]
  have hs0 := Real.sqrt_nonneg
    (spaceTimeGradNormSq (fun s x => spaceGrad (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x))
  have hsm := Real.sqrt_nonneg (I.kappaSeq κ M m)
  have harith := sa_normie2_arith (μ := I.kappaSeq κ M m + a β I.Λ m * epsilon β I.Λ m ^ 2)
    (CH := CH) (E := epsilon β I.Λ (m - 1) ^ (4 * delta β)) hμ hs0 hsm hHG
  have hfin : 0 ≤ 3 * (1 + Real.sqrt K) * Real.sqrt (I.kappaSeq κ M m) * (CH * B) := by positivity
  calc _ ≤ 3 * (1 + Real.sqrt K) * Real.sqrt (I.kappaSeq κ M m) *
        (CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * B) := by linarith
    _ ≤ 3 * (1 + Real.sqrt K) * Real.sqrt (I.kappaSeq κ M m) *
        (CH * epsilon β I.Λ (m - 1) ^ delta β * B) := by gcongr
    _ = _ := by ring

end AVenhance.Infra.Section5.Contracts
end
