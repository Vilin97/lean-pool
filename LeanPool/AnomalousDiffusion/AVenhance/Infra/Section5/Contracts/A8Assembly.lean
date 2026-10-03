/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A7Assembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.IndyStepDownV2

/-! # Step-down estimate assembly from the individual contract producers

The producer hypotheses are the three part-I contracts and seven relative contracts.
Relative producers may use exactly the gate. Independent constants and thresholds
are combined before the ingredient instance is introduced.
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section5 Integration

/-- The independent part-I and relative contract producers. -/
structure A8ContractProducers (β C₀ : ℝ) : Prop where
  initial : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m θm _θprev T => InitialLayerContract I hΦ m (I.kappaSeq κ M m) θm T C
        (Real.sqrt (l2NormSq θ₀)))
  ansatz : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => SectionFourAnsatzContract I hΦ m (I.kappaSeq κ M m) θ₀ T C)
  iterate : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ _κ _M _R θ₀ m _θm θprev T => SectionFourIterateContract I m θ₀ θprev T C)
  gradient : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma
        β / 2 - delta β) ≤ R →
      TGradientContract β (I.kappaSeq κ M (m - 1)) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  material : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β
        / 2 - delta β) ≤ R →
      TMaterialContract I Φ m (I.kappaSeq κ M (m - 1)) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  jets : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma
        β / 2 - delta β) ≤ R →
      TPositiveJetsContract I m T C (Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt
          (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  relative_initial : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m θm θprev T => (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β
        / 2 - delta β) ≤ R →
      InitialLayerContract I hΦ m (I.kappaSeq κ M m) θm T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  terms : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β
        / 2 - delta β) ≤ R →
      RelativeTermsContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C (Real.sqrt
          (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev
          s) x))))
  leading : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β
        / 2 - delta β) ≤ R →
      LeadingErrorContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  temperature : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma
        β / 2 - delta β) ≤ R →
      TemperatureErrorContract I m (I.kappaSeq κ M (m - 1)) θprev T C (Real.sqrt (I.kappaSeq κ M
          (m - 1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))

/-- Part I from its three independent producers. -/
theorem partI_family_of_contracts (β C₀ : ℝ) (h : A8ContractProducers β C₀) :
    PartIFamilyContract β C₀ := by
  obtain ⟨Ci, Li, hi⟩ := h.initial
  obtain ⟨Ca, La, ha⟩ := h.ansatz
  obtain ⟨Ct, Lt, ht⟩ := h.iterate
  obtain ⟨L, _, hL⟩ := exists_nonneg_upper_bound [Li, La, Lt]
  refine ⟨L, Ci, Ca, Ct, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM
    θm θprev T hθm hθprev hT
  exact {
    hInitial := hi I hz hx hh ((hL Li (by simp)).trans hΛ) Φ hΦ κ hκ M hM hperm R hR
      θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT
    hSectionFourAnsatz := ha I hz hx hh ((hL La (by simp)).trans hΛ) Φ hΦ κ hκ M hM
      hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
    hSectionFourIterate := ht I hz hx hh ((hL Lt (by simp)).trans hΛ) Φ hΦ κ hκ M hM
      hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT
  }

/-- Assemble all step-down estimate inputs from the individual contracts; no step-down estimate
    conclusion is assumed. -/
theorem indy_inputs_of_contracts (β C₀ : ℝ) (h7 : A7ContractProducers β C₀)
    (h8 : A8ContractProducers β C₀) : Nonempty (IndyStepDownV2Inputs β C₀) := by
  obtain ⟨c_gradient, l_gradient, h_gradient⟩ := h8.gradient
  obtain ⟨c_material, l_material, h_material⟩ := h8.material
  obtain ⟨c_jets, l_jets, h_jets⟩ := h8.jets
  obtain ⟨c_relative_initial, l_relative_initial, h_relative_initial⟩ := h8.relative_initial
  obtain ⟨c_terms, l_terms, h_terms⟩ := h8.terms
  obtain ⟨c_leading, l_leading, h_leading⟩ := h8.leading
  obtain ⟨c_temperature, l_temperature, h_temperature⟩ := h8.temperature
  obtain ⟨L, _, hL⟩ := exists_nonneg_upper_bound [l_gradient, l_material, l_jets,
      l_relative_initial, l_terms, l_leading, l_temperature]
  obtain ⟨A, hA0, hA⟩ := exists_nonneg_upper_bound [2 ^ (14 : ℕ), c_gradient, c_material, |c_jets|]
  obtain ⟨C, hC0, hC⟩ := exists_nonneg_upper_bound [c_relative_initial, c_terms, c_leading,
      c_temperature]
  refine ⟨{
    A := A, Ci := C, Cr := C, Ca := C, Ct := C
    hA := hA _ (by simp), hCi := hC0, hCr := hC0, hCa := hC0, hCt := hC0
    bigbound := bigbound_family_of_contracts β C₀ h7
    partI := partI_family_of_contracts β C₀ h8
    CΛ := L
    relative := ?_
  }⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM
    θm θprev T hθm hθprev hT hgate hlater
  have he : 0 ≤ epsilon β I.Λ (m - 1) :=
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have hτ : 0 ≤ (tauP β I.Λ m)⁻¹ := inv_nonneg.mpr
    (Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have hrho : 0 ≤ epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) := Real.rpow_nonneg he _
  have hS : 0 ≤ Real.sqrt (I.kappaSeq κ M (m - 1)) *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have p_gradient := h_gradient I hz hx hh ((hL l_gradient (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T
    hθm hθprev hT hgate hlater
  have p_material := h_material I hz hx hh ((hL l_material (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T
    hθm hθprev hT hgate hlater
  have p_jets := h_jets I hz hx hh ((hL l_jets (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T
    hθm hθprev hT hgate hlater
  have p_relative_initial := h_relative_initial I hz hx hh ((hL l_relative_initial (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T
    hθm hθprev hT hgate hlater
  have p_terms := h_terms I hz hx hh ((hL l_terms (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T
    hθm hθprev hT hgate hlater
  have p_leading := h_leading I hz hx hh ((hL l_leading (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T
    hθm hθprev hT hgate hlater
  have p_temperature := h_temperature I hz hx hh ((hL l_temperature (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T
    hθm hθprev hT hgate hlater
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact p_gradient.trans (mul_le_mul_of_nonneg_right (hA c_gradient (by simp)) hS)
  · apply p_material.trans
    gcongr
    exact hA c_material (by simp)
  · intro n i hn t ht
    apply (p_jets n i hn t ht).trans
    apply (le_abs_self _).trans
    simp only [abs_mul, abs_pow, abs_div, abs_of_nonneg hS,
      abs_of_nonneg hrho, abs_of_nonneg (Nat.cast_nonneg n.factorial : (0 : ℝ) ≤ n.factorial)]
    have hjA := hA |c_jets| (by simp)
    gcongr
  · filter_upwards [p_relative_initial] with s hs
    apply hs.trans
    gcongr
    exact hC c_relative_initial (by simp)
  · intro i hi
    apply (p_terms i hi).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    exact hC c_terms (by simp)
  · apply p_leading.trans
    gcongr
    exact hC c_leading (by simp)
  · apply p_temperature.trans
    gcongr
    exact hC c_temperature (by simp)

/-- The literal step-down estimate statement from only the individual big-bound estimate and
    step-down estimate contract producers. -/
theorem indystepdown_of_contracts (β C₀ : ℝ) (h7 : A7ContractProducers β C₀)
    (h8 : A8ContractProducers β C₀) : IndyStepDownStatement β C₀ := by
  obtain ⟨h⟩ := indy_inputs_of_contracts β C₀ h7 h8
  exact Integration.indystepdown_v2_of_inputs β C₀ h

end AVenhance.Infra.Section5.Contracts
