/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.NegativePrincipalValueEndpoints
public import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryEndpointDirectResolved
public import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteModulationDirectBlockResolved
public import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveFullMaximalMeasurability
public import LeanPool.QuadraticCarleson.QuadraticCarleson.NegativeWeakOneOneCorollary

/-!
# Paper-facing headline statements

Review entry point for arXiv:2609.04101v1. These explicit theorem types retain
the source test domain, strict level sets, modulars, and quantifier order.
Both negative and positive endpoints use the same genuine principal-value
operators. The definitions and proofs live in the individually imported files.

This review-facing statement map identifies the claims formalized here. It does
not assert that every auxiliary result cited by the article is formalized in
this repository.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace QuadraticCarleson.PaperTheorems

open PositivePrincipalValueEndpoints


/-- Theorem `t:loglogfail`: lacunary failure below `t log₂ t`. -/
theorem lacunary_sub_log2_modular_failure
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasFunctionPhiModularEstimate Phi lacunaryPrincipalValueMaximal :=
  NegativePrincipalValueEndpoints.lacunary_not_hasPhiModularEstimate Phi hPhi

/-- Theorem `t:loglogfail`, full-modulation consequence. -/
theorem full_sub_log2_modular_failure
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasFunctionPhiModularEstimate Phi fullPrincipalValueMaximal :=
  NegativePrincipalValueEndpoints.full_not_hasPhiModularEstimate Phi hPhi

/-- Theorem `t:loglogfail`: the printed unit-height witness for `0 < κ < 1`. -/
theorem lacunary_counterexample_at_unit_height
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    {kappa : ℝ} (hkappa : 0 < kappa ∧ kappa < 1) :
    ∃ f : L0Infinity,
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖))) <
        ENNReal.ofReal kappa * volume {x | 1 < lacunaryPrincipalValueMaximal f x} :=
  NegativePrincipalValueEndpoints.lacunary_exists_paper_modular_witness Phi hPhi hkappa

/-- The same printed witness range for the full real-modulation operator. -/
theorem full_counterexample_at_unit_height
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi)
    {kappa : ℝ} (hkappa : 0 < kappa ∧ kappa < 1) :
    ∃ f : L0Infinity,
      (∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖))) <
        ENNReal.ofReal kappa * volume {x | 1 < fullPrincipalValueMaximal f x} :=
  NegativePrincipalValueEndpoints.full_exists_paper_modular_witness Phi hPhi hkappa

/-- Theorem `t:LlogL`, first bound: full-modulation `L log₁ L`, with one
constant for all inputs and all positive thresholds. -/
theorem full_LlogL_endpoint :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ lam : ℝ,
        HasQuadraticPrincipalValue lam f x (principalValueRepresentative lam f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < fullPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) :=
  HilbertMaximalWeakResolved.full_principalValue_endpoint

/-- Theorem `t:LlogL`, second bound: lacunary `L (log₂ L)² log₄ L`, with
one constant for all inputs and all positive thresholds. -/
theorem lacunary_log2_squared_log4_endpoint :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) :=
  LacunaryEndpointDirectResolved.lacunary_principalValue_endpoint

/-- Introduction's weak `(1,1)` failure, for the same lacunary PV operator. -/
theorem lacunary_not_weakOneOne :
    ¬∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (α : ℝ), 0 < α →
      ENNReal.ofReal α * volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
        ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ := by
  intro hweak
  exact lacunary_sub_log2_modular_failure NegativeWeakOneOneCorollary.identityYoungFunction
    NegativeWeakOneOneCorollary.identityYoungFunction_growsSlowerThanEndpoint
    (NegativeWeakOneOneCorollary.hasFunctionPhiModularEstimate_identity_of_weakOneOne hweak)

/-- Introduction's weak `(1,1)` failure, for the same full PV operator. -/
theorem full_not_weakOneOne :
    ¬∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (α : ℝ), 0 < α →
      ENNReal.ofReal α * volume {x | ENNReal.ofReal α < fullPrincipalValueMaximal f x} ≤
        ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ := by
  intro hweak
  exact full_sub_log2_modular_failure NegativeWeakOneOneCorollary.identityYoungFunction
    NegativeWeakOneOneCorollary.identityYoungFunction_growsSlowerThanEndpoint
    (NegativeWeakOneOneCorollary.hasFunctionPhiModularEstimate_identity_of_weakOneOne hweak)

/-- Both actual headline level-set operators are a.e.-measurable. -/
theorem principalValueMaxima_aemeasurable (f : L0Infinity) :
    AEMeasurable (fullPrincipalValueMaximal f) volume ∧
      AEMeasurable (lacunaryPrincipalValueMaximal f) volume :=
  ⟨PositiveFullMaximalMeasurability.aemeasurable_fullPrincipalValueMaximal f,
    PositiveFullMaximalMeasurability.aemeasurable_lacunaryPrincipalValueMaximal f⟩

/-- Corollary `c:finitemodulationsweak11`: arbitrary signed nonzero finite
modulations, uniformly over `B`. This does not put the supremum over `B`
inside the operator. -/
theorem finite_modulation_blocks_weakOneOne
    {N : ℕ} (B : ℕ) (lam : Fin N → ℝ) (hlam : ∀ i, lam i ≠ 0)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    ENNReal.ofReal α * volume
        {x | ENNReal.ofReal α <
          FiniteModulationDirectBlockResolved.finitePaperBlockMaxEnorm B lam hlam f x} ≤
      ENNReal.ofReal
          (FiniteModulationDirectBlockResolved.finiteBlockWeakConstant * paperLog 1 N ^ 2) *
        ∫⁻ x, ‖f x‖ₑ :=
  FiniteModulationDirectBlockResolved.finiteModulationBlock_weak_bound B lam hlam f hα


end QuadraticCarleson.PaperTheorems
