/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertPrincipalValueClosure
public import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveFullOperatorEndpoint
public import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryPositiveOperatorReduction

/-!
# Positive endpoints for genuine quadratic principal values

The ordinary Hilbert maximal weak estimate is the sole classical input for
the full-modulation result. The lacunary result additionally uses precisely
the uniform individual frozen-block weak estimate. Neither hypothesis is an
estimate for the assembled quadratic operator.

All level-set measures below are outer measures. In particular, passing to
the supremum over every real modulation requires no assumed measurability.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace QuadraticCarleson
namespace PositivePrincipalValueEndpoints

open HilbertPrincipalValueClosure PositiveFullOperatorEndpoint
open PositiveFullOscillatoryEndpoint OscillatoryReduction
open LacunaryOscillatoryScaling LacunaryPositiveOperatorReduction
open KaltonPaperApplication


/-- The L0-only Hilbert hypothesis gives the earlier real-valued weak-bound
interface on each actual L0 input, without extending its domain. -/
theorem extendedWeakL1Bound_zeroHilbert_of_uniform
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH) (f : L0Infinity) :
    HasExtendedWeakL1Bound volume (CH.toReal * (∫⁻ x, ‖f x‖ₑ).toReal)
      (quadraticHilbertMaximalTruncation 0 f) := by
  refine ⟨mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, fun a ha ↦ ?_⟩
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hH.1.ne,
    ENNReal.ofReal_toReal f.integrable.hasFiniteIntegral.ne]
  exact hH.2 f (ENNReal.ofReal a)

/-- Compatibility with the previously isolated, stronger all-integrable-input
form of the ordinary Hilbert maximal theorem. -/
theorem uniformHilbertMaximalWeakBound_of_all_integrable
    {CH : ℝ} (hH : HasUniformZeroHilbertMaximalWeakBound CH) :
    HasUniformHilbertMaximalWeakBound (ENNReal.ofReal CH) := by
  apply hasUniformHilbertMaximalWeakBound_of_real ENNReal.ofReal_lt_top
  intro f a ha
  have h := (hH.2 f f.measurable_toFun f.integrable).2 a ha
  simpa only [ENNReal.ofReal_mul hH.1,
    ENNReal.ofReal_toReal f.integrable.hasFiniteIntegral.ne] using h

/-- The full principal-value endpoint constant combining oscillatory, Hilbert, and error bounds. -/
noncomputable def fullPrincipalValueEndpointConstant (CH : ℝ≥0∞) : ℝ≥0∞ :=
  4 * fullOscillatoryEndpointConstant + 8 * CH + 16 * maximalErrorConstant

theorem fullPrincipalValueEndpointConstant_lt_top
    {CH : ℝ≥0∞} (hCH : CH < ∞) : fullPrincipalValueEndpointConstant CH < ∞ := by
  unfold fullPrincipalValueEndpointConstant
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by finiteness) fullOscillatoryEndpointConstant_lt_top,
      ENNReal.mul_lt_top (by finiteness) hCH⟩,
    ENNReal.mul_lt_top (by finiteness) maximalErrorConstant_lt_top⟩

/-- The exact arbitrary-threshold full-modulation source modular, now using
only the ordinary Hilbert maximal estimate on the paper's own test domain. -/
theorem quadraticCarlesonL0_levelSet_le_full_modular
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < quadraticCarlesonL0 f x} ≤
      fullPrincipalValueEndpointConstant CH * ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) := by
  let g := normalizedL0Input α f
  have h := quadraticCarlesonL0_levelSet_one_le_orlicz_of_hilbertWeak
    g ENNReal.toReal_nonneg (extendedWeakL1Bound_zeroHilbert_of_uniform hH g)
  rw [← quadraticCarlesonL0_levelSet_eq_normalized hα f] at h
  have hnorm (x : ℝ) : ‖g x‖ = ‖f x‖ / α := norm_normalizedL0Input hα f x
  simpa only [hnorm, ENNReal.ofReal_toReal hH.1.ne,
    ofReal_maximalErrorConstantReal, fullPrincipalValueEndpointConstant] using h

/-- The ordinary Hilbert remainder at threshold `α/6` is absorbed into the
paper's lacunary modular using its elementary domination of `L¹`. -/
theorem zeroHilbert_levelSet_sixth_le_lacunary_modular
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal (α / 6) < quadraticHilbertMaximalTruncation 0 f x} ≤
      (6 * CH) * ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  have h := hH.2 f (ENNReal.ofReal (α / 6))
  have hc : ENNReal.ofReal (6 / α) * ENNReal.ofReal (α / 6) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 6 / α)]
    have heq : (6 / α) * (α / 6) = 1 := by field_simp
    rw [heq, ENNReal.ofReal_one]
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal (6 / α))) h
  rw [← mul_assoc, hc, one_mul] at hh
  have heq : ENNReal.ofReal (6 / α) * (CH * ∫⁻ x, ‖f x‖ₑ) =
      (6 * CH) * ∫⁻ x, ENNReal.ofReal (‖f x‖ / α) := by
    rw [lintegral_scaled_norm_eq f hα, ENNReal.ofReal_div_of_pos hα,
      ENNReal.ofReal_ofNat, div_eq_mul_inv]
    ring
  rw [heq] at hh
  exact hh.trans (mul_le_mul' le_rfl (lintegral_scaled_norm_le_lacunaryOrlicz f hα))

/-- The lacunary principal-value endpoint constant combining Hilbert and remainder bounds. -/
noncomputable def lacunaryPrincipalValueEndpointConstant
    (CH : ℝ≥0∞) (CB : ℝ) : ℝ≥0∞ :=
  6 * CH + lacunaryRemainderEndpointConstant CB

theorem lacunaryPrincipalValueEndpointConstant_lt_top
    {CH : ℝ≥0∞} (hCH : CH < ∞) (CB : ℝ) :
    lacunaryPrincipalValueEndpointConstant CH CB < ∞ := by
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by finiteness) hCH, lacunaryRemainderEndpointConstant_lt_top CB⟩

/-- The exact lacunary source modular, conditional only on the two already
isolated individual analytic estimates. The block hypothesis is uniform in
the input, so no unjustified scaling of stopping atoms is used. -/
theorem lacunaryQuadraticCarlesonL0_levelSet_le_lacunary_modular
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH)
    {CB : ℝ} (hB : HasUniformL0LogSquaredFrozenBlockWeakBounds CB)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < lacunaryQuadraticCarlesonL0 f x} ≤
      lacunaryPrincipalValueEndpointConstant CH CB * ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  apply (lacunaryQuadraticCarlesonL0_levelSet_le_hilbert_remainder_add_scaled_orlicz
    hB f hα).trans
  exact (add_le_add (zeroHilbert_levelSet_sixth_le_lacunary_modular hH f hα)
    le_rfl).trans_eq (by rw [← add_mul]; rfl)

/-- An everywhere-defined complex representative: it is the unique genuine
PV wherever that limit exists, and zero elsewhere. Its fallback is confined
to one null set under the ordinary Hilbert maximal hypothesis. -/
noncomputable def principalValueRepresentative (lam : ℝ) (f : L0Infinity) (x : ℝ) : ℂ := by
  classical
  exact if h : ∃ z : ℂ, HasQuadraticPrincipalValue lam f x z then h.choose else 0

theorem principalValueRepresentative_eq {lam : ℝ} {f : L0Infinity} {x : ℝ} {z : ℂ}
    (hz : HasQuadraticPrincipalValue lam f x z) :
    principalValueRepresentative lam f x = z := by
  have hex : ∃ w : ℂ, HasQuadraticPrincipalValue lam f x w := ⟨z, hz⟩
  rw [principalValueRepresentative, dite_eq_left hex]
  exact tendsto_nhds_unique hex.choose_spec hz

theorem ae_forall_hasPrincipalValue_representative
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH) (f : L0Infinity) :
    ∀ᵐ x, ∀ lam : ℝ,
      HasQuadraticPrincipalValue lam f x (principalValueRepresentative lam f x) := by
  filter_upwards [ae_forall_real_exists_quadraticPrincipalValue hH f] with x hx
  intro lam
  obtain ⟨z, hz⟩ := hx lam
  rwa [principalValueRepresentative_eq hz]

/-- The paper's supremum of the norms of genuine principal values, using
the harmless null-set convention of `principalValueRepresentative`. -/
noncomputable def fullPrincipalValueMaximal (f : L0Infinity) (x : ℝ) : ℝ≥0∞ :=
  ⨆ lam : ℝ, ENNReal.ofReal ‖principalValueRepresentative lam f x‖

/-- The supremum of principal-value representatives over dyadic modulations. -/
noncomputable def lacunaryPrincipalValueMaximal (f : L0Infinity) (x : ℝ) : ℝ≥0∞ :=
  ⨆ m : ℤ, ENNReal.ofReal ‖principalValueRepresentative (dyadicModulation m) f x‖

/-- The equality holds on one common full-measure set before the uncountable
real supremum is taken; no uncountable intersection of null sets is used. -/
theorem fullPrincipalValueMaximal_ae_eq
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH) (f : L0Infinity) :
    fullPrincipalValueMaximal f =ᵐ[volume] quadraticCarlesonL0 f := by
  filter_upwards [ae_forall_hasPrincipalValue_representative hH f] with x hx
  unfold fullPrincipalValueMaximal quadraticCarlesonL0
  exact iSup_congr fun lam ↦
    (quadraticHilbertL0Limsup_eq_of_principalValue lam f x _ (hx lam)).symm

theorem lacunaryPrincipalValueMaximal_ae_eq
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH) (f : L0Infinity) :
    lacunaryPrincipalValueMaximal f =ᵐ[volume] lacunaryQuadraticCarlesonL0 f := by
  filter_upwards [ae_forall_hasPrincipalValue_representative hH f] with x hx
  unfold lacunaryPrincipalValueMaximal lacunaryQuadraticCarlesonL0
  exact iSup_congr fun m ↦ (quadraticHilbertL0Limsup_eq_of_principalValue
    (dyadicModulation m) f x _ (hx (dyadicModulation m))).symm

/-- Full-modulation `L log₁ L` endpoint for genuine PVs, at every positive
threshold. Only the ordinary Hilbert maximal weak estimate is conditional. -/
theorem fullPrincipalValueMaximal_levelSet_le
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < fullPrincipalValueMaximal f x} ≤
      fullPrincipalValueEndpointConstant CH * ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) := by
  have hset : {x | ENNReal.ofReal α < fullPrincipalValueMaximal f x} =ᵐ[volume]
      {x | ENNReal.ofReal α < quadraticCarlesonL0 f x} := by
    filter_upwards [fullPrincipalValueMaximal_ae_eq hH f] with x hx
    rw [hx]
  rw [measure_congr hset]
  exact quadraticCarlesonL0_levelSet_le_full_modular hH f hα

/-- Lacunary `L (log₂ L)² log₄ L` endpoint for genuine PVs, conditional on
the ordinary Hilbert and individual frozen-block weak estimates only. -/
theorem lacunaryPrincipalValueMaximal_levelSet_le
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH)
    {CB : ℝ} (hB : HasUniformL0LogSquaredFrozenBlockWeakBounds CB)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
      lacunaryPrincipalValueEndpointConstant CH CB * ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  have hset : {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} =ᵐ[volume]
      {x | ENNReal.ofReal α < lacunaryQuadraticCarlesonL0 f x} := by
    filter_upwards [lacunaryPrincipalValueMaximal_ae_eq hH f] with x hx
    rw [hx]
  rw [measure_congr hset]
  exact lacunaryQuadraticCarlesonL0_levelSet_le_lacunary_modular hH hB f hα

/-- Paper-facing full theorem: one finite constant works for every input
and threshold, and all modulations are actual PVs on one common conull set. -/
theorem full_principalValue_endpoint
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ lam : ℝ,
        HasQuadraticPrincipalValue lam f x (principalValueRepresentative lam f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < fullPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) := by
  refine ⟨fullPrincipalValueEndpointConstant CH,
    fullPrincipalValueEndpointConstant_lt_top hH.1, fun f ↦ ?_⟩
  exact ⟨ae_forall_hasPrincipalValue_representative hH f,
    fun _ hα ↦ fullPrincipalValueMaximal_levelSet_le hH f hα⟩

/-- Paper-facing lacunary theorem. The only additional input beyond the
ordinary Hilbert theorem is the exact uniform individual-block estimate. -/
theorem lacunary_principalValue_endpoint
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH)
    {CB : ℝ} (hB : HasUniformL0LogSquaredFrozenBlockWeakBounds CB) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  refine ⟨lacunaryPrincipalValueEndpointConstant CH CB,
    lacunaryPrincipalValueEndpointConstant_lt_top hH.1 CB, fun f ↦ ⟨?_, ?_⟩⟩
  · filter_upwards [ae_forall_hasPrincipalValue_representative hH f] with x hx
    exact fun m ↦ hx (dyadicModulation m)
  · exact fun _ hα ↦ lacunaryPrincipalValueMaximal_levelSet_le hH hB f hα


end PositivePrincipalValueEndpoints
end QuadraticCarleson
