/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.CanonicalScaleAtoms
public import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleRangeSummation

/-! # Actual scale-atom masses in the lacunary block-packing notation -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace CanonicalScaleAtoms

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms PositiveHighHeightEstimate
open LacunaryMiddleRangeSummation

theorem enorm_stoppingScaleLevelBadPart_eq_tsum_atoms
    (A : ℕ → ℝ) (f : ℝ → ℂ) (j : ℤ) (k : ℕ) (x : ℝ) :
    ‖stoppingScaleLevelBadPart A f j k x‖ₑ =
      ∑' c : stoppingCell f,
        (dyadicAtomScaleClass stoppingLength j).indicator
          (fun c ↦ ‖levelAtom A f k (stoppingCenter c) (stoppingLength c) x‖ₑ) c := by
  classical
  by_cases hx : x ∈ stoppingBadUnion f
  · obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    rw [stoppingScaleLevelBadPart_eq_atom_of_mem A c hc, tsum_eq_single c]
    · exact enorm_indicator_eq_indicator_enorm _ _
    · intro d hdc
      have hz := levelAtom_eq_zero_of_other_mem (A := A) (f := f) (k := k)
        centeredStoppingIntervals_pairwiseDisjoint hdc
        (by simpa only [centeredInterval_eq_stoppingInterval] using hc)
      by_cases hd : d ∈ dyadicAtomScaleClass stoppingLength j <;> simp [hd, hz]
  · have hz (c : stoppingCell f) :
        levelAtom A f k (stoppingCenter c) (stoppingLength c) x = 0 := by
      apply levelAtom_eq_zero_of_not_mem
      rw [centeredInterval_eq_stoppingInterval]
      exact fun hc ↦ hx (mem_iUnion.mpr ⟨c, hc⟩)
    simp [stoppingScaleLevelBadPart_eq_zero_of_notMem A hx, hz]

/-- The coefficient used in the arithmetic block-packing lemma is exactly
the L¹ mass of the genuine canonical `b_{j,k}`. -/
theorem lintegral_enorm_stoppingScaleLevelBadPart_eq_atomScaleMass
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (j : ℤ) (k : ℕ) :
    (∫⁻ x, ‖stoppingScaleLevelBadPart A f j k x‖ₑ) =
      atomScaleMass (stoppingLength (f := f))
        (fun c ↦ ∫⁻ x, ‖levelAtom A f k (stoppingCenter c) (stoppingLength c) x‖ₑ) j := by
  have hm (c : stoppingCell f) : Measurable (fun x ↦
      (dyadicAtomScaleClass stoppingLength j).indicator
        (fun c ↦ ‖levelAtom A f k (stoppingCenter c) (stoppingLength c) x‖ₑ) c) := by
    by_cases hc : c ∈ dyadicAtomScaleClass stoppingLength j
    · simpa only [indicator_of_mem hc] using
        (measurable_levelAtom hf k (stoppingCenter c) (stoppingLength c)).enorm
    · simp only [indicator_of_notMem hc]
      exact measurable_const
  simp_rw [enorm_stoppingScaleLevelBadPart_eq_tsum_atoms]
  rw [lintegral_tsum (fun c ↦ (hm c).aemeasurable)]
  unfold atomScaleMass
  apply tsum_congr
  intro c
  by_cases hc : c ∈ dyadicAtomScaleClass stoppingLength j <;> simp [hc]

theorem lintegral_enorm_stoppingScaleLevelBadPart_eq_atomScaleIntegralMass
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (j : ℤ) {k : ℕ} (hAk : 0 ≤ A k) :
    (∫⁻ x, ‖stoppingScaleLevelBadPart A f j k x‖ₑ) =
      atomScaleMass (stoppingLength (f := f))
        (fun c ↦ ENNReal.ofReal (∫ x, ‖levelAtom A f k (stoppingCenter c) (stoppingLength c)
          x‖)) j := by
  rw [lintegral_enorm_stoppingScaleLevelBadPart_eq_atomScaleMass hf]
  congr 1
  funext c
  symm
  simpa only [ofReal_norm] using ofReal_integral_eq_lintegral_ofReal
    (integrable_levelAtom hf hAk (stoppingCenter c) (stoppingLength c)).norm
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)

/-- The existing disjoint-residue block packing now applies directly to
the actual canonical scale-sliced atoms, with no supplied atom family. -/
theorem tsum_sparseBlock_stoppingScaleLevelBadPart_mass_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) {k : ℕ} (hAk : 0 ≤ A k)
    (B c : ℕ) (hB : 0 < B) (hc : 2 * c ≤ 5 * B) (ρ : ℤ) :
    (∑' τ : ℤ, sparseBlockMass B c ρ
      (fun j ↦ ∫⁻ x, ‖stoppingScaleLevelBadPart A f j k x‖ₑ) τ) ≤
      2 * PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k := by
  simp_rw [lintegral_enorm_stoppingScaleLevelBadPart_eq_atomScaleIntegralMass hf _ hAk]
  apply (tsum_sparseBlock_atomScaleMass_le B c hB hc ρ
    (stoppingLength (f := f)) stoppingLength_pos _).trans
  exact tsum_atomL1Mass_le_two_mul_global_level_mass hf hAk
    _ _ centeredStoppingIntervals_pairwiseDisjoint

end CanonicalScaleAtoms
end QuadraticCarleson
