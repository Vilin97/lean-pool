/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundStoppingIntervals
import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundLevelRecombination
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightEstimate

/-! # Exact canonical stopping bad-part recombination -/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveStoppingBadEstimate

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms CalderonZygmundLevelRecombination
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate

noncomputable def stoppingBadPart (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x - stoppingGoodPart f x

noncomputable def stoppingLevelBadPart (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  disjointLevelAtomSum fullAmplitude f k
    (stoppingCenter (f := f)) (stoppingLength (f := f))

theorem stoppingLevelBadPart_eq_atom_of_mem {f : ℝ → ℂ}
    (c : stoppingCell f) {x : ℝ} (hx : x ∈ c.1.interval (rootLength f)) (k : ℕ) :
    stoppingLevelBadPart f k x =
      levelAtom fullAmplitude f k (stoppingCenter c) (stoppingLength c) x := by
  classical
  unfold stoppingLevelBadPart disjointLevelAtomSum
  apply tsum_eq_single c
  intro d hdc
  exact levelAtom_eq_zero_of_other_mem centeredStoppingIntervals_pairwiseDisjoint hdc
    (by simpa only [centeredInterval_eq_stoppingInterval] using hx)

theorem stoppingLevelBadPart_eq_zero_of_notMem {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ stoppingBadUnion f) (k : ℕ) : stoppingLevelBadPart f k x = 0 := by
  unfold stoppingLevelBadPart disjointLevelAtomSum
  have hz (c : stoppingCell f) :
      levelAtom fullAmplitude f k (stoppingCenter c) (stoppingLength c) x = 0 := by
    apply levelAtom_eq_zero_of_not_mem
    rw [centeredInterval_eq_stoppingInterval]
    exact fun hc ↦ hx (mem_iUnion.mpr ⟨c, hc⟩)
  simp only [hz, tsum_zero]

theorem hasSum_stoppingLevelBadPart {f : ℝ → ℂ} (hf : Measurable f)
    (hfi : Integrable f) (x : ℝ) :
    HasSum (fun k ↦ stoppingLevelBadPart f k x) (stoppingBadPart f x) := by
  by_cases hx : x ∈ stoppingBadUnion f
  · obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    simp_rw [stoppingLevelBadPart_eq_atom_of_mem c hc]
    have hs := hasSum_levelAtom_apply (fullAmplitude_pos 0).le strictMono_fullAmplitude
      fullAmplitude_cofinal hf (stoppingCenter c) (stoppingLength c) hfi.integrableOn x
    convert hs using 1
    unfold stoppingBadPart centeredAtom
    rw [centeredInterval_eq_stoppingInterval, indicator_of_mem hc,
      stoppingGoodPart_eq_average_of_mem c hc]
    rfl
  · simp only [stoppingLevelBadPart_eq_zero_of_notMem hx]
    rw [stoppingBadPart, stoppingGoodPart_eq_of_notMem hx, sub_self]
    exact hasSum_zero

theorem tsum_stoppingLevelBadPart {f : ℝ → ℂ} (hf : Measurable f)
    (hfi : Integrable f) (x : ℝ) :
    (∑' k, stoppingLevelBadPart f k x) = stoppingBadPart f x :=
  (hasSum_stoppingLevelBadPart hf hfi x).tsum_eq

theorem measurable_stoppingLevelBadPart {f : ℝ → ℂ} (hf : Measurable f) (k : ℕ) :
    Measurable (stoppingLevelBadPart f k) :=
  measurable_disjointLevelAtomSum hf k _ _

theorem measurable_stoppingBadPart {f : ℝ → ℂ} (hf : Measurable f)
    (hfi : Integrable f) : Measurable (stoppingBadPart f) := by
  have heq : stoppingBadPart f = fun x ↦ ∑' k, stoppingLevelBadPart f k x :=
    funext (fun x ↦ (tsum_stoppingLevelBadPart hf hfi x).symm)
  rw [heq]
  exact Measurable.tsum (measurable_stoppingLevelBadPart hf)

theorem lintegral_enorm_stoppingLevelBadPart_le {f : ℝ → ℂ}
    (hf : Measurable f) (k : ℕ) :
    (∫⁻ x, ‖stoppingLevelBadPart f k x‖ₑ) ≤
      2 * magnitudeLevelL1Mass volume fullAmplitude f k := by
  have hp (x : ℝ) := map_disjointLevelAtomSum fullAmplitude f k
    (stoppingCenter (f := f)) stoppingLength centeredStoppingIntervals_pairwiseDisjoint
      (fun z ↦ ‖z‖ₑ) (by simp) x
  simp_rw [stoppingLevelBadPart, hp]
  rw [lintegral_tsum (fun c ↦
    ((measurable_levelAtom hf k (stoppingCenter c) (stoppingLength c)).enorm).aemeasurable)]
  have heq (c : stoppingCell f) :
      (∫⁻ x, ‖levelAtom fullAmplitude f k (stoppingCenter c) (stoppingLength c) x‖ₑ) =
      ENNReal.ofReal (∫ x, ‖levelAtom fullAmplitude f k (stoppingCenter c) (stoppingLength c) x‖) := by
    symm
    simpa only [ofReal_norm] using ofReal_integral_eq_lintegral_ofReal
      (integrable_levelAtom hf (fullAmplitude_pos k).le (stoppingCenter c) (stoppingLength c)).norm
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
  simp_rw [heq]
  exact tsum_atomL1Mass_le_two_mul_global_level_mass hf (fullAmplitude_pos k).le
    _ _ centeredStoppingIntervals_pairwiseDisjoint

theorem tsum_fullMagnitudeLevelL1Mass {f : ℝ → ℂ} (hf : Measurable f) :
    (∑' k, magnitudeLevelL1Mass volume fullAmplitude f k) = ∫⁻ x, ‖f x‖ₑ := by
  unfold magnitudeLevelL1Mass
  rw [← lintegral_iUnion (fun k ↦ measurableSet_magnitudeLevelSet hf k)
    (fun k l hkl ↦ magnitudeLevelSet_disjoint strictMono_fullAmplitude f hkl),
    iUnion_magnitudeLevelSet_eq_univ (fullAmplitude_pos 0).le strictMono_fullAmplitude
      fullAmplitude_cofinal f]
  simp only [Measure.restrict_univ, ofReal_norm]

theorem tsum_lintegral_enorm_stoppingLevelBadPart_le {f : ℝ → ℂ} (hf : Measurable f) :
    (∑' k, ∫⁻ x, ‖stoppingLevelBadPart f k x‖ₑ) ≤ 2 * ∫⁻ x, ‖f x‖ₑ := by
  have hs := ENNReal.tsum_le_tsum (lintegral_enorm_stoppingLevelBadPart_le hf)
  rwa [ENNReal.tsum_mul_left, tsum_fullMagnitudeLevelL1Mass hf] at hs

theorem integrable_stoppingLevelBadPart {f : ℝ → ℂ} (hf : Measurable f)
    (hfi : Integrable f) (k : ℕ) : Integrable (stoppingLevelBadPart f k) := by
  refine ⟨(measurable_stoppingLevelBadPart hf k).aestronglyMeasurable, ?_⟩
  apply (ENNReal.le_tsum k).trans_lt
  exact (tsum_lintegral_enorm_stoppingLevelBadPart_le hf).trans_lt
    (ENNReal.mul_lt_top (by finiteness) hfi.hasFiniteIntegral)

theorem integrable_stoppingBadPart {f : ℝ → ℂ} (hf : Measurable f)
    (hfi : Integrable f) : Integrable (stoppingBadPart f) := by
  refine ⟨(measurable_stoppingBadPart hf hfi).aestronglyMeasurable, ?_⟩
  have hp (x : ℝ) : ‖stoppingBadPart f x‖ₑ ≤ ∑' k, ‖stoppingLevelBadPart f k x‖ₑ := by
    rw [← tsum_stoppingLevelBadPart hf hfi x]
    exact enorm_tsum_le_tsum_enorm
  apply (lintegral_mono hp).trans_lt
  rw [lintegral_tsum (fun k ↦ (measurable_stoppingLevelBadPart hf k).enorm.aemeasurable)]
  exact (tsum_lintegral_enorm_stoppingLevelBadPart_le hf).trans_lt
    (ENNReal.mul_lt_top (by finiteness) hfi.hasFiniteIntegral)

end PositiveStoppingBadEstimate
end QuadraticCarleson
