/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.DyadicAtomScales
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveStoppingBadRecombination

/-!
# Canonical stopping atoms sliced by their exact dyadic lengths

The scale class is exactly `2^j ≤ length < 2^(j+1)`. The construction is
generic in the magnitude amplitudes and therefore covers both the full and
lacunary partitions. No interval family is supplied as an assumption.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace CanonicalScaleAtoms

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms CalderonZygmundLevelRecombination
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate
open PositiveStoppingBadEstimate

noncomputable def canonicalLevelBadPart (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  disjointLevelAtomSum A f k (stoppingCenter (f := f)) stoppingLength

/-- The actual `b_{j,k}`, summed over exactly the canonical cells whose
length lies in the approved half-open dyadic scale class. -/
noncomputable def stoppingScaleLevelBadPart (A : ℕ → ℝ) (f : ℝ → ℂ)
    (j : ℤ) (k : ℕ) (x : ℝ) : ℂ :=
  ∑' c : stoppingCell f,
    (dyadicAtomScaleClass (stoppingLength (f := f)) j).indicator
      (fun c ↦ levelAtom A f k (stoppingCenter c) (stoppingLength c) x) c

theorem canonicalLevelBadPart_eq_atom_of_mem (A : ℕ → ℝ) {f : ℝ → ℂ}
    (c : stoppingCell f) {x : ℝ} (hx : x ∈ c.1.interval (rootLength f)) (k : ℕ) :
    canonicalLevelBadPart A f k x =
      levelAtom A f k (stoppingCenter c) (stoppingLength c) x := by
  classical
  unfold canonicalLevelBadPart disjointLevelAtomSum
  apply tsum_eq_single c
  intro d hdc
  exact levelAtom_eq_zero_of_other_mem centeredStoppingIntervals_pairwiseDisjoint hdc
    (by simpa only [centeredInterval_eq_stoppingInterval] using hx)

theorem stoppingScaleLevelBadPart_eq_atom_of_mem (A : ℕ → ℝ) {f : ℝ → ℂ}
    (c : stoppingCell f) {x : ℝ} (hx : x ∈ c.1.interval (rootLength f)) (j : ℤ) (k : ℕ) :
    stoppingScaleLevelBadPart A f j k x =
      (dyadicAtomScaleClass stoppingLength j).indicator
        (fun c ↦ levelAtom A f k (stoppingCenter c) (stoppingLength c) x) c := by
  classical
  unfold stoppingScaleLevelBadPart
  apply tsum_eq_single c
  intro d hdc
  have hz := levelAtom_eq_zero_of_other_mem (A := A) (f := f) (k := k)
    centeredStoppingIntervals_pairwiseDisjoint hdc
    (by simpa only [centeredInterval_eq_stoppingInterval] using hx)
  by_cases hd : d ∈ dyadicAtomScaleClass stoppingLength j <;> simp [hd, hz]

theorem canonicalLevelBadPart_eq_zero_of_notMem (A : ℕ → ℝ) {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ stoppingBadUnion f) (k : ℕ) : canonicalLevelBadPart A f k x = 0 := by
  have hz (c : stoppingCell f) :
      levelAtom A f k (stoppingCenter c) (stoppingLength c) x = 0 := by
    apply levelAtom_eq_zero_of_not_mem
    rw [centeredInterval_eq_stoppingInterval]
    exact fun hc ↦ hx (mem_iUnion.mpr ⟨c, hc⟩)
  simp only [canonicalLevelBadPart, disjointLevelAtomSum, hz, tsum_zero]

theorem stoppingScaleLevelBadPart_eq_zero_of_notMem (A : ℕ → ℝ) {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ stoppingBadUnion f) (j : ℤ) (k : ℕ) :
    stoppingScaleLevelBadPart A f j k x = 0 := by
  have hz (c : stoppingCell f) :
      levelAtom A f k (stoppingCenter c) (stoppingLength c) x = 0 := by
    apply levelAtom_eq_zero_of_not_mem
    rw [centeredInterval_eq_stoppingInterval]
    exact fun hc ↦ hx (mem_iUnion.mpr ⟨c, hc⟩)
  simp [stoppingScaleLevelBadPart, hz]

/-- Every point sees at most one spatial scale, since canonical cells are
literally disjoint and every positive length belongs to one scale class. -/
theorem stoppingScaleLevelBadPart_eq_single_scale (A : ℕ → ℝ) (f : ℝ → ℂ)
    (k : ℕ) (x : ℝ) : ∃ j₀ : ℤ, ∀ j : ℤ,
    stoppingScaleLevelBadPart A f j k x =
      if j = j₀ then canonicalLevelBadPart A f k x else 0 := by
  classical
  by_cases hx : x ∈ stoppingBadUnion f
  · obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    refine ⟨dyadicAtomScaleIndex stoppingLength stoppingLength_pos c, ?_⟩
    intro j
    rw [stoppingScaleLevelBadPart_eq_atom_of_mem A c hc,
      canonicalLevelBadPart_eq_atom_of_mem A c hc]
    have heq : c ∈ dyadicAtomScaleClass stoppingLength j ↔
        j = dyadicAtomScaleIndex stoppingLength stoppingLength_pos c := by
      rw [mem_dyadicAtomScaleClass_iff_index_eq stoppingLength stoppingLength_pos]
      exact eq_comm
    simp only [indicator_apply, heq]
  · refine ⟨0, fun j ↦ ?_⟩
    simp only [stoppingScaleLevelBadPart_eq_zero_of_notMem A hx,
      canonicalLevelBadPart_eq_zero_of_notMem A hx, ite_self]

theorem hasSum_stoppingScaleLevelBadPart (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (x : ℝ) :
    HasSum (fun j : ℤ ↦ stoppingScaleLevelBadPart A f j k x) (canonicalLevelBadPart A f k x) := by
  obtain ⟨j₀, hj₀⟩ := stoppingScaleLevelBadPart_eq_single_scale A f k x
  simp_rw [hj₀]
  exact hasSum_ite_eq j₀ _

theorem tsum_stoppingScaleLevelBadPart (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (x : ℝ) :
    (∑' j : ℤ, stoppingScaleLevelBadPart A f j k x) = canonicalLevelBadPart A f k x :=
  (hasSum_stoppingScaleLevelBadPart A f k x).tsum_eq

theorem tsum_enorm_stoppingScaleLevelBadPart (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (x : ℝ) :
    (∑' j : ℤ, ‖stoppingScaleLevelBadPart A f j k x‖ₑ) = ‖canonicalLevelBadPart A f k x‖ₑ := by
  classical
  obtain ⟨j₀, hj₀⟩ := stoppingScaleLevelBadPart_eq_single_scale A f k x
  simp_rw [hj₀]
  rw [tsum_eq_single j₀]
  · simp
  · intro j hj
    simp [hj]

theorem pairwiseDisjoint_support_stoppingScaleLevelBadPart
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) :
    Pairwise (Disjoint on fun j : ℤ ↦ Function.support (stoppingScaleLevelBadPart A f j k)) := by
  intro j l hjl
  apply Set.disjoint_left.mpr
  intro x hxj hxl
  obtain ⟨j₀, hj₀⟩ := stoppingScaleLevelBadPart_eq_single_scale A f k x
  have hj : j = j₀ := by
    by_contra h
    exact hxj (by rw [hj₀ j, ite_eq_right h])
  have hl : l = j₀ := by
    by_contra h
    exact hxl (by rw [hj₀ l, ite_eq_right h])
  exact hjl (hj.trans hl.symm)

theorem measurable_stoppingScaleLevelBadPart {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) (j : ℤ) (k : ℕ) : Measurable (stoppingScaleLevelBadPart A f j k) := by
  apply Measurable.tsum
  intro c
  by_cases hc : c ∈ dyadicAtomScaleClass stoppingLength j
  · simpa only [indicator_of_mem hc] using measurable_levelAtom hf k (stoppingCenter c) (stoppingLength c)
  · simp only [indicator_of_notMem hc]
    exact measurable_const

theorem measurable_canonicalLevelBadPart {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) (k : ℕ) : Measurable (canonicalLevelBadPart A f k) :=
  measurable_disjointLevelAtomSum hf k _ _

/-- Exact L¹ mass packing across spatial scales; there is no overlap loss. -/
theorem tsum_lintegral_enorm_stoppingScaleLevelBadPart {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) (k : ℕ) :
    (∑' j : ℤ, ∫⁻ x, ‖stoppingScaleLevelBadPart A f j k x‖ₑ) =
      ∫⁻ x, ‖canonicalLevelBadPart A f k x‖ₑ := by
  rw [← lintegral_tsum (fun j ↦ (measurable_stoppingScaleLevelBadPart hf j k).enorm.aemeasurable)]
  simp only [tsum_enorm_stoppingScaleLevelBadPart]

theorem lintegral_enorm_canonicalLevelBadPart_le {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) {k : ℕ} (hAk : 0 ≤ A k) :
    (∫⁻ x, ‖canonicalLevelBadPart A f k x‖ₑ) ≤
      2 * magnitudeLevelL1Mass volume A f k := by
  have hp (x : ℝ) := map_disjointLevelAtomSum A f k
    (stoppingCenter (f := f)) stoppingLength centeredStoppingIntervals_pairwiseDisjoint
      (fun z ↦ ‖z‖ₑ) (by simp) x
  simp_rw [canonicalLevelBadPart, hp]
  rw [lintegral_tsum (fun c ↦
    (measurable_levelAtom hf k (stoppingCenter c) (stoppingLength c)).enorm.aemeasurable)]
  have heq (c : stoppingCell f) :
      (∫⁻ x, ‖levelAtom A f k (stoppingCenter c) (stoppingLength c) x‖ₑ) =
      ENNReal.ofReal (∫ x, ‖levelAtom A f k (stoppingCenter c) (stoppingLength c) x‖) := by
    symm
    simpa only [ofReal_norm] using ofReal_integral_eq_lintegral_ofReal
      (integrable_levelAtom hf hAk (stoppingCenter c) (stoppingLength c)).norm
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
  simp_rw [heq]
  exact tsum_atomL1Mass_le_two_mul_global_level_mass hf hAk
    _ _ centeredStoppingIntervals_pairwiseDisjoint

theorem integrable_canonicalLevelBadPart {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) {k : ℕ} (hAk : 0 ≤ A k) :
    Integrable (canonicalLevelBadPart A f k) := by
  refine ⟨(measurable_canonicalLevelBadPart hf k).aestronglyMeasurable, ?_⟩
  apply (lintegral_enorm_canonicalLevelBadPart_le hf hAk).trans_lt
  apply ENNReal.mul_lt_top (by finiteness)
  apply lt_of_le_of_lt ?_ hfi.hasFiniteIntegral
  simpa only [magnitudeLevelL1Mass, ofReal_norm, Measure.restrict_univ] using
    lintegral_mono_set (μ := volume) (f := fun x ↦ ‖f x‖ₑ)
      (subset_univ (magnitudeLevelSet A f k))

theorem integrable_stoppingScaleLevelBadPart {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (j : ℤ) {k : ℕ} (hAk : 0 ≤ A k) :
    Integrable (stoppingScaleLevelBadPart A f j k) := by
  refine ⟨(measurable_stoppingScaleLevelBadPart hf j k).aestronglyMeasurable, ?_⟩
  apply (ENNReal.le_tsum j).trans_lt
  rw [tsum_lintegral_enorm_stoppingScaleLevelBadPart hf]
  exact (integrable_canonicalLevelBadPart hf hfi hAk).hasFiniteIntegral

theorem tsum_stoppingScaleLevelBadPart_full (f : ℝ → ℂ) (k : ℕ) (x : ℝ) :
    (∑' j : ℤ, stoppingScaleLevelBadPart fullAmplitude f j k x) = stoppingLevelBadPart f k x :=
  tsum_stoppingScaleLevelBadPart fullAmplitude f k x

noncomputable def lacunaryStoppingLevelBadPart (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  canonicalLevelBadPart lacunaryAmplitude f k

theorem tsum_stoppingScaleLevelBadPart_lacunary (f : ℝ → ℂ) (k : ℕ) (x : ℝ) :
    (∑' j : ℤ, stoppingScaleLevelBadPart lacunaryAmplitude f j k x) =
      lacunaryStoppingLevelBadPart f k x :=
  tsum_stoppingScaleLevelBadPart lacunaryAmplitude f k x

theorem hasSum_canonicalLevelBadPart {A : ℕ → ℝ}
    (hA0 : 0 ≤ A 0) (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    HasSum (fun k ↦ canonicalLevelBadPart A f k x) (stoppingBadPart f x) := by
  by_cases hx : x ∈ stoppingBadUnion f
  · obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    simp_rw [canonicalLevelBadPart_eq_atom_of_mem A c hc]
    have hs := hasSum_levelAtom_apply hA0 hA hcofinal hf
      (stoppingCenter c) (stoppingLength c) hfi.integrableOn x
    convert hs using 1
    unfold stoppingBadPart centeredAtom
    rw [centeredInterval_eq_stoppingInterval, indicator_of_mem hc,
      stoppingGoodPart_eq_average_of_mem c hc]
    rfl
  · simp only [canonicalLevelBadPart_eq_zero_of_notMem A hx]
    rw [stoppingBadPart, stoppingGoodPart_eq_of_notMem hx, sub_self]
    exact hasSum_zero

theorem hasSum_lacunaryStoppingLevelBadPart {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    HasSum (fun k ↦ lacunaryStoppingLevelBadPart f k x) (stoppingBadPart f x) :=
  hasSum_canonicalLevelBadPart (lacunaryAmplitude_pos 0).le strictMono_lacunaryAmplitude
    lacunaryAmplitude_cofinal hf hfi x

/-- Summing both the exact spatial slices and the lacunary magnitude
levels loses only the usual atom mass factor two. -/
theorem tsum_lacunary_scale_level_L1Mass_le {f : ℝ → ℂ} (hf : Measurable f) :
    (∑' k : ℕ, ∑' j : ℤ, ∫⁻ x, ‖stoppingScaleLevelBadPart lacunaryAmplitude f j k x‖ₑ) ≤
      2 * ∫⁻ x, ‖f x‖ₑ := by
  simp_rw [tsum_lintegral_enorm_stoppingScaleLevelBadPart hf]
  have hm : (∑' k, magnitudeLevelL1Mass volume lacunaryAmplitude f k) =
      ∫⁻ x, ‖f x‖ₑ := by
    unfold magnitudeLevelL1Mass
    rw [← lintegral_iUnion (fun k ↦ measurableSet_magnitudeLevelSet hf k)
      (fun k l hkl ↦ magnitudeLevelSet_disjoint strictMono_lacunaryAmplitude f hkl),
      iUnion_magnitudeLevelSet_eq_univ (lacunaryAmplitude_pos 0).le
        strictMono_lacunaryAmplitude lacunaryAmplitude_cofinal f]
    simp only [Measure.restrict_univ, ofReal_norm]
  have hs := ENNReal.tsum_le_tsum (fun k ↦
    lintegral_enorm_canonicalLevelBadPart_le hf (lacunaryAmplitude_pos k).le)
  rwa [ENNReal.tsum_mul_left, hm] at hs

end CanonicalScaleAtoms
end QuadraticCarleson
