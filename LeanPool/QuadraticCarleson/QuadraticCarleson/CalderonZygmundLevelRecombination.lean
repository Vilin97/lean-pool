/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundLevelAtoms

/-!
# Recombining Calderón--Zygmund magnitude-level atoms

The magnitude sets form a measurable partition. Consequently their
restrictions sum pointwise to the original function. On a fixed finite
interval, local integrability justifies commuting the corresponding series
with the interval integral and average, and hence recombining the level atoms
into the ordinary centered atom.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators Function Topology

namespace QuadraticCarleson
namespace CalderonZygmundLevelRecombination

open PositiveEndpointOptimization PositiveLevelIntegration
open CalderonZygmundLevelAtoms


noncomputable
section

/-- A finite partial sum of the magnitude-level restrictions. -/
def partialLevelRestricted (A : ℕ → ℝ) (f : ℝ → ℂ) (s : Finset ℕ) : ℝ → ℂ :=
  fun x ↦ ∑ k ∈ s, levelRestricted A f k x

/-- The ordinary centered bad atom on an explicitly supplied interval. -/
def centeredAtom (f : ℝ → ℂ) (z R : ℝ) : ℝ → ℂ :=
  (centeredInterval z R).indicator
    (fun x ↦ f x - ⨍ y in centeredInterval z R, f y)

/-- The centered atom associated to a finite partial sum of levels. -/
def partialLevelAtom (A : ℕ → ℝ) (f : ℝ → ℂ)
    (s : Finset ℕ) (z R : ℝ) : ℝ → ℂ :=
  (centeredInterval z R).indicator
    (fun x ↦ partialLevelRestricted A f s x -
      ⨍ y in centeredInterval z R, partialLevelRestricted A f s y)

/-- At each point, the disjoint magnitude restrictions have exactly one
nonzero term and sum to `f`. -/
theorem hasSum_levelRestricted_apply
    {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    (f : ℝ → ℂ) (x : ℝ) :
    HasSum (fun k ↦ levelRestricted A f k x) (f x) := by
  obtain ⟨k, hxk, hunique⟩ :=
    exists_unique_mem_magnitudeLevelSet hA hcofinal f x
  have heq : (fun l ↦ levelRestricted A f l x) =
      (fun l ↦ if l = k then f x else 0) := by
    funext l
    by_cases hl : l = k
    · subst l
      simp [levelRestricted_apply_of_mem hxk]
    · have hxl : x ∉ magnitudeLevelSet A f l := by
        intro hmem
        exact hl (hunique l hmem)
      simp [hl, levelRestricted_apply_of_not_mem hxl]
  rw [heq]
  exact hasSum_ite_eq k (f x)

theorem tsum_levelRestricted_apply
    {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    (f : ℝ → ℂ) (x : ℝ) :
    (∑' k, levelRestricted A f k x) = f x :=
  (hasSum_levelRestricted_apply hA hcofinal f x).tsum_eq

theorem ae_tsum_levelRestricted_eq
    {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    (f : ℝ → ℂ) :
    (∑' k, levelRestricted A f k ·) =ᵐ[volume] f := by
  filter_upwards with x
  exact tsum_levelRestricted_apply hA hcofinal f x

/-- Finite sums commute with the interval average under precisely the local
integrability of their summands. -/
theorem setAverage_partialLevelRestricted
    {A : ℕ → ℝ} {f : ℝ → ℂ} (s : Finset ℕ) (z R : ℝ)
    (hfi : ∀ k ∈ s, IntegrableOn (levelRestricted A f k) (centeredInterval z R)) :
    (⨍ x in centeredInterval z R, partialLevelRestricted A f s x) =
      ∑ k ∈ s, levelAverage A f k z R := by
  simpa [partialLevelRestricted, levelAverage] using
    (setAverage_finsetSum (s := centeredInterval z R) (t := s) hfi)

/-- No infinite-series hypothesis is needed for the exact finite atom
recombination identity. -/
theorem finset_sum_levelAtom_eq_partialLevelAtom
    {A : ℕ → ℝ} {f : ℝ → ℂ} (s : Finset ℕ) (z R : ℝ)
    (hfi : ∀ k ∈ s, IntegrableOn (levelRestricted A f k) (centeredInterval z R)) :
    (∑ k ∈ s, levelAtom A f k z R) = partialLevelAtom A f s z R := by
  funext x
  have havg := setAverage_partialLevelRestricted s z R hfi
  by_cases hx : x ∈ centeredInterval z R
  · simp only [levelAtom, partialLevelAtom, indicator_of_mem hx, Finset.sum_apply,
      Finset.sum_sub_distrib]
    rw [havg]
    rfl
  · simp [levelAtom, partialLevelAtom, hx]

/-- Local integrability of `f` is enough to commute the countable magnitude
partition with the interval integral. Absolute convergence is supplied by
the disjoint measurable partition rather than assumed separately. -/
theorem hasSum_setIntegral_levelRestricted
    {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    {f : ℝ → ℂ} (hf : Measurable f) (z R : ℝ)
    (hfi : IntegrableOn f (centeredInterval z R)) :
    HasSum
      (fun k ↦ ∫ x in centeredInterval z R, levelRestricted A f k x)
      (∫ x in centeredInterval z R, f x) := by
  let I := centeredInterval z R
  let S : ℕ → Set ℝ := fun k ↦ I ∩ magnitudeLevelSet A f k
  have hSm : ∀ k, MeasurableSet (S k) := fun k ↦
    measurableSet_Ico.inter (measurableSet_magnitudeLevelSet hf k)
  have hSd : Pairwise (Disjoint on S) := by
    intro k l hkl
    exact (magnitudeLevelSet_disjoint hA f hkl).mono inter_subset_right inter_subset_right
  have hUnion : ⋃ k, S k = I := by
    dsimp only [S]
    rw [← inter_iUnion]
    rw [iUnion_magnitudeLevelSet_eq_univ hA hcofinal f]
    simp
  have hsum : HasSum (fun k ↦ ∫ x in S k, f x) (∫ x in I, f x) := by
    rw [← hUnion]
    exact hasSum_integral_iUnion hSm hSd (by simpa [hUnion] using hfi)
  have heq : (fun k ↦ ∫ x in centeredInterval z R, levelRestricted A f k x) =
      (fun k ↦ ∫ x in S k, f x) := by
    funext k
    dsimp only [I, S]
    exact setIntegral_indicator (measurableSet_magnitudeLevelSet hf k)
  rw [heq]
  exact hsum

/-- Countable magnitude-level averages sum to the average of `f`; no
summability assumption beyond local integrability of `f` is required. -/
theorem hasSum_levelAverage
    {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    {f : ℝ → ℂ} (hf : Measurable f) (z R : ℝ)
    (hfi : IntegrableOn f (centeredInterval z R)) :
    HasSum (fun k ↦ levelAverage A f k z R)
      (⨍ x in centeredInterval z R, f x) := by
  have hsum := (hasSum_setIntegral_levelRestricted hA hcofinal hf z R hfi).const_smul
    (volume.real (centeredInterval z R))⁻¹
  simpa [levelAverage, setAverage_eq] using hsum

theorem tsum_levelAverage
    {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    {f : ℝ → ℂ} (hf : Measurable f) (z R : ℝ)
    (hfi : IntegrableOn f (centeredInterval z R)) :
    (∑' k, levelAverage A f k z R) = ⨍ x in centeredInterval z R, f x :=
  (hasSum_levelAverage hA hcofinal hf z R hfi).tsum_eq

/-- The level atoms form a convergent series whose sum is exactly the
ordinary centered atom. -/
theorem hasSum_levelAtom_apply
    {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    {f : ℝ → ℂ} (hf : Measurable f) (z R : ℝ)
    (hfi : IntegrableOn f (centeredInterval z R)) (x : ℝ) :
    HasSum (fun k ↦ levelAtom A f k z R x) (centeredAtom f z R x) := by
  by_cases hx : x ∈ centeredInterval z R
  · have hrestr := hasSum_levelRestricted_apply hA hcofinal f x
    have havg := hasSum_levelAverage hA hcofinal hf z R hfi
    simpa [levelAtom, centeredAtom, hx] using hrestr.sub havg
  · simp [levelAtom, centeredAtom, hx]

theorem tsum_levelAtom_apply
    {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    {f : ℝ → ℂ} (hf : Measurable f) (z R : ℝ)
    (hfi : IntegrableOn f (centeredInterval z R)) (x : ℝ) :
    (∑' k, levelAtom A f k z R x) = centeredAtom f z R x :=
  (hasSum_levelAtom_apply hA hcofinal hf z R hfi x).tsum_eq

theorem ae_tsum_levelAtom_eq_centeredAtom
    {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    {f : ℝ → ℂ} (hf : Measurable f) (z R : ℝ)
    (hfi : IntegrableOn f (centeredInterval z R)) :
    (∑' k, levelAtom A f k z R ·) =ᵐ[volume] centeredAtom f z R := by
  filter_upwards with x
  exact tsum_levelAtom_apply hA hcofinal hf z R hfi x

/-! ### Full and lacunary specializations -/

/-- The sum of the restrictions of `f` to a finite selection of full magnitude levels. -/
abbrev fullPartialLevelRestricted (f : ℝ → ℂ) (s : Finset ℕ) : ℝ → ℂ :=
  partialLevelRestricted fullAmplitude f s

/-- The sum of the restrictions of `f` to a finite selection of lacunary magnitude levels. -/
abbrev lacunaryPartialLevelRestricted (f : ℝ → ℂ) (s : Finset ℕ) : ℝ → ℂ :=
  partialLevelRestricted lacunaryAmplitude f s

/-- The finite sum of full magnitude-level atoms on the chosen interval. -/
abbrev fullPartialLevelAtom (f : ℝ → ℂ) (s : Finset ℕ) (z R : ℝ) : ℝ → ℂ :=
  partialLevelAtom fullAmplitude f s z R

/-- The finite sum of lacunary magnitude-level atoms on the chosen interval. -/
abbrev lacunaryPartialLevelAtom (f : ℝ → ℂ) (s : Finset ℕ) (z R : ℝ) : ℝ → ℂ :=
  partialLevelAtom lacunaryAmplitude f s z R

theorem tsum_fullLevelRestricted_apply (f : ℝ → ℂ) (x : ℝ) :
    (∑' k, levelRestricted fullAmplitude f k x) = f x :=
  tsum_levelRestricted_apply strictMono_fullAmplitude
    (fun t _ ↦ fullAmplitude_cofinal t) f x

theorem tsum_lacunaryLevelRestricted_apply (f : ℝ → ℂ) (x : ℝ) :
    (∑' k, levelRestricted lacunaryAmplitude f k x) = f x :=
  tsum_levelRestricted_apply strictMono_lacunaryAmplitude
    (fun t _ ↦ lacunaryAmplitude_cofinal t) f x

theorem ae_tsum_fullLevelRestricted_eq (f : ℝ → ℂ) :
    (∑' k, levelRestricted fullAmplitude f k ·) =ᵐ[volume] f :=
  ae_tsum_levelRestricted_eq strictMono_fullAmplitude
    (fun t _ ↦ fullAmplitude_cofinal t) f

theorem ae_tsum_lacunaryLevelRestricted_eq (f : ℝ → ℂ) :
    (∑' k, levelRestricted lacunaryAmplitude f k ·) =ᵐ[volume] f :=
  ae_tsum_levelRestricted_eq strictMono_lacunaryAmplitude
    (fun t _ ↦ lacunaryAmplitude_cofinal t) f

theorem setAverage_fullPartialLevelRestricted {f : ℝ → ℂ} (hf : Measurable f)
    (s : Finset ℕ) (z R : ℝ) :
    (⨍ x in centeredInterval z R, fullPartialLevelRestricted f s x) =
      ∑ k ∈ s, levelAverage fullAmplitude f k z R := by
  apply setAverage_partialLevelRestricted
  intro k _
  exact integrableOn_levelRestricted hf (fullAmplitude_pos k).le z R

theorem setAverage_lacunaryPartialLevelRestricted {f : ℝ → ℂ} (hf : Measurable f)
    (s : Finset ℕ) (z R : ℝ) :
    (⨍ x in centeredInterval z R, lacunaryPartialLevelRestricted f s x) =
      ∑ k ∈ s, levelAverage lacunaryAmplitude f k z R := by
  apply setAverage_partialLevelRestricted
  intro k _
  exact integrableOn_levelRestricted hf (lacunaryAmplitude_pos k).le z R

theorem finset_sum_fullLevelAtom_eq {f : ℝ → ℂ} (hf : Measurable f)
    (s : Finset ℕ) (z R : ℝ) :
    (∑ k ∈ s, fullLevelAtom f k z R) = fullPartialLevelAtom f s z R := by
  apply finset_sum_levelAtom_eq_partialLevelAtom
  intro k _
  exact integrableOn_levelRestricted hf (fullAmplitude_pos k).le z R

theorem finset_sum_lacunaryLevelAtom_eq {f : ℝ → ℂ} (hf : Measurable f)
    (s : Finset ℕ) (z R : ℝ) :
    (∑ k ∈ s, lacunaryLevelAtom f k z R) = lacunaryPartialLevelAtom f s z R := by
  apply finset_sum_levelAtom_eq_partialLevelAtom
  intro k _
  exact integrableOn_levelRestricted hf (lacunaryAmplitude_pos k).le z R

theorem tsum_fullLevelAverage {f : ℝ → ℂ} (hf : Measurable f) (z R : ℝ)
    (hfi : IntegrableOn f (centeredInterval z R)) :
    (∑' k, levelAverage fullAmplitude f k z R) =
      ⨍ x in centeredInterval z R, f x :=
  tsum_levelAverage strictMono_fullAmplitude
    (fun t _ ↦ fullAmplitude_cofinal t) hf z R hfi

theorem tsum_lacunaryLevelAverage {f : ℝ → ℂ} (hf : Measurable f) (z R : ℝ)
    (hfi : IntegrableOn f (centeredInterval z R)) :
    (∑' k, levelAverage lacunaryAmplitude f k z R) =
      ⨍ x in centeredInterval z R, f x :=
  tsum_levelAverage strictMono_lacunaryAmplitude
    (fun t _ ↦ lacunaryAmplitude_cofinal t) hf z R hfi

theorem tsum_fullLevelAtom_apply {f : ℝ → ℂ} (hf : Measurable f) (z R : ℝ)
    (hfi : IntegrableOn f (centeredInterval z R)) (x : ℝ) :
    (∑' k, fullLevelAtom f k z R x) = centeredAtom f z R x :=
  tsum_levelAtom_apply strictMono_fullAmplitude
    (fun t _ ↦ fullAmplitude_cofinal t) hf z R hfi x

theorem tsum_lacunaryLevelAtom_apply {f : ℝ → ℂ} (hf : Measurable f) (z R : ℝ)
    (hfi : IntegrableOn f (centeredInterval z R)) (x : ℝ) :
    (∑' k, lacunaryLevelAtom f k z R x) = centeredAtom f z R x :=
  tsum_levelAtom_apply strictMono_lacunaryAmplitude
    (fun t _ ↦ lacunaryAmplitude_cofinal t) hf z R hfi x

theorem ae_tsum_fullLevelAtom_eq_centeredAtom {f : ℝ → ℂ} (hf : Measurable f)
    (z R : ℝ) (hfi : IntegrableOn f (centeredInterval z R)) :
    (∑' k, fullLevelAtom f k z R ·) =ᵐ[volume] centeredAtom f z R :=
  ae_tsum_levelAtom_eq_centeredAtom strictMono_fullAmplitude
    (fun t _ ↦ fullAmplitude_cofinal t) hf z R hfi

theorem ae_tsum_lacunaryLevelAtom_eq_centeredAtom {f : ℝ → ℂ} (hf : Measurable f)
    (z R : ℝ) (hfi : IntegrableOn f (centeredInterval z R)) :
    (∑' k, lacunaryLevelAtom f k z R ·) =ᵐ[volume] centeredAtom f z R :=
  ae_tsum_levelAtom_eq_centeredAtom strictMono_lacunaryAmplitude
    (fun t _ ↦ lacunaryAmplitude_cofinal t) hf z R hfi

end
end CalderonZygmundLevelRecombination
end QuadraticCarleson
