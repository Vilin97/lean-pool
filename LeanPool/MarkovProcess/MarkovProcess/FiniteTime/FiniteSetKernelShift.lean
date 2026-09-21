/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.DenseTimeFiniteShift
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.KernelShift
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.ProjectiveFamily

/-!
# Translation of finite-set kernels

This file translates finite sets of nonnegative observation times, reindexes paths on the
translated set back to the original coordinates, and proves the corresponding translation law
for conservative transition-kernel semigroups.  It is finite-dimensional kernel infrastructure;
it does not assert a path-space Markov property.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

/-- The image of a finite set of nonnegative times under translation by `s`. -/
def finiteSetTranslate (s : NNReal) (I : Finset NNReal) : Finset NNReal :=
  I.map (addLeftEmbedding s)

@[simp]
theorem mem_finiteSetTranslate (s : NNReal) (I : Finset NNReal) (t : NNReal) :
    t ∈ finiteSetTranslate s I ↔ ∃ r ∈ I, s + r = t := by
  rw [finiteSetTranslate, Finset.mem_map]
  rfl

/-- Translation identifies the original finite time set with its translated image. -/
def finiteSetTranslateEquiv (s : NNReal) (I : Finset NNReal) : I ≃ finiteSetTranslate s I :=
  Equiv.ofBijective
    (fun t ↦ ⟨s + t, (mem_finiteSetTranslate s I (s + t)).mpr ⟨t, t.property, rfl⟩⟩)
    ⟨by
      intro t u h
      apply Subtype.ext
      exact add_left_cancel (congrArg Subtype.val h),
    by
      intro t
      obtain ⟨r, hrI, hrt⟩ := (mem_finiteSetTranslate s I t).mp t.property
      exact ⟨⟨r, hrI⟩, Subtype.ext hrt⟩⟩

@[simp]
theorem finiteSetTranslateEquiv_apply (s : NNReal) (I : Finset NNReal) (t : I) :
    (finiteSetTranslateEquiv s I t : NNReal) = s + t :=
  rfl

/-- Reindex a path on translated times back to the original finite set. -/
def pullbackFiniteSetTranslate {alpha : Type*} (s : NNReal) (I : Finset NNReal)
    (path : finiteSetTranslate s I → alpha) : I → alpha :=
  fun t ↦ path (finiteSetTranslateEquiv s I t)

@[simp]
theorem pullbackFiniteSetTranslate_apply {alpha : Type*} (s : NNReal) (I : Finset NNReal)
    (path : finiteSetTranslate s I → alpha) (t : I) :
    pullbackFiniteSetTranslate s I path t = path (finiteSetTranslateEquiv s I t) :=
  rfl

theorem measurable_pullbackFiniteSetTranslate {alpha : Type*} [MeasurableSpace alpha]
    (s : NNReal) (I : Finset NNReal) :
    Measurable (pullbackFiniteSetTranslate (alpha := alpha) s I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply (finiteSetTranslateEquiv s I t)

private def finiteSetTranslateFinOrderIso (s : NNReal) (I : Finset NNReal) :
    Fin I.card ≃o Fin (finiteSetTranslate s I).card :=
  Fin.castOrderIso (by simp only [finiteSetTranslate, Finset.card_map])

private theorem finiteSetTimes_translate (s : NNReal) (I : Finset NNReal) :
    (finiteSetTimes (finiteSetTranslate s I)).restrict
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding =
      (finiteSetTimes I).translate s := by
  let e := (finiteSetTranslateFinOrderIso s I).toOrderEmbedding
  have hcard : (finiteSetTranslate s I).card = I.card := by
    simp only [finiteSetTranslate, Finset.card_map]
  have hleft :
      (fun i : Fin I.card ↦ finiteSetTimes (finiteSetTranslate s I) (e i)) =
        (finiteSetTranslate s I).orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      exact Finset.orderEmbOfFin_mem _ rfl (e i)
    · exact (finiteSetTimes (finiteSetTranslate s I)).strictMono.comp e.strictMono
  have hright :
      (fun i : Fin I.card ↦ s + finiteSetTimes I i) =
        (finiteSetTranslate s I).orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      exact Finset.mem_map_of_mem (addLeftEmbedding s)
        (Finset.orderEmbOfFin_mem I rfl i)
    · intro i j hij
      simpa only [add_comm] using add_lt_add_left ((finiteSetTimes I).strictMono hij) s
  apply DFunLike.ext _ _
  intro i
  exact congrFun (hleft.trans hright.symm) i

private theorem pullback_orderedPathToFiniteSet {alpha : Type*}
    (s : NNReal) (I : Finset NNReal) :
    pullbackFiniteSetTranslate (alpha := alpha) s I ∘
        orderedPathToFiniteSet (α := alpha) (finiteSetTranslate s I) =
      orderedPathToFiniteSet I ∘ FiniteOrderedTimes.restrictPath
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding := by
  funext path t
  apply congrArg path
  apply (finiteSetTimes (finiteSetTranslate s I)).injective
  have hshifted :
      finiteSetTimes (finiteSetTranslate s I)
          (((finiteSetTranslate s I).orderIsoOfFin rfl).symm
            (finiteSetTranslateEquiv s I t)) =
        s + t := by
    change (((finiteSetTranslate s I).orderIsoOfFin rfl
      (((finiteSetTranslate s I).orderIsoOfFin rfl).symm
        (finiteSetTranslateEquiv s I t)) : finiteSetTranslate s I) : NNReal) = s + t
    rw [OrderIso.apply_symm_apply]
    exact finiteSetTranslateEquiv_apply s I t
  have htimes := congrArg
    (fun times : FiniteOrderedTimes I.card ↦
      times ((I.orderIsoOfFin rfl).symm t))
    (finiteSetTimes_translate s I)
  have horiginal : finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) = t := by
    change (((I.orderIsoOfFin rfl) ((I.orderIsoOfFin rfl).symm t) : I) : NNReal) = t
    exact congrArg Subtype.val ((I.orderIsoOfFin rfl).apply_symm_apply t)
  change finiteSetTimes (finiteSetTranslate s I)
      ((finiteSetTranslateFinOrderIso s I).toOrderEmbedding
        ((I.orderIsoOfFin rfl).symm t)) =
    s + finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) at htimes
  rw [horiginal] at htimes
  rw [hshifted]
  exact htimes.symm

namespace IsConservative

variable {alpha : Type*} [MeasurableSpace alpha]

/-- Translating a finite observation set is the same as evolving first for the translation
amount, after the translated coordinates are reindexed by their original times. -/
theorem finiteSetKernel_map_pullback_translate
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (s : NNReal) (I : Finset NNReal) :
    (finiteSetKernel P (finiteSetTranslate s I)).map
        (pullbackFiniteSetTranslate (alpha := alpha) s I) =
      (finiteSetKernel P I).comp (P s) := by
  rw [finiteSetKernel_eq_map, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
  · rw [pullback_orderedPathToFiniteSet, Kernel.map_comp_right]
    · rw [hP.finiteTimeKernel_map_restrictPath P
          (finiteSetTimes (finiteSetTranslate s I))
          (finiteSetTranslateFinOrderIso s I).toOrderEmbedding,
        finiteSetTimes_translate, hP.finiteTimeKernel_translate P s,
        Kernel.map_comp]
    · exact FiniteOrderedTimes.measurable_restrictPath
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding
    · exact measurable_orderedPathToFiniteSet I
  · exact measurable_orderedPathToFiniteSet (finiteSetTranslate s I)
  · exact measurable_pullbackFiniteSetTranslate s I

end IsConservative

end
end SubMarkovKernelSemigroup

namespace DenseTime

/-- Casting a translated finite dense-time set to physical time agrees with translating its
finite set of physical times. -/
theorem map_castOrderEmbedding_addFinset (s : DenseTime) (I : Finset DenseTime) :
    (addFinset s I).map castOrderEmbedding.toEmbedding =
      SubMarkovKernelSemigroup.finiteSetTranslate (castOrderEmbedding s)
        (I.map castOrderEmbedding.toEmbedding) := by
  ext t
  simp only [addFinset, SubMarkovKernelSemigroup.finiteSetTranslate, Finset.mem_map]
  constructor
  · rintro ⟨u, ⟨r, hrI, rfl⟩, rfl⟩
    exact ⟨castOrderEmbedding r, ⟨r, hrI, rfl⟩, (castOrderEmbedding_add s r).symm⟩
  · rintro ⟨u, ⟨r, hrI, hru⟩, hut⟩
    subst u
    exact ⟨s + r, ⟨r, hrI, rfl⟩, (castOrderEmbedding_add s r).trans hut⟩

end DenseTime
end MarkovProcess
