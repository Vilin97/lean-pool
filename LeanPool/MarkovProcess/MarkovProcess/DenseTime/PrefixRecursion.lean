/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.DenseTime.ConditionalKernel
public import Mathlib.Probability.Kernel.Composition.Lemmas


/-!
# One-step recursion for finite dense-time histories

This file identifies the result of adjoining one conditionally sampled observation to an
augmented finite history. It makes no infinite-process or path-regularity claim.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

private theorem step_transport {X H Z Y T : Type*}
    [MeasurableSpace X] [MeasurableSpace H] [MeasurableSpace Z]
    [MeasurableSpace Y] [MeasurableSpace T]
    (κ : Kernel X Z) (η : Kernel Z Y) [IsSFiniteKernel η] (E : H ≃ᵐ Z)
    (g : H × Y → T) (hg : Measurable g) (q : Z × Y → T)
    (hcompat : g ∘ Prod.map E.symm id = q) :
    (((Kernel.id ×ₖ η.comap E E.measurable) ∘ₖ κ.map E.symm).map g) =
      ((Kernel.id ×ₖ η) ∘ₖ κ).map q := by
  rw [Kernel.comp_map κ (Kernel.id ×ₖ η.comap E E.measurable) E.symm.measurable]
  rw [Kernel.comap_prod]
  rw [Kernel.id_comap]
  rw [← Kernel.id_map]
  rw [← Kernel.comap_comp_right]
  have hcomap : η.comap ((E : H → Z) ∘ E.symm)
      (E.measurable.comp E.symm.measurable) = η := by
    ext z
    rw [Kernel.comap_apply]
    change η (E (E.symm z)) _ = η z _
    rw [E.apply_symm_apply]
  rw [hcomap]
  rw [← Kernel.map_id' η]
  rw [Kernel.map_prod_map]
  · rw [← Kernel.map_comp]
    · rw [← Kernel.map_comp_right]
      · rw [Kernel.map_id']
        change (Kernel.id ×ₖ η ∘ₖ κ).map (g ∘ Prod.map E.symm id) = _
        rw [hcompat]
      all_goals first | exact hg | fun_prop
  all_goals first | exact hg | fun_prop

private theorem prod_comp_prod_map_prodAssoc {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel (X × A) B) [IsSFiniteKernel η] :
    (((Kernel.id ×ₖ η) ∘ₖ (Kernel.id ×ₖ κ)).map MeasurableEquiv.prodAssoc) =
      Kernel.id ×ₖ (κ ⊗ₖ η) := by
  ext x s hs
  rw [Kernel.map_apply' _ MeasurableEquiv.prodAssoc.measurable _ hs, Kernel.comp_apply]
  rw [← Measure.compProd_eq_comp_prod]
  have hfirst : (Kernel.id ×ₖ κ) x = Measure.dirac x ⊗ₘ κ := by
    rw [Measure.compProd_eq_comp_prod]
    exact (Measure.dirac_bind (Kernel.measurable (Kernel.id ×ₖ κ)) x).symm
  rw [hfirst]
  rw [← Measure.map_apply MeasurableEquiv.prodAssoc.measurable hs]
  rw [Measure.compProd_assoc']
  have hlast : (Kernel.id ×ₖ (κ ⊗ₖ η)) x = Measure.dirac x ⊗ₘ (κ ⊗ₖ η) := by
    rw [Measure.compProd_eq_comp_prod]
    exact (Measure.dirac_bind (Kernel.measurable (Kernel.id ×ₖ (κ ⊗ₖ η))) x).symm
  rw [hlast]

end ProbabilityTheory.Kernel

namespace MarkovProcess
namespace DenseTimeHistory

variable {α : Type*} [MeasurableSpace α]

/-- Adjoin one observation at the end of a finite dense-time history. -/
def append (n : ℕ) : DenseTimeHistory α n × α → DenseTimeHistory α (n + 1) :=
  fun hx ↦ (historyEquiv (n + 1)).symm
    ((historyEquiv n hx.1).1, (splitLast n).symm ((historyEquiv n hx.1).2, hx.2))

/-- Adjoining one observation to a finite dense-time history is measurable. -/
theorem measurable_append (n : ℕ) : Measurable (append (α := α) n) := by
  unfold append
  fun_prop

@[simp]
theorem historyEquiv_append (n : ℕ) (history : DenseTimeHistory α n) (x : α) :
    historyEquiv (n + 1) (append n (history, x)) =
      ((historyEquiv n history).1, (splitLast n).symm ((historyEquiv n history).2, x)) := by
  exact MeasurableEquiv.apply_symm_apply _ _

@[simp]
theorem append_apply_castSucc (n : ℕ) (history : DenseTimeHistory α n) (x : α)
    (i : Set.Iic n) :
    append n (history, x) ⟨i, i.property.trans n.le_succ⟩ = history i := by
  rcases i with ⟨_ | i, hi⟩
  · change (historyEquiv (n + 1) (append n (history, x))).1 =
      (historyEquiv n history).1
    rw [historyEquiv_append]
  · let j : Fin n := ⟨i, Nat.succ_le_iff.mp hi⟩
    change (historyEquiv (n + 1) (append n (history, x))).2 j.castSucc =
      (historyEquiv n history).2 j
    rw [historyEquiv_append]
    change (splitLast n).symm ((historyEquiv n history).2, x) j.castSucc = _
    rw [splitLast_symm_apply_castSucc]

@[simp]
theorem append_apply_last (n : ℕ) (history : DenseTimeHistory α n) (x : α) :
    append n (history, x) ⟨n + 1, Nat.le_refl (n + 1)⟩ = x := by
  change (historyEquiv (n + 1) (append n (history, x))).2 (Fin.last n) = x
  rw [historyEquiv_append]
  change (splitLast n).symm ((historyEquiv n history).2, x) (Fin.last n) = x
  rw [splitLast_symm_apply_last]

end DenseTimeHistory

namespace SubMarkovKernelSemigroup

section

variable {D α : Type*} [MeasurableSpace α]

namespace IsConservative

variable [StandardBorelSpace α] [Nonempty α]

/-- Sampling the next observation conditionally and adjoining it gives the next prefix law. -/
theorem augmentedPrefixKernel_step (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (((Kernel.id ×ₖ denseStep P hP e ι n) ∘ₖ augmentedPrefixKernel P e ι n).map
        (DenseTimeHistory.append n)) =
      augmentedPrefixKernel P e ι (n + 1) := by
  let q : ((α × (Fin n → α)) × α) → DenseTimeHistory α (n + 1) :=
    fun z ↦ (DenseTimeHistory.historyEquiv (n + 1)).symm
      (z.1.1, (DenseTimeHistory.splitLast n).symm (z.1.2, z.2))
  let r : (α × ((Fin n → α) × α)) → DenseTimeHistory α (n + 1) :=
    fun z ↦ (DenseTimeHistory.historyEquiv (n + 1)).symm
      (z.1, (DenseTimeHistory.splitLast n).symm z.2)
  let : IsMarkovKernel (denseTimePrefixKernel P e ι n) :=
    hP.isMarkovKernel_denseTimePrefixKernel P e ι n
  let : IsMarkovKernel (denseTimePrefixKernel P e ι (n + 1)) :=
    hP.isMarkovKernel_denseTimePrefixKernel P e ι (n + 1)
  let : IsMarkovKernel (observationCondKernel P hP e ι n) :=
    isMarkovKernel_observationCondKernel P hP e ι n
  have hcompat : DenseTimeHistory.append n ∘
      Prod.map (DenseTimeHistory.historyEquiv n).symm id = q := by
    funext z
    change DenseTimeHistory.append n
      ((DenseTimeHistory.historyEquiv n).symm z.1, z.2) = q z
    rw [DenseTimeHistory.append]
    change _ = (DenseTimeHistory.historyEquiv (n + 1)).symm
      (z.1.1, (DenseTimeHistory.splitLast n).symm (z.1.2, z.2))
    simp only [MeasurableEquiv.apply_symm_apply]
  have htransport := Kernel.step_transport
    (Kernel.id ×ₖ denseTimePrefixKernel P e ι n)
    (observationCondKernel P hP e ι n) (DenseTimeHistory.historyEquiv n)
    (DenseTimeHistory.append n) (DenseTimeHistory.measurable_append n) q hcompat
  rw [augmentedPrefixKernel, denseStep, Kernel.mapOfMeasurable_eq_map]
  rw [htransport]
  have hq : q = r ∘ MeasurableEquiv.prodAssoc := by
    rfl
  rw [hq, Kernel.map_comp_right]
  · rw [Kernel.prod_comp_prod_map_prodAssoc]
    rw [compProd_observationCondKernel P hP e ι n]
    rw [nextObservationJoint]
    rw [Kernel.mapOfMeasurable_eq_map]
    rw [← Kernel.map_id' Kernel.id]
    rw [Kernel.map_prod_map]
    · rw [← Kernel.map_comp_right]
      · change (Kernel.id ×ₖ denseTimePrefixKernel P e ι (n + 1)).map
          (r ∘ Prod.map id (DenseTimeHistory.splitLast n)) = _
        have hr : r ∘ Prod.map id (DenseTimeHistory.splitLast n) =
            (DenseTimeHistory.historyEquiv (n + 1)).symm := by
          funext z
          dsimp only [r, Function.comp_apply, Prod.map_apply, id_eq]
          change (DenseTimeHistory.historyEquiv (n + 1)).symm
            (z.1, (DenseTimeHistory.splitLast n).symm (DenseTimeHistory.splitLast n z.2)) = _
          rw [MeasurableEquiv.symm_apply_apply]
        rw [hr, augmentedPrefixKernel, Kernel.mapOfMeasurable_eq_map]
      all_goals fun_prop
    all_goals fun_prop
  all_goals fun_prop

end IsConservative
end
end SubMarkovKernelSemigroup

end MarkovProcess

end PortComputability
