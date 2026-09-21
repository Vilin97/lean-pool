/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Time.CountableDenseTime
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.ProjectiveFamily

/-!
# Kernels on finite prefixes of a countable time enumeration

This file constructs the finite-dimensional kernel on the first `n` points of an arbitrary
enumeration, with coordinates retained in enumeration order. The enumeration need not respect
the order of physical time.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

variable {D α : Type*} [MeasurableSpace α]

/-- The physical times occurring in the first `n` positions of an enumeration. -/
def denseTimePhysicalPrefix (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Finset NNReal :=
  (CountableEnumeration.prefix e n).map ι

private theorem denseTimePhysicalPrefix_mono (e : ℕ ≃ D) (ι : D ↪ NNReal) :
    Monotone (denseTimePhysicalPrefix e ι) := by
  intro m n hmn t ht
  rw [denseTimePhysicalPrefix, Finset.mem_map] at ht ⊢
  obtain ⟨d, hd, rfl⟩ := ht
  exact ⟨d, CountableEnumeration.prefix_mono e hmn hd, rfl⟩

private theorem denseTime_mem_physicalPrefix (e : ℕ ≃ D) (ι : D ↪ NNReal)
    (n : ℕ) (i : Fin n) : ι (e i) ∈ denseTimePhysicalPrefix e ι n := by
  rw [denseTimePhysicalPrefix, Finset.mem_map]
  exact ⟨e i, by
    rw [CountableEnumeration.mem_prefix_iff, e.symm_apply_apply]
    exact i.isLt, rfl⟩

/-- Reindex a path on the physical prefix by its enumeration positions. -/
def denseTimePrefixReindex (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ)
    (path : denseTimePhysicalPrefix e ι n → α) : Fin n → α :=
  fun i ↦ path ⟨ι (e i), denseTime_mem_physicalPrefix e ι n i⟩

/-- Reindexing a physical-prefix path by enumeration positions is measurable. -/
theorem measurable_denseTimePrefixReindex (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    Measurable (denseTimePrefixReindex (α := α) e ι n) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_apply
    (⟨ι (e i), denseTime_mem_physicalPrefix e ι n i⟩ : denseTimePhysicalPrefix e ι n)

/-- The finite-dimensional kernel on the first `n` enumerated physical times, with coordinates
in enumeration order. -/
def denseTimePrefixKernel (P : SubMarkovKernelSemigroup α) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) : Kernel α (Fin n → α) :=
  Kernel.mapOfMeasurable (finiteSetKernel P (denseTimePhysicalPrefix e ι n))
    (denseTimePrefixReindex e ι n) (measurable_denseTimePrefixReindex e ι n)

/-- The enumeration-prefix kernel agrees with the ordinary kernel map. -/
theorem denseTimePrefixKernel_eq_map (P : SubMarkovKernelSemigroup α) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) :
    denseTimePrefixKernel P e ι n =
      (finiteSetKernel P (denseTimePhysicalPrefix e ι n)).map
        (denseTimePrefixReindex e ι n) :=
  Kernel.mapOfMeasurable_eq_map _ (measurable_denseTimePrefixReindex e ι n)

omit [MeasurableSpace α] in
private theorem denseTimePrefixReindex_restrict {m n : ℕ} (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (h : m ≤ n) :
    denseTimePrefixReindex (α := α) e ι m ∘
        Finset.restrict₂ (π := fun _ ↦ α) (denseTimePhysicalPrefix_mono e ι h) =
      FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h) ∘
        denseTimePrefixReindex e ι n := by
  funext path i
  rfl

namespace IsConservative

/-- Under conservativity, each enumeration-prefix kernel is a Markov kernel. -/
theorem isMarkovKernel_denseTimePrefixKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (denseTimePrefixKernel P e ι n) := by
  rw [denseTimePrefixKernel_eq_map]
  let : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalPrefix e ι n)) :=
    hP.isMarkovKernel_finiteSetKernel P _
  exact Kernel.IsMarkovKernel.map _ (measurable_denseTimePrefixReindex e ι n)

/-- Under conservativity, an enumeration-prefix kernel gives a probability measure at every
starting state. -/
theorem isProbabilityMeasure_denseTimePrefixKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) (x : α) :
    IsProbabilityMeasure (denseTimePrefixKernel P e ι n x) := by
  let : IsMarkovKernel (denseTimePrefixKernel P e ι n) :=
    hP.isMarkovKernel_denseTimePrefixKernel P e ι n
  exact IsMarkovKernel.isProbabilityMeasure x

/-- Prefix kernels are exactly consistent under restriction to an earlier prefix. -/
theorem denseTimePrefixKernel_map_restrictPath (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) {m n : ℕ} (h : m ≤ n) :
    denseTimePrefixKernel P e ι m =
      (denseTimePrefixKernel P e ι n).map
        (FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h)) := by
  rw [denseTimePrefixKernel_eq_map, denseTimePrefixKernel_eq_map,
    hP.finiteSetKernel_map_restrict₂ P (denseTimePhysicalPrefix_mono e ι h),
    ← Kernel.map_comp_right, ← Kernel.map_comp_right]
  · rw [denseTimePrefixReindex_restrict e ι h]
  · exact measurable_denseTimePrefixReindex e ι n
  · exact FiniteOrderedTimes.measurable_restrictPath (Fin.castLEOrderEmb h)
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ α)
      (denseTimePhysicalPrefix_mono e ι h)
  · exact measurable_denseTimePrefixReindex e ι m

end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess
