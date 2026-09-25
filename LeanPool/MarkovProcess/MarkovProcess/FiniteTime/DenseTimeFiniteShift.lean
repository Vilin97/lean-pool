/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.DenseTime.Shift


/-!
# Finite-coordinate shifts on dense-time paths

Addition by a dense time transports finite sets of dense-time coordinates injectively.  This file
provides the resulting coordinate equivalence and relates restriction after shifting a dense-time
path to restriction on the translated finite set.  It makes no probability-law or Markov claim.
-/

@[expose] public section

noncomputable section PortComputability

namespace MarkovProcess

section

namespace DenseTime

/-- The image of a finite dense-time set under addition by `s`. -/
def addFinset (s : DenseTime) (I : Finset DenseTime) : Finset DenseTime :=
  I.map (addOrderEmbedding s).toEmbedding

@[simp]
theorem mem_addFinset (s : DenseTime) (I : Finset DenseTime) (t : DenseTime) :
    t ∈ addFinset s I ↔ ∃ r ∈ I, s + r = t := by
  rw [addFinset, Finset.mem_map]
  constructor
  · rintro ⟨r, hr, hrt⟩
    exact ⟨r, hr, hrt⟩
  · rintro ⟨r, hr, hrt⟩
    exact ⟨r, hr, hrt⟩

/-- Addition by `s` identifies a finite dense-time set with its translated image. -/
def addFinsetEquiv (s : DenseTime) (I : Finset DenseTime) : I ≃ addFinset s I :=
  Equiv.ofBijective
    (fun t ↦ ⟨s + t, (mem_addFinset s I (s + t)).mpr ⟨t, t.property, rfl⟩⟩)
    ⟨by
      intro t u h
      apply Subtype.ext
      apply (addOrderEmbedding s).injective
      exact congrArg Subtype.val h,
    by
      intro t
      obtain ⟨r, hrI, hrt⟩ := (mem_addFinset s I t).mp t.property
      refine ⟨⟨r, hrI⟩, Subtype.ext ?_⟩
      exact hrt⟩

@[simp]
theorem addFinsetEquiv_apply (s : DenseTime) (I : Finset DenseTime) (t : I) :
    (addFinsetEquiv s I t : DenseTime) = s + t := rfl

end DenseTime

namespace DenseTimePath

variable {alpha : Type*}

/-- Reindex a path on a translated finite dense-time set back to the original coordinates. -/
def pullbackAddFinset (s : DenseTime) (I : Finset DenseTime)
    (path : DenseTime.addFinset s I → alpha) : I → alpha :=
  fun t ↦ path (DenseTime.addFinsetEquiv s I t)

@[simp]
theorem pullbackAddFinset_apply (s : DenseTime) (I : Finset DenseTime)
    (path : DenseTime.addFinset s I → alpha) (t : I) :
    pullbackAddFinset s I path t = path (DenseTime.addFinsetEquiv s I t) := rfl

variable [MeasurableSpace alpha]

/-- Reindexing from a translated finite dense-time set is measurable. -/
theorem measurable_pullbackAddFinset (s : DenseTime) (I : Finset DenseTime) :
    Measurable (pullbackAddFinset (alpha := alpha) s I) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_pi_apply (DenseTime.addFinsetEquiv s I t)

omit [MeasurableSpace alpha] in
/-- Restriction after shifting equals translated restriction followed by the canonical
reindexing. -/
theorem restrict_shift (s : DenseTime) (I : Finset DenseTime) (path : DenseTime → alpha) :
    I.restrict (shift s path) =
      pullbackAddFinset s I ((DenseTime.addFinset s I).restrict path) := by
  funext t
  rfl

end DenseTimePath
end
end MarkovProcess

end PortComputability
