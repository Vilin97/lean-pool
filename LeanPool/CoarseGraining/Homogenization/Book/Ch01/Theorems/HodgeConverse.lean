/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Hodge

/-! # Hodge Converse -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

/-- Public a.e.-based Hodge converse on bounded open convex domains.

This avoids exposing the internal representative-equality predicate as the
Chapter 1 public surface. -/
theorem potentialField_of_orthogonal_to_solenoidalZeroNormalTrace_boundedOpenConvex
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f)
    (horth :
      ∀ {g : Vec d → Vec d}, MemVectorL2 U g →
        SolenoidalZeroNormalTraceFieldOn U g →
          ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume = 0) :
    PotentialFieldOn U f := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isFiniteMeasure_restrict_volume
  have hcriterion : Homogenization.HodgeConverseCriterion U :=
    Homogenization.hodgeConverseCriterion_of_isOpenBoundedConvexDomain hU
  have horth_internal :
      ∀ {g : Vec d → Vec d}, MemVectorL2 U g →
        Homogenization.IsSolenoidalZeroNormalTraceOn U g →
          ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume = 0 := by
    intro g hg hsol
    exact horth hg ⟨hg, hsol⟩
  rcases hcriterion hf horth_internal with ⟨u, hgrad⟩
  refine ⟨hf, u, ?_⟩
  exact Filter.EventuallyEq.of_eq hgrad.symm

end

end Ch01
end Book
end Homogenization
