/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H10Graph

/-! # Potential Solenoidal L2Realization -/

namespace Homogenization

/-!
# Closed-range realization for the canonical zero-trace potential subspace

This file closes the last abstract hypothesis used by the note-facing coarse
Poincare theorem surface. The proof combines:

* the representative upgrade `exists_h10Function_of_mem_h10GraphClosedSubmodule`
  from `Foundations/H10Graph.lean`, which shows every point of the closed
  `H¹₀` graph is realized by an honest `H¹₀` function, and
* the closed-range gradient projection
  `H10GraphClosed.isClosed_range_gradientCLM`.

Together they discharge `HasPotentialZeroTraceClosureRealization U` on every
bounded open convex domain.
-/

namespace PotentialSolenoidalL2Data

variable {d : ℕ} [NeZero d] {U : Set (Vec d)}
/-- Every generator of the predicate `L²` zero-trace potential submodule
transports under `vectorL2ToHilbertVectorL2` to an element in the range of
the gradient projection from the closed `H¹₀` graph. -/
private theorem vectorL2ToHilbertVectorL2_mem_range_gradientCLM_of_mem_potentialZeroTraceSubmodule
    {F : VectorL2 U} (hF : F ∈ potentialZeroTraceSubmodule U) :
    vectorL2ToHilbertVectorL2 (U := U) F ∈
      Set.range (H10GraphClosed.gradientCLM (d := d) (U := U)) := by
  rcases hF with ⟨f, hf, hFeq, hpot⟩
  obtain ⟨u, hu⟩ := hpot
  have hpair_open :
      (u.toH1Function.toScalarL2, u.toH1Function.gradToHilbertVectorL2) ∈
        h10GraphSubmodule U :=
    h10_pair_mem_h10GraphSubmodule u
  have hpair :
      (u.toH1Function.toScalarL2, u.toH1Function.gradToHilbertVectorL2) ∈
        (h10GraphClosedSubmodule U).toSubmodule :=
    (Submodule.le_topologicalClosure _) hpair_open
  refine ⟨⟨(u.toH1Function.toScalarL2, u.toH1Function.gradToHilbertVectorL2),
    hpair⟩, ?_⟩
  have hHilbertEq :
      toHilbertVectorL2OfVecField hf = u.toH1Function.gradToHilbertVectorL2 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [coeFn_toHilbertVectorL2OfVecField (U := U) hf,
      u.toH1Function.coeFn_gradToHilbertVectorL2] with x hhf hhu
    rw [hhf, hhu]
    simp [hilbertifyVecField, ← hu]
  show H10GraphClosed.gradientCLM (d := d) (U := U) _ =
    vectorL2ToHilbertVectorL2 (U := U) F
  have hFhilbert :
      vectorL2ToHilbertVectorL2 (U := U) F = u.toH1Function.gradToHilbertVectorL2 := by
    rw [← hFeq, vectorL2ToHilbertVectorL2_toVectorL2]
    exact hHilbertEq
  rw [hFhilbert]
  rfl

/-- Main realization theorem: on bounded open convex domains, every member
of the canonical closed zero-trace potential subspace is the gradient of an
actual `H¹₀` function. -/
theorem hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) :
    HasPotentialZeroTraceClosureRealization U := by
  intro F hF
  -- Step 1: Unfold membership to a closure statement in the ambient set.
  have hF_closure :
      F ∈ closure ((potentialZeroTraceSubmodule U : Submodule ℝ (VectorL2 U)) :
        Set (VectorL2 U)) := by
    have hFSub : F ∈ (potentialZeroTraceSubmodule U).topologicalClosure := hF
    simpa [Submodule.topologicalClosure_coe] using! hFSub
  -- Step 2: Package the range of `gradientCLM` as a closed set, and use
  -- continuity of `vectorL2ToHilbertVectorL2` to push the closure through.
  let S : Set (HilbertVectorL2 U) :=
    Set.range (H10GraphClosed.gradientCLM (d := d) (U := U))
  have hS_closed : IsClosed S :=
    H10GraphClosed.isClosed_range_gradientCLM (U := U) hU
  have hpre_closed :
      IsClosed
        ((vectorL2ToHilbertVectorL2 (U := U)) ⁻¹' S) :=
    hS_closed.preimage (vectorL2ToHilbertVectorL2 (U := U)).continuous
  have hsub :
      ((potentialZeroTraceSubmodule U : Submodule ℝ (VectorL2 U)) :
        Set (VectorL2 U)) ⊆
        (vectorL2ToHilbertVectorL2 (U := U)) ⁻¹' S := by
    intro F' hF'
    exact
      vectorL2ToHilbertVectorL2_mem_range_gradientCLM_of_mem_potentialZeroTraceSubmodule hF'
  have hFinRange :
      vectorL2ToHilbertVectorL2 (U := U) F ∈ S := by
    have : F ∈ (vectorL2ToHilbertVectorL2 (U := U)) ⁻¹' S :=
      (closure_minimal hsub hpre_closed) hF_closure
    exact this
  rcases hFinRange with ⟨z, hz⟩
  -- Step 3: Upgrade `z : H10GraphClosedSpace U` to an honest `H¹₀` function.
  rcases exists_h10Function_of_mem_h10GraphClosedSubmodule (U := U) hU z.2
    with ⟨u, hu_val, hu_grad⟩
  -- Step 4: Transport back to `VectorL2 U` and identify `u.toH1Function.grad` with `F`.
  have hgrad_eq :
      vectorL2ToHilbertVectorL2 (U := U) F = u.toH1Function.gradToHilbertVectorL2 := by
    -- z.2 := gradient z in the closed graph, matches `gradientCLM z = vectorL2ToHilbertVectorL2 F`.
    have : H10GraphClosed.gradientCLM (d := d) (U := U) z =
        u.toH1Function.gradToHilbertVectorL2 := by
      -- gradientCLM z = (z : ScalarL2 × HilbertVectorL2).snd = z.1.2 = z.2
      -- But here z : H10GraphClosedSpace; we only know u.gradToHilbertVectorL2 = z.1.2
      -- via hu_grad. We need: gradientCLM z = z.1.2.
      have := hu_grad
      -- gradientCLM z = z.1.2 by definition
      simp [H10GraphClosed.gradientCLM]
      exact this.symm
    rw [← this, hz]
  have hF_back :
      F = u.toH1Function.gradToVectorL2 := by
    have hinv := hilbertVectorL2ToVectorL2_vectorL2ToHilbertVectorL2 (U := U) F
    have happly :
        hilbertVectorL2ToVectorL2 (U := U) u.toH1Function.gradToHilbertVectorL2
          = u.toH1Function.gradToVectorL2 := by
      simp [H1Function.gradToVectorL2, H1Function.gradToHilbertVectorL2,
        hilbertVectorL2ToVectorL2_toHilbertVectorL2]
    calc
      F = hilbertVectorL2ToVectorL2 (U := U)
            (vectorL2ToHilbertVectorL2 (U := U) F) := hinv.symm
      _ = hilbertVectorL2ToVectorL2 (U := U)
            u.toH1Function.gradToHilbertVectorL2 := by rw [hgrad_eq]
      _ = u.toH1Function.gradToVectorL2 := happly
  -- Step 5: a.e. equality → `IsPotentialZeroTraceOn` via `congr_ae`.
  have hae : u.toH1Function.grad =ᵐ[MeasureTheory.volume.restrict U] ⇑F := by
    have h1 : (⇑u.toH1Function.gradToVectorL2 : Vec d → Vec d)
        =ᵐ[volumeMeasureOn U] u.toH1Function.grad :=
      u.toH1Function.coeFn_gradToVectorL2
    have h2 :
        (⇑u.toH1Function.gradToVectorL2 : Vec d → Vec d)
          =ᵐ[volumeMeasureOn U] (⇑F : Vec d → Vec d) := by
      rw [hF_back]
    -- Combine h1 (symmetric) and h2.
    have hcombine :
        (u.toH1Function.grad : Vec d → Vec d)
          =ᵐ[volumeMeasureOn U] (⇑F : Vec d → Vec d) :=
      (h1.symm).trans h2
    exact hcombine
  exact IsPotentialZeroTraceOn.congr_ae hae ⟨u, rfl⟩

end PotentialSolenoidalL2Data

end Homogenization
