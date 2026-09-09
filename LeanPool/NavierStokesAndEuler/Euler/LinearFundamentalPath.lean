/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamel
import LeanPool.NavierStokesAndEuler.Euler.LinearFundamentalExistence
import Mathlib.Tactic.Positivity.Finset

/-!
# Actual continuous fundamental paths from the existence theorem

This module chooses the paths whose existence was proved by Picard iteration
and records their initial values, two-sided inverse identities, and actual
within-interval derivatives. The final specialization constructs an Evolution
for every continuous bounded operator coefficient.
-/

@[expose] public section


noncomputable section

namespace EulerLinearFundamentalExistence

open Set ContinuousLinearMap EulerVolterraConvolution EulerLinearDuhamel

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  (T : ℝ) (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T, A))

/-- The continuous paths constructed from the actual Banach-space ODE. -/
structure FundamentalPath where
  /-- Forward of `FundamentalPath`, of type `C(Icc (0 : ℝ) T,A)`. -/
  forward : C(Icc (0 : ℝ) T,A)
  /-- Backward of `FundamentalPath`, of type `C(Icc (0 : ℝ) T,A)`. -/
  backward : C(Icc (0 : ℝ) T,A)
  forward_initial : forward ⟨0,le_rfl,hT⟩ = 1
  backward_initial : backward ⟨0,le_rfl,hT⟩ = 1
  forward_backward : ∀ t, forward t * backward t = 1
  backward_forward : ∀ t, backward t * forward t = 1
  derivative : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT forward) (B t * forward t) (Icc (0 : ℝ) T) t

/-- Every continuous coefficient has such actual paths, with no smallness hypothesis. -/
theorem nonempty_fundamentalPath : Nonempty (FundamentalPath T hT B) := by
  obtain ⟨Φ,Ψ,hΦ0,hΨ0,hΦ,hΨ,hInv⟩ := exists_fundamental T hT B
  let Φc : C(Icc (0 : ℝ) T,A) := ⟨fun t => Φ t,
    (show ContinuousOn Φ (Icc (0 : ℝ) T) from
      fun t ht => (hΦ t ht).continuousAt.continuousWithinAt).domRestrict⟩
  let Ψc : C(Icc (0 : ℝ) T,A) := ⟨fun t => Ψ t,
    (show ContinuousOn Ψ (Icc (0 : ℝ) T) from
      fun t ht => (hΨ t ht).continuousAt.continuousWithinAt).domRestrict⟩
  refine ⟨{
    forward := Φc
    backward := Ψc
    forward_initial := hΦ0
    backward_initial := hΨ0
    forward_backward := fun t => (hInv t t.property).1
    backward_forward := fun t => (hInv t t.property).2
    derivative := ?_ }⟩
  intro t
  have hd : HasDerivWithinAt Φ (B t * Φ t) (Icc (0 : ℝ) T) t := by
    simpa only [extendPath, projIcc_of_mem hT t.property] using
      (hΦ t t.property).hasDerivWithinAt (s := Icc (0 : ℝ) T)
  apply hd.congr_of_mem _ t.property
  intro s hs
  simp only [extendPath, projIcc_of_mem hT hs]
  rfl

/-- A fixed choice of the genuinely constructed fundamental paths. -/
def fundamentalPath : FundamentalPath T hT B :=
  Classical.choice (nonempty_fundamentalPath T hT B)

end EulerLinearFundamentalExistence

namespace EulerLinearDuhamel

open Set EulerLinearFundamentalExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T, E →L[ℝ] E))

/-- A homogeneous evolution constructed for an arbitrary continuous operator coefficient. -/
def constructedEvolution : Evolution T hT B where
  forward := (fundamentalPath T hT B).forward
  backward := (fundamentalPath T hT B).backward
  forward_backward := (fundamentalPath T hT B).forward_backward
  backward_forward := (fundamentalPath T hT B).backward_forward
  derivative := (fundamentalPath T hT B).derivative

/-- Its forward path starts at the identity. -/
theorem constructedEvolution_initial :
    (constructedEvolution T hT B).forward ⟨0,le_rfl,hT⟩ = ContinuousLinearMap.id ℝ E :=
  (fundamentalPath T hT B).forward_initial

end EulerLinearDuhamel
