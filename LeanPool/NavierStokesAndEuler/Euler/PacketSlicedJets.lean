/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPointJets
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-!
Actual PDE jets on a closed time interval.  Time derivatives are within the
interval, while space and angle derivatives are ordinary Fréchet derivatives.
No smooth extension across a time endpoint is assumed.
-/

noncomputable section

namespace EulerPacketPointJets

open EulerSmoothLimit EulerFiniteGrades Finset Set

abbrev SpatialDomain := Space × ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def joinDerivative (v : E) (D : SpatialDomain →L[ℝ] E) : Domain →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ SpatialDomain).smulRight v+
    D.comp (ContinuousLinearMap.snd ℝ ℝ SpatialDomain)

theorem joinDerivative_apply (v : E) (D : SpatialDomain →L[ℝ] E) (h : Domain) :
    joinDerivative v D h=h.1 • v+D h.2 := rfl

def slicedJet (s : Set ℝ) (f : Domain → E) (z : Domain) : Jet E :=
  (f z, joinDerivative (derivWithin (fun t => f (t,z.2)) s z.1)
    (fderiv ℝ (fun y => f (z.1,y)) z.2))

theorem slicedJet_time (s : Set ℝ) (f : Domain → E) (z : Domain) :
    (slicedJet s f z).2 timeDirection=derivWithin (fun t => f (t,z.2)) s z.1 := by
  change (1 : ℝ) • derivWithin (fun t => f (t,z.2)) s z.1+
    (fderiv ℝ (fun y => f (z.1,y)) z.2) (0 : SpatialDomain)=_
  simp

theorem slicedJet_space (s : Set ℝ) (f : Domain → E) (z : Domain) (v : Space) :
    (slicedJet s f z).2 (spatialInjection v)=fderiv ℝ (fun y => f (z.1,y)) z.2 (v,0) := by
  simp [slicedJet, joinDerivative, spatialInjection]

theorem slicedJet_angle (s : Set ℝ) (f : Domain → E) (z : Domain) :
    (slicedJet s f z).2 angleDirection=fderiv ℝ (fun y => f (z.1,y)) z.2 (0,1) := by
  simp [slicedJet, joinDerivative, angleDirection]

/-- The time entry is the derivative furnished by the actual interval evolution. -/
theorem slicedJet_time_eq (s : Set ℝ) (f : Domain → E) (z : Domain) (v : E)
    (hs : UniqueDiffWithinAt ℝ s z.1) (ht : HasDerivWithinAt (fun t => f (t,z.2)) v s z.1) :
    (slicedJet s f z).2 timeDirection=v := by
  rw [slicedJet_time, ht.derivWithin hs]

theorem slicedJet_fieldSum (s : Set ℝ) (M : ℕ) (κ : ℝ) (u : ℕ → Domain → E) (z : Domain)
    (hs : UniqueDiffWithinAt ℝ s z.1)
    (ht : ∀ n ≤ M, DifferentiableWithinAt ℝ (fun t => u n (t,z.2)) s z.1)
    (hx : ∀ n ≤ M, DifferentiableAt ℝ (fun y => u n (z.1,y)) z.2) :
    slicedJet s (fieldSum M κ u) z=evaluate M κ (fun n => slicedJet s (u n) z) := by
  have htime := HasDerivWithinAt.fun_sum (u := range (M+1))
    (fun n hn => ((ht n (by have h := mem_range.mp hn; omega)).hasDerivWithinAt).const_smul (κ^n))
  have hspace := HasFDerivAt.fun_sum (u := range (M+1))
    (fun n hn => ((hx n (by have h := mem_range.mp hn; omega)).hasFDerivAt).const_smul (κ^n))
  have hdt : derivWithin (fun t => fieldSum M κ u (t,z.2)) s z.1=
      ∑ n ∈ range (M+1), κ^n • derivWithin (fun t => u n (t,z.2)) s z.1 := htime.derivWithin hs
  have hdx : fderiv ℝ (fun y => fieldSum M κ u (z.1,y)) z.2=
      ∑ n ∈ range (M+1), κ^n • fderiv ℝ (fun y => u n (z.1,y)) z.2 := hspace.fderiv
  apply Prod.ext
  · change (∑ n ∈ range (M+1), κ^n • u n z)=
      (AddMonoidHom.fst E (Domain →L[ℝ] E)) (∑ n ∈ range (M+1), κ^n • slicedJet s (u n) z)
    rw [map_sum]
    rfl
  · change joinDerivative _ _=
      (AddMonoidHom.snd E (Domain →L[ℝ] E)) (∑ n ∈ range (M+1), κ^n • slicedJet s (u n) z)
    rw [hdt, hdx, map_sum]
    change joinDerivative
      (∑ n ∈ range (M+1), κ^n • derivWithin (fun t => u n (t,z.2)) s z.1)
      (∑ n ∈ range (M+1), κ^n • fderiv ℝ (fun y => u n (z.1,y)) z.2)=
      ∑ n ∈ range (M+1), κ^n • joinDerivative
        (derivWithin (fun t => u n (t,z.2)) s z.1) (fderiv ℝ (fun y => u n (z.1,y)) z.2)
    apply ContinuousLinearMap.ext
    intro h
    simp only [joinDerivative_apply, Finset.smul_sum, _root_.sum_apply,
      smul_apply, smul_smul, sum_add_distrib, smul_add]
    congr 1
    apply sum_congr rfl
    intro n _
    rw [mul_comm]

end EulerPacketPointJets
