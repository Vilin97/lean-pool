/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerEndpoint

@[expose] public section

/-! The maximal positive horizon of a fixed ordinary Euler datum.
Existence below the supremum and failure above it follow from restriction;
membership of the endpoint is deliberately left to a continuation theorem. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field

def HasEulerEvolution (A : SmoothL2Field Space) (T : ℝ) : Prop :=
  ∃ hT : 0 < T, ∃ U : Evolution T hT.le, U.velocity ⟨0,le_rfl,hT.le⟩=A

theorem HasEulerEvolution.restrict {A : SmoothL2Field Space} {T : ℝ}
    (h : HasEulerEvolution A T) (S : ℝ) (hS : 0 < S) (hST : S ≤ T) :
    HasEulerEvolution A S := by
  obtain ⟨hT,U,hU⟩ := h
  exact ⟨hS,U.restrictTime S hS.le hST,hU⟩

theorem HasEulerEvolution.lt_of_failure {A : SmoothL2Field Space} {T B : ℝ}
    (h : HasEulerEvolution A T) (hB : 0 < B) (hfail : ¬ HasEulerEvolution A B) : T < B := by
  by_contra hn
  exact hfail (h.restrict B hB (le_of_not_gt hn))

/-- A compatible family of smooth solutions on every strictly shorter
positive interval, with no solution on any longer interval. -/
structure FiniteLifespan (A : SmoothL2Field Space) where
  duration : ℝ
  duration_pos : 0 < duration
  shorter : ∀ S, 0 < S → S < duration → HasEulerEvolution A S
  maximal : ∀ S, duration < S → ¬ HasEulerEvolution A S

theorem exists_finite_lifespan (A : SmoothL2Field Space) (B : ℝ) (hB : 0 < B)
    (hlocal : ∃ T, HasEulerEvolution A T) (hfail : ¬ HasEulerEvolution A B) :
    ∃ L : FiniteLifespan A, L.duration ≤ B := by
  let times : Set ℝ := {T | HasEulerEvolution A T}
  have hne : times.Nonempty := hlocal
  have hbound : ∀ T ∈ times, T ≤ B := fun T hT => (hT.lt_of_failure hB hfail).le
  have hbdd : BddAbove times := ⟨B,hbound⟩
  have hpos : 0 < sSup times := by
    obtain ⟨T,hT⟩ := hlocal
    exact hT.choose.trans_le (le_csSup hbdd hT)
  refine ⟨{
    duration := sSup times
    duration_pos := hpos
    shorter := ?_
    maximal := ?_ },csSup_le hne hbound⟩
  · intro S hS hST
    obtain ⟨T,hT,hST'⟩ := exists_lt_of_lt_csSup hne hST
    exact hT.restrict S hS hST'.le
  · intro S hST hS
    exact (not_le_of_gt hST) (le_csSup hbdd hS)

namespace FiniteLifespan

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

def evolution (S : ℝ) (hS : 0 < S) (hST : S < L.duration) : Evolution S hS.le :=
  (L.shorter S hS hST).choose_spec.choose

theorem evolution_initial (S : ℝ) (hS : 0 < S) (hST : S < L.duration) :
    (L.evolution S hS hST).velocity ⟨0,le_rfl,hS.le⟩=A :=
  (L.shorter S hS hST).choose_spec.choose_spec

theorem evolution_agrees (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (hSL : S < L.duration) (hTL : T < L.duration) (hST : S ≤ T)
    (t : Icc (0 : ℝ) S) :
    (L.evolution T hT hTL).velocity ⟨t,t.property.1,t.property.2.trans hST⟩=
        (L.evolution S hS hSL).velocity t ∧
      (L.evolution T hT hTL).pressureForce ⟨t,t.property.1,t.property.2.trans hST⟩=
        (L.evolution S hS hSL).pressureForce t :=
  endpoint_matches_partial (L.evolution T hT hTL) A (L.evolution_initial T hT hTL)
    S hS hST (L.evolution S hS hSL) (L.evolution_initial S hS hSL) t

theorem endpoint_of_bounded_gradient (G : ℝ)
    (hG : ∀ S (hS : 0 < S) (hST : S < L.duration) t,
      (L.evolution S hS hST).gradientIntegral t ≤ G) : HasEulerEvolution A L.duration := by
  refine ⟨L.duration_pos,?_⟩
  apply exists_smooth_endpoint L.duration L.duration_pos A G
  intro S hS hST
  exact ⟨L.evolution S hS hST,L.evolution_initial S hS hST,hG S hS hST⟩

end FiniteLifespan
end EulerOrdinarySobolev
