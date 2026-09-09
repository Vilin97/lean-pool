/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedResidual
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownGrade

@[expose] public section

/-!
The well-founded profile recursion in (14), on literal time/space/angle fields.
Every new mean is computed before the new high coefficient.  The supplied
linear inverse maps are the interface to the analytic source constructions;
this file proves the recursion and its dependence only on earlier grades.
-/

noncomputable section

namespace EulerPacketProfileRecursion

open EulerSmoothLimit EulerPacketPointJets Set

abbrev VectorField := Domain → Space
abbrev ScalarField := Domain → ℝ

structure Profile where
  high : VectorField
  mean : VectorField
  corrector : VectorField
  highPressure : ScalarField
  meanPressure : ScalarField

instance : Zero Profile := ⟨⟨0,0,0,0,0⟩⟩

structure Operators where
  interval : Set ℝ
  period : ℝ
  inverseFrame : Domain → Space →L[ℝ] Space
  strain : Domain → Space →L[ℝ] Space
  normal : VectorField
  meanSolve : VectorField → VectorField × ScalarField
  highSolve : VectorField → VectorField × ScalarField
  curlCorrector : VectorField → VectorField

/-- Literal angular averaging at each time and spatial label. -/
def angleMean (P : ℝ) (f : VectorField) : VectorField :=
  fun z => P⁻¹ • ∫ θ in 0..P, f (z.1,(z.2.1,θ))

/-- The stored coefficients determine the jets of V_i=A_i+B_i+C_{i-1}. -/
def velocityJet (s : Set ℝ) (a : ℕ → Profile) (z : Domain) (i : ℕ) : VectorJet :=
  if i=0 then 0 else slicedJet s (a i).high z+slicedJet s (a i).mean z+
    slicedJet s (a (i-1)).corrector z

def knownJets (O : Operators) (p : ℕ) (a : ℕ → Profile) (z : Domain) : ℕ → VectorJet :=
  history p (velocityJet O.interval a z) (slicedJet O.interval (a (p-1)).corrector z)

/-- All terms of the grade-p forcing that are already determined. -/
def knownForce (O : Operators) (p : ℕ) (a : ℕ → Profile) : VectorField :=
  fun z => -(linearPart (O.strain z) (slicedJet O.interval (a (p-1)).corrector z)+
    slowPressure (O.inverseFrame z) (pressureJet (a (p-1)).highPressure z)+
    nonlinearGrade (p+1) p (O.inverseFrame z) (O.normal z) (knownJets O p a z))

def meanForce (O : Operators) (p : ℕ) (a : ℕ → Profile) : VectorField :=
  angleMean O.period (knownForce O p a)

def meanResult (O : Operators) (p : ℕ) (a : ℕ → Profile) : VectorField × ScalarField :=
  O.meanSolve (meanForce O p a)

/-- The sole new mean-primary interaction is added after solving the mean. -/
def highForce (O : Operators) (p : ℕ) (a : ℕ → Profile) : VectorField :=
  fun z => knownForce O p a z-meanForce O p a z-
    fastAdvection (O.normal z) (slicedJet O.interval (meanResult O p a).1 z)
      (slicedJet O.interval (a 1).high z)

def step (O : Operators) (p : ℕ) (a : ℕ → Profile) : Profile :=
  let b := meanResult O p a
  let h := O.highSolve (highForce O p a)
  ⟨h.1,b.1,O.curlCorrector h.1,h.2,b.2⟩

theorem velocityJet_congr (s : Set ℝ) (p : ℕ) (a b : ℕ → Profile)
    (h : ∀ i<p, a i=b i) (z : Domain) (i : ℕ) (hi : i<p) :
    velocityJet s a z i=velocityJet s b z i := by
  by_cases hz : i=0
  · simp only [velocityJet, hz, ite_true]
  · simp only [velocityJet, hz, ite_false, h i hi, h (i-1) (by omega)]

theorem knownJets_congr (O : Operators) (p : ℕ) (hp : 1 ≤ p) (a b : ℕ → Profile)
    (h : ∀ i<p, a i=b i) (z : Domain) : knownJets O p a z=knownJets O p b z := by
  unfold knownJets
  rw [h (p-1) (by omega)]
  exact history_congr p _ _ _ (fun i hi => velocityJet_congr O.interval p a b h z i hi)

theorem knownForce_congr (O : Operators) (p : ℕ) (hp : 1 ≤ p) (a b : ℕ → Profile)
    (h : ∀ i<p, a i=b i) : knownForce O p a=knownForce O p b := by
  funext z
  unfold knownForce
  rw [h (p-1) (by omega), knownJets_congr O p hp a b h z]

/-- At p≥2 the complete new profile depends only on the strict prefix. -/
theorem step_congr (O : Operators) (p : ℕ) (hp : 2 ≤ p) (a b : ℕ → Profile)
    (h : ∀ i<p, a i=b i) : step O p a=step O p b := by
  have hf := knownForce_congr O p (by omega) a b h
  have h₁ := h 1 (by omega)
  have hh : highForce O p a=highForce O p b := by
    funext z
    simp only [highForce, meanResult, meanForce, hf, h₁]
  simp only [step, meanResult, meanForce, hf, hh]

def recursionStep (O : Operators) (primary : Profile) (p : ℕ)
    (a : (i : ℕ) → i<p → Profile) : Profile :=
  if p=0 then 0 else if p=1 then primary else
    step O p (fun i => if hi : i<p then a i hi else 0)

/-- All finite profile families are restrictions of this one well-founded sequence. -/
def profiles (O : Operators) (primary : Profile) : ℕ → Profile :=
  Nat.strongRec (recursionStep O primary)

theorem profiles_unfold (O : Operators) (primary : Profile) (p : ℕ) :
    profiles O primary p=recursionStep O primary p (fun i _ => profiles O primary i) :=
  Nat.strongRec_eq (recursionStep O primary) p

@[simp] theorem profiles_zero (O : Operators) (primary : Profile) : profiles O primary 0=0 := by
  rw [profiles_unfold]
  simp only [recursionStep, ite_true]

@[simp] theorem profiles_one (O : Operators) (primary : Profile) : profiles O primary 1=primary :=
  by
  rw [profiles_unfold]
  simp only [recursionStep, one_ne_zero, ite_false, ite_true]

/-- This is an actual recursive construction, not an existence assumption on profiles. -/
theorem profiles_step (O : Operators) (primary : Profile) (p : ℕ) (hp : 2 ≤ p) :
    profiles O primary p=step O p (profiles O primary) := by
  rw [profiles_unfold]
  simp only [recursionStep, show p ≠ 0 by omega, show p ≠ 1 by omega, ite_false]
  apply step_congr O p hp
  intro i hi
  simp only [dite_eq_left hi]

theorem profiles_mean (O : Operators) (primary : Profile) (p : ℕ) (hp : 2 ≤ p) :
    (profiles O primary p).mean=(meanResult O p (profiles O primary)).1 := by
  rw [profiles_step O primary p hp]
  rfl

theorem profiles_high (O : Operators) (primary : Profile) (p : ℕ) (hp : 2 ≤ p) :
    (profiles O primary p).high=(O.highSolve (highForce O p (profiles O primary))).1 := by
  rw [profiles_step O primary p hp]
  rfl

theorem profiles_corrector (O : Operators) (primary : Profile) (p : ℕ) (hp : 2 ≤ p) :
    (profiles O primary p).corrector=O.curlCorrector (profiles O primary p).high := by
  rw [profiles_step O primary p hp]
  rfl

end EulerPacketProfileRecursion
