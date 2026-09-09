/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTimeFreeze
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveCancellation

/-! The literal initial packet is the sum of its oscillating high part
and its angle-independent mean part. Every field below is realized by
the already constructed continuous cylinder L² paths. -/

@[expose] public section


noncomputable section


namespace EulerPacketInitial

open Set Finset EulerSmoothLimit EulerPacketProfileRecursion EulerPacketPointJets
  EulerPacketCylinderField EulerFiniteGrades

/-- Time slice, defined pointwise by `f (t,z.2)`. -/
def timeSlice (t : ℝ) (f : VectorField) : VectorField := fun z => f (t,z.2)

/-- High grade, given by `assemble N (fun i => timeSlice t (a i).high) (fun i => timeSlice t (a
i).corrector)`. -/
def highGrade (N : ℕ) (t : ℝ) (a : ℕ → Profile) : ℕ → VectorField :=
  assemble N (fun i => timeSlice t (a i).high) (fun i => timeSlice t (a i).corrector)

/-- Mean grade, given by `truncate N (fun i => timeSlice t (a i).mean)`. -/
def meanGrade (N : ℕ) (t : ℝ) (a : ℕ → Profile) : ℕ → VectorField :=
  truncate N (fun i => timeSlice t (a i).mean)

/-- High, given by `fieldSum (N+1) κ (highGrade N t a)`. -/
def high (N : ℕ) (κ t : ℝ) (a : ℕ → Profile) : VectorField :=
  fieldSum (N+1) κ (highGrade N t a)

/-- Mean, given by `fieldSum (N+1) κ (meanGrade N t a)`. -/
def mean (N : ℕ) (κ t : ℝ) (a : ℕ → Profile) : VectorField :=
  fieldSum (N+1) κ (meanGrade N t a)

theorem high_eq (N : ℕ) (κ t : ℝ) (a : ℕ → Profile) :
    high N κ t a = fieldSum N κ (fun i => timeSlice t (a i).high) +
      κ • fieldSum N κ (fun i => timeSlice t (a i).corrector) := by
  funext z
  have h := congrFun (evaluate_assemble N κ (fun i => timeSlice t (a i).high)
    (fun i => timeSlice t (a i).corrector)) z
  simpa only [high,highGrade,fieldSum,evaluate,Finset.sum_apply,Pi.smul_apply,Pi.add_apply] using h

theorem mean_eq (N : ℕ) (κ t : ℝ) (a : ℕ → Profile) :
    mean N κ t a = fieldSum N κ (fun i => timeSlice t (a i).mean) := by
  funext z
  have h := congrFun (evaluate_truncate_extend N (N+1) (by omega) κ
    (fun i => timeSlice t (a i).mean)) z
  simpa only [mean,meanGrade,fieldSum,evaluate,Finset.sum_apply,Pi.smul_apply] using h

theorem packet_split (N : ℕ) (κ t : ℝ) (a : ℕ → Profile) :
    timeSlice t (fieldSum (N+1) κ (assembledVelocity N a)) =
      high N κ t a + mean N κ t a := by
  rw [high_eq,mean_eq]
  funext z
  have he := congrFun (evaluate_assemble N κ (fun i => (a i).high+(a i).mean)
    (fun i => (a i).corrector)) (t,z.2)
  simpa only [timeSlice,fieldSum,evaluate,assembledVelocity,Finset.sum_apply,Pi.add_apply,
    Pi.smul_apply,smul_add,sum_add_distrib,add_assoc,add_comm,add_left_comm] using he

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {N : ℕ}
  {a : ℕ → Profile} {support : Set Space}

/-- High grade field, given by `Field.assembleFamily N _ _ (fun i hi => (G i hi).high.freeze t)
(fun i hi => (G i hi).corrector.freeze t) n`. -/
def highGradeField (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (n : ℕ) : Field P T (highGrade N t a n) :=
  Field.assembleFamily N _ _ (fun i hi => (G i hi).high.freeze t)
    (fun i hi => (G i hi).corrector.freeze t) n

/-- Mean grade field, given by `Field.truncateFamily N _ (fun i hi => (G i hi).mean.freeze t)
n`. -/
def meanGradeField (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (n : ℕ) : Field P T (meanGrade N t a n) :=
  Field.truncateFamily N _ (fun i hi => (G i hi).mean.freeze t) n

/-- High field, given by `Field.evaluateFamily (N+1) κ _ (highGradeField G t)`. -/
def highField (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (κ : ℝ) : Field P T (high N κ t a) :=
  Field.evaluateFamily (N+1) κ _ (highGradeField G t)

/-- Mean field, given by `Field.evaluateFamily (N+1) κ _ (meanGradeField G t)`. -/
def meanField (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (κ : ℝ) : Field P T (mean N κ t a) :=
  Field.evaluateFamily (N+1) κ _ (meanGradeField G t)

theorem high_zero_outside (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (κ s : ℝ) (x : Space) (hx : x ∉ support) (θ : ℝ) :
    high N κ t a (s,(x,θ)) = 0 := by
  rw [high_eq]
  change (∑ i ∈ range (N+1), κ^i • (a i).high (t,(x,θ))) +
    κ • (∑ i ∈ range (N+1), κ^i • (a i).corrector (t,(x,θ))) = 0
  have hh : (∑ i ∈ range (N+1), κ^i • (a i).high (t,(x,θ))) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [(G i (by have := mem_range.mp hi; omega)).high_zero t x hx θ,smul_zero]
  have hc : (∑ i ∈ range (N+1), κ^i • (a i).corrector (t,(x,θ))) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [(G i (by have := mem_range.mp hi; omega)).corrector_zero t x hx θ,smul_zero]
  rw [hh,hc,smul_zero,add_zero]

theorem mean_angle (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (κ s : ℝ) (x : Space) (θ : ℝ) :
    mean N κ t a (s,(x,θ)) = mean N κ t a (s,(x,0)) := by
  rw [mean_eq]
  change (∑ i ∈ range (N+1), κ^i • (a i).mean (t,(x,θ))) =
    ∑ i ∈ range (N+1), κ^i • (a i).mean (t,(x,0))
  apply sum_congr rfl
  intro i hi
  rw [(G i (by have := mem_range.mp hi; omega)).mean_angle t x θ]

theorem mean_zero_outside (t : ℝ) (κ s : ℝ) (a : ℕ → Profile)
    (K : Set Space)
    (hmean : ∀ i, i ≤ N → ∀ x, x ∉ K → ∀ θ, (a i).mean (t, (x, θ)) = 0)
    (x : Space) (hx : x ∉ K) (θ : ℝ) :
    mean N κ t a (s,(x,θ)) = 0 := by
  rw [mean_eq]
  change (∑ i ∈ range (N+1), κ^i • (a i).mean (t,(x,θ))) = 0
  apply sum_eq_zero
  intro i hi
  rw [hmean i (by have := mem_range.mp hi; omega) x hx θ,smul_zero]

end EulerPacketInitial
