/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentCoefficientPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionPrimitiveBounds

@[expose] public section

/-! Composing the actual coefficient envelope with the parent label
polynomial gives a single fixed polynomial in the parent size K. -/

noncomputable section

namespace EulerParentCorrectionCost

open EulerParentCoefficientPolynomial EulerPacketCorrectionPrimitive EulerPolynomialCost

variable (P : ℝ) [Fact (0 < P)]

def parentEnvelope (K : ℝ) : ℝ :=
  1+leafEnvelope K+primitiveEnvelope P (leafEnvelope K)

def parentPolynomial : Polynomial ℝ :=
  1+leafPolynomial+(primitivePolynomial P).comp leafPolynomial

def parentConstant : ℝ := coefficientCost (parentPolynomial P)
def parentPower : ℕ := (parentPolynomial P).natDegree

theorem parentConstant_pos : 0 < parentConstant P := coefficientCost_pos _

theorem parentPolynomial_eval (K : ℝ) : (parentPolynomial P).eval K=parentEnvelope P K := by
  simp only [parentPolynomial,parentEnvelope,Polynomial.eval_add,Polynomial.eval_one,
    Polynomial.eval_comp,leafPolynomial_eval,primitivePolynomial_eval]

theorem parentEnvelope_power (K : ℝ) (hK : 1 ≤ K) :
    parentEnvelope P K ≤ parentConstant P*K^parentPower P := by
  rw [← parentPolynomial_eval]
  exact (le_abs_self _).trans (eval_bound (parentPolynomial P) K hK)

theorem parentEnvelope_bounds (K : ℝ) (hK : 0 ≤ K) :
    1 ≤ parentEnvelope P K ∧ leafEnvelope K ≤ parentEnvelope P K ∧
    primitiveEnvelope P (leafEnvelope K) ≤ parentEnvelope P K := by
  have hl := (leaf_bounds K hK).1
  have hp := (primitive_components P (leafEnvelope K) (zero_le_one.trans hl)).1
  unfold parentEnvelope
  exact ⟨by linarith,by linarith,by linarith⟩

end EulerParentCorrectionCost

namespace EulerPacketCylinderField.CoefficientBudget

open EulerParentCorrectionCost EulerParentCoefficientPolynomial

variable {P T : ℝ} [Fact (0 < P)] {O : EulerPacketProfileRecursion.Operators}
  {C : CoefficientData P T O} (B : CoefficientBudget C)

theorem parent_primitive_bound (K : ℝ) (hK : 0 ≤ K)
    (hR : B.Rc ≤ leafEnvelope K) (hC : B.amplitude ≤ leafEnvelope K) :
    B.multiplierCost ≤ parentEnvelope P K ∧ B.termCost ≤ parentEnvelope P K := by
  have h := B.primitive_bound (leafEnvelope K) (zero_le_one.trans (leaf_bounds K hK).1) hR hC
  have he := (parentEnvelope_bounds P K hK).2.2
  exact ⟨h.1.trans he,h.2.trans he⟩

end EulerPacketCylinderField.CoefficientBudget
