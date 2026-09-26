/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.StrongEntropy
public import LeanPool.BeyondBethe.BeyondBethe.ExplicitBounds
public import LeanPool.BeyondBethe.BeyondBethe.NumericalPotentials
public import Mathlib.Tactic

/-! # Approximate KKT -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# From objective accuracy to an approximate KKT certificate

The regularizer makes the objective strongly concave.  Consequently an
approximately optimal doubly stochastic matrix is close to an exact
maximizer.  On an explicitly truncated interior of the Birkhoff polytope the
logarithmic gradient is Lipschitz, so closeness of the matrices gives
closeness of their gradients.  Finally, anchored row and column potentials
turn that gradient estimate into the approximate logarithmic KKT equations
used by the permanent certificate.

The executable elementary-function oracle approximates the *negative*
gradient.  The last theorem below records the corresponding sign and the
additive constant `2 + tau` explicitly.
-/

/-- On a common floor `delta`, one coordinate of the regularized Bethe
gradient is `3 / delta`-Lipschitz when `0 <= tau <= 1`. -/
theorem regularizedBetheGradient_sub_abs_le
    {ι : Type*} {τ δ : ℝ} {A X Y : Matrix ι ι ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hδ : 0 < δ)
    (hXlo : ∀ i j, δ ≤ X i j) (hYlo : ∀ i j, δ ≤ Y i j)
    (hXcomp : ∀ i j, δ ≤ 1 - X i j)
    (hYcomp : ∀ i j, δ ≤ 1 - Y i j)
    (i j : ι) :
    abs (regularizedBetheGradient τ A X i j -
        regularizedBetheGradient τ A Y i j) ≤
      3 * abs (X i j - Y i j) / δ := by
  have hlog := abs_log_sub_log_le_div hδ (hXlo i j) (hYlo i j)
  have hcomplog := abs_log_sub_log_le_div hδ (hXcomp i j) (hYcomp i j)
  have hcoef0 : 0 ≤ 1 + τ := by linarith
  have hcoef2 : 1 + τ ≤ 2 := by linarith
  have hscaled :
      abs ((1 + τ) *
        (Real.log (X i j) - Real.log (Y i j))) ≤
          2 * (abs (X i j - Y i j) / δ) := by
    rw [abs_mul, abs_of_nonneg hcoef0]
    calc
      (1 + τ) * abs (Real.log (X i j) - Real.log (Y i j)) ≤
          (1 + τ) * (abs (X i j - Y i j) / δ) :=
        mul_le_mul_of_nonneg_left hlog hcoef0
      _ ≤ 2 * (abs (X i j - Y i j) / δ) :=
        mul_le_mul_of_nonneg_right hcoef2 (by positivity)
  have hcompdiff :
      abs ((1 - X i j) - (1 - Y i j)) = abs (X i j - Y i j) := by
    rw [show (1 - X i j) - (1 - Y i j) =
      -(X i j - Y i j) by ring, abs_neg]
  rw [hcompdiff] at hcomplog
  have htriangle := abs_add_le
    (-(1 + τ) * (Real.log (X i j) - Real.log (Y i j)))
    (-(Real.log (1 - X i j) - Real.log (1 - Y i j)))
  have hfirst :
      abs (-(1 + τ) * (Real.log (X i j) - Real.log (Y i j))) =
        abs ((1 + τ) * (Real.log (X i j) - Real.log (Y i j))) := by
    rw [show -(1 + τ) * (Real.log (X i j) - Real.log (Y i j)) =
      -((1 + τ) * (Real.log (X i j) - Real.log (Y i j))) by ring,
      abs_neg]
  have hid :
      regularizedBetheGradient τ A X i j -
          regularizedBetheGradient τ A Y i j =
        -(1 + τ) * (Real.log (X i j) - Real.log (Y i j)) +
          -(Real.log (1 - X i j) - Real.log (1 - Y i j)) := by
    simp only [regularizedBetheGradient]
    ring
  rw [hid]
  calc
    abs (_ + _) ≤
        abs ((1 + τ) *
          (Real.log (X i j) - Real.log (Y i j))) +
        abs (Real.log (1 - X i j) - Real.log (1 - Y i j)) := by
          simpa only [hfirst, abs_neg] using htriangle
    _ ≤ 2 * (abs (X i j - Y i j) / δ) +
        abs (X i j - Y i j) / δ := add_le_add hscaled hcomplog
    _ = 3 * abs (X i j - Y i j) / δ := by ring

/-- A single coordinate is bounded by the Frobenius norm.  This square-only
form avoids introducing square roots into the rational algorithm. -/
theorem abs_matrixCoordinate_le_of_sum_sq_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {D : Matrix ι κ ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsq : (∑ i, ∑ j, (D i j) ^ 2) ≤ ρ ^ 2)
    (a : ι) (b : κ) : abs (D a b) ≤ ρ := by
  have hcoord : (D a b) ^ 2 ≤ ∑ i, ∑ j, (D i j) ^ 2 := by
    calc
      (D a b) ^ 2 ≤ ∑ j, (D a j) ^ 2 :=
        Finset.single_le_sum (fun j _ ↦ sq_nonneg (D a j))
          (Finset.mem_univ b)
      _ ≤ ∑ i, ∑ j, (D i j) ^ 2 :=
        Finset.single_le_sum
          (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (D i j))
          (Finset.mem_univ a)
  have habs0 : 0 ≤ abs (D a b) := abs_nonneg _
  rw [← sq_abs] at hcoord
  nlinarith [hcoord.trans hsq]

/-- A sufficiently small objective gap forces entrywise proximity to an exact
regularized maximizer.  The arithmetic hypothesis `4 g <= tau rho^2` is
chosen so that every quantity can be selected rationally. -/
theorem regularizedBetheMaximizer_coordinate_close_of_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι)
    {τ g ρ : ℝ} (hτ : 0 < τ) (hρ : 0 ≤ ρ)
    (hscale : 4 * g ≤ τ * ρ ^ 2)
    {A X Y : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y)
    (hmax : ∀ Z, IsDoublyStochastic Z →
      regularizedBetheObjective τ A Z ≤
        regularizedBetheObjective τ A X)
    (hgap : regularizedBetheObjective τ A X -
        regularizedBetheObjective τ A Y ≤ g)
    (i j : ι) : abs (X i j - Y i j) ≤ ρ := by
  have hdist := regularizedBetheMaximizer_distance_sq_le_gap
    hcard hτ.le hX hY hmax
  have hsquares :
      (∑ i, ∑ j, (X i j - Y i j) ^ 2) ≤ ρ ^ 2 := by
    nlinarith
  exact abs_matrixCoordinate_le_of_sum_sq_le hρ hsquares i j

/-- Objective accuracy plus a common interior floor controls the model error
between the negative gradients at an approximate and an exact optimizer. -/
theorem negativeGradient_close_of_objective_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι)
    {τ g ρ δ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hscale : 4 * g ≤ τ * ρ ^ 2)
    {A X Y : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y)
    (hmax : ∀ Z, IsDoublyStochastic Z →
      regularizedBetheObjective τ A Z ≤
        regularizedBetheObjective τ A X)
    (hgap : regularizedBetheObjective τ A X -
        regularizedBetheObjective τ A Y ≤ g)
    (hXlo : ∀ i j, δ ≤ X i j) (hYlo : ∀ i j, δ ≤ Y i j)
    (hXcomp : ∀ i j, δ ≤ 1 - X i j)
    (hYcomp : ∀ i j, δ ≤ 1 - Y i j)
    (i j : ι) :
    abs (-regularizedBetheGradient τ A Y i j -
        -regularizedBetheGradient τ A X i j) ≤ 3 * ρ / δ := by
  have hcoord := regularizedBetheMaximizer_coordinate_close_of_gap
    hcard hτ hρ hscale hX hY hmax hgap i j
  have hcoord' : abs (Y i j - X i j) ≤ ρ := by
    simpa only [abs_sub_comm] using hcoord
  have hgrad := regularizedBetheGradient_sub_abs_le (A := A) hτ.le hτ1 hδ
    hYlo hXlo hYcomp hXcomp i j
  rw [show -regularizedBetheGradient τ A Y i j -
      -regularizedBetheGradient τ A X i j =
        -(regularizedBetheGradient τ A Y i j -
          regularizedBetheGradient τ A X i j) by ring, abs_neg]
  exact hgrad.trans (by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoord' (by norm_num)) hδ.le)

/-- The complete analytic bridge to the certificate interface.  `Gtilde` is
an executable approximation to the negative gradient at the returned point
`Y`.  Anchoring it produces explicit potentials; the signs and the derivative
constant are incorporated in the displayed output potentials. -/
theorem approximateLogKKT_of_objective_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : 1 < Fintype.card ι)
    {τ g ρ δ evaluationError : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hscale : 4 * g ≤ τ * ρ ^ 2)
    {A X Y Gtilde : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y)
    (hmax : ∀ Z, IsDoublyStochastic Z →
      regularizedBetheObjective τ A Z ≤
        regularizedBetheObjective τ A X)
    (hgap : regularizedBetheObjective τ A X -
        regularizedBetheObjective τ A Y ≤ g)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hXlo : ∀ i j, δ ≤ X i j) (hYlo : ∀ i j, δ ≤ Y i j)
    (hXcomp : ∀ i j, δ ≤ 1 - X i j)
    (hYcomp : ∀ i j, δ ≤ 1 - Y i j)
    (heval : ∀ i j,
      abs (-regularizedBetheGradient τ A Y i j - Gtilde i j) ≤
        evaluationError)
    (i0 j0 : ι) :
    HasApproximateLogKKT
      (evaluationError + 4 * (evaluationError + 3 * ρ / δ)) τ A Y
      (fun i ↦ -anchoredRowPotential Gtilde j0 i + (2 + τ))
      (fun j ↦ -anchoredColumnPotential Gtilde i0 j0 j) := by
  obtain ⟨R, C, hRC⟩ := exists_rowColumnPotentials_of_rectangle_identity
    (fun i j ↦ regularizedBetheGradient τ A X i j)
    (fun hik hjl ↦ regularizedGradient_rectangle_identity
      hX hXint hmax hik hjl)
  have hstar : ∀ i j,
      -regularizedBetheGradient τ A X i j = -R i + -C j := by
    intro i j
    rw [hRC i j]
    ring
  have hmodel : ∀ i j,
      abs (Gtilde i j - -regularizedBetheGradient τ A X i j) ≤
        evaluationError + 3 * ρ / δ := by
    intro i j
    have hclose := negativeGradient_close_of_objective_gap
      hcard hτ hτ1 hρ hδ hscale hX hY hmax hgap
      hXlo hYlo hXcomp hYcomp i j
    calc
      abs (Gtilde i j - -regularizedBetheGradient τ A X i j) =
          abs ((Gtilde i j - -regularizedBetheGradient τ A Y i j) +
            (-regularizedBetheGradient τ A Y i j -
              -regularizedBetheGradient τ A X i j)) := by congr 1 <;> ring
      _ ≤ abs (Gtilde i j - -regularizedBetheGradient τ A Y i j) +
          abs (-regularizedBetheGradient τ A Y i j -
            -regularizedBetheGradient τ A X i j) := abs_add_le _ _
      _ ≤ evaluationError + 3 * ρ / δ := by
        have heval' :
            abs (Gtilde i j - -regularizedBetheGradient τ A Y i j) ≤
              evaluationError := by
          simpa only [abs_sub_comm] using heval i j
        exact add_le_add heval' hclose
  intro i j
  have hres := anchoredPotentials_residual_of_evaluation
    hstar hmodel heval i0 j0 i j
  change abs (Real.log (A i j) -
    ((-anchoredRowPotential Gtilde j0 i + (2 + τ)) +
      -anchoredColumnPotential Gtilde i0 j0 j +
      (1 + τ) * Real.log (Y i j) + Real.log (1 - Y i j))) ≤ _
  have hid :
      Real.log (A i j) -
          ((-anchoredRowPotential Gtilde j0 i + (2 + τ)) +
            -anchoredColumnPotential Gtilde i0 j0 j +
            (1 + τ) * Real.log (Y i j) + Real.log (1 - Y i j)) =
        -(-regularizedBetheGradient τ A Y i j -
          (anchoredRowPotential Gtilde j0 i +
            anchoredColumnPotential Gtilde i0 j0 j)) := by
    simp only [regularizedBetheGradient]
    ring
  rw [hid, abs_neg]
  exact hres

end BeyondBethe
