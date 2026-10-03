/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Operators
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.GoodSet
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LineSecondOrder
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Assembly from directional quadratic estimates

This file specializes the project estimate-assembly lemmas to Hessian candidates reconstructed
from finitely many directional coefficients. It is a small bridge between future slicing data and
the existing `SecondOrderDifferentiableAEOn` interface.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pointwise local quadratic estimate data whose Hessian candidate is assembled from a finite
matrix of directional coefficients. -/
def MixedDirectionalQuadraticEstimateAt {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ a : ι → ι → ℝ,
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder u x p (x + z) -
            (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ ≤
          ε * ‖z‖ ^ 2

/-- Punctured normalized quotient version of `MixedDirectionalQuadraticEstimateAt`. -/
def MixedDirectionalQuadraticQuotientEstimateAt {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ a : ι → ι → ℝ,
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z) -
            (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ /
            ‖z‖ ^ 2 ≤ ε

/-- Pointwise local quadratic estimate data whose Hessian candidate is assembled from pure
directional coefficients `q i` and pairwise-sum coefficients `r i j` by polarization. This is a
closer target for the later finite slicing reconstruction than an arbitrary coefficient matrix. -/
def PolarizedMixedDirectionalQuadraticEstimateAt {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (v : ι → E) (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder u x p (x + z) -
            (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ ≤
          ε * ‖z‖ ^ 2

/-- Punctured normalized quotient version of
`PolarizedMixedDirectionalQuadraticEstimateAt`. -/
def PolarizedMixedDirectionalQuadraticQuotientEstimateAt {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (v : ι → E) (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z) -
            (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ /
            ‖z‖ ^ 2 ≤ ε

/-- Pointwise finite slicing target: scalar quadratic estimate data holds for the line
restriction in each selected direction and each pairwise sum direction. This is the finite
direction list needed by polarization-based Hessian reconstruction. -/
def DirectionalSliceEstimateAt {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) (x : E) : Prop :=
  (∀ ⦃i : ι⦄, i ∈ D →
    RealScalarQuadraticEstimateAt (lineRestriction u x (v i)) 0) ∧
  (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
    RealScalarQuadraticEstimateAt (lineRestriction u x (v i + v j)) 0)

/-- Finite slicing target with compatible first-order data: all selected line estimates use
the directional slopes coming from one ambient vector `p`. The coefficients `q` and `r` are the
pure and pairwise-sum quadratic coefficients used by the polarization reconstruction. -/
def CompatibleDirectionalSliceEstimateAt {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
    (∀ ⦃i : ι⦄, i ∈ D →
      RealScalarQuadraticEstimateWithDataAt (lineRestriction u x (v i)) 0
        (inner ℝ p (v i)) (q i)) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      RealScalarQuadraticEstimateWithDataAt (lineRestriction u x (v i + v j)) 0
        (inner ℝ p (v i + v j)) (r i j))

/-- Compatible finite slicing data with pairwise-sum coefficients symmetric on the selected
finite direction set. This is the coefficient shape expected by the polarized reconstruction
algebra. -/
def SymmetricCompatibleDirectionalSliceEstimateAt {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
    (∀ ⦃i : ι⦄, i ∈ D →
      RealScalarQuadraticEstimateWithDataAt (lineRestriction u x (v i)) 0
        (inner ℝ p (v i)) (q i)) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      RealScalarQuadraticEstimateWithDataAt (lineRestriction u x (v i + v j)) 0
        (inner ℝ p (v i + v j)) (r i j))

/-- Punctured normalized quotient version of `DirectionalSliceEstimateAt`. -/
def DirectionalSliceQuotientEstimateAt {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) (x : E) : Prop :=
  (∀ ⦃i : ι⦄, i ∈ D →
    RealScalarQuadraticQuotientEstimateAt (lineRestriction u x (v i)) 0) ∧
  (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
    RealScalarQuadraticQuotientEstimateAt (lineRestriction u x (v i + v j)) 0)

/-- Punctured normalized quotient version of `CompatibleDirectionalSliceEstimateAt`. -/
def CompatibleDirectionalSliceQuotientEstimateAt {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
    (∀ ⦃i : ι⦄, i ∈ D →
      RealScalarQuadraticQuotientEstimateWithDataAt (lineRestriction u x (v i)) 0
        (inner ℝ p (v i)) (q i)) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      RealScalarQuadraticQuotientEstimateWithDataAt (lineRestriction u x (v i + v j)) 0
        (inner ℝ p (v i + v j)) (r i j))

/-- Punctured normalized quotient version of
`SymmetricCompatibleDirectionalSliceEstimateAt`. -/
def SymmetricCompatibleDirectionalSliceQuotientEstimateAt {ι : Type*} (D : Finset ι)
    (v : ι → E) (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
    (∀ ⦃i : ι⦄, i ∈ D →
      RealScalarQuadraticQuotientEstimateWithDataAt (lineRestriction u x (v i)) 0
        (inner ℝ p (v i)) (q i)) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      RealScalarQuadraticQuotientEstimateWithDataAt (lineRestriction u x (v i + v j)) 0
        (inner ℝ p (v i + v j)) (r i j))

/-- Points carrying mixed-directional quadratic estimate data. -/
def mixedDirectionalQuadraticEstimateSet {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) : Set E :=
  {x | MixedDirectionalQuadraticEstimateAt D v u x}

/-- Points carrying punctured normalized mixed-directional quadratic estimate data. -/
def mixedDirectionalQuadraticQuotientEstimateSet {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) : Set E :=
  {x | MixedDirectionalQuadraticQuotientEstimateAt D v u x}

/-- Points carrying polarized mixed-directional quadratic estimate data. -/
def polarizedMixedDirectionalQuadraticEstimateSet {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (v : ι → E) (u : E → ℝ) : Set E :=
  {x | PolarizedMixedDirectionalQuadraticEstimateAt D v u x}

/-- Points carrying punctured normalized polarized mixed-directional quadratic estimate data. -/
def polarizedMixedDirectionalQuadraticQuotientEstimateSet {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (v : ι → E) (u : E → ℝ) : Set E :=
  {x | PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x}

/-- Points carrying scalar estimate data on the finite list of selected directions and their
pairwise sums. -/
def directionalSliceEstimateSet {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) : Set E :=
  {x | DirectionalSliceEstimateAt D v u x}

/-- Points carrying compatible scalar estimate data on the finite list of selected directions and
their pairwise sums. -/
def compatibleDirectionalSliceEstimateSet {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) : Set E :=
  {x | CompatibleDirectionalSliceEstimateAt D v u x}

/-- Points carrying symmetric compatible scalar estimate data on the finite list of selected
directions and their pairwise sums. -/
def symmetricCompatibleDirectionalSliceEstimateSet {ι : Type*} (D : Finset ι)
    (v : ι → E) (u : E → ℝ) : Set E :=
  {x | SymmetricCompatibleDirectionalSliceEstimateAt D v u x}

/-- Points carrying scalar quotient-estimate data on the finite list of selected directions and
their pairwise sums. -/
def directionalSliceQuotientEstimateSet {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) : Set E :=
  {x | DirectionalSliceQuotientEstimateAt D v u x}

/-- Points carrying compatible scalar quotient-estimate data on the finite list of selected
directions and their pairwise sums. -/
def compatibleDirectionalSliceQuotientEstimateSet {ι : Type*} (D : Finset ι) (v : ι → E)
    (u : E → ℝ) : Set E :=
  {x | CompatibleDirectionalSliceQuotientEstimateAt D v u x}

/-- Points carrying symmetric compatible scalar quotient-estimate data on the finite list of
selected directions and their pairwise sums. -/
def symmetricCompatibleDirectionalSliceQuotientEstimateSet {ι : Type*} (D : Finset ι)
    (v : ι → E) (u : E → ℝ) : Set E :=
  {x | SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x}

/-- Points where the line restriction in one fixed direction has scalar quadratic estimate data
at the base parameter. This is the single-direction output expected from the later Fubini step. -/
def directionalLineScalarEstimateSet (v : E) (u : E → ℝ) : Set E :=
  {x | RealScalarQuadraticEstimateAt (lineRestriction u x v) 0}

/-- Points where the line restriction in one fixed direction has punctured normalized scalar
quotient-estimate data at the base parameter. -/
def directionalLineScalarQuotientEstimateSet (v : E) (u : E → ℝ) : Set E :=
  {x | RealScalarQuadraticQuotientEstimateAt (lineRestriction u x v) 0}

@[simp]
theorem mem_mixedDirectionalQuadraticEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E} :
    x ∈ mixedDirectionalQuadraticEstimateSet D v u ↔
      MixedDirectionalQuadraticEstimateAt D v u x :=
  Iff.rfl

@[simp]
theorem mem_mixedDirectionalQuadraticQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E} :
    x ∈ mixedDirectionalQuadraticQuotientEstimateSet D v u ↔
      MixedDirectionalQuadraticQuotientEstimateAt D v u x :=
  Iff.rfl

@[simp]
theorem mem_polarizedMixedDirectionalQuadraticEstimateSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E} :
    x ∈ polarizedMixedDirectionalQuadraticEstimateSet D v u ↔
      PolarizedMixedDirectionalQuadraticEstimateAt D v u x :=
  Iff.rfl

@[simp]
theorem mem_polarizedMixedDirectionalQuadraticQuotientEstimateSet
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E} :
    x ∈ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u ↔
      PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x :=
  Iff.rfl

@[simp]
theorem mem_directionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E} :
    x ∈ directionalSliceEstimateSet D v u ↔ DirectionalSliceEstimateAt D v u x :=
  Iff.rfl

@[simp]
theorem mem_compatibleDirectionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E} :
    x ∈ compatibleDirectionalSliceEstimateSet D v u ↔
      CompatibleDirectionalSliceEstimateAt D v u x :=
  Iff.rfl

@[simp]
theorem mem_symmetricCompatibleDirectionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E} :
    x ∈ symmetricCompatibleDirectionalSliceEstimateSet D v u ↔
      SymmetricCompatibleDirectionalSliceEstimateAt D v u x :=
  Iff.rfl

@[simp]
theorem mem_directionalSliceQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E} :
    x ∈ directionalSliceQuotientEstimateSet D v u ↔
      DirectionalSliceQuotientEstimateAt D v u x :=
  Iff.rfl

@[simp]
theorem mem_compatibleDirectionalSliceQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E} :
    x ∈ compatibleDirectionalSliceQuotientEstimateSet D v u ↔
      CompatibleDirectionalSliceQuotientEstimateAt D v u x :=
  Iff.rfl

@[simp]
theorem mem_symmetricCompatibleDirectionalSliceQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E} :
    x ∈ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u ↔
      SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x :=
  Iff.rfl

@[simp]
theorem mem_directionalLineScalarEstimateSet
    {v : E} {u : E → ℝ} {x : E} :
    x ∈ directionalLineScalarEstimateSet v u ↔
      RealScalarQuadraticEstimateAt (lineRestriction u x v) 0 :=
  Iff.rfl

@[simp]
theorem mem_directionalLineScalarQuotientEstimateSet
    {v : E} {u : E → ℝ} {x : E} :
    x ∈ directionalLineScalarQuotientEstimateSet v u ↔
      RealScalarQuadraticQuotientEstimateAt (lineRestriction u x v) 0 :=
  Iff.rfl

end AleksandrovDifferentiability
