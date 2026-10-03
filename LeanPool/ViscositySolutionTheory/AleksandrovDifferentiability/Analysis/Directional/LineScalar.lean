/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.EstimateDefs

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Scalar estimates along affine lines

This file records zero-direction cases and transport wrappers for scalar quadratic estimates on
line restrictions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every point is good for the zero-direction scalar estimate set. -/
theorem mem_directionalLineScalarEstimateSet_zero (u : E → ℝ) (x : E) :
    x ∈ directionalLineScalarEstimateSet (0 : E) u :=
  realScalarQuadraticEstimateAt_lineRestriction_zero_direction u x

/-- Every point is good for the zero-direction scalar quotient-estimate set. -/
theorem mem_directionalLineScalarQuotientEstimateSet_zero (u : E → ℝ) (x : E) :
    x ∈ directionalLineScalarQuotientEstimateSet (0 : E) u :=
  realScalarQuadraticQuotientEstimateAt_lineRestriction_zero_direction u x

@[simp]
theorem directionalLineScalarEstimateSet_zero (u : E → ℝ) :
    directionalLineScalarEstimateSet (0 : E) u = Set.univ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => mem_directionalLineScalarEstimateSet_zero u x⟩

@[simp]
theorem directionalLineScalarQuotientEstimateSet_zero (u : E → ℝ) :
    directionalLineScalarQuotientEstimateSet (0 : E) u = Set.univ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => mem_directionalLineScalarQuotientEstimateSet_zero u x⟩

/-- Affine ambient functions have scalar line-estimate data in every direction and at every
base point. -/
theorem mem_directionalLineScalarEstimateSet_inner_add_const
    (p v : E) (c : ℝ) (x : E) :
    x ∈ directionalLineScalarEstimateSet v (fun y : E => inner ℝ p y + c) := by
  have hfun :
      lineRestriction (fun y : E => inner ℝ p y + c) x v =
        fun t : ℝ => inner ℝ p v * t + (inner ℝ p x + c) := by
    funext t
    simp [lineRestriction, inner_add_right, real_inner_smul_right]
    ring
  simpa [directionalLineScalarEstimateSet, hfun] using
    realScalarQuadraticEstimateAt_affine (inner ℝ p v) (inner ℝ p x + c) 0

/-- Quotient-estimate version of
`mem_directionalLineScalarEstimateSet_inner_add_const`. -/
theorem mem_directionalLineScalarQuotientEstimateSet_inner_add_const
    (p v : E) (c : ℝ) (x : E) :
    x ∈ directionalLineScalarQuotientEstimateSet v (fun y : E => inner ℝ p y + c) := by
  have hfun :
      lineRestriction (fun y : E => inner ℝ p y + c) x v =
        fun t : ℝ => inner ℝ p v * t + (inner ℝ p x + c) := by
    funext t
    simp [lineRestriction, inner_add_right, real_inner_smul_right]
    ring
  simpa [directionalLineScalarQuotientEstimateSet, hfun] using
    realScalarQuadraticQuotientEstimateAt_affine (inner ℝ p v) (inner ℝ p x + c) 0

/-- Affine ambient functions have scalar line-estimate data with the ambient slope projected
onto the line direction and zero quadratic coefficient. -/
theorem realScalarQuadraticEstimateWithDataAt_lineRestriction_inner_add_const
    (p x v : E) (c : ℝ) :
    RealScalarQuadraticEstimateWithDataAt
      (lineRestriction (fun y : E => inner ℝ p y + c) x v) 0
        (inner ℝ p v) 0 := by
  have hfun :
      lineRestriction (fun y : E => inner ℝ p y + c) x v =
        fun t : ℝ => inner ℝ p v * t + (inner ℝ p x + c) := by
    funext t
    simp [lineRestriction, inner_add_right, real_inner_smul_right]
    ring
  simpa [hfun] using
    realScalarQuadraticEstimateWithDataAt_affine (inner ℝ p v) (inner ℝ p x + c) 0

/-- Quotient-estimate version of
`realScalarQuadraticEstimateWithDataAt_lineRestriction_inner_add_const`. -/
theorem realScalarQuadraticQuotientEstimateWithDataAt_lineRestriction_inner_add_const
    (p x v : E) (c : ℝ) :
    RealScalarQuadraticQuotientEstimateWithDataAt
      (lineRestriction (fun y : E => inner ℝ p y + c) x v) 0
        (inner ℝ p v) 0 := by
  exact
    RealScalarQuadraticEstimateWithDataAt.quadraticQuotientEstimateWithDataAt
      (realScalarQuadraticEstimateWithDataAt_lineRestriction_inner_add_const p x v c)

/-- For affine ambient functions, every point is good for every scalar directional-line
estimate. -/
theorem directionalLineScalarEstimateSet_inner_add_const (p v : E) (c : ℝ) :
    directionalLineScalarEstimateSet v (fun y : E => inner ℝ p y + c) = Set.univ := by
  ext x
  exact ⟨fun _ => trivial,
    fun _ => mem_directionalLineScalarEstimateSet_inner_add_const p v c x⟩

/-- Quotient-estimate version of `directionalLineScalarEstimateSet_inner_add_const`. -/
theorem directionalLineScalarQuotientEstimateSet_inner_add_const (p v : E) (c : ℝ) :
    directionalLineScalarQuotientEstimateSet v (fun y : E => inner ℝ p y + c) = Set.univ := by
  ext x
  exact ⟨fun _ => trivial,
    fun _ => mem_directionalLineScalarQuotientEstimateSet_inner_add_const p v c x⟩

/-- Affine ambient functions carry compatible finite slice data for every finite direction
list. The compatible ambient slope is the affine slope and all quadratic coefficients are zero. -/
theorem compatibleDirectionalSliceEstimateAt_inner_add_const
    {ι : Type*} (D : Finset ι) (v : ι → E) (p : E) (c : ℝ) (x : E) :
    CompatibleDirectionalSliceEstimateAt D v (fun y : E => inner ℝ p y + c) x := by
  refine ⟨p, (fun _ => 0), (fun _ _ => 0), ?_, ?_⟩
  · intro i _hi
    exact realScalarQuadraticEstimateWithDataAt_lineRestriction_inner_add_const p x (v i) c
  · intro i _hi j _hj
    exact
      realScalarQuadraticEstimateWithDataAt_lineRestriction_inner_add_const
        p x (v i + v j) c

/-- Symmetric compatible finite slice data for affine ambient functions. -/
theorem symmetricCompatibleDirectionalSliceEstimateAt_inner_add_const
    {ι : Type*} (D : Finset ι) (v : ι → E) (p : E) (c : ℝ) (x : E) :
    SymmetricCompatibleDirectionalSliceEstimateAt D v (fun y : E => inner ℝ p y + c) x := by
  refine ⟨p, (fun _ => 0), (fun _ _ => 0), ?_, ?_, ?_⟩
  · intro i _hi j _hj
    rfl
  · intro i _hi
    exact realScalarQuadraticEstimateWithDataAt_lineRestriction_inner_add_const p x (v i) c
  · intro i _hi j _hj
    exact
      realScalarQuadraticEstimateWithDataAt_lineRestriction_inner_add_const
        p x (v i + v j) c

/-- Quotient-estimate version of
`compatibleDirectionalSliceEstimateAt_inner_add_const`. -/
theorem compatibleDirectionalSliceQuotientEstimateAt_inner_add_const
    {ι : Type*} (D : Finset ι) (v : ι → E) (p : E) (c : ℝ) (x : E) :
    CompatibleDirectionalSliceQuotientEstimateAt D v
      (fun y : E => inner ℝ p y + c) x := by
  refine ⟨p, (fun _ => 0), (fun _ _ => 0), ?_, ?_⟩
  · intro i _hi
    exact
      realScalarQuadraticQuotientEstimateWithDataAt_lineRestriction_inner_add_const
        p x (v i) c
  · intro i _hi j _hj
    exact
      realScalarQuadraticQuotientEstimateWithDataAt_lineRestriction_inner_add_const
        p x (v i + v j) c

/-- Quotient-estimate version of
`symmetricCompatibleDirectionalSliceEstimateAt_inner_add_const`. -/
theorem symmetricCompatibleDirectionalSliceQuotientEstimateAt_inner_add_const
    {ι : Type*} (D : Finset ι) (v : ι → E) (p : E) (c : ℝ) (x : E) :
    SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v
      (fun y : E => inner ℝ p y + c) x := by
  refine ⟨p, (fun _ => 0), (fun _ _ => 0), ?_, ?_, ?_⟩
  · intro i _hi j _hj
    rfl
  · intro i _hi
    exact
      realScalarQuadraticQuotientEstimateWithDataAt_lineRestriction_inner_add_const
        p x (v i) c
  · intro i _hi j _hj
    exact
      realScalarQuadraticQuotientEstimateWithDataAt_lineRestriction_inner_add_const
        p x (v i + v j) c

/-- For affine ambient functions, every point carries compatible finite slice data. -/
theorem compatibleDirectionalSliceEstimateSet_inner_add_const
    {ι : Type*} (D : Finset ι) (v : ι → E) (p : E) (c : ℝ) :
    compatibleDirectionalSliceEstimateSet D v (fun y : E => inner ℝ p y + c) =
      Set.univ := by
  ext x
  exact ⟨fun _ => trivial,
    fun _ => compatibleDirectionalSliceEstimateAt_inner_add_const D v p c x⟩

/-- For affine ambient functions, every point carries symmetric compatible finite slice data. -/
theorem symmetricCompatibleDirectionalSliceEstimateSet_inner_add_const
    {ι : Type*} (D : Finset ι) (v : ι → E) (p : E) (c : ℝ) :
    symmetricCompatibleDirectionalSliceEstimateSet D v (fun y : E => inner ℝ p y + c) =
      Set.univ := by
  ext x
  exact ⟨fun _ => trivial,
    fun _ => symmetricCompatibleDirectionalSliceEstimateAt_inner_add_const D v p c x⟩

/-- Quotient-estimate version of
`compatibleDirectionalSliceEstimateSet_inner_add_const`. -/
theorem compatibleDirectionalSliceQuotientEstimateSet_inner_add_const
    {ι : Type*} (D : Finset ι) (v : ι → E) (p : E) (c : ℝ) :
    compatibleDirectionalSliceQuotientEstimateSet D v
      (fun y : E => inner ℝ p y + c) = Set.univ := by
  ext x
  exact ⟨fun _ => trivial,
    fun _ => compatibleDirectionalSliceQuotientEstimateAt_inner_add_const D v p c x⟩

/-- Quotient-estimate version of
`symmetricCompatibleDirectionalSliceEstimateSet_inner_add_const`. -/
theorem symmetricCompatibleDirectionalSliceQuotientEstimateSet_inner_add_const
    {ι : Type*} (D : Finset ι) (v : ι → E) (p : E) (c : ℝ) :
    symmetricCompatibleDirectionalSliceQuotientEstimateSet D v
      (fun y : E => inner ℝ p y + c) = Set.univ := by
  ext x
  exact ⟨fun _ => trivial,
    fun _ => symmetricCompatibleDirectionalSliceQuotientEstimateAt_inner_add_const D v p c x⟩

/-- Nonzero scalar rescaling of a direction does not change the scalar directional-line good set. -/
theorem directionalLineScalarEstimateSet_smul_eq
    {v : E} {c : ℝ} (hc : c ≠ 0) (u : E → ℝ) :
    directionalLineScalarEstimateSet (c • v) u = directionalLineScalarEstimateSet v u := by
  ext x
  exact RealScalarQuadraticEstimateAt.lineRestriction_smul_iff (u := u) (x := x) (v := v) hc

/-- Quotient-estimate version of `directionalLineScalarEstimateSet_smul_eq`. -/
theorem directionalLineScalarQuotientEstimateSet_smul_eq
    {v : E} {c : ℝ} (hc : c ≠ 0) (u : E → ℝ) :
    directionalLineScalarQuotientEstimateSet (c • v) u =
      directionalLineScalarQuotientEstimateSet v u := by
  ext x
  exact
    RealScalarQuadraticQuotientEstimateAt.lineRestriction_smul_iff (u := u) (x := x) (v := v) hc

@[simp]
theorem directionalLineScalarEstimateSet_neg (v : E) (u : E → ℝ) :
    directionalLineScalarEstimateSet (-v) u = directionalLineScalarEstimateSet v u := by
  simpa using
    (directionalLineScalarEstimateSet_smul_eq (v := v) (c := (-1 : ℝ)) (by norm_num) u)

@[simp]
theorem directionalLineScalarQuotientEstimateSet_neg (v : E) (u : E → ℝ) :
    directionalLineScalarQuotientEstimateSet (-v) u =
      directionalLineScalarQuotientEstimateSet v u := by
  simpa using
    (directionalLineScalarQuotientEstimateSet_smul_eq
      (v := v) (c := (-1 : ℝ)) (by norm_num) u)

/-- The fixed-direction scalar estimate good set is contained in its punctured normalized
quotient version. -/
theorem directionalLineScalarEstimateSet_subset_directionalLineScalarQuotientEstimateSet
    {v : E} {u : E → ℝ} :
    directionalLineScalarEstimateSet v u ⊆ directionalLineScalarQuotientEstimateSet v u := by
  intro x hx
  exact hx.quadraticQuotientEstimateAt

/-- On `ℝ`, scalar quadratic estimate data at a point gives scalar estimate data on the
restriction to any real affine line through that point. -/
theorem RealScalarQuadraticEstimateAt.real_lineRestriction
    {f : ℝ → ℝ} {x ξ : ℝ} (h : RealScalarQuadraticEstimateAt f x) :
    RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction f x ξ) 0 := by
  rcases h with ⟨p, q, hest⟩
  have hwith : RealScalarQuadraticEstimateWithDataAt f x p q := hest
  exact
    (RealScalarQuadraticEstimateWithDataAt.real_lineRestriction
      (ξ := ξ) hwith).realScalarQuadraticEstimateAt

/-- A scalar estimate for the unit real-line restriction through `x` is exactly a scalar estimate
at `x`. -/
theorem RealScalarQuadraticEstimateAt.of_real_lineRestriction_one
    {f : ℝ → ℝ} {x : ℝ}
    (h : RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction f x 1) 0) :
    RealScalarQuadraticEstimateAt f x := by
  rcases h with ⟨p, q, hest⟩
  refine ⟨p, q, ?_⟩
  intro ε hε
  simpa [AleksandrovDifferentiability.lineRestriction] using hest ε hε

/-- Quotient-estimate version of `RealScalarQuadraticEstimateAt.real_lineRestriction`. -/
theorem RealScalarQuadraticQuotientEstimateAt.real_lineRestriction
    {f : ℝ → ℝ} {x ξ : ℝ} (h : RealScalarQuadraticQuotientEstimateAt f x) :
    RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction f x ξ) 0 := by
  rcases h with ⟨p, q, hest⟩
  have hwith : RealScalarQuadraticQuotientEstimateWithDataAt f x p q := hest
  exact
    (RealScalarQuadraticQuotientEstimateWithDataAt.real_lineRestriction
      (ξ := ξ) hwith).realScalarQuadraticQuotientEstimateAt

/-- Punctured normalized quotient version of
`RealScalarQuadraticEstimateAt.of_real_lineRestriction_one`. -/
theorem RealScalarQuadraticQuotientEstimateAt.of_real_lineRestriction_one
    {f : ℝ → ℝ} {x : ℝ}
    (h : RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction f x 1) 0) :
    RealScalarQuadraticQuotientEstimateAt f x := by
  rcases h with ⟨p, q, hest⟩
  refine ⟨p, q, ?_⟩
  intro ε hε
  simpa [AleksandrovDifferentiability.lineRestriction] using hest ε hε

/-- On the real line, scalar quadratic estimate data at a point supplies compatible finite
slice data for any finite family of real directions: every line slope is obtained from the same
ambient scalar first-order coefficient. -/
theorem RealScalarQuadraticEstimateAt.compatibleDirectionalSliceEstimateAt_real
    {ι : Type*} {D : Finset ι} {v : ι → ℝ} {f : ℝ → ℝ} {x : ℝ}
    (h : RealScalarQuadraticEstimateAt f x) :
    CompatibleDirectionalSliceEstimateAt D v f x := by
  rcases h with ⟨p, q, hest⟩
  have hwith : RealScalarQuadraticEstimateWithDataAt f x p q := hest
  refine ⟨p, (fun i => v i ^ 2 * q), (fun i j => (v i + v j) ^ 2 * q), ?_, ?_⟩
  · intro i _hi
    have hi := hwith.real_lineRestriction (ξ := v i)
    simpa [Real.inner_apply, mul_comm] using hi
  · intro i _hi j _hj
    have hij := hwith.real_lineRestriction (ξ := v i + v j)
    simpa [Real.inner_apply, mul_comm] using hij

/-- Punctured normalized quotient version of
`RealScalarQuadraticEstimateAt.compatibleDirectionalSliceEstimateAt_real`. -/
theorem RealScalarQuadraticQuotientEstimateAt.compatibleDirectionalSliceQuotientEstimateAt_real
    {ι : Type*} {D : Finset ι} {v : ι → ℝ} {f : ℝ → ℝ} {x : ℝ}
    (h : RealScalarQuadraticQuotientEstimateAt f x) :
    CompatibleDirectionalSliceQuotientEstimateAt D v f x := by
  rcases h with ⟨p, q, hest⟩
  have hwith : RealScalarQuadraticQuotientEstimateWithDataAt f x p q := hest
  refine ⟨p, (fun i => v i ^ 2 * q), (fun i j => (v i + v j) ^ 2 * q), ?_, ?_⟩
  · intro i _hi
    have hi := hwith.real_lineRestriction (ξ := v i)
    simpa [Real.inner_apply, mul_comm] using hi
  · intro i _hi j _hj
    have hij := hwith.real_lineRestriction (ξ := v i + v j)
    simpa [Real.inner_apply, mul_comm] using hij

/-- On the real line, the ordinary scalar-estimate good set is contained in every directional
line scalar-estimate good set. -/
theorem realScalarQuadraticEstimateSet_subset_directionalLineScalarEstimateSet
    (ξ : ℝ) (f : ℝ → ℝ) :
    realScalarQuadraticEstimateSet f ⊆ directionalLineScalarEstimateSet ξ f := by
  intro x hx
  exact hx.real_lineRestriction

/-- Quotient-estimate version of
`realScalarQuadraticEstimateSet_subset_directionalLineScalarEstimateSet`. -/
theorem realScalarQuadraticQuotientEstimateSet_subset_directionalLineScalarQuotientEstimateSet
    (ξ : ℝ) (f : ℝ → ℝ) :
    realScalarQuadraticQuotientEstimateSet f ⊆ directionalLineScalarQuotientEstimateSet ξ f := by
  intro x hx
  exact hx.real_lineRestriction

/-- Normalizing a nonzero direction by the inverse of its norm gives a unit direction. -/
lemma norm_inv_norm_smul_eq_one {w : E} (hw : w ≠ 0) :
    ‖‖w‖⁻¹ • w‖ = 1 := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact inv_mul_cancel₀ hn

end AleksandrovDifferentiability
