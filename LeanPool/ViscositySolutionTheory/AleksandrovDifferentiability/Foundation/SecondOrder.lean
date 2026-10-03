/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Second order expansion interfaces

This file contains the local formulation of second order differentiability used
for the convex Aleksandrov theorem.
-/

@[expose] public noncomputable section

open Asymptotics
open InnerProduct
open scoped Topology

namespace AleksandrovDifferentiability

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A continuous linear operator is symmetric with respect to the real inner product. -/
def IsSymmetricOperator (B : E →L[ℝ] E) : Prop :=
  (B : E →ₗ[ℝ] E).IsSymmetric

/-- The concrete quadratic second order expansion at `x`, written in increment coordinates.

The point `p` is the first-order vector and `B` is the Hessian candidate. The quadratic term is
`(1 / 2) * ⟪z, B z⟫_ℝ`, the usual inner-product notation for `z · B z / 2`.
-/
def HasSecondOrderExpansionAt
    (u : E → ℝ) (x p : E) (B : E →L[ℝ] E) : Prop :=
  (fun z : E =>
      u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z))
    =o[𝓝 0] (fun z : E => ‖z‖ ^ 2)

/-- A second-order expansion whose first-order term is a continuous linear functional.

Mathlib's Fréchet derivative of a scalar-valued map has this shape. The project theorem statement
uses gradient vectors instead, so `hasSecondOrderExpansionAt_of_clm` below converts this interface
through the Fréchet-Riesz representation theorem. -/
def HasSecondOrderExpansionAtCLM
    (u : E → ℝ) (x : E) (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E) : Prop :=
  (fun z : E =>
      u (x + z) - u x - ℓ z - (1 / 2 : ℝ) * inner ℝ z (B z))
    =o[𝓝 0] (fun z : E => ‖z‖ ^ 2)

/-- Second order differentiability at a point, with a symmetric Hessian candidate. -/
def SecondOrderDifferentiableAt (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ B : E →L[ℝ] E,
    IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B

/-- Points where `u` has the prescribed second-order expansion data `(p, B)`. -/
def secondOrderExpansionSet (u : E → ℝ) (p : E) (B : E →L[ℝ] E) : Set E :=
  {x | HasSecondOrderExpansionAt u x p B}

/-- Points where `u` has prescribed second-order expansion data whose first-order term is the
continuous linear functional `ℓ`. -/
def secondOrderExpansionSetCLM
    (u : E → ℝ) (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E) : Set E :=
  {x | HasSecondOrderExpansionAtCLM u x ℓ B}

/-- Points where `u` carries some symmetric second-order expansion data whose first-order term is
a continuous linear functional. In Hilbert spaces this is another route into
`secondOrderDifferentiabilitySet`, via Fréchet-Riesz. -/
def secondOrderCLMExpansionDataSet (u : E → ℝ) : Set E :=
  {x | ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
    IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B}

/-- Points where `u` is second-order differentiable in the project sense. -/
def secondOrderDifferentiabilitySet (u : E → ℝ) : Set E :=
  {x | SecondOrderDifferentiableAt u x}

@[simp]
theorem mem_secondOrderExpansionSet {u : E → ℝ} {x p : E} {B : E →L[ℝ] E} :
    x ∈ secondOrderExpansionSet u p B ↔ HasSecondOrderExpansionAt u x p B :=
  Iff.rfl

@[simp]
theorem mem_secondOrderExpansionSetCLM
    {u : E → ℝ} {x : E} {ℓ : E →L[ℝ] ℝ} {B : E →L[ℝ] E} :
    x ∈ secondOrderExpansionSetCLM u ℓ B ↔ HasSecondOrderExpansionAtCLM u x ℓ B :=
  Iff.rfl

@[simp]
theorem mem_secondOrderCLMExpansionDataSet {u : E → ℝ} {x : E} :
    x ∈ secondOrderCLMExpansionDataSet u ↔
      ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B :=
  Iff.rfl

@[simp]
theorem mem_secondOrderDifferentiabilitySet {u : E → ℝ} {x : E} :
    x ∈ secondOrderDifferentiabilitySet u ↔ SecondOrderDifferentiableAt u x :=
  Iff.rfl

theorem secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (hB : IsSymmetricOperator B)
    (h : HasSecondOrderExpansionAt u x p B) :
    SecondOrderDifferentiableAt u x := by
  exact ⟨p, B, hB, h⟩

section SymmetricPart

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The symmetric part of a continuous linear operator. The quadratic form
`z ↦ inner ℝ z (B z)` only depends on this symmetric part. -/
noncomputable def symmetricPartCLM (B : H →L[ℝ] H) : H →L[ℝ] H :=
  (1 / 2 : ℝ) • (B + B†)

/-- The symmetric part is symmetric. -/
theorem isSymmetricOperator_symmetricPartCLM (B : H →L[ℝ] H) :
    IsSymmetricOperator (symmetricPartCLM B) := by
  rw [IsSymmetricOperator]
  intro x y
  dsimp [symmetricPartCLM]
  simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  ring

/-- The quadratic form of an operator agrees with that of its symmetric part. -/
theorem inner_symmetricPartCLM_self (B : H →L[ℝ] H) (z : H) :
    inner ℝ z ((symmetricPartCLM B) z) = inner ℝ z (B z) := by
  dsimp [symmetricPartCLM]
  rw [smul_apply, add_apply,
    inner_smul_right, inner_add_right, ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm (B z) z]
  ring

/-- A second-order expansion may always be rewritten with the symmetric part of its quadratic
operator. -/
theorem HasSecondOrderExpansionAt.symmetricPart
    {u : H → ℝ} {x p : H} {B : H →L[ℝ] H}
    (h : HasSecondOrderExpansionAt u x p B) :
    HasSecondOrderExpansionAt u x p (symmetricPartCLM B) := by
  refine h.congr_left ?_
  intro z
  rw [inner_symmetricPartCLM_self]

/-- A second-order expansion with any continuous linear quadratic operator gives second-order
differentiability by replacing the operator with its symmetric part. -/
theorem secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt_symmetricPart
    {u : H → ℝ} {x p : H} {B : H →L[ℝ] H}
    (h : HasSecondOrderExpansionAt u x p B) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt
    (isSymmetricOperator_symmetricPartCLM B) h.symmetricPart

end SymmetricPart

@[simp]
theorem isSymmetricOperator_zero_operator :
    IsSymmetricOperator (0 : E →L[ℝ] E) := by
  rw [IsSymmetricOperator]
  intro x y
  simp

/-- Constant functions have zero second-order expansion everywhere. -/
theorem hasSecondOrderExpansionAt_const (c : ℝ) (x : E) :
    HasSecondOrderExpansionAt (fun _ : E => c) x 0 0 := by
  dsimp [HasSecondOrderExpansionAt]
  refine (isLittleO_zero (fun z : E => ‖z‖ ^ 2) (𝓝 0)).congr_left ?_
  intro z
  simp

/-- Constant functions are second-order differentiable everywhere. -/
theorem secondOrderDifferentiableAt_const (c : ℝ) (x : E) :
    SecondOrderDifferentiableAt (fun _ : E => c) x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt isSymmetricOperator_zero_operator
    (hasSecondOrderExpansionAt_const c x)

/-- Affine functions represented by an inner-product slope have zero Hessian everywhere. -/
theorem hasSecondOrderExpansionAt_inner_add_const (p : E) (c : ℝ) (x : E) :
    HasSecondOrderExpansionAt (fun y : E => inner ℝ p y + c) x p 0 := by
  dsimp [HasSecondOrderExpansionAt]
  refine (isLittleO_zero (fun z : E => ‖z‖ ^ 2) (𝓝 0)).congr_left ?_
  intro z
  simp [inner_add_right, add_comm]

/-- Affine functions represented by an inner-product slope are second-order differentiable
everywhere. -/
theorem secondOrderDifferentiableAt_inner_add_const (p : E) (c : ℝ) (x : E) :
    SecondOrderDifferentiableAt (fun y : E => inner ℝ p y + c) x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt isSymmetricOperator_zero_operator
    (hasSecondOrderExpansionAt_inner_add_const p c x)

/-- Symmetry is preserved by scalar multiplication of the operator. -/
theorem IsSymmetricOperator.smul {B : E →L[ℝ] E} (hB : IsSymmetricOperator B) (c : ℝ) :
    IsSymmetricOperator (c • B) := by
  intro x y
  calc
    inner ℝ ((c • B) x) y = c * inner ℝ (B x) y := by
      rw [smul_apply, real_inner_smul_left]
    _ = c * inner ℝ x (B y) := congrArg (fun r : ℝ => c * r) (hB x y)
    _ = inner ℝ x ((c • B) y) := by
      rw [smul_apply, real_inner_smul_right]

/-- Pull a second-order expansion back across a nonzero scalar dilation and translation.

If `z ↦ u (a + r • z)` has expansion data `(p, B)` at `z`, then `u` has expansion data
`(r⁻¹ • p, (r⁻¹)^2 • B)` at `a + r • z`. This is the local transport step needed for the
source-cube-to-open-domain localization. -/
theorem HasSecondOrderExpansionAt.of_comp_add_smul
    {u : E → ℝ} {a z p : E} {B : E →L[ℝ] E} {r : ℝ} (hr : r ≠ 0)
    (h : HasSecondOrderExpansionAt (fun y : E => u (a + r • y)) z p B) :
    HasSecondOrderExpansionAt u (a + r • z) (r⁻¹ • p) ((r⁻¹ ^ 2 : ℝ) • B) := by
  dsimp [HasSecondOrderExpansionAt] at h ⊢
  have htendsto : Filter.Tendsto (fun w : E => r⁻¹ • w) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun w : E => (r⁻¹ : ℝ) • w) :=
      (continuous_const : Continuous fun _ : E => (r⁻¹ : ℝ)).smul continuous_id
    simpa using hc.tendsto (0 : E)
  have hcomp := h.comp_tendsto htendsto
  have hscaled :
      ((fun z₁ : E =>
          u (a + r • (z + z₁)) - u (a + r • z) - inner ℝ p z₁ -
            (1 / 2 : ℝ) * inner ℝ z₁ (B z₁)) ∘ fun w : E => r⁻¹ • w)
        =o[𝓝 (0 : E)] (fun w : E => ‖(r⁻¹ : ℝ)‖ ^ 2 * ‖w‖ ^ 2) := by
    refine hcomp.congr_right ?_
    intro w
    simp [norm_smul, mul_pow, mul_comm]
  refine hscaled.of_const_mul_right.congr_left ?_
  intro w
  have hpoint : a + r • (z + r⁻¹ • w) = a + r • z + w := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr, one_smul]
    abel
  have hslope : inner ℝ p (r⁻¹ • w) = inner ℝ (r⁻¹ • p) w := by
    simp [real_inner_smul_left, real_inner_smul_right]
  have hquad :
      inner ℝ (r⁻¹ • w) (B (r⁻¹ • w)) =
        inner ℝ w ((r⁻¹ ^ 2 : ℝ) • B w) := by
    simp [map_smul, real_inner_smul_left, real_inner_smul_right, pow_two, mul_assoc]
  dsimp [Function.comp]
  rw [hpoint, hslope, hquad, smul_apply]

/-- Second-order differentiability is transported back across a nonzero scalar dilation and
translation. -/
theorem SecondOrderDifferentiableAt.of_comp_add_smul
    {u : E → ℝ} {a z : E} {r : ℝ} (hr : r ≠ 0)
    (h : SecondOrderDifferentiableAt (fun y : E => u (a + r • y)) z) :
    SecondOrderDifferentiableAt u (a + r • z) := by
  rcases h with ⟨p, B, hB, hquad⟩
  exact
    ⟨r⁻¹ • p, (r⁻¹ ^ 2 : ℝ) • B, hB.smul (r⁻¹ ^ 2),
      hquad.of_comp_add_smul hr⟩

/-- On a subsingleton inner product space every function is second-order differentiable at every
point. This records the degenerate finite-dimensional endpoint used as a sanity check for the
theorem-boundary statements. -/
theorem secondOrderDifferentiableAt_of_subsingleton [Subsingleton E]
    (u : E → ℝ) (x : E) :
    SecondOrderDifferentiableAt u x := by
  refine secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt (p := 0) (B := 0) ?_ ?_
  · exact isSymmetricOperator_zero_operator
  · dsimp [HasSecondOrderExpansionAt]
    refine (isLittleO_zero (fun z : E => ‖z‖ ^ 2) (𝓝 0)).congr_left ?_
    intro z
    have hz : z = 0 := Subsingleton.elim z 0
    subst z
    simp

/-- Finite-dimensional rank-zero version of `secondOrderDifferentiableAt_of_subsingleton`. -/
theorem secondOrderDifferentiableAt_of_finrank_eq_zero [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 0) (u : E → ℝ) (x : E) :
    SecondOrderDifferentiableAt u x := by
  have hzero : ∀ y : E, y = 0 :=
    (finrank_zero_iff_forall_zero (K := ℝ) (V := E)).mp hE
  have : Subsingleton E := (subsingleton_iff_forall_eq (0 : E)).mpr hzero
  exact secondOrderDifferentiableAt_of_subsingleton u x

/-- Convert a scalar first-order continuous-linear-map expansion into the project expansion
format when the linear functional is represented by inner product with `p`. -/
theorem hasSecondOrderExpansionAt_of_clm_eq_inner
    {u : E → ℝ} {x p : E} {ℓ : E →L[ℝ] ℝ} {B : E →L[ℝ] E}
    (hℓ : ∀ z : E, ℓ z = inner ℝ p z)
    (h : HasSecondOrderExpansionAtCLM u x ℓ B) :
    HasSecondOrderExpansionAt u x p B := by
  refine h.congr_left ?_
  intro z
  simp [hℓ z]

/-- A continuous-linear-map first-order expansion with a symmetric Hessian candidate gives
second-order differentiability in the project sense, provided the linear functional is represented
by inner product with `p`. -/
theorem secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM_eq_inner
    {u : E → ℝ} {x p : E} {ℓ : E →L[ℝ] ℝ} {B : E →L[ℝ] E}
    (hℓ : ∀ z : E, ℓ z = inner ℝ p z)
    (hB : IsSymmetricOperator B)
    (h : HasSecondOrderExpansionAtCLM u x ℓ B) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB
    (hasSecondOrderExpansionAt_of_clm_eq_inner hℓ h)

section Riesz

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- In a real Hilbert space, convert a scalar first-order continuous-linear-map expansion into the
project expansion format by representing the functional via Fréchet-Riesz. -/
theorem hasSecondOrderExpansionAt_of_clm
    {u : H → ℝ} {x : H} {ℓ : H →L[ℝ] ℝ} {B : H →L[ℝ] H}
    (h : HasSecondOrderExpansionAtCLM u x ℓ B) :
    HasSecondOrderExpansionAt u x ((InnerProductSpace.toDual ℝ H).symm ℓ) B :=
  hasSecondOrderExpansionAt_of_clm_eq_inner
    (fun z => by
      exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := H)
        (x := z) (y := ℓ)).symm) h

/-- A continuous-linear-map first-order expansion with a symmetric Hessian candidate gives
second-order differentiability in a real Hilbert space. -/
theorem secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM
    {u : H → ℝ} {x : H} {ℓ : H →L[ℝ] ℝ} {B : H →L[ℝ] H}
    (hB : IsSymmetricOperator B)
    (h : HasSecondOrderExpansionAtCLM u x ℓ B) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB
    (hasSecondOrderExpansionAt_of_clm h)

/-- A fixed CLM expansion locus with symmetric Hessian lies inside the project differentiability
locus in a real Hilbert space. -/
theorem secondOrderExpansionSetCLM_subset_secondOrderDifferentiabilitySet
    {u : H → ℝ} {ℓ : H →L[ℝ] ℝ} {B : H →L[ℝ] H}
    (hB : IsSymmetricOperator B) :
    secondOrderExpansionSetCLM u ℓ B ⊆ secondOrderDifferentiabilitySet u := by
  intro x hx
  exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM hB hx

/-- The CLM expansion-data locus lies inside the project differentiability locus in a real Hilbert
space. -/
theorem secondOrderCLMExpansionDataSet_subset_secondOrderDifferentiabilitySet
    {u : H → ℝ} :
    secondOrderCLMExpansionDataSet u ⊆ secondOrderDifferentiabilitySet u := by
  intro x hx
  rcases hx with ⟨ℓ, B, hB, hquad⟩
  exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM hB hquad

end Riesz

theorem secondOrderExpansionSet_subset_secondOrderDifferentiabilitySet
    {u : E → ℝ} {p : E} {B : E →L[ℝ] E} (hB : IsSymmetricOperator B) :
    secondOrderExpansionSet u p B ⊆ secondOrderDifferentiabilitySet u := by
  intro x hx
  exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB hx

end AleksandrovDifferentiability
