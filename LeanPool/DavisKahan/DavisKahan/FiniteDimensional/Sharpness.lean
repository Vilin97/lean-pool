/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.DavisKahan.Sources.Davis1963.RotationEnergy
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.Core.AngleOperatorBlockSum
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.UnitarilyInvariant
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DoubleAngle.SinTheta
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.TwoDimensionalSingularValues
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation

/-!
# Sharpness and two-dimensional extremizers

Literature map:

* `prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 13.
* Davis--Kahan (1970), Section 2 immediately after the four headline
  theorems, and the two-dimensional models used throughout Sections 6--8.
* `prose/core-arguments/Davis-1963-core-arguments.tex`, final sharp two-subspace
  section.

The constants in all four classic theorems are optimal.  Planar models must
respect the multiplicity convention of each angle operator: the one-sided
`sin (2Θ)` map has one nonzero singular value per principal plane, unlike the
symmetric off-diagonal perturbations used by the full-space tangent models.
-/


/-! ## Remaining construction plan

Use a single explicit planar model for every sharpness result.  Define the
reference and rotated one-dimensional subspaces in `EuclideanSpace R (Fin 2)`,
use a diagonal gapped operator, and form sine, tangent, and double-angle
perturbations by rotation/conjugation.  Prove the model projections and
singular values by extensional matrix calculation.  Each sharpness theorem
should then be a scalar trigonometric simplification, making failures at right
angles or quarter turns explicit rather than hidden in abstract geometry.
-/


/-! ## Weak-agent execution plan: explicit planar extremizers

Use the standard basis `e0`, `e1` of `EuclideanSpace 𝕜 (Fin 2)`.  Add local
abbreviations and simp lemmas before defining any operator:

* `uθ := cos θ • e0 + sin θ • e1`;
* `vθ := -sin θ • e0 + cos θ • e1`;
* orthonormality of `uθ,vθ`;
* `modelSubspace = 𝕜 ∙ e0` and
  `rotatedModelSubspace θ = 𝕜 ∙ uθ`.

Prefer `Submodule.span 𝕜 {e0}` and `Submodule.span 𝕜 {uθ}`.  Prove membership
and projection formulas once.  Then establish the `2 × 2` matrices of both
orthogonal projections by `LinearMap.ext` on `e0,e1`.

Define `modelGappedOperator a b` by
`e0 ↦ a • e0`, `e1 ↦ b • e1`.  For the `sin Θ` extremizer, use

`Rθ D Rθ⁻¹ - D`,

where `Rθ` sends `e0,e1` to `uθ,vθ`.  Its eigenvalues are
`±(b-a) sin θ`, so its operator norm is `(b-a) sin θ` on the stated angle
range.  Prove this by an explicit characteristic/eigenvector calculation or
by squaring the matrix to a scalar multiple of the identity.

Do not reuse that perturbation for the tangent and double-angle theorems.
For each remaining model, first write the exact equality conditions from the
corresponding block/Sylvester proof and solve the resulting scalar equations
for the four matrix entries.  Add a private theorem recording those entries,
then define the operator from the solved matrix.  This is safer than guessing a
rotation conjugate and discovering later that the zero-compression or
off-diagonal hypothesis fails.

For every model, prove in this order:

1. symmetry;
2. the required reducing and compression/off-diagonal hypotheses;
3. the exact internal or ordered gap;
4. the singular values of the perturbation;
5. the singular values of the angle operator;
6. the displayed UI-norm equality by unitary invariance and homogeneity.

For a `2 × 2` operator whose square is `r^2 • id`, use that identity to prove
both singular values are `|r|`; avoid expanding the general singular-value
definition repeatedly.  Keep trigonometric side conditions (`sin θ ≥ 0`,
`cos θ > 0`, `cos (2θ) > 0`) as named lemmas.

For direct sums, define the block operator by the decomposition
`Fin (2*m) ≃ Fin m × Fin 2` and transport `m` copies of the planar model.
Prove the singular-value multiset is repeated blockwise before invoking any UI
norm.  The scalar limit theorem should use existing `Real.tendsto_sin_div` and
`Real.tendsto_tan_div`-style lemmas if available; isolate it from the operator
sharpness development.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Filter

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The model two-dimensional space in which the sharpness counterexamples live. -/
abbrev Plane (𝕜 : Type*)  := EuclideanSpace 𝕜 (Fin 2)

/-- First standard basis vector of the planar model. -/
noncomputable def e0 : Plane 𝕜 := EuclideanSpace.single 0 1

/-- Second standard basis vector of the planar model. -/
noncomputable def e1 : Plane 𝕜 := EuclideanSpace.single 1 1

/-- Unit vector at angle `θ` from the coordinate line. -/
noncomputable def uθ (θ : ℝ) : Plane 𝕜 :=
  (Real.cos θ : 𝕜) • e0 + (Real.sin θ : 𝕜) • e1

/-- Coordinate line in the two-dimensional model. -/
noncomputable def modelSubspace : Submodule 𝕜 (Plane 𝕜) :=
  Submodule.span 𝕜 {e0}

/-- Line obtained by rotating the coordinate line by angle `θ`. -/
noncomputable def rotatedModelSubspace (θ : ℝ) : Submodule 𝕜 (Plane 𝕜) :=
  Submodule.span 𝕜 {uθ θ}

/-! Construct the following five operators as explicit `2 × 2` matrices in
the standard basis.  Start with `diag(a,b)`, conjugate by the planar rotation
for the `sin Θ` model, use the graph residual for `tan Θ`, and take the
reflection/off-diagonal parts for the double-angle models.  Matrix ext reduces
all later norm and equality claims to scalar trigonometric identities. -/

/-- Diagonal gapped operator used by the extremal examples. -/
noncomputable def modelGappedOperator (a b : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin (Matrix.diagonal ![(a : 𝕜), (b : 𝕜)])

/-- Planar rotation matrix by angle `θ` with real entries cast into `𝕜`. -/
noncomputable def planarRotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) 𝕜 :=
  !![(Real.cos θ : 𝕜), -(Real.sin θ : 𝕜);
     (Real.sin θ : 𝕜), (Real.cos θ : 𝕜)]

/-- Perturbation producing equality in the `sin Θ` model: the rotation
conjugate of the diagonal model minus the diagonal model,
`R(θ) diag(a,b) R(θ)ᵀ - diag(a,b)`.  Its entries are
`(b-a) sin²θ`, off-diagonal `(a-b) sinθ cosθ`, and `(a-b) sin²θ`, so its
square is `((b-a) sinθ)² • 1`. -/
noncomputable def modelSinThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  let d := b - a
  Matrix.toEuclideanLin
    !![((d * Real.sin θ ^ 2 : ℝ) : 𝕜),
       ((-d * Real.sin θ * Real.cos θ : ℝ) : 𝕜);
       ((-d * Real.sin θ * Real.cos θ : ℝ) : 𝕜),
       ((-d * Real.sin θ ^ 2 : ℝ) : 𝕜)]

/-- Perturbation/residual producing equality in the `tan Θ` model.

Construction route: use the graph residual of the rotated one-dimensional
subspace, with scaling chosen so the ordered Sylvester inequality is an
equality. -/
noncomputable def modelTanThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin
    !![(0 : 𝕜), (((b-a) * Real.tan θ : ℝ) : 𝕜);
       (((b-a) * Real.tan θ : ℝ) : 𝕜), (0 : 𝕜)]

/-- Reflection-compatible perturbation producing equality in `sin (2 Θ)`:
the purely off-diagonal part of the rotated model, with entry
`(a-b) sinθ cosθ = ((a-b)/2) sin (2θ)` in both corners.  Being purely
off-diagonal it anticommutes with the reflection `diag(1,-1)` through the
model subspace. -/
noncomputable def modelSinTwoThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin
    !![0, (((a - b) / 2 * Real.sin (2 * θ) : ℝ) : 𝕜);
       (((a - b) / 2 * Real.sin (2 * θ) : ℝ) : 𝕜), 0]

/-- Off-diagonal perturbation used by the `tan (2 Θ)` extremizer: the purely
off-diagonal symmetric perturbation with entry `((b-a)/2) tan (2θ)`.

Sign audit, 2026-08-10.  The planar Riccati rotation law for
`diag(a,b) + h (e₀ ⊗ e₁ + e₁ ⊗ e₀)` is `tan (2θ) = 2h/(a-b)`, not `2h/(b-a)`
as this docstring previously said, so the reducing line of `diag(a,b) + H` sits
at angle `-θ`, and the operator whose reducing line is `rotatedModelSubspace θ`
is `modelGappedOperator a b - H`: see `modelTanTwoThetaPerturbedOperator`.  Only
the sign is affected; the two singular values are `((b-a)/2) |tan 2θ|` either
way, so every unitarily invariant seminorm -- and hence
`tanTwoTheta_model_equality` -- is unchanged. -/
noncomputable def modelTanTwoThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin
    !![0, (((b - a) / 2 * Real.tan (2 * θ) : ℝ) : 𝕜);
       (((b - a) / 2 * Real.tan (2 * θ) : ℝ) : 𝕜), 0]


/-! ## Explicit planar geometry -/

/-- The first planar basis vector is a unit vector. -/
@[simp] theorem norm_e0 : ‖e0 (𝕜 := 𝕜)‖ = 1 := by
  simp [e0]

/-- `e1` is a unit vector. -/
@[simp] theorem norm_e1 : ‖e1 (𝕜 := 𝕜)‖ = 1 := by
  simp [e1]

/-- `e0` is normalised. -/
theorem inner_e0_e0 : ⟪e0 (𝕜 := 𝕜), e0⟫_𝕜 = 1 := by
  simp [e0]

/-- `e1` is normalised. -/
theorem inner_e1_e1 : ⟪e1 (𝕜 := 𝕜), e1⟫_𝕜 = 1 := by
  simp [e1]

/-- `e0` and `e1` are orthogonal. -/
@[simp] theorem inner_e0_e1 : ⟪e0 (𝕜 := 𝕜), e1⟫_𝕜 = 0 := by
  simp [e0, e1, EuclideanSpace.inner_single_left]

/-- Orthogonality in the other order, for `simp` to close either orientation. -/
@[simp] theorem inner_e1_e0 : ⟪e1 (𝕜 := 𝕜), e0⟫_𝕜 = 0 := by
  simp [e0, e1, EuclideanSpace.inner_single_left]

/-- The rotated generator's overlap with `e0` is `cos θ`. -/
@[simp] theorem inner_uθ_e0 (θ : ℝ) :
    ⟪uθ (𝕜 := 𝕜) θ, e0⟫_𝕜 = (Real.cos θ : 𝕜) := by
  simp only [uθ, inner_add_left, inner_smul_left, inner_smul_left,
    inner_e0_e0, inner_e1_e0, RCLike.conj_ofReal, RCLike.conj_ofReal]
  ring

/-- The rotated generator's overlap with `e1` is `sin θ`. -/
@[simp] theorem inner_uθ_e1 (θ : ℝ) :
    ⟪uθ (𝕜 := 𝕜) θ, e1⟫_𝕜 = (Real.sin θ : 𝕜) := by
  simp only [uθ, inner_add_left, inner_smul_left, inner_smul_left,
    inner_e0_e1, inner_e1_e1, RCLike.conj_ofReal, RCLike.conj_ofReal]
  ring

/-- The rotated generator is a unit vector: the rotation is by a genuine angle. -/
@[simp] theorem norm_uθ (θ : ℝ) : ‖uθ (𝕜 := 𝕜) θ‖ = 1 := by
  have hsq : ‖uθ (𝕜 := 𝕜) θ‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), uθ]
    simp only [inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, inner_e0_e0, inner_e1_e1, inner_e0_e1, inner_e1_e0,
      RCLike.conj_ofReal]
    -- the residual goal is `RCLike.re` of a real cast; `nlinarith` cannot see
    -- through the cast until it is pushed outwards
    simp only [mul_one, mul_zero, add_zero, zero_add, ← RCLike.ofReal_mul,
      ← RCLike.ofReal_add, RCLike.ofReal_re]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (uθ (𝕜 := 𝕜) θ)]

private theorem plane_eq_coord_smul_e0_add_coord_smul_e1 (x : Plane 𝕜) :
    x = x 0 • e0 (𝕜 := 𝕜) + x 1 • e1 (𝕜 := 𝕜) := by
  ext i
  fin_cases i <;> simp [e0, e1]

private theorem plane_linearMap_ext {F' : Type*} [AddCommMonoid F'] [Module 𝕜 F']
    {A B : Plane 𝕜 →ₗ[𝕜] F'}
    (h0 : A (e0 (𝕜 := 𝕜)) = B (e0 (𝕜 := 𝕜)))
    (h1 : A (e1 (𝕜 := 𝕜)) = B (e1 (𝕜 := 𝕜))) : A = B := by
  ext x
  rw [plane_eq_coord_smul_e0_add_coord_smul_e1 x]
  simp [h0, h1]

private theorem starProjection_span_singleton_apply_of_norm_one
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
     (v x : E') (hv : ‖v‖ = 1) :
    (Submodule.span 𝕜 {v}).starProjection x = ⟪v, x⟫_𝕜 • v := by
  classical
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span (by simp))
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        have hyv : y = v := by simpa using hy
        subst y
        simp [inner_sub_left, inner_smul_left,
          hv, inner_conj_symm]
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_right, ha, mul_zero]

/-- The model subspace projects `e0` to itself. -/
@[simp] theorem modelSubspace_starProjection_e0 :
    (modelSubspace (𝕜 := 𝕜)).starProjection (e0 (𝕜 := 𝕜)) = e0 := by
  have h := starProjection_span_singleton_apply_of_norm_one (𝕜 := 𝕜)
    (e0 (𝕜 := 𝕜)) (e0 (𝕜 := 𝕜)) norm_e0
  simpa [modelSubspace] using h

/-- The model subspace annihilates `e1`. -/
@[simp] theorem modelSubspace_starProjection_e1 :
    (modelSubspace (𝕜 := 𝕜)).starProjection (e1 (𝕜 := 𝕜)) = 0 := by
  have h := starProjection_span_singleton_apply_of_norm_one (𝕜 := 𝕜)
    (e0 (𝕜 := 𝕜)) (e1 (𝕜 := 𝕜)) norm_e0
  simpa [modelSubspace] using h

/-- The rotated subspace sends `e0` to `cos θ • uθ`: the overlap is the cosine of the angle, which
is what makes `θ` the principal angle between the two subspaces. -/
@[simp] theorem rotatedModelSubspace_starProjection_e0 (θ : ℝ) :
    (rotatedModelSubspace (𝕜 := 𝕜) θ).starProjection (e0 (𝕜 := 𝕜)) =
      (Real.cos θ : 𝕜) • uθ θ := by
  have h := starProjection_span_singleton_apply_of_norm_one (𝕜 := 𝕜)
    (uθ (𝕜 := 𝕜) θ) (e0 (𝕜 := 𝕜)) (norm_uθ θ)
  simpa [rotatedModelSubspace] using h

/-- The rotated subspace sends `e1` to `sin θ • uθ`. -/
@[simp] theorem rotatedModelSubspace_starProjection_e1 (θ : ℝ) :
    (rotatedModelSubspace (𝕜 := 𝕜) θ).starProjection (e1 (𝕜 := 𝕜)) =
      (Real.sin θ : 𝕜) • uθ θ := by
  have h := starProjection_span_singleton_apply_of_norm_one (𝕜 := 𝕜)
    (uθ (𝕜 := 𝕜) θ) (e1 (𝕜 := 𝕜)) (norm_uθ θ)
  simpa [rotatedModelSubspace] using h

/-- The rotated line is invariant, so its projector fixes its own generator.
The double-angle operators nest the two projectors, so this is needed. -/
@[simp] theorem rotatedModelSubspace_starProjection_uθ (θ : ℝ) :
    (rotatedModelSubspace (𝕜 := 𝕜) θ).starProjection (uθ (𝕜 := 𝕜) θ) =
      uθ θ := by
  have h := starProjection_span_singleton_apply_of_norm_one (𝕜 := 𝕜)
    (uθ (𝕜 := 𝕜) θ) (uθ (𝕜 := 𝕜) θ) (norm_uθ θ)
  rw [rotatedModelSubspace, h, inner_self_eq_norm_sq_to_K, norm_uθ]
  simp

/-- Coordinate projection of the rotated generator, in the same nested
position. -/
@[simp] theorem modelSubspace_starProjection_uθ (θ : ℝ) :
    (modelSubspace (𝕜 := 𝕜)).starProjection (uθ (𝕜 := 𝕜) θ) =
      (Real.cos θ : 𝕜) • e0 := by
  rw [uθ, map_add, map_smul, map_smul, modelSubspace_starProjection_e0,
    modelSubspace_starProjection_e1]
  simp

private theorem projection_sub_model_eq_matrix (θ : ℝ) :
    projection (modelSubspace (𝕜 := 𝕜)) -
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ) =
      Matrix.toEuclideanLin
        !![((Real.sin θ ^ 2 : ℝ) : 𝕜),
           ((-Real.sin θ * Real.cos θ : ℝ) : 𝕜);
           ((-Real.sin θ * Real.cos θ : ℝ) : 𝕜),
           ((-Real.sin θ ^ 2 : ℝ) : 𝕜)] := by
  have hpy : ((Real.sin θ : 𝕜)) ^ 2 + ((Real.cos θ : 𝕜)) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => (r : 𝕜)) (Real.sin_sq_add_cos_sq θ)
    push_cast at h
    exact h
  apply plane_linearMap_ext
  · -- reduce the projections *before* `e0`/`e1` are unfolded into coordinates
    simp only [LinearMap.sub_apply, projection, ContinuousLinearMap.coe_coe,
      modelSubspace_starProjection_e0,
      rotatedModelSubspace_starProjection_e0]
    ext i
    fin_cases i <;>
      simp [uθ, e0, e1, Matrix.toLpLin_apply] <;>
      (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal,
        mul_one]) <;>
      -- `ring` degrades to `ring_nf` and *succeeds*, so `first` would never
      -- reach the Pythagorean case; `ring1` fails properly
      first
        | ring1
        | linear_combination (-1 : 𝕜) * hpy
  · simp only [LinearMap.sub_apply, projection, ContinuousLinearMap.coe_coe,
      modelSubspace_starProjection_e1,
      rotatedModelSubspace_starProjection_e1]
    ext i
    fin_cases i <;>
      simp [uθ, e0, e1, Matrix.toLpLin_apply] <;>
      (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal,
        mul_one])
    ring1

private theorem sinThetaMap_model_eq_matrix (θ : ℝ) :
    sinThetaMap (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ) =
      Matrix.toEuclideanLin
        !![((Real.sin θ ^ 2 : ℝ) : 𝕜), 0;
           ((-Real.sin θ * Real.cos θ : ℝ) : 𝕜), 0] := by
  have hpy : ((Real.sin θ : 𝕜)) ^ 2 + ((Real.cos θ : 𝕜)) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => (r : 𝕜)) (Real.sin_sq_add_cos_sq θ)
    push_cast at h
    exact h
  apply plane_linearMap_ext
  · -- reduce the projections *before* `e0`/`e1` are unfolded into coordinates
    simp only [sinThetaMap, complementaryProjection, projection,
      ContinuousLinearMap.coe_coe, LinearMap.comp_apply,
      modelSubspace_starProjection_e0,
      rotatedModelSubspace_starProjection_e0,
      Submodule.starProjection_orthogonal_val]
    ext i
    fin_cases i <;>
      simp [uθ, e0, e1, Matrix.toLpLin_apply] <;>
      (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal,
        mul_one]) <;>
      -- `ring` degrades to `ring_nf` and *succeeds*, so `first` would never
      -- reach the Pythagorean case; `ring1` fails properly
      first
        | ring1
        | linear_combination (-1 : 𝕜) * hpy
  · simp only [sinThetaMap, complementaryProjection, projection,
      ContinuousLinearMap.coe_coe, LinearMap.comp_apply,
      modelSubspace_starProjection_e1,
      Submodule.starProjection_orthogonal_val]
    ext i
    fin_cases i <;>
      simp [e1, Matrix.toLpLin_apply]

private theorem sinTwoAngleOperator_model_eq_matrix (θ : ℝ) :
    sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ) =
      Matrix.toEuclideanLin
        !![0, 0; ((Real.sin (2 * θ) : ℝ) : 𝕜), 0] := by
  have hpy : ((Real.sin θ : 𝕜)) ^ 2 + ((Real.cos θ : 𝕜)) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => (r : 𝕜)) (Real.sin_sq_add_cos_sq θ)
    push_cast at h
    exact h
  apply plane_linearMap_ext
  · -- reduce the projections before `e0`/`e1` become coordinates
    simp only [sinTwoAngleOperator, complementaryProjection, projection,
      ContinuousLinearMap.coe_coe, LinearMap.comp_apply,
      LinearMap.smul_apply,
      modelSubspace_starProjection_e0,
      rotatedModelSubspace_starProjection_e0,
      map_smul,
      modelSubspace_starProjection_uθ,
      Submodule.starProjection_orthogonal_val]
    ext i
    fin_cases i <;>
      simp [uθ, e0, e1, Matrix.toLpLin_apply,
        Real.sin_two_mul]
    try push_cast
    try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
    ring1
  ·
    simp only [sinTwoAngleOperator, complementaryProjection, projection,
      ContinuousLinearMap.coe_coe, LinearMap.comp_apply,
      LinearMap.smul_apply,
      modelSubspace_starProjection_e1,
      map_zero]
    ext i
    fin_cases i <;>
      simp [e1, Matrix.toLpLin_apply,
        Real.sin_two_mul]

private theorem projection_sub_model_isSymmetric (θ : ℝ) :
    (projection (modelSubspace (𝕜 := 𝕜)) -
      projection (rotatedModelSubspace (𝕜 := 𝕜) θ)).IsSymmetric :=
  (projection_isSymmetric _).sub (projection_isSymmetric _)

private theorem projection_sub_model_sq (θ : ℝ) :
    (projection (modelSubspace (𝕜 := 𝕜)) -
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ)) ∘ₗ
      (projection (modelSubspace (𝕜 := 𝕜)) -
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      ((((Real.sin θ) ^ 2 : ℝ) : 𝕜) • LinearMap.id) := by
  have hpy : ((Real.sin θ : 𝕜)) ^ 2 + ((Real.cos θ : 𝕜)) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => (r : 𝕜)) (Real.sin_sq_add_cos_sq θ)
    push_cast at h
    exact h
  rw [projection_sub_model_eq_matrix]
  ext x i
  fin_cases i <;>
    simp [Matrix.toLpLin_apply] <;>
    (try simp only [RCLike.algebraMap_eq_ofReal, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]) <;>
    first
      | ring1
      | linear_combination (((Real.sin θ : 𝕜)) ^ 2 * x.ofLp 0) * hpy
      | linear_combination (((Real.sin θ : 𝕜)) ^ 2 * x.ofLp 1) * hpy

private theorem modelSinThetaPerturbation_isSymmetric (a b θ : ℝ) :
    (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ).IsSymmetric := by
  -- symmetry is exactly hermitianness of the underlying real matrix
  simp only [modelSinThetaPerturbation]
  refine Matrix.isSymmetric_toEuclideanLin_iff.mpr ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, RCLike.conj_ofReal]

private theorem modelSinThetaPerturbation_sq (a b θ : ℝ) :
    modelSinThetaPerturbation (𝕜 := 𝕜) a b θ ∘ₗ
      modelSinThetaPerturbation (𝕜 := 𝕜) a b θ =
      (((((b - a) * Real.sin θ) ^ 2 : ℝ) : 𝕜) • LinearMap.id) := by
  have hpy : ((Real.sin θ : 𝕜)) ^ 2 + ((Real.cos θ : 𝕜)) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => (r : 𝕜)) (Real.sin_sq_add_cos_sq θ)
    push_cast at h
    exact h
  ext x i
  fin_cases i <;>
    simp [modelSinThetaPerturbation, Matrix.toLpLin_apply] <;>
    (try simp only [RCLike.algebraMap_eq_ofReal, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]) <;>
    first
      | ring1
      | linear_combination ((((b : 𝕜) - (a : 𝕜)) ^ 2 *
          ((Real.sin θ : 𝕜)) ^ 2 * x.ofLp 0) * hpy)
      | linear_combination ((((b : 𝕜) - (a : 𝕜)) ^ 2 *
          ((Real.sin θ : 𝕜)) ^ 2 * x.ofLp 1) * hpy)

-- Elaboration got slower across the Mathlib bump and this proof no longer fits the default
-- budget.  Raised to the same level the three declarations lower in this file already use.
private theorem singularValues_sinThetaMap_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (sinThetaMap (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.sin θ) 0 := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hpy : ((Real.sin θ : 𝕜)) ^ 2 + ((Real.cos θ : 𝕜)) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => (r : 𝕜)) (Real.sin_sq_add_cos_sq θ)
    push_cast at h
    exact h
  rw [sinThetaMap_model_eq_matrix]
  apply singularValues_eq_pair_of_gram_eq finrank_euclideanSpace_fin
    (EuclideanSpace.basisFun (Fin 2) 𝕜) _ hsin (by norm_num) hsin
  -- compute the adjoint as a matrix; `adjoint_inner_left` cannot reduce an
  -- adjoint *composition* into matrix form
  have hadj : (Matrix.toEuclideanLin
      !![((Real.sin θ ^ 2 : ℝ) : 𝕜), 0;
         ((-Real.sin θ * Real.cos θ : ℝ) : 𝕜), 0]).adjoint =
      Matrix.toEuclideanLin
      !![((Real.sin θ ^ 2 : ℝ) : 𝕜), ((-Real.sin θ * Real.cos θ : ℝ) : 𝕜);
         0, 0] := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, RCLike.conj_ofReal]
  rw [hadj]
  refine (EuclideanSpace.basisFun (Fin 2) 𝕜).toBasis.ext fun i => ?_
  rw [OrthonormalBasis.coe_toBasis]
  fin_cases i <;>
    rw [diagOp_apply_basis] <;>
    ext j <;> fin_cases j <;>
    simp [LinearMap.comp_apply, Matrix.toLpLin_apply,
      Matrix.vecHead, Matrix.vecTail, EuclideanSpace.basisFun_apply]
  try push_cast
  first
    | ring1
    | linear_combination (((Real.sin θ : 𝕜)) ^ 2) * hpy

private theorem singularValues_projection_sub_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (projection (modelSubspace (𝕜 := 𝕜)) -
      projection (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.sin θ) (Real.sin θ) := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  simpa [abs_of_nonneg hsin] using
    singularValues_eq_abs_pair_of_isSymmetric_sq finrank_euclideanSpace_fin
      (EuclideanSpace.basisFun (Fin 2) 𝕜)
      (projection (modelSubspace (𝕜 := 𝕜)) -
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ))
      (Real.sin θ) (projection_sub_model_isSymmetric θ)
      (projection_sub_model_sq θ)

private theorem singularValues_modelSinThetaPerturbation
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
      pairSingularValues ((b - a) * Real.sin θ)
        ((b - a) * Real.sin θ) := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hprod : 0 ≤ (b - a) * Real.sin θ :=
    mul_nonneg (sub_nonneg.mpr hab.le) hsin
  simpa [abs_of_nonneg hprod] using
    singularValues_eq_abs_pair_of_isSymmetric_sq finrank_euclideanSpace_fin
      (EuclideanSpace.basisFun (Fin 2) 𝕜)
      (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ)
      ((b - a) * Real.sin θ)
      (modelSinThetaPerturbation_isSymmetric a b θ)
      (modelSinThetaPerturbation_sq a b θ)

private theorem singularValues_sinAngle_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.sin θ) (Real.sin θ) := by
  rw [← singularValues_projection_sub_projection]
  exact singularValues_projection_sub_model hθ0 hθ1

private theorem sinAngleOperator_model_eq_smul_id
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    sinAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ) =
      (((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) := by
  let A := projection (modelSubspace (𝕜 := 𝕜)) -
    projection (rotatedModelSubspace (𝕜 := 𝕜) θ)
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hpos : ((((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) :
      Plane 𝕜 →ₗ[𝕜] Plane 𝕜).IsPositive := by
    constructor
    · intro x y
      simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
        inner_smul_right, RCLike.conj_ofReal]
    · intro x
      rw [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
        RCLike.conj_ofReal, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner]
      exact mul_nonneg hsin (sq_nonneg _)
  have hsquare :
      ((((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) : Plane 𝕜 →ₗ[𝕜] Plane 𝕜) ∘ₗ
          (((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) = A.adjoint ∘ₗ A := by
    rw [show A.adjoint = A from (projection_sub_model_isSymmetric θ).adjoint_eq,
      show A ∘ₗ A = ((((Real.sin θ) ^ 2 : ℝ) : 𝕜) • LinearMap.id) from
        projection_sub_model_sq θ]
    -- plain `ext` also splits the coordinate, leaving `match_scalars` a
    -- scalar goal it cannot use
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    match_scalars
    ring
  change TauCeti.operatorAbs A = _
  exact (LinearMap.IsPositive.sqrt_unique A.isPositive_adjoint_comp_self hpos hsquare).symm

private theorem singularValues_tanAngle_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.tan θ) (Real.tan θ) := by
  have hθle : θ ≤ Real.pi / 2 := hθ1.le
  have hsinEq := sinAngleOperator_model_eq_smul_id (𝕜 := 𝕜) hθ0 hθle
  have harcsin : Real.arcsin (Real.sin θ) = θ :=
    Real.arcsin_sin (by linarith [Real.pi_pos]) hθle
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have htan : 0 ≤ Real.tan θ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ0 hθle
  -- the operator sits inside the symmetry witness, so it can only be
  -- replaced through the congruence bridge
  -- `sinAngleOperator` is *defined* as this modulus, so the equation has to
  -- be restated in the form the goal actually carries
  have hsinEq' : TauCeti.operatorAbs (projection (modelSubspace (𝕜 := 𝕜)) -
      projection (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      (((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) := hsinEq
  have hinner : TauCeti.selfAdjointFunctionalCalculus
      (TauCeti.isPositive_operatorAbs (projection (modelSubspace (𝕜 := 𝕜)) -
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ))).isSymmetric
      Real.arcsin = (((θ : ℝ) : 𝕜) • LinearMap.id) := by
    rw [TauCeti.selfAdjointFunctionalCalculus_congr_op _
      (show ((((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) :
          Plane 𝕜 →ₗ[𝕜] Plane 𝕜).IsSymmetric by
        intro x y
        simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
          inner_smul_right, RCLike.conj_ofReal])
      hsinEq' Real.arcsin]
    rw [TauCeti.selfAdjointFunctionalCalculus_real_smul_id,
      harcsin]
  rw [tanAngleOperator,
    TauCeti.selfAdjointFunctionalCalculus_congr_op _
      (show ((((θ : ℝ) : 𝕜) • LinearMap.id) :
          Plane 𝕜 →ₗ[𝕜] Plane 𝕜).IsSymmetric by
        intro x y
        simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
          inner_smul_right, RCLike.conj_ofReal])
      hinner safeTan,
    TauCeti.selfAdjointFunctionalCalculus_real_smul_id]
  simp only [safeTan, ite_eq_right hcos]
  rw [show Real.sin θ / Real.cos θ = Real.tan θ from (Real.tan_eq_sin_div_cos θ).symm]
  -- restate the scalar operator as a constant diagonal so the planar
  -- singular-value lemma applies
  rw [← diagOp_const_pair (EuclideanSpace.basisFun (Fin 2) 𝕜) (Real.tan θ)]
  simpa [abs_of_nonneg htan] using
    singularValues_diagOp_fin_two (𝕜 := 𝕜) finrank_euclideanSpace_fin
      (EuclideanSpace.basisFun (Fin 2) 𝕜) htan htan le_rfl

private theorem singularValues_sinTwoAngle_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.sin (2 * θ)) 0 := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  rw [sinTwoAngleOperator_model_eq_matrix]
  simpa [abs_of_nonneg hsin] using
    singularValues_lowerLeft_two_by_two (𝕜 := 𝕜) (Real.sin (2 * θ))

private theorem singularValues_tanTwoAngle_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 4) :
    (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.tan (2 * θ)) (Real.tan (2 * θ)) := by
  have hθle : θ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hsinEq := sinAngleOperator_model_eq_smul_id (𝕜 := 𝕜) hθ0 hθle
  have harcsin : Real.arcsin (Real.sin θ) = θ :=
    Real.arcsin_sin (by linarith [Real.pi_pos]) hθle
  have hcos : Real.cos (2 * θ) ≠ 0 := by
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  have htan : 0 ≤ Real.tan (2 * θ) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
  have hsinEq' : TauCeti.operatorAbs (projection (modelSubspace (𝕜 := 𝕜)) -
      projection (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      (((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) := hsinEq
  have hsymSin : ((((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) :
      Plane 𝕜 →ₗ[𝕜] Plane 𝕜).IsSymmetric := by
    intro x y
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal]
  have hsymTheta : ((((θ : ℝ) : 𝕜) • LinearMap.id) :
      Plane 𝕜 →ₗ[𝕜] Plane 𝕜).IsSymmetric := by
    intro x y
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal]
  have hinner : TauCeti.selfAdjointFunctionalCalculus
      (TauCeti.isPositive_operatorAbs (projection (modelSubspace (𝕜 := 𝕜)) -
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ))).isSymmetric
      Real.arcsin = (((θ : ℝ) : 𝕜) • LinearMap.id) := by
    rw [TauCeti.selfAdjointFunctionalCalculus_congr_op _ hsymSin
      hsinEq' Real.arcsin,
      TauCeti.selfAdjointFunctionalCalculus_real_smul_id, harcsin]
  rw [tanTwoAngleOperator,
    TauCeti.selfAdjointFunctionalCalculus_congr_op _ hsymTheta
      hinner safeTanTwo,
    TauCeti.selfAdjointFunctionalCalculus_real_smul_id]
  simp only [safeTanTwo, ite_eq_right hcos]
  rw [show Real.sin (2 * θ) / Real.cos (2 * θ) = Real.tan (2 * θ) from
    (Real.tan_eq_sin_div_cos (2 * θ)).symm,
    ← diagOp_const_pair (EuclideanSpace.basisFun (Fin 2) 𝕜) (Real.tan (2 * θ))]
  simpa [abs_of_nonneg htan] using
    singularValues_diagOp_fin_two (𝕜 := 𝕜) finrank_euclideanSpace_fin
      (EuclideanSpace.basisFun (Fin 2) 𝕜) htan htan le_rfl

private theorem singularValues_modelSinTwoThetaPerturbation
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
      pairSingularValues (((b - a) / 2) * Real.sin (2 * θ))
        (((b - a) / 2) * Real.sin (2 * θ)) := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hprod : 0 ≤ ((b-a)/2) * Real.sin (2*θ) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hab.le) (by norm_num)) hsin
  have habs1 : |(a - b) / 2| = (b - a) / 2 := by
    rw [abs_of_nonpos (by linarith : (a - b) / 2 ≤ 0)]
    ring
  have habs2 : |Real.sin (2 * θ)| = Real.sin (2 * θ) := abs_of_nonneg hsin
  simpa [modelSinTwoThetaPerturbation, habs1, habs2, abs_of_nonneg hprod]
    using
    singularValues_offDiagonal_two_by_two (𝕜 := 𝕜)
      (((a-b)/2) * Real.sin (2*θ))

private theorem singularValues_modelTanTwoThetaPerturbation
    {a b θ : ℝ} (hab : a < b) (htan : 0 ≤ Real.tan (2 * θ)) :
    (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
      pairSingularValues (((b - a) / 2) * Real.tan (2 * θ))
        (((b - a) / 2) * Real.tan (2 * θ)) := by
  have hprod : 0 ≤ ((b-a)/2) * Real.tan (2*θ) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hab.le) (by norm_num)) htan
  simpa [modelTanTwoThetaPerturbation, abs_of_nonneg hprod] using
    singularValues_offDiagonal_two_by_two (𝕜 := 𝕜)
      (((b-a)/2) * Real.tan (2*θ))

private theorem singularValues_modelTanThetaPerturbation
    {a b θ : ℝ} (hab : a < b) (htan : 0 ≤ Real.tan θ) :
    (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
      pairSingularValues ((b-a) * Real.tan θ) ((b-a) * Real.tan θ) := by
  have hprod : 0 ≤ (b-a) * Real.tan θ :=
    mul_nonneg (sub_nonneg.mpr hab.le) htan
  simpa [modelTanThetaPerturbation, abs_of_nonneg hprod] using
    singularValues_offDiagonal_two_by_two (𝕜 := 𝕜) ((b-a) * Real.tan θ)

/-- The model subspaces have exactly the prescribed principal angle.

Lean proof route for a weaker agent:

1. Write the two normalized spanning vectors explicitly, compute the single overlap singular
  value `|cos θ|`, and use the angle-range hypotheses to simplify `arccos`.
2. Prove the overlap scalar is nonnegative on `[0,π/2]`, so the absolute value disappears.
3. Rewrite the first principal angle with `Real.arccos_cos` and the supplied range bounds.
-/
theorem principalAngles_model (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    principalAngles (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ) 0 = θ := by
  rw [principalAngles]
  change Real.arcsin
      ((sinThetaMap (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues 0) = θ
  rw [singularValues_sinThetaMap_model hθ0 hθ1]
  simp only [pairSingularValues_zero]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) hθ1

/-- The scalar gap is a positive real, so its field norm is itself.  The
singular-value comparisons need this to discharge the `‖b - a‖` that
`singularValues_smul` introduces. -/
private theorem norm_ofReal_sub_of_lt {a b : ℝ} (hab : a < b) :
    ‖((b : 𝕜) - (a : 𝕜))‖ = b - a := by
  rw [← RCLike.ofReal_sub, RCLike.norm_ofReal, abs_of_pos (sub_pos.mpr hab)]

/-- Equality case for the `sin Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by
  -two matrices, their singular values, the gap, and the relevant angle function explicitly;
    equality should reduce to a scalar trigonometric identity.

Signature audit: The theorem now uses a dedicated `sin Θ` perturbation model; do not reuse it
for the tangent or double-angle families.
-/
theorem sinTheta_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (b - a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      N (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  have hsing :
      (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
        ((b-a : 𝕜) • sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues := by
    rw [singularValues_modelSinThetaPerturbation hab hθ0 (le_of_lt hθ1),
      TauCeti.singularValues_smul,
      singularValues_sinAngle_model hθ0 (le_of_lt hθ1)]
    ext i
    simp [pairSingularValues, norm_ofReal_sub_of_lt hab]
  calc
    (b-a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ))
        = N ((b-a : 𝕜) • sinAngleOperator (modelSubspace (𝕜 := 𝕜))
            (rotatedModelSubspace (𝕜 := 𝕜) θ)) := by
          rw [N.smul_eq, norm_ofReal_sub_of_lt hab]
    _ = N (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ) :=
      N.eq_of_same_singularValues hsing.symm

/-- Equality case for the `tan Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by
  -two matrices, their singular values, the gap, and the relevant angle function explicitly;
    equality should reduce to a scalar trigonometric identity.

Signature audit: The dedicated tangent model must include the zero-compression/Galerkin
hypothesis required by the theorem it saturates.
-/
theorem tanTheta_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (b - a) * N (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      N (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  have htan : 0 ≤ Real.tan θ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ0 hθ1.le
  have hsing :
      (((b - a : ℝ) : 𝕜) • tanAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
        (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues := by
    rw [TauCeti.singularValues_smul,
      singularValues_tanAngle_model hθ0 hθ1,
      singularValues_modelTanThetaPerturbation hab htan]
    ext i
    simp [pairSingularValues, norm_ofReal_sub_of_lt hab]
  calc
    (b - a) * N (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
        N (((b - a : ℝ) : 𝕜) • tanAngleOperator
          (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)) := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_pos (sub_pos.mpr hab)]
    _ = N (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ) :=
      N.eq_of_same_singularValues hsing
/-- Equality case for the `sin 2Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by
  -two matrices, their singular values, the gap, and the relevant angle function explicitly;
    equality should reduce to a scalar trigonometric identity.

Signature audit: The dedicated double-angle model is reflection-compatible and is independent
of the single-angle extremizer.
-/
theorem sinTwoTheta_model_operatorNorm_equality
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (b - a) * ‖(sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ =
      2 * ‖(modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ := by
  rw [opNorm_eq_singularValues_zero (sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) finrank_euclideanSpace_fin (by norm_num),
    opNorm_eq_singularValues_zero (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ)
      finrank_euclideanSpace_fin (by norm_num),
    singularValues_sinTwoAngle_model hθ0 hθ1,
    singularValues_modelSinTwoThetaPerturbation hab hθ0 hθ1]
  simp only [pairSingularValues_zero]
  ring

/-- **The one-sided `sin 2Θ` model equality does not extend past the operator norm.**

`sinTwoAngleOperator U V = 2 P_{Uᗮ} P_V P_U` is supported on `U`, so in a plane with a
one-dimensional `U` it has the single nonzero singular value `sin 2θ`, whereas the extremal
perturbation is a full-rank symmetric off-diagonal block with the two singular values
`((b-a)/2) sin 2θ`.  The two lists are therefore not proportional, and the equality recorded in
`sinTwoTheta_model_operatorNorm_equality` is genuinely restricted to a gauge that reads only the
leading singular value.  The Ky Fan `2` gauge separates the two sides by exactly the factor two
carried by the rank mismatch.

This refutes, for the model of this file, any statement of the form
`(b - a) * N (sinTwoAngleOperator …) = 2 * N (modelSinTwoThetaPerturbation …)` quantified over
all unitarily invariant seminorms `N`.  The correct all-seminorm statement replaces the
one-sided map by the symmetric sine of the doubled angle: see `sinTwoTheta_model_equality`. -/
theorem sinTwoTheta_model_equality_fails_beyond_operatorNorm
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi / 4) :
    ∃ N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜),
      (b - a) * N (sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)) ≠
        2 * N (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  refine ⟨(UnitarilyInvariantSeminorm.kyFan
    (𝕜 := 𝕜) (E := Plane 𝕜) (F := Plane 𝕜) 2), ?_⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hL : (UnitarilyInvariantSeminorm.kyFan
        (𝕜 := 𝕜) (E := Plane 𝕜) (F := Plane 𝕜) 2)
      (sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) = Real.sin (2 * θ) := by
    change TauCeti.kyFanSum 2 _ = _
    rw [TauCeti.kyFanSum,
      singularValues_sinTwoAngle_model hθ0.le hθ1]
    simp [Fin.sum_univ_two]
  have hR : (UnitarilyInvariantSeminorm.kyFan
        (𝕜 := 𝕜) (E := Plane 𝕜) (F := Plane 𝕜) 2)
      (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ) = (b - a) * Real.sin (2 * θ) := by
    change TauCeti.kyFanSum 2 _ = _
    rw [TauCeti.kyFanSum,
      singularValues_modelSinTwoThetaPerturbation hab hθ0.le hθ1]
    simp only [Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one,
      pairSingularValues_zero, pairSingularValues_one]
    ring
  rw [hL, hR]
  nlinarith [mul_pos hgap hsin]

/-- **Equality case for the `sin 2Θ` theorem, at every unitarily invariant seminorm.**

The reflection through the rotated line carries `modelSubspace` to
`rotatedModelSubspace (2θ)`, so the symmetric sine of the doubled angle is the
gauge-faithful double-angle operator of this model: it has the *two* singular values
`sin 2θ`, matching the rank of the extremal perturbation.  Both sides are then the same
symmetric gauge applied to the same singular-value list, which is exactly the paper's reason
for stating equality at arbitrary unitarily invariant norms.

`norm_sinTwoAngle_model_eq_norm_sinAngle_doubled` identifies the left-hand operator with the
one-sided `sinTwoAngleOperator` at the operator norm, recovering
`sinTwoTheta_model_operatorNorm_equality`; beyond the operator norm the one-sided map cannot
attain equality, by `sinTwoTheta_model_equality_fails_beyond_operatorNorm`. -/
theorem sinTwoTheta_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (b - a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ))) =
      2 * N (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  have hsing :
      (((b - a : ℝ) : 𝕜) • sinAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ))).singularValues =
        (((2 : ℝ) : 𝕜) • modelSinTwoThetaPerturbation
          (𝕜 := 𝕜) a b θ).singularValues := by
    rw [TauCeti.singularValues_smul,
      TauCeti.singularValues_smul,
      singularValues_sinAngle_model (𝕜 := 𝕜) (by linarith) (by linarith),
      singularValues_modelSinTwoThetaPerturbation hab hθ0 hθ1]
    have h2 : ‖((2 : ℝ) : 𝕜)‖ = 2 := by
      rw [RCLike.norm_ofReal]; norm_num
    have hba : ‖((b - a : ℝ) : 𝕜)‖ = b - a := by
      rw [RCLike.norm_ofReal, abs_of_pos (sub_pos.mpr hab)]
    ext i
    simp only [pairSingularValues, h2, hba, Finsupp.smul_apply,
      Finsupp.add_apply, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> ring
  calc
    (b - a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ))) =
        N (((b - a : ℝ) : 𝕜) • sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ))) := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_pos (sub_pos.mpr hab)]
    _ = N (((2 : ℝ) : 𝕜) • modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ) :=
      N.eq_of_same_singularValues hsing
    _ = 2 * N (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
      rw [N.smul_eq]
      norm_num
/-- The one-sided double-angle map and the symmetric sine of the doubled angle have the same
operator norm in the planar model: both read off the leading singular value `sin 2θ`.  This is
the planar instance of the general identity between the one-sided `sin 2Θ` map and the sine of
the angle to the reflected subspace. -/
theorem norm_sinTwoAngle_model_eq_norm_sinAngle_doubled
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    ‖(sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ =
      ‖(sinAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ))).toContinuousLinearMap‖ := by
  rw [opNorm_eq_singularValues_zero (sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) finrank_euclideanSpace_fin (by norm_num),
    opNorm_eq_singularValues_zero (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ))) finrank_euclideanSpace_fin (by norm_num),
    singularValues_sinTwoAngle_model hθ0 hθ1,
    singularValues_sinAngle_model (𝕜 := 𝕜) (by linarith) (by linarith)]
  simp only [pairSingularValues_zero]

/-- Equality case for the `tan 2Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by
  -two matrices, their singular values, the gap, and the relevant angle function explicitly;
    equality should reduce to a scalar trigonometric identity.
-/
theorem tanTwoTheta_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 4) :
    (b - a) * N (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      2 * N (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  have htan : 0 ≤ Real.tan (2 * θ) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
  have hsing :
      (((b - a : ℝ) : 𝕜) • tanTwoAngleOperator
        (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
        (((2 : ℝ) : 𝕜) • modelTanTwoThetaPerturbation
          (𝕜 := 𝕜) a b θ).singularValues := by
    rw [TauCeti.singularValues_smul,
      TauCeti.singularValues_smul,
      singularValues_tanTwoAngle_model hθ0 hθ1,
      singularValues_modelTanTwoThetaPerturbation hab htan]
    have h2 : ‖((2 : ℝ) : 𝕜)‖ = 2 := by
      rw [RCLike.norm_ofReal]; norm_num
    have hba : ‖((b - a : ℝ) : 𝕜)‖ = b - a := by
      rw [RCLike.norm_ofReal, abs_of_pos (sub_pos.mpr hab)]
    -- simp normalizes to `θ * 2`, so orient the rewrite that way
    have htcomm : Real.tan (2 * θ) = Real.tan (θ * 2) := by rw [mul_comm]
    ext i
    simp only [pairSingularValues, h2, hba,
      htcomm, Finsupp.smul_apply,
      Finsupp.add_apply, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> ring
  calc
    (b - a) * N (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
        N (((b - a : ℝ) : 𝕜) • tanTwoAngleOperator
          (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)) := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_pos (sub_pos.mpr hab)]
    _ = N (((2 : ℝ) : 𝕜) • modelTanTwoThetaPerturbation
          (𝕜 := 𝕜) a b θ) :=
      N.eq_of_same_singularValues hsing
    _ = 2 * N (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
      rw [N.smul_eq]
      norm_num
/-- The constant one in the single-angle theorems cannot be decreased.

Lean proof route for a weaker agent:

1. Instantiate the corrected planar equality model at any nonzero admissible angle and use `c <
  1` or `c < 2` to obtain the strict counterexample to a smaller universal constant.
2. Choose explicit `a<b` and `0<θ<π/2`, then invoke `sinTheta_model_equality` for the operator norm.
3. Multiply the strict inequality `c<1` by the positive perturbation norm.
-/
theorem sinTheta_constant_optimal :
    ∀ c : ℝ, c < 1 → ∃ (a b θ : ℝ), a < b ∧ 0 < θ ∧
      c * ‖(modelSinThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ <
        (b - a) * ‖(sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ := by
  intro c hc
  refine ⟨0, 1, Real.pi / 6, by norm_num, by positivity, ?_⟩
  have heq := sinTheta_model_equality
    (UnitarilyInvariantSeminorm.opNorm (𝕜 := 𝕜) (E := (Plane 𝕜)) (F := (Plane 𝕜)))
    (𝕜 := 𝕜) (a := 0) (b := 1) (θ := Real.pi/6)
    (by norm_num) (by positivity) (by linarith [Real.pi_pos])
  -- read the norm off the singular values rather than off a component
  have hpos : 0 < ‖(modelSinThetaPerturbation (𝕜 := 𝕜) 0 1
      (Real.pi/6)).toContinuousLinearMap‖ := by
    rw [opNorm_eq_singularValues_zero _ finrank_euclideanSpace_fin
        (by norm_num),
      singularValues_modelSinThetaPerturbation (𝕜 := 𝕜) (by norm_num)
        (by positivity) (by linarith [Real.pi_pos]),
      pairSingularValues_zero, Real.sin_pi_div_six]
    norm_num
  -- `opNorm` is definitionally the continuous-map norm
  have hgoal : (1 - 0 : ℝ) * ‖(sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) (Real.pi/6))).toContinuousLinearMap‖
      = ‖(modelSinThetaPerturbation (𝕜 := 𝕜) 0 1
        (Real.pi/6)).toContinuousLinearMap‖ := heq
  rw [hgoal]
  exact mul_lt_of_lt_one_left hpos hc
/-- The factor two in the double-angle theorems cannot be decreased.

Lean proof route for a weaker agent:

1. Instantiate the corrected planar equality model at any nonzero admissible angle and use `c <
  1` or `c < 2` to obtain the strict counterexample to a smaller universal constant.
2. Choose an angle with nonzero double-angle map and invoke
  `sinTwoTheta_model_operatorNorm_equality`.
3. Multiply `c<2` by the positive perturbation norm and rewrite the equality.
-/
theorem sinTwoTheta_constant_optimal :
    ∀ c : ℝ, c < 2 → ∃ (a b θ : ℝ), a < b ∧ 0 < θ ∧
      c * ‖(modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ <
        (b - a) * ‖(sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ := by
  intro c hc
  refine ⟨0, 1, Real.pi / 8, by norm_num, by positivity, ?_⟩
  have heq := sinTwoTheta_model_operatorNorm_equality
    (𝕜 := 𝕜) (a := 0) (b := 1) (θ := Real.pi/8)
    (by norm_num) (by positivity) (by linarith [Real.pi_pos])
  have hpos : 0 < ‖(modelSinTwoThetaPerturbation (𝕜 := 𝕜) 0 1
      (Real.pi/8)).toContinuousLinearMap‖ := by
    rw [opNorm_eq_singularValues_zero _ finrank_euclideanSpace_fin
        (by norm_num),
      singularValues_modelSinTwoThetaPerturbation (𝕜 := 𝕜) (by norm_num)
        (by positivity) (by linarith [Real.pi_pos]),
      pairSingularValues_zero]
    have hs : 0 < Real.sin (2 * (Real.pi / 8)) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [Real.pi_pos]
    nlinarith
  nlinarith
/-- **The constant one in the `tan Theta` theorem cannot be decreased.**

The `sin Theta` and `sin 2Theta` families had their constants pinned above; this
and the next theorem complete the source's assertion that the constants in *all
four* families are best possible.  The route is the same: instantiate the
tangent equality model at one explicit admissible angle, where the residual has
strictly positive operator norm, and multiply the strict inequality `c < 1`
through. -/
theorem tanTheta_constant_optimal :
    ∀ c : ℝ, c < 1 → ∃ (a b θ : ℝ), a < b ∧ 0 < θ ∧
      c * ‖(modelTanThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ <
        (b - a) * ‖(tanAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ := by
  intro c hc
  refine ⟨0, 1, Real.pi / 6, by norm_num, by positivity, ?_⟩
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have heq := tanTheta_model_equality
    (UnitarilyInvariantSeminorm.opNorm (𝕜 := 𝕜) (E := (Plane 𝕜)) (F := (Plane 𝕜)))
    (𝕜 := 𝕜) (a := 0) (b := 1) (θ := Real.pi / 6)
    (by norm_num) (by positivity) (by linarith)
  have htan : 0 < Real.tan (Real.pi / 6) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by linarith)
  have hpos : 0 < ‖(modelTanThetaPerturbation (𝕜 := 𝕜) 0 1
      (Real.pi / 6)).toContinuousLinearMap‖ := by
    rw [opNorm_eq_singularValues_zero _ finrank_euclideanSpace_fin (by norm_num),
      singularValues_modelTanThetaPerturbation (𝕜 := 𝕜) (by norm_num) htan.le,
      pairSingularValues_zero]
    nlinarith
  have hgoal : (1 - 0 : ℝ) * ‖(tanAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) (Real.pi / 6))).toContinuousLinearMap‖
      = ‖(modelTanThetaPerturbation (𝕜 := 𝕜) 0 1
        (Real.pi / 6)).toContinuousLinearMap‖ := heq
  rw [hgoal]
  exact mul_lt_of_lt_one_left hpos hc
/-- **The factor two in the `tan 2Theta` theorem cannot be decreased.** -/
theorem tanTwoTheta_constant_optimal :
    ∀ c : ℝ, c < 2 → ∃ (a b θ : ℝ), a < b ∧ 0 < θ ∧
      c * ‖(modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ <
        (b - a) * ‖(tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ := by
  intro c hc
  refine ⟨0, 1, Real.pi / 8, by norm_num, by positivity, ?_⟩
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have heq := tanTwoTheta_model_equality
    (UnitarilyInvariantSeminorm.opNorm (𝕜 := 𝕜) (E := (Plane 𝕜)) (F := (Plane 𝕜)))
    (𝕜 := 𝕜) (a := 0) (b := 1) (θ := Real.pi / 8)
    (by norm_num) (by positivity) (by linarith)
  have htan : 0 < Real.tan (2 * (Real.pi / 8)) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by linarith)
  have hpos : 0 < ‖(modelTanTwoThetaPerturbation (𝕜 := 𝕜) 0 1
      (Real.pi / 8)).toContinuousLinearMap‖ := by
    rw [opNorm_eq_singularValues_zero _ finrank_euclideanSpace_fin (by norm_num),
      singularValues_modelTanTwoThetaPerturbation (𝕜 := 𝕜) (by norm_num) htan.le,
      pairSingularValues_zero]
    nlinarith
  have hgoal : (1 - 0 : ℝ) * ‖(tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) (Real.pi / 8))).toContinuousLinearMap‖
      = 2 * ‖(modelTanTwoThetaPerturbation (𝕜 := 𝕜) 0 1
        (Real.pi / 8)).toContinuousLinearMap‖ := heq
  rw [hgoal]
  nlinarith

/-!
The former `directSum_models_simultaneous_equality` declaration was false: the
one-sided `sinTwoAngleOperator` contributes one nonzero singular value per
principal plane, whereas the symmetric off-diagonal perturbation contributes
two.  That rank mismatch is now a theorem rather than a remark --
`sinTwoTheta_model_equality_fails_beyond_operatorNorm` exhibits a gauge separating the two
sides -- and the rank-matched replacement is `sinTwoTheta_model_equality`, which measures the
double angle by the symmetric sine of the doubled angle, the sine of the angle to the subspace
reflected through the rotated line.  The operator-norm sharpness result above remains the
correct endpoint for the one-sided map, by
`norm_sinTwoAngle_model_eq_norm_sinAngle_doubled`.
-/

/-! ## Simultaneous equality and finite orthogonal direct sums -/

/-- **All four theorem conclusions attain equality at one planar configuration, for every
unitarily invariant seminorm at once.**

The configuration is the single pair of lines `modelSubspace`, `rotatedModelSubspace θ`; each
family is saturated by its own extremal residual, which is what the source's four *independent*
inequalities require.  Note that the four residuals are genuinely different operators: no
single perturbation saturates all four, since the extremal residual norms
`(b-a) sin θ`, `(b-a) tan θ`, `((b-a)/2) sin 2θ` and `((b-a)/2) tan 2θ` differ off `θ = 0`. -/
theorem model_all_four_equalities
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 4) :
    (b - a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
        N (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ) ∧
      (b - a) * N (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
        N (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ) ∧
      (b - a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ))) =
        2 * N (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ) ∧
      (b - a) * N (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
        2 * N (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) :=
  ⟨sinTheta_model_equality N hab hθ0 (by linarith [Real.pi_pos]),
   tanTheta_model_equality N hab hθ0 (by linarith [Real.pi_pos]),
   sinTwoTheta_model_equality N hab hθ0 hθ1.le,
   tanTwoTheta_model_equality N hab hθ0 hθ1⟩

/-- A scalar multiple of an operator with a constant planar singular pair has the singular
values of the correspondingly scaled pair.  This is the one computation the four direct-sum
transfers below share. -/
private theorem singularValues_smul_of_pair_eq
    {E' F' : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F']
    {S P : E' →ₗ[𝕜] F'} {c s : ℝ} (hc : 0 ≤ c)
    (hS : S.singularValues = pairSingularValues s s)
    (hP : P.singularValues = pairSingularValues (c * s) (c * s)) :
    (((c : ℝ) : 𝕜) • S).singularValues = P.singularValues := by
  rw [TauCeti.singularValues_smul, hS, hP,
    RCLike.norm_ofReal, abs_of_nonneg hc]
  ext i
  simp only [pairSingularValues, Finsupp.smul_apply, Finsupp.add_apply,
    Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> ring

/-- **The `sin Θ` equality survives an orthogonal direct sum of two planes with independent
angles, at every unitarily invariant seminorm.**

The two blocks may carry different angles, so the common singular-value list of the two sides
is an arbitrary four-term list; that is the source's "direct sums realize any finite
singular-value list".  No merge formula for the two sorted lists is needed --
`singularValues_orthogonalBlockSum_congr` transfers the blockwise proportionality directly. -/
theorem sinTheta_directSum_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) (WithLp 2 (Plane 𝕜 × Plane 𝕜)))
    {a b θ₁ θ₂ : ℝ} (hab : a < b) (h₁0 : 0 ≤ θ₁) (h₁1 : θ₁ ≤ Real.pi / 2)
    (h₂0 : 0 ≤ θ₂) (h₂1 : θ₂ ≤ Real.pi / 2) :
    (b - a) * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (sinAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₁))
        (sinAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₂))) =
      N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ₁)
        (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ₂)) :=
  UnitarilyInvariantSeminorm.apply_orthogonalBlockSum_eq_of_singularValues_smul_eq
    N (sub_pos.mpr hab).le
    (singularValues_smul_of_pair_eq (sub_pos.mpr hab).le
      (singularValues_sinAngle_model h₁0 h₁1)
      (singularValues_modelSinThetaPerturbation hab h₁0 h₁1))
    (singularValues_smul_of_pair_eq (sub_pos.mpr hab).le
      (singularValues_sinAngle_model h₂0 h₂1)
      (singularValues_modelSinThetaPerturbation hab h₂0 h₂1))

/-- The `tan Θ` equality on an orthogonal direct sum of two planes with independent angles, at
every unitarily invariant seminorm. -/
theorem tanTheta_directSum_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) (WithLp 2 (Plane 𝕜 × Plane 𝕜)))
    {a b θ₁ θ₂ : ℝ} (hab : a < b) (h₁0 : 0 ≤ θ₁) (h₁1 : θ₁ < Real.pi / 2)
    (h₂0 : 0 ≤ θ₂) (h₂1 : θ₂ < Real.pi / 2) :
    (b - a) * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₁))
        (tanAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₂))) =
      N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ₁)
        (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ₂)) :=
  UnitarilyInvariantSeminorm.apply_orthogonalBlockSum_eq_of_singularValues_smul_eq
    N (sub_pos.mpr hab).le
    (singularValues_smul_of_pair_eq (sub_pos.mpr hab).le
      (singularValues_tanAngle_model h₁0 h₁1)
      (singularValues_modelTanThetaPerturbation hab
        (Real.tan_nonneg_of_nonneg_of_le_pi_div_two h₁0 h₁1.le)))
    (singularValues_smul_of_pair_eq (sub_pos.mpr hab).le
      (singularValues_tanAngle_model h₂0 h₂1)
      (singularValues_modelTanThetaPerturbation hab
        (Real.tan_nonneg_of_nonneg_of_le_pi_div_two h₂0 h₂1.le)))

/-- The `sin 2Θ` equality on an orthogonal direct sum of two planes with independent angles, at
every unitarily invariant seminorm.  As in the plane, the double angle is measured by the
symmetric sine of the doubled angle. -/
theorem sinTwoTheta_directSum_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) (WithLp 2 (Plane 𝕜 × Plane 𝕜)))
    {a b θ₁ θ₂ : ℝ} (hab : a < b) (h₁0 : 0 ≤ θ₁) (h₁1 : θ₁ ≤ Real.pi / 4)
    (h₂0 : 0 ≤ θ₂) (h₂1 : θ₂ ≤ Real.pi / 4) :
    (b - a) * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ₁)))
        (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ₂)))) =
      2 * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ₁)
        (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ₂)) := by
  have hc : (0 : ℝ) ≤ (b - a) / 2 := by linarith [sub_pos.mpr hab]
  have h :=
    UnitarilyInvariantSeminorm.apply_orthogonalBlockSum_eq_of_singularValues_smul_eq
      N hc
      (singularValues_smul_of_pair_eq hc
        (singularValues_sinAngle_model (𝕜 := 𝕜) (by linarith) (by linarith))
        (singularValues_modelSinTwoThetaPerturbation hab h₁0 h₁1))
      (singularValues_smul_of_pair_eq hc
        (singularValues_sinAngle_model (𝕜 := 𝕜) (by linarith) (by linarith))
        (singularValues_modelSinTwoThetaPerturbation hab h₂0 h₂1))
  linarith

/-- The `tan 2Θ` equality on an orthogonal direct sum of two planes with independent angles, at
every unitarily invariant seminorm. -/
theorem tanTwoTheta_directSum_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) (WithLp 2 (Plane 𝕜 × Plane 𝕜)))
    {a b θ₁ θ₂ : ℝ} (hab : a < b) (h₁0 : 0 ≤ θ₁) (h₁1 : θ₁ < Real.pi / 4)
    (h₂0 : 0 ≤ θ₂) (h₂1 : θ₂ < Real.pi / 4) :
    (b - a) * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₁))
        (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₂))) =
      2 * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ₁)
        (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ₂)) := by
  have hc : (0 : ℝ) ≤ (b - a) / 2 := by linarith [sub_pos.mpr hab]
  have h :=
    UnitarilyInvariantSeminorm.apply_orthogonalBlockSum_eq_of_singularValues_smul_eq
      N hc
      (singularValues_smul_of_pair_eq hc
        (singularValues_tanTwoAngle_model h₁0 h₁1)
        (singularValues_modelTanTwoThetaPerturbation hab
          (Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))))
      (singularValues_smul_of_pair_eq hc
        (singularValues_tanTwoAngle_model h₂0 h₂1)
        (singularValues_modelTanTwoThetaPerturbation hab
          (Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))))
  linarith

/-- **All four conclusions attain equality simultaneously on one finite orthogonal direct sum,
for every unitarily invariant seminorm.**

The two planes carry independent angles `θ₁, θ₂`, so the realized singular-value lists are not
proportional to a single plane's; iterating the construction realizes any finite list.  This is
the printed Section 2 assertion, with the double-angle family measured by the symmetric sine of
the doubled angle, the normalization forced by
`sinTwoTheta_model_equality_fails_beyond_operatorNorm`. -/
theorem directSum_model_all_four_equalities
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) (WithLp 2 (Plane 𝕜 × Plane 𝕜)))
    {a b θ₁ θ₂ : ℝ} (hab : a < b) (h₁0 : 0 ≤ θ₁) (h₁1 : θ₁ < Real.pi / 4)
    (h₂0 : 0 ≤ θ₂) (h₂1 : θ₂ < Real.pi / 4) :
    ((b - a) * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (sinAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₁))
        (sinAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₂))) =
        N (UnitarilyInvariantSeminorm.orthogonalBlockSum
          (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ₁)
          (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ₂))) ∧
      ((b - a) * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₁))
        (tanAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₂))) =
        N (UnitarilyInvariantSeminorm.orthogonalBlockSum
          (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ₁)
          (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ₂))) ∧
      ((b - a) * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ₁)))
        (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ₂)))) =
        2 * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
          (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ₁)
          (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ₂))) ∧
      ((b - a) * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₁))
        (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₂))) =
        2 * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
          (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ₁)
          (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ₂))) :=
  ⟨sinTheta_directSum_model_equality N hab h₁0 (by linarith [Real.pi_pos])
      h₂0 (by linarith [Real.pi_pos]),
   tanTheta_directSum_model_equality N hab h₁0 (by linarith [Real.pi_pos])
      h₂0 (by linarith [Real.pi_pos]),
   sinTwoTheta_directSum_model_equality N hab h₁0 h₁1.le h₂0 h₂1.le,
   tanTwoTheta_directSum_model_equality N hab h₁0 h₁1 h₂0 h₂1⟩


/-- To first order in a linear perturbation parameter, all four theorem
conclusions agree.

Signature audit: The theorem has been renamed to match its scalar content.  The operator-level
first-order comparison should be a separate corollary of the four planar equality theorems.
-/
theorem single_double_sine_tangent_ratios_tendsto_one :
    Tendsto (fun θ : ℝ => Real.sin θ / Real.tan θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
    Tendsto (fun θ : ℝ => Real.sin (2 * θ) / Real.tan (2 * θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have base : Tendsto (fun θ : ℝ => Real.sin θ / Real.tan θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hcos : Tendsto (fun θ : ℝ => Real.cos θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have h : Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.cos 0)) :=
        (Real.continuous_cos.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      rw [← Set.Ioi_inter_Iio]
      exact inter_mem_nhdsWithin _ (Iio_mem_nhds Real.pi_div_two_pos)
    refine hcos.congr' ?_
    filter_upwards [hmem] with θ hθ
    have hsin : Real.sin θ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos, hθ.2]))
    rw [Real.tan_eq_sin_div_cos, div_div_eq_mul_div,
      mul_comm (Real.sin θ) (Real.cos θ), mul_div_assoc, div_self hsin, mul_one]
  refine ⟨base, ?_⟩
  have h2 : Tendsto (fun θ : ℝ => 2 * θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun θ : ℝ => 2 * θ) := continuous_const.mul continuous_id
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ (hθ : (0 : ℝ) < θ)
      exact mul_pos two_pos hθ
  exact base.comp h2

/-! ## Admissible operator pairs behind the planar models

Every `*_model_equality` above compares an angle operator with an *explicitly given matrix*.  On
its own that is an identity between two matrices, not sharpness of a theorem: a theorem's
constant is shown optimal only once the matrix on the right is exhibited as the residual `B - A`
of a pair `(A, B)` satisfying that theorem's own hypotheses -- both operators symmetric, the
relevant subspace invariant, and the relevant gap present with the value the constant is
divided by.

This section supplies those pairs.  The frame `uθ θ`, `vθ θ` diagonalizes every perturbed
operator below, so each verification reduces to two eigenvector equations. -/

/-- The unit vector completing `uθ θ` to the rotated orthonormal frame of the plane. -/
noncomputable def vθ (θ : ℝ) : Plane 𝕜 :=
  -(Real.sin θ : 𝕜) • e0 + (Real.cos θ : 𝕜) • e1

private theorem plane_sin_sq_add_cos_sq (θ : ℝ) :
    ((Real.sin θ : 𝕜)) ^ 2 + ((Real.cos θ : 𝕜)) ^ 2 = 1 := by
  have h := congrArg (fun r : ℝ => (r : 𝕜)) (Real.sin_sq_add_cos_sq θ)
  push_cast at h
  exact h

/-- The complementary frame vector is the generator rotated by a further quarter turn.  Stating
it this way transports every `uθ` lemma to `vθ` instead of repeating the computations. -/
theorem vθ_eq_uθ_add_pi_div_two (θ : ℝ) :
    vθ (𝕜 := 𝕜) θ = uθ (𝕜 := 𝕜) (θ + Real.pi / 2) := by
  rw [vθ, uθ, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  push_cast
  module

/-- The complementary frame vector is a unit vector. -/
@[simp] theorem norm_vθ (θ : ℝ) : ‖vθ (𝕜 := 𝕜) θ‖ = 1 := by
  rw [vθ_eq_uθ_add_pi_div_two]
  exact norm_uθ _

/-- Overlap of the complementary frame vector with the first coordinate. -/
@[simp] theorem inner_vθ_e0 (θ : ℝ) :
    ⟪vθ (𝕜 := 𝕜) θ, e0⟫_𝕜 = -(Real.sin θ : 𝕜) := by
  rw [vθ_eq_uθ_add_pi_div_two, inner_uθ_e0, Real.cos_add_pi_div_two]
  push_cast
  ring

/-- Overlap of the complementary frame vector with the second coordinate. -/
@[simp] theorem inner_vθ_e1 (θ : ℝ) :
    ⟪vθ (𝕜 := 𝕜) θ, e1⟫_𝕜 = (Real.cos θ : 𝕜) := by
  rw [vθ_eq_uθ_add_pi_div_two, inner_uθ_e1, Real.sin_add_pi_div_two]

/-- The rotated frame is orthogonal. -/
@[simp] theorem inner_uθ_vθ (θ : ℝ) :
    ⟪uθ (𝕜 := 𝕜) θ, vθ (𝕜 := 𝕜) θ⟫_𝕜 = 0 := by
  simp only [vθ, inner_add_right, inner_smul_right, inner_uθ_e0, inner_uθ_e1]
  ring

/-- The rotated generator is nonzero, which every eigenvector argument below needs. -/
theorem uθ_ne_zero (θ : ℝ) : uθ (𝕜 := 𝕜) θ ≠ 0 := by
  intro h
  have := norm_uθ (𝕜 := 𝕜) θ
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- The complementary frame vector is nonzero. -/
theorem vθ_ne_zero (θ : ℝ) : vθ (𝕜 := 𝕜) θ ≠ 0 := by
  intro h
  have := norm_vθ (𝕜 := 𝕜) θ
  rw [h, norm_zero] at this
  exact zero_ne_one this

private theorem e0_ne_zero : e0 (𝕜 := 𝕜) ≠ 0 := by
  intro h
  have := norm_e0 (𝕜 := 𝕜)
  rw [h, norm_zero] at this
  exact zero_ne_one this

private theorem e1_ne_zero : e1 (𝕜 := 𝕜) ≠ 0 := by
  intro h
  have := norm_e1 (𝕜 := 𝕜)
  rw [h, norm_zero] at this
  exact zero_ne_one this

private theorem orthogonal_span_singleton_plane {u v : Plane 𝕜}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : ⟪u, v⟫_𝕜 = 0) :
    (Submodule.span 𝕜 {u})ᗮ = Submodule.span 𝕜 {v} := by
  have hle : Submodule.span 𝕜 {v} ≤ (Submodule.span 𝕜 {u})ᗮ := by
    rw [Submodule.span_le]
    intro y hy
    have hyv : y = v := by simpa using hy
    subst hyv
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro w hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [inner_smul_left, huv, mul_zero]
  have h1 := Submodule.finrank_add_finrank_orthogonal
    (K := (Submodule.span 𝕜 {u} : Submodule 𝕜 (Plane 𝕜)))
  rw [finrank_span_singleton hu, finrank_euclideanSpace_fin] at h1
  have hrank : Module.finrank 𝕜 (Submodule.span 𝕜 {v} : Submodule 𝕜 (Plane 𝕜)) =
      Module.finrank 𝕜 ((Submodule.span 𝕜 {u} : Submodule 𝕜 (Plane 𝕜))ᗮ) := by
    rw [finrank_span_singleton hv]
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hrank).symm

/-- The orthogonal complement of the coordinate line is the second coordinate line. -/
theorem orthogonal_modelSubspace :
    (modelSubspace (𝕜 := 𝕜))ᗮ = Submodule.span 𝕜 {e1 (𝕜 := 𝕜)} :=
  orthogonal_span_singleton_plane e0_ne_zero e1_ne_zero inner_e0_e1

/-- The orthogonal complement of the rotated line is spanned by the complementary frame
vector. -/
theorem orthogonal_rotatedModelSubspace (θ : ℝ) :
    (rotatedModelSubspace (𝕜 := 𝕜) θ)ᗮ = Submodule.span 𝕜 {vθ (𝕜 := 𝕜) θ} :=
  orthogonal_span_singleton_plane (uθ_ne_zero θ) (vθ_ne_zero θ) (inner_uθ_vθ θ)

private theorem isInvariant_span_singleton {A : Plane 𝕜 →ₗ[𝕜] Plane 𝕜} {u : Plane 𝕜}
    {lam : ℝ} (h : A u = (lam : 𝕜) • u) :
    IsInvariant A (Submodule.span 𝕜 {u}) := by
  intro x hx
  rw [Submodule.mem_span_singleton] at hx ⊢
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c * (lam : 𝕜), by rw [map_smul, h, smul_smul, mul_comm]⟩

private theorem restrictedPointSpectrum_span_singleton_subset {A : Plane 𝕜 →ₗ[𝕜] Plane 𝕜}
    {u : Plane 𝕜} (hu : u ≠ 0) {lam : ℝ} (h : A u = (lam : 𝕜) • u) :
    restrictedPointSpectrum A (Submodule.span 𝕜 {u}) ⊆ {lam} := by
  intro μ hμ
  rw [mem_restrictedPointSpectrum_iff] at hμ
  obtain ⟨x, hxU, hx0, hxeq⟩ := hμ
  rw [Submodule.mem_span_singleton] at hxU
  obtain ⟨c, rfl⟩ := hxU
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx0 (by simp)
  rw [map_smul, h, smul_smul, smul_smul] at hxeq
  have hzero : (c * (lam : 𝕜) - (μ : 𝕜) * c) • u = 0 := by
    rw [sub_smul, hxeq, sub_self]
  rcases smul_eq_zero.mp hzero with hscal | hu0
  · have hfac : c * ((lam : 𝕜) - (μ : 𝕜)) = 0 := by linear_combination hscal
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact absurd h' hc
    · exact (RCLike.ofReal_injective (K := 𝕜) (sub_eq_zero.mp h')).symm
  · exact absurd hu0 hu

private theorem re_inner_span_singleton {A : Plane 𝕜 →ₗ[𝕜] Plane 𝕜} {u : Plane 𝕜}
    (hu : ‖u‖ = 1) {lam : ℝ} (h : A u = (lam : 𝕜) • u)
    {x : Plane 𝕜} (hx : x ∈ Submodule.span 𝕜 {u}) :
    RCLike.re ⟪A x, x⟫_𝕜 = lam * ‖x‖ ^ 2 := by
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  have huu : ⟪u, u⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  rw [map_smul, h, inner_smul_left, inner_smul_left, inner_smul_right, huu, norm_smul, hu]
  simp only [mul_one, RCLike.conj_ofReal]
  rw [show (starRingEnd 𝕜) c * ((lam : 𝕜) * c) = (lam : 𝕜) * ((starRingEnd 𝕜) c * c) by ring,
    RCLike.conj_mul, RCLike.re_ofReal_mul]
  simp

/-! ### The `sin Θ` model as an admissible perturbation pair -/

private theorem modelGappedOperator_eq_matrix (a b : ℝ) :
    modelGappedOperator (𝕜 := 𝕜) a b =
      Matrix.toEuclideanLin !![((a : ℝ) : 𝕜), 0; 0, ((b : ℝ) : 𝕜)] := by
  rw [modelGappedOperator]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The gapped model operator is symmetric. -/
theorem modelGappedOperator_isSymmetric (a b : ℝ) :
    (modelGappedOperator (𝕜 := 𝕜) a b).IsSymmetric := by
  rw [modelGappedOperator_eq_matrix]
  refine Matrix.isSymmetric_toEuclideanLin_iff.mpr ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, RCLike.conj_ofReal]

/-- The first coordinate is the low eigenvector of the gapped model operator. -/
@[simp] theorem modelGappedOperator_apply_e0 (a b : ℝ) :
    modelGappedOperator (𝕜 := 𝕜) a b (e0 (𝕜 := 𝕜)) = ((a : ℝ) : 𝕜) • e0 := by
  rw [modelGappedOperator_eq_matrix]
  ext i
  fin_cases i <;> simp [e0, Matrix.toLpLin_apply]
  all_goals simp only [RCLike.real_smul_eq_coe_mul, mul_one]

/-- The second coordinate is the high eigenvector of the gapped model operator. -/
@[simp] theorem modelGappedOperator_apply_e1 (a b : ℝ) :
    modelGappedOperator (𝕜 := 𝕜) a b (e1 (𝕜 := 𝕜)) = ((b : ℝ) : 𝕜) • e1 := by
  rw [modelGappedOperator_eq_matrix]
  ext i
  fin_cases i <;> simp [e1, Matrix.toLpLin_apply]
  all_goals simp only [RCLike.real_smul_eq_coe_mul, mul_one]

/-- The gapped model operator in the rotated frame: a diagonal entry and the off-diagonal entry
`(b - a) sin θ cos θ` that every tangent and double-angle model has to cancel. -/
theorem modelGappedOperator_apply_uθ (a b θ : ℝ) :
    modelGappedOperator (𝕜 := 𝕜) a b (uθ (𝕜 := 𝕜) θ) =
      ((a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2 : ℝ) : 𝕜) • uθ (𝕜 := 𝕜) θ +
        (((b - a) * Real.sin θ * Real.cos θ : ℝ) : 𝕜) • vθ (𝕜 := 𝕜) θ := by
  have hpy := plane_sin_sq_add_cos_sq (𝕜 := 𝕜) θ
  rw [modelGappedOperator_eq_matrix]
  ext i
  fin_cases i <;>
    simp [uθ, vθ, e0, e1, Matrix.toLpLin_apply] <;>
    (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]) <;>
    first
      | ring1
      | linear_combination ((a : 𝕜) * (Real.cos θ : 𝕜)) * hpy
      | linear_combination (-((a : 𝕜) * (Real.cos θ : 𝕜))) * hpy
      | linear_combination ((a : 𝕜) * (Real.sin θ : 𝕜)) * hpy
      | linear_combination (-((a : 𝕜) * (Real.sin θ : 𝕜))) * hpy
      | linear_combination ((b : 𝕜) * (Real.cos θ : 𝕜)) * hpy
      | linear_combination (-((b : 𝕜) * (Real.cos θ : 𝕜))) * hpy
      | linear_combination ((b : 𝕜) * (Real.sin θ : 𝕜)) * hpy
      | linear_combination (-((b : 𝕜) * (Real.sin θ : 𝕜))) * hpy

/-- The rotation conjugate `R(θ) diag(a, b) R(θ)ᵀ` of the gapped model operator.  This is the
second operator of the `sin Θ` extremal pair: it is symmetric, it leaves `rotatedModelSubspace θ`
invariant, and its difference with `modelGappedOperator a b` is exactly
`modelSinThetaPerturbation a b θ`. -/
noncomputable def modelRotatedOperator (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin
    !![((a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2 : ℝ) : 𝕜),
       (((a - b) * Real.sin θ * Real.cos θ : ℝ) : 𝕜);
       (((a - b) * Real.sin θ * Real.cos θ : ℝ) : 𝕜),
       ((a * Real.sin θ ^ 2 + b * Real.cos θ ^ 2 : ℝ) : 𝕜)]

/-- The rotated model operator is symmetric. -/
theorem modelRotatedOperator_isSymmetric (a b θ : ℝ) :
    (modelRotatedOperator (𝕜 := 𝕜) a b θ).IsSymmetric := by
  rw [modelRotatedOperator]
  refine Matrix.isSymmetric_toEuclideanLin_iff.mpr ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, RCLike.conj_ofReal]

/-- The rotated generator is the low eigenvector of the rotated model operator. -/
theorem modelRotatedOperator_apply_uθ (a b θ : ℝ) :
    modelRotatedOperator (𝕜 := 𝕜) a b θ (uθ (𝕜 := 𝕜) θ) = ((a : ℝ) : 𝕜) • uθ (𝕜 := 𝕜) θ := by
  have hpy := plane_sin_sq_add_cos_sq (𝕜 := 𝕜) θ
  rw [modelRotatedOperator]
  ext i
  fin_cases i <;>
    simp [uθ, e0, e1, Matrix.toLpLin_apply] <;>
    (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]) <;>
    first
      | ring1
      | linear_combination ((a : 𝕜) * (Real.cos θ : 𝕜)) * hpy
      | linear_combination (-((a : 𝕜) * (Real.cos θ : 𝕜))) * hpy
      | linear_combination ((a : 𝕜) * (Real.sin θ : 𝕜)) * hpy

/-- The complementary frame vector is the high eigenvector of the rotated model operator. -/
theorem modelRotatedOperator_apply_vθ (a b θ : ℝ) :
    modelRotatedOperator (𝕜 := 𝕜) a b θ (vθ (𝕜 := 𝕜) θ) = ((b : ℝ) : 𝕜) • vθ (𝕜 := 𝕜) θ := by
  have hpy := plane_sin_sq_add_cos_sq (𝕜 := 𝕜) θ
  rw [modelRotatedOperator]
  ext i
  fin_cases i <;>
    simp [vθ, e0, e1, Matrix.toLpLin_apply] <;>
    (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]) <;>
    first
      | ring1
      | linear_combination ((a : 𝕜) * (Real.cos θ : 𝕜)) * hpy
      | linear_combination (-((a : 𝕜) * (Real.cos θ : 𝕜))) * hpy
      | linear_combination ((a : 𝕜) * (Real.sin θ : 𝕜)) * hpy
      | linear_combination (-((a : 𝕜) * (Real.sin θ : 𝕜))) * hpy
      | linear_combination ((b : 𝕜) * (Real.cos θ : 𝕜)) * hpy
      | linear_combination (-((b : 𝕜) * (Real.cos θ : 𝕜))) * hpy
      | linear_combination ((b : 𝕜) * (Real.sin θ : 𝕜)) * hpy
      | linear_combination (-((b : 𝕜) * (Real.sin θ : 𝕜))) * hpy

/-- **The `sin Θ` model perturbation is a genuine residual.**  It is the difference of the two
symmetric operators of the extremal pair, not merely a matrix with the right singular values. -/
theorem modelRotatedOperator_sub_modelGappedOperator (a b θ : ℝ) :
    modelRotatedOperator (𝕜 := 𝕜) a b θ - modelGappedOperator (𝕜 := 𝕜) a b =
      modelSinThetaPerturbation (𝕜 := 𝕜) a b θ := by
  have hpy := plane_sin_sq_add_cos_sq (𝕜 := 𝕜) θ
  rw [modelRotatedOperator, modelGappedOperator_eq_matrix, modelSinThetaPerturbation,
    ← map_sub]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;>
    (try simp only [RCLike.algebraMap_eq_ofReal]) <;>
    first
      | ring1
      | linear_combination ((a : 𝕜) * (Real.cos θ : 𝕜)) * hpy
      | linear_combination (-((a : 𝕜) * (Real.cos θ : 𝕜))) * hpy
      | linear_combination ((a : 𝕜) * (Real.sin θ : 𝕜)) * hpy
      | linear_combination (-((a : 𝕜) * (Real.sin θ : 𝕜))) * hpy
      | linear_combination ((b : 𝕜) * (Real.cos θ : 𝕜)) * hpy
      | linear_combination (-((b : 𝕜) * (Real.cos θ : 𝕜))) * hpy
      | linear_combination ((b : 𝕜) * (Real.sin θ : 𝕜)) * hpy
      | linear_combination (-((b : 𝕜) * (Real.sin θ : 𝕜))) * hpy
      | linear_combination ((a : 𝕜)) * hpy
      | linear_combination (-(a : 𝕜)) * hpy
      | linear_combination ((b : 𝕜)) * hpy

/-- The coordinate line is invariant under the gapped model operator. -/
theorem isInvariant_modelGappedOperator_modelSubspace (a b : ℝ) :
    IsInvariant (modelGappedOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜)) :=
  isInvariant_span_singleton (lam := a) (modelGappedOperator_apply_e0 a b)

/-- The rotated line is invariant under the rotated model operator. -/
theorem isInvariant_modelRotatedOperator_rotatedModelSubspace (a b θ : ℝ) :
    IsInvariant (modelRotatedOperator (𝕜 := 𝕜) a b θ) (rotatedModelSubspace (𝕜 := 𝕜) θ) :=
  isInvariant_span_singleton (lam := a) (modelRotatedOperator_apply_uθ a b θ)

/-- The interval/exterior gap of the `sin Θ` pair, in the orientation the theorem consumes
first: the selected block of the unperturbed operator against the complementary block of the
perturbed one. -/
theorem intervalExteriorGap_sinTheta_model {a b θ : ℝ} (hab : a < b) :
    PointIntervalExteriorGap (modelGappedOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜))
      (modelRotatedOperator (𝕜 := 𝕜) a b θ) (rotatedModelSubspace (𝕜 := 𝕜) θ)ᗮ a a (b - a) := by
  constructor
  · intro lam hlam
    have h := restrictedPointSpectrum_span_singleton_subset (𝕜 := 𝕜) e0_ne_zero
      (modelGappedOperator_apply_e0 (𝕜 := 𝕜) a b) hlam
    rw [Set.mem_singleton_iff] at h
    subst h
    simp
  · intro lam hlam
    rw [orthogonal_rotatedModelSubspace] at hlam
    have h := restrictedPointSpectrum_span_singleton_subset (𝕜 := 𝕜) (vθ_ne_zero θ)
      (modelRotatedOperator_apply_vθ (𝕜 := 𝕜) a b θ) hlam
    rw [Set.mem_singleton_iff] at h
    subst h
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo, not_and, not_lt]
    intro _
    linarith

/-- The interval/exterior gap of the `sin Θ` pair in the mirrored orientation, which the
symmetric `sin Θ` theorem also requires. -/
theorem intervalExteriorGap_sinTheta_model_symm {a b θ : ℝ} (hab : a < b) :
    PointIntervalExteriorGap (modelRotatedOperator (𝕜 := 𝕜) a b θ) (rotatedModelSubspace (𝕜 := 𝕜) θ)
      (modelGappedOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜))ᗮ a a (b - a) := by
  constructor
  · intro lam hlam
    have h := restrictedPointSpectrum_span_singleton_subset (𝕜 := 𝕜) (uθ_ne_zero θ)
      (modelRotatedOperator_apply_uθ (𝕜 := 𝕜) a b θ) hlam
    rw [Set.mem_singleton_iff] at h
    subst h
    simp
  · intro lam hlam
    rw [orthogonal_modelSubspace] at hlam
    have h := restrictedPointSpectrum_span_singleton_subset (𝕜 := 𝕜) e1_ne_zero
      (modelGappedOperator_apply_e1 (𝕜 := 𝕜) a b) hlam
    rw [Set.mem_singleton_iff] at h
    subst h
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo, not_and, not_lt]
    intro _
    linarith

/-- **The `sin Θ` planar model is an admissible perturbation pair.**

Both operators are symmetric, each of the two lines is invariant under its own operator, the
interval/exterior gap holds in both orientations with `δ = b - a`, and the residual is exactly
`modelSinThetaPerturbation a b θ`.  Consequently `sinTheta_model_equality` -- and through it
`sinTheta_constant_optimal` -- is equality in `TauCeti.sinAngleOperator_perturbation_le`, that
is, sharpness of the **theorem's** constant, not of a matrix identity. -/
theorem sinTheta_model_isAdmissiblePair {a b θ : ℝ} (hab : a < b) :
    (modelGappedOperator (𝕜 := 𝕜) a b).IsSymmetric ∧
      (modelRotatedOperator (𝕜 := 𝕜) a b θ).IsSymmetric ∧
      IsInvariant (modelGappedOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜)) ∧
      IsInvariant (modelRotatedOperator (𝕜 := 𝕜) a b θ)
        (rotatedModelSubspace (𝕜 := 𝕜) θ) ∧
      PointIntervalExteriorGap (modelGappedOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜))
        (modelRotatedOperator (𝕜 := 𝕜) a b θ) (rotatedModelSubspace (𝕜 := 𝕜) θ)ᗮ a a (b - a) ∧
      PointIntervalExteriorGap (modelRotatedOperator (𝕜 := 𝕜) a b θ)
        (rotatedModelSubspace (𝕜 := 𝕜) θ)
        (modelGappedOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜))ᗮ a a (b - a) ∧
      modelRotatedOperator (𝕜 := 𝕜) a b θ - modelGappedOperator (𝕜 := 𝕜) a b =
        modelSinThetaPerturbation (𝕜 := 𝕜) a b θ :=
  ⟨modelGappedOperator_isSymmetric a b, modelRotatedOperator_isSymmetric a b θ,
   isInvariant_modelGappedOperator_modelSubspace a b,
   isInvariant_modelRotatedOperator_rotatedModelSubspace a b θ,
   intervalExteriorGap_sinTheta_model hab, intervalExteriorGap_sinTheta_model_symm hab,
   modelRotatedOperator_sub_modelGappedOperator a b θ⟩

/-- **Equality in the `sin Θ` perturbation theorem.**

`TauCeti.sinAngleOperator_perturbation_le` gives `δ * N (sin Θ) ≤ N (B - A)` for an admissible
pair; `sinTheta_model_isAdmissiblePair` supplies one with `δ = b - a`, and here the inequality
is an equality for every unitarily invariant seminorm. -/
theorem sinTheta_perturbation_le_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (b - a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      N (modelRotatedOperator (𝕜 := 𝕜) a b θ - modelGappedOperator (𝕜 := 𝕜) a b) := by
  rw [modelRotatedOperator_sub_modelGappedOperator]
  exact sinTheta_model_equality N hab hθ0 hθ1

/-! ### The perturbation that is off-diagonal in the rotated frame

The `tan Θ` and `sin 2Θ` families need a symmetric perturbation whose *rotated* compression
vanishes, `-r (uθ ⊗ vθ + vθ ⊗ uθ)`.  It has the same two singular values `|r|` as the
correspondingly scaled coordinate-frame off-diagonal matrix used by the model equalities above,
so a unitarily invariant seminorm cannot tell them apart; but only this one is a residual. -/

/-- The symmetric perturbation `-r (uθ ⊗ vθ + vθ ⊗ uθ)`, written in coordinates.  It exchanges
the two rotated frame vectors up to the factor `-r`. -/
noncomputable def modelRotatedOffDiagonal (r θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin
    !![((r * Real.sin (2 * θ) : ℝ) : 𝕜), ((-(r * Real.cos (2 * θ)) : ℝ) : 𝕜);
       ((-(r * Real.cos (2 * θ)) : ℝ) : 𝕜), ((-(r * Real.sin (2 * θ)) : ℝ) : 𝕜)]

/-- The rotated off-diagonal perturbation is symmetric. -/
theorem modelRotatedOffDiagonal_isSymmetric (r θ : ℝ) :
    (modelRotatedOffDiagonal (𝕜 := 𝕜) r θ).IsSymmetric := by
  rw [modelRotatedOffDiagonal]
  refine Matrix.isSymmetric_toEuclideanLin_iff.mpr ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, RCLike.conj_ofReal]

/-- The rotated off-diagonal perturbation sends the rotated generator to the complementary
frame vector: this is what cancels the off-diagonal block of the base operator. -/
theorem modelRotatedOffDiagonal_apply_uθ (r θ : ℝ) :
    modelRotatedOffDiagonal (𝕜 := 𝕜) r θ (uθ (𝕜 := 𝕜) θ) =
      -((r : ℝ) : 𝕜) • vθ (𝕜 := 𝕜) θ := by
  have hpy := plane_sin_sq_add_cos_sq (𝕜 := 𝕜) θ
  rw [modelRotatedOffDiagonal]
  ext i
  fin_cases i <;>
    simp [uθ, vθ, e0, e1, Matrix.toLpLin_apply, Real.sin_two_mul, Real.cos_two_mul'] <;>
    (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]) <;>
    (try push_cast) <;>
    first
      | ring1
      | linear_combination ((r : 𝕜) * (Real.sin θ : 𝕜)) * hpy
      | linear_combination (-((r : 𝕜) * (Real.sin θ : 𝕜))) * hpy
      | linear_combination ((r : 𝕜) * (Real.cos θ : 𝕜)) * hpy
      | linear_combination (-((r : 𝕜) * (Real.cos θ : 𝕜))) * hpy

/-- The rotated off-diagonal perturbation exchanges the two frame vectors. -/
theorem modelRotatedOffDiagonal_apply_vθ (r θ : ℝ) :
    modelRotatedOffDiagonal (𝕜 := 𝕜) r θ (vθ (𝕜 := 𝕜) θ) =
      -((r : ℝ) : 𝕜) • uθ (𝕜 := 𝕜) θ := by
  have hpy := plane_sin_sq_add_cos_sq (𝕜 := 𝕜) θ
  rw [modelRotatedOffDiagonal]
  ext i
  fin_cases i <;>
    simp [uθ, vθ, e0, e1, Matrix.toLpLin_apply, Real.sin_two_mul, Real.cos_two_mul'] <;>
    (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]) <;>
    (try push_cast) <;>
    first
      | ring1
      | linear_combination ((r : 𝕜) * (Real.sin θ : 𝕜)) * hpy
      | linear_combination (-((r : 𝕜) * (Real.sin θ : 𝕜))) * hpy
      | linear_combination ((r : 𝕜) * (Real.cos θ : 𝕜)) * hpy
      | linear_combination (-((r : 𝕜) * (Real.cos θ : 𝕜))) * hpy
private theorem modelRotatedOffDiagonal_sq (r θ : ℝ) :
    modelRotatedOffDiagonal (𝕜 := 𝕜) r θ ∘ₗ modelRotatedOffDiagonal (𝕜 := 𝕜) r θ =
      ((((r ^ 2 : ℝ)) : 𝕜) • LinearMap.id) := by
  have hpy := plane_sin_sq_add_cos_sq (𝕜 := 𝕜) (2 * θ)
  ext x i
  fin_cases i <;>
    simp [modelRotatedOffDiagonal, Matrix.toLpLin_apply] <;>
    (try simp only [RCLike.algebraMap_eq_ofReal, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]) <;>
    first
      | ring1
      | linear_combination ((r : 𝕜) ^ 2 * x.ofLp 0) * hpy
      | linear_combination (-((r : 𝕜) ^ 2 * x.ofLp 0)) * hpy
      | linear_combination ((r : 𝕜) ^ 2 * x.ofLp 1) * hpy
private theorem singularValues_modelRotatedOffDiagonal (r θ : ℝ) :
    (modelRotatedOffDiagonal (𝕜 := 𝕜) r θ).singularValues =
      pairSingularValues |r| |r| :=
  singularValues_eq_abs_pair_of_isSymmetric_sq finrank_euclideanSpace_fin
    (EuclideanSpace.basisFun (Fin 2) 𝕜)
    (modelRotatedOffDiagonal (𝕜 := 𝕜) r θ) r
    (modelRotatedOffDiagonal_isSymmetric r θ) (modelRotatedOffDiagonal_sq r θ)
private theorem norm_eq_of_singularValues_eq {A B : Plane 𝕜 →ₗ[𝕜] Plane 𝕜}
    (h : A.singularValues = B.singularValues) :
    ‖A.toContinuousLinearMap‖ = ‖B.toContinuousLinearMap‖ := by
  rw [opNorm_eq_singularValues_zero (𝕜 := 𝕜) A (n := 2)
      finrank_euclideanSpace_fin (by norm_num),
    opNorm_eq_singularValues_zero (𝕜 := 𝕜) B (n := 2)
      finrank_euclideanSpace_fin (by norm_num), h]

/-! ### The `tan Θ` model as an admissible perturbation pair -/

/-- The unperturbed operator of the `tan Θ` extremal pair.  Its internal gap is
`(b - a)(1 + tan²θ) = (b - a)/cos²θ`; the Ritz value on the perturbed line sits exactly
`b - a` below the complementary block, which is the gap the `tan Θ` theorem divides by. -/
noncomputable def modelTanThetaBaseOperator (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  modelGappedOperator a (a + (b - a) * (1 + Real.tan θ ^ 2))

/-- The perturbed operator of the `tan Θ` extremal pair.  Its perturbation is off-diagonal in
the rotated frame, which is exactly the Galerkin condition `Q H Q = 0` of the `tan Θ`
theorem. -/
noncomputable def modelTanThetaPerturbedOperator (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ +
    modelRotatedOffDiagonal ((b - a) * Real.tan θ) θ

/-- The `tan Θ` pair's residual is the rotated off-diagonal perturbation. -/
theorem modelTanThetaPerturbedOperator_sub_base (a b θ : ℝ) :
    modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
        modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ =
      modelRotatedOffDiagonal (𝕜 := 𝕜) ((b - a) * Real.tan θ) θ := by
  rw [modelTanThetaPerturbedOperator]
  abel

/-- Both operators of the `tan Θ` pair are symmetric. -/
theorem modelTanThetaBaseOperator_isSymmetric (a b θ : ℝ) :
    (modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ).IsSymmetric :=
  modelGappedOperator_isSymmetric _ _

/-- The perturbed `tan Θ` operator is symmetric. -/
theorem modelTanThetaPerturbedOperator_isSymmetric (a b θ : ℝ) :
    (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ).IsSymmetric := by
  rw [modelTanThetaPerturbedOperator]
  exact (modelTanThetaBaseOperator_isSymmetric a b θ).add
    (modelRotatedOffDiagonal_isSymmetric _ _)

/-- **The rotated line is an eigenline of the perturbed `tan Θ` operator**, with Ritz value
`a + (b - a) tan²θ`: the base operator's rotated off-diagonal block is cancelled exactly. -/
theorem modelTanThetaPerturbedOperator_apply_uθ {a b θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ (uθ (𝕜 := 𝕜) θ) =
      ((a + (b - a) * Real.tan θ ^ 2 : ℝ) : 𝕜) • uθ (𝕜 := 𝕜) θ := by
  have hpyR := Real.sin_sq_add_cos_sq θ
  have hs : Real.sin θ = Real.tan θ * Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hkey : (1 + Real.tan θ ^ 2) * Real.cos θ ^ 2 = 1 := by
    linear_combination hpyR - (Real.sin θ + Real.tan θ * Real.cos θ) * hs
  have hdiag : a * Real.cos θ ^ 2 +
      (a + (b - a) * (1 + Real.tan θ ^ 2)) * Real.sin θ ^ 2 =
      a + (b - a) * Real.tan θ ^ 2 := by
    linear_combination a * hpyR +
      ((b - a) * (1 + Real.tan θ ^ 2) * (Real.sin θ + Real.tan θ * Real.cos θ)) * hs +
      ((b - a) * Real.tan θ ^ 2) * hkey
  have hoff : ((a + (b - a) * (1 + Real.tan θ ^ 2)) - a) * Real.sin θ * Real.cos θ =
      (b - a) * Real.tan θ := by
    linear_combination ((b - a) * (1 + Real.tan θ ^ 2) * Real.cos θ) * hs +
      ((b - a) * Real.tan θ) * hkey
  rw [modelTanThetaPerturbedOperator, modelTanThetaBaseOperator, LinearMap.add_apply,
    modelGappedOperator_apply_uθ, modelRotatedOffDiagonal_apply_uθ, hdiag, hoff]
  module

/-- The rotated line is invariant under the perturbed `tan Θ` operator. -/
theorem isInvariant_modelTanThetaPerturbedOperator {a b θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    IsInvariant (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
      (rotatedModelSubspace (𝕜 := 𝕜) θ) :=
  isInvariant_span_singleton (lam := a + (b - a) * Real.tan θ ^ 2)
    (modelTanThetaPerturbedOperator_apply_uθ hcos)

/-- The coordinate line is invariant under the unperturbed `tan Θ` operator. -/
theorem isInvariant_modelTanThetaBaseOperator (a b θ : ℝ) :
    IsInvariant (modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ) (modelSubspace (𝕜 := 𝕜)) :=
  isInvariant_modelGappedOperator_modelSubspace _ _

/-- **The Galerkin/Ritz condition of the `tan Θ` theorem holds for this pair**: the residual
has vanishing compression onto the perturbed line. -/
theorem compression_modelTanThetaResidual_eq_zero (a b θ : ℝ) :
    projection (rotatedModelSubspace (𝕜 := 𝕜) θ) ∘ₗ
        modelRotatedOffDiagonal (𝕜 := 𝕜) ((b - a) * Real.tan θ) θ ∘ₗ
      projection (rotatedModelSubspace (𝕜 := 𝕜) θ) = 0 := by
  ext x
  have hproj : (rotatedModelSubspace (𝕜 := 𝕜) θ).starProjection x =
      ⟪uθ (𝕜 := 𝕜) θ, x⟫_𝕜 • uθ (𝕜 := 𝕜) θ :=
    starProjection_span_singleton_apply_of_norm_one _ _ (norm_uθ θ)
  have hvθ : (rotatedModelSubspace (𝕜 := 𝕜) θ).starProjection (vθ (𝕜 := 𝕜) θ) = 0 := by
    rw [rotatedModelSubspace,
      starProjection_span_singleton_apply_of_norm_one _ _ (norm_uθ θ), inner_uθ_vθ,
      zero_smul]
  simp only [LinearMap.comp_apply, projection, ContinuousLinearMap.coe_coe,
    LinearMap.zero_apply, hproj, map_smul, modelRotatedOffDiagonal_apply_uθ, hvθ]
  simp

/-- **The ordered gap of the `tan Θ` pair is exactly `b - a`.**  The Ritz value on the rotated
line is `a + (b - a) tan²θ` and the unwanted exact block sits at `a + (b - a)(1 + tan²θ)`. -/
theorem orderedGap_tanTheta_model {a b θ : ℝ} (_hab : a < b) (hcos : Real.cos θ ≠ 0) :
    OrderedGap (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
      (rotatedModelSubspace (𝕜 := 𝕜) θ) (modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ)
      (modelSubspace (𝕜 := 𝕜))ᗮ (b - a) := by
  intro lam μ hlam hμ
  have hl := restrictedPointSpectrum_span_singleton_subset (𝕜 := 𝕜) (uθ_ne_zero θ)
    (modelTanThetaPerturbedOperator_apply_uθ (𝕜 := 𝕜) (a := a) (b := b) hcos) hlam
  rw [Set.mem_singleton_iff] at hl
  rw [orthogonal_modelSubspace] at hμ
  have hr := restrictedPointSpectrum_span_singleton_subset (𝕜 := 𝕜) e1_ne_zero
    (modelGappedOperator_apply_e1 (𝕜 := 𝕜) a (a + (b - a) * (1 + Real.tan θ ^ 2))) hμ
  rw [Set.mem_singleton_iff] at hr
  subst hl
  subst hr
  ring_nf
  linarith

/-- **The `tan Θ` planar model is an admissible perturbation pair.**

The equality `tanTheta_model_equality` therefore records equality in the source's `tan Θ`
perturbation bound `δ N(tan Θ) ≤ N(H)` at `δ = b - a`, not merely an identity of matrices.
Note where the pair differs from the naive guess: the residual is off-diagonal in the
**rotated** frame, and the unperturbed internal gap is `(b - a)(1 + tan²θ)`, strictly larger
than `b - a` off `θ = 0`.  The coordinate-frame matrix `modelTanThetaPerturbation` has the same
two singular values, which is why the seminorm equality is unaffected. -/
theorem tanTheta_model_isAdmissiblePair {a b θ : ℝ} (hab : a < b) (hcos : Real.cos θ ≠ 0) :
    (modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ).IsSymmetric ∧
      (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ).IsSymmetric ∧
      IsInvariant (modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ) (modelSubspace (𝕜 := 𝕜)) ∧
      IsInvariant (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
        (rotatedModelSubspace (𝕜 := 𝕜) θ) ∧
      OrderedGap (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
        (rotatedModelSubspace (𝕜 := 𝕜) θ) (modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ)
        (modelSubspace (𝕜 := 𝕜))ᗮ (b - a) ∧
      projection (rotatedModelSubspace (𝕜 := 𝕜) θ) ∘ₗ
          (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
            modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ) ∘ₗ
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ) = 0 :=
  ⟨modelTanThetaBaseOperator_isSymmetric a b θ,
   modelTanThetaPerturbedOperator_isSymmetric a b θ,
   isInvariant_modelTanThetaBaseOperator a b θ,
   isInvariant_modelTanThetaPerturbedOperator hcos,
   orderedGap_tanTheta_model hab hcos,
   by rw [modelTanThetaPerturbedOperator_sub_base]
      exact compression_modelTanThetaResidual_eq_zero a b θ⟩

/-- **Equality in the `tan Θ` perturbation bound, for the admissible pair.** -/
theorem tanTheta_perturbation_le_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (b - a) * N (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      N (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
        modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ) := by
  have htan : 0 ≤ Real.tan θ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ0 hθ1.le
  have hprod : 0 ≤ (b - a) * Real.tan θ := mul_nonneg (sub_nonneg.mpr hab.le) htan
  have hsing : (modelRotatedOffDiagonal (𝕜 := 𝕜) ((b - a) * Real.tan θ) θ).singularValues =
      (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues := by
    rw [singularValues_modelRotatedOffDiagonal,
      singularValues_modelTanThetaPerturbation hab htan, abs_of_nonneg hprod]
  rw [modelTanThetaPerturbedOperator_sub_base, N.eq_of_same_singularValues hsing]
  exact tanTheta_model_equality N hab hθ0 hθ1

/-- **The `tan Θ` source bound is attained by a genuine admissible pair.**

This packages the theorem hypotheses and the equality conclusion in one statement.  Sharpness is
therefore a property of an actual `(A,B)` configuration, not merely an identity between the
model angle operator and an unrelated matrix. -/
theorem tanTheta_model_sourceSharpness
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    ((modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ).IsSymmetric ∧
      (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ).IsSymmetric ∧
      IsInvariant (modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ)
        (modelSubspace (𝕜 := 𝕜)) ∧
      IsInvariant (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
        (rotatedModelSubspace (𝕜 := 𝕜) θ) ∧
      OrderedGap (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
        (rotatedModelSubspace (𝕜 := 𝕜) θ)
        (modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ)
        (modelSubspace (𝕜 := 𝕜))ᗮ (b - a) ∧
      projection (rotatedModelSubspace (𝕜 := 𝕜) θ) ∘ₗ
          (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
            modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ) ∘ₗ
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ) = 0) ∧
      (b - a) * N (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
        N (modelTanThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
          modelTanThetaBaseOperator (𝕜 := 𝕜) a b θ) := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  exact ⟨tanTheta_model_isAdmissiblePair hab hcos,
    tanTheta_perturbation_le_model_equality N hab hθ0 hθ1⟩

/-! ### The `sin 2Θ` model as an admissible perturbation pair -/

/-- The unperturbed operator of the `sin 2Θ` extremal pair.  The coordinate line carries the
**upper** block here, which is the orientation `TwoBlockFormGap` fixes. -/
noncomputable def modelSinTwoThetaBaseOperator (a b : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  modelGappedOperator b a

/-- The perturbed operator of the `sin 2Θ` extremal pair: the base operator with its rotated
off-diagonal block deleted, so the rotated line reduces it. -/
noncomputable def modelSinTwoThetaPerturbedOperator (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b +
    modelRotatedOffDiagonal (-((b - a) * Real.sin θ * Real.cos θ)) θ

/-- The `sin 2Θ` pair's residual is the rotated off-diagonal perturbation. -/
theorem modelSinTwoThetaPerturbedOperator_sub_base (a b θ : ℝ) :
    modelSinTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
        modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b =
      modelRotatedOffDiagonal (𝕜 := 𝕜) (-((b - a) * Real.sin θ * Real.cos θ)) θ := by
  rw [modelSinTwoThetaPerturbedOperator]
  abel

/-- The unperturbed `sin 2Θ` operator is symmetric. -/
theorem modelSinTwoThetaBaseOperator_isSymmetric (a b : ℝ) :
    (modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b).IsSymmetric :=
  modelGappedOperator_isSymmetric _ _

/-- The perturbed `sin 2Θ` operator is symmetric. -/
theorem modelSinTwoThetaPerturbedOperator_isSymmetric (a b θ : ℝ) :
    (modelSinTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ).IsSymmetric := by
  rw [modelSinTwoThetaPerturbedOperator]
  exact (modelSinTwoThetaBaseOperator_isSymmetric a b).add
    (modelRotatedOffDiagonal_isSymmetric _ _)

/-- **The rotated line is an eigenline of the perturbed `sin 2Θ` operator.** -/
theorem modelSinTwoThetaPerturbedOperator_apply_uθ (a b θ : ℝ) :
    modelSinTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ (uθ (𝕜 := 𝕜) θ) =
      ((b * Real.cos θ ^ 2 + a * Real.sin θ ^ 2 : ℝ) : 𝕜) • uθ (𝕜 := 𝕜) θ := by
  rw [modelSinTwoThetaPerturbedOperator, modelSinTwoThetaBaseOperator, LinearMap.add_apply,
    modelGappedOperator_apply_uθ, modelRotatedOffDiagonal_apply_uθ]
  push_cast
  module

/-- The rotated line is invariant under the perturbed `sin 2Θ` operator. -/
theorem isInvariant_modelSinTwoThetaPerturbedOperator (a b θ : ℝ) :
    IsInvariant (modelSinTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
      (rotatedModelSubspace (𝕜 := 𝕜) θ) :=
  isInvariant_span_singleton (lam := b * Real.cos θ ^ 2 + a * Real.sin θ ^ 2)
    (modelSinTwoThetaPerturbedOperator_apply_uθ a b θ)

/-- The coordinate line is invariant under the unperturbed `sin 2Θ` operator. -/
theorem isInvariant_modelSinTwoThetaBaseOperator (a b : ℝ) :
    IsInvariant (modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜)) :=
  isInvariant_modelGappedOperator_modelSubspace _ _

/-- **The two-block form gap of the `sin 2Θ` pair is exactly `b - a`.** -/
theorem twoBlockFormGap_sinTwoTheta_model (a b : ℝ) :
    TwoBlockFormGap (modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜))
      a b := by
  constructor
  · intro x hx
    rw [modelSinTwoThetaBaseOperator,
      re_inner_span_singleton norm_e0 (modelGappedOperator_apply_e0 (𝕜 := 𝕜) b a) hx]
  · intro x hx
    rw [orthogonal_modelSubspace] at hx
    rw [modelSinTwoThetaBaseOperator,
      re_inner_span_singleton norm_e1 (modelGappedOperator_apply_e1 (𝕜 := 𝕜) b a) hx]

/-- **The `sin 2Θ` planar model is an admissible perturbation pair.**

This corrects the record: the rotated line *is* reducing for a symmetric `B` whose residual has
the singular values of `modelSinTwoThetaPerturbation`.  What fails is only the naive guess
`B = modelGappedOperator a b + modelSinTwoThetaPerturbation a b θ`; the residual must be
off-diagonal in the **rotated** frame, and the base operator's upper block must be the
coordinate line. -/
theorem sinTwoTheta_model_isAdmissiblePair (a b θ : ℝ) :
    (modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b).IsSymmetric ∧
      (modelSinTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ).IsSymmetric ∧
      IsInvariant (modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜)) ∧
      IsInvariant (modelSinTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
        (rotatedModelSubspace (𝕜 := 𝕜) θ) ∧
      TwoBlockFormGap (modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b)
        (modelSubspace (𝕜 := 𝕜)) a b :=
  ⟨modelSinTwoThetaBaseOperator_isSymmetric a b,
   modelSinTwoThetaPerturbedOperator_isSymmetric a b θ,
   isInvariant_modelSinTwoThetaBaseOperator a b,
   isInvariant_modelSinTwoThetaPerturbedOperator a b θ,
   twoBlockFormGap_sinTwoTheta_model a b⟩

private theorem singularValues_modelSinTwoThetaResidual
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (modelRotatedOffDiagonal (𝕜 := 𝕜)
        (-((b - a) * Real.sin θ * Real.cos θ)) θ).singularValues =
      (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hprod : 0 ≤ ((b - a) / 2) * Real.sin (2 * θ) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hab.le) (by norm_num)) hsin
  have hrewrite : (b - a) * Real.sin θ * Real.cos θ = ((b - a) / 2) * Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; ring
  rw [singularValues_modelRotatedOffDiagonal,
    singularValues_modelSinTwoThetaPerturbation hab hθ0 hθ1, hrewrite, abs_neg,
    abs_of_nonneg hprod]

/-- **Equality in the `sin 2Θ` perturbation theorem at the operator norm.**

`sinTwoTheta_perturbation_le` gives `(b - a) N (sin 2Θ) ≤ 2 N (B - A)` for the admissible pair
of `sinTwoTheta_model_isAdmissiblePair`; at the operator norm this is an equality.  It cannot
be an equality at every unitarily invariant seminorm, because the one-sided `sin 2Θ` map has
one nonzero singular value where the residual has two --
`sinTwoTheta_model_equality_fails_beyond_operatorNorm`. -/
theorem sinTwoTheta_perturbation_le_model_operatorNorm_equality
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (b - a) * ‖(sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ =
      2 * ‖(modelSinTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
        modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b).toContinuousLinearMap‖ := by
  rw [modelSinTwoThetaPerturbedOperator_sub_base,
    norm_eq_of_singularValues_eq (singularValues_modelSinTwoThetaResidual hab hθ0 hθ1)]
  exact sinTwoTheta_model_operatorNorm_equality hab hθ0 hθ1

/-- **Equality in the rank-matched `sin 2Θ` bound, at every unitarily invariant seminorm.**

The symmetric sine of the doubled angle is the gauge-faithful double-angle operator of this
model; against the admissible pair's residual it attains equality at every seminorm at once,
which is the form of the source's simultaneous-equality claim. -/
theorem sinTwoTheta_model_equality_of_admissiblePair
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (b - a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) (2 * θ))) =
      2 * N (modelSinTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
        modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b) := by
  rw [modelSinTwoThetaPerturbedOperator_sub_base,
    N.eq_of_same_singularValues (singularValues_modelSinTwoThetaResidual hab hθ0 hθ1)]
  exact sinTwoTheta_model_equality N hab hθ0 hθ1

/-- The reflection-residual `sin 2Θ` theorem specialized to the planar sharpness
configuration.  This is the source theorem's stronger residual form, not merely its derived
factor-two perturbation consequence. -/
theorem sinTwoTheta_reflectionDefect_model_le
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) :
    (b - a) * N (sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) ≤
      N (reflectionDefect (rotatedModelSubspace (𝕜 := 𝕜) θ)
        (modelSinTwoThetaBaseOperator (𝕜 := 𝕜) a b)) :=
  sinTwoTheta_reflectionDefect_le N
    (modelSinTwoThetaBaseOperator_isSymmetric a b)
    (isInvariant_modelSinTwoThetaBaseOperator a b) hab
    (twoBlockFormGap_sinTwoTheta_model a b)

/-! ### The `tan 2Θ` model as an admissible perturbation pair -/

/-- The perturbed operator of the `tan 2Θ` extremal pair.  The perturbation is off-diagonal in
the **coordinate** frame -- the `tan 2Θ` theorem's `P H P = 0 = P^⊥ H P^⊥` hypothesis -- and the
planar Riccati law then puts the reducing line of the perturbed operator at angle `θ`.

The sign is the one the Riccati law forces: `tan 2θ = 2h/(a - b)` for
`B = diag(a, b) + h(e₀ ⊗ e₁ + e₁ ⊗ e₀)`, so the residual is *minus*
`modelTanTwoThetaPerturbation a b θ`.  A unitarily invariant seminorm does not see the sign. -/
noncomputable def modelTanTwoThetaPerturbedOperator (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  modelGappedOperator a b - modelTanTwoThetaPerturbation a b θ

/-- The `tan 2Θ` pair's residual is minus the coordinate-frame off-diagonal model. -/
theorem modelTanTwoThetaPerturbedOperator_sub_base (a b θ : ℝ) :
    modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ - modelGappedOperator (𝕜 := 𝕜) a b =
      -modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ := by
  rw [modelTanTwoThetaPerturbedOperator]
  abel

/-- The perturbed `tan 2Θ` operator is symmetric. -/
theorem modelTanTwoThetaPerturbedOperator_isSymmetric (a b θ : ℝ) :
    (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ).IsSymmetric := by
  rw [modelTanTwoThetaPerturbedOperator]
  refine (modelGappedOperator_isSymmetric a b).sub ?_
  rw [modelTanTwoThetaPerturbation]
  refine Matrix.isSymmetric_toEuclideanLin_iff.mpr ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, RCLike.conj_ofReal]

private theorem modelTanTwoThetaPerturbation_apply_uθ (a b θ : ℝ) :
    modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ (uθ (𝕜 := 𝕜) θ) =
      (((((b - a) / 2) * Real.tan (2 * θ)) * Real.sin (2 * θ) : ℝ) : 𝕜) • uθ (𝕜 := 𝕜) θ +
        (((((b - a) / 2) * Real.tan (2 * θ)) * Real.cos (2 * θ) : ℝ) : 𝕜) •
          vθ (𝕜 := 𝕜) θ := by
  have hpy := plane_sin_sq_add_cos_sq (𝕜 := 𝕜) θ
  set h : ℝ := ((b - a) / 2) * Real.tan (2 * θ) with hh
  rw [modelTanTwoThetaPerturbation]
  ext i
  fin_cases i <;>
    simp [uθ, vθ, e0, e1, Matrix.toLpLin_apply, Real.sin_two_mul, Real.cos_two_mul',
      ← hh] <;>
    (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]) <;>
    (try push_cast) <;>
    first
      | ring1
      | linear_combination ((h : 𝕜) * (Real.sin θ : 𝕜)) * hpy
      | linear_combination (-((h : 𝕜) * (Real.sin θ : 𝕜))) * hpy
      | linear_combination ((h : 𝕜) * (Real.cos θ : 𝕜)) * hpy
      | linear_combination (-((h : 𝕜) * (Real.cos θ : 𝕜))) * hpy

/-- **The rotated line is an eigenline of the perturbed `tan 2Θ` operator**: the planar Riccati
law `tan 2θ = 2h/(a - b)` is exactly the cancellation of the rotated off-diagonal block. -/
theorem modelTanTwoThetaPerturbedOperator_apply_uθ {a b θ : ℝ}
    (hcos2 : Real.cos (2 * θ) ≠ 0) :
    modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ (uθ (𝕜 := 𝕜) θ) =
      ((a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2 -
        ((b - a) / 2) * Real.tan (2 * θ) * Real.sin (2 * θ) : ℝ) : 𝕜) • uθ (𝕜 := 𝕜) θ := by
  have hcancel : (b - a) * Real.sin θ * Real.cos θ =
      ((b - a) / 2) * Real.tan (2 * θ) * Real.cos (2 * θ) := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    rw [Real.sin_two_mul]
    ring
  rw [modelTanTwoThetaPerturbedOperator, LinearMap.sub_apply, modelGappedOperator_apply_uθ,
    modelTanTwoThetaPerturbation_apply_uθ, hcancel]
  push_cast
  module

/-- The rotated line is invariant under the perturbed `tan 2Θ` operator. -/
theorem isInvariant_modelTanTwoThetaPerturbedOperator {a b θ : ℝ}
    (hcos2 : Real.cos (2 * θ) ≠ 0) :
    IsInvariant (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
      (rotatedModelSubspace (𝕜 := 𝕜) θ) :=
  isInvariant_span_singleton
    (lam := a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2 -
      ((b - a) / 2) * Real.tan (2 * θ) * Real.sin (2 * θ))
    (modelTanTwoThetaPerturbedOperator_apply_uθ hcos2)

/-- **The internal gap of the `tan 2Θ` pair's unperturbed operator is exactly `b - a`.** -/
theorem pointInternalGap_tanTwoTheta_model {a b : ℝ} (hab : a < b) :
    PointInternalGap (modelGappedOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜)) (b - a) := by
  refine ⟨isInvariant_modelGappedOperator_modelSubspace a b, ?_⟩
  intro lam μ hlam hμ
  have hl := restrictedPointSpectrum_span_singleton_subset (𝕜 := 𝕜) e0_ne_zero
    (modelGappedOperator_apply_e0 (𝕜 := 𝕜) a b) hlam
  rw [Set.mem_singleton_iff] at hl
  rw [orthogonal_modelSubspace] at hμ
  have hr := restrictedPointSpectrum_span_singleton_subset (𝕜 := 𝕜) e1_ne_zero
    (modelGappedOperator_apply_e1 (𝕜 := 𝕜) a b) hμ
  rw [Set.mem_singleton_iff] at hr
  subst hl
  subst hr
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **The `tan 2Θ` residual is off-diagonal for the unperturbed splitting**, which is the extra
hypothesis `P H P = 0 = P^⊥ H P^⊥` of the `tan 2Θ` theorem. -/
theorem modelTanTwoThetaResidual_offDiagonal (a b θ : ℝ) :
    projection (modelSubspace (𝕜 := 𝕜)) ∘ₗ
        modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ ∘ₗ
        projection (modelSubspace (𝕜 := 𝕜)) = 0 ∧
      complementaryProjection (modelSubspace (𝕜 := 𝕜)) ∘ₗ
        modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ ∘ₗ
        complementaryProjection (modelSubspace (𝕜 := 𝕜)) = 0 := by
  have he0 : modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ (e0 (𝕜 := 𝕜)) =
      ((((b - a) / 2) * Real.tan (2 * θ) : ℝ) : 𝕜) • e1 (𝕜 := 𝕜) := by
    rw [modelTanTwoThetaPerturbation]
    ext i
    fin_cases i <;> simp [e0, e1, Matrix.toLpLin_apply]
  have he1 : modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ (e1 (𝕜 := 𝕜)) =
      ((((b - a) / 2) * Real.tan (2 * θ) : ℝ) : 𝕜) • e0 (𝕜 := 𝕜) := by
    rw [modelTanTwoThetaPerturbation]
    ext i
    fin_cases i <;> simp [e0, e1, Matrix.toLpLin_apply]
  have key1 : ∀ z ∈ (modelSubspace (𝕜 := 𝕜))ᗮ,
      modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ z ∈ modelSubspace (𝕜 := 𝕜) := by
    intro z hz
    rw [orthogonal_modelSubspace, Submodule.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    rw [map_smul, he1, modelSubspace]
    exact Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hP : ∀ y : Plane 𝕜, (modelSubspace (𝕜 := 𝕜)).starProjection y =
      ⟪e0 (𝕜 := 𝕜), y⟫_𝕜 • e0 (𝕜 := 𝕜) := by
    intro y
    rw [modelSubspace]
    exact starProjection_span_singleton_apply_of_norm_one _ _ norm_e0
  constructor
  · refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, projection, ContinuousLinearMap.coe_coe,
      LinearMap.zero_apply, hP, map_smul, he0, inner_e0_e1, zero_smul, smul_zero]
  · refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, complementaryProjection, projection,
      ContinuousLinearMap.coe_coe, LinearMap.zero_apply]
    exact Submodule.starProjection_orthogonal_apply_eq_zero
      (key1 _ (Submodule.starProjection_apply_mem _ x))

/-- The actual residual `B - A` of the `tan 2Θ` model is off-diagonal for the
unperturbed splitting.  The sign in `B - A = -H` is immaterial for both diagonal
compressions, but this theorem records the source hypothesis in exactly the residual spelling. -/
theorem modelTanTwoThetaPerturbedResidual_offDiagonal (a b θ : ℝ) :
    projection (modelSubspace (𝕜 := 𝕜)) ∘ₗ
        (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
          modelGappedOperator (𝕜 := 𝕜) a b) ∘ₗ
        projection (modelSubspace (𝕜 := 𝕜)) = 0 ∧
      complementaryProjection (modelSubspace (𝕜 := 𝕜)) ∘ₗ
        (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
          modelGappedOperator (𝕜 := 𝕜) a b) ∘ₗ
        complementaryProjection (modelSubspace (𝕜 := 𝕜)) = 0 := by
  rw [modelTanTwoThetaPerturbedOperator_sub_base]
  rcases modelTanTwoThetaResidual_offDiagonal (𝕜 := 𝕜) a b θ with ⟨hP, hPperp⟩
  constructor
  · apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hP x
    simpa only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.zero_apply,
      map_neg, neg_zero] using congrArg Neg.neg hx
  · apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hPperp x
    simpa only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.zero_apply,
      map_neg, neg_zero] using congrArg Neg.neg hx

/-- **The `tan 2Θ` planar model is an admissible perturbation pair.**

The equality `tanTwoTheta_model_equality` therefore records equality in the source's `tan 2Θ`
perturbation bound `δ N(tan 2Θ) ≤ 2 N(H)` at `δ = b - a`. -/
theorem tanTwoTheta_model_isAdmissiblePair {a b θ : ℝ} (hab : a < b)
    (hcos2 : Real.cos (2 * θ) ≠ 0) :
    (modelGappedOperator (𝕜 := 𝕜) a b).IsSymmetric ∧
      (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ).IsSymmetric ∧
      IsInvariant (modelGappedOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜)) ∧
      IsInvariant (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
        (rotatedModelSubspace (𝕜 := 𝕜) θ) ∧
      PointInternalGap (modelGappedOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜)) (b - a) ∧
      modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ - modelGappedOperator (𝕜 := 𝕜) a b =
        -modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ :=
  ⟨modelGappedOperator_isSymmetric a b,
   modelTanTwoThetaPerturbedOperator_isSymmetric a b θ,
   isInvariant_modelGappedOperator_modelSubspace a b,
   isInvariant_modelTanTwoThetaPerturbedOperator hcos2,
   pointInternalGap_tanTwoTheta_model hab,
   modelTanTwoThetaPerturbedOperator_sub_base a b θ⟩

/-- **Equality in the `tan 2Θ` perturbation bound, for the admissible pair.** -/
theorem tanTwoTheta_perturbation_le_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 4) :
    (b - a) * N (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      2 * N (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
        modelGappedOperator (𝕜 := 𝕜) a b) := by
  have hneg : N (-modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) =
      N (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
    rw [show (-modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) =
      ((-1 : 𝕜) • modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) by module, N.smul_eq]
    simp
  rw [modelTanTwoThetaPerturbedOperator_sub_base, hneg]
  exact tanTwoTheta_model_equality N hab hθ0 hθ1

/-- **The `tan 2Θ` source bound is attained by a genuine admissible pair.**

The package includes the internal gap, the reducing subspaces, the actual residual's two
vanishing diagonal compressions, and equality in the sharp factor-two conclusion for every
unitarily invariant seminorm. -/
theorem tanTwoTheta_model_sourceSharpness
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 4) :
    ((modelGappedOperator (𝕜 := 𝕜) a b).IsSymmetric ∧
      (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ).IsSymmetric ∧
      IsInvariant (modelGappedOperator (𝕜 := 𝕜) a b) (modelSubspace (𝕜 := 𝕜)) ∧
      IsInvariant (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ)
        (rotatedModelSubspace (𝕜 := 𝕜) θ) ∧
      PointInternalGap (modelGappedOperator (𝕜 := 𝕜) a b)
        (modelSubspace (𝕜 := 𝕜)) (b - a) ∧
      modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
          modelGappedOperator (𝕜 := 𝕜) a b =
        -modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) ∧
      (projection (modelSubspace (𝕜 := 𝕜)) ∘ₗ
          (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
            modelGappedOperator (𝕜 := 𝕜) a b) ∘ₗ
          projection (modelSubspace (𝕜 := 𝕜)) = 0 ∧
        complementaryProjection (modelSubspace (𝕜 := 𝕜)) ∘ₗ
          (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
            modelGappedOperator (𝕜 := 𝕜) a b) ∘ₗ
          complementaryProjection (modelSubspace (𝕜 := 𝕜)) = 0) ∧
      (b - a) * N (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
        2 * N (modelTanTwoThetaPerturbedOperator (𝕜 := 𝕜) a b θ -
          modelGappedOperator (𝕜 := 𝕜) a b) := by
  have hcos2 : Real.cos (2 * θ) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [hθ1]⟩)
  exact ⟨tanTwoTheta_model_isAdmissiblePair hab hcos2,
    modelTanTwoThetaPerturbedResidual_offDiagonal a b θ,
    tanTwoTheta_perturbation_le_model_equality N hab hθ0 hθ1⟩

/-! ### The block-sum angle operator at the subspace level

The direct-sum equalities above are stated on `orthogonalBlockSum` of the *plane* angle
operators.  The missing bookkeeping is the identification of the block sum of two projectors
with the projector of an actual subspace of `WithLp 2 (E₁ × E₂)`; with it, those statements
become statements about a pair of subspaces.  Iteration to `m` blocks composes the two-block
lemma and is left to the consumer. -/

/-- **The projector onto a block sum of subspaces is the block sum of the projectors**, in the
`projection` spelling used by the angle operators.

The reusable `projection` form lives in `ForTauCeti` as
`TauCeti.projection_orthogonalBlockSumSubmodule`; it is derived there from the underlying
`starProjection_orthogonalBlockSumSubmodule` identity. -/
theorem projection_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ : Submodule 𝕜 E₁) (U₂ : Submodule 𝕜 E₂) :
    projection
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (projection U₁) (projection U₂) :=
  TauCeti.projection_orthogonalBlockSumSubmodule U₁ U₂

/-! ### Actual direct-sum subspace pairs and their angle operators -/

/-- The unperturbed subspace in the orthogonal direct sum of two planar sharpness models. -/
noncomputable def directSumModelSubspace :
    Submodule 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) :=
  UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule
    (modelSubspace (𝕜 := 𝕜)) (modelSubspace (𝕜 := 𝕜))

/-- The perturbed subspace in the orthogonal direct sum of two planar models. -/
noncomputable def directSumRotatedModelSubspace (θ₁ θ₂ : ℝ) :
    Submodule 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) :=
  UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule
    (rotatedModelSubspace (𝕜 := 𝕜) θ₁) (rotatedModelSubspace (𝕜 := 𝕜) θ₂)

/-- The sine-angle operator of the actual direct-sum pair is the block sum of the two planar
sine-angle operators. -/
theorem sinAngleOperator_directSumModelSubspaces (θ₁ θ₂ : ℝ) :
    sinAngleOperator (directSumModelSubspace (𝕜 := 𝕜))
        (directSumRotatedModelSubspace (𝕜 := 𝕜) θ₁ θ₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ₁))
        (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ₂)) :=
  TauCeti.sinAngleOperator_orthogonalBlockSumSubmodule
    (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₁)
    (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₂)

/-- The finite angle operator itself preserves the direct-sum decomposition. -/
theorem angleOperator_directSumModelSubspaces (θ₁ θ₂ : ℝ) :
    angleOperator (directSumModelSubspace (𝕜 := 𝕜))
        (directSumRotatedModelSubspace (𝕜 := 𝕜) θ₁ θ₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (angleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ₁))
        (angleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ₂)) :=
  angleOperator_orthogonalBlockSumSubmodule
    (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₁)
    (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₂)

/-- The canonical `tan Θ` operator of the actual direct-sum pair is block-diagonal. -/
theorem tanAngleOperator_directSumModelSubspaces (θ₁ θ₂ : ℝ) :
    tanAngleOperator (directSumModelSubspace (𝕜 := 𝕜))
        (directSumRotatedModelSubspace (𝕜 := 𝕜) θ₁ θ₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ₁))
        (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ₂)) :=
  tanAngleOperator_orthogonalBlockSumSubmodule
    (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₁)
    (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₂)

/-- The canonical `tan 2Θ` operator of the actual direct-sum pair is block-diagonal. -/
theorem tanTwoAngleOperator_directSumModelSubspaces (θ₁ θ₂ : ℝ) :
    tanTwoAngleOperator (directSumModelSubspace (𝕜 := 𝕜))
        (directSumRotatedModelSubspace (𝕜 := 𝕜) θ₁ θ₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ₁))
        (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ₂)) :=
  tanTwoAngleOperator_orthogonalBlockSumSubmodule
    (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₁)
    (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ₂)

/-- `sin Θ` equality for an explicit orthogonal direct sum of two subspace pairs. -/
theorem sinTheta_directSum_subspace_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) (WithLp 2 (Plane 𝕜 × Plane 𝕜)))
    {a b θ₁ θ₂ : ℝ} (hab : a < b) (h₁0 : 0 ≤ θ₁) (h₁1 : θ₁ ≤ Real.pi / 2)
    (h₂0 : 0 ≤ θ₂) (h₂1 : θ₂ ≤ Real.pi / 2) :
    (b - a) * N (sinAngleOperator (directSumModelSubspace (𝕜 := 𝕜))
      (directSumRotatedModelSubspace (𝕜 := 𝕜) θ₁ θ₂)) =
      N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ₁)
        (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ₂)) := by
  rw [sinAngleOperator_directSumModelSubspaces]
  exact sinTheta_directSum_model_equality N hab h₁0 h₁1 h₂0 h₂1

/-- `tan Θ` equality for an explicit orthogonal direct sum of two subspace pairs. -/
theorem tanTheta_directSum_subspace_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) (WithLp 2 (Plane 𝕜 × Plane 𝕜)))
    {a b θ₁ θ₂ : ℝ} (hab : a < b) (h₁0 : 0 ≤ θ₁) (h₁1 : θ₁ < Real.pi / 2)
    (h₂0 : 0 ≤ θ₂) (h₂1 : θ₂ < Real.pi / 2) :
    (b - a) * N (tanAngleOperator (directSumModelSubspace (𝕜 := 𝕜))
      (directSumRotatedModelSubspace (𝕜 := 𝕜) θ₁ θ₂)) =
      N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ₁)
        (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ₂)) := by
  rw [tanAngleOperator_directSumModelSubspaces]
  exact tanTheta_directSum_model_equality N hab h₁0 h₁1 h₂0 h₂1

/-- `sin 2Θ` equality for an explicit orthogonal direct sum of two subspace pairs. -/
theorem sinTwoTheta_directSum_subspace_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) (WithLp 2 (Plane 𝕜 × Plane 𝕜)))
    {a b θ₁ θ₂ : ℝ} (hab : a < b) (h₁0 : 0 ≤ θ₁) (h₁1 : θ₁ ≤ Real.pi / 4)
    (h₂0 : 0 ≤ θ₂) (h₂1 : θ₂ ≤ Real.pi / 4) :
    (b - a) * N (sinAngleOperator (directSumModelSubspace (𝕜 := 𝕜))
      (directSumRotatedModelSubspace (𝕜 := 𝕜) (2 * θ₁) (2 * θ₂))) =
      2 * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ₁)
        (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ₂)) := by
  rw [sinAngleOperator_directSumModelSubspaces]
  exact sinTwoTheta_directSum_model_equality N hab h₁0 h₁1 h₂0 h₂1

/-- `tan 2Θ` equality for an explicit orthogonal direct sum of two subspace pairs. -/
theorem tanTwoTheta_directSum_subspace_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (Plane 𝕜 × Plane 𝕜)) (WithLp 2 (Plane 𝕜 × Plane 𝕜)))
    {a b θ₁ θ₂ : ℝ} (hab : a < b) (h₁0 : 0 ≤ θ₁) (h₁1 : θ₁ < Real.pi / 4)
    (h₂0 : 0 ≤ θ₂) (h₂1 : θ₂ < Real.pi / 4) :
    (b - a) * N (tanTwoAngleOperator (directSumModelSubspace (𝕜 := 𝕜))
      (directSumRotatedModelSubspace (𝕜 := 𝕜) θ₁ θ₂)) =
      2 * N (UnitarilyInvariantSeminorm.orthogonalBlockSum
        (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ₁)
        (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ₂)) := by
  rw [tanTwoAngleOperator_directSumModelSubspaces]
  exact tanTwoTheta_directSum_model_equality N hab h₁0 h₁1 h₂0 h₂1

end DavisKahan.FiniteDimensional
end TauCeti
