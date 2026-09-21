/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.RankOneNormalization
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFrobenius
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem61Universal
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleReal
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorModulus

/-! # Sharpness -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Source-faithful sharpness and the one-gap counterexample

The single-angle constant is already attained on a two-dimensional reducing
model.  The residual and the directed sine block are scalar multiples of the
same rank-one isometry, so equality holds simultaneously for every normalized
source norm.  Orthogonal finite sums retain the same scalar operator identity.

The final section records the explicit matrix counterexample printed directly
before Proposition 6.1: one directional gap does not imply the symmetric
square-norm estimate.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators

open TauCeti.DavisKahan.Foundation
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe u

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The two-dimensional model space `𝕜²` carrying the planar equality configuration. -/
abbrev PlanarModelSpace (𝕜 : Type u) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 2)

/-- First standard vector of the planar equality model. -/
def planarModelE0 : PlanarModelSpace 𝕜 :=
  EuclideanSpace.single (0 : Fin 2) 1

/-- Second standard vector of the planar equality model. -/
def planarModelE1 : PlanarModelSpace 𝕜 :=
  EuclideanSpace.single (1 : Fin 2) 1

/-- Scalar-to-vector map used for all one-dimensional model blocks. -/
noncomputable def scalarColumn (v : PlanarModelSpace 𝕜) :
    𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
  (ContinuousLinearMap.id 𝕜 𝕜).smulRight v

/-- Exact spectral inclusion. -/
noncomputable def planarExactMap :
    𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
  scalarColumn planarModelE0

/-- Complementary spectral inclusion. -/
noncomputable def planarComplementMap :
    𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
  scalarColumn planarModelE1

/-- Trial inclusion at angle `theta`. -/
noncomputable def planarTrialMap (theta : ℝ) :
    𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
  scalarColumn
    ((Real.cos theta : 𝕜) • planarModelE0 +
      (Real.sin theta : 𝕜) • planarModelE1)

/-- Two-level self-adjoint operator with gap `delta`. -/
noncomputable def planarAmbient (delta : ℝ) :
    PlanarModelSpace 𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
  (Matrix.toEuclideanLin
    !![(0 : 𝕜), 0; 0, (delta : 𝕜)]).toContinuousLinearMap

/-- Zero trial operator. -/
noncomputable def planarTrialOperator : 𝕜 →L[𝕜] 𝕜 := 0

/-- Literal directed sine block of the planar model. -/
noncomputable def planarSineBlock (theta : ℝ) :
    𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
  ((Real.sin theta : 𝕜) • planarComplementMap)

/-- Residual of the planar equality model. -/
noncomputable def planarResidual (delta theta : ℝ) :
    𝕜 →L[𝕜] PlanarModelSpace 𝕜 :=
  ((delta * Real.sin theta : ℝ) : 𝕜) • planarComplementMap

/-- The first model vector is a unit vector. -/
@[simp]
theorem norm_planarModelE0 : ‖planarModelE0 (𝕜 := 𝕜)‖ = 1 := by
  simp [planarModelE0]

/-- The second model vector is a unit vector. -/
@[simp]
theorem norm_planarModelE1 : ‖planarModelE1 (𝕜 := 𝕜)‖ = 1 := by
  simp [planarModelE1]

/-- The adjoint of a scalar column reads off the corresponding coordinate.

Every block identity below needs this; without it the adjoint stays an opaque
term and no component computation closes. -/
theorem adjoint_scalarColumn_apply (i : Fin 2) (x : PlanarModelSpace 𝕜) :
    (scalarColumn (EuclideanSpace.single i (1 : 𝕜))).adjoint x =
      x.ofLp i := by
  -- Identify the adjoint by the defining inner-product identity, evaluated on
  -- the coordinate functional `x ↦ x i`.
  have hadj :
      (ContinuousLinearMap.id 𝕜 𝕜).smulRight
            (EuclideanSpace.single i (1 : 𝕜)) =
          ((EuclideanSpace.proj i : PlanarModelSpace 𝕜 →L[𝕜] 𝕜)).adjoint := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro z y
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      inner_smul_left, EuclideanSpace.inner_single_left]
    simp [RCLike.inner_apply, mul_comm]
  have := congrArg (fun T : 𝕜 →L[𝕜] PlanarModelSpace 𝕜 => T.adjoint) hadj
  simp only [ContinuousLinearMap.adjoint_adjoint] at this
  rw [scalarColumn, this]
  rfl

/-- Pointwise formula: the scalar column sends `z` to `z • v`. -/
@[simp]
theorem scalarColumn_apply (v : PlanarModelSpace 𝕜) (z : 𝕜) :
    scalarColumn v z = z • v := rfl

/-- Pointwise formula for the exact-subspace embedding: `z ↦ z • e₀`. -/
@[simp]
theorem planarExactMap_apply (z : 𝕜) :
    planarExactMap (𝕜 := 𝕜) z = z • planarModelE0 := rfl

/-- Pointwise formula for the complement embedding: `z ↦ z • e₁`. -/
@[simp]
theorem planarComplementMap_apply (z : 𝕜) :
    planarComplementMap (𝕜 := 𝕜) z = z • planarModelE1 := rfl

/-- Pointwise formula for the trial embedding: `z` times the unit vector at angle
`theta` in the `e₀`-`e₁` frame. -/
@[simp]
theorem planarTrialMap_apply (theta : ℝ) (z : 𝕜) :
    planarTrialMap (𝕜 := 𝕜) theta z =
      z • ((Real.cos theta : 𝕜) • planarModelE0 +
        (Real.sin theta : 𝕜) • planarModelE1) := rfl

/-- The adjoint of the exact embedding reads off the zeroth coordinate. -/
@[simp]
theorem adjoint_planarExactMap_apply (x : PlanarModelSpace 𝕜) :
    (planarExactMap (𝕜 := 𝕜)).adjoint x = x.ofLp 0 :=
  adjoint_scalarColumn_apply 0 x

/-- The adjoint of the complement embedding reads off the first coordinate. -/
@[simp]
theorem adjoint_planarComplementMap_apply (x : PlanarModelSpace 𝕜) :
    (planarComplementMap (𝕜 := 𝕜)).adjoint x = x.ofLp 1 :=
  adjoint_scalarColumn_apply 1 x

/-- The trial column is isometric for every real angle. -/
theorem planarTrialMap_isometry (theta : ℝ) :
    IsometricEmbedding (planarTrialMap (𝕜 := 𝕜) theta) := by
  intro z
  simp only [planarTrialMap, scalarColumn,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
  rw [norm_smul]
  have horth :
      ⟪planarModelE0 (𝕜 := 𝕜), planarModelE1 (𝕜 := 𝕜)⟫_𝕜 = 0 := by
    simp [planarModelE0, planarModelE1, EuclideanSpace.inner_single_left]
  have horthSmul :
      ⟪(Real.cos theta : 𝕜) • planarModelE0 (𝕜 := 𝕜),
        (Real.sin theta : 𝕜) • planarModelE1 (𝕜 := 𝕜)⟫_𝕜 = 0 := by
    rw [inner_smul_left, inner_smul_right, horth]
    ring
  have hunitSq :
      ‖(Real.cos theta : 𝕜) • planarModelE0 (𝕜 := 𝕜) +
          (Real.sin theta : 𝕜) • planarModelE1 (𝕜 := 𝕜)‖ ^ 2 = 1 := by
    -- Pythagoras is stated in `mul_self` form, so the square is opened first.
    have hpyth :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthSmul
    simp only [norm_smul, norm_smul, norm_planarModelE0, norm_planarModelE1, mul_one,
      mul_one, RCLike.norm_ofReal, RCLike.norm_ofReal] at hpyth
    rw [sq, hpyth, ← sq, ← sq, sq_abs, sq_abs]
    exact Real.cos_sq_add_sin_sq theta
  have hunit :
      ‖(Real.cos theta : 𝕜) • planarModelE0 (𝕜 := 𝕜) +
          (Real.sin theta : 𝕜) • planarModelE1 (𝕜 := 𝕜)‖ = 1 := by
    calc
      ‖(Real.cos theta : 𝕜) • planarModelE0 (𝕜 := 𝕜) +
            (Real.sin theta : 𝕜) • planarModelE1 (𝕜 := 𝕜)‖ =
          Real.sqrt
            (‖(Real.cos theta : 𝕜) • planarModelE0 (𝕜 := 𝕜) +
              (Real.sin theta : 𝕜) • planarModelE1 (𝕜 := 𝕜)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = 1 := by rw [hunitSq, Real.sqrt_one]
  rw [hunit, mul_one]

/-- Exact and complementary columns form the coordinate orthogonal
decomposition. -/
theorem planar_exact_decomposition :
    OrthogonalExactDecomposition
      (planarExactMap (𝕜 := 𝕜))
      (planarComplementMap (𝕜 := 𝕜)) := by
  refine {
    isometry₀ := ?_
    isometry₁ := ?_
    orthogonal := ?_
    projection_sum := ?_ }
  · intro z
    simp [planarExactMap, scalarColumn, norm_smul]
  · intro z
    simp [planarComplementMap, scalarColumn, norm_smul]
  · ext
    simp [planarModelE1]
  · ext x i
    fin_cases i <;>
      simp [planarModelE0, planarModelE1]

/-- Direct matrix calculation of the planar residual identity. -/
theorem planar_residual_identity (delta theta : ℝ) :
    planarAmbient (𝕜 := 𝕜) delta ∘L
        planarTrialMap (𝕜 := 𝕜) theta -
      planarTrialMap (𝕜 := 𝕜) theta ∘L
        planarTrialOperator (𝕜 := 𝕜) =
      planarResidual (𝕜 := 𝕜) delta theta := by
  ext i
  fin_cases i <;>
    simp [planarAmbient, planarTrialOperator, planarResidual,
      planarModelE0, planarModelE1, Matrix.toLpLin_apply,
      mul_comm]

/-- The projection residual is literally the rank-one sine block. -/
theorem planar_directedSine_identity (theta : ℝ) :
    (ContinuousLinearMap.id 𝕜 (PlanarModelSpace 𝕜) -
        planarExactMap (𝕜 := 𝕜) ∘L
          (planarExactMap (𝕜 := 𝕜)).adjoint) ∘L
      planarTrialMap (𝕜 := 𝕜) theta =
        planarSineBlock (𝕜 := 𝕜) theta := by
  ext i
  fin_cases i <;>
    simp [planarSineBlock, planarModelE0, planarModelE1]

/-- The complement inclusion is a norm-one rank-one map. -/
theorem planarComplementMap_norm_rank :
    ‖planarComplementMap (𝕜 := 𝕜)‖ = 1 ∧
      (planarComplementMap (𝕜 := 𝕜)).rank ≤ (1 : Cardinal) := by
  constructor
  · rw [planarComplementMap, scalarColumn,
      ContinuousLinearMap.norm_smulRight_apply,
      ContinuousLinearMap.norm_id, one_mul, norm_planarModelE1]
  · exact (LinearMap.rank_le_domain
      (planarComplementMap (𝕜 := 𝕜)).toLinearMap).trans_eq (by simp)

/-- Equality in Theorem 6.1 is attained simultaneously for every normalized
source norm. -/
theorem theorem61_planar_equality_every_norm
    (N : SymmetricNormingFunction)
    {delta theta : ℝ} (hdelta : 0 ≤ delta) :
    N.gauge (planarResidual (𝕜 := 𝕜) delta theta) =
      delta * N.gauge (planarSineBlock (𝕜 := 𝕜) theta) := by
  have hV := planarComplementMap_norm_rank (𝕜 := 𝕜)
  have hVmem := N.mem_rankOne hV.1 hV.2
  rw [planarResidual, planarSineBlock,
    N.gauge_smul _ hVmem, N.gauge_smul _ hVmem]
  simp [abs_of_nonneg hdelta]
  ring

/-- At every nonzero acute angle the sine block has strictly positive source
norm. -/
theorem planarSineBlock_gauge_pos
    (N : SymmetricNormingFunction)
    {theta : ℝ} (h0 : 0 < theta) (h1 : theta < Real.pi) :
    0 < N.gauge (planarSineBlock (𝕜 := 𝕜) theta) := by
  have hV := planarComplementMap_norm_rank (𝕜 := 𝕜)
  have hVmem := N.mem_rankOne hV.1 hV.2
  rw [planarSineBlock, N.gauge_smul _ hVmem,
    N.gauge_rankOne hV.1 hV.2, mul_one, RCLike.norm_ofReal]
  exact abs_pos.mpr (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'

/-- No constant strictly below one can replace the source constant in the
single-angle theorem. -/
theorem sinTheta_constant_one_optimal
    (N : SymmetricNormingFunction) :
    ∀ c : ℝ, c < 1 →
      ∃ delta theta : ℝ,
        0 < delta ∧ 0 < theta ∧ theta < Real.pi / 2 ∧
        c * N.gauge (planarResidual (𝕜 := 𝕜) delta theta) <
          delta * N.gauge (planarSineBlock (𝕜 := 𝕜) theta) := by
  intro c hc
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi42 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨1, Real.pi / 4, zero_lt_one, hpi4, hpi42, ?_⟩
  rw [theorem61_planar_equality_every_norm N zero_le_one]
  have hpos := planarSineBlock_gauge_pos (𝕜 := 𝕜) N
    hpi4 (by linarith [Real.pi_pos])
  nlinarith

/-- Scalar homogeneity of the paper gauge on a finite-dimensional operator.

This is a supporting identity for a future finite-multiplicity extremal model;
it is not itself that model. -/
theorem finiteDimensional_scalar_homogeneity
    {m : ℕ} (N : SymmetricNormingFunction)
    (S : EuclideanSpace 𝕜 (Fin m) →L[𝕜] EuclideanSpace 𝕜 (Fin m))
    {delta : ℝ} (hdelta : 0 ≤ delta) (hS : N.Mem S) :
    N.gauge (((delta : ℝ) : 𝕜) • S) = delta * N.gauge S := by
  rw [N.gauge_smul _ hS]
  simp [abs_of_nonneg hdelta]

section Counterexample


/-- The real model plane is two-dimensional. -/
theorem realPlane_finrank : Module.finrank ℝ (PlanarModelSpace ℝ) = 2 := by simp

/-!
### The real coordinate frame

Every quantity in the printed counterexample is a combination of the two
coordinate vectors, so the whole calculation reduces to one orthonormality fact
and one Pythagoras step.  Deriving those once keeps the individual proofs from
having to unfold `EuclideanSpace` coordinates, where the simp set rewrites
`⟪x, x⟫_ℝ` back into `‖x‖ ^ 2` and stalls.
-/

private theorem real_inner_e0_e1 :
    ⟪planarModelE0 (𝕜 := ℝ), planarModelE1 (𝕜 := ℝ)⟫_ℝ = 0 := by
  simp [planarModelE0, planarModelE1, EuclideanSpace.inner_single_left]

/-- Squared length of a combination of the two coordinate vectors. -/
private theorem real_norm_sq_combo (a b : ℝ) :
    ‖a • planarModelE0 (𝕜 := ℝ) + b • planarModelE1 (𝕜 := ℝ)‖ ^ 2 =
      a ^ 2 + b ^ 2 := by
  have horth :
      ⟪a • planarModelE0 (𝕜 := ℝ), b • planarModelE1 (𝕜 := ℝ)⟫_ℝ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_e0_e1]
    ring
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  simp only [norm_smul, norm_smul, norm_planarModelE0, norm_planarModelE1, mul_one,
    mul_one, Real.norm_eq_abs, Real.norm_eq_abs] at hpyth
  rw [sq, hpyth, ← sq, ← sq, sq_abs, sq_abs]

/-- The trial direction written in the coordinate frame. -/
private theorem real_diff_eq_combo :
    planarModelE0 (𝕜 := ℝ) - planarModelE1 (𝕜 := ℝ) =
      (1 : ℝ) • planarModelE0 (𝕜 := ℝ) + (-1 : ℝ) • planarModelE1 (𝕜 := ℝ) := by
  rw [one_smul, neg_one_smul, sub_eq_add_neg]

private theorem real_inner_diff_e0 :
    ⟪planarModelE0 (𝕜 := ℝ) - planarModelE1 (𝕜 := ℝ),
      planarModelE0 (𝕜 := ℝ)⟫_ℝ = 1 := by
  rw [inner_sub_left]
  simp [planarModelE0, planarModelE1, EuclideanSpace.inner_single_left]

private theorem real_inner_diff_e1 :
    ⟪planarModelE0 (𝕜 := ℝ) - planarModelE1 (𝕜 := ℝ),
      planarModelE1 (𝕜 := ℝ)⟫_ℝ = -1 := by
  rw [inner_sub_left]
  simp [planarModelE0, planarModelE1, EuclideanSpace.inner_single_left]

/-- The perturbed operator of the counterexample: `diag(0, 1)`. -/
noncomputable def counterexampleA :
    (PlanarModelSpace ℝ) →L[ℝ] (PlanarModelSpace ℝ) :=
  (Matrix.toEuclideanLin !![(0 : ℝ), 0; 0, 1]).toContinuousLinearMap

/-- The perturbation of the counterexample: the off-diagonal involution `!![1,1;1,0]`. -/
noncomputable def counterexampleH :
    (PlanarModelSpace ℝ) →L[ℝ] (PlanarModelSpace ℝ) :=
  (Matrix.toEuclideanLin !![(1 : ℝ), 1; 1, 0]).toContinuousLinearMap

/-- The exact subspace of the counterexample: the line spanned by `e₀`. -/
noncomputable def counterexampleExact : Submodule ℝ (PlanarModelSpace ℝ) :=
  Submodule.span ℝ {planarModelE0 (𝕜 := ℝ)}

/-- Unit vector spanning the trial line in the printed counterexample. -/
noncomputable def counterexampleTrialVector : (PlanarModelSpace ℝ) :=
  (1 / Real.sqrt 2) •
    (planarModelE0 (𝕜 := ℝ) - planarModelE1 (𝕜 := ℝ))

/-- The trial subspace of the counterexample: the line spanned by the unit vector
along `e₀ - e₁`, i.e. at `π/4` to the exact subspace. -/
noncomputable def counterexampleTrial : Submodule ℝ (PlanarModelSpace ℝ) :=
  Submodule.span ℝ {counterexampleTrialVector}

/-- The counterexample's exact subspace is orthogonally complemented. -/
noncomputable instance counterexampleExact_projection :
    counterexampleExact.HasOrthogonalProjection := inferInstance

/-- The counterexample's trial subspace is orthogonally complemented. -/
noncomputable instance counterexampleTrial_projection :
    counterexampleTrial.HasOrthogonalProjection := inferInstance

/-- Orthogonal projection onto a unit-generated real line. -/
private theorem starProjection_span_singleton_apply_of_norm_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (v x : E) (hv : ‖v‖ = 1) :
    (Submodule.span ℝ {v}).starProjection x = ⟪v, x⟫_ℝ • v := by
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
          hv, real_inner_comm]
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_right, ha, mul_zero]

/-- The trial generator in the printed counterexample is a unit vector. -/
theorem norm_counterexampleTrialVector :
    ‖counterexampleTrialVector‖ = 1 := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hdiffsq : ‖planarModelE0 (𝕜 := ℝ) - planarModelE1‖ ^ 2 = 2 := by
    rw [real_diff_eq_combo, real_norm_sq_combo]
    norm_num
  have hdiff : ‖planarModelE0 (𝕜 := ℝ) - planarModelE1‖ = Real.sqrt 2 := by
    calc
      ‖planarModelE0 (𝕜 := ℝ) - planarModelE1‖ =
          Real.sqrt (‖planarModelE0 (𝕜 := ℝ) - planarModelE1‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 2 := by rw [hdiffsq]
  rw [counterexampleTrialVector, norm_smul, hdiff,
    Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hsqrt2)]
  field_simp [ne_of_gt hsqrt2]

/-- The exact subspace fixes `e₀`, being the line it spans. -/
@[simp]
theorem counterexampleExact_starProjection_e0 :
    counterexampleExact.starProjection (planarModelE0 (𝕜 := ℝ)) =
      planarModelE0 := by
  -- The orthogonal-projection instance is indexed by the submodule itself, so
  -- rewriting the submodule has no type-correct motive.  Instantiate the
  -- general lemma at the definitional unfolding instead.
  have h : counterexampleExact.starProjection (planarModelE0 (𝕜 := ℝ)) =
      ⟪planarModelE0 (𝕜 := ℝ), planarModelE0 (𝕜 := ℝ)⟫_ℝ •
        planarModelE0 (𝕜 := ℝ) :=
    starProjection_span_singleton_apply_of_norm_one _ _ norm_planarModelE0
  rw [h]
  simp [planarModelE0]

/-- The exact subspace annihilates `e₁`, which is orthogonal to it. -/
@[simp]
theorem counterexampleExact_starProjection_e1 :
    counterexampleExact.starProjection (planarModelE1 (𝕜 := ℝ)) = 0 := by
  have h : counterexampleExact.starProjection (planarModelE1 (𝕜 := ℝ)) =
      ⟪planarModelE0 (𝕜 := ℝ), planarModelE1 (𝕜 := ℝ)⟫_ℝ •
        planarModelE0 (𝕜 := ℝ) :=
    starProjection_span_singleton_apply_of_norm_one _ _ norm_planarModelE0
  rw [h, real_inner_e0_e1, zero_smul]

/-- Pointwise formula for the orthogonal projection onto the trial line. -/
@[simp]
theorem counterexampleTrial_starProjection_apply (x : (PlanarModelSpace ℝ)) :
    counterexampleTrial.starProjection x =
      ⟪counterexampleTrialVector, x⟫_ℝ •
        counterexampleTrialVector :=
  starProjection_span_singleton_apply_of_norm_one _ _
    norm_counterexampleTrialVector

/-- Value of the trial projection at `e₀`: the `π/4` angle splits it evenly. -/
@[simp]
theorem counterexampleTrial_starProjection_e0 :
    counterexampleTrial.starProjection (planarModelE0 (𝕜 := ℝ)) =
      (1 / 2 : ℝ) •
        (planarModelE0 (𝕜 := ℝ) - planarModelE1 (𝕜 := ℝ)) := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rw [counterexampleTrial_starProjection_apply]
  have hinner :
      ⟪counterexampleTrialVector, planarModelE0 (𝕜 := ℝ)⟫_ℝ =
        1 / Real.sqrt 2 := by
    rw [counterexampleTrialVector, real_inner_smul_left,
      real_inner_diff_e0, mul_one]
  rw [hinner, counterexampleTrialVector, smul_smul]
  have hcoeff :
      (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
    field_simp [ne_of_gt hsqrt2]
    nlinarith
  rw [hcoeff]

/-- Value of the trial projection at `e₁`: the `π/4` angle splits it evenly. -/
@[simp]
theorem counterexampleTrial_starProjection_e1 :
    counterexampleTrial.starProjection (planarModelE1 (𝕜 := ℝ)) =
      (-1 / 2 : ℝ) •
        (planarModelE0 (𝕜 := ℝ) - planarModelE1 (𝕜 := ℝ)) := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rw [counterexampleTrial_starProjection_apply]
  have hinner :
      ⟪counterexampleTrialVector, planarModelE1 (𝕜 := ℝ)⟫_ℝ =
        -1 / Real.sqrt 2 := by
    rw [counterexampleTrialVector, real_inner_smul_left,
      real_inner_diff_e1]
    ring
  rw [hinner, counterexampleTrialVector, smul_smul]
  have hcoeff :
      (-1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = -1 / 2 := by
    field_simp [ne_of_gt hsqrt2]
    nlinarith
  rw [hcoeff]

/-- The projection difference on the first coordinate vector. -/
theorem counterexample_projectionDifference_e0 :
    (counterexampleExact.starProjection -
        counterexampleTrial.starProjection) (planarModelE0 (𝕜 := ℝ)) =
      (1 / 2 : ℝ) • planarModelE0 (𝕜 := ℝ) +
        (1 / 2 : ℝ) • planarModelE1 (𝕜 := ℝ) := by
  rw [sub_apply,
    counterexampleExact_starProjection_e0,
    counterexampleTrial_starProjection_e0]
  module

/-- The projection difference on the second coordinate vector. -/
theorem counterexample_projectionDifference_e1 :
    (counterexampleExact.starProjection -
        counterexampleTrial.starProjection) (planarModelE1 (𝕜 := ℝ)) =
      (1 / 2 : ℝ) • planarModelE0 (𝕜 := ℝ) +
        (-(1 / 2) : ℝ) • planarModelE1 (𝕜 := ℝ) := by
  rw [sub_apply,
    counterexampleExact_starProjection_e1,
    counterexampleTrial_starProjection_e1]
  module

/-- The printed perturbation on the first coordinate vector. -/
theorem counterexampleH_e0 :
    counterexampleH (planarModelE0 (𝕜 := ℝ)) =
      (1 : ℝ) • planarModelE0 (𝕜 := ℝ) + (1 : ℝ) • planarModelE1 (𝕜 := ℝ) := by
  ext i
  fin_cases i <;>
    simp [counterexampleH, planarModelE0, planarModelE1,
      Matrix.toLpLin_apply]

/-- The printed perturbation on the second coordinate vector. -/
theorem counterexampleH_e1 :
    counterexampleH (planarModelE1 (𝕜 := ℝ)) =
      (1 : ℝ) • planarModelE0 (𝕜 := ℝ) + (0 : ℝ) • planarModelE1 (𝕜 := ℝ) := by
  ext i
  fin_cases i <;>
    simp [counterexampleH, planarModelE0, planarModelE1,
      Matrix.toLpLin_apply]

/-- The real complexified sine operator has the same paper square norm as the
real projection difference from which it is constructed. -/
theorem hilbertSchmidtNorm_sinAngleOperatorRC_eq_projectionDifference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ContinuousLinearMap.hilbertSchmidtNorm
        (TauCeti.DavisKahan.Angle.Real.sinAngleOperatorRC U V) =
      ContinuousLinearMap.hilbertSchmidtNorm (U.starProjection - V.starProjection) := by
  rw [TauCeti.DavisKahan.Angle.Real.sinAngleOperatorRC,
    TauCeti.DavisKahan.Angle.sinAngleOperatorC]
  calc
    ContinuousLinearMap.hilbertSchmidtNorm
        (ContinuousLinearMap.modulus
          ((complexifySubmodule U).starProjection -
            (complexifySubmodule V).starProjection)) =
        ContinuousLinearMap.hilbertSchmidtNorm
          ((complexifySubmodule U).starProjection -
            (complexifySubmodule V).starProjection) :=
      SameApproximationSingularSequence.hilbertSchmidtNorm_eq
        (modulus_hasSameApproximationNumbers _)
    _ = ContinuousLinearMap.hilbertSchmidtNorm
        (complexify (U.starProjection - V.starProjection)) := by
      rw [starProjection_complexifySubmodule,
        starProjection_complexifySubmodule, complexify_sub]
    _ = ContinuousLinearMap.hilbertSchmidtNorm
        (U.starProjection - V.starProjection) :=
      hilbertSchmidtNorm_complexify _

/-- The source counterexample has angle `pi/4`, hence square sine norm one. -/
theorem counterexample_sine_square_norm :
    ContinuousLinearMap.hilbertSchmidtNorm
      (TauCeti.DavisKahan.Angle.Real.sinAngleOperatorRC
        counterexampleExact counterexampleTrial) = 1 := by
  rw [hilbertSchmidtNorm_sinAngleOperatorRC_eq_projectionDifference,
    hilbertSchmidtNorm_eq_frobenius,
    TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_basis (𝕜 := ℝ) (E := (PlanarModelSpace ℝ))
    (counterexampleExact.starProjection -
      counterexampleTrial.starProjection).toLinearMap
    realPlane_finrank (EuclideanSpace.basisFun (Fin 2) ℝ)]
  rw [Fin.sum_univ_two]
  simp only [EuclideanSpace.basisFun_apply]
  change Real.sqrt
    (‖(counterexampleExact.starProjection -
          counterexampleTrial.starProjection) (planarModelE0 (𝕜 := ℝ))‖ ^ 2 +
      ‖(counterexampleExact.starProjection -
          counterexampleTrial.starProjection) (planarModelE1 (𝕜 := ℝ))‖ ^ 2) = 1
  rw [counterexample_projectionDifference_e0,
    counterexample_projectionDifference_e1,
    real_norm_sq_combo, real_norm_sq_combo]
  norm_num

/-- The perturbation in the printed counterexample has square norm `sqrt 3`. -/
theorem counterexample_perturbation_square_norm :
    ContinuousLinearMap.hilbertSchmidtNorm counterexampleH = Real.sqrt 3 := by
  rw [hilbertSchmidtNorm_eq_frobenius,
    TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_basis (𝕜 := ℝ) (E := (PlanarModelSpace
      ℝ)) counterexampleH.toLinearMap
    realPlane_finrank (EuclideanSpace.basisFun (Fin 2) ℝ)]
  rw [Fin.sum_univ_two]
  simp only [EuclideanSpace.basisFun_apply]
  change Real.sqrt
    (‖counterexampleH (planarModelE0 (𝕜 := ℝ))‖ ^ 2 +
      ‖counterexampleH (planarModelE1 (𝕜 := ℝ))‖ ^ 2) = Real.sqrt 3
  rw [counterexampleH_e0, counterexampleH_e1,
    real_norm_sq_combo, real_norm_sq_combo]
  norm_num

/-- The single directional gap `delta=2` does not imply the symmetric
square-norm estimate. -/
theorem oneGap_does_not_imply_symmetric_square_estimate :
    ContinuousLinearMap.hilbertSchmidtNorm counterexampleH <
      2 * ContinuousLinearMap.hilbertSchmidtNorm
        (TauCeti.DavisKahan.Angle.Real.sinAngleOperatorRC
          counterexampleExact counterexampleTrial) := by
  rw [counterexample_sine_square_norm,
    counterexample_perturbation_square_norm]
  have hsqrt3 : Real.sqrt 3 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
  nlinarith

end Counterexample

end

end ExactSinTheta
end DavisKahan
end TauCeti
