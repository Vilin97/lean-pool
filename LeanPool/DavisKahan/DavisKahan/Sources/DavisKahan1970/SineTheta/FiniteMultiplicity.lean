/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Sharpness
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.BlockSum
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNormLaws
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-! # Finite Multiplicity -/

open TauCeti.DavisKahan.Angle


/-!
# Finite-multiplicity equality models for Davis--Kahan Theorem 6.1

The planar model proves sharpness on one copy.  This file constructs the
literal orthogonal sum of `m` identical copies in one formula.  The exact and
complementary coordinate maps are the two inclusions into an `L²` product, the
trial map rotates every coordinate plane through the same angle, and the
ambient operator is zero on the exact block and `delta` on the complementary
block.

Consequently the residual is literally `delta` times the directed sine block.
The only ideal-theoretic point is that the complementary inclusion has finite
rank.  It is decomposed into `m` norm-one rank-one coordinate columns, proving
membership in every source norm without postulating finite-dimensional
membership as an extra assumption.
-/

namespace TauCeti
namespace DavisKahan1970

open DavisKahan

open scoped InnerProductSpace BigOperators ENNReal
open DavisKahan.ExactSinTheta
-- `IsometricEmbedding` is re-exported here from the bounded-operator layer.

noncomputable section

universe u

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Coordinate space for the multiplicity-`m` equality model. -/
abbrev FiniteMultiplicitySpace (𝕜 : Type u) [RCLike 𝕜] (m : ℕ) :=
  EuclideanSpace 𝕜 (Fin m)

/-- Ambient orthogonal sum of the exact and complementary coordinate spaces. -/
abbrev FiniteMultiplicityAmbient (𝕜 : Type u) [RCLike 𝕜] (m : ℕ) :=
  WithLp 2
    (FiniteMultiplicitySpace 𝕜 m × FiniteMultiplicitySpace 𝕜 m)

/-- Exact inclusion into the first orthogonal block. -/
def finiteMultiplicityExactMap (m : ℕ) :
    FiniteMultiplicitySpace 𝕜 m →L[𝕜] FiniteMultiplicityAmbient 𝕜 m :=
  blockInl

/-- Complementary inclusion into the second orthogonal block. -/
def finiteMultiplicityComplementMap (m : ℕ) :
    FiniteMultiplicitySpace 𝕜 m →L[𝕜] FiniteMultiplicityAmbient 𝕜 m :=
  blockInr

/-- Simultaneous rotation through `theta` in all `m` coordinate planes. -/
def finiteMultiplicityTrialMap (m : ℕ) (theta : ℝ) :
    FiniteMultiplicitySpace 𝕜 m →L[𝕜] FiniteMultiplicityAmbient 𝕜 m :=
  ((Real.cos theta : ℝ) : 𝕜) • finiteMultiplicityExactMap (𝕜 := 𝕜) m +
    ((Real.sin theta : ℝ) : 𝕜) • finiteMultiplicityComplementMap (𝕜 := 𝕜) m

/-- Two-level ambient operator, with eigenvalues zero and `delta`. -/
def finiteMultiplicityAmbientOperator (m : ℕ) (delta : ℝ) :
    FiniteMultiplicityAmbient 𝕜 m →L[𝕜] FiniteMultiplicityAmbient 𝕜 m :=
  continuousOrthogonalBlockSum
    (0 : FiniteMultiplicitySpace 𝕜 m →L[𝕜]
      FiniteMultiplicitySpace 𝕜 m)
    (((delta : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜
      (FiniteMultiplicitySpace 𝕜 m))

/-- Zero trial operator on the coordinate space. -/
def finiteMultiplicityTrialOperator (m : ℕ) :
    FiniteMultiplicitySpace 𝕜 m →L[𝕜] FiniteMultiplicitySpace 𝕜 m :=
  0

/-- Directed sine block of the multiplicity model. -/
def finiteMultiplicitySineBlock (m : ℕ) (theta : ℝ) :
    FiniteMultiplicitySpace 𝕜 m →L[𝕜] FiniteMultiplicityAmbient 𝕜 m :=
  ((Real.sin theta : ℝ) : 𝕜) •
    finiteMultiplicityComplementMap (𝕜 := 𝕜) m

/-- Residual of the multiplicity model. -/
def finiteMultiplicityResidual (m : ℕ) (delta theta : ℝ) :
    FiniteMultiplicitySpace 𝕜 m →L[𝕜] FiniteMultiplicityAmbient 𝕜 m :=
  (((delta * Real.sin theta : ℝ) : 𝕜) •
    finiteMultiplicityComplementMap (𝕜 := 𝕜) m)

/-- The finite-multiplicity exact embedding, unfolded. -/
@[simp]
theorem finiteMultiplicityExactMap_apply (m : ℕ)
    (x : FiniteMultiplicitySpace 𝕜 m) :
    finiteMultiplicityExactMap (𝕜 := 𝕜) m x =
      WithLp.toLp 2 (x, 0) :=
  rfl

/-- The finite-multiplicity complementary embedding, unfolded. -/
@[simp]
theorem finiteMultiplicityComplementMap_apply (m : ℕ)
    (x : FiniteMultiplicitySpace 𝕜 m) :
    finiteMultiplicityComplementMap (𝕜 := 𝕜) m x =
      WithLp.toLp 2 (0, x) :=
  rfl

/-- The simultaneous trial column is isometric. -/
theorem finiteMultiplicityTrialMap_isometry (m : ℕ) (theta : ℝ) :
    IsometricEmbedding (finiteMultiplicityTrialMap (𝕜 := 𝕜) m theta) := by
  intro x
  -- The rotated column is the single `L²` pair with the two scaled copies.
  have hval : finiteMultiplicityTrialMap (𝕜 := 𝕜) m theta x =
      WithLp.toLp 2 (((Real.cos theta : ℝ) : 𝕜) • x,
        ((Real.sin theta : ℝ) : 𝕜) • x) := by
    simp only [finiteMultiplicityTrialMap, add_apply,
      smul_apply, finiteMultiplicityExactMap_apply,
      finiteMultiplicityComplementMap_apply, ← WithLp.toLp_smul,
      ← WithLp.toLp_add]
    simp
  rw [hval]
  -- Compare squares: both sides are nonnegative and the `L²` product norm is
  -- stated for the square.
  have hsq : ‖WithLp.toLp 2 (((Real.cos theta : ℝ) : 𝕜) • x,
      ((Real.sin theta : ℝ) : 𝕜) • x)‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_smul, RCLike.norm_ofReal,
      mul_pow, sq_abs]
    rw [← add_mul, Real.cos_sq_add_sin_sq, one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg x)).mp hsq

/-- Direct calculation of the residual identity in every multiplicity. -/
theorem finiteMultiplicity_residual_identity (m : ℕ) (delta theta : ℝ) :
    finiteMultiplicityAmbientOperator (𝕜 := 𝕜) m delta ∘L
        finiteMultiplicityTrialMap (𝕜 := 𝕜) m theta -
      finiteMultiplicityTrialMap (𝕜 := 𝕜) m theta ∘L
        finiteMultiplicityTrialOperator (𝕜 := 𝕜) m =
      finiteMultiplicityResidual (𝕜 := 𝕜) m delta theta := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [finiteMultiplicityAmbientOperator, finiteMultiplicityTrialMap,
    finiteMultiplicityTrialOperator, finiteMultiplicityResidual]
  -- The two sides scale by the same real number but through different actions:
  -- iterated real scalars on the left, one coerced product on the right.
  rw [← map_mul, algebraMap_smul, smul_smul, mul_comm]

/-- The exact projection removes the first block and leaves exactly the
multiplicity-`m` sine block. -/
theorem finiteMultiplicity_directedSine_identity (m : ℕ) (theta : ℝ) :
    (ContinuousLinearMap.id 𝕜 (FiniteMultiplicityAmbient 𝕜 m) -
        finiteMultiplicityExactMap (𝕜 := 𝕜) m ∘L
          (finiteMultiplicityExactMap (𝕜 := 𝕜) m).adjoint) ∘L
      finiteMultiplicityTrialMap (𝕜 := 𝕜) m theta =
        finiteMultiplicitySineBlock (𝕜 := 𝕜) m theta := by
  ext x
  -- The adjoint of the first block inclusion is the first coordinate map.
  have hadj :
      (finiteMultiplicityExactMap (𝕜 := 𝕜) m).adjoint =
        WithLp.fstL 2 𝕜
          (FiniteMultiplicitySpace 𝕜 m)
          (FiniteMultiplicitySpace 𝕜 m) := by
    -- `eq_adjoint_iff` characterises `A = adjoint B`, so the equation has to be
    -- turned around first.
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro y z
    simp [finiteMultiplicityExactMap]
  rw [hadj]
  apply WithLp.ofLp_injective 2
  simp [finiteMultiplicityTrialMap, finiteMultiplicitySineBlock]

/-- Scalar column into an arbitrary Hilbert space. -/
def finiteMultiplicityScalarColumn
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (v : H) : 𝕜 →L[𝕜] H :=
  (ContinuousLinearMap.id 𝕜 𝕜).smulRight v

/-- The `i`th coordinate column of the complementary inclusion. -/
def finiteMultiplicityCoordinateColumn (m : ℕ) (i : Fin m) :
    FiniteMultiplicitySpace 𝕜 m →L[𝕜] FiniteMultiplicityAmbient 𝕜 m :=
  finiteMultiplicityScalarColumn
      (finiteMultiplicityComplementMap (𝕜 := 𝕜) m
        ((EuclideanSpace.basisFun (Fin m) 𝕜) i)) ∘L
    EuclideanSpace.proj i

/-- Each coordinate column is norm-one and rank at most one. -/
theorem finiteMultiplicityCoordinateColumn_norm_rank (m : ℕ) (i : Fin m) :
    ‖finiteMultiplicityCoordinateColumn (𝕜 := 𝕜) m i‖ = 1 ∧
      (finiteMultiplicityCoordinateColumn (𝕜 := 𝕜) m i).rank ≤
        (1 : Cardinal) := by
  let b := EuclideanSpace.basisFun (Fin m) 𝕜
  let v := finiteMultiplicityComplementMap (𝕜 := 𝕜) m (b i)
  have hb : ‖b i‖ = 1 := b.orthonormal.1 i
  have hv : ‖v‖ = 1 := by simp [v, hb]
  have hscalar : ‖finiteMultiplicityScalarColumn (𝕜 := 𝕜) v‖ = 1 := by
    rw [finiteMultiplicityScalarColumn,
      ContinuousLinearMap.norm_smulRight_apply,
      ContinuousLinearMap.norm_id, one_mul, hv]
  -- The coordinate functional is the inner product against a unit coordinate
  -- vector, so Cauchy--Schwarz bounds it.  Only the upper bound is needed here;
  -- the matching lower bound is established separately below, so the stated
  -- equality is unaffected.
  have hproj : ‖(EuclideanSpace.proj i :
      FiniteMultiplicitySpace 𝕜 m →L[𝕜] 𝕜)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    have hx : (EuclideanSpace.proj i :
        FiniteMultiplicitySpace 𝕜 m →L[𝕜] 𝕜) x =
        ⟪(EuclideanSpace.single i (1 : 𝕜) :
          FiniteMultiplicitySpace 𝕜 m), x⟫_𝕜 := by
      simp [EuclideanSpace.inner_single_left]
    rw [hx, one_mul]
    calc
      ‖⟪(EuclideanSpace.single i (1 : 𝕜) :
          FiniteMultiplicitySpace 𝕜 m), x⟫_𝕜‖
          ≤ ‖(EuclideanSpace.single i (1 : 𝕜) :
              FiniteMultiplicitySpace 𝕜 m)‖ * ‖x‖ :=
        norm_inner_le_norm _ _
      _ = ‖x‖ := by simp
  constructor
  · apply le_antisymm
    · calc
        ‖finiteMultiplicityCoordinateColumn (𝕜 := 𝕜) m i‖ ≤
            ‖finiteMultiplicityScalarColumn (𝕜 := 𝕜) v‖ *
              ‖(EuclideanSpace.proj i :
                FiniteMultiplicitySpace 𝕜 m →L[𝕜] 𝕜)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * 1 :=
          mul_le_mul hscalar.le hproj (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · have hlower :=
        (finiteMultiplicityCoordinateColumn (𝕜 := 𝕜) m i).le_opNorm (b i)
      simpa [finiteMultiplicityCoordinateColumn,
        finiteMultiplicityScalarColumn, b, v, hb, hv] using hlower
  · change LinearMap.rank
        ((finiteMultiplicityScalarColumn (𝕜 := 𝕜) v).toLinearMap.comp
          (EuclideanSpace.proj i).toLinearMap) ≤ 1
    calc
      LinearMap.rank
          ((finiteMultiplicityScalarColumn (𝕜 := 𝕜) v).toLinearMap.comp
            (EuclideanSpace.proj i).toLinearMap) ≤
          LinearMap.rank
            (finiteMultiplicityScalarColumn (𝕜 := 𝕜) v).toLinearMap :=
        LinearMap.rank_comp_le_left _ _
      _ ≤ Module.rank 𝕜 𝕜 := LinearMap.rank_le_domain _
      _ = 1 := by simp

/-- The complementary inclusion is the sum of its rank-one coordinate
columns. -/
theorem finiteMultiplicityComplementMap_eq_sum_coordinateColumn (m : ℕ) :
    finiteMultiplicityComplementMap (𝕜 := 𝕜) m =
      ∑ i : Fin m, finiteMultiplicityCoordinateColumn (𝕜 := 𝕜) m i := by
  let b := EuclideanSpace.basisFun (Fin m) 𝕜
  ext x
  rw [← b.sum_repr x]
  simp [finiteMultiplicityCoordinateColumn, finiteMultiplicityScalarColumn,
    b, map_sum]

/-- Membership in a source ideal is closed under addition.

The gauge triangle inequality is what makes this true, and it is available for
the real and complex scalar fields; it is a property of the field, not an
assumption about the operators involved. -/
theorem SymmetricNormingFunction.mem_add
    (N : SymmetricNormingFunction)
    {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.Mem (A + B) := by
  intro htop
  have hle := N.extendedGauge_add_le A B
  rw [htop] at hle
  exact (ENNReal.add_ne_top.mpr ⟨hA, hB⟩) (top_le_iff.mp hle)

/-- Membership in a source ideal is closed under finite sums. -/
theorem SymmetricNormingFunction.mem_finset_sum
    (N : SymmetricNormingFunction)
    {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {ι : Type*} {s : Finset ι} {A : ι → E →L[𝕜] F}
    (hA : ∀ i ∈ s, N.Mem (A i)) :
    N.Mem (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro htop
      rw [Finset.sum_empty, N.extendedGauge_zero] at htop
      simp at htop
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      -- These live in the source-facade namespace, not the implementation
      -- namespace of `SymmetricNormingFunction`, so dot notation cannot find
      -- them.
      exact SymmetricNormingFunction.mem_add N
        (hA i (Finset.mem_insert_self i s))
        (ih fun j hj => hA j (Finset.mem_insert_of_mem hj))

/-- The multiplicity-`m` complementary inclusion belongs to every source
unitarily invariant ideal. -/
theorem finiteMultiplicityComplementMap_mem
    (m : ℕ) (N : SymmetricNormingFunction) :
    N.Mem (finiteMultiplicityComplementMap (𝕜 := 𝕜) m) := by
  rw [finiteMultiplicityComplementMap_eq_sum_coordinateColumn]
  simpa using
    SymmetricNormingFunction.mem_finset_sum N
      (s := Finset.univ)
      (A := fun i => finiteMultiplicityCoordinateColumn (𝕜 := 𝕜) m i)
      (fun i _ => N.mem_rankOne
        (finiteMultiplicityCoordinateColumn_norm_rank
          (𝕜 := 𝕜) m i).1
        (finiteMultiplicityCoordinateColumn_norm_rank
          (𝕜 := 𝕜) m i).2)

/-- The sine block belongs to every source ideal. -/
theorem finiteMultiplicitySineBlock_mem
    (m : ℕ) (theta : ℝ) (N : SymmetricNormingFunction) :
    N.Mem (finiteMultiplicitySineBlock (𝕜 := 𝕜) m theta) := by
  unfold finiteMultiplicitySineBlock SymmetricNormingFunction.Mem
  rw [N.extendedGauge_smul]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (finiteMultiplicityComplementMap_mem (𝕜 := 𝕜) m N)

/-- Equality in Theorem 6.1 at every finite multiplicity and simultaneously
for every normalized source norm. -/
theorem Theorem6_1_finiteMultiplicity_equality_every_norm
    (m : ℕ) (N : SymmetricNormingFunction)
    {delta theta : ℝ} (hdelta : 0 ≤ delta) :
    N.gauge (finiteMultiplicityResidual (𝕜 := 𝕜) m delta theta) =
      delta * N.gauge (finiteMultiplicitySineBlock (𝕜 := 𝕜) m theta) := by
  have hmem := finiteMultiplicityComplementMap_mem (𝕜 := 𝕜) m N
  rw [finiteMultiplicityResidual, finiteMultiplicitySineBlock,
    N.gauge_smul _ hmem, N.gauge_smul _ hmem]
  simp [abs_of_nonneg hdelta]
  ring

/-- At a nonzero sine angle the model has an injective sine block on an
`m`-dimensional coordinate space, so it is a genuine multiplicity-`m` model
rather than a scalar homogeneity restatement. -/
theorem finiteMultiplicitySineBlock_injective
    (m : ℕ) {theta : ℝ} (htheta : Real.sin theta ≠ 0) :
    Function.Injective (finiteMultiplicitySineBlock (𝕜 := 𝕜) m theta) := by
  intro x y hxy
  have hc : (((Real.sin theta : ℝ) : 𝕜)) ≠ 0 := by
    exact_mod_cast htheta
  apply_fun WithLp.sndL 2 𝕜
      (FiniteMultiplicitySpace 𝕜 m)
      (FiniteMultiplicitySpace 𝕜 m) at hxy
  simp only [finiteMultiplicitySineBlock, smul_apply,
    finiteMultiplicityComplementMap_apply, map_smul, WithLp.sndL_apply,
    WithLp.toLp_snd] at hxy
  -- Cancel in `𝕜`.  Letting the scalar normalise to the real action instead
  -- would need a separate no-zero-smul-divisors instance over `ℝ`.
  exact smul_right_injective _ hc hxy

end

end DavisKahan1970
end TauCeti
