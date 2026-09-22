/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionFiniteP
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionScalarFiniteP

/-!
# Finite-`p` transport for mixed-parity Dirichlet reflections

Differentiating an all-odd scalar reflection in coordinate `i` changes the
cell parity from `S` to `S * s_i`. Differentiating once more in coordinate
`j` gives the Hessian-row parity `S * s_i * s_j`. This file records those
pointwise formulas and their exact finite-`p` norm transport. No weak
derivative assertion is made here.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The mixed scalar sign `S * s_i` on one reflection cell. -/
def cubeDirichletOddReflectionMixedCellSign {d : ℕ}
    (choice : Fin d → Fin 3) (i : Fin d) : ℝ :=
  cubeDirichletOddReflectionCellSign choice *
    if choice i = 1 then 1 else -1

@[simp] theorem cubeDirichletOddReflectionMixedCellSign_apply {d : ℕ}
    (choice : Fin d → Fin 3) (i : Fin d) :
    cubeDirichletOddReflectionMixedCellSign choice i =
      cubeDirichletOddReflectionCellSign choice *
        if choice i = 1 then 1 else -1 :=
  rfl

@[simp] theorem cubeDirichletOddReflectionMixedCellSign_mul_self
    {d : ℕ} (choice : Fin d → Fin 3) (i : Fin d) :
    cubeDirichletOddReflectionMixedCellSign choice i *
        cubeDirichletOddReflectionMixedCellSign choice i = 1 := by
  unfold cubeDirichletOddReflectionMixedCellSign
  calc
    (cubeDirichletOddReflectionCellSign choice *
        (if choice i = 1 then 1 else -1)) *
        (cubeDirichletOddReflectionCellSign choice *
          (if choice i = 1 then 1 else -1)) =
      (cubeDirichletOddReflectionCellSign choice *
          cubeDirichletOddReflectionCellSign choice) *
        ((if choice i = 1 then 1 else -1) *
          (if choice i = 1 then 1 else -1)) := by ring
    _ = 1 := by
      rw [cubeDirichletOddReflectionCellSign_mul_self]
      by_cases hi : choice i = 1 <;> simp [hi]

@[simp] theorem norm_cubeDirichletOddReflectionMixedCellSign
    {d : ℕ} (choice : Fin d → Fin 3) (i : Fin d) :
    ‖cubeDirichletOddReflectionMixedCellSign choice i‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Real.norm_eq_abs, sq_abs, one_pow, pow_two,
    cubeDirichletOddReflectionMixedCellSign_mul_self]

/-- The cellwise mixed reflection of a scalar gradient coordinate. -/
def cubeDirichletOddReflectionGradientCoordCellScalar {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) (i : Fin d)
    (v : Vec d → ℝ) : Vec d → ℝ :=
  fun x ↦ cubeDirichletOddReflectionMixedCellSign choice i *
    v (cubeFaceReflectionCellFoldMap Q choice x)

@[simp] theorem cubeDirichletOddReflectionGradientCoordCellScalar_apply
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (i : Fin d) (v : Vec d → ℝ) (x : Vec d) :
    cubeDirichletOddReflectionGradientCoordCellScalar Q choice i v x =
      cubeDirichletOddReflectionCellSign choice *
        (if choice i = 1 then 1 else -1) *
          v (cubeFaceReflectionCellFoldMap Q choice x) := by
  rw [cubeDirichletOddReflectionGradientCoordCellScalar,
    cubeDirichletOddReflectionMixedCellSign]

/-- The global mixed reflection of a scalar gradient coordinate. Its parity is
exactly `S * s_i`. -/
def cubeDirichletOddReflectionGradientCoordScalar {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (v : Vec d → ℝ) : Vec d → ℝ :=
  fun x ↦ cubeDirichletOddReflectionSign Q x *
    cubeCoordinateFoldSign Q x i * v (cubeCoordinateFold Q x)

@[simp] theorem cubeDirichletOddReflectionGradientCoordScalar_apply
    {d : ℕ} (Q : TriadicCube d) (i : Fin d)
    (v : Vec d → ℝ) (x : Vec d) :
    cubeDirichletOddReflectionGradientCoordScalar Q i v x =
      cubeDirichletOddReflectionSign Q x *
        cubeCoordinateFoldSign Q x i * v (cubeCoordinateFold Q x) :=
  rfl

/-- The mixed scalar reflection is the `i`th coordinate of the odd reflection
of the vector field supported in coordinate `i`. -/
theorem cubeDirichletOddReflectionGradientCoordScalar_eq_vectorField_singleCoordinate
    {d : ℕ} (Q : TriadicCube d) (i : Fin d)
    (v : Vec d → ℝ) (x : Vec d) :
    cubeDirichletOddReflectionGradientCoordScalar Q i v x =
      cubeDirichletOddReflectionVectorField Q
        (fun y j ↦ if j = i then v y else 0) x i := by
  simp only [cubeDirichletOddReflectionGradientCoordScalar,
    cubeDirichletOddReflectionVectorField,
    cubeCoordinateFoldReflectedVectorField,
    Pi.smul_apply, smul_eq_mul, if_pos]
  ring

/-- The cellwise mixed reflection of one Hessian row. Its `j`th coordinate
has parity `S * s_i * s_j`. -/
def cubeDirichletOddReflectionHessianRowCellVectorField {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) (i : Fin d)
    (R : Vec d → Vec d) : Vec d → Vec d :=
  fun x ↦ cubeDirichletOddReflectionMixedCellSign choice i •
    cubeFaceReflectionCellFoldLinear choice
      (R (cubeFaceReflectionCellFoldMap Q choice x))

@[simp] theorem cubeDirichletOddReflectionHessianRowCellVectorField_apply
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (i j : Fin d) (R : Vec d → Vec d) (x : Vec d) :
    cubeDirichletOddReflectionHessianRowCellVectorField Q choice i R x j =
      cubeDirichletOddReflectionCellSign choice *
        (if choice i = 1 then 1 else -1) *
          (if choice j = 1 then 1 else -1) *
            R (cubeFaceReflectionCellFoldMap Q choice x) j := by
  simp only [cubeDirichletOddReflectionHessianRowCellVectorField,
    cubeDirichletOddReflectionMixedCellSign, Pi.smul_apply, smul_eq_mul,
    cubeFaceReflectionCellFoldLinear_apply]
  by_cases hi : choice i = 1 <;> by_cases hj : choice j = 1 <;>
    simp only [hi, hj, if_true, if_false] <;> ring

/-- The global mixed reflection of one Hessian row. -/
def cubeDirichletOddReflectionHessianRowVectorField {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (R : Vec d → Vec d) :
    Vec d → Vec d :=
  fun x ↦
    (cubeDirichletOddReflectionSign Q x * cubeCoordinateFoldSign Q x i) •
      cubeCoordinateFoldReflectedVectorField Q R x

/-- The global Hessian-row formula exposes the exact chain-rule parity
`S * s_i * s_j`. -/
@[simp] theorem cubeDirichletOddReflectionHessianRowVectorField_apply
    {d : ℕ} (Q : TriadicCube d) (i j : Fin d)
    (R : Vec d → Vec d) (x : Vec d) :
    cubeDirichletOddReflectionHessianRowVectorField Q i R x j =
      cubeDirichletOddReflectionSign Q x *
        cubeCoordinateFoldSign Q x i * cubeCoordinateFoldSign Q x j *
          R (cubeCoordinateFold Q x) j := by
  simp only [cubeDirichletOddReflectionHessianRowVectorField,
    cubeCoordinateFoldReflectedVectorField, Pi.smul_apply, smul_eq_mul]
  ring

/-- The global mixed scalar agrees with its affine formula on each reflection
cell. -/
theorem cubeDirichletOddReflectionGradientCoordScalar_eq_cell_of_mem
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (i : Fin d) (v : Vec d → ℝ) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    cubeDirichletOddReflectionGradientCoordScalar Q i v x =
      cubeDirichletOddReflectionGradientCoordCellScalar Q choice i v x := by
  rw [cubeDirichletOddReflectionGradientCoordScalar,
    cubeDirichletOddReflectionGradientCoordCellScalar,
    cubeDirichletOddReflectionMixedCellSign,
    cubeDirichletOddReflectionSign_eq_cellSign_of_mem_cellCube Q choice hx,
    cubeCoordinateFoldSign_eq_cellFoldLinear_sign_of_mem_cellCube Q choice hx i,
    cubeCoordinateFold_eq_cubeFaceReflectionCellFoldMap_of_mem_cellCube Q choice hx]

/-- The global mixed Hessian row agrees with its affine formula on each
reflection cell. -/
theorem cubeDirichletOddReflectionHessianRowVectorField_eq_cell_of_mem
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (i : Fin d) (R : Vec d → Vec d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    cubeDirichletOddReflectionHessianRowVectorField Q i R x =
      cubeDirichletOddReflectionHessianRowCellVectorField Q choice i R x := by
  rw [cubeDirichletOddReflectionHessianRowVectorField,
    cubeDirichletOddReflectionHessianRowCellVectorField,
    cubeDirichletOddReflectionMixedCellSign,
    cubeDirichletOddReflectionSign_eq_cellSign_of_mem_cellCube Q choice hx,
    cubeCoordinateFoldSign_eq_cellFoldLinear_sign_of_mem_cellCube Q choice hx i,
    cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
      Q choice R hx]

/-- The mixed scalar is unchanged on the source cube. -/
theorem cubeDirichletOddReflectionGradientCoordScalar_eq_self_of_mem_openCubeSet
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (v : Vec d → ℝ)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    cubeDirichletOddReflectionGradientCoordScalar Q i v x = v x := by
  rw [cubeDirichletOddReflectionGradientCoordScalar,
    cubeDirichletOddReflectionSign_eq_one_of_mem_openCubeSet Q hx,
    cubeCoordinateFoldSign_eq_one_of_mem_openCubeSet Q hx i,
    cubeCoordinateFold_eq_self_of_mem_openCubeSet Q hx]
  norm_num

/-- The mixed Hessian row is unchanged on the source cube. -/
theorem cubeDirichletOddReflectionHessianRowVectorField_eq_self_of_mem_openCubeSet
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (R : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    cubeDirichletOddReflectionHessianRowVectorField Q i R x = R x := by
  rw [cubeDirichletOddReflectionHessianRowVectorField,
    cubeDirichletOddReflectionSign_eq_one_of_mem_openCubeSet Q hx,
    cubeCoordinateFoldSign_eq_one_of_mem_openCubeSet Q hx i,
    cubeCoordinateFoldReflectedVectorField_eq_self_of_mem_openCubeSet Q R hx]
  norm_num

private theorem norm_cubeCoordinateFoldSign {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) (i : Fin d) :
    ‖cubeCoordinateFoldSign Q x i‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Real.norm_eq_abs, sq_abs, one_pow, pow_two,
    cubeCoordinateFoldSign_mul_self]

private theorem eLpNorm_foldSign_smul {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : TriadicCube d) (i : Fin d) (f : Vec d → E)
    (p : ℝ≥0∞) (μ : MeasureTheory.Measure (Vec d)) :
    MeasureTheory.eLpNorm (fun x => cubeCoordinateFoldSign Q x i • f x) p μ =
      MeasureTheory.eLpNorm f p μ := by
  have hsign : MeasureTheory.AEStronglyMeasurable
      (fun x => cubeCoordinateFoldSign Q x i) μ := by
    apply Measurable.aestronglyMeasurable
    unfold cubeCoordinateFoldSign
    exact Measurable.ite
      (measurableSet_lt (measurable_pi_apply i) measurable_const) measurable_const
      (Measurable.ite
        (measurableSet_lt (measurable_pi_apply i) measurable_const)
        measurable_const measurable_const)
  have hback : MeasureTheory.AEStronglyMeasurable
      (fun x => cubeCoordinateFoldSign Q x i • f x) μ →
      MeasureTheory.AEStronglyMeasurable f μ := by
    intro h
    apply (hsign.smul h).congr
    exact MeasureTheory.ae_of_all _ fun x => by
      change cubeCoordinateFoldSign Q x i •
        (cubeCoordinateFoldSign Q x i • f x) = f x
      rw [smul_smul, cubeCoordinateFoldSign_mul_self, one_smul]
  by_cases hf : MeasureTheory.AEStronglyMeasurable f μ
  · apply MeasureTheory.eLpNorm_congr_norm_ae (hsign.smul hf) hf
    exact MeasureTheory.ae_of_all _ fun x => by
      change ‖cubeCoordinateFoldSign Q x i • f x‖ = ‖f x‖
      rw [norm_smul, norm_cubeCoordinateFoldSign, one_mul]
  · rw [MeasureTheory.eLpNorm_of_not_aestronglyMeasurable hf,
      MeasureTheory.eLpNorm_of_not_aestronglyMeasurable (fun h => hf (hback h))]

private theorem eLpNorm_gradientCoordScalar_eq_odd {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (v : Vec d → ℝ)
    (p : ℝ≥0∞) (μ : MeasureTheory.Measure (Vec d)) :
    MeasureTheory.eLpNorm (cubeDirichletOddReflectionGradientCoordScalar Q i v) p μ =
      MeasureTheory.eLpNorm (cubeDirichletOddReflectionScalar Q v) p μ := by
  have heq : cubeDirichletOddReflectionGradientCoordScalar Q i v =
      fun x => cubeCoordinateFoldSign Q x i • cubeDirichletOddReflectionScalar Q v x := by
    funext x
    simp only [cubeDirichletOddReflectionGradientCoordScalar,
      cubeDirichletOddReflectionScalar, smul_eq_mul]
    ring
  rw [heq]
  exact eLpNorm_foldSign_smul Q i _ p μ

private theorem eLpNorm_hessianRowVectorField_eq_odd {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (R : Vec d → Vec d)
    (p : ℝ≥0∞) (μ : MeasureTheory.Measure (Vec d)) :
    MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec (cubeDirichletOddReflectionHessianRowVectorField Q i R x))
      p μ = MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q R x)) p μ := by
  have heq : (fun x => HilbertVec.ofVec
      (cubeDirichletOddReflectionHessianRowVectorField Q i R x)) =
      fun x => cubeCoordinateFoldSign Q x i •
        HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q R x) := by
    funext x
    ext j
    simp only [cubeDirichletOddReflectionHessianRowVectorField_apply,
      cubeDirichletOddReflectionVectorField, cubeCoordinateFoldReflectedVectorField,
      Pi.smul_apply, smul_eq_mul, HilbertVec.ofVec, PiLp.smul_apply, PiLp.toLp_apply]
    ring
  rw [heq]
  exact eLpNorm_foldSign_smul Q i _ p μ

/-- The mixed scalar has the same pointwise norm as the all-odd scalar
reflection. -/
theorem norm_cubeDirichletOddReflectionGradientCoordScalar_eq_oddReflection
    {d : ℕ} (Q : TriadicCube d) (i : Fin d)
    (v : Vec d → ℝ) (x : Vec d) :
    ‖cubeDirichletOddReflectionGradientCoordScalar Q i v x‖ =
      ‖cubeDirichletOddReflectionScalar Q v x‖ := by
  have heq : cubeDirichletOddReflectionGradientCoordScalar Q i v x =
      cubeCoordinateFoldSign Q x i *
        cubeDirichletOddReflectionScalar Q v x := by
    simp only [cubeDirichletOddReflectionGradientCoordScalar,
      cubeDirichletOddReflectionScalar]
    ring
  rw [heq, norm_mul, norm_cubeCoordinateFoldSign, one_mul]

/-- The mixed Hessian row has the same pointwise Euclidean norm as the all-odd
vector reflection. -/
theorem norm_hilbertVec_cubeDirichletOddReflectionHessianRowVectorField_eq_oddReflection
    {d : ℕ} (Q : TriadicCube d) (i : Fin d)
    (R : Vec d → Vec d) (x : Vec d) :
    ‖HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField Q i R x)‖ =
      ‖HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q R x)‖ := by
  have heq :
      cubeDirichletOddReflectionHessianRowVectorField Q i R x =
        cubeCoordinateFoldSign Q x i •
          cubeDirichletOddReflectionVectorField Q R x := by
    ext j
    simp only [cubeDirichletOddReflectionHessianRowVectorField_apply,
      cubeDirichletOddReflectionVectorField, Pi.smul_apply, smul_eq_mul,
      cubeCoordinateFoldReflectedVectorField]
    ring
  rw [heq]
  change ‖cubeCoordinateFoldSign Q x i •
      HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q R x)‖ = _
  rw [norm_smul, norm_cubeCoordinateFoldSign, one_mul]

/-- The mixed scalar has the norm of the pulled-back scalar on each cell. -/
theorem norm_cubeDirichletOddReflectionGradientCoordCellScalar
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (i : Fin d) (v : Vec d → ℝ) (x : Vec d) :
    ‖cubeDirichletOddReflectionGradientCoordCellScalar Q choice i v x‖ =
      ‖v (cubeFaceReflectionCellFoldMap Q choice x)‖ := by
  rw [cubeDirichletOddReflectionGradientCoordCellScalar, norm_mul,
    norm_cubeDirichletOddReflectionMixedCellSign, one_mul]

/-- The mixed Hessian-row cell formula is a Euclidean isometry. -/
theorem norm_hilbertVec_cubeDirichletOddReflectionHessianRowCellVectorField
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (i : Fin d) (R : Vec d → Vec d) (x : Vec d) :
    ‖HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowCellVectorField Q choice i R x)‖ =
      ‖HilbertVec.ofVec (R (cubeFaceReflectionCellFoldMap Q choice x))‖ := by
  let r := R (cubeFaceReflectionCellFoldMap Q choice x)
  change ‖cubeDirichletOddReflectionMixedCellSign choice i •
      HilbertVec.ofVec (cubeFaceReflectionCellFoldLinear choice r)‖ =
    ‖HilbertVec.ofVec r‖
  rw [norm_smul, norm_cubeDirichletOddReflectionMixedCellSign, one_mul]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [HilbertVec.norm_sq_ofVec, HilbertVec.norm_sq_ofVec]
  calc
    vecDot (cubeFaceReflectionCellFoldLinear choice r)
        (cubeFaceReflectionCellFoldLinear choice r) = vecDot r r := by
      rw [← vecDot_cubeFaceReflectionCellFoldLinear_left choice
        (cubeFaceReflectionCellFoldLinear choice r) r,
        cubeFaceReflectionCellFoldLinear_involutive]

private theorem aestronglyMeasurable_gradientCoordScalar_cell
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (i : Fin d) (v : Vec d → ℝ)
    (hv : MeasureTheory.AEStronglyMeasurable v
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.AEStronglyMeasurable
      (cubeDirichletOddReflectionGradientCoordScalar Q i v)
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
  have hmp : MeasureTheory.MeasurePreserving
      (cubeFaceReflectionCellFoldMap Q choice)
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice)))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice] using
      (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
        (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
        (openCubeSet Q)
  have hcomp : MeasureTheory.AEStronglyMeasurable
      (fun x ↦ v (cubeFaceReflectionCellFoldMap Q choice x))
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    have hvmap : MeasureTheory.AEStronglyMeasurable v
        (MeasureTheory.Measure.map (cubeFaceReflectionCellFoldMap Q choice)
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice)))) := by
      rw [hmp.map_eq]
      exact hv
    simpa [Function.comp_def] using hvmap.comp_aemeasurable hmp.aemeasurable
  have hcell := hcomp.const_mul
    (cubeDirichletOddReflectionMixedCellSign choice i)
  refine hcell.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))] with x hx
  exact (cubeDirichletOddReflectionGradientCoordScalar_eq_cell_of_mem
    Q choice i v hx).symm

private theorem aestronglyMeasurable_hessianRow_cell
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (i : Fin d) (R : Vec d → Vec d)
    (hR : MeasureTheory.AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec (R x))
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField Q i R x))
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
  have hmp : MeasureTheory.MeasurePreserving
      (cubeFaceReflectionCellFoldMap Q choice)
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice)))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice] using
      (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
        (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
        (openCubeSet Q)
  have hcomp : MeasureTheory.AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec
        (R (cubeFaceReflectionCellFoldMap Q choice x)))
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    have hRmap : MeasureTheory.AEStronglyMeasurable
        (fun x ↦ HilbertVec.ofVec (R x))
        (MeasureTheory.Measure.map (cubeFaceReflectionCellFoldMap Q choice)
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice)))) := by
      rw [hmp.map_eq]
      exact hR
    simpa [Function.comp_def] using hRmap.comp_aemeasurable hmp.aemeasurable
  have hvec : MeasureTheory.AEStronglyMeasurable
      (fun x ↦ R (cubeFaceReflectionCellFoldMap Q choice x))
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    simpa using
      (HilbertVec.continuousLinearEquivVec d).continuous.comp_aestronglyMeasurable hcomp
  have hlinear :=
    (cubeFaceReflectionCellFoldLinear choice).continuous.comp_aestronglyMeasurable hvec
  have hcell : MeasureTheory.AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowCellVectorField Q choice i R x))
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    simpa only [cubeDirichletOddReflectionHessianRowCellVectorField] using!
      (HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable
        (hlinear.const_smul
          (cubeDirichletOddReflectionMixedCellSign choice i))
  refine hcell.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))] with x hx
  exact congrArg HilbertVec.ofVec
    (cubeDirichletOddReflectionHessianRowVectorField_eq_cell_of_mem
      Q choice i R hx).symm

private theorem aestronglyMeasurable_gradientCoordScalar_block
    {d : ℕ} {v : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hv : MeasureTheory.AEStronglyMeasurable v
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.AEStronglyMeasurable
      (cubeDirichletOddReflectionGradientCoordScalar Q i v)
      (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
  classical
  rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
  exact MeasureTheory.AEStronglyMeasurable.iUnion fun choice ↦
    aestronglyMeasurable_gradientCoordScalar_cell Q choice i v hv

private theorem aestronglyMeasurable_hessianRow_block
    {d : ℕ} {R : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d)
    (hR : MeasureTheory.AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec (R x))
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField Q i R x))
      (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
  classical
  rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
  exact MeasureTheory.AEStronglyMeasurable.iUnion fun choice ↦
    aestronglyMeasurable_hessianRow_cell Q choice i R hR

private theorem normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet
    {d : ℕ} (m : ℤ) :
    normalizedCubeMeasure (originCube d m) =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube]

private theorem restrict_openCubeSet_originCube_eq_smul_normalizedCubeMeasure
    {d : ℕ} (m : ℤ) :
    MeasureTheory.volume.restrict (openCubeSet (originCube d m)) =
      ENNReal.ofReal (cubeVolume (originCube d m)) •
        normalizedCubeMeasure (originCube d m) := by
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  rw [ENNReal.ofReal_inv_of_pos (cubeVolume_pos _)]
  rw [smul_smul]
  have hnonzero : ENNReal.ofReal (cubeVolume (originCube d m)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (cubeVolume_pos _)
  have hone : ENNReal.ofReal (cubeVolume (originCube d m)) *
      (ENNReal.ofReal (cubeVolume (originCube d m)))⁻¹ = 1 := by
    simpa [mul_comm] using
      ENNReal.inv_mul_cancel hnonzero ENNReal.ofReal_ne_top
  rw [hone, one_smul]

/-! ## Scalar-coordinate finite-`p` transport -/

/-- Exact finite-`p` norm transport for a mixed scalar on the full reflection
block. -/
theorem eLpNorm_cubeFaceReflectionBlockSet_gradientCoordScalar
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (v : Vec d → ℝ)
    (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (cubeDirichletOddReflectionGradientCoordScalar Q i v) p.exponent
      (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) =
      ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        MeasureTheory.eLpNorm v p.exponent
          (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  rw [eLpNorm_gradientCoordScalar_eq_odd Q i v p.exponent _]
  exact eLpNorm_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar Q v p

/-- `MemLp` transport for a mixed scalar on the full reflection block. -/
theorem memLp_cubeFaceReflectionBlockSet_gradientCoordScalar
    {d : ℕ} {v : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (p : FiniteLpExponent)
    (hv : MeasureTheory.MemLp v p.exponent
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.MemLp
      (cubeDirichletOddReflectionGradientCoordScalar Q i v) p.exponent
      (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
  have hodd :=
    memLp_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar Q p hv
  exact hodd.congr_norm
    (aestronglyMeasurable_gradientCoordScalar_block Q i hv.aestronglyMeasurable)
    (MeasureTheory.ae_of_all _ fun x ↦
      (norm_cubeDirichletOddReflectionGradientCoordScalar_eq_oddReflection
        Q i v x).symm)

/-- Exact unnormalized mixed-scalar norm transport from an origin cube to its
centered parent. -/
theorem eLpNorm_openCubeSet_succ_originCube_gradientCoordScalar
    {d : ℕ} {m : ℤ} (i : Fin d) (v : Vec d → ℝ)
    (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (cubeDirichletOddReflectionGradientCoordScalar (originCube d m) i v)
      p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1)))) =
      ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        MeasureTheory.eLpNorm v p.exponent
          (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
  rw [eLpNorm_gradientCoordScalar_eq_odd (originCube d m) i v p.exponent _]
  exact
    eLpNorm_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar v p

/-- `MemLp` transport for a mixed scalar from an origin cube to its centered
parent. -/
theorem memLp_openCubeSet_succ_originCube_gradientCoordScalar
    {d : ℕ} {m : ℤ} {v : Vec d → ℝ} (i : Fin d)
    (p : FiniteLpExponent)
    (hv : MeasureTheory.MemLp v p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d m)))) :
    MeasureTheory.MemLp
      (cubeDirichletOddReflectionGradientCoordScalar (originCube d m) i v)
      p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1)))) := by
  have hblock := memLp_cubeFaceReflectionBlockSet_gradientCoordScalar
    (originCube d m) i p hv
  have hmeasure :
      MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1))) =
        MeasureTheory.volume.restrict
          (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa using MeasureTheory.Measure.restrict_congr_set
      (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  rw [hmeasure]
  exact hblock

/-- Normalized mixed-scalar finite-`p` norms are exactly preserved from an
origin cube to its centered parent. -/
theorem eLpNorm_normalizedCubeMeasure_succ_originCube_gradientCoordScalar
    {d : ℕ} {m : ℤ} (i : Fin d) (v : Vec d → ℝ)
    (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (cubeDirichletOddReflectionGradientCoordScalar (originCube d m) i v)
      p.exponent (normalizedCubeMeasure (originCube d (m + 1))) =
      MeasureTheory.eLpNorm v p.exponent
        (normalizedCubeMeasure (originCube d m)) := by
  rw [eLpNorm_gradientCoordScalar_eq_odd (originCube d m) i v p.exponent _]
  exact
    eLpNorm_normalizedCubeMeasure_succ_originCube_cubeDirichletOddReflectionScalar
      v p

/-- Normalized `MemLp` is preserved by the mixed-scalar origin-cube
reflection. -/
theorem memLp_normalizedCubeMeasure_succ_originCube_gradientCoordScalar
    {d : ℕ} {m : ℤ} {v : Vec d → ℝ} (i : Fin d)
    (p : FiniteLpExponent)
    (hv : MeasureTheory.MemLp v p.exponent
      (normalizedCubeMeasure (originCube d m))) :
    MeasureTheory.MemLp
      (cubeDirichletOddReflectionGradientCoordScalar (originCube d m) i v)
      p.exponent (normalizedCubeMeasure (originCube d (m + 1))) := by
  have hvOpen : MeasureTheory.MemLp v p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
    rw [restrict_openCubeSet_originCube_eq_smul_normalizedCubeMeasure]
    exact hv.smul_measure ENNReal.ofReal_ne_top
  have hreflect :=
    memLp_openCubeSet_succ_originCube_gradientCoordScalar i p hvOpen
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  exact hreflect.smul_measure ENNReal.ofReal_ne_top

/-! ## Hessian-row finite-`p` transport -/

/-- Exact Euclidean finite-`p` norm transport for a mixed Hessian row on the
full reflection block. -/
theorem eLpNorm_cubeFaceReflectionBlockSet_hessianRowVectorField
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (R : Vec d → Vec d)
    (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField Q i R x))
      p.exponent (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) =
      ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        MeasureTheory.eLpNorm (fun x ↦ HilbertVec.ofVec (R x)) p.exponent
          (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  rw [eLpNorm_hessianRowVectorField_eq_odd Q i R p.exponent _]
  exact eLpNorm_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField
    Q R p

/-- Euclidean `MemLp` transport for a mixed Hessian row on the full reflection
block. -/
theorem memLp_cubeFaceReflectionBlockSet_hessianRowVectorField
    {d : ℕ} {R : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d)
    (p : FiniteLpExponent)
    (hR : MeasureTheory.MemLp (fun x ↦ HilbertVec.ofVec (R x)) p.exponent
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.MemLp
      (fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField Q i R x))
      p.exponent
      (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
  have hodd :=
    memLp_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField Q p hR
  exact hodd.congr_norm
    (aestronglyMeasurable_hessianRow_block Q i hR.aestronglyMeasurable)
    (MeasureTheory.ae_of_all _ fun x ↦
      (norm_hilbertVec_cubeDirichletOddReflectionHessianRowVectorField_eq_oddReflection
        Q i R x).symm)

/-- Exact unnormalized Euclidean norm transport for a mixed Hessian row from
an origin cube to its centered parent. -/
theorem eLpNorm_openCubeSet_succ_originCube_hessianRowVectorField
    {d : ℕ} {m : ℤ} (i : Fin d) (R : Vec d → Vec d)
    (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField
          (originCube d m) i R x))
      p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1)))) =
      ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        MeasureTheory.eLpNorm (fun x ↦ HilbertVec.ofVec (R x)) p.exponent
          (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
  rw [eLpNorm_hessianRowVectorField_eq_odd (originCube d m) i R p.exponent _]
  exact
    eLpNorm_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField R p

/-- Euclidean `MemLp` transport for a mixed Hessian row from an origin cube to
its centered parent. -/
theorem memLp_openCubeSet_succ_originCube_hessianRowVectorField
    {d : ℕ} {m : ℤ} {R : Vec d → Vec d} (i : Fin d)
    (p : FiniteLpExponent)
    (hR : MeasureTheory.MemLp (fun x ↦ HilbertVec.ofVec (R x)) p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d m)))) :
    MeasureTheory.MemLp
      (fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField
          (originCube d m) i R x))
      p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1)))) := by
  have hblock := memLp_cubeFaceReflectionBlockSet_hessianRowVectorField
    (originCube d m) i p hR
  have hmeasure :
      MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1))) =
        MeasureTheory.volume.restrict
          (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa using MeasureTheory.Measure.restrict_congr_set
      (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  rw [hmeasure]
  exact hblock

/-- Normalized Euclidean finite-`p` Hessian-row norms are exactly preserved
from an origin cube to its centered parent. -/
theorem eLpNorm_normalizedCubeMeasure_succ_originCube_hessianRowVectorField
    {d : ℕ} {m : ℤ} (i : Fin d) (R : Vec d → Vec d)
    (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField
          (originCube d m) i R x))
      p.exponent (normalizedCubeMeasure (originCube d (m + 1))) =
      MeasureTheory.eLpNorm (fun x ↦ HilbertVec.ofVec (R x)) p.exponent
        (normalizedCubeMeasure (originCube d m)) := by
  rw [eLpNorm_hessianRowVectorField_eq_odd (originCube d m) i R p.exponent _]
  exact
    eLpNorm_normalizedCubeMeasure_succ_originCube_cubeDirichletOddReflectionVectorField
      R p

/-- Normalized Euclidean `MemLp` is preserved by the mixed Hessian-row
origin-cube reflection. -/
theorem memLp_normalizedCubeMeasure_succ_originCube_hessianRowVectorField
    {d : ℕ} {m : ℤ} {R : Vec d → Vec d} (i : Fin d)
    (p : FiniteLpExponent)
    (hR : MeasureTheory.MemLp (fun x ↦ HilbertVec.ofVec (R x)) p.exponent
      (normalizedCubeMeasure (originCube d m))) :
    MeasureTheory.MemLp
      (fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField
          (originCube d m) i R x))
      p.exponent (normalizedCubeMeasure (originCube d (m + 1))) := by
  have hROpen : MeasureTheory.MemLp (fun x ↦ HilbertVec.ofVec (R x))
      p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
    rw [restrict_openCubeSet_originCube_eq_smul_normalizedCubeMeasure]
    exact hR.smul_measure ENNReal.ofReal_ne_top
  have hreflect :=
    memLp_openCubeSet_succ_originCube_hessianRowVectorField i p hROpen
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  exact hreflect.smul_measure ENNReal.ofReal_ne_top

end

end Homogenization
