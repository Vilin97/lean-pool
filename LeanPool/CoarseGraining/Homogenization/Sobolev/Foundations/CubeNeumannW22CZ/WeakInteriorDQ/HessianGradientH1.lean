/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.AnalyticInput
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.Solver

/-! # Hessian Gradient H1 -/

namespace Homogenization

open scoped ENNReal Topology

noncomputable section

/-!
# Gradient-coordinate `H¹` functions from weak Hessians

The Hessian-to-Besov part of C.2 needs to apply one-cube Poincare to each
component of the Poisson gradient on descendant cubes. This file packages the
basic Sobolev witness: a weak Hessian on `u` makes every coordinate
`∂ᵢu` into an `H¹` function with weak gradient given by the `i`th Hessian row.
-/

namespace HasWeakHessianOn

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

/-- The `i`th weak-gradient coordinate as an `H¹` function. Its weak gradient
is the `i`th row of the weak Hessian. -/
noncomputable def gradCoordH1Function (H : HasWeakHessianOn U u)
    (i : Fin d) : H1Function U where
  toFun := fun x => u.grad x i
  grad := fun x j => H.hess i j x
  memL2 := u.grad_memL2 i
  gradMemL2 := H.hess_memL2 i
  hasWeakGradient := H.weak_second i

@[simp] theorem gradCoordH1Function_apply
    (H : HasWeakHessianOn U u) (i : Fin d) (x : Vec d) :
    H.gradCoordH1Function i x = u.grad x i :=
  rfl

@[simp] theorem gradCoordH1Function_grad
    (H : HasWeakHessianOn U u) (i : Fin d) (x : Vec d) :
    (H.gradCoordH1Function i).grad x = fun j => H.hess i j x :=
  rfl

@[simp] theorem gradCoordH1Function_grad_apply
    (H : HasWeakHessianOn U u) (i j : Fin d) (x : Vec d) :
    (H.gradCoordH1Function i).grad x j = H.hess i j x :=
  rfl

/-- The coordinate-gradient `L²` sum of `∂ᵢu` is exactly the `i`th Hessian row
sum recorded by the Hessian witness. -/
theorem gradCoordH1Function_gradientCoordL2NormSum_eq
    (H : HasWeakHessianOn U u) (i : Fin d) :
    (H.gradCoordH1Function i).gradientCoordL2NormSum =
      ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ := by
  rfl

/-- Restricting the domain does not increase the `L²` norm of a Hessian row,
viewed as the weak gradient of the corresponding gradient coordinate. -/
theorem restrict_gradCoordH1Function_gradToVectorL2_norm_le
    (H : HasWeakHessianOn U u) {V : Set (Vec d)}
    (hVopen : IsOpen V) (hVU : V ⊆ U) (i : Fin d) :
    ‖((H.restrict hVopen hVU).gradCoordH1Function i).gradToVectorL2‖ ≤
      ‖(H.gradCoordH1Function i).gradToVectorL2‖ := by
  have hmono :
      MeasureTheory.eLpNorm (fun x => fun j : Fin d => H.hess i j x)
          (2 : ℝ≥0∞) (volumeMeasureOn V) ≤
        MeasureTheory.eLpNorm (fun x => fun j : Fin d => H.hess i j x)
          (2 : ℝ≥0∞) (volumeMeasureOn U) := by
    exact MeasureTheory.eLpNorm_mono_measure _
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU)
  have htop :
      MeasureTheory.eLpNorm (fun x => fun j : Fin d => H.hess i j x)
          (2 : ℝ≥0∞) (volumeMeasureOn U) ≠ ∞ := by
    exact ne_of_lt (H.gradCoordH1Function i).grad_memVectorL2.eLpNorm_lt_top
  rw [H1Function.gradToVectorL2, Homogenization.toVectorL2,
    MeasureTheory.Lp.norm_toLp]
  rw [H1Function.gradToVectorL2, Homogenization.toVectorL2,
    MeasureTheory.Lp.norm_toLp]
  exact ENNReal.toReal_mono htop hmono

private theorem h1Function_norm_gradToVectorL2_le_gradientCoordL2NormSum
    (v : H1Function U) :
    ‖v.gradToVectorL2‖ ≤ v.gradientCoordL2NormSum := by
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let D : Vec d → ℝ := fun x => ∑ j : Fin d, ‖v.grad x j‖
  have hcoord_mem :
      ∀ j : Fin d, MeasureTheory.MemLp (fun x => ‖v.grad x j‖)
        (2 : ℝ≥0∞) μ := by
    intro j
    simpa [μ] using (v.grad_memL2 j).norm
  have hD_mem : MeasureTheory.MemLp D (2 : ℝ≥0∞) μ := by
    have hsum :=
      MeasureTheory.memLp_finsetSum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := Finset.univ)
        (f := fun j : Fin d => fun x : Vec d => ‖v.grad x j‖)
        (fun j _hj => hcoord_mem j)
    simpa [D] using hsum
  have hD_memScalar : MemScalarL2 U D := by
    simpa [MemScalarL2, μ] using hD_mem
  let dCoordLp : ScalarL2 U := Homogenization.toScalarL2 hD_memScalar
  have hrow_le_sumLp : ‖v.gradToVectorL2‖ ≤ ‖dCoordLp‖ := by
    refine MeasureTheory.Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [H1Function.coeFn_gradToVectorL2 v,
      Homogenization.coeFn_toScalarL2 hD_memScalar] with x hrow hD
    rw [hrow, hD]
    have hD_nonneg : 0 ≤ D x := by
      exact Finset.sum_nonneg fun j _hj => norm_nonneg _
    have hvec_le : ‖v.grad x‖ ≤ D x := by
      refine (pi_norm_le_iff_of_nonneg hD_nonneg).2 ?_
      intro j
      exact Finset.single_le_sum
        (fun k _hk => norm_nonneg (v.grad x k))
        (Finset.mem_univ j)
    simpa [Real.norm_eq_abs, abs_of_nonneg hD_nonneg] using hvec_le
  have hsum_eLp :
      MeasureTheory.eLpNorm D (2 : ℝ≥0∞) μ ≤
        ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => ‖v.grad x j‖) (2 : ℝ≥0∞) μ := by
    have hD :
        D = ∑ j : Fin d, (fun x : Vec d => ‖v.grad x j‖) := by
      funext x
      simp [D]
    rw [hD]
    simpa using
      (MeasureTheory.eLpNorm_sum_le
        (μ := μ) (p := (2 : ℝ≥0∞)) (s := Finset.univ)
        (f := fun j : Fin d => fun x : Vec d => ‖v.grad x j‖)
        (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)))
  have hsum_toReal :
      ENNReal.toReal
          (∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => ‖v.grad x j‖) (2 : ℝ≥0∞) μ) =
        ∑ j : Fin d, ‖v.gradCoordToScalarL2 j‖ := by
    rw [ENNReal.toReal_sum (fun j _hj => (hcoord_mem j).eLpNorm_lt_top.ne)]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [MeasureTheory.eLpNorm_norm _ (v.grad_memL2 j).aestronglyMeasurable]
    simp [H1Function.gradCoordToScalarL2, Homogenization.toScalarL2,
      MeasureTheory.Lp.norm_toLp, μ]
  have hsumLp_le :
      ‖dCoordLp‖ ≤ v.gradientCoordL2NormSum := by
    calc
      ‖dCoordLp‖ = ENNReal.toReal (MeasureTheory.eLpNorm D (2 : ℝ≥0∞) μ) := by
          simp [dCoordLp, Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp,
            μ]
      _ ≤ ENNReal.toReal
            (∑ j : Fin d,
              MeasureTheory.eLpNorm (fun x => ‖v.grad x j‖) (2 : ℝ≥0∞) μ) := by
          refine ENNReal.toReal_mono ?_ hsum_eLp
          exact ENNReal.sum_ne_top.2 fun j _hj => (hcoord_mem j).eLpNorm_lt_top.ne
      _ = v.gradientCoordL2NormSum := by
          change
            ENNReal.toReal
                (∑ j : Fin d,
                  MeasureTheory.eLpNorm (fun x => ‖v.grad x j‖) (2 : ℝ≥0∞) μ) =
              ∑ j : Fin d, ‖v.gradCoordToScalarL2 j‖
          exact hsum_toReal
  exact hrow_le_sumLp.trans hsumLp_le

theorem gradCoordH1Function_gradToVectorL2_norm_le_rowCoordL2NormSum
    (H : HasWeakHessianOn U u) (i : Fin d) :
    ‖(H.gradCoordH1Function i).gradToVectorL2‖ ≤
      ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ := by
  calc
    ‖(H.gradCoordH1Function i).gradToVectorL2‖
        ≤ (H.gradCoordH1Function i).gradientCoordL2NormSum :=
          h1Function_norm_gradToVectorL2_le_gradientCoordL2NormSum
            (H.gradCoordH1Function i)
    _ = ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ :=
          H.gradCoordH1Function_gradientCoordL2NormSum_eq i

theorem gradCoordH1Function_gradToVectorL2_norm_le_hessianCoordL2NormSum
    (H : HasWeakHessianOn U u) (i : Fin d) :
    ‖(H.gradCoordH1Function i).gradToVectorL2‖ ≤
      H.hessianCoordL2NormSum := by
  have hrow :=
    H.gradCoordH1Function_gradToVectorL2_norm_le_rowCoordL2NormSum i
  have hrow_le_total :
      (∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖) ≤
        H.hessianCoordL2NormSum := by
    unfold HasWeakHessianOn.hessianCoordL2NormSum
    exact Finset.single_le_sum
      (fun k _hk => Finset.sum_nonneg fun j _hj => norm_nonneg _)
      (Finset.mem_univ i)
  exact hrow.trans hrow_le_total

end HasWeakHessianOn

namespace HasWeakHessianOn

variable {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}

private theorem cubePoissonRhs_toScalarL2_norm_le_coercive
    (hC : H1CoerciveEstimate (openCubeSet Q))
    (v : H1Function (openCubeSet Q))
    (hvOpen : MemScalarL2 (openCubeSet Q) (v.cubePoissonRhs Q)) :
    ‖Homogenization.toScalarL2 hvOpen‖ ≤
      hC.fixedValue * ‖v.gradToVectorL2‖ := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hLpEq :
      Homogenization.toScalarL2 hvOpen =
        (v.toMeanZeroOnCube Q).toScalarL2 := by
    apply MeasureTheory.Lp.ext
    filter_upwards
      [Homogenization.coeFn_toScalarL2 hvOpen,
        H1Function.coeFn_toScalarL2 (v.toMeanZeroOnCube Q).toH1Function]
      with x hx hmean
    rw [hx]
    change v.cubePoissonRhs Q x =
      (v.toMeanZeroOnCube Q).toH1Function.toScalarL2 x
    rw [hmean]
    simp
  have hPoincare :
      (v.toMeanZeroOnCube Q).valueL2Norm ≤
        hC.fixedValue * ‖v.gradToVectorL2‖ := by
    simpa [H1Function.toMeanZeroOnCube] using hC.bound_subAverage v
  simpa [H1MeanZeroFunction.valueL2Norm, hLpEq] using hPoincare

/-- One-cube Poincare applied to a gradient coordinate of a weak-Hessian
function, stated in normalized cube-oscillation form.

This is the single-cube ingredient for the later descendant summation:
`cubeBesovOscillation` of `∂ᵢu` is controlled by the coercive constant on the
cube and the `L²` norm of the Hessian row. -/
theorem cubeBesovOscillation_gradCoord_le_volumeFactor_mul_coerciveConst
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d)
    (hC : H1CoerciveEstimate (openCubeSet Q)) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.grad x i) ≤
      ((cubeVolume Q)⁻¹ + 1) * hC.fixedValue *
        ‖(H.gradCoordH1Function i).gradToVectorL2‖ := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let v : H1Function (openCubeSet Q) := H.gradCoordH1Function i
  have hvMem : MeasureTheory.MemLp (v.cubePoissonRhs Q) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    v.cubePoissonRhs_memL2_normalizedCubeMeasure
  let hvOpen : MemScalarL2 (openCubeSet Q) (v.cubePoissonRhs Q) :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hvMem
  have hnormOpen :
      ‖Homogenization.toScalarL2 hvOpen‖ ≤
        hC.fixedValue * ‖v.gradToVectorL2‖ := by
    exact cubePoissonRhs_toScalarL2_norm_le_coercive hC v hvOpen
  have hnorm :=
    cubeLpNorm_two_le_volume_inv_add_one_mul_norm_toScalarL2_openCubeSet
      Q hvMem
  calc
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.grad x i)
        = cubeLpNorm Q (2 : ℝ≥0∞) (v.cubePoissonRhs Q) := by
            have hosc :=
              H1Function.cubeBesovOscillation_eq_cubeLpNorm_cubePoissonRhs
                (Q := Q) (u := v)
            simpa [v] using hosc
    _ ≤ ((cubeVolume Q)⁻¹ + 1) * ‖Homogenization.toScalarL2 hvOpen‖ := by
          simpa [hvOpen] using hnorm
    _ ≤ ((cubeVolume Q)⁻¹ + 1) *
          (hC.fixedValue * ‖v.gradToVectorL2‖) := by
          exact mul_le_mul_of_nonneg_left hnormOpen
            (by
              have hInv : 0 ≤ (cubeVolume Q)⁻¹ :=
                inv_nonneg.mpr (cubeVolume_nonneg Q)
              linarith)
    _ = ((cubeVolume Q)⁻¹ + 1) * hC.fixedValue *
          ‖(H.gradCoordH1Function i).gradToVectorL2‖ := by
          rw [mul_assoc]

/-- Scale-sharp one-cube Poincare handoff for a gradient coordinate.

This is the same estimate as
`cubeBesovOscillation_gradCoord_le_volumeFactor_mul_coerciveConst`, but with
the exact q=2 normalized `L²` conversion factor `volume^{-1/2}`. This is the
form needed for the C.2 depth summation, where the descendant-count factor
cancels this normalization. -/
theorem cubeBesovOscillation_gradCoord_le_volumeInvRpowHalf_mul_coerciveConst
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d)
    (hC : H1CoerciveEstimate (openCubeSet Q)) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.grad x i) ≤
      ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * hC.fixedValue *
        ‖(H.gradCoordH1Function i).gradToVectorL2‖ := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let v : H1Function (openCubeSet Q) := H.gradCoordH1Function i
  have hvMem : MeasureTheory.MemLp (v.cubePoissonRhs Q) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    v.cubePoissonRhs_memL2_normalizedCubeMeasure
  let hvOpen : MemScalarL2 (openCubeSet Q) (v.cubePoissonRhs Q) :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hvMem
  have hnormOpen :
      ‖Homogenization.toScalarL2 hvOpen‖ ≤
        hC.fixedValue * ‖v.gradToVectorL2‖ := by
    exact cubePoissonRhs_toScalarL2_norm_le_coercive hC v hvOpen
  have hnorm :=
    cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openCubeSet
      Q hvMem
  calc
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.grad x i)
        = cubeLpNorm Q (2 : ℝ≥0∞) (v.cubePoissonRhs Q) := by
            have hosc :=
              H1Function.cubeBesovOscillation_eq_cubeLpNorm_cubePoissonRhs
                (Q := Q) (u := v)
            simpa [v] using hosc
    _ = ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
          ‖Homogenization.toScalarL2 hvOpen‖ := by
          simpa [hvOpen] using hnorm
    _ ≤ ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
          (hC.fixedValue * ‖v.gradToVectorL2‖) := by
          exact mul_le_mul_of_nonneg_left hnormOpen
            (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
    _ = ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * hC.fixedValue *
          ‖(H.gradCoordH1Function i).gradToVectorL2‖ := by
          rw [mul_assoc]

/-- Descendant-cube form of
`cubeBesovOscillation_gradCoord_le_volumeFactor_mul_coerciveConst`, obtained
by restricting the Hessian witness to the descendant open cube. -/
theorem cubeBesovOscillation_gradCoord_descendant_le_volumeFactor_mul_coerciveConst
    {R : TriadicCube d} {j : ℕ}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hR : R ∈ descendantsAtDepth Q j) (i : Fin d)
    (hC : H1CoerciveEstimate (openCubeSet R)) :
    cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => u.grad x i) ≤
      ((cubeVolume R)⁻¹ + 1) * hC.fixedValue *
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖ := by
  let HR : HasWeakHessianOn (openCubeSet R) (u.restrictToOpenSubcube hR) :=
    H.restrict (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
  have hmain :=
    HR.cubeBesovOscillation_gradCoord_le_volumeFactor_mul_coerciveConst i hC
  change
    cubeBesovOscillation R (2 : ℝ≥0∞)
        (fun x => (u.restrictToOpenSubcube hR).grad x i) ≤
      ((cubeVolume R)⁻¹ + 1) * hC.fixedValue *
        ‖(HR.gradCoordH1Function i).gradToVectorL2‖
  exact hmain

/-- Descendant-cube form of the scale-sharp one-cube Poincare handoff. -/
theorem cubeBesovOscillation_gradCoord_descendant_le_volumeInvRpowHalf_mul_coerciveConst
    {R : TriadicCube d} {j : ℕ}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hR : R ∈ descendantsAtDepth Q j) (i : Fin d)
    (hC : H1CoerciveEstimate (openCubeSet R)) :
    cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => u.grad x i) ≤
      ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * hC.fixedValue *
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖ := by
  let HR : HasWeakHessianOn (openCubeSet R) (u.restrictToOpenSubcube hR) :=
    H.restrict (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
  have hmain :=
    HR.cubeBesovOscillation_gradCoord_le_volumeInvRpowHalf_mul_coerciveConst i hC
  change
    cubeBesovOscillation R (2 : ℝ≥0∞)
        (fun x => (u.restrictToOpenSubcube hR).grad x i) ≤
      ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * hC.fixedValue *
        ‖(HR.gradCoordH1Function i).gradToVectorL2‖
  exact hmain

end HasWeakHessianOn

end

end Homogenization
