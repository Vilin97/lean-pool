/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.OverlapDefinitions
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapLp
public import LeanPool.CoarseGraining.Homogenization.Multiscale.OverlapLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpCoordinate
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.OverlapCube
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.CubeVector

/-!
# Vector finite-`p` Poincare estimates on overlap cubes

The scalar overlap-cube estimate is transported here to the normalized vector
carrier used by the finite-`p` Calderon--Zygmund layer.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem scalarOverlap_normalizedCubeMeasure_eq_open {d : ℕ}
    (S : TriadicCube d) :
    ScalarOverlap.normalizedCubeMeasure S =
      ENNReal.ofReal ((overlapCubeVolume S)⁻¹) •
        volumeMeasureOn (openOverlapCubeSet S) := by
  change ENNReal.ofReal ((overlapCubeVolume S)⁻¹) •
      (volume.restrict (ScalarOverlap.cubeSet S)) = _
  change ENNReal.ofReal ((overlapCubeVolume S)⁻¹) •
      (volume.restrict (overlapCubeSet S)) = _
  rw [volume_restrict_overlapCubeSet_eq_volume_restrict_openOverlapCubeSet]

private theorem scalarOverlap_cubeAverage_eq_integralAverage_open {d : ℕ}
    (S : TriadicCube d) (f : Vec d → ℝ) :
    ScalarOverlap.cubeAverage S f = integralAverage (openOverlapCubeSet S) f := by
  simpa only [ScalarOverlap.cubeAverage, ScalarOverlap.cubeVolume,
    ScalarOverlap.cubeSet, ScalarOverlap.scaleFactor] using!
    overlapCubeAverage_eq_integralAverage_openOverlapCubeSet S f

private theorem scalar_overlap_coordinate_normalized_bound {d : ℕ} [NeZero d]
    (q : FiniteLpExponent) (C : ℝ)
    (hPoincare : ∀ (S : TriadicCube d) (u : W1pFunction (openOverlapCubeSet S) q.exponent),
      u.subAverageLpSeminorm ≤
        (C * overlapCubeScaleFactor S) * u.gradientCoordLpSeminormSum)
    (Q : TriadicCube d) (j : ℕ) (S : TriadicCube d)
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j)
    (V : CubeVectorW1pFunction Q q) (i : Fin d) :
    ENNReal.toReal (eLpNorm
        (fun x => V.toField x i - ScalarOverlap.cubeAverageVec S V.toField i)
        q.exponent (ScalarOverlap.normalizedCubeMeasure S)) ≤
      (C * overlapCubeScaleFactor S) *
        ∑ k : Fin d, ENNReal.toReal (eLpNorm (fun x => V.jacobian x i k)
          q.exponent (ScalarOverlap.normalizedCubeMeasure S)) := by
  have hsub : openOverlapCubeSet S ⊆ openCubeSet Q := by
    exact ScalarOverlap.openCubeSet_subset_openCubeSet_of_mem_centersAtDepth hS
  let w : W1pFunction (openOverlapCubeSet S) q.exponent :=
    (V.coord i).restrict (isOpen_openOverlapCubeSet S) hsub
  have hraw := hPoincare S w
  have havg : ScalarOverlap.cubeAverageVec S V.toField i =
      integralAverage (openOverlapCubeSet S) w.toFun := by
    simpa [ScalarOverlap.cubeAverageVec, w] using!
      (scalarOverlap_cubeAverage_eq_integralAverage_open S (fun x => V.toField x i))
  change ENNReal.toReal (eLpNorm
      (fun x => w.toFun x - integralAverage (openOverlapCubeSet S) w.toFun)
      q.exponent (volumeMeasureOn (openOverlapCubeSet S))) ≤
    (C * overlapCubeScaleFactor S) *
      ∑ k : Fin d, ENNReal.toReal (eLpNorm (fun x => w.grad x k)
        q.exponent (volumeMeasureOn (openOverlapCubeSet S))) at hraw
  rw [scalarOverlap_normalizedCubeMeasure_eq_open]
  rw [MeasureTheory.eLpNorm_smul_measure_of_ne_top q.lt_top.ne]
  simp_rw [MeasureTheory.eLpNorm_smul_measure_of_ne_top q.lt_top.ne]
  let A : ℝ :=
    (ENNReal.ofReal (overlapCubeVolume S)⁻¹ ^ (1 / q.exponent).toReal).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left hraw hA
  simpa [A, w, havg, ENNReal.toReal_mul, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm] using! hmul

private theorem memLp_overlap_vector_residual {d : ℕ} {Q S : TriadicCube d}
    {j : ℕ} (q : FiniteLpExponent) (hS : S ∈ ScalarOverlap.centersAtDepth Q j)
    (V : CubeVectorW1pFunction Q q) :
    MemLp (fun x => HilbertVec.ofVec
      (V.toField x - ScalarOverlap.cubeAverageVec S V.toField))
      q.exponent (ScalarOverlap.normalizedCubeMeasure S) := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  have hV := V.euclideanMemLp
  rw [MeasureTheory.memLp_piLp_iff] at hV
  have hcoord := ScalarOverlap.memLp_sub_cubeAverage_of_mem_centersAtDepth_of_memLp
    hS (hV i)
  simpa only [Function.comp_apply, HilbertVec.ofVec, PiLp.toLp_apply,
    V.toField_apply, Pi.sub_apply, ScalarOverlap.cubeAverageVec] using hcoord

private theorem memLp_overlap_jacobian {d : ℕ} {Q S : TriadicCube d}
    {j : ℕ} (q : FiniteLpExponent) (hS : S ∈ ScalarOverlap.centersAtDepth Q j)
    (V : CubeVectorW1pFunction Q q) :
    MemLp (fun x => HilbertMat.ofMat (V.jacobian x))
      q.exponent (ScalarOverlap.normalizedCubeMeasure S) := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  rw [MeasureTheory.memLp_piLp_iff]
  intro k
  have hV := V.jacobianHilbertMemLp
  rw [MeasureTheory.memLp_piLp_iff] at hV
  have hrow := hV i
  rw [MeasureTheory.memLp_piLp_iff] at hrow
  have hentry := ScalarOverlap.memLp_of_mem_centersAtDepth_of_memLp hS (hrow k)
  simpa only [Function.comp_apply, HilbertMat.ofMat, HilbertVec.ofVec,
    PiLp.toLp_apply, V.jacobian_apply] using hentry

private theorem eLpNorm_overlap_jacobian_entry_le {d : ℕ} {Q S : TriadicCube d}
    {j : ℕ} (q : FiniteLpExponent) (_hS : S ∈ ScalarOverlap.centersAtDepth Q j)
    (V : CubeVectorW1pFunction Q q) (i k : Fin d) :
    eLpNorm (fun x => V.jacobian x i k) q.exponent
      (ScalarOverlap.normalizedCubeMeasure S) ≤
    eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
      (ScalarOverlap.normalizedCubeMeasure S) := by
  apply eLpNorm_mono_ae
  filter_upwards [] with x
  calc
    ‖V.jacobian x i k‖ ≤
        ‖(HilbertMat.ofMat (V.jacobian x) : HilbertMat d).ofLp i‖ := by
      simpa only [HilbertMat.ofMat, HilbertVec.ofVec, PiLp.toLp_apply] using
        PiLp.norm_apply_le
          ((HilbertMat.ofMat (V.jacobian x) : HilbertMat d).ofLp i) k
    _ ≤ ‖HilbertMat.ofMat (V.jacobian x)‖ :=
      PiLp.norm_apply_le (HilbertMat.ofMat (V.jacobian x) : HilbertMat d) i

/-- The normalized finite-`p` Poincare estimate for vector fields on one
retained overlap cube. -/
theorem exists_overlapCubeVector_normalized_poincare_constant {d : ℕ} [NeZero d]
    (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (Q : TriadicCube d) (j : ℕ) (S : TriadicCube d),
        S ∈ ScalarOverlap.centersAtDepth Q j →
        ∀ V : CubeVectorW1pFunction Q q,
          eLpNorm
              (fun x => HilbertVec.ofVec
                (V.toField x - ScalarOverlap.cubeAverageVec S V.toField))
              q.exponent (ScalarOverlap.normalizedCubeMeasure S) ≤
            C * ENNReal.ofReal (overlapCubeScaleFactor S) *
              eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x))
                q.exponent (ScalarOverlap.normalizedCubeMeasure S) := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_overlapCube_subAverage_poincare_constant_finite (d := d) q
  let K : ℝ := (d : ℝ) * (d : ℝ) * (d : ℝ) * C
  refine ⟨ENNReal.ofReal K, ENNReal.ofReal_ne_top, ?_⟩
  intro Q j S hS V
  let μ : Measure (Vec d) := ScalarOverlap.normalizedCubeMeasure S
  let R : Vec d → Vec d :=
    fun x => V.toField x - ScalarOverlap.cubeAverageVec S V.toField
  have hRmem : MemLp (fun x => HilbertVec.ofVec (R x)) q.exponent μ := by
    simpa [μ, R] using memLp_overlap_vector_residual q hS V
  have hRcoord_mem : ∀ i : Fin d, MemLp (fun x => R x i) q.exponent μ := by
    intro i
    have hpi := hRmem
    rw [MeasureTheory.memLp_piLp_iff] at hpi
    simpa only [Function.comp_apply, HilbertVec.ofVec, PiLp.toLp_apply] using hpi i
  have hRcoord_meas : ∀ i : Fin d, AEStronglyMeasurable (fun x => R x i) μ :=
    fun i => (hRcoord_mem i).aestronglyMeasurable
  have hMmem : MemLp (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent μ := by
    simpa [μ] using memLp_overlap_jacobian q hS V
  have hsumR_top : (∑ i : Fin d, eLpNorm (fun x => R x i) q.exponent μ) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun i _ => (hRcoord_mem i).eLpNorm_ne_top
  have hrightR_top :
      ‖(d : ℝ)‖ₑ * ∑ i : Fin d, eLpNorm (fun x => R x i) q.exponent μ ≠ ∞ :=
    ENNReal.mul_ne_top enorm_ne_top hsumR_top
  have hvecENN :
      eLpNorm (fun x => HilbertVec.ofVec (R x)) q.exponent μ ≤
        ‖(d : ℝ)‖ₑ * ∑ i : Fin d, eLpNorm (fun x => R x i) q.exponent μ :=
    euclidean_eLpNorm_le_dimension_mul_sum_coordinates μ q R hRcoord_meas
  have hvec : ENNReal.toReal
      (eLpNorm (fun x => HilbertVec.ofVec (R x)) q.exponent μ) ≤
        ENNReal.toReal
          (‖(d : ℝ)‖ₑ * ∑ i : Fin d, eLpNorm (fun x => R x i) q.exponent μ) :=
    ENNReal.toReal_mono hrightR_top hvecENN
  have hscalar : ∀ i : Fin d,
      ENNReal.toReal (eLpNorm (fun x => R x i) q.exponent μ) ≤
        (C * overlapCubeScaleFactor S) *
          ∑ k : Fin d, ENNReal.toReal (eLpNorm (fun x => V.jacobian x i k)
            q.exponent μ) := by
    intro i
    simpa [μ, R] using scalar_overlap_coordinate_normalized_bound q C hC Q j S hS V i
  have hentry : ∀ i k : Fin d,
      ENNReal.toReal (eLpNorm (fun x => V.jacobian x i k) q.exponent μ) ≤
        ENNReal.toReal (eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x))
          q.exponent μ) := by
    intro i k
    exact ENNReal.toReal_mono hMmem.eLpNorm_ne_top
      (eLpNorm_overlap_jacobian_entry_le q hS V i k)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hright_top :
      ENNReal.ofReal K * ENNReal.ofReal (overlapCubeScaleFactor S) *
        eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent μ ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      hMmem.eLpNorm_ne_top
  refine (ENNReal.toReal_le_toReal hRmem.eLpNorm_ne_top hright_top).mp ?_
  have hvec' : ENNReal.toReal
      (eLpNorm (fun x => HilbertVec.ofVec (R x)) q.exponent μ) ≤
        (d : ℝ) * ∑ i : Fin d,
          ENNReal.toReal (eLpNorm (fun x => R x i) q.exponent μ) := by
    calc
      ENNReal.toReal (eLpNorm (fun x => HilbertVec.ofVec (R x)) q.exponent μ) ≤
          ENNReal.toReal
            (‖(d : ℝ)‖ₑ * ∑ i : Fin d, eLpNorm (fun x => R x i) q.exponent μ) := hvec
      _ = (d : ℝ) * ∑ i : Fin d,
          ENNReal.toReal (eLpNorm (fun x => R x i) q.exponent μ) := by
          rw [ENNReal.toReal_mul,
            ENNReal.toReal_sum (fun i _ => (hRcoord_mem i).eLpNorm_ne_top)]
          simp
  have hsum_scalar :
      ∑ i : Fin d, ENNReal.toReal (eLpNorm (fun x => R x i) q.exponent μ) ≤
        ∑ i : Fin d, (C * overlapCubeScaleFactor S) *
          ∑ k : Fin d, ENNReal.toReal (eLpNorm (fun x => V.jacobian x i k)
            q.exponent μ) := by
    exact Finset.sum_le_sum fun i _ => hscalar i
  have hsum_entry :
      ∑ i : Fin d, ∑ k : Fin d,
        ENNReal.toReal (eLpNorm (fun x => V.jacobian x i k) q.exponent μ) ≤
      ∑ _i : Fin d, ∑ _k : Fin d,
        ENNReal.toReal (eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x))
          q.exponent μ) := by
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hentry i k
  calc
    ENNReal.toReal (eLpNorm (fun x => HilbertVec.ofVec (R x)) q.exponent μ) ≤
        (d : ℝ) * ∑ i : Fin d,
          ENNReal.toReal (eLpNorm (fun x => R x i) q.exponent μ) := hvec'
    _ ≤ (d : ℝ) * ∑ i : Fin d, (C * overlapCubeScaleFactor S) *
          ∑ k : Fin d, ENNReal.toReal (eLpNorm (fun x => V.jacobian x i k)
            q.exponent μ) := by
          exact mul_le_mul_of_nonneg_left hsum_scalar (Nat.cast_nonneg d)
    _ = (d : ℝ) * (C * overlapCubeScaleFactor S) *
        ∑ i : Fin d, ∑ k : Fin d,
          ENNReal.toReal (eLpNorm (fun x => V.jacobian x i k) q.exponent μ) := by
          rw [← Finset.mul_sum]
          ring
    _ ≤ (d : ℝ) * (C * overlapCubeScaleFactor S) *
        ∑ _i : Fin d, ∑ _k : Fin d,
          ENNReal.toReal (eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x))
            q.exponent μ) := by
          exact mul_le_mul_of_nonneg_left hsum_entry
            (mul_nonneg (Nat.cast_nonneg d)
              (mul_nonneg hC_nonneg (overlapCubeScaleFactor_nonneg S)))
    _ = K * overlapCubeScaleFactor S *
        ENNReal.toReal (eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x))
          q.exponent μ) := by
          simp [K]
          ring
    _ = ENNReal.toReal (ENNReal.ofReal K * ENNReal.ofReal (overlapCubeScaleFactor S) *
        eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent μ) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
          simp [hK_nonneg, overlapCubeScaleFactor_nonneg]

end

end Homogenization
