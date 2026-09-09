/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

/-! The actual homogeneous first-order test space on ordinary Euclidean three-space. -/

noncomputable section

namespace EulerMeanGradientTest

open MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanCutoffCurl
open scoped ContDiff ENNReal NNReal

/-- Smooth compactly supported vector fields, as a genuine function submodule. -/
def testSpace : Submodule ℝ (Space → Space) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, by
    change IsCompact (tsupport (0 : Space → Space))
    simp⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c f hf := ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩

abbrev Test := ↥testSpace

theorem Test.smooth (f : Test) : ContDiff ℝ ∞ (f : Space → Space) := f.property.1

theorem Test.compact (f : Test) : HasCompactSupport (f : Space → Space) := f.property.2

theorem Test.column_memLp (f : Test) (i : Fin 3) :
    MemLp (fun x => fderiv ℝ (f : Space → Space) x (EuclideanSpace.single i 1)) 2 volume := by
  exact ((f.smooth.fderiv_right (m := ∞) (by simp)).continuous.clm_apply
    continuous_const).memLp_of_hasCompactSupport
    (f.compact.fderiv_apply ℝ (EuclideanSpace.single i 1))

/-- A genuine distributional/classical derivative column as an L² vector field. -/
def derivativeColumn (f : Test) (i : Fin 3) : L2 :=
  (f.column_memLp i).toLp _

theorem derivativeColumn_ae (f : Test) (i : Fin 3) :
    derivativeColumn f i =ᵐ[volume]
      fun x => fderiv ℝ (f : Space → Space) x (EuclideanSpace.single i 1) :=
  (f.column_memLp i).coeFn_toLp

theorem derivativeColumn_add (f g : Test) (i : Fin 3) :
    derivativeColumn (f + g) i = derivativeColumn f i + derivativeColumn g i := by
  apply Lp.ext
  filter_upwards [derivativeColumn_ae (f+g) i, derivativeColumn_ae f i,
    derivativeColumn_ae g i, Lp.coeFn_add (derivativeColumn f i) (derivativeColumn g i)]
    with x hfg hf hg ha
  simp only [Pi.add_apply] at ha
  rw [hfg, ha, hf, hg]
  change fderiv ℝ ((f : Space → Space) + (g : Space → Space)) x _ = _
  rw [fderiv_add ((f.smooth.differentiable (by simp)).differentiableAt)
    ((g.smooth.differentiable (by simp)).differentiableAt)]
  rfl

theorem derivativeColumn_smul (c : ℝ) (f : Test) (i : Fin 3) :
    derivativeColumn (c • f) i = c • derivativeColumn f i := by
  apply Lp.ext
  filter_upwards [derivativeColumn_ae (c • f) i, derivativeColumn_ae f i,
    Lp.coeFn_smul c (derivativeColumn f i)] with x hcf hf hs
  simp only [Pi.smul_apply] at hs
  rw [hcf, hs, hf]
  change fderiv ℝ (c • (f : Space → Space)) x _ = _
  rw [fderiv_const_smul ((f.smooth.differentiable (by simp)).differentiableAt) c]
  rfl

/-- The Hilbert space of three L² derivative columns, with the Frobenius norm. -/
abbrev GradientTensor := PiLp 2 (fun _ : Fin 3 => L2)

/-- The actual gradient map on compact smooth vector tests. -/
def testGradient : Test →ₗ[ℝ] GradientTensor where
  toFun f := WithLp.toLp 2 (fun i => derivativeColumn f i)
  map_add' f g := by ext i : 1; exact derivativeColumn_add f g i
  map_smul' c f := by ext i : 1; exact derivativeColumn_smul c f i

theorem testGradient_apply (f : Test) (i : Fin 3) :
    testGradient f i = derivativeColumn f i := rfl

/-- The operator norm is bounded by the sum of the Euclidean derivative-column norms. -/
theorem opNorm_le_sum_columns (A : Space →L[ℝ] Space) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (EuclideanSpace.single i 1)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  have hv : (∑ i : Fin 3, v i • (EuclideanSpace.single i 1 : Space)) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  calc
    ‖A v‖ = ‖∑ i : Fin 3, v i • A (EuclideanSpace.single i 1)‖ := by
      congr 1
      calc
        A v = A (∑ i : Fin 3, v i • (EuclideanSpace.single i 1 : Space)) := congrArg A hv.symm
        _ = _ := by simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • A (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖v i‖ * ‖A (EuclideanSpace.single i 1)‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖A (EuclideanSpace.single i 1)‖ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        (PiLp.norm_apply_le v i) (norm_nonneg _))
    _ = (∑ i : Fin 3, ‖A (EuclideanSpace.single i 1)‖) * ‖v‖ := by
      rw [← Finset.mul_sum, mul_comm]

/-- The derivative norm used by the cutoff bound is controlled by the actual Hilbert gradient norm. -/
theorem lpNorm_fderiv_le_gradient (f : Test) :
    lpNorm (fderiv ℝ (f : Space → Space)) 2 volume ≤ 3 * ‖testGradient f‖ := by
  let a : Fin 3 → Space → ℝ := fun i x =>
    ‖fderiv ℝ (f : Space → Space) x (EuclideanSpace.single i 1)‖
  have ha (i : Fin 3) : MemLp (a i) 2 volume := (f.column_memLp i).norm
  have hsum : MemLp (∑ i : Fin 3, a i) 2 volume := memLp_finsetSum' Finset.univ (fun i _ => ha i)
  calc
    lpNorm (fderiv ℝ (f : Space → Space)) 2 volume ≤ lpNorm (∑ i : Fin 3, a i) 2 volume :=
      lpNorm_mono_real hsum (fun x => by
        simpa [a] using (opNorm_le_sum_columns (fderiv ℝ (f : Space → Space) x)))
    _ ≤ ∑ i : Fin 3, lpNorm (a i) 2 volume := lpNorm_sum_le (fun i _ => ha i) (by norm_num)
    _ = ∑ i : Fin 3, ‖derivativeColumn f i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [derivativeColumn, Lp.norm_toLp, toReal_eLpNorm (f.column_memLp i).aestronglyMeasurable]
      exact lpNorm_norm (f.column_memLp i).aestronglyMeasurable 2
    _ ≤ ∑ _i : Fin 3, ‖testGradient f‖ :=
      Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le (testGradient f) i)
    _ = 3 * ‖testGradient f‖ := by simp

/-- Homogeneous H¹ is the closed subspace generated by actual compact test gradients. -/
def homogeneousSpace : Submodule ℝ GradientTensor := testGradient.range.topologicalClosure

instance : CompleteSpace homogeneousSpace :=
  testGradient.range.isClosed_topologicalClosure.completeSpace_coe

/-- The dense map from genuine tests into the homogeneous Hilbert space. -/
def homogeneousGradient : Test →ₗ[ℝ] homogeneousSpace :=
  testGradient.codRestrict homogeneousSpace
    (fun f => testGradient.range.le_topologicalClosure (LinearMap.mem_range_self _ f))

theorem homogeneousGradient_dense : DenseRange homogeneousGradient := by
  rw [DenseRange, Subtype.dense_iff]
  rw [← Set.range_comp]
  exact fun _ hx => hx

end EulerMeanGradientTest
