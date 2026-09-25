/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Regularity
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise
public import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix
public import LeanPool.CoarseGraining.Homogenization.PDE.DirichletRHS
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.Regularity
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.WeakDerivativeTestClosure
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.AnalyticInput
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalCubeBridge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Realization
public import Mathlib.Algebra.Order.Chebyshev

/-! # Basic -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise


/-!
# Discrete constant-coefficient Dirichlet Besov compatibility kernel

This file records the discrete compatibility kernel used by the legacy
K-functional/overlap route.  It is not the exact Lean contract for
`l.constant.coefficient.Dirichlet.Besov.function.spaces` pending the continuum
`K`/`H^s` gate.
-/

/-- Normalized cube `L²` data also gives vector `L²` data on the open cube.
This is the measure-conversion needed when normalized Besov data is paired
against Sobolev test gradients. -/
theorem memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure {d : ℕ}
    (Q : TriadicCube d) {f : Vec d → Vec d}
    (hf : MeasureTheory.MemLp f (2 : ENNReal) (normalizedCubeMeasure Q)) :
    MemVectorL2 (openCubeSet Q) f := by
  have hle :
      cubeMeasure Q ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    have hvol_nonneg : 0 ≤ cubeVolume Q := cubeVolume_nonneg Q
    have hmul :
        ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hvol_nonneg]
      have hreal : cubeVolume Q * (cubeVolume Q)⁻¹ = 1 := by
        field_simp [(cubeVolume_pos Q).ne']
      rw [hreal]
      norm_num
    have heq : ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q = cubeMeasure Q := by
      rw [normalizedCubeMeasure]
      ext s
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply]
      change
        ENNReal.ofReal (cubeVolume Q) *
            (ENNReal.ofReal ((cubeVolume Q)⁻¹) * (cubeMeasure Q) s) =
          (cubeMeasure Q) s
      rw [← mul_assoc, hmul, one_mul]
    exact le_of_eq heq.symm
  have hfCube :
      MeasureTheory.MemLp f (2 : ENNReal) (cubeMeasure Q) :=
    hf.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q))
      ENNReal.ofReal_ne_top hle
  simpa [MemVectorL2, volumeMeasureOn, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hfCube

/-- Monotonicity of the normalized cube average, with integrability supplied on
the underlying half-open cube. -/
theorem cubeAverage_le_of_le_on_cubeSet {d : ℕ} {Q : TriadicCube d}
    {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume)
    (hg : MeasureTheory.IntegrableOn g (cubeSet Q) MeasureTheory.volume)
    (hle : ∀ x ∈ cubeSet Q, f x ≤ g x) :
    cubeAverage Q f ≤ cubeAverage Q g := by
  unfold cubeAverage
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (cubeVolume_nonneg Q))
  exact
    MeasureTheory.integral_mono_ae hf hg <|
      (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
        Filter.Eventually.of_forall hle

/-- Jensen/Cauchy bound for the normalized scalar cube average. -/
theorem sq_cubeAverage_le_cubeAverage_sq_of_memLp {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    (cubeAverage Q f) ^ 2 ≤ cubeAverage Q (fun x => f x ^ 2) := by
  have hconst : MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const (1 : ℝ)
  have hholder :
      |cubeAverage Q (fun x => f x * (1 : ℝ))| ≤
        cubeLpNorm Q (2 : ℝ≥0∞) f *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => (1 : ℝ)) :=
    abs_cubeAverage_mul_le_mul_cubeLpNorm_of_holderConjugate
      Q (2 : ℝ≥0∞) (2 : ℝ≥0∞) f (fun _ : Vec d => (1 : ℝ)) hf hconst
  have hone :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => (1 : ℝ)) = 1 := by
    simpa using
      (cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ))
        (by norm_num))
  have habs : |cubeAverage Q f| ≤ cubeLpNorm Q (2 : ℝ≥0∞) f := by
    simpa [hone] using hholder
  have hsq :
      |cubeAverage Q f| ^ 2 ≤ (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) f)).mpr habs
  have hlp :
      (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ 2 =
        cubeAverage Q (fun x => ‖f x‖ ^ (2 : ℝ)) := by
    simpa using
      (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
        (Q := Q) (p := (2 : ℝ≥0∞)) (f := f)
        (by norm_num) (by norm_num) hf)
  calc
    (cubeAverage Q f) ^ 2 = |cubeAverage Q f| ^ 2 := by rw [sq_abs]
    _ ≤ (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ 2 := hsq
    _ = cubeAverage Q (fun x => f x ^ 2) := by
          rw [hlp]
          congr 1
          funext x
          simp [Real.norm_eq_abs, sq_abs]

/-- Coordinatewise Jensen/Cauchy bound for vector-valued cube averages. -/
theorem vecNormSq_cubeAverageVec_le_sum_cubeAverage_sq_of_memLp {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    vecNormSq (cubeAverageVec Q u) ≤
      ∑ i : Fin d, cubeAverage Q (fun x => (u x i) ^ 2) := by
  have hcoord : ∀ i : Fin d,
      (cubeAverage Q (fun x => u x i)) ^ 2 ≤
        cubeAverage Q (fun x => (u x i) ^ 2) := by
    intro i
    have hui : MeasureTheory.MemLp (fun x => u x i)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
    exact sq_cubeAverage_le_cubeAverage_sq_of_memLp Q (fun x => u x i) hui
  calc
    vecNormSq (cubeAverageVec Q u)
        = ∑ i : Fin d, (cubeAverage Q (fun x => u x i)) ^ 2 := by
            simp [cubeAverageVec, vecNormSq, vecDot, pow_two]
    _ ≤ ∑ i : Fin d, cubeAverage Q (fun x => (u x i) ^ 2) := by
            exact Finset.sum_le_sum fun i _hi => hcoord i

/-- The ambient Pi norm of a project vector is bounded by its Euclidean square
root. -/
theorem norm_le_sqrt_vecNormSq {d : ℕ} (v : Vec d) :
    ‖v‖ ≤ Real.sqrt (vecNormSq v) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_
  intro i
  have hsq : ‖v i‖ ^ (2 : ℕ) ≤ (Real.sqrt (vecNormSq v)) ^ (2 : ℕ) := by
    calc
      ‖v i‖ ^ (2 : ℕ) = v i ^ (2 : ℕ) := by
        rw [Real.norm_eq_abs, sq_abs]
      _ ≤ vecNormSq v := sq_apply_le_vecNormSq v i
      _ = (Real.sqrt (vecNormSq v)) ^ (2 : ℕ) := by
        rw [Real.sq_sqrt (vecNormSq_nonneg v)]
  exact le_of_sq_le_sq hsq (Real.sqrt_nonneg _)

theorem vecNormSq_le_card_mul_norm_sq {d : ℕ} (v : Vec d) :
    vecNormSq v ≤ (Fintype.card (Fin d) : ℝ) * ‖v‖ ^ 2 := by
  rw [vecNormSq, vecDot]
  calc
    (∑ i : Fin d, v i * v i) ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hcoord_abs : |v i| ≤ ‖v‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
      have hcoord_sq : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
        nlinarith [abs_nonneg (v i), norm_nonneg v]
      simpa [sq_abs, pow_two] using hcoord_sq
    _ = (Fintype.card (Fin d) : ℝ) * ‖v‖ ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem enorm_rpow_two_le_ofReal_vecNormSq {d : ℕ} (v : Vec d) :
    ‖v‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (vecNormSq v) := by
  have hnorm_sq_nat : ‖v‖ ^ (2 : ℕ) ≤ vecNormSq v := by
    have hnorm := norm_le_sqrt_vecNormSq v
    have hsq :
        ‖v‖ ^ (2 : ℕ) ≤
          (Real.sqrt (vecNormSq v)) ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg v) (Real.sqrt_nonneg _)).mpr hnorm
    simpa [Real.sq_sqrt (vecNormSq_nonneg v)] using hsq
  have hnorm_sq : ‖v‖ ^ (2 : ℝ) ≤ vecNormSq v := by
    simpa [Real.rpow_two] using hnorm_sq_nat
  calc
    ‖v‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal (‖v‖ ^ (2 : ℝ)) := by
          rw [← ofReal_norm]
          rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg v) (by norm_num)]
    _ ≤ ENNReal.ofReal (vecNormSq v) :=
          ENNReal.ofReal_le_ofReal hnorm_sq

theorem ofReal_vecNormSq_le_card_mul_enorm_rpow_two {d : ℕ} (v : Vec d) :
    ENNReal.ofReal (vecNormSq v) ≤
      (Fintype.card (Fin d) : ℝ≥0∞) * ‖v‖ₑ ^ (2 : ℝ) := by
  have hreal := vecNormSq_le_card_mul_norm_sq v
  calc
    ENNReal.ofReal (vecNormSq v)
        ≤ ENNReal.ofReal ((Fintype.card (Fin d) : ℝ) * ‖v‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hreal
    _ =
        (Fintype.card (Fin d) : ℝ≥0∞) * ‖v‖ₑ ^ (2 : ℝ) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          rw [ENNReal.ofReal_natCast]
          rw [← ofReal_norm]
          rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg v) (by norm_num)]
          rw [Real.rpow_two]

theorem H1Function.norm_gradToVectorL2_le_gradientCoordL2NormSum
    {d : ℕ} {U : Set (Vec d)} (v : H1Function U) :
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
  let dCoordLp : ScalarL2 U := Homogenization.toScalarL2 (by
    simpa [MemScalarL2, μ] using hD_mem)
  have hrow_le_sumLp : ‖v.gradToVectorL2‖ ≤ ‖dCoordLp‖ := by
    refine MeasureTheory.Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [H1Function.coeFn_gradToVectorL2 v,
      Homogenization.coeFn_toScalarL2 (by
        simpa [MemScalarL2, μ] using hD_mem)] with x hrow hD
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
        (fun j _hj => (hcoord_mem j).1)
        (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)))
  have hsum_toReal :
      ENNReal.toReal
          (∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => ‖v.grad x j‖) (2 : ℝ≥0∞) μ) =
        ∑ j : Fin d, ‖v.gradCoordToScalarL2 j‖ := by
    rw [ENNReal.toReal_sum (fun j _hj => (hcoord_mem j).2.ne)]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [MeasureTheory.eLpNorm_norm]
    simp [H1Function.gradCoordToScalarL2, Homogenization.toScalarL2,
      MeasureTheory.Lp.norm_toLp, μ]
  calc
    ‖v.gradToVectorL2‖ ≤ ‖dCoordLp‖ := hrow_le_sumLp
    _ = ENNReal.toReal (MeasureTheory.eLpNorm D (2 : ℝ≥0∞) μ) := by
          simp [dCoordLp, Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp, μ]
    _ ≤
        ENNReal.toReal
          (∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => ‖v.grad x j‖) (2 : ℝ≥0∞) μ) := by
          refine ENNReal.toReal_mono ?_ hsum_eLp
          exact ENNReal.sum_ne_top.2 fun j _hj => (hcoord_mem j).2.ne
    _ = v.gradientCoordL2NormSum := by
          simpa [H1Function.gradientCoordL2NormSum] using hsum_toReal

/-- The square of the normalized vector `L²` norm is controlled by the
normalized average of the Euclidean square. The dimension-free direction uses
`‖v‖_∞ ≤ |v|_2` pointwise. -/
theorem cubeLpNorm_two_sq_le_cubeAverage_vecNormSq {d : ℕ}
    {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ 2 ≤
      cubeAverage Q (fun x => vecNormSq (F x)) := by
  have hF_open : MemVectorL2 (cubeSet Q) F := by
    have hle :
        cubeMeasure Q ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
      have hvol_nonneg : 0 ≤ cubeVolume Q := cubeVolume_nonneg Q
      have hmul :
          ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
        rw [← ENNReal.ofReal_mul hvol_nonneg]
        have hreal : cubeVolume Q * (cubeVolume Q)⁻¹ = 1 := by
          field_simp [(cubeVolume_pos Q).ne']
        rw [hreal]
        norm_num
      have heq : ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q = cubeMeasure Q := by
        rw [normalizedCubeMeasure]
        ext s
        rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply]
        change
          ENNReal.ofReal (cubeVolume Q) *
              (ENNReal.ofReal ((cubeVolume Q)⁻¹) * (cubeMeasure Q) s) =
            (cubeMeasure Q) s
        rw [← mul_assoc, hmul, one_mul]
      exact le_of_eq heq.symm
    have hfCube :
        MeasureTheory.MemLp F (2 : ENNReal) (cubeMeasure Q) :=
      hF.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q))
        ENNReal.ofReal_ne_top hle
    simpa [MemVectorL2, volumeMeasureOn, cubeMeasure] using hfCube
  have hnorm_int :
      MeasureTheory.IntegrableOn (fun x => ‖F x‖ ^ (2 : ℕ))
        (cubeSet Q) MeasureTheory.volume := by
    have hF_vol : MeasureTheory.MemLp F (2 : ENNReal)
        (MeasureTheory.volume.restrict (cubeSet Q)) := by
      simpa [MemVectorL2, volumeMeasureOn] using hF_open
    simpa using!
      hF_vol.integrable_norm_rpow
        (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)
  have hvec_int :
      MeasureTheory.IntegrableOn (fun x => vecNormSq (F x))
        (cubeSet Q) MeasureTheory.volume := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hF_open hF_open
  have hnorm_eq :
      (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ (2 : ℕ) =
        cubeAverage Q (fun x => ‖F x‖ ^ (2 : ℕ)) := by
    simpa using
      cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
        (Q := Q) (p := (2 : ℝ≥0∞)) (f := F)
        (by norm_num) (by norm_num) hF
  rw [hnorm_eq]
  exact cubeAverage_le_of_le_on_cubeSet hnorm_int hvec_int fun x _hx => by
    have hsq :
        ‖F x‖ ^ (2 : ℕ) ≤ (Real.sqrt (vecNormSq (F x))) ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr
        (norm_le_sqrt_vecNormSq (F x))
    simpa [Real.sq_sqrt (vecNormSq_nonneg (F x))] using hsq

/-- Vector Cauchy-Schwarz for normalized cube averages, stated in the ambient
`cubeLpNorm` used by the K-functional layer. -/
theorem abs_cubeAverage_vecDot_le_card_mul_cubeLpNorm_two_mul {d : ℕ}
    (Q : TriadicCube d) (F G : Vec d → Vec d)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : MeasureTheory.MemLp G (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    |cubeAverage Q (fun x => vecDot (F x) (G x))| ≤
      (Fintype.card (Fin d) : ℝ) *
        cubeLpNorm Q (2 : ℝ≥0∞) F *
          cubeLpNorm Q (2 : ℝ≥0∞) G := by
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => F x i * G x i)
          (normalizedCubeMeasure Q) := by
    intro i
    have hFi : MeasureTheory.MemLp (fun x => F x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
      memLp_component_of_memLp F i hF
    have hGi : MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
      memLp_component_of_memLp G i hG
    simpa [Pi.mul_apply] using! hFi.integrable_mul hGi
  calc
    |cubeAverage Q (fun x => vecDot (F x) (G x))|
        ≤ ∑ i, |cubeBesovPairing Q (fun x => F x i) (fun x => G x i)| :=
          abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q F G hInt
    _ ≤ ∑ i,
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => F x i) *
            cubeLpNorm Q (2 : ℝ≥0∞) (fun x => G x i) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact abs_cubeBesovPairing_le_mul_cubeLpNorm_of_holderConjugate
            Q (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x i) (fun x => G x i)
            (memLp_component_of_memLp F i hF)
            (memLp_component_of_memLp G i hG)
    _ ≤ ∑ _i : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞) F *
            cubeLpNorm Q (2 : ℝ≥0∞) G := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact mul_le_mul
            (cubeLpNorm_two_component_le_cubeLpNorm_two Q F i hF)
            (cubeLpNorm_two_component_le_cubeLpNorm_two Q G i hG)
            (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x => G x i))
            (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F)
    _ =
        (Fintype.card (Fin d) : ℝ) *
          cubeLpNorm Q (2 : ℝ≥0∞) F *
            cubeLpNorm Q (2 : ℝ≥0∞) G := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring

theorem memScalarL2_of_contDiff_hasCompactSupport {d : ℕ}
    (U : Set (Vec d)) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_compact : HasCompactSupport ψ) :
    MemScalarL2 U ψ := by
  simpa [MemScalarL2, volumeMeasureOn] using
    (hψ.continuous.memLp_of_hasCompactSupport hψ_compact).restrict U

theorem memScalarL2_euclideanCoordDeriv_of_contDiff_hasCompactSupport
    {d : ℕ} (U : Set (Vec d)) (i : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_compact : HasCompactSupport ψ) :
    MemScalarL2 U (euclideanCoordDeriv i ψ) := by
  simpa [MemScalarL2, volumeMeasureOn] using
    ((contDiff_euclideanCoordDeriv hψ i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordDeriv hψ_compact i)).restrict U

namespace H1Function

/-- Weak integration by parts between an `H¹` function and a zero-trace `H¹`
test. -/
theorem integral_mul_zeroTrace_gradCoord_eq_neg_integral_gradCoord_mul
    {d : ℕ} {U : Set (Vec d)} (u : H1Function U)
    (φ : H10Function U) (i : Fin d) :
    ∫ x in U, u x * φ.toH1Function.grad x i ∂MeasureTheory.volume =
      -∫ x in U, u.grad x i * φ.toH1Function x ∂MeasureTheory.volume := by
  let Dapprox : ℕ → Vec d → ℝ := fun n x =>
    euclideanCoordDeriv i (φ.approx n) x
  have happroxL2 : ∀ n, MemScalarL2 U (φ.approx n) := by
    intro n
    exact memScalarL2_of_contDiff_hasCompactSupport
      U (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
  have hDapproxL2 : ∀ n, MemScalarL2 U (Dapprox n) := by
    intro n
    exact memScalarL2_euclideanCoordDeriv_of_contDiff_hasCompactSupport
      U i (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
  exact
    HasWeakPartialDerivOn.integral_mul_deriv_eq_neg_integral_mul_of_eLpNorm_approx
      (U := U) (i := i) (u := u.toFun) (gi := fun x => u.grad x i)
      (ψ := φ.toH1Function.toFun) (Dψ := fun x => φ.toH1Function.grad x i)
      (u.hasWeakPartialDerivOn i) u.memL2 (u.gradMemL2 i)
      φ.toH1Function.memL2 (φ.toH1Function.gradMemL2 i)
      φ.approx φ.approx_smooth φ.approx_hasCompactSupport φ.approx_support_subset
      happroxL2 (by
        intro n
        simpa [Dapprox] using hDapproxL2 n)
      φ.tendsto_approx (by
        simpa [Dapprox, euclideanCoordDeriv] using φ.tendsto_approx_grad i)

end H1Function


end

end Homogenization
