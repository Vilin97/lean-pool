/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentL2
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotient

/-! # Reflection Parent Approx -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal Topology

noncomputable section

variable {d : ℕ} {m : ℤ}

/-- For Hilbert-valued `L²` functions, the square of the `toReal` `eLpNorm`
is the integral of the pointwise squared norm. -/
theorem toReal_eLpNorm_two_sq_eq_integral_norm_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] {μ : MeasureTheory.Measure α} {f : α → E}
    (hf : MeasureTheory.MemLp f 2 μ) :
    (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hpow : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by
    norm_num
  have hnorm :=
    hf.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by simp : (2 : ℝ≥0∞) ≠ ⊤)
  have hsq_norm :
      (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ 2 =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
    rw [hnorm, hpow]
    have hint_nonneg :
        0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
      exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (norm_nonneg (f x)) _)
    rw [ENNReal.toReal_ofReal]
    · rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hint_nonneg
    · exact Real.rpow_nonneg hint_nonneg _
  calc
    (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ 2 =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := hsq_norm
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
          congr 1 with x
          rw [Real.rpow_two]

/-- Scalar all-face reflection distributes over subtraction. -/
@[simp] theorem cubeCoordinateFoldReflectedScalar_sub_apply
    (Q : TriadicCube d) (F U : Vec d → ℝ) (x : Vec d) :
    cubeCoordinateFoldReflectedScalar Q (fun y => F y - U y) x =
      cubeCoordinateFoldReflectedScalar Q F x -
        cubeCoordinateFoldReflectedScalar Q U x := by
  rfl

/-- Vector all-face reflection distributes over subtraction. -/
@[simp] theorem cubeCoordinateFoldReflectedVectorField_sub_apply
    (Q : TriadicCube d) (G H : Vec d → Vec d) (x : Vec d) :
    cubeCoordinateFoldReflectedVectorField Q (fun y => G y - H y) x =
      cubeCoordinateFoldReflectedVectorField Q G x -
        cubeCoordinateFoldReflectedVectorField Q H x := by
  ext i
  simp [cubeCoordinateFoldReflectedVectorField, sub_eq_add_neg, mul_add]

/-- Reflected scalar differences are `L²` on the centered parent cube whenever
the original difference is `L²` on the origin cube. -/
theorem memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sub
    {F U : Vec d → ℝ}
    (hFU : MemScalarL2 (openCubeSet (originCube d m)) (fun x => F x - U x)) :
    MemScalarL2 (openCubeSet (originCube d (m + 1)))
      (fun x =>
        cubeCoordinateFoldReflectedScalar (originCube d m) F x -
          cubeCoordinateFoldReflectedScalar (originCube d m) U x) := by
  simpa using!
    memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
      (m := m) hFU

/-- Reflected vector-field differences are `L²` on the centered parent cube
whenever the original difference is `L²` on the origin cube. -/
theorem memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_sub
    {G H : Vec d → Vec d}
    (hGH : MemVectorL2 (openCubeSet (originCube d m)) (fun x => G x - H x)) :
    MemVectorL2 (openCubeSet (originCube d (m + 1)))
      (fun x =>
        cubeCoordinateFoldReflectedVectorField (originCube d m) G x -
          cubeCoordinateFoldReflectedVectorField (originCube d m) H x) := by
  have hfun :
      cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun x => G x - H x) =
        fun x =>
          cubeCoordinateFoldReflectedVectorField (originCube d m) G x -
            cubeCoordinateFoldReflectedVectorField (originCube d m) H x := by
    funext x
    exact cubeCoordinateFoldReflectedVectorField_sub_apply
      (originCube d m) G H x
  simpa [hfun] using
    memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
      (m := m) hGH

/-- Scalar reflected-difference energy on the centered parent cube is `3^d`
copies of the original difference energy. -/
theorem setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sub_sq_of_memScalarL2_three_pow
    {F U : Vec d → ℝ}
    (hFU : MemScalarL2 (openCubeSet (originCube d m)) (fun x => F x - U x)) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        (cubeCoordinateFoldReflectedScalar (originCube d m) F x -
          cubeCoordinateFoldReflectedScalar (originCube d m) U x) *
          (cubeCoordinateFoldReflectedScalar (originCube d m) F x -
            cubeCoordinateFoldReflectedScalar (originCube d m) U x)
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet (originCube d m),
          (F y - U y) * (F y - U y) ∂MeasureTheory.volume := by
  simpa using
    setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sq_of_memScalarL2_three_pow
      (m := m) (F := fun y => F y - U y) hFU

/-- Vector reflected-difference energy on the centered parent cube is `3^d`
copies of the original difference energy. -/
theorem setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_sub_self_pairing_of_memVectorL2_three_pow
    {G H : Vec d → Vec d}
    (hGH : MemVectorL2 (openCubeSet (originCube d m)) (fun x => G x - H x)) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x -
            cubeCoordinateFoldReflectedVectorField (originCube d m) H x)
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x -
            cubeCoordinateFoldReflectedVectorField (originCube d m) H x)
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet (originCube d m),
          vecDot (G y - H y) (G y - H y) ∂MeasureTheory.volume := by
  have hfun :
      cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun x => G x - H x) =
        fun x =>
          cubeCoordinateFoldReflectedVectorField (originCube d m) G x -
            cubeCoordinateFoldReflectedVectorField (originCube d m) H x := by
    funext x
    exact cubeCoordinateFoldReflectedVectorField_sub_apply
      (originCube d m) G H x
  simpa [hfun] using
    setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2_three_pow
      (m := m) (G := fun y => G y - H y) hGH

/-- Scalar `L²` convergence on the original cube transfers to the all-face
reflected scalar differences on the centered parent cube. -/
theorem tendsto_eLpNorm_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sub
    {F : ℕ → Vec d → ℝ} {U : Vec d → ℝ}
    (hFU : ∀ n,
      MemScalarL2 (openCubeSet (originCube d m)) (fun x => F n x - U x))
    (hlim :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => F n x - U x) 2
            (volumeMeasureOn (openCubeSet (originCube d m))))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x =>
            cubeCoordinateFoldReflectedScalar (originCube d m) (F n) x -
              cubeCoordinateFoldReflectedScalar (originCube d m) U x)
          2 (volumeMeasureOn (openCubeSet (originCube d (m + 1)))))
      Filter.atTop (nhds 0) := by
  let C : ℝ := (3 : ℝ) ^ d + 1
  let parentDiff : ℕ → Vec d → ℝ := fun n x =>
    cubeCoordinateFoldReflectedScalar (originCube d m) (F n) x -
      cubeCoordinateFoldReflectedScalar (originCube d m) U x
  have hparent_mem : ∀ n,
      MemScalarL2 (openCubeSet (originCube d (m + 1))) (parentDiff n) := by
    intro n
    simpa [parentDiff] using
      memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sub
        (m := m) (F := F n) (U := U) (hFU n)
  have horig_real :
      Filter.Tendsto
        (fun n =>
          ENNReal.toReal
            (MeasureTheory.eLpNorm (fun x => F n x - U x) 2
              (volumeMeasureOn (openCubeSet (originCube d m)))))
        Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => (hFU n).eLpNorm_ne_top)).2 hlim
  have hscaled_real :
      Filter.Tendsto
        (fun n =>
          C *
            ENNReal.toReal
              (MeasureTheory.eLpNorm (fun x => F n x - U x) 2
                (volumeMeasureOn (openCubeSet (originCube d m)))))
        Filter.atTop (nhds 0) := by
    simpa using horig_real.const_mul C
  have hparent_real :
      Filter.Tendsto
        (fun n =>
          ENNReal.toReal
            (MeasureTheory.eLpNorm (parentDiff n) 2
              (volumeMeasureOn (openCubeSet (originCube d (m + 1))))))
        Filter.atTop (nhds 0) := by
    refine squeeze_zero
      (fun n => ENNReal.toReal_nonneg)
      (fun n => ?_)
      hscaled_real
    let a : ℝ :=
      ENNReal.toReal
        (MeasureTheory.eLpNorm (parentDiff n) 2
          (volumeMeasureOn (openCubeSet (originCube d (m + 1)))))
    let b : ℝ :=
      ENNReal.toReal
        (MeasureTheory.eLpNorm (fun x => F n x - U x) 2
          (volumeMeasureOn (openCubeSet (originCube d m))))
    have hsq_eq :
        a ^ 2 = (3 : ℝ) ^ d * b ^ 2 := by
      have henergy :=
        setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sub_sq_of_memScalarL2_three_pow
          (m := m) (F := F n) (U := U) (hFU n)
      rw [toReal_eLpNorm_two_sq_eq_integral_sq (hparent_mem n),
        toReal_eLpNorm_two_sq_eq_integral_sq (hFU n)]
      simpa [a, b, parentDiff, pow_two] using henergy
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    have hthree_nonneg : 0 ≤ (3 : ℝ) ^ d := by
      positivity
    have hthree_le_C_sq : (3 : ℝ) ^ d ≤ C ^ 2 := by
      dsimp [C]
      nlinarith [sq_nonneg ((3 : ℝ) ^ d), sq_nonneg ((3 : ℝ) ^ d + 1)]
    have hsq_le : a ^ 2 ≤ (C * b) ^ 2 := by
      calc
        a ^ 2 = (3 : ℝ) ^ d * b ^ 2 := hsq_eq
        _ ≤ C ^ 2 * b ^ 2 := by
            exact mul_le_mul_of_nonneg_right hthree_le_C_sq (sq_nonneg b)
        _ = (C * b) ^ 2 := by ring
    have hCb_nonneg : 0 ≤ C * b := by
      exact mul_nonneg hC_nonneg ENNReal.toReal_nonneg
    exact (sq_le_sq₀ ENNReal.toReal_nonneg hCb_nonneg).1 hsq_le
  exact
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => (hparent_mem n).eLpNorm_ne_top)).1 hparent_real

/-- A coordinate of a reflected vector-field difference has the same `3^d`
energy transfer as a reflected scalar difference. -/
theorem setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_sub_coord_sq_of_memScalarL2_three_pow
    {G H : Vec d → Vec d} (j : Fin d)
    (hGHj :
      MemScalarL2 (openCubeSet (originCube d m)) (fun x => G x j - H x j)) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        ((cubeCoordinateFoldReflectedVectorField (originCube d m) G x -
          cubeCoordinateFoldReflectedVectorField (originCube d m) H x) j) *
          ((cubeCoordinateFoldReflectedVectorField (originCube d m) G x -
            cubeCoordinateFoldReflectedVectorField (originCube d m) H x) j)
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet (originCube d m),
          (G y j - H y j) * (G y j - H y j) ∂MeasureTheory.volume := by
  have hscalar :=
    setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sub_sq_of_memScalarL2_three_pow
      (m := m) (F := fun y => G y j) (U := fun y => H y j) hGHj
  calc
    ∫ x in openCubeSet (originCube d (m + 1)),
        ((cubeCoordinateFoldReflectedVectorField (originCube d m) G x -
          cubeCoordinateFoldReflectedVectorField (originCube d m) H x) j) *
          ((cubeCoordinateFoldReflectedVectorField (originCube d m) G x -
            cubeCoordinateFoldReflectedVectorField (originCube d m) H x) j)
        ∂MeasureTheory.volume =
      ∫ x in openCubeSet (originCube d (m + 1)),
        (cubeCoordinateFoldReflectedScalar (originCube d m) (fun y => G y j) x -
          cubeCoordinateFoldReflectedScalar (originCube d m) (fun y => H y j) x) *
          (cubeCoordinateFoldReflectedScalar (originCube d m) (fun y => G y j) x -
            cubeCoordinateFoldReflectedScalar (originCube d m) (fun y => H y j) x)
        ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (originCube d (m + 1))) ?_
          intro x _hx
          let s : ℝ := cubeCoordinateFoldSign (originCube d m) x j
          let A : ℝ := G (cubeCoordinateFold (originCube d m) x) j
          let B : ℝ := H (cubeCoordinateFold (originCube d m) x) j
          have hs : s * s = 1 := by
            simp [s]
          change (s * A - s * B) * (s * A - s * B) = (A - B) * (A - B)
          nlinarith [hs]
    _ = (3 : ℝ) ^ d *
        ∫ y in openCubeSet (originCube d m),
          (G y j - H y j) * (G y j - H y j) ∂MeasureTheory.volume := hscalar

/-- Coordinatewise `L²` convergence on the original cube transfers to
coordinates of the all-face reflected vector-field differences on the centered
parent cube. -/
theorem tendsto_eLpNorm_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_sub_coord
    {G : ℕ → Vec d → Vec d} {H : Vec d → Vec d} (j : Fin d)
    (hGH : ∀ n,
      MemVectorL2 (openCubeSet (originCube d m)) (fun x => G n x - H x))
    (hlim :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => G n x j - H x j) 2
            (volumeMeasureOn (openCubeSet (originCube d m))))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x =>
            (cubeCoordinateFoldReflectedVectorField (originCube d m) (G n) x -
              cubeCoordinateFoldReflectedVectorField (originCube d m) H x) j)
          2 (volumeMeasureOn (openCubeSet (originCube d (m + 1)))))
      Filter.atTop (nhds 0) := by
  let C : ℝ := (3 : ℝ) ^ d + 1
  let parentDiff : ℕ → Vec d → ℝ := fun n x =>
    (cubeCoordinateFoldReflectedVectorField (originCube d m) (G n) x -
      cubeCoordinateFoldReflectedVectorField (originCube d m) H x) j
  have hparent_mem : ∀ n,
      MemScalarL2 (openCubeSet (originCube d (m + 1))) (parentDiff n) := by
    intro n
    have hparent_vec :
        MemVectorL2 (openCubeSet (originCube d (m + 1)))
          (fun x =>
            cubeCoordinateFoldReflectedVectorField (originCube d m) (G n) x -
              cubeCoordinateFoldReflectedVectorField (originCube d m) H x) :=
      memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_sub
        (m := m) (G := G n) (H := H) (hGH n)
    simpa [parentDiff] using memScalarL2_coord_of_memVectorL2 hparent_vec j
  have hGHj : ∀ n,
      MemScalarL2 (openCubeSet (originCube d m)) (fun x => G n x j - H x j) := by
    intro n
    simpa using memScalarL2_coord_of_memVectorL2 (hGH n) j
  have horig_real :
      Filter.Tendsto
        (fun n =>
          ENNReal.toReal
            (MeasureTheory.eLpNorm (fun x => G n x j - H x j) 2
              (volumeMeasureOn (openCubeSet (originCube d m)))))
        Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => (hGHj n).eLpNorm_ne_top)).2 hlim
  have hscaled_real :
      Filter.Tendsto
        (fun n =>
          C *
            ENNReal.toReal
              (MeasureTheory.eLpNorm (fun x => G n x j - H x j) 2
                (volumeMeasureOn (openCubeSet (originCube d m)))))
        Filter.atTop (nhds 0) := by
    simpa using horig_real.const_mul C
  have hparent_real :
      Filter.Tendsto
        (fun n =>
          ENNReal.toReal
            (MeasureTheory.eLpNorm (parentDiff n) 2
              (volumeMeasureOn (openCubeSet (originCube d (m + 1))))))
        Filter.atTop (nhds 0) := by
    refine squeeze_zero
      (fun n => ENNReal.toReal_nonneg)
      (fun n => ?_)
      hscaled_real
    let a : ℝ :=
      ENNReal.toReal
        (MeasureTheory.eLpNorm (parentDiff n) 2
          (volumeMeasureOn (openCubeSet (originCube d (m + 1)))))
    let b : ℝ :=
      ENNReal.toReal
        (MeasureTheory.eLpNorm (fun x => G n x j - H x j) 2
          (volumeMeasureOn (openCubeSet (originCube d m))))
    have hsq_eq :
        a ^ 2 = (3 : ℝ) ^ d * b ^ 2 := by
      have henergy :=
        setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_sub_coord_sq_of_memScalarL2_three_pow
          (m := m) (G := G n) (H := H) j (hGHj n)
      rw [toReal_eLpNorm_two_sq_eq_integral_sq (hparent_mem n),
        toReal_eLpNorm_two_sq_eq_integral_sq (hGHj n)]
      simpa [a, b, parentDiff, pow_two] using henergy
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    have hthree_le_C_sq : (3 : ℝ) ^ d ≤ C ^ 2 := by
      dsimp [C]
      nlinarith [sq_nonneg ((3 : ℝ) ^ d), sq_nonneg ((3 : ℝ) ^ d + 1)]
    have hsq_le : a ^ 2 ≤ (C * b) ^ 2 := by
      calc
        a ^ 2 = (3 : ℝ) ^ d * b ^ 2 := hsq_eq
        _ ≤ C ^ 2 * b ^ 2 := by
            exact mul_le_mul_of_nonneg_right hthree_le_C_sq (sq_nonneg b)
        _ = (C * b) ^ 2 := by ring
    have hCb_nonneg : 0 ≤ C * b := by
      exact mul_nonneg hC_nonneg ENNReal.toReal_nonneg
    exact (sq_le_sq₀ ENNReal.toReal_nonneg hCb_nonneg).1 hsq_le
  exact
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => (hparent_mem n).eLpNorm_ne_top)).1 hparent_real

/-- Scalar `L²` convergence transfer, stated directly in the `ScalarL2`
classes on the centered parent cube. -/
theorem tendsto_toScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
    {F : ℕ → Vec d → ℝ} {U : Vec d → ℝ}
    (hF : ∀ n, MemScalarL2 (openCubeSet (originCube d m)) (F n))
    (hU : MemScalarL2 (openCubeSet (originCube d m)) U)
    (hlim :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => F n x - U x) 2
            (volumeMeasureOn (openCubeSet (originCube d m))))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n =>
        toScalarL2
          (memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
            (m := m) (hF n)))
      Filter.atTop
      (nhds
        (toScalarL2
          (memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
            (m := m) hU))) := by
  let parentF : ℕ → Vec d → ℝ := fun n =>
    cubeCoordinateFoldReflectedScalar (originCube d m) (F n)
  let parentU : Vec d → ℝ :=
    cubeCoordinateFoldReflectedScalar (originCube d m) U
  have hparentF : ∀ n,
      MemScalarL2 (openCubeSet (originCube d (m + 1))) (parentF n) := by
    intro n
    simpa [parentF] using
      memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
        (m := m) (hF n)
  have hparentU :
      MemScalarL2 (openCubeSet (originCube d (m + 1))) parentU := by
    simpa [parentU] using
      memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
        (m := m) hU
  have hdiff : ∀ n,
      MemScalarL2 (openCubeSet (originCube d m)) (fun x => F n x - U x) :=
    fun n => (hF n).sub hU
  have hlim_parent :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => parentF n x - parentU x) 2
            (volumeMeasureOn (openCubeSet (originCube d (m + 1)))))
        Filter.atTop (nhds 0) := by
    simpa [parentF, parentU] using
      tendsto_eLpNorm_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sub
        (m := m) (F := F) (U := U) hdiff hlim
  simpa [parentF, parentU] using
    tendsto_toScalarL2_of_tendsto_eLpNorm
      (U := openCubeSet (originCube d (m + 1)))
      (F := parentF) (G := parentU) hparentF hparentU hlim_parent

/-- Coordinatewise reflected-gradient convergence transfer, stated directly in
the `ScalarL2` classes on the centered parent cube. -/
theorem tendsto_toScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_coord
    {G : ℕ → Vec d → Vec d} {H : Vec d → Vec d} (j : Fin d)
    (hG : ∀ n, MemVectorL2 (openCubeSet (originCube d m)) (G n))
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hlim :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => G n x j - H x j) 2
            (volumeMeasureOn (openCubeSet (originCube d m))))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n =>
        toScalarL2
          (memScalarL2_coord_of_memVectorL2
            (memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
              (m := m) (hG n)) j))
      Filter.atTop
      (nhds
        (toScalarL2
          (memScalarL2_coord_of_memVectorL2
            (memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
              (m := m) hH) j))) := by
  let parentG : ℕ → Vec d → ℝ := fun n x =>
    cubeCoordinateFoldReflectedVectorField (originCube d m) (G n) x j
  let parentH : Vec d → ℝ := fun x =>
    cubeCoordinateFoldReflectedVectorField (originCube d m) H x j
  have hparentG : ∀ n,
      MemScalarL2 (openCubeSet (originCube d (m + 1))) (parentG n) := by
    intro n
    simpa [parentG] using
      memScalarL2_coord_of_memVectorL2
        (memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
          (m := m) (hG n)) j
  have hparentH :
      MemScalarL2 (openCubeSet (originCube d (m + 1))) parentH := by
    simpa [parentH] using
      memScalarL2_coord_of_memVectorL2
        (memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
          (m := m) hH) j
  have hdiff : ∀ n,
      MemVectorL2 (openCubeSet (originCube d m)) (fun x => G n x - H x) :=
    fun n => (hG n).sub hH
  have hlim_parent :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => parentG n x - parentH x) 2
            (volumeMeasureOn (openCubeSet (originCube d (m + 1)))))
        Filter.atTop (nhds 0) := by
    simpa [parentG, parentH, Pi.sub_apply] using
      tendsto_eLpNorm_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_sub_coord
        (m := m) (G := G) (H := H) j hdiff hlim
  simpa [parentG, parentH] using
    tendsto_toScalarL2_of_tendsto_eLpNorm
      (U := openCubeSet (originCube d (m + 1)))
      (F := parentG) (G := parentH) hparentG hparentH hlim_parent

end

end Homogenization
