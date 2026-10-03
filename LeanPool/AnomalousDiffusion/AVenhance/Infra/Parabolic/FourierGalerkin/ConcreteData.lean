/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.FrozenInitialData
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.FrozenMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ScalarSpace

/-!
# Positive real Fourier Galerkin data for the drift

This module instantiates the abstract finite weak-form ODE by the positive symmetric real Fourier
cutoff. The coefficient datum is the quotient-torus representative of the initial datum.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization
open scoped ENNReal RealInnerProductSpace

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance concreteDataMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance concreteDataMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance concreteDataProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The `PiLp 2` norm is the Euclidean norm used by the gradient energy. -/
theorem spatialVector_norm_eq_euclideanVecNorm (v : Vec 2) :
    ‖(WithLp.toLp 2 v : SpatialVector)‖ = euclideanVecNorm v := by
  rw [PiLp.norm_eq_of_L2]
  congr 1
  simp [Homogenization.vecNormSq, Homogenization.vecDot, Fin.sum_univ_succ]
  ring

/-- The local Galerkin matrix dot product is the Euclidean vector pairing. -/
theorem fourierGalerkin_vecDot_eq_frozen (u v : Vec 2) :
    vecDot u v = Homogenization.vecDot u v := by
  simp [vecDot, Homogenization.vecDot]

/-- The gradient norm of one positive-cutoff mode belongs to scalar `L²`. -/
theorem realFourierModeGradFin_norm_memLp (N : ℕ)
    (i : Fin (RealFourierDimension N)) :
    MemLp (fun x : Torus => euclideanVecNorm (realFourierModeGradFin N i x)) 2 volume := by
  have h := (realFourierModeGradFin_memLp N i).norm
  convert h using 1
  funext x
  exact (spatialVector_norm_eq_euclideanVecNorm _).symm

/-- The pointwise finite gradient sum is the representative of the `L²` gradient map. -/
theorem realFourierGradientMap_coeFn (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    (fun x : Torus => ((realFourierGradientMap N c) x : SpatialVector)) =ᵐ[volume]
      fun x => WithLp.toLp 2
        (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradFin N i x) := by
  rw [realFourierGradientMap_apply]
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin (RealFourierDimension N) => c i • realFourierModeGradL2 N i)
  have hterm : ∀ᵐ x ∂volume, ∀ i : Fin (RealFourierDimension N),
      (c i • realFourierModeGradL2 N i) x =
        WithLp.toLp 2 (c i • realFourierModeGradFin N i x) := by
    apply ae_all_iff.2
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (realFourierModeGradL2 N i),
      (realFourierModeGradFin_memLp N i).coeFn_toLp] with x hs hm
    calc
      (c i • realFourierModeGradL2 N i) x = c i • (realFourierModeGradL2 N i) x := hs
      _ = c i • WithLp.toLp 2 (realFourierModeGradFin N i x) := congrArg (fun v => c i • v) hm
      _ = WithLp.toLp 2 (c i • realFourierModeGradFin N i x) := by simp
  filter_upwards [hsum, hterm] with x hsum hterm
  simp only [Finset.sum_apply] at hsum
  calc
    (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradL2 N i) x =
        ∑ i : Fin (RealFourierDimension N), (c i • realFourierModeGradL2 N i) x := hsum
    _ =
        ∑ i : Fin (RealFourierDimension N),
          WithLp.toLp 2 (c i • realFourierModeGradFin N i x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i
    _ = WithLp.toLp 2
        (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradFin N i x) := by
      rw [← WithLp.toLp_sum]

/-- The pointwise finite scalar sum is the representative of the scalar synthesis map. -/
theorem realFourierScalarMap_coeFn (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    (fun x : Torus => (realFourierScalarMap N c) x) =ᵐ[volume]
      fun x => modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x := by
  rw [realFourierScalarMap_apply]
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin (RealFourierDimension N) => c i • realFourierModeL2 N i)
  have hterm : ∀ᵐ x ∂volume, ∀ i : Fin (RealFourierDimension N),
      (c i • realFourierModeL2 N i) x = c i * realFourierModeFin N i x := by
    apply ae_all_iff.2
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (realFourierModeL2 N i),
      (realFourierModeFin_memLp N i).coeFn_toLp] with x hs hm
    calc
      (c i • realFourierModeL2 N i) x = c i * (realFourierModeL2 N i) x := hs
      _ = c i * realFourierModeFin N i x := congrArg (fun v => c i * v) hm
  filter_upwards [hsum, hterm] with x hsum hterm
  simp only [Finset.sum_apply] at hsum
  calc
    (∑ i : Fin (RealFourierDimension N), c i • realFourierModeL2 N i) x =
        ∑ i : Fin (RealFourierDimension N), (c i • realFourierModeL2 N i) x := hsum
    _ =
        ∑ i : Fin (RealFourierDimension N), c i * realFourierModeFin N i x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i
    _ = modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x := rfl

/-- The scalar `L²` norm squared is the integral of the pointwise squared norm. -/
theorem l2_norm_sq_eq_integral_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : Lp E 2 (volume : Measure Torus)) :
    ‖f‖ ^ 2 = ∫ x : Torus, ‖f x‖ ^ 2 := by
  have hinner := real_inner_self_eq_norm_sq f
  rw [MeasureTheory.L2.inner_def] at hinner
  calc
    ‖f‖ ^ 2 = inner ℝ f f := hinner.symm
    _ = ∫ x : Torus, inner ℝ (f x) (f x) := MeasureTheory.L2.inner_def f f
    _ = ∫ x : Torus, ‖f x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      exact real_inner_self_eq_norm_sq (f x)

/-- The diffusion energy of a finite real Fourier gradient sum is its weak-form pairing. -/
theorem realFourierGradientMap_inner_formula (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    inner ℝ (realFourierGradientMap N c) (realFourierGradientMap N c) =
      ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
        c i * c j * inner ℝ (realFourierModeGradL2 N i) (realFourierModeGradL2 N j) := by
  rw [realFourierGradientMap_apply, sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right]
  simp [mul_assoc]

/-- The `L²` pairing of two real Fourier gradient modes is the diffusion matrix entry. -/
theorem realFourierModeGradL2_inner (N : ℕ)
    (i j : Fin (RealFourierDimension N)) :
    inner ℝ (realFourierModeGradL2 N i) (realFourierModeGradL2 N j) =
      ∫ x : Torus, vecDot (realFourierModeGradFin N i x) (realFourierModeGradFin N j x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(realFourierModeGradFin_memLp N i).coeFn_toLp,
    (realFourierModeGradFin_memLp N j).coeFn_toLp] with x hi hj
  have hi' : (realFourierModeGradL2 N i) x =
      WithLp.toLp 2 (realFourierModeGradFin N i x) := hi
  have hj' : (realFourierModeGradL2 N j) x =
      WithLp.toLp 2 (realFourierModeGradFin N j x) := hj
  rw [hi', hj']
  rw [PiLp.inner_apply]
  simp [vecDot, Fin.sum_univ_succ]
  ring

/-- Quadratic pairing of a finite coefficient matrix in the Euclidean coefficient inner product. -/
theorem matrixCoefficientCLM_inner_quadratic {n : ℕ}
    (A : Fin n → Fin n → ℝ) (c : Coefficients n) :
    inner ℝ c (matrixCoefficientCLM A c) =
      ∑ i : Fin n, ∑ j : Fin n, c i * c j * A i j := by
  simp [PiLp.inner_apply, matrixCoefficientCLM_apply, Finset.mul_sum,
    mul_comm, mul_left_comm]

/-- The finite gradient energy equals the quadratic form of the weak diffusion matrix. -/
theorem realFourierGradientMap_diffusionMatrix (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    ‖realFourierGradientMap N c‖ ^ 2 =
      ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
        c i * c j *
          ∫ x : Torus,
            vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x) := by
  rw [← real_inner_self_eq_norm_sq, realFourierGradientMap_inner_formula]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [realFourierModeGradL2_inner]
  have hsymm :
      (∫ x : Torus,
        vecDot (realFourierModeGradFin N i x) (realFourierModeGradFin N j x)) =
      ∫ x : Torus,
        vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x) := by
    apply integral_congr_ae
    filter_upwards with x
    simp [vecDot]
    ring
  rw [hsymm]

/-- The quadratic weak-form matrix splits into the direct drift form and the gradient energy. -/
theorem realFourierWeakMatrix_quadratic (N : ℕ)
    (b : ℝ → Torus → Vec 2) (κ t : ℝ)
    (c : Coefficients (RealFourierDimension N)) :
    (∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
      c i * c j * weakFormMatrixEntry b κ (realFourierModeFin N)
        (realFourierModeGradFin N) t i j) =
      -(∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
        c i * c j * ∫ x : Torus,
          vecDot (b t x) (realFourierModeGradFin N j x) * realFourierModeFin N i x) -
        κ * ‖realFourierGradientMap N c‖ ^ 2 := by
  calc
    _ = ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
        (-(c i * c j * ∫ x : Torus,
            vecDot (b t x) (realFourierModeGradFin N j x) * realFourierModeFin N i x) -
          κ * (c i * c j * ∫ x : Torus,
            vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [weakFormMatrixEntry]
      ring
    _ = -(∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
          c i * c j * ∫ x : Torus,
            vecDot (b t x) (realFourierModeGradFin N j x) * realFourierModeFin N i x) -
        κ * (∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
          c i * c j * ∫ x : Torus,
            vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      simp_rw [← Finset.mul_sum]
    _ = _ := by rw [realFourierGradientMap_diffusionMatrix]

/-- The `L²` norm of a finite real Fourier gradient sum is its integral gradient energy. -/
theorem realFourierGradientMap_norm_sq (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    ‖realFourierGradientMap N c‖ ^ 2 =
      ∫ x : Torus,
        euclideanVecNorm (∑ i : Fin (RealFourierDimension N),
          c i • realFourierModeGradFin N i x) ^ 2 := by
  have hnorm := l2_norm_sq_eq_integral_sq (realFourierGradientMap N c)
  calc
    ‖realFourierGradientMap N c‖ ^ 2 =
        ∫ x : Torus, ‖(realFourierGradientMap N c) x‖ ^ 2 := hnorm
    _ = ∫ x : Torus,
        euclideanVecNorm (∑ i : Fin (RealFourierDimension N),
          c i • realFourierModeGradFin N i x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [realFourierGradientMap_coeFn N c] with x hx
      rw [hx]
      exact congrArg (fun z : ℝ => z ^ 2)
        (spatialVector_norm_eq_euclideanVecNorm _)

/-- The finite pointwise real Fourier gradient sum belongs to scalar `L²` after taking its
Euclidean norm. -/
theorem realFourierGradientExpansion_norm_memLp (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    MemLp (fun x : Torus => euclideanVecNorm
      (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradFin N i x)) 2 volume := by
  have hLp := (Lp.memLp (realFourierGradientMap N c)).norm
  have hEq : (fun x : Torus => euclideanVecNorm
      (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradFin N i x)) =ᵐ[volume]
      fun x => ‖(realFourierGradientMap N c) x‖ := by
    filter_upwards [realFourierGradientMap_coeFn N c] with x hx
    rw [hx]
    exact (spatialVector_norm_eq_euclideanVecNorm _).symm
  exact MemLp.ae_eq hEq.symm hLp

/-- The finite pointwise real Fourier scalar sum belongs to scalar `L²`. -/
theorem realFourierScalarExpansion_memLp (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    MemLp (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c) 2 volume := by
  have hLp : MemLp (fun x : Torus => (realFourierScalarMap N c) x) 2 volume :=
    Lp.memLp (realFourierScalarMap N c)
  have hEq := realFourierScalarMap_coeFn N c
  exact (memLp_congr_ae hEq).1 hLp

/-- The gradient factor of the finite Fourier sum is its vector `L²` norm. -/
theorem realFourierGradientExpansion_l2Factor (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    (∫ x : Torus, euclideanVecNorm
      (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradFin N i x) ^
        (2 : ℝ)) ^ ((1 : ℝ) / 2) = ‖realFourierGradientMap N c‖ := by
  have hint : (∫ x : Torus, euclideanVecNorm
      (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradFin N i x) ^
        (2 : ℝ)) = ‖realFourierGradientMap N c‖ ^ 2 := by
    calc
      _ = ∫ x : Torus, euclideanVecNorm
          (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradFin N i x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.rpow_two]
      _ = ‖realFourierGradientMap N c‖ ^ 2 :=
        (realFourierGradientMap_norm_sq N c).symm
  rw [hint, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The scalar factor of the finite Fourier sum is the coefficient norm. -/
theorem realFourierScalarExpansion_l2Factor (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    (∫ x : Torus,
      ‖modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x‖ ^ (2 : ℝ)) ^
        ((1 : ℝ) / 2) = ‖c‖ := by
  have hint : (∫ x : Torus,
      ‖modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x‖ ^ (2 : ℝ)) =
      ‖realFourierScalarMap N c‖ ^ 2 := by
    have hnorm := l2_norm_sq_eq_integral_sq (realFourierScalarMap N c)
    have hcoeeq := realFourierScalarMap_coeFn N c
    calc
      _ = ∫ x : Torus, ‖(realFourierScalarMap N c) x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hcoeeq] with x hx
        rw [hx, Real.rpow_two]
      _ = ‖realFourierScalarMap N c‖ ^ 2 := hnorm.symm
  rw [hint, realFourierScalarMap_norm, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

/-- The square-integral factor of a normalized scalar Fourier mode. -/
def realFourierModeFinL2Factor (N : ℕ) (i : Fin (RealFourierDimension N)) : ℝ :=
  (∫ x : Torus, ‖realFourierModeFin N i x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)

/-- The square-integral factor of a real Fourier gradient mode. -/
def realFourierModeGradFinL2Factor (N : ℕ)
    (i : Fin (RealFourierDimension N)) : ℝ :=
  (∫ x : Torus, euclideanVecNorm (realFourierModeGradFin N i x) ^ (2 : ℝ)) ^
    ((1 : ℝ) / 2)

/-- Every real mode has scalar `L²` factor one. -/
theorem realFourierModeFin_l2Factor_eq_one (N : ℕ)
    (i : Fin (RealFourierDimension N)) : realFourierModeFinL2Factor N i = 1 := by
  have hpoint : (fun x : Torus => ‖realFourierModeFin N i x‖ ^ (2 : ℝ)) =
      fun x => realFourierModeFin N i x * realFourierModeFin N i x := by
    funext x
    rw [Real.rpow_two]
    simp [Real.norm_eq_abs]
    ring
  have hint : (∫ x : Torus,
      ‖realFourierModeFin N i x‖ ^ (2 : ℝ)) = 1 := by
    rw [show (fun x : Torus => ‖realFourierModeFin N i x‖ ^ (2 : ℝ)) =
      fun x => realFourierModeFin N i x * realFourierModeFin N i x from hpoint]
    simpa using realFourierModeFin_orthonormal N i i
  rw [realFourierModeFinL2Factor, hint]
  norm_num

/-- The finite cutoff has an explicit bound for all individual gradient-mode factors. -/
def realFourierCutoffGradientBound (N : ℕ) : ℝ :=
  ∑ i : Fin (RealFourierDimension N), realFourierModeGradFinL2Factor N i

theorem realFourierModeGradFin_l2Factor_nonneg (N : ℕ)
    (i : Fin (RealFourierDimension N)) : 0 ≤ realFourierModeGradFinL2Factor N i := by
  apply Real.rpow_nonneg
  apply integral_nonneg_of_ae
  filter_upwards with x
  exact Real.rpow_nonneg (euclideanVecNorm_nonneg _) _

theorem realFourierCutoffGradientBound_nonneg (N : ℕ) :
    0 ≤ realFourierCutoffGradientBound N := by
  exact Finset.sum_nonneg fun i hi => realFourierModeGradFin_l2Factor_nonneg N i

theorem realFourierModeGradFin_l2Factor_le_cutoff (N : ℕ)
    (i : Fin (RealFourierDimension N)) :
    realFourierModeGradFinL2Factor N i ≤ realFourierCutoffGradientBound N := by
  exact Finset.single_le_sum
    (fun j hj => realFourierModeGradFin_l2Factor_nonneg N j) (Finset.mem_univ i)

/-- Cauchy--Schwarz for the two-vector dot product in its Euclidean norm. -/
theorem vecDot_abs_le_euclidean (u v : Vec 2) :
    |Homogenization.vecDot u v| ≤ euclideanVecNorm u * euclideanVecNorm v := by
  have hu : 0 ≤ euclideanVecNorm u := euclideanVecNorm_nonneg u
  have hv : 0 ≤ euclideanVecNorm v := euclideanVecNorm_nonneg v
  have hcs := Homogenization.sq_vecDot_le_vecNormSq_mul_vecNormSq u v
  have hsq : |Homogenization.vecDot u v| ^ 2 ≤
      (euclideanVecNorm u * euclideanVecNorm v) ^ 2 := by
    rw [sq_abs, mul_pow, euclideanVecNorm_sq, euclideanVecNorm_sq]
    exact hcs
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hu hv)).mp hsq

/-- The diffusion pairing is bounded by the product of the two gradient-mode factors. -/
theorem realFourierModeGradFin_diffusion_abs_bound_by_factors (N : ℕ)
    (i j : Fin (RealFourierDimension N)) :
    |∫ x : Torus,
      vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x)| ≤
        realFourierModeGradFinL2Factor N j * realFourierModeGradFinL2Factor N i := by
  have hpoint : ∀ᵐ x ∂(volume : Measure Torus),
      |vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x)| ≤
        1 * (|euclideanVecNorm (realFourierModeGradFin N j x)| *
          |euclideanVecNorm (realFourierModeGradFin N i x)|) := by
    filter_upwards with x
    have h := vecDot_abs_le_euclidean
      (realFourierModeGradFin N j x) (realFourierModeGradFin N i x)
    change |Homogenization.vecDot (realFourierModeGradFin N j x)
        (realFourierModeGradFin N i x)| ≤ _
    simpa [abs_of_nonneg (euclideanVecNorm_nonneg _), abs_of_nonneg
      (euclideanVecNorm_nonneg _)] using h
  have h := driftIntegral_bound_of_L2_or_not
    (fun x : Torus => vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x))
    (fun x => euclideanVecNorm (realFourierModeGradFin N j x))
    (fun x => euclideanVecNorm (realFourierModeGradFin N i x)) 1 (by norm_num) hpoint
    (realFourierModeGradFin_norm_memLp N j) (realFourierModeGradFin_norm_memLp N i)
  simpa [realFourierModeGradFinL2Factor, Real.norm_eq_abs,
    abs_of_nonneg (euclideanVecNorm_nonneg _)] using h

/-- The diffusion pairing of any two cutoff modes is bounded by the square of the cutoff gradient
bound. -/
theorem realFourierModeGradFin_diffusion_abs_bound (N : ℕ)
    (i j : Fin (RealFourierDimension N)) :
    |∫ x : Torus,
      vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x)| ≤
        realFourierCutoffGradientBound N ^ 2 := by
  have hji := realFourierModeGradFin_l2Factor_le_cutoff N j
  have hii := realFourierModeGradFin_l2Factor_le_cutoff N i
  have hii_nonneg := realFourierModeGradFin_l2Factor_nonneg N i
  have hG := realFourierCutoffGradientBound_nonneg N
  calc
    |∫ x : Torus,
      vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x)| ≤
        realFourierModeGradFinL2Factor N j * realFourierModeGradFinL2Factor N i :=
          realFourierModeGradFin_diffusion_abs_bound_by_factors N i j
    _ ≤ realFourierCutoffGradientBound N ^ 2 := by
      calc
        realFourierModeGradFinL2Factor N j * realFourierModeGradFinL2Factor N i ≤
            realFourierCutoffGradientBound N * realFourierModeGradFinL2Factor N i :=
          mul_le_mul_of_nonneg_right hji hii_nonneg
        _ ≤ realFourierCutoffGradientBound N * realFourierCutoffGradientBound N :=
          mul_le_mul_of_nonneg_left hii hG
        _ = realFourierCutoffGradientBound N ^ 2 := by ring

/-- The product-measurable drift has a.e. strongly measurable torus slices. -/
theorem frozenDrift_torus_slice_aestronglyMeasurable
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      AEStronglyMeasurable
        (AVenhance.Infra.Torus.periodicToTorus (b t)) (volume : Measure Torus) := by
  let μt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let μx : Measure (Vec 2) := volume.restrict AVenhance.unitCube
  have hbCell := frozenDrift_aestronglyMeasurable_cell b hb_meas
  have hbProd : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2) (μt.prod μx) := by
    change AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube))
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (Vec 2)]
    exact hbCell
  have hslice := hbProd.prodMk_left
  filter_upwards [hslice] with t ht
  let cell : Set (Vec 2) := AVenhance.Infra.Torus.unitCell 2
  have hcellLe : (volume : Measure (Vec 2)).restrict cell ≤
      (volume : Measure (Vec 2)).restrict AVenhance.unitCube := by
    exact Measure.restrict_mono_ae AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.le
  have htCell : AEStronglyMeasurable (fun x : Vec 2 => b t x)
      ((volume : Measure (Vec 2)).restrict cell) := ht.mono_measure hcellLe
  let cellSubtype := {x : Vec 2 // x ∈ cell}
  let cellMeasure : Measure cellSubtype :=
    volume.comap (Subtype.val : cellSubtype → Vec 2)
  have hmeasureCell : MeasurePreserving (fun x : cellSubtype => (x : Vec 2))
      cellMeasure ((volume : Measure (Vec 2)).restrict cell) := by
    change MeasurePreserving Subtype.val
      ((volume : Measure (Vec 2)).comap (Subtype.val : cellSubtype → Vec 2))
      ((volume : Measure (Vec 2)).restrict cell)
    exact ⟨measurable_subtype_coe,
      map_comap_subtype_coe (AVenhance.Infra.Torus.measurableSet_unitCell 2) volume⟩
  let equiv := UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))
  have hmeasureTorus : MeasurePreserving equiv (volume : Measure Torus) cellMeasure := by
    change MeasurePreserving equiv (volume : Measure Torus)
      ((volume : Measure (Vec 2)).comap (Subtype.val : cellSubtype → Vec 2))
    simpa [equiv, cell, AVenhance.Infra.Torus.unitCell,
      AVenhance.Infra.Torus.unitCellAt] using
      UnitAddTorus.measurePreserving_equivPiIoc (a := fun _ : Fin 2 => (0 : ℝ))
  have htSubtype : AEStronglyMeasurable (fun x : cellSubtype => b t x.1) cellMeasure :=
    htCell.comp_measurePreserving hmeasureCell
  have htTorus : AEStronglyMeasurable
      (fun x : Torus => b t (equiv x).1) (volume : Measure Torus) :=
    htSubtype.comp_measurePreserving hmeasureTorus
  have heq : (fun x : Torus => b t (equiv x).1) =
      AVenhance.Infra.Torus.periodicToTorus (b t) := by
    funext x
    rfl
  exact heq ▸ htTorus

/-- Every real-mode drift matrix integrand is spatially integrable for almost every time. -/
theorem frozenDrift_realModeEntry_integrable_ae (N : ℕ)
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ i j,
      Integrable (fun x : Torus =>
        vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
          (realFourierModeGradFin N j x) * realFourierModeFin N i x) volume := by
  have hslice := frozenDrift_torus_slice_aestronglyMeasurable b hb_meas
  obtain ⟨B, hB, hdot⟩ := frozenDrift_vecDot_bound b hb_bdd
  filter_upwards [hslice, ae_restrict_mem measurableSet_Icc] with t hbt ht
  intro i j
  have hgrad_meas : AEStronglyMeasurable (realFourierModeGradFin N j)
      (volume : Measure Torus) := by
    let a := (realFourierIndexEquivFin N).symm j
    have hmeas : Measurable
        (AVenhance.Infra.Torus.periodicToTorus (realFourierModeAmbientGrad N a)) := by
      exact (realFourierModeAmbientGrad_continuous N a).measurable.comp
        (AVenhance.Infra.Torus.measurable_unitTorusRepresentative 2)
    exact (realFourierModeGradFin_eq_periodicToTorus N j).symm ▸
      hmeas.aestronglyMeasurable
  have hmode_meas : AEStronglyMeasurable (realFourierModeFin N i)
      (volume : Measure Torus) :=
    (realFourierModeFin_continuous N i).aestronglyMeasurable
  have hdot_cont : Continuous (fun p : Vec 2 × Vec 2 =>
      Homogenization.vecDot p.1 p.2) := by
    unfold Homogenization.vecDot
    exact continuous_finsetSum _ fun k hk =>
      ((continuous_apply k).comp continuous_fst).mul
        ((continuous_apply k).comp continuous_snd)
  have hdot_meas : AEStronglyMeasurable (fun x : Torus =>
      Homogenization.vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
        (realFourierModeGradFin N j x)) volume :=
    hdot_cont.comp_aestronglyMeasurable (hbt.prodMk hgrad_meas)
  have hfun_meas : AEStronglyMeasurable (fun x : Torus =>
      Homogenization.vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
        (realFourierModeGradFin N j x) * realFourierModeFin N i x) volume :=
    hdot_meas.mul hmode_meas
  let g : Torus → ℝ := fun x => euclideanVecNorm (realFourierModeGradFin N j x)
  let u : Torus → ℝ := realFourierModeFin N i
  let f : Torus → ℝ := fun x =>
    Homogenization.vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
      (realFourierModeGradFin N j x) * realFourierModeFin N i x
  have hpoint : ∀ᵐ x ∂(volume : Measure Torus),
      |f x| ≤ B * (|g x| * |u x|) := by
    filter_upwards with x
    have hb := hdot t ht
      (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) (realFourierModeGradFin N j x)
    have hrep : AVenhance.Infra.Torus.periodicToTorus (b t) x =
        b t (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) := rfl
    dsimp [f, g, u]
    rw [hrep]
    calc
      |Homogenization.vecDot (b t
          (AVenhance.Infra.Torus.unitTorusRepresentative 2 x))
          (realFourierModeGradFin N j x) * realFourierModeFin N i x| =
          |Homogenization.vecDot (b t
            (AVenhance.Infra.Torus.unitTorusRepresentative 2 x))
            (realFourierModeGradFin N j x)| * |realFourierModeFin N i x| := abs_mul _ _
      _ ≤ (B * euclideanVecNorm (realFourierModeGradFin N j x)) *
            |realFourierModeFin N i x| :=
          mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = B * (|euclideanVecNorm (realFourierModeGradFin N j x)| *
            |realFourierModeFin N i x|) := by
          rw [abs_of_nonneg (euclideanVecNorm_nonneg _)]
          ring
  have htriple : ENNReal.HolderTriple 2 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have hprod : Integrable (fun x : Torus => |g x| * |u x|) volume := by
    have hm := @MemLp.integrable_mul Torus _ volume ℝ _ 2 2
      (fun x => ‖g x‖) (fun x => ‖u x‖)
      (realFourierModeGradFin_norm_memLp N j).norm
      (realFourierModeFin_memLp N i).norm htriple
    convert hm using 1
  have hmajor : Integrable (fun x : Torus => B * (|g x| * |u x|)) volume :=
    hprod.const_mul B
  have hfintegrable : Integrable f volume := by
    apply hmajor.mono' hfun_meas
    filter_upwards [hpoint] with x hx
    simpa [Real.norm_eq_abs, f, g, u] using hx
  simpa [f, vecDot, Homogenization.vecDot] using hfintegrable

/-- Pointwise bilinearity of the drift form under the two finite real Fourier syntheses. -/
theorem realFourierDriftExpansion_pointwise (N : ℕ)
    (b : Torus → Vec 2) (c : Coefficients (RealFourierDimension N)) :
    (fun x : Torus =>
      Homogenization.vecDot (b x)
        (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
          modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x) =
      fun x =>
        ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
          c i * c j *
            (Homogenization.vecDot (b x) (realFourierModeGradFin N j x) *
              realFourierModeFin N i x) := by
  funext x
  have hgrad : Homogenization.vecDot (b x)
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) =
      ∑ j : Fin (RealFourierDimension N), c j *
        Homogenization.vecDot (b x) (realFourierModeGradFin N j x) := by
    simp only [Homogenization.vecDot, Pi.smul_apply, Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hgrad]
  simp only [modeExpansion]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Under the a.e. slice integrability supplied by product measurability, the finite drift
integral expands as the quadratic sum of weak matrix entries. -/
theorem realFourierDriftExpansion_integral (N : ℕ)
    (b : ℝ → Torus → Vec 2) (t : ℝ)
    (c : Coefficients (RealFourierDimension N))
    (hentries : ∀ i j, Integrable (fun x : Torus =>
      Homogenization.vecDot (b t x) (realFourierModeGradFin N j x) *
        realFourierModeFin N i x) volume) :
    ∫ x : Torus,
      Homogenization.vecDot (b t x)
        (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
          modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x =
      ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
        c i * c j * ∫ x : Torus,
          Homogenization.vecDot (b t x) (realFourierModeGradFin N j x) *
            realFourierModeFin N i x := by
  rw [show (fun x : Torus =>
      Homogenization.vecDot (b t x)
        (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
          modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x) =
      fun x =>
        ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
          c i * c j *
            (Homogenization.vecDot (b t x) (realFourierModeGradFin N j x) *
              realFourierModeFin N i x) from
    realFourierDriftExpansion_pointwise N (fun x => b t x) c]
  have hinner (i : Fin (RealFourierDimension N)) :
      Integrable (fun x : Torus => ∑ j : Fin (RealFourierDimension N),
        c i * c j *
          (Homogenization.vecDot (b t x) (realFourierModeGradFin N j x) *
            realFourierModeFin N i x)) volume := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact (hentries i j).const_mul (c i * c j)
  rw [integral_finsetSum (s := Finset.univ) (f := fun i : Fin (RealFourierDimension N) =>
      fun x => ∑ j : Fin (RealFourierDimension N),
        c i * c j *
          (Homogenization.vecDot (b t x) (realFourierModeGradFin N j x) *
            realFourierModeFin N i x)) (fun i hi => hinner i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum (s := Finset.univ) (f := fun j : Fin (RealFourierDimension N) =>
      fun x => c i * c j *
        (Homogenization.vecDot (b t x) (realFourierModeGradFin N j x) *
          realFourierModeFin N i x))]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul]
  · intro j hj
    exact (hentries i j).const_mul (c i * c j)

/-- The quadratic drift form obtained by expanding a positive-cutoff real Fourier sum. -/
@[irreducible]
noncomputable def positiveCutoffGradientMap (N : ℕ) :
    Coefficients (RealFourierDimension N) →L[ℝ] SpatialGradientL2 :=
  realFourierGradientMap N

/-- Quadratic contribution of the drift to the real Fourier Galerkin energy. -/
def realFourierDriftForm (N : ℕ) (drift : ℝ → Torus → Vec 2) (t : ℝ)
    (c : Coefficients (RealFourierDimension N)) : ℝ :=
  ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
    c i * c j * ∫ x : Torus,
      Homogenization.vecDot (drift t x) (realFourierModeGradFin N j x) *
        realFourierModeFin N i x

/-- The explicit dot-product constant associated with the drift bound. -/
noncomputable def positiveCutoffDriftConstant (b : ℝ → Vec 2 → Vec 2)
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) : ℝ :=
  Real.sqrt 2 * Classical.choose hb_bdd

/-- The bounded drift controls the concrete finite Fourier drift form. -/
theorem positiveCutoffDriftForm_bound (N : ℕ)
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) :
    0 ≤ positiveCutoffDriftConstant b hb_bdd ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ c,
      |realFourierDriftForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c| ≤
          positiveCutoffDriftConstant b hb_bdd * ‖positiveCutoffGradientMap N c‖ * ‖c‖ := by
  classical
  let drift : ℝ → Torus → Vec 2 := fun t =>
    AVenhance.Infra.Torus.periodicToTorus (b t)
  let C : ℝ := Classical.choose hb_bdd
  have hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C := Classical.choose_spec hb_bdd
  have hC_nonneg : 0 ≤ C := by
    have h := hC (1 / 2) (by norm_num) 0
    exact (norm_nonneg _).trans h
  let B := positiveCutoffDriftConstant b hb_bdd
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) hC_nonneg
  have hdot : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x v,
      |Homogenization.vecDot (b t x) v| ≤ B * euclideanVecNorm v := by
    intro t ht x v
    exact vecDot_le_of_supNorm_le hC_nonneg (hC t ht x)
  have hentries := frozenDrift_realModeEntry_integrable_ae N b hb_meas hb_bdd
  refine ⟨hB, ?_⟩
  filter_upwards [hentries, ae_restrict_mem measurableSet_Icc] with t hentries_t ht
  intro c
  have hentries_t' (i j : Fin (RealFourierDimension N)) :
      Integrable (fun x : Torus => Homogenization.vecDot (drift t x)
        (realFourierModeGradFin N j x) * realFourierModeFin N i x) volume := by
    simpa only [drift, ← fourierGalerkin_vecDot_eq_frozen] using hentries_t i j
  have hexpansion := realFourierDriftExpansion_integral N drift t c hentries_t'
  have hpoint : ∀ᵐ x ∂(volume : Measure Torus),
      |Homogenization.vecDot (drift t x)
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
            modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x| ≤
        B * (|euclideanVecNorm
            (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)| *
          |modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x|) := by
    filter_upwards with x
    have hd := hdot t ht (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)
    have hrep : drift t x = b t (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) := rfl
    rw [hrep]
    calc
      |Homogenization.vecDot (b t
          (AVenhance.Infra.Torus.unitTorusRepresentative 2 x))
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
            modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x| =
        |Homogenization.vecDot (b t
            (AVenhance.Infra.Torus.unitTorusRepresentative 2 x))
            (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)| *
          |modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x| := abs_mul _ _
      _ ≤ (B * euclideanVecNorm
            (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)) *
          |modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x| :=
        mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      _ = B * (|euclideanVecNorm
            (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)| *
          |modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x|) := by
        rw [abs_of_nonneg (euclideanVecNorm_nonneg _)]
        ring
  have hL2 := driftIntegral_bound_of_L2_or_not
    (fun x : Torus => Homogenization.vecDot (drift t x)
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
        modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x)
    (fun x => euclideanVecNorm
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x))
    (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c) B hB hpoint
    (realFourierGradientExpansion_norm_memLp N c) (realFourierScalarExpansion_memLp N c)
  have hform : realFourierDriftForm N drift t c =
      ∫ x : Torus,
        Homogenization.vecDot (drift t x)
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
          modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x := by
    dsimp [realFourierDriftForm]
    exact hexpansion.symm
  have hgradNormIntegral :
      (∫ x : Torus, ‖euclideanVecNorm
        (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)‖ ^
          (2 : ℝ)) =
      ∫ x : Torus, euclideanVecNorm
        (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) ^
          (2 : ℝ) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (euclideanVecNorm_nonneg _)]
  calc
    |realFourierDriftForm N drift t c| = |∫ x : Torus,
        Homogenization.vecDot (drift t x)
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
          modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x| :=
            congrArg abs hform
    _ ≤ B * (∫ x : Torus, ‖euclideanVecNorm
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)‖ ^
          (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ x : Torus,
          ‖modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x‖ ^
            (2 : ℝ)) ^ ((1 : ℝ) / 2) := hL2
    _ = B * (∫ x : Torus, euclideanVecNorm
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) ^
          (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ x : Torus,
          ‖modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x‖ ^
            (2 : ℝ)) ^ ((1 : ℝ) / 2) := by rw [hgradNormIntegral]
    _ = B * ‖positiveCutoffGradientMap N c‖ * ‖c‖ := by
      rw [realFourierGradientExpansion_l2Factor,
        realFourierScalarExpansion_l2Factor]
      unfold positiveCutoffGradientMap
      rfl

/-- The chosen drift constant satisfies the bound proved from the hypotheses. -/
theorem positiveCutoffDriftConstant_spec (N : ℕ) (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) :
    0 ≤ positiveCutoffDriftConstant b hb_bdd ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ c,
        |realFourierDriftForm N
          (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c| ≤
            positiveCutoffDriftConstant b hb_bdd *
              ‖positiveCutoffGradientMap N c‖ * ‖c‖ := by
  exact positiveCutoffDriftForm_bound N b hb_meas hb_bdd

/-- A uniform matrix-entry bound for the positive real Fourier frame. -/
theorem positiveCutoffWeakFormEntry_bound (N : ℕ) (b : ℝ → Vec 2 → Vec 2)
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) (κ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ i j : Fin (RealFourierDimension N),
        |weakFormMatrixEntry
          (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x) κ
          (realFourierModeFin N) (realFourierModeGradFin N) t i j| ≤ K := by
  classical
  have hG : 0 ≤ realFourierCutoffGradientBound N :=
    realFourierCutoffGradientBound_nonneg N
  have hgrad_memLp : ∀ i : Fin (RealFourierDimension N),
      MemLp (fun x : Torus => euclideanVecNorm (realFourierModeGradFin N i x)) 2 volume :=
    realFourierModeGradFin_norm_memLp N
  have hmode_memLp : ∀ i : Fin (RealFourierDimension N),
      MemLp (realFourierModeFin N i) 2 volume := realFourierModeFin_memLp N
  have hgrad_factor : ∀ i : Fin (RealFourierDimension N),
      0 ≤ realFourierModeGradFinL2Factor N i ∧
        realFourierModeGradFinL2Factor N i ≤ realFourierCutoffGradientBound N := by
    intro i
    exact ⟨realFourierModeGradFin_l2Factor_nonneg N i,
      realFourierModeGradFin_l2Factor_le_cutoff N i⟩
  have hmode_factor : ∀ i : Fin (RealFourierDimension N),
      0 ≤ realFourierModeFinL2Factor N i ∧ realFourierModeFinL2Factor N i ≤ 1 := by
    intro i
    rw [realFourierModeFin_l2Factor_eq_one]
    norm_num
  have hdiffusion : ∀ i j : Fin (RealFourierDimension N),
      |∫ x : Torus, vecDot (realFourierModeGradFin N j x)
        (realFourierModeGradFin N i x)| ≤ realFourierCutoffGradientBound N ^ 2 := by
    intro i j
    exact realFourierModeGradFin_diffusion_abs_bound N i j
  exact frozenWeakFormMatrixEntry_abs_bound b hb_bdd κ (realFourierModeFin N)
    (realFourierModeGradFin N) hG (by norm_num) (sq_nonneg _) hgrad_memLp hmode_memLp
    hgrad_factor hmode_factor hdiffusion

/-- A chosen entry bound for the positive-cutoff weak matrix. -/
noncomputable def positiveCutoffMatrixConstant (N : ℕ) (b : ℝ → Vec 2 → Vec 2)
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) (κ : ℝ) : ℝ :=
  Classical.choose (positiveCutoffWeakFormEntry_bound N b hb_bdd κ)

/-- The chosen matrix bound applies to every entry on the physical time interval. -/
theorem positiveCutoffMatrixConstant_spec (N : ℕ) (b : ℝ → Vec 2 → Vec 2)
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) (κ : ℝ) :
    0 ≤ positiveCutoffMatrixConstant N b hb_bdd κ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j : Fin (RealFourierDimension N),
        |weakFormMatrixEntry
          (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x) κ
          (realFourierModeFin N) (realFourierModeGradFin N) t i j| ≤
            positiveCutoffMatrixConstant N b hb_bdd κ := by
  exact Classical.choose_spec (positiveCutoffWeakFormEntry_bound N b hb_bdd κ)

/-- The finite coefficient energy identity for the concrete positive Fourier weak matrix. -/
theorem positiveCutoffWeakForm_energy_identity (N : ℕ) (b : ℝ → Vec 2 → Vec 2) (κ : ℝ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (c : Coefficients (RealFourierDimension N)) :
    2 * inner ℝ c
        (frozenWeakFormCoefficient b κ (realFourierModeFin N)
          (realFourierModeGradFin N) t c) =
      -2 * realFourierDriftForm N
          (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c -
        2 * κ * ‖positiveCutoffGradientMap N c‖ ^ 2 := by
  let drift : ℝ → Torus → Vec 2 := fun s =>
    AVenhance.Infra.Torus.periodicToTorus (b s)
  have hcoeff : frozenWeakFormCoefficient b κ (realFourierModeFin N)
      (realFourierModeGradFin N) t = matrixCoefficientCLM
        (fun i j => weakFormMatrixEntry drift κ (realFourierModeFin N)
          (realFourierModeGradFin N) t i j) := by
    simp [frozenWeakFormCoefficient, ht, drift]
  rw [hcoeff, matrixCoefficientCLM_inner_quadratic, realFourierWeakMatrix_quadratic]
  simp only [realFourierDriftForm, drift, positiveCutoffGradientMap, realFourierGradientMap_apply,
      neg_mul]
  simp_rw [← fourierGalerkin_vecDot_eq_frozen]
  ring_nf

/-- The pointwise coefficient energy identity holds for a.e. physical time. -/
theorem positiveCutoffWeakForm_energy_ae (N : ℕ) (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ c,
      2 * inner ℝ c
          (frozenWeakFormCoefficient b κ (realFourierModeFin N)
            (realFourierModeGradFin N) t c) =
        -2 * realFourierDriftForm N
            (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c -
          2 * κ * ‖positiveCutoffGradientMap N c‖ ^ 2 := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  intro c
  exact positiveCutoffWeakForm_energy_identity N b κ t ht c

/-- The measurable-drift theorem applies to the concrete real Fourier frame. -/
theorem positiveCutoffCoefficient_aestronglyMeasurable (N : ℕ)
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t)) (κ : ℝ) :
    AEStronglyMeasurable
      (frozenWeakFormCoefficient b κ (realFourierModeFin N) (realFourierModeGradFin N)) volume := by
  let modeAmbient : Fin (RealFourierDimension N) → Vec 2 → ℝ := fun i =>
    realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)
  let modeGradAmbient : Fin (RealFourierDimension N) → Vec 2 → Vec 2 := fun i =>
    realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm i)
  have hmode_eq : ∀ i, realFourierModeFin N i =
      AVenhance.Infra.Torus.periodicToTorus (modeAmbient i) := by
    intro i
    exact realFourierModeFin_eq_periodicToTorus N i
  have hgrad_eq : ∀ i, realFourierModeGradFin N i =
      AVenhance.Infra.Torus.periodicToTorus (modeGradAmbient i) := by
    intro i
    exact realFourierModeGradFin_eq_periodicToTorus N i
  have hmode_meas : ∀ i, AEStronglyMeasurable (modeAmbient i)
      (volume.restrict AVenhance.unitCube) := by
    intro i
    exact (realFourierModeAmbient_contDiff N
      ((realFourierIndexEquivFin N).symm i)).continuous.aestronglyMeasurable.mono_measure
        (Measure.restrict_le_self)
  have hgrad_meas : ∀ i, AEStronglyMeasurable (modeGradAmbient i)
      (volume.restrict AVenhance.unitCube) := by
    intro i
    exact (realFourierModeAmbientGrad_continuous N
      ((realFourierIndexEquivFin N).symm i)).aestronglyMeasurable.mono_measure
        (Measure.restrict_le_self)
  have hmode_per : ∀ i, AVenhance.Infra.Torus.IsZdPeriodic (modeAmbient i) := by
    intro i
    exact (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen (modeAmbient i)).2
      (realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm i))
  have hgrad_per : ∀ i k,
      AVenhance.Infra.Torus.IsZdPeriodic (fun x => modeGradAmbient i x k) := by
    intro i k
    have hvec : AVenhance.Infra.Torus.IsZdPeriodic (modeGradAmbient i) :=
      (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen (modeGradAmbient i)).2
        (realFourierModeAmbientGrad_periodic N ((realFourierIndexEquivFin N).symm i))
    intro z x
    exact congrFun (hvec z x) k
  exact frozenWeakFormCoefficient_aestronglyMeasurable b hb_meas hb_per κ
    (realFourierModeFin N) (realFourierModeGradFin N) modeAmbient modeGradAmbient
    hmode_eq hgrad_eq hmode_meas hgrad_meas hmode_per hgrad_per

/-- The concrete cutoff coefficient agrees a.e. with its weak-form matrix. -/
theorem positiveCutoffCoefficient_matrixSpec (N : ℕ) (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ c i,
      frozenWeakFormCoefficient b κ (realFourierModeFin N)
        (realFourierModeGradFin N) t c i =
        ∑ j, weakFormMatrixEntry
          (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x) κ
          (realFourierModeFin N) (realFourierModeGradFin N) t i j * c j := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  intro c i
  simp [frozenWeakFormCoefficient, ht, matrixCoefficientCLM_apply, weakFormMatrixEntry]

/-- The matrix bound gives the global operator bound required by the finite ODE. -/
theorem positiveCutoffCoefficient_norm_le (N : ℕ) (b : ℝ → Vec 2 → Vec 2)
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) (κ : ℝ) :
    ∀ t, ‖frozenWeakFormCoefficient b κ (realFourierModeFin N)
      (realFourierModeGradFin N) t‖ ≤
        (RealFourierDimension N : ℝ) ^ 2 * positiveCutoffMatrixConstant N b hb_bdd κ := by
  have hspec := positiveCutoffMatrixConstant_spec N b hb_bdd κ
  exact frozenWeakFormCoefficient_norm_le_of_entries b κ (realFourierModeFin N)
    (realFourierModeGradFin N) hspec.1 hspec.2

/-- Projection of the initial datum has the finite real Fourier expansion in its own
coefficient vector. -/
theorem positiveCutoffInitial_projection (N : ℕ) (θ₀ : Vec 2 → ℝ)
    (hθ₀_L2 : MemL2On AVenhance.unitCube θ₀) :
    ∀ x : Torus,
      modeExpansion (RealFourierDimension N) (realFourierModeFin N)
        (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus θ₀)) x =
        realFourierProjection N (AVenhance.Infra.Torus.periodicToTorus θ₀) x := by
  have hθtorus : MemLp (AVenhance.Infra.Torus.periodicToTorus θ₀) 2
      (volume : Measure Torus) := frozenInitialData_memLp_torus hθ₀_L2
  intro x
  exact congrFun
    (realFourierModeFin_projectionExpansion_eq_projection N
      (hθtorus.integrable (by norm_num))) x

/-- Concrete positive-cutoff Galerkin data built from the measurable, bounded, periodic
drift and the `L²` initial datum. -/
noncomputable def positiveCutoffGalerkinData (N : ℕ)
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t))
    (κ : ℝ) (hκ : 0 < κ) (θ₀ : Vec 2 → ℝ)
    (hθ₀_L2 : MemL2On AVenhance.unitCube θ₀) :
    WeakFormGalerkinData (RealFourierDimension N) SpatialGradientL2 :=
  { mode := realFourierModeFin N
    modeGrad := realFourierModeGradFin N
    mode_orthonormal := realFourierModeFin_orthonormal N
    frequencyCutoff := N
    modeExpansion_fixed_by_projection := fun c x =>
      congrFun (realFourierProjection_modeExpansion N c) x
    initialData := AVenhance.Infra.Torus.periodicToTorus θ₀
    drift := fun t => AVenhance.Infra.Torus.periodicToTorus (b t)
    diffusivity := κ
    diffusivity_pos := hκ
    initial := modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus θ₀)
    coefficient := frozenWeakFormCoefficient b κ (realFourierModeFin N)
      (realFourierModeGradFin N)
    coefficientBound := (RealFourierDimension N : ℝ) ^ 2 *
      positiveCutoffMatrixConstant N b hb_bdd κ
    coefficientBound_nonneg := mul_nonneg (sq_nonneg _)
      (positiveCutoffMatrixConstant_spec N b hb_bdd κ).1
    coefficient_aestronglyMeasurable :=
      positiveCutoffCoefficient_aestronglyMeasurable N b hb_meas hb_per κ
    coefficient_norm_le := positiveCutoffCoefficient_norm_le N b hb_bdd κ
    matrix_spec := positiveCutoffCoefficient_matrixSpec N b κ
    initial_is_projection := rfl
    projection_eq_modeExpansion := positiveCutoffInitial_projection N θ₀ hθ₀_L2
    gradient := positiveCutoffGradientMap N
    driftBound := positiveCutoffDriftConstant b hb_bdd
    driftForm := realFourierDriftForm N
      (fun t => AVenhance.Infra.Torus.periodicToTorus (b t))
    weakForm_energy := positiveCutoffWeakForm_energy_ae N b κ
    drift_bound := by
      change ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ c,
        |realFourierDriftForm N
          (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c| ≤
            positiveCutoffDriftConstant b hb_bdd *
              ‖positiveCutoffGradientMap N c‖ * ‖c‖
      exact (positiveCutoffDriftForm_bound N b hb_meas hb_bdd).2 }

end AVenhance.Infra.Parabolic.FourierGalerkin

end
