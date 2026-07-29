/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.GammaFactor
public import LeanPool.Odlyzko.CompletedZeta.UnitFundamentalDomain
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open Complex MeasureTheory Set

namespace NumberField.Odlyzko

theorem cpow_prod_of_nonneg {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i) (s : ℂ) :
    (((∏ i ∈ t, a i : ℝ) : ℂ) ^ s) =
      ∏ i ∈ t, ((a i : ℂ) ^ s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (ha i (Finset.mem_insert_self i t))
          (Finset.prod_nonneg fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)),
        Finset.prod_insert hi]
      simp_all

theorem integrableOn_cpow_mul_cexp_neg_mul_sq_Ioi
    {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn
      (fun x : ℝ ↦
        (x : ℂ) ^ (2 * s - 1) * Complex.exp (-(r * x ^ 2)))
      (Ioi 0) := by
  have hbase :
      MellinConvergent (fun t : ℝ ↦ Complex.exp (-(t : ℂ))) s := by
    rw [MellinConvergent]
    convert Complex.GammaIntegral_convergent hs using 1
    · ext t
      simp [mul_comm]
  have hscaled :
      MellinConvergent
        (fun t : ℝ ↦ Complex.exp (-((r * t : ℝ) : ℂ))) s := by
    simpa only [Complex.ofReal_mul] using
      (MellinConvergent.comp_mul_left (f :=
        fun t : ℝ ↦ Complex.exp (-(t : ℂ))) (s := s) hr).2 hbase
  have hsquare :
      MellinConvergent
        (fun t : ℝ ↦ Complex.exp (-((r * t ^ 2 : ℝ) : ℂ)))
        (2 * s) := by
    have h := (MellinConvergent.comp_rpow
      (f := fun t : ℝ ↦ Complex.exp (-((r * t : ℝ) : ℂ)))
      (s := 2 * s) (a := 2) (by norm_num)).2
    simp_all
  rw [MellinConvergent] at hsquare
  simp_all

theorem integral_cpow_mul_cexp_neg_mul_sq_Ioi
    {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0,
      (x : ℂ) ^ (2 * s - 1) * Complex.exp (-(r * x ^ 2))) =
      (2 : ℂ)⁻¹ * (1 / r : ℂ) ^ s * Complex.Gamma s := by
  have hsq := mellin_comp_rpow
    (f := fun t : ℝ ↦ Complex.exp (-(r * t))) (2 * s) 2
  rw [show (2 * s) / (2 : ℝ) = s by norm_num] at hsq
  have hgamma := integral_cpow_mul_exp_neg_mul_Ioi hs hr
  rw [mellin] at hsq
  rw [mellin] at hsq
  simp only [smul_eq_mul, Complex.real_smul] at hsq
  rw [hgamma] at hsq
  have htwo : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  simpa only [htwo, Complex.ofReal_inv, Complex.ofReal_ofNat,
    Complex.ofReal_pow, one_div, Real.rpow_two, mul_assoc] using hsq

theorem integral_complexPlaceGaussian
    {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0,
      (x : ℂ) ^ (2 * s - 1) *
        Complex.exp (-(((2 * Real.pi * a : ℝ) : ℂ) *
          (x : ℂ) ^ 2))) =
      (2 : ℂ)⁻¹ * (a : ℂ) ^ (-s) * CompletedZeta.complexPlaceGammaFactor s := by
  rw [integral_cpow_mul_cexp_neg_mul_sq_Ioi hs
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) ha)]
  have hinv {r : ℝ} (hr : 0 < r) :
      (1 / r : ℂ) ^ s = (r : ℂ) ^ (-s) := by
    rw [one_div,
      Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg hr.le]
        exact Real.pi_ne_zero.symm),
      Complex.cpow_neg]
  rw [hinv (mul_pos (mul_pos (by norm_num) Real.pi_pos) ha)]
  rw [show ((2 * Real.pi * a : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * (a : ℂ) by simp]
  rw [Complex.mul_cpow_ofReal_nonneg
    (mul_nonneg (by norm_num) Real.pi_pos.le) ha.le (-s)]
  rw [complexPlaceGammaFactor_eq]
  rw [show ((2 * Real.pi : ℝ) : ℂ) =
    2 * (Real.pi : ℂ) by simp]
  ring

theorem integral_pi_complexPlaceGaussian_eq_prod
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ι → ℝ,
      ∏ i,
        (x i : ℂ) ^ (2 * s - 1) *
          Complex.exp (-(((2 * Real.pi * a i : ℝ) : ℂ) *
            (x i : ℂ) ^ 2))
      ∂Measure.pi (fun _ ↦ volume.restrict (Ioi 0))) =
      ∏ i, (2 : ℂ)⁻¹ * (a i : ℂ) ^ (-s) *
        CompletedZeta.complexPlaceGammaFactor s := by
  calc
    _ = ∏ i, ∫ x : ℝ,
        (x : ℂ) ^ (2 * s - 1) *
          Complex.exp (-(((2 * Real.pi * a i : ℝ) : ℂ) *
            (x : ℂ) ^ 2))
        ∂volume.restrict (Ioi 0) :=
      integral_fintype_prod_eq_prod _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact integral_complexPlaceGaussian hs (ha i)

end NumberField.Odlyzko

end

section

open Complex MeasureTheory NumberField NumberField.InfinitePlace Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem integral_totallyComplexGaussian_eq_prod
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ,
      ∏ w,
        (q w : ℂ) ^ (2 * s - 1) *
          Complex.exp (-(((2 * Real.pi * (w x) ^ 2 : ℝ) : ℂ) *
            (q w : ℂ) ^ 2))
      ∂Measure.pi (fun _ ↦ volume.restrict (Ioi 0))) =
      ∏ w : InfinitePlace K, (2 : ℂ)⁻¹ * (((w x) ^ 2 : ℝ) : ℂ) ^ (-s) *
        CompletedZeta.complexPlaceGammaFactor s := by
  classical
  apply integral_pi_complexPlaceGaussian_eq_prod
    (a := fun w : InfinitePlace K ↦ (w x) ^ 2)
  · intro w
    exact sq_pos_of_pos (InfinitePlace.pos_iff.mpr hx)
  · grind

variable [IsTotallyComplex K]

theorem prod_infinitePlace_sq_cpow_eq_absNorm_cpow
    (x : K) (s : ℂ) :
    (∏ w : InfinitePlace K, (((w x) ^ 2 : ℝ) : ℂ) ^ s) =
      ((((|Algebra.norm ℚ x| : ℚ) : ℝ)) : ℂ) ^ s := by
  classical
  rw [← cpow_prod_of_nonneg Finset.univ (fun w : InfinitePlace K ↦ (w x) ^ 2)
    (fun _ _ ↦ sq_nonneg _) s]
  congr 2
  simpa only [IsTotallyComplex.mult_eq] using InfinitePlace.prod_eq_abs_norm x

theorem prod_complexPlaceGaussian_eq_absNorm
    (x : K) (s : ℂ) :
    (∏ w : InfinitePlace K,
        (2 : ℂ)⁻¹ * (((w x) ^ 2 : ℝ) : ℂ) ^ (-s) *
          CompletedZeta.complexPlaceGammaFactor s) =
      ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^
          Fintype.card (InfinitePlace K) *
        ((((|Algebra.norm ℚ x| : ℚ) : ℝ)) : ℂ) ^ (-s) := by
  classical
  rw [← prod_infinitePlace_sq_cpow_eq_absNorm_cpow K x (-s)]
  calc
    _ = ∏ w : InfinitePlace K,
        ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) *
          (((w x) ^ 2 : ℝ) : ℂ) ^ (-s) := by grind
    _ = (∏ _w : InfinitePlace K,
          (2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) *
        ∏ w : InfinitePlace K, (((w x) ^ 2 : ℝ) : ℂ) ^ (-s) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by simp

theorem integral_totallyComplexGaussian_eq_absNorm
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ,
      ∏ w,
        (q w : ℂ) ^ (2 * s - 1) *
          Complex.exp (-(((2 * Real.pi * (w x) ^ 2 : ℝ) : ℂ) *
            (q w : ℂ) ^ 2))
      ∂Measure.pi (fun _ ↦ volume.restrict (Ioi 0))) =
      ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^ nrComplexPlaces K *
        ((((|Algebra.norm ℚ x| : ℚ) : ℝ)) : ℂ) ^ (-s) := by
  rw [integral_totallyComplexGaussian_eq_prod K hx hs,
    prod_complexPlaceGaussian_eq_absNorm K x s,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

end NumberField.Odlyzko

end

section

open Complex MeasureTheory NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- A complex place mellin gaussian used in the Odlyzko-bound argument. -/
noncomputable def complexPlaceMellinGaussian
    (x : K) (s : ℂ) (q : InfinitePlace K → ℝ) : ℂ :=
  ∏ w,
    (q w : ℂ) ^ (2 * s - 1) *
      Complex.exp (-(((2 * Real.pi * (w x) ^ 2 : ℝ) : ℂ) *
        (q w : ℂ) ^ 2))

theorem integrable_complexPlaceMellinGaussian
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    Integrable (complexPlaceMellinGaussian K x s)
      (Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0))) := by
  unfold complexPlaceMellinGaussian
  apply Integrable.fintype_prod
    (f := fun w : InfinitePlace K ↦ fun q : ℝ ↦
      (q : ℂ) ^ (2 * s - 1) *
        Complex.exp (-(((2 * Real.pi * (w x) ^ 2 : ℝ) : ℂ) *
          (q : ℂ) ^ 2)))
    (μ := fun _ : InfinitePlace K ↦ volume.restrict (Set.Ioi 0))
  intro w
  change IntegrableOn
    (fun q : ℝ ↦
      (q : ℂ) ^ (2 * s - 1) *
        Complex.exp (-(((2 * Real.pi * (w x) ^ 2 : ℝ) : ℂ) *
          (q : ℂ) ^ 2)))
    (Set.Ioi 0)
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using
    integrableOn_cpow_mul_cexp_neg_mul_sq_Ioi hs
      (r := 2 * Real.pi * (w x) ^ 2)
      (mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (sq_pos_of_pos (InfinitePlace.pos_iff.mpr hx)))

variable [IsTotallyComplex K]

theorem prod_infinitePlace_apply_unit_eq_one (u : (𝓞 K)ˣ) :
    ∏ w : InfinitePlace K, w (((u : 𝓞 K) : K)) = 1 := by
  classical
  let p := ∏ w : InfinitePlace K, w (((u : 𝓞 K) : K))
  have hp : 0 ≤ p :=
    Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _
  have hsq : p ^ 2 = 1 := by
    dsimp [p]
    rw [← Finset.prod_pow]
    simpa only [IsTotallyComplex.mult_eq, Units.norm, Rat.cast_one, abs_one] using
      InfinitePlace.prod_eq_abs_norm (((u : 𝓞 K) : K))
  nlinarith

theorem prod_infinitePlace_apply_unit_cpow_eq_one
    (u : (𝓞 K)ˣ) (s : ℂ) :
    ∏ w : InfinitePlace K,
      ((w (((u : 𝓞 K) : K)) : ℝ) : ℂ) ^ s = 1 := by
  classical
  rw [← cpow_prod_of_nonneg Finset.univ
    (fun w : InfinitePlace K ↦ w (((u : 𝓞 K) : K)))
    (fun _ _ ↦ apply_nonneg _ _) s]
  rw [prod_infinitePlace_apply_unit_eq_one K u]
  simp

theorem complexPlaceMellinGaussian_unit_mul
    (u : (𝓞 K)ˣ) (x : K) (s : ℂ) (q : InfinitePlace K → ℝ)
    (hq : ∀ w, 0 ≤ q w) :
    complexPlaceMellinGaussian K ((((u : 𝓞 K) : K)) * x) s q =
      complexPlaceMellinGaussian K x s
        ((fun w ↦ w (((u : 𝓞 K) : K))) * q) := by
  classical
  rw [complexPlaceMellinGaussian, complexPlaceMellinGaussian]
  simp only [Pi.mul_apply]
  symm
  calc
    _ = ∏ w : InfinitePlace K,
        ((w (((u : 𝓞 K) : K)) : ℂ) ^ (2 * s - 1)) *
          ((q w : ℂ) ^ (2 * s - 1) *
            Complex.exp (-(((2 * Real.pi *
              (w ((((u : 𝓞 K) : K)) * x)) ^ 2 : ℝ) : ℂ) *
                (q w : ℂ) ^ 2))) := by
      apply Finset.prod_congr rfl
      intro w _
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
        (apply_nonneg _ _) (hq w)]
      rw [mul_assoc, map_mul]
      push_cast
      ring_nf
    _ = (∏ w : InfinitePlace K,
          ((w (((u : 𝓞 K) : K)) : ℂ) ^ (2 * s - 1))) *
        ∏ w : InfinitePlace K,
          ((q w : ℂ) ^ (2 * s - 1) *
            Complex.exp (-(((2 * Real.pi *
              (w ((((u : 𝓞 K) : K)) * x)) ^ 2 : ℝ) : ℂ) *
                (q w : ℂ) ^ 2))) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by
      rw [prod_infinitePlace_apply_unit_cpow_eq_one K u (2 * s - 1),
        one_mul]

theorem integral_complexPlaceMellinGaussian
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ,
      complexPlaceMellinGaussian K x s q
      ∂Measure.pi (fun _ ↦ MeasureTheory.volume.restrict (Set.Ioi 0))) =
      ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^ nrComplexPlaces K *
        ((((|Algebra.norm ℚ x| : ℚ) : ℝ)) : ℂ) ^ (-s) := by
  exact integral_totallyComplexGaussian_eq_absNorm K hx hs

theorem complexPlaceMellinGaussian_fundamentalUnitForShift
    (z : {w : InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} → ℤ)
    (x : K) (s : ℂ) (y : mixedEmbedding.realSpace K) :
      complexPlaceMellinGaussian K x s
        ((fun w ↦ w (((fundamentalUnitForShift z : (𝓞 K)ˣ) : 𝓞 K) : K)) *
          mixedEmbedding.fundamentalCone.expMapBasis y) =
      complexPlaceMellinGaussian K
        ((((fundamentalUnitForShift z : (𝓞 K)ˣ) : 𝓞 K) : K) * x) s
        (mixedEmbedding.fundamentalCone.expMapBasis y) := by
  symm
  apply complexPlaceMellinGaussian_unit_mul
  exact fun w ↦
    (mixedEmbedding.fundamentalCone.expMapBasis_pos y w).le

end NumberField.Odlyzko

end
