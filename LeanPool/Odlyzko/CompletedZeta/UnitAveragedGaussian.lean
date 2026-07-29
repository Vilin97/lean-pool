/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.TotallyComplexGaussian
public import LeanPool.Odlyzko.CompletedZeta.UnitFundamentalDomain

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

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
