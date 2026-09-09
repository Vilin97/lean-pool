/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TorusInverse
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

/-!
# Fourier coefficients of actual smooth periodic functions

Coefficients are defined by actual unit-interval integrals. Their decay is
derived from integration by parts and bounds for actual coordinate derivatives.
-/

noncomputable section

namespace NavierStokes.SmoothFourierData

open Set Function MeasureTheory TorusInverse
open scoped BigOperators ContDiff Interval Topology

local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- The actual unit-period Fourier coefficient of a function on the line. -/
def unitCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f n

theorem unitCoeff_eq_integral (f : ℝ → ℂ) (n : ℤ) :
    unitCoeff f n = ∫ x in (0 : ℝ)..1, fourier (-n) (x : UnitAddCircle) * f x := by
  have h := fourierCoeffOn_eq_integral f n (show (0 : ℝ) < 1 by norm_num)
  simpa [unitCoeff, fourier_coe_apply, smul_eq_mul] using h

theorem unitCoeff_const_mul (f : ℝ → ℂ) (c : ℂ) (n : ℤ) :
    unitCoeff (fun x => c * f x) n = c * unitCoeff f n :=
  fourierCoeffOn.const_mul f c n (show (0 : ℝ) < 1 by norm_num)

theorem unitCoeff_norm_le {f : ℝ → ℂ} {C : ℝ} (n : ℤ)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C) : ‖unitCoeff f n‖ ≤ C := by
  rw [unitCoeff_eq_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := C) (f := fun x => fourier (-n) (x : UnitAddCircle) * f x)
    (fun x hx => by
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using uIoc_subset_uIcc hx
      simpa only [norm_mul, fourier_apply, Circle.norm_coe, one_mul] using hb x hx')
  simpa only [sub_zero, abs_one, mul_one] using h

/-- The boundary term cancels because the actual endpoint values agree. -/
theorem unitCoeff_of_hasDerivAt {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f') (hp : f 1 = f 0) :
    unitCoeff f n = (omega * (n : ℂ))⁻¹ * unitCoeff f' n := by
  have h := fourierCoeffOn_of_hasDerivAt (show (0 : ℝ) < 1 by norm_num) hn
    (fun x _ => hd x) (hc.intervalIntegrable 0 1)
  have hden : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = -(omega * (n : ℂ)) := by
    unfold omega
    ring
  simpa only [unitCoeff, hp, sub_self, mul_zero, sub_zero, Complex.ofReal_one,
    Complex.ofReal_zero, one_mul, zero_sub, hden, one_div, inv_neg, neg_mul_neg] using h

/-- Unit-periodicity in both coordinates, expressed on the universal cover. -/
def UnitPeriodic (f : Plane → ℂ) : Prop :=
  ∀ z : Plane, ∀ k : Frequency, f (z + ((k.1 : ℝ), (k.2 : ℝ))) = f z

/-- The genuine first coordinate derivative. -/
noncomputable def partialX (f : Plane → ℂ) (z : Plane) : ℂ := fderiv ℝ f z (1, 0)

noncomputable def xJet (p : ℕ) (f : Plane → ℂ) : Plane → ℂ := partialX^[p] f

@[simp] theorem xJet_zero (f : Plane → ℂ) : xJet 0 f = f := rfl

theorem xJet_succ (p : ℕ) (f : Plane → ℂ) : xJet (p + 1) f = partialX (xJet p f) := by
  exact Function.iterate_succ_apply' partialX p f

theorem partialX_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (partialX f) :=
  (ContinuousLinearMap.apply ℝ ℂ (1, 0)).contDiff.comp
    (hf.fderiv_right (by simp))

theorem xJet_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (p : ℕ) :
    ContDiff ℝ ∞ (xJet p f) := by
  induction p with
  | zero => exact hf
  | succ p ih => rw [xJet_succ]; exact partialX_smooth ih

theorem partialX_periodic {f : Plane → ℂ} (hf : UnitPeriodic f) :
    UnitPeriodic (partialX f) := by
  intro z k
  have hfun : (fun w : Plane => f (w + ((k.1 : ℝ), (k.2 : ℝ)))) = f := funext fun w => hf w k
  have h := congrArg (fun g : Plane → ℂ => fderiv ℝ g z) hfun
  rw [fderiv_comp_add_right] at h
  exact congrArg (fun L : Plane →L[ℝ] ℂ => L (1, 0)) h

theorem xJet_periodic {f : Plane → ℂ} (hf : UnitPeriodic f) (p : ℕ) :
    UnitPeriodic (xJet p f) := by
  induction p with
  | zero => exact hf
  | succ p ih => rw [xJet_succ]; exact partialX_periodic ih

theorem hasDerivAt_slice {f : Plane → ℂ} {x y : ℝ}
    (hf : DifferentiableAt ℝ f (x, y)) :
    HasDerivAt (fun t => f (t, y)) (partialX f (x, y)) x := by
  exact hf.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

/-- The actual two-dimensional Fourier coefficient, with the first coordinate integrated first. -/
def coefficient (f : Plane → ℂ) (k : Frequency) : ℂ :=
  unitCoeff (fun y => unitCoeff (fun x => f (x, y)) k.1) k.2

theorem coefficient_norm_le {f : Plane → ℂ} {C : ℝ} (k : Frequency)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C) :
    ‖coefficient f k‖ ≤ C := by
  apply unitCoeff_norm_le
  intro y hy
  exact unitCoeff_norm_le k.1 (fun x hx => hb x hx y hy)

theorem coefficient_partialX {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) :
    coefficient f k = (omega * (k.1 : ℂ))⁻¹ * coefficient (partialX f) k := by
  have heq : (fun y => unitCoeff (fun x => f (x, y)) k.1) =
      (fun y => (omega * (k.1 : ℂ))⁻¹ * unitCoeff (fun x => partialX f (x, y)) k.1) := by
    funext y
    apply unitCoeff_of_hasDerivAt hk
    · intro x
      exact hasDerivAt_slice ((hf.differentiable (by simp)) (x, y))
    · exact (partialX_smooth hf).continuous.comp (continuous_id.prodMk continuous_const)
    · simpa using hp (0, y) (1, 0)
  unfold coefficient
  rw [heq, unitCoeff_const_mul]

/-- Repeated Fourier integration by parts in the first coordinate. -/
theorem coefficient_xJet {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) (p : ℕ) :
    coefficient f k = (omega * (k.1 : ℂ))⁻¹ ^ p * coefficient (xJet p f) k := by
  induction p with
  | zero => simp only [pow_zero, one_mul, xJet_zero]
  | succ p ih =>
      rw [ih, coefficient_partialX (xJet_smooth hf p) (xJet_periodic hp p) hk,
        xJet_succ, pow_succ, mul_assoc]

/-- A coefficient-decay estimate obtained from a bound on an actual derivative. -/
theorem coefficient_decay_first {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) (p : ℕ) {C : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖xJet p f (x, y)‖ ≤ C) :
    ‖coefficient f k‖ ≤ ‖(omega * (k.1 : ℂ))⁻¹‖ ^ p * C := by
  rw [coefficient_xJet hf hp hk p, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (coefficient_norm_le k hb) (pow_nonneg (norm_nonneg _) p)

/-- The negative Fourier character on the unit square. -/
def kernel (k : Frequency) (z : Plane) : ℂ :=
  fourier (-k.1) (z.1 : UnitAddCircle) * fourier (-k.2) (z.2 : UnitAddCircle)

theorem kernel_continuous (k : Frequency) : Continuous (kernel k) :=
  (((fourier (-k.1)).continuous.comp (AddCircle.continuous_mk' 1)).comp continuous_fst).mul
    (((fourier (-k.2)).continuous.comp (AddCircle.continuous_mk' 1)).comp continuous_snd)

theorem coefficient_eq_doubleIntegral (f : Plane → ℂ) (k : Frequency) :
    coefficient f k = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, kernel k (x, y) * f (x, y) := by
  unfold coefficient
  rw [unitCoeff_eq_integral]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [unitCoeff_eq_integral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  unfold kernel
  ring

theorem integral_square_swap {f : Plane → ℂ} (hf : Continuous f) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y) := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply (integral_integral_swap ?_).symm
  change Integrable f ((volume.restrict (Ioc (0 : ℝ) 1)).prod
    (volume.restrict (Ioc (0 : ℝ) 1)))
  rw [Measure.prod_restrict]
  exact (hf.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

noncomputable def swapFunction (f : Plane → ℂ) : Plane → ℂ := fun z => f (z.2, z.1)

theorem swapFunction_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (swapFunction f) := hf.comp (contDiff_snd.prodMk contDiff_fst)

theorem swapFunction_periodic {f : Plane → ℂ} (hp : UnitPeriodic f) :
    UnitPeriodic (swapFunction f) := by
  intro z k
  exact hp (z.2, z.1) (k.2, k.1)

theorem coefficient_swap {f : Plane → ℂ} (hf : Continuous f) (k : Frequency) :
    coefficient f k = coefficient (swapFunction f) (k.2, k.1) := by
  rw [coefficient_eq_doubleIntegral, coefficient_eq_doubleIntegral,
    integral_square_swap ((kernel_continuous k).fun_mul hf)]
  apply intervalIntegral.integral_congr
  intro x _
  apply intervalIntegral.integral_congr
  intro y _
  unfold kernel swapFunction
  ring

theorem coefficient_decay_second {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.2 ≠ 0) (p : ℕ) {C : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet p (swapFunction f) (x, y)‖ ≤ C) :
    ‖coefficient f k‖ ≤ ‖(omega * (k.2 : ℂ))⁻¹‖ ^ p * C := by
  rw [coefficient_swap hf.continuous k]
  exact coefficient_decay_first (swapFunction_smooth hf) (swapFunction_periodic hp) hk p hb

theorem norm_omega_ge_one : 1 ≤ ‖omega‖ := by
  have hnorm : ‖omega‖ = 2 * Real.pi := by
    simp [omega, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm]
  linarith [Real.two_le_pi]

/-- Multiplying by the first frequency power is controlled by the actual derivative norm. -/
theorem coefficient_first_moment {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) (p : ℕ) {C : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖xJet p f (x, y)‖ ≤ C) :
    |(k.1 : ℝ)| ^ p * ‖coefficient f k‖ ≤ C := by
  have hsymbol : omega * (k.1 : ℂ) ≠ 0 :=
    mul_ne_zero omega_ne_zero (by exact_mod_cast hk)
  have hident : (omega * (k.1 : ℂ)) ^ p * coefficient f k = coefficient (xJet p f) k := by
    rw [coefficient_xJet hf hp hk p, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hsymbol, one_pow, one_mul]
  have hn := congrArg norm hident
  simp only [norm_mul, norm_pow, Complex.norm_intCast] at hn
  have hfreq : |(k.1 : ℝ)| ≤ ‖omega‖ * |(k.1 : ℝ)| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right norm_omega_ge_one (abs_nonneg (k.1 : ℝ))
  calc
    |(k.1 : ℝ)| ^ p * ‖coefficient f k‖ ≤
        (‖omega‖ * |(k.1 : ℝ)|) ^ p * ‖coefficient f k‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hfreq p) (norm_nonneg _)
    _ = ‖coefficient (xJet p f) k‖ := hn
    _ ≤ C := coefficient_norm_le k hb

theorem dominant_coordinate_ne_zero {k : Frequency} (hk : k ≠ 0)
    (hdom : |(k.2 : ℝ)| ≤ |(k.1 : ℝ)|) : k.1 ≠ 0 := by
  intro hzero
  have hsecond : (k.2 : ℝ) = 0 := abs_eq_zero.mp
    (le_antisymm (by simpa [hzero] using hdom) (abs_nonneg _))
  exact hk (Prod.ext hzero (by exact_mod_cast hsecond))

theorem weight_le_dominant {k : Frequency} (hk : k.1 ≠ 0)
    (hdom : |(k.2 : ℝ)| ≤ |(k.1 : ℝ)|) : weight k ≤ 3 * |(k.1 : ℝ)| := by
  have hi : (1 : ℤ) ≤ |k.1| := Int.add_one_le_iff.mpr (abs_pos.mpr hk)
  have hr : (1 : ℝ) ≤ |(k.1 : ℝ)| := by exact_mod_cast hi
  unfold weight
  linarith

theorem weight_moment_of_dominant {k : Frequency} {p : ℕ} {A C : ℝ}
    (hk : k.1 ≠ 0) (hdom : |(k.2 : ℝ)| ≤ |(k.1 : ℝ)|) (hA : 0 ≤ A)
    (hb : |(k.1 : ℝ)| ^ p * A ≤ C) : weight k ^ p * A ≤ 3 ^ p * C := by
  calc
    weight k ^ p * A ≤ (3 * |(k.1 : ℝ)|) ^ p * A :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (weight_pos k).le (weight_le_dominant hk hdom) p) hA
    _ = 3 ^ p * (|(k.1 : ℝ)| ^ p * A) := by rw [mul_pow]; ring
    _ ≤ 3 ^ p * C := mul_le_mul_of_nonneg_left hb (by positivity)

/-- Finite derivative loss: a p-th frequency moment uses only the values and
the p-th pure derivative in each coordinate on the unit square. -/
theorem coefficient_polynomial_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (p : ℕ) {C : ℝ}
    (hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖xJet p f (x, y)‖ ≤ C)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet p (swapFunction f) (x, y)‖ ≤ C) (k : Frequency) :
    weight k ^ p * ‖coefficient f k‖ ≤ 3 ^ p * C := by
  by_cases hk : k = 0
  · subst k
    have hC : 0 ≤ C := (norm_nonneg _).trans (hzero 0 (by norm_num) 0 (by norm_num))
    simp only [weight, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, abs_zero, add_zero,
      one_pow, one_mul]
    exact (coefficient_norm_le 0 hzero).trans
      (le_mul_of_one_le_left hC (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)))
  rcases le_total |(k.2 : ℝ)| |(k.1 : ℝ)| with hdom | hdom
  · have hne := dominant_coordinate_ne_zero hk hdom
    exact weight_moment_of_dominant hne hdom (norm_nonneg _)
      (coefficient_first_moment hf hp hne p hfirst)
  · have hswap : (k.2, k.1) ≠ (0 : Frequency) := by
      intro h
      exact hk (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
    have hne := dominant_coordinate_ne_zero hswap hdom
    have h := weight_moment_of_dominant hne hdom
      (norm_nonneg (coefficient (swapFunction f) (k.2, k.1)))
      (coefficient_first_moment (swapFunction_smooth hf) (swapFunction_periodic hp) hne p hsecond)
    rw [← coefficient_swap hf.continuous k] at h
    have hw : weight (k.2, k.1) = weight k := by unfold weight; dsimp; ring
    simpa only [hw] using h

/-- Smoothness on the compact unit square supplies the derivative bounds;
no coefficient-decay hypothesis is used. -/
theorem exists_coefficient_polynomial_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (p : ℕ) :
    ∃ C : ℝ, ∀ k : Frequency, weight k ^ p * ‖coefficient f k‖ ≤ C := by
  have hc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn (xJet_smooth hf p).continuous.continuousOn
  obtain ⟨D, hD⟩ := hc.exists_bound_of_continuousOn
    (xJet_smooth (swapFunction_smooth hf) p).continuous.continuousOn
  let C := max A (max B D)
  refine ⟨3 ^ p * C, coefficient_polynomial_bound hf hp p ?_ ?_ ?_⟩
  · intro x hx y hy
    exact (hA (x, y) ⟨hx, hy⟩).trans (le_max_left _ _)
  · intro x hx y hy
    exact (hB (x, y) ⟨hx, hy⟩).trans ((le_max_left B D).trans (le_max_right _ _))
  · intro x hx y hy
    exact (hD (x, y) ⟨hx, hy⟩).trans ((le_max_right B D).trans (le_max_right _ _))

theorem summable_integer_weight_inv_two :
    Summable (fun n : ℤ => ((1 + |(n : ℝ)|) ^ 2)⁻¹) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hNat : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_one] using h
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast, Nat.abs_cast, add_comm, one_div] using hNat
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
      Nat.abs_cast, add_comm, one_div] using hNat

theorem weight_inv_four_le_product (k : Frequency) :
    (weight k ^ 4)⁻¹ ≤ ((1 + |(k.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(k.2 : ℝ)|) ^ 2)⁻¹ := by
  have hfirst : 1 + |(k.1 : ℝ)| ≤ weight k := by
    unfold weight
    linarith [abs_nonneg (k.2 : ℝ)]
  have hsecond : 1 + |(k.2 : ℝ)| ≤ weight k := by
    unfold weight
    linarith [abs_nonneg (k.1 : ℝ)]
  have hproduct : (1 + |(k.1 : ℝ)|) ^ 2 * (1 + |(k.2 : ℝ)|) ^ 2 ≤ weight k ^ 4 := by
    calc
      _ ≤ (weight k ^ 2) * (weight k ^ 2) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hfirst 2)
          (pow_le_pow_left₀ (by positivity) hsecond 2) (sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have h := one_div_le_one_div_of_le (by positivity :
    0 < (1 + |(k.1 : ℝ)|) ^ 2 * (1 + |(k.2 : ℝ)|) ^ 2) hproduct
  simpa only [one_div, mul_inv_rev, mul_comm] using h

theorem summable_weight_inv_four : Summable (fun k : Frequency => (weight k ^ 4)⁻¹) := by
  have hprod := summable_integer_weight_inv_two.mul_of_nonneg
    summable_integer_weight_inv_two (fun n => by positivity) (fun n => by positivity)
  exact Summable.of_nonneg_of_le (fun k => inv_nonneg.mpr (pow_nonneg (weight_pos k).le _))
    weight_inv_four_le_product hprod

/-- Every smooth unit-periodic function has all weighted absolute Fourier moments.
For the p-th moment the proof uses p+4 derivatives and a summable lattice majorant. -/
theorem rapid_coefficient {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) :
    Rapid (coefficient f) := by
  intro p
  obtain ⟨C, hC⟩ := exists_coefficient_polynomial_bound hf hp (p + 4)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (weight_pos k).le _) (norm_nonneg _)) _
    (summable_weight_inv_four.mul_left C)
  intro k
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (weight_pos k) 4)).mpr
  calc
    (weight k ^ p * ‖coefficient f k‖) * weight k ^ 4 =
        weight k ^ (p + 4) * ‖coefficient f k‖ := by rw [pow_add]; ring
    _ ≤ C := hC k

/-- A quantitative finite-loss estimate for the exact seminorm used by
`TorusInverse`. The lattice constant is finite by `summable_weight_inv_four`. -/
theorem coefficient_seminorm_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (p : ℕ) {C : ℝ}
    (hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (p + 4) f (x, y)‖ ≤ C)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (p + 4) (swapFunction f) (x, y)‖ ≤ C) :
    coeffSeminorm p (coefficient f) ≤
      (3 ^ (p + 4) * C) * ∑' k : Frequency, (weight k ^ 4)⁻¹ := by
  have hb (k : Frequency) : weight k ^ p * ‖coefficient f k‖ ≤
      (3 ^ (p + 4) * C) * (weight k ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (weight_pos k) 4)).mpr
    calc
      (weight k ^ p * ‖coefficient f k‖) * weight k ^ 4 =
          weight k ^ (p + 4) * ‖coefficient f k‖ := by rw [pow_add]; ring
      _ ≤ 3 ^ (p + 4) * C := coefficient_polynomial_bound hf hp (p + 4) hzero hfirst hsecond k
  have h := (rapid_coefficient hf hp p).tsum_le_tsum hb
    (summable_weight_inv_four.mul_left (3 ^ (p + 4) * C))
  simpa only [coeffSeminorm, tsum_mul_left] using h

/-! ## Identification with the actual torus Fourier coefficients -/

noncomputable def torusLift (f : Torus → ℂ) (x : Plane) : ℂ :=
  f ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle))

theorem torusLift_periodic (f : Torus → ℂ) : UnitPeriodic (torusLift f) := by
  intro z k
  simp [torusLift]

def torusCoefficient (f : Torus → ℂ) (k : Frequency) : ℂ :=
  ∫ z, torusMode (-k) z * f z ∂torusMeasure

theorem unitCoeff_torusLift (f : UnitAddCircle → ℂ) (n : ℤ) :
    unitCoeff (fun x : ℝ => f (x : UnitAddCircle)) n = fourierCoeff f n := by
  rw [unitCoeff_eq_integral, fourierCoeff_eq_intervalIntegral f n 0]
  simp only [one_div_one, zero_add, one_smul, smul_eq_mul]

theorem torusCoefficient_integrable (f : C(Torus, ℂ)) (k : Frequency) :
    Integrable (fun z => torusMode (-k) z * f z) torusMeasure := by
  apply (integrable_const (‖f‖ : ℝ)).mono'
    ((torusMode (-k)).continuous.fun_mul f.continuous).aestronglyMeasurable
  filter_upwards with z
  simpa only [norm_mul, norm_torusMode, one_mul] using f.norm_coe_le_norm z

theorem coefficient_lift_eq_torus (f : C(Torus, ℂ)) (k : Frequency) :
    coefficient (torusLift f) k = torusCoefficient f k := by
  change unitCoeff (fun y => unitCoeff
    (fun x => f ((x : UnitAddCircle), (y : UnitAddCircle))) k.1) k.2 = _
  have hinner : (fun y : ℝ => unitCoeff
      (fun x => f ((x : UnitAddCircle), (y : UnitAddCircle))) k.1) =
      (fun y : ℝ => fourierCoeff (fun x : UnitAddCircle => f (x, (y : UnitAddCircle))) k.1) := by
    funext y
    exact unitCoeff_torusLift (fun x : UnitAddCircle => f (x, (y : UnitAddCircle))) k.1
  rw [hinner, unitCoeff_torusLift
    (fun y : UnitAddCircle => fourierCoeff (fun x : UnitAddCircle => f (x, y)) k.1) k.2]
  unfold fourierCoeff torusCoefficient
  rw [show torusMeasure = (AddCircle.haarAddCircle : Measure UnitAddCircle).prod
    AddCircle.haarAddCircle from rfl,
    integral_prod_symm _ (torusCoefficient_integrable f k)]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [torusMode, ContinuousMap.coe_mk, Prod.fst_neg, Prod.snd_neg]
  ring

/-- The same continuous function on Mathlib's native finite-product torus. -/
noncomputable def nativeFunction (f : C(Torus, ℂ)) : C(UnitAddTorus (Fin 2), ℂ) where
  toFun z := f (z 0, z 1)
  continuous_toFun := f.continuous.comp ((continuous_apply 0).prodMk (continuous_apply 1))

theorem native_mode_eq (k : Fin 2 → ℤ) (z : UnitAddTorus (Fin 2)) :
    UnitAddTorus.mFourier k z = torusMode (k 0, k 1) (z 0, z 1) := by
  simp [UnitAddTorus.mFourier, torusMode, Fin.prod_univ_two]

theorem native_coefficient_eq (f : C(Torus, ℂ)) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (nativeFunction f) k = torusCoefficient f (k 0, k 1) := by
  have h := (measurePreserving_finTwoArrow
    (AddCircle.haarAddCircle : Measure UnitAddCircle)).integral_comp'
      (fun z : Torus => torusMode (-(k 0, k 1)) z * f z)
  simp only [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier, torusMode, torusCoefficient,
    torusMeasure, nativeFunction, Fin.prod_univ_two, smul_eq_mul,
    MeasureTheory.volume_pi,
    MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo_apply] at h ⊢
  exact h

/-- Genuine Fourier reconstruction: summability is derived from smoothness. -/
theorem torusSeries_coefficient (f : C(Torus, ℂ))
    (hf : ContDiff ℝ ∞ (torusLift f)) (z : Torus) :
    torusSeries (coefficient (torusLift f)) z = f z := by
  have ha := rapid_coefficient hf (torusLift_periodic f)
  have hc (k : Fin 2 → ℤ) : UnitAddTorus.mFourierCoeff (nativeFunction f) k =
      coefficient (torusLift f) (k 0, k 1) := by
    rw [native_coefficient_eq, coefficient_lift_eq_torus]
  have hsum : Summable (UnitAddTorus.mFourierCoeff (nativeFunction f)) := by
    have hcoef : Summable (coefficient (torusLift f)) := Summable.of_norm ha.summable_norm
    have h := hcoef.comp_injective (finTwoArrowEquiv ℤ).injective
    have heq : UnitAddTorus.mFourierCoeff (nativeFunction f) =
        (fun k : Fin 2 → ℤ => coefficient (torusLift f) (k 0, k 1)) := funext hc
    rw [heq]
    exact h
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum ![z.1, z.2]
  simp_rw [hc] at h
  have hnative : HasSum (fun k : Fin 2 → ℤ =>
      coefficient (torusLift f) (k 0, k 1) * torusMode (k 0, k 1) z) (f z) := by
    simpa [hc, native_mode_eq, nativeFunction, smul_eq_mul] using h
  have hpairs : HasSum (fun k : Frequency =>
      coefficient (torusLift f) k * torusMode k z) (f z) :=
    (finTwoArrowEquiv ℤ).hasSum_iff.mp hnative
  exact hpairs.tsum_eq

theorem series_coefficient_lift (f : C(Torus, ℂ))
    (hf : ContDiff ℝ ∞ (torusLift f)) (x : Plane) :
    series (coefficient (torusLift f)) x = torusLift f x := by
  rw [series_eq_torusSeries]
  exact torusSeries_coefficient f hf _

theorem coefficient_zero_eq_mean (f : C(Torus, ℂ)) :
    coefficient (torusLift f) 0 = ∫ z, f z ∂torusMeasure := by
  rw [coefficient_lift_eq_torus]
  simp [torusCoefficient, torusMode]

/-- The constructed inverse now solves the equation for an arbitrary smooth
zero-mean torus function, not only for a preassigned coefficient sequence. -/
theorem inverse_solves_smooth_torus (d : Direction) (f : C(Torus, ℂ))
    (hf : ContDiff ℝ ∞ (torusLift f)) (hmean : (∫ z, f z ∂torusMeasure) = 0) (x : Plane) :
    fderiv ℝ (directionalInverse d (coefficient (torusLift f))) x (vector d) =
      torusLift f x := by
  have ha := rapid_coefficient hf (torusLift_periodic f)
  have hz : coefficient (torusLift f) 0 = 0 := by rw [coefficient_zero_eq_mean, hmean]
  rw [directionalInverse_solves d ha hz, series_coefficient_lift f hf]

/-! ## Descent of an arbitrary periodic function on the plane -/

theorem unitPeriodic_first {f : Plane → ℂ} (hp : UnitPeriodic f) (y : ℝ) :
    Periodic (fun x => f (x, y)) 1 := by
  intro x
  simpa using hp (x, y) (1, 0)

theorem unitPeriodic_second {f : Plane → ℂ} (hp : UnitPeriodic f) (x : ℝ) :
    Periodic (fun y => f (x, y)) 1 := by
  intro y
  simpa using hp (x, y) (0, 1)

noncomputable def firstLift (f : Plane → ℂ) (hp : UnitPeriodic f)
    (z : UnitAddCircle) (y : ℝ) : ℂ :=
  (unitPeriodic_first hp y).lift z

theorem firstLift_periodic (f : Plane → ℂ) (hp : UnitPeriodic f) (z : UnitAddCircle) :
    Periodic (firstLift f hp z) 1 := by
  intro y
  refine Quotient.inductionOn' z (fun x => ?_)
  change f (x, y + 1) = f (x, y)
  exact unitPeriodic_second hp x y

noncomputable def descend (f : Plane → ℂ) (hp : UnitPeriodic f) (z : Torus) : ℂ :=
  (firstLift_periodic f hp z.1).lift z.2

@[simp] theorem descend_coe (f : Plane → ℂ) (hp : UnitPeriodic f) (x y : ℝ) :
    descend f hp ((x : UnitAddCircle), (y : UnitAddCircle)) = f (x, y) := rfl

theorem descend_continuous {f : Plane → ℂ} (hf : Continuous f) (hp : UnitPeriodic f) :
    Continuous (descend f hp) := by
  have hq : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  apply (hq.prodMap hq).isQuotientMap.continuous_iff.mpr
  exact hf

noncomputable def descendContinuous (f : Plane → ℂ) (hf : Continuous f)
    (hp : UnitPeriodic f) : C(Torus, ℂ) where
  toFun := descend f hp
  continuous_toFun := descend_continuous hf hp

@[simp] theorem torusLift_descendContinuous (f : Plane → ℂ) (hf : Continuous f)
    (hp : UnitPeriodic f) : torusLift (descendContinuous f hf hp) = f := rfl

/-- Pointwise reconstruction for an arbitrary actual smooth unit-periodic
function on the plane; neither rapid decay nor reconstruction is a premise. -/
theorem series_coefficient {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (x : Plane) : series (coefficient f) x = f x := by
  have h := series_coefficient_lift (descendContinuous f hf.continuous hp)
    (show ContDiff ℝ ∞ (torusLift (descendContinuous f hf.continuous hp)) from hf) x
  exact h

theorem coefficient_zero_eq_integral (f : Plane → ℂ) :
    coefficient f 0 = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y) := by
  rw [coefficient_eq_doubleIntegral]
  simp [kernel]

/-- The final coefficient bridge to the existing inverse construction. -/
theorem smooth_periodic_fourier_data {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) : Rapid (coefficient f) ∧ series (coefficient f) = f :=
  ⟨rapid_coefficient hf hp, funext (series_coefficient hf hp)⟩

theorem inverse_solves_smooth_periodic (d : Direction) {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f)
    (hmean : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)) = 0) (x : Plane) :
    fderiv ℝ (directionalInverse d (coefficient f)) x (vector d) = f x := by
  have hz : coefficient f 0 = 0 := by rw [coefficient_zero_eq_integral, hmean]
  rw [directionalInverse_solves d (rapid_coefficient hf hp) hz, series_coefficient hf hp]

end NavierStokes.SmoothFourierData
