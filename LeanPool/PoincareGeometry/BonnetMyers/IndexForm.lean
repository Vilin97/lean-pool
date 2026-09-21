/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The scalar comparison test

The Bonnet--Myers index-form argument uses the Dirichlet test field
`sin (π t / L)`.  This file records the calculation independently of the
manifold layer.  In particular, the sharp constant is not inserted as an
axiom: it is the value of an explicitly computed interval integral.
-/

noncomputable section

open Set
open MeasureTheory
open scoped Real Interval BigOperators
open Real

namespace BonnetMyersEntry

/-- The scalar Dirichlet test field on an interval of length `L`. -/
def sineTest (L t : ℝ) : ℝ := Real.sin (Real.pi * t / L)

/-- The derivative of `sineTest`, written in the form used by the index form. -/
def sineTestDeriv (L t : ℝ) : ℝ :=
  (Real.pi / L) * Real.cos (Real.pi * t / L)

lemma sineTest_eq_zero_left (L : ℝ) : sineTest L 0 = 0 := by
  simp [sineTest]

lemma sineTest_eq_zero_right (L : ℝ) (hL : 0 < L) : sineTest L L = 0 := by
  simp [sineTest, hL.ne']

lemma sineTest_sq_integral (L : ℝ) (hL : 0 < L) :
    (∫ t in (0 : ℝ)..L, sineTest L t ^ 2) = L / 2 := by
  have hc : Real.pi / L ≠ 0 := ne_of_gt (div_pos Real.pi_pos hL)
  have hcomp := intervalIntegral.integral_comp_mul_left
    (f := fun u : ℝ => Real.sin u ^ 2) (a := (0 : ℝ)) (b := L)
    (c := Real.pi / L) hc
  have hcomp' :
      (∫ t in (0 : ℝ)..L, Real.sin (Real.pi * t / L) ^ 2) =
        (Real.pi / L)⁻¹ • (∫ u in (Real.pi / L) * 0..(Real.pi / L) * L,
          Real.sin u ^ 2) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcomp
  rw [show (fun t : ℝ => sineTest L t ^ 2) =
      fun t => Real.sin (Real.pi * t / L) ^ 2 by rfl, hcomp']
  simp only [zero_mul, mul_zero, smul_eq_mul, integral_sin_sq]
  have hmul : Real.pi / L * L = Real.pi := by field_simp [hL.ne']
  rw [hmul]
  simp [Real.sin_zero, Real.cos_zero, Real.sin_pi]
  field_simp [hL.ne'] <;> simp [hL.ne']

lemma sineTestDeriv_sq_integral (L : ℝ) (hL : 0 < L) :
    (∫ t in (0 : ℝ)..L, sineTestDeriv L t ^ 2) =
      (Real.pi / L) ^ 2 * (L / 2) := by
  have hc : Real.pi / L ≠ 0 := ne_of_gt (div_pos Real.pi_pos hL)
  have hcomp := intervalIntegral.integral_comp_mul_left
    (f := fun u : ℝ => Real.cos u ^ 2) (a := (0 : ℝ)) (b := L)
    (c := Real.pi / L) hc
  have hcomp' :
      (∫ t in (0 : ℝ)..L, Real.cos (Real.pi * t / L) ^ 2) =
        (Real.pi / L)⁻¹ • (∫ u in (Real.pi / L) * 0..(Real.pi / L) * L,
          Real.cos u ^ 2) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcomp
  rw [show (fun t : ℝ => sineTestDeriv L t ^ 2) =
      fun t => (Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2 by
        funext t
        simp [sineTestDeriv]
        ring]
  rw [intervalIntegral.integral_const_mul, hcomp']
  simp only [zero_mul, mul_zero, smul_eq_mul, integral_cos_sq]
  have hmul : Real.pi / L * L = Real.pi := by field_simp [hL.ne']
  rw [hmul]
  simp [Real.sin_zero, Real.cos_zero, Real.sin_pi]
  field_simp [hL.ne'] <;> simp [hL.ne']

/-- The scalar index form of the sine test. -/
def sineIndexForm (K L : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..L, sineTestDeriv L t ^ 2) -
    K * (∫ t in (0 : ℝ)..L, sineTest L t ^ 2)

lemma sineIndexForm_eq (K L : ℝ) (hL : 0 < L) :
    sineIndexForm K L = ((Real.pi / L) ^ 2 - K) * (L / 2) := by
  rw [sineIndexForm, sineTestDeriv_sq_integral L hL, sineTest_sq_integral L hL]
  ring

lemma sineIndexForm_negative {K L : ℝ} (hK : 0 < K)
    (hL : Real.pi / Real.sqrt K < L) :
    sineIndexForm K L < 0 := by
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hLpos : 0 < L := by
    exact lt_trans (div_pos Real.pi_pos hsqrt) hL
  rw [sineIndexForm_eq K L hLpos]
  have hratio : (Real.pi / L) ^ 2 < K := by
    have hpi : Real.pi < Real.sqrt K * L := by
      have := (div_lt_iff₀ hsqrt).mp hL
      nlinarith
    have hquot : Real.pi / L < Real.sqrt K := by
      apply (div_lt_iff₀ hLpos).2
      nlinarith [hpi]
    have hsq : (Real.pi / L) ^ 2 < (Real.sqrt K) ^ 2 :=
      (sq_lt_sq₀ (div_nonneg (le_of_lt Real.pi_pos) hLpos.le)
        hsqrt.le).2 hquot
    simpa [Real.sq_sqrt hK.le] using hsq
  have hfactor : (Real.pi / L) ^ 2 - K < 0 := sub_neg.mpr hratio
  have hhalf : 0 < L / 2 := by linarith
  exact mul_neg_of_neg_of_pos hfactor hhalf

/-- The scalar Dirichlet test has the displayed derivative at every time.
Exposing this separately lets the manifold layer use exactly the same test
function, rather than re-deriving its elementary calculus in a moving tangent
fibre. -/
lemma hasDerivAt_sineTest (L t : ℝ) :
    HasDerivAt (sineTest L) (sineTestDeriv L t) t := by
  have harg : HasDerivAt (fun s : ℝ ↦ Real.pi * s / L) (Real.pi / L) t := by
    have hfun : (fun s : ℝ ↦ Real.pi * s / L) =
        (fun s ↦ (Real.pi / L) * s) := by
      funext s
      ring
    rw [hfun]
    simpa using (hasDerivAt_id t).const_mul (Real.pi / L)
  have hsin := (Real.hasDerivAt_sin (Real.pi * t / L)).comp t harg
  have hsin' : HasDerivAt
      (fun s : ℝ ↦ Real.sin (Real.pi * s / L))
      (Real.cos (Real.pi * t / L) * (Real.pi / L)) t := by
    have hfun : (fun s : ℝ ↦ Real.sin (Real.pi * s / L)) =
        Real.sin ∘ (fun s ↦ Real.pi * s / L) := by
      funext s
      rfl
    rw [hfun]
    simpa only [Function.comp_apply] using hsin
  have hscalar : HasDerivAt
      (fun s : ℝ ↦ Real.sin (Real.pi * s / L))
      ((Real.pi / L) * Real.cos (Real.pi * t / L)) t := by
    simpa [mul_comm] using hsin'
  change HasDerivAt
    (fun s : ℝ ↦ Real.sin (Real.pi * s / L))
    ((Real.pi / L) * Real.cos (Real.pi * t / L)) t
  exact hscalar

/-! ### The same test in an inner-product fibre

The comparison argument is applied to vector fields along a geodesic.  The
scalar calculation above is therefore useful only after it has been lifted to
an actual unit vector in the transverse fibre.  These definitions make that
lift explicit; no curvature or index-form hypothesis is hidden in it.
-/

def vectorSineTest {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : ℝ) (e : V) (t : ℝ) : V := sineTest L t • e

def vectorSineTestDeriv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : ℝ) (e : V) (t : ℝ) : V := sineTestDeriv L t • e

def vectorSineIndexForm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K L : ℝ) (e : V) : ℝ :=
  (∫ t in (0 : ℝ)..L,
      inner ℝ (vectorSineTestDeriv L e t) (vectorSineTestDeriv L e t)) -
    K * (∫ t in (0 : ℝ)..L,
      inner ℝ (vectorSineTest L e t) (vectorSineTest L e t))

lemma hasDerivAt_vectorSineTest
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : ℝ) (e : V) (t : ℝ) :
    HasDerivAt (vectorSineTest L e) (vectorSineTestDeriv L e t) t := by
  change HasDerivAt (fun s : ℝ ↦ sineTest L s • e)
    (sineTestDeriv L t • e) t
  exact (hasDerivAt_sineTest L t).smul_const e

lemma vectorSineTest_eq_zero_left
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : ℝ) (e : V) : vectorSineTest L e 0 = 0 := by
  simp [vectorSineTest, sineTest]

lemma vectorSineTest_eq_zero_right
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : ℝ) (e : V) (hL : 0 < L) : vectorSineTest L e L = 0 := by
  simp [vectorSineTest, sineTest, hL.ne']

lemma vectorSineIndexForm_eq_sineIndexForm
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K L : ℝ} {e : V} (he : ‖e‖ = 1) :
    vectorSineIndexForm K L e = sineIndexForm K L := by
  have he' : inner ℝ e e = 1 := by
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
  have hderiv (t : ℝ) :
      inner ℝ (vectorSineTestDeriv L e t) (vectorSineTestDeriv L e t) =
        sineTestDeriv L t ^ 2 := by
    change inner ℝ (sineTestDeriv L t • e) (sineTestDeriv L t • e) = _
    rw [real_inner_smul_left, real_inner_smul_right, he']
    ring
  have htest (t : ℝ) :
      inner ℝ (vectorSineTest L e t) (vectorSineTest L e t) =
        sineTest L t ^ 2 := by
    change inner ℝ (sineTest L t • e) (sineTest L t • e) = _
    rw [real_inner_smul_left, real_inner_smul_right, he']
    ring
  simp only [vectorSineIndexForm, sineIndexForm]
  rw [show (fun t : ℝ ↦
      inner ℝ (vectorSineTestDeriv L e t) (vectorSineTestDeriv L e t)) =
      (fun t ↦ sineTestDeriv L t ^ 2) by funext t; exact hderiv t]
  rw [show (fun t : ℝ ↦
      inner ℝ (vectorSineTest L e t) (vectorSineTest L e t)) =
      (fun t ↦ sineTest L t ^ 2) by funext t; exact htest t]

lemma vectorSineIndexForm_negative
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K L : ℝ} {e : V} (he : ‖e‖ = 1) (hK : 0 < K)
    (hL : Real.pi / Real.sqrt K < L) :
    vectorSineIndexForm K L e < 0 := by
  rw [vectorSineIndexForm_eq_sineIndexForm he]
  exact sineIndexForm_negative hK hL

/-! ### An explicit abstract index form

The geometric second-variation theorem will instantiate this definition with
the covariant derivative and curvature endomorphism along a geodesic.  Keeping
the integral and comparison steps here makes the sign direction explicit. -/

def indexForm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : ℝ → V →L[ℝ] V) (J DJ : ℝ → V) (L : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..L, inner ℝ (DJ t) (DJ t) ∂volume) -
    (∫ t in (0 : ℝ)..L, inner ℝ (J t) (A t (J t)) ∂volume)

def constantCurvatureOperator {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (K : ℝ) : ℝ → V →L[ℝ] V :=
  fun _ ↦ K • ContinuousLinearMap.id ℝ V

lemma indexForm_constantCurvatureOperator_vectorSine
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K L : ℝ) (e : V) :
    indexForm (constantCurvatureOperator K)
        (vectorSineTest L e) (vectorSineTestDeriv L e) L =
      vectorSineIndexForm K L e := by
  simp [indexForm, constantCurvatureOperator, vectorSineIndexForm,
    ContinuousLinearMap.smul_apply, inner_smul_right]

lemma indexForm_le_of_curvature_lower
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {A : ℝ → V →L[ℝ] V} {J DJ : ℝ → V} {K L : ℝ}
    (hL : 0 ≤ L)
    (hA : ∀ t ∈ Icc (0 : ℝ) L,
      K * inner ℝ (J t) (J t) ≤ inner ℝ (J t) (A t (J t)))
    (hJ : IntervalIntegrable
      (fun t ↦ inner ℝ (J t) (J t)) volume 0 L)
    (hAJ : IntervalIntegrable
      (fun t ↦ inner ℝ (J t) (A t (J t))) volume 0 L) :
    indexForm A J DJ L ≤
      (∫ t in (0 : ℝ)..L, inner ℝ (DJ t) (DJ t) ∂volume) -
        K * (∫ t in (0 : ℝ)..L, inner ℝ (J t) (J t) ∂volume) := by
  have hmono :
      (∫ t in (0 : ℝ)..L, K * inner ℝ (J t) (J t) ∂volume) ≤
        (∫ t in (0 : ℝ)..L, inner ℝ (J t) (A t (J t)) ∂volume) := by
    simpa only using intervalIntegral.integral_mono_on (f := fun t ↦
      K * inner ℝ (J t) (J t))
      (g := fun t ↦ inner ℝ (J t) (A t (J t)))
      (μ := volume) hL (hJ.const_mul K) hAJ hA
  have hconst :
      (∫ t in (0 : ℝ)..L, K * inner ℝ (J t) (J t) ∂volume) =
        K * (∫ t in (0 : ℝ)..L, inner ℝ (J t) (J t) ∂volume) := by
    rw [intervalIntegral.integral_const_mul]
  rw [indexForm]
  exact sub_le_sub_left (hconst ▸ hmono) _

end BonnetMyersEntry
