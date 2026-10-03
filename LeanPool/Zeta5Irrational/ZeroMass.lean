/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.Zeta5Irrational.Gaussian
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Lemma 6.2 (zero-mass logarithmic energy) for the truncated kernel

We work with explicit "atoms": a finite family of continuous curves `γ k : ℝ → ℂ`
(parametrised over `[0, 2π]`) with real weights `s k`.  The double integral of a kernel `f`
against the atoms `k, l` is `pairInt γ f k l`, and the energy is
`energy s γ f = ∑ k l, s k * s l * pairInt γ f k l`.

For the truncated kernel `Ltr a b r = (1/2) ∫_a^b (e^{-s} - e^{-s r²})/s ds` and zero total mass
`∑ s k = 0`, the energy is nonpositive (`energy_Ltr_nonpos`): this is the Gaussian
positivity argument of the paper.
-/

public section

open MeasureTheory Set Real intervalIntegral

namespace Zeta5Irrational

/-- The truncated logarithmic kernel `L_{a,b}(r)`. -/
@[expose] noncomputable def Ltr (a b r : ℝ) : ℝ :=
  (1 / 2) * ∫ s in a..b, (Real.exp (-s) - Real.exp (-s * r ^ 2)) / s

variable {ι : Type*}

/-- Double integral of a kernel against two atoms. -/
@[expose] noncomputable def pairInt (γ : ι → ℝ → ℂ) (f : ℂ → ℂ → ℝ) (k l : ι) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π, f (γ k θ) (γ l φ)

/-- The energy of the signed combination of atoms. -/
@[expose] noncomputable def energy [Fintype ι] (s : ι → ℝ) (γ : ι → ℝ → ℂ) (f : ℂ → ℂ → ℝ) : ℝ :=
  ∑ k, ∑ l, s k * s l * pairInt γ f k l

/-- Gaussian pair integral. -/
noncomputable def Gk (γ : ι → ℝ → ℂ) (t : ℝ) (k l : ι) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π, Real.exp (-t * ‖γ k θ - γ l φ‖ ^ 2)

/-- Gaussian smoothing of one atom. -/
noncomputable def gk (γ : ι → ℝ → ℂ) (t : ℝ) (k : ι) (u : ℂ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * π, Real.exp (-(2 * t) * ‖γ k θ - u‖ ^ 2)

lemma sq_sub_comm' (a b : ℝ) : (a - b) ^ 2 = (b - a) ^ 2 := by ring

/-- Integrability of a Gaussian on `ℂ`. -/
lemma integrable_gaussC {c : ℝ} (hc : 0 < c) (z : ℂ) :
    Integrable (fun u : ℂ => Real.exp (-c * ‖z - u‖ ^ 2)) := by
  have e :
    (fun u : ℂ => Real.exp (-c * ‖z - u‖ ^ 2)) =
      (fun p : ℝ × ℝ => Real.exp (-c * (p.1 - z.re) ^ 2) * Real.exp (-c * (p.2 - z.im) ^ 2)) ∘
        Complex.measurableEquivRealProd := by
    funext u
    simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply, normSq_eq,
      Complex.sub_re, Complex.sub_im, ← Real.exp_add]
    congr 1; ring
  rw [e,
    Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding,
    Measure.volume_eq_prod]
  exact (integrable_gaussian_sub hc z.re).mul_prod (integrable_gaussian_sub hc z.im)

/-- `‖γ - u‖² ≥ ‖u‖²/2 - ‖γ‖²`, in exponential form. -/
lemma exp_gauss_le {t R : ℝ} (ht : 0 ≤ t) {γ u : ℂ} (hγ : ‖γ‖ ≤ R) :
    Real.exp (-(2 * t) * ‖γ - u‖ ^ 2) ≤ Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖u‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : ‖u‖ ≤ ‖γ - u‖ + ‖γ‖ := by
    calc
      ‖u‖ = ‖γ - (γ - u)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖γ‖ + ‖γ - u‖ := (norm_sub_le _ _)
      _ = _ := add_comm _ _
  have h2 : ‖u‖ ^ 2 ≤ 2 * ‖γ - u‖ ^ 2 + 2 * ‖γ‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg u) h1
    nlinarith [sq_nonneg (‖γ - u‖ - ‖γ‖)]
  have h3 : ‖γ‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg γ]
  nlinarith

/-- Fubini between an interval integral and an integral over `ℂ`, for a continuous integrand
with a Gaussian bound in the complex variable. -/
lemma swap_interval_complex {F : ℝ → ℂ → ℝ} (hF : Continuous (Function.uncurry F)) {c C : ℝ}
    (hc : 0 < c) {a b : ℝ} (hab : a ≤ b)
    (hbound : ∀ θ ∈ Icc a b, ∀ u, |F θ u| ≤ C * Real.exp (-c * ‖u‖ ^ 2)) :
    ∫ θ in a..b, ∫ u : ℂ, F θ u = ∫ u : ℂ, ∫ θ in a..b, F θ u := by
  rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hab]
  apply integral_integral_swap
  have hg :
    Integrable (fun p : ℝ × ℂ => C * Real.exp (-c * ‖(0 : ℂ) - p.2‖ ^ 2))
      ((volume.restrict (Ioc a b)).prod volume) :=
    (integrable_const C).mul_prod (integrable_gaussC hc 0)
  refine hg.mono' hF.aestronglyMeasurable ?_
  rw [Measure.restrict_prod_eq_prod_univ]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with p hp
  simp only [Real.norm_eq_abs, zero_sub, norm_neg]
  exact hbound p.1 (Ioc_subset_Icc_self hp.1) p.2

lemma gk_nonneg (γ : ι → ℝ → ℂ) (t : ℝ) (k : ι) (u : ℂ) : 0 ≤ gk γ t k u :=
  intervalIntegral.integral_nonneg (by positivity) fun _ _ => (Real.exp_pos _).le

lemma continuous_gk {γ : ι → ℝ → ℂ} (hγ : ∀ k, Continuous (γ k)) (t : ℝ) (k : ι) :
    Continuous (gk γ t k) := by
  unfold gk
  apply continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

lemma gk_le_two_pi {γ : ι → ℝ → ℂ} (hγ : ∀ k, Continuous (γ k)) {t : ℝ} (ht : 0 ≤ t) (k : ι)
    (u : ℂ) : gk γ t k u ≤ 2 * π := by
  unfold gk
  have :=
    intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := 2 * π) (f := fun θ =>
      Real.exp (-(2 * t) * ‖γ k θ - u‖ ^ 2)) (g := fun _ => (1 : ℝ)) (by positivity)
      (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const
      (fun θ _ => by
        apply Real.exp_le_one_iff.mpr
        have : 0 ≤ ‖γ k θ - u‖ ^ 2 := by positivity
        nlinarith)
  simpa using this

lemma gk_le {γ : ι → ℝ → ℂ} (hγ : ∀ k, Continuous (γ k)) {R : ℝ} (hR : ∀ k θ, ‖γ k θ‖ ≤ R) {t : ℝ}
    (ht : 0 ≤ t) (k : ι) (u : ℂ) :
    gk γ t k u ≤ 2 * π * Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖u‖ ^ 2) := by
  unfold gk
  have :=
    intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := 2 * π) (f := fun θ =>
      Real.exp (-(2 * t) * ‖γ k θ - u‖ ^ 2)) (g := fun _ =>
      Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖u‖ ^ 2)) (by positivity)
      (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const
      (fun θ _ => exp_gauss_le ht (hR k θ))
  rw [intervalIntegral.integral_const] at this
  simp only [sub_zero, smul_eq_mul] at this
  linarith

/-- The Gaussian pair integral as an integral over `ℂ` of a product of smoothed atoms. -/
lemma Gk_eq {γ : ι → ℝ → ℂ} (hγ : ∀ k, Continuous (γ k)) {R : ℝ} (hR : ∀ k θ, ‖γ k θ‖ ≤ R) {t : ℝ}
    (ht : 0 < t) (k l : ι) : Gk γ t k l = 4 * t / π * ∫ u : ℂ, gk γ t k u * gk γ t l u := by
  have hconv :
    ∀ z w : ℂ,
      Real.exp (-t * ‖z - w‖ ^ 2) =
        4 * t / π *
          ∫ u : ℂ, Real.exp (-(2 * t) * ‖z - u‖ ^ 2) * Real.exp (-(2 * t) * ‖w - u‖ ^ 2) := by
    intro z w
    rw [gaussian_conv ht]
    field_simp
  unfold Gk
  simp_rw [hconv]
  simp_rw [intervalIntegral.integral_const_mul]
  congr 1
    -- inner swap
  have hinner :
    ∀ θ,
      ∫ φ in (0 : ℝ)..2 * π,
          ∫ u : ℂ, Real.exp (-(2 * t) * ‖γ k θ - u‖ ^ 2) * Real.exp (-(2 * t) * ‖γ l φ - u‖ ^ 2) =
        ∫ u : ℂ, Real.exp (-(2 * t) * ‖γ k θ - u‖ ^ 2) * gk γ t l u := by
    intro θ
    rw [swap_interval_complex (c := t) (C := Real.exp (2 * t * R ^ 2)) (by fun_prop) ht
        (by positivity)]
    · unfold gk
      congr 1; funext u
      rw [intervalIntegral.integral_const_mul]
    · intro φ _ u
      rw [abs_of_nonneg (by positivity)]
      calc
        Real.exp (-(2 * t) * ‖γ k θ - u‖ ^ 2) * Real.exp (-(2 * t) * ‖γ l φ - u‖ ^ 2) ≤
            1 * (Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖u‖ ^ 2)) := by
          apply mul_le_mul _ (exp_gauss_le ht.le (hR l φ)) (Real.exp_pos _).le zero_le_one
          apply Real.exp_le_one_iff.mpr
          have : 0 ≤ ‖γ k θ - u‖ ^ 2 := by positivity
          nlinarith
        _ = _ := by ring
  simp_rw [hinner]
  rw [swap_interval_complex (c := t) (C := Real.exp (2 * t * R ^ 2) * (2 * π))
      (by
        have := continuous_gk hγ t l
        fun_prop)
      ht (by positivity)]
  · unfold gk
    congr 1; funext u
    rw [intervalIntegral.integral_mul_const]
  · intro θ _ u
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (gk_nonneg γ t l u))]
    calc
      Real.exp (-(2 * t) * ‖γ k θ - u‖ ^ 2) * gk γ t l u ≤
          (Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖u‖ ^ 2)) * (2 * π) :=
        mul_le_mul (exp_gauss_le ht.le (hR k θ)) (gk_le_two_pi hγ ht.le l u) (gk_nonneg γ t l u)
          (by positivity)
      _ = _ := by ring

/-- The Gaussian energy is nonnegative. -/
lemma gaussian_energy_nonneg [Fintype ι] {s : ι → ℝ} {γ : ι → ℝ → ℂ} (hγ : ∀ k, Continuous (γ k))
    {R : ℝ} (hR : ∀ k θ, ‖γ k θ‖ ≤ R) {t : ℝ} (ht : 0 < t) :
    0 ≤ ∑ k, ∑ l, s k * s l * Gk γ t k l := by
  simp_rw [Gk_eq hγ hR ht]
  have hint : ∀ k l : ι, Integrable (fun u : ℂ => gk γ t k u * gk γ t l u) := by
    intro k l
    have hg :
      Integrable
        (fun u : ℂ =>
          (2 * π * Real.exp (2 * t * R ^ 2) * (2 * π)) * Real.exp (-t * ‖(0 : ℂ) - u‖ ^ 2)) :=
      (integrable_gaussC ht 0).const_mul _
    refine hg.mono' ((continuous_gk hγ t k).mul (continuous_gk hγ t l)).aestronglyMeasurable ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gk_nonneg _ _ _ _) (gk_nonneg _ _ _ _))]
    simp only [zero_sub, norm_neg]
    calc
      gk γ t k u * gk γ t l u ≤
          (2 * π * Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖u‖ ^ 2)) * (2 * π) :=
        mul_le_mul (gk_le hγ hR ht.le k u) (gk_le_two_pi hγ ht.le l u) (gk_nonneg _ _ _ _)
          (by positivity)
      _ = _ := by ring
  have e :
    ∑ k, ∑ l, s k * s l * (4 * t / π * ∫ u : ℂ, gk γ t k u * gk γ t l u) =
      4 * t / π * ∫ u : ℂ, (∑ k, s k * gk γ t k u) ^ 2 := by
    have :
      ∀ u : ℂ, (∑ k, s k * gk γ t k u) ^ 2 = ∑ k, ∑ l, s k * s l * (gk γ t k u * gk γ t l u) := by
      intro u
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _
        (fun k _ => integrable_finsetSum _ (fun l _ => (hint k l).const_mul _))]
    simp_rw [integral_finsetSum _ (fun l _ => (hint _ l).const_mul _),
      MeasureTheory.integral_const_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [e]
  exact mul_nonneg (by positivity) (integral_nonneg fun u => sq_nonneg _)

/-! ### The truncated kernel -/

lemma continuous_inv_max {a : ℝ} (ha : 0 < a) : Continuous fun s : ℝ => (max s a)⁻¹ :=
  (continuous_id.max continuous_const).inv₀ fun _s => (lt_max_of_lt_right ha).ne'

lemma Ltr_eq_max {a b : ℝ} (_ha : 0 < a) (hab : a ≤ b) (r : ℝ) :
    Ltr a b r = (1 / 2) * ∫ s in a..b, (Real.exp (-s) - Real.exp (-s * r ^ 2)) * (max s a)⁻¹ := by
  unfold Ltr
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hab] at hs
  simp only [max_eq_left hs.1, div_eq_mul_inv]

/-- Continuity of the Gaussian pair integral in the parameter. -/
lemma continuous_Gk {γ : ι → ℝ → ℂ} (hγ : ∀ k, Continuous (γ k)) (k l : ι) :
    Continuous fun t => Gk γ t k l := by
  unfold Gk
  apply continuous_parametric_intervalIntegral_of_continuous'
  apply continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

/-- The truncated-kernel pair integral in terms of Gaussian pair integrals. -/
lemma pairInt_Ltr {γ : ι → ℝ → ℂ} (hγ : ∀ k, Continuous (γ k)) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (k l : ι) :
    pairInt γ (fun z w => Ltr a b ‖z - w‖) k l =
      (1 / 2) * ∫ s in a..b, (Real.exp (-s) * (2 * π) ^ 2 - Gk γ s k l) / s := by
  unfold pairInt
  simp_rw [Ltr_eq_max ha hab, intervalIntegral.integral_const_mul]
  congr 1
  have hinv := continuous_inv_max ha
  have hH :
    ∀ θ,
      Continuous
        (Function.uncurry fun φ s =>
          (Real.exp (-s) - Real.exp (-s * ‖γ k θ - γ l φ‖ ^ 2)) * (max s a)⁻¹) := by
    intro θ
    have h1 :
      Continuous fun p : ℝ × ℝ => Real.exp (-p.2) - Real.exp (-p.2 * ‖γ k θ - γ l p.1‖ ^ 2) := by
      fun_prop
    exact h1.mul (hinv.comp continuous_snd)
  have h1 :
    ∀ θ,
      (∫ φ in (0 : ℝ)..2 * π,
          ∫ s in a..b, (Real.exp (-s) - Real.exp (-s * ‖γ k θ - γ l φ‖ ^ 2)) * (max s a)⁻¹) =
        ∫ s in a..b,
          ∫ φ in (0 : ℝ)..2 * π,
            (Real.exp (-s) - Real.exp (-s * ‖γ k θ - γ l φ‖ ^ 2)) * (max s a)⁻¹ := by
    intro θ
    exact
      intervalIntegral_swap_of_continuous (f := fun φ s =>
        (Real.exp (-s) - Real.exp (-s * ‖γ k θ - γ l φ‖ ^ 2)) * (max s a)⁻¹) (hH θ)
        (by positivity) hab
  simp_rw [h1]
  have hH2 :
    Continuous
      (Function.uncurry fun (p : ℝ × ℝ) φ =>
        (Real.exp (-p.2) - Real.exp (-p.2 * ‖γ k p.1 - γ l φ‖ ^ 2)) * (max p.2 a)⁻¹) := by
    have h1 :
      Continuous fun q : (ℝ × ℝ) × ℝ =>
        Real.exp (-q.1.2) - Real.exp (-q.1.2 * ‖γ k q.1.1 - γ l q.2‖ ^ 2) :=
      by fun_prop
    exact h1.mul (hinv.comp (continuous_snd.comp continuous_fst))
  rw [intervalIntegral_swap_of_continuous (f := fun θ s =>
      ∫ φ in (0 : ℝ)..2 * π, (Real.exp (-s) - Real.exp (-s * ‖γ k θ - γ l φ‖ ^ 2)) * (max s a)⁻¹)
      (by exact continuous_parametric_intervalIntegral_of_continuous' hH2 0 (2 * π))
      (by positivity) hab]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hab] at hs
  simp only
  simp_rw [intervalIntegral.integral_mul_const]
  rw [max_eq_left hs.1, div_eq_mul_inv]
  congr 1
  unfold Gk
  have hi :
    ∀ θ, IntervalIntegrable (fun φ => Real.exp (-s * ‖γ k θ - γ l φ‖ ^ 2)) volume 0 (2 * π) :=
    fun θ => by apply Continuous.intervalIntegrable; fun_prop
  simp_rw [intervalIntegral.integral_sub intervalIntegrable_const (hi _),
    intervalIntegral.integral_const]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (by
        apply Continuous.intervalIntegrable
        apply continuous_parametric_intervalIntegral_of_continuous'
        fun_prop),
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- **Lemma 6.2 for the truncated kernel**: the energy of a zero-mass combination of atoms
with respect to `L_{a,b}` is nonpositive. -/
theorem energy_Ltr_nonpos [Fintype ι] {s : ι → ℝ} {γ : ι → ℝ → ℂ} (hγ : ∀ k, Continuous (γ k))
    {R : ℝ} (hR : ∀ k θ, ‖γ k θ‖ ≤ R) (hmass : ∑ k, s k = 0) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : energy s γ (fun z w => Ltr a b ‖z - w‖) ≤ 0 := by
  unfold energy
  simp_rw [pairInt_Ltr hγ ha hab]
  have hc :
    ∀ k l : ι,
      ContinuousOn (fun t => (Real.exp (-t) * (2 * π) ^ 2 - Gk γ t k l) / t) (uIcc a b) := by
    intro k l
    rw [uIcc_of_le hab]
    apply
      ContinuousOn.div (Continuous.continuousOn (by have := continuous_Gk hγ k l; fun_prop))
        continuousOn_id
    intro t ht; exact (ha.trans_le ht.1).ne'
  have e :
    ∑ k,
        ∑ l, s k * s l * ((1 / 2) * ∫ t in a..b, (Real.exp (-t) * (2 * π) ^ 2 - Gk γ t k l) / t) =
      (1 / 2) *
        ∫ t in a..b, ∑ k, ∑ l, s k * s l * ((Real.exp (-t) * (2 * π) ^ 2 - Gk γ t k l) / t) := by
    rw [intervalIntegral.integral_finsetSum (f := fun k t =>
        ∑ l, s k * s l * ((Real.exp (-t) * (2 * π) ^ 2 - Gk γ t k l) / t))
        (fun k _ =>
          (continuousOn_finsetSum _ fun l _ =>
              continuousOn_const.mul (hc k l)).intervalIntegrable),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_finsetSum (f := fun l t =>
        s k * s l * ((Real.exp (-t) * (2 * π) ^ 2 - Gk γ t k l) / t))
        (fun l _ => (continuousOn_const.mul (hc k l)).intervalIntegrable),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [intervalIntegral.integral_const_mul]; ring
  rw [e]
  have hpt :
    ∀ t ∈ Icc a b,
      0 ≤ -(∑ k, ∑ l, s k * s l * ((Real.exp (-t) * (2 * π) ^ 2 - Gk γ t k l) / t)) := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hJ := gaussian_energy_nonneg (s := s) hγ hR ht0
    have hA : ∑ k, ∑ l, s k * s l * (Real.exp (-t) * (2 * π) ^ 2) = 0 := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, hmass, zero_mul]
    have :
      ∑ k, ∑ l, s k * s l * ((Real.exp (-t) * (2 * π) ^ 2 - Gk γ t k l) / t) =
        (∑ k, ∑ l, s k * s l * (Real.exp (-t) * (2 * π) ^ 2) - ∑ k, ∑ l, s k * s l * Gk γ t k l) /
          t := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this, hA, zero_sub, neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hJ) ht0.le
  have := intervalIntegral.integral_nonneg (μ := volume) hab hpt
  rw [intervalIntegral.integral_neg] at this
  linarith

end Zeta5Irrational
