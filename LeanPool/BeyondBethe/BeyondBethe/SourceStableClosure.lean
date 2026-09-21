/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Stable
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic

/-! # Source Stable Closure -/

open Filter MeasureTheory Metric Real Set

namespace BeyondBethe

/-!
# Closure of the stable cone

The source proof uses two limiting operations on stable polynomials: taking a
coefficient in a multiaffine variable and specializing a variable to the real
boundary.  In the source literature these facts are usually folded into the
statement that stability preservers may output the zero polynomial.

This file starts from the one-variable analytic fact needed to justify those
limits.  We prove it from the isolated-zero theorem, compactness of a circle,
and the mean-value identity for the logarithm of a nonvanishing analytic
function.  Thus no version of Hurwitz's theorem is introduced as an axiom.
-/

/-- A linear perturbation of a nonzero polynomial cannot be zero-free on a
fixed disk for every positive perturbation size if the limiting polynomial
vanishes at the center.  This is the precise one-variable Hurwitz principle
needed below. -/
theorem polynomial_linear_perturbation_has_nearby_zero
    (A B : Polynomial ℂ) (R : ℝ)
    (hA : A ≠ 0) (hR : 0 < R) (hA0 : A.eval 0 = 0) :
    ∃ t : ℝ, 0 < t ∧ ∃ z ∈ closedBall (0 : ℂ) R,
      (A + Polynomial.C (t : ℂ) * B).eval z = 0 := by
  have hAanalytic : AnalyticOnNhd ℂ (fun z : ℂ ↦ A.eval z) Set.univ := by
    exact AnalyticOnNhd.eval_polynomial A
  have hpunctured :
      ∀ᶠ z in nhdsWithin (0 : ℂ) ({0} : Set ℂ)ᶜ, A.eval z ≠ 0 := by
    rcases (hAanalytic 0 (Set.mem_univ 0)).eventually_eq_zero_or_eventually_ne_zero with
      hlocal | hlocal
    · have hzero : Set.EqOn (fun z : ℂ ↦ A.eval z) 0 Set.univ :=
        hAanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (Set.mem_univ 0) (by
            filter_upwards [hlocal] with z hz
            simpa using hz)
      exfalso
      apply hA
      apply Polynomial.zero_of_eval_zero
      intro z
      simpa using hzero (Set.mem_univ z)
    · exact hlocal
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunctured
  let r : ℝ := min (δ / 2) (R / 2)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrδ : r < δ := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hrR : r < R := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hR)
  have hsphereA : ∀ z ∈ sphere (0 : ℂ) r, A.eval z ≠ 0 := by
    intro z hz
    apply hδsub
    constructor
    · rw [mem_sphere, dist_zero_right] at hz
      rw [mem_ball, dist_zero_right, hz]
      exact hrδ
    · rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hz0
      subst z
      have : (0 : ℝ) = r := by simpa [mem_sphere] using hz
      exact hr.ne' this.symm
  have hsphere_nonempty : (sphere (0 : ℂ) r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  obtain ⟨u, hu, humin⟩ :=
    (isCompact_sphere (0 : ℂ) r).exists_isMinOn hsphere_nonempty
      (A.continuous.norm.continuousOn)
  let m : ℝ := ‖A.eval u‖
  have hm : 0 < m := by
    dsimp [m]
    exact norm_pos_iff.mpr (hsphereA u hu)
  have hm_lower : ∀ z ∈ sphere (0 : ℂ) r, m ≤ ‖A.eval z‖ := by
    intro z hz
    exact humin hz
  obtain ⟨v, hv, hvmax⟩ :=
    (isCompact_sphere (0 : ℂ) r).exists_isMaxOn hsphere_nonempty
      (B.continuous.norm.continuousOn)
  let M : ℝ := max ‖B.eval v‖ ‖B.eval 0‖
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hM_sphere : ∀ z ∈ sphere (0 : ℂ) r, ‖B.eval z‖ ≤ M := by
    intro z hz
    exact (hvmax hz).trans (le_max_left _ _)
  have hM_center : ‖B.eval 0‖ ≤ M := by
    exact le_max_right _ _
  let t : ℝ := m / (4 * (M + 1))
  have ht : 0 < t := by
    dsimp [t]
    positivity
  let F : Polynomial ℂ := A + Polynomial.C (t : ℂ) * B
  by_contra hno
  push_neg at hno
  have hFzeroFree : ∀ z ∈ closedBall (0 : ℂ) r, F.eval z ≠ 0 := by
    intro z hz
    exact hno t ht z (closedBall_subset_closedBall hrR.le hz)
  have hFanalytic : AnalyticOnNhd ℂ (fun z : ℂ ↦ F.eval z)
      (closedBall (0 : ℂ) r) := by
    exact (AnalyticOnNhd.eval_polynomial F).mono (Set.subset_univ _)
  have hmean :
      circleAverage (fun z : ℂ ↦ Real.log ‖F.eval z‖) 0 r =
        Real.log ‖F.eval 0‖ := by
    apply AnalyticOnNhd.circleAverage_log_norm_of_ne_zero
        (R := r) (c := (0 : ℂ)) (g := fun z : ℂ ↦ F.eval z)
    · simpa [abs_of_pos hr] using hFanalytic
    · simpa [abs_of_pos hr] using hFzeroFree
  have hperturb_sphere : ∀ z ∈ sphere (0 : ℂ) r,
      ‖((t : ℂ) * B.eval z)‖ < m / 2 := by
    intro z hz
    calc
      ‖((t : ℂ) * B.eval z)‖ = t * ‖B.eval z‖ := by
        simp [norm_mul, Real.norm_eq_abs, abs_of_pos ht]
      _ ≤ t * M := mul_le_mul_of_nonneg_left (hM_sphere z hz) ht.le
      _ < m / 2 := by
        dsimp [t]
        have hden : 0 < 4 * (M + 1) := by positivity
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden, div_mul_eq_mul_div]
        nlinarith
  have hF_lower : ∀ z ∈ sphere (0 : ℂ) r, m / 2 < ‖F.eval z‖ := by
    intro z hz
    have htriangle : ‖A.eval z‖ ≤
        ‖F.eval z‖ + ‖((t : ℂ) * B.eval z)‖ := by
      have heval : F.eval z = A.eval z + (t : ℂ) * B.eval z := by
        simp [F]
      rw [heval]
      simpa [add_assoc] using norm_sub_le (A.eval z + (t : ℂ) * B.eval z)
        ((t : ℂ) * B.eval z)
    linarith [hm_lower z hz, hperturb_sphere z hz]
  have hlog_lower : ∀ z ∈ sphere (0 : ℂ) r,
      Real.log (m / 2) ≤ Real.log ‖F.eval z‖ := by
    intro z hz
    exact Real.strictMonoOn_log.monotoneOn
      (half_pos hm) (norm_pos_iff.mpr (hFzeroFree z (sphere_subset_closedBall hz)))
      (hF_lower z hz).le
  have havg_lower : Real.log (m / 2) ≤
      circleAverage (fun z : ℂ ↦ Real.log ‖F.eval z‖) 0 r := by
    rw [← circleAverage_const (Real.log (m / 2)) (0 : ℂ) r]
    apply circleAverage_mono
    · exact circleIntegrable_const _ _ _
    · have hmer : MeromorphicOn (fun z : ℂ ↦ F.eval z)
          (sphere (0 : ℂ) |r|) := by
          simpa [abs_of_pos hr] using
            (hFanalytic.mono sphere_subset_closedBall).meromorphicOn
      exact hmer.circleIntegrable_log_norm
    · simpa [abs_of_pos hr] using hlog_lower
  have hF0 : F.eval 0 = (t : ℂ) * B.eval 0 := by
    simp [F, hA0]
  have hcenter_norm : ‖F.eval 0‖ < m / 2 := by
    rw [hF0]
    simp only [norm_mul]
    rw [show ‖(t : ℂ)‖ = t by simp [Real.norm_eq_abs, abs_of_pos ht]]
    calc
      t * ‖B.eval 0‖ ≤ t * M := mul_le_mul_of_nonneg_left hM_center ht.le
      _ < m / 2 := by
        dsimp [t]
        have hden : 0 < 4 * (M + 1) := by positivity
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden, div_mul_eq_mul_div]
        nlinarith
  have hlog_center : Real.log ‖F.eval 0‖ < Real.log (m / 2) := by
    exact Real.strictMonoOn_log
      (norm_pos_iff.mpr (hFzeroFree 0 (by simp [hr.le]))) (half_pos hm) hcenter_norm
  rw [hmean] at havg_lower
  exact (not_lt_of_ge havg_lower) hlog_center

/-! ## The multivariate closure lemma -/

/-- Complex-coefficient stability in the product of open upper half-planes. -/
def IsUpperHalfPlaneStable
    {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  ∀ z : σ → ℂ, (∀ i, 0 < (z i).im) → p.eval z ≠ 0

/-- Restrict a multivariate polynomial to the affine complex line `z + s v`. -/
noncomputable def affineLinePolynomial
    {σ : Type*} (p : MvPolynomial σ ℂ) (z v : σ → ℂ) : Polynomial ℂ :=
  p.eval₂ Polynomial.C (fun i ↦ Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X)

@[simp]
theorem affineLinePolynomial_eval
    {σ : Type*} (p : MvPolynomial σ ℂ) (z v : σ → ℂ) (s : ℂ) :
    (affineLinePolynomial p z v).eval s = p.eval (fun i ↦ z i + s * v i) := by
  rw [affineLinePolynomial, MvPolynomial.polynomial_eval_eval₂]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  have hring : (Polynomial.evalRingHom s).comp Polynomial.C = RingHom.id ℂ := by
    ext x
    simp
  rw [hring, MvPolynomial.eval₂_id]
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  ring

theorem exists_eval_ne_zero_of_mvPolynomial_ne_zero
    {σ : Type*} {p : MvPolynomial σ ℂ} (hp : p ≠ 0) :
    ∃ z : σ → ℂ, p.eval z ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext
  intro z
  simpa using h z

/-- The limit, along a positive real ray, of stable multivariate polynomials
is stable or identically zero.  This is the finite-dimensional form of
Hurwitz closure used in the preservation argument. -/
theorem upperHalfPlaneStableOrZero_of_positive_ray
    {σ : Type*} [Fintype σ]
    (p q : MvPolynomial σ ℂ)
    (hstable : ∀ t : ℝ, 0 < t →
      IsUpperHalfPlaneStable (p + MvPolynomial.C (t : ℂ) * q)) :
    p = 0 ∨ IsUpperHalfPlaneStable p := by
  by_cases hp : p = 0
  · exact Or.inl hp
  right
  intro z hz
  intro hpz
  obtain ⟨w, hw⟩ := exists_eval_ne_zero_of_mvPolynomial_ne_zero hp
  let v : σ → ℂ := fun i ↦ w i - z i
  let A : Polynomial ℂ := affineLinePolynomial p z v
  let B : Polynomial ℂ := affineLinePolynomial q z v
  have hA0 : A.eval 0 = 0 := by
    simp [A, v, hpz]
  have hA1 : A.eval 1 = p.eval w := by
    simp [A, v]
  have hA : A ≠ 0 := by
    intro hzero
    have := congrArg (fun P : Polynomial ℂ ↦ P.eval 1) hzero
    simp [hA1, hw] at this
  have hnear :
      {s : ℂ | ∀ i, 0 < (z i + s * v i).im} ∈ nhds (0 : ℂ) := by
    change ∀ᶠ s in nhds (0 : ℂ), ∀ i, 0 < (z i + s * v i).im
    rw [Filter.eventually_all]
    intro i
    have hcont : ContinuousAt (fun s : ℂ ↦ (z i + s * v i).im) 0 := by
      fun_prop
    exact hcont.eventually (isOpen_Ioi.mem_nhds (by simpa using hz i))
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨t, ht, s, hsball, hsroot⟩ :=
    polynomial_linear_perturbation_has_nearby_zero A B (R / 2)
      hA (half_pos hR) hA0
  have hsR : s ∈ ball (0 : ℂ) R := by
    rw [mem_closedBall, dist_zero_right] at hsball
    rw [mem_ball, dist_zero_right]
    exact hsball.trans_lt (half_lt_self hR)
  have hlineUpper : ∀ i, 0 < (z i + s * v i).im := hRsub hsR
  have hne := hstable t ht (fun i ↦ z i + s * v i) hlineUpper
  apply hne
  rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  simpa [A, B, affineLinePolynomial_eval] using hsroot

/-! ## Coefficients, boundary values, and the Lieb--Sokal contraction -/

/-- Adjoin one multiaffine variable, with fixedValue coefficient `g` and
linear coefficient `f`. -/
noncomputable def linearExtension
    {σ : Type*} (g f : MvPolynomial σ ℂ) : MvPolynomial (Option σ) ℂ :=
  MvPolynomial.rename some g +
    MvPolynomial.X none * MvPolynomial.rename some f

@[simp]
theorem linearExtension_eval
    {σ : Type*} (g f : MvPolynomial σ ℂ) (z : Option σ → ℂ) :
    (linearExtension g f).eval z =
      g.eval (z ∘ some) + z none * f.eval (z ∘ some) := by
  simp [linearExtension, MvPolynomial.eval_rename]

/-- The coefficient of a stable polynomial in a multiaffine variable is
stable or zero.  It is obtained as a large-imaginary-value limit. -/
theorem linearExtension_linearCoefficient_stableOrZero
    {σ : Type*} [Fintype σ]
    {g f : MvPolynomial σ ℂ}
    (hstable : IsUpperHalfPlaneStable (linearExtension g f)) :
    f = 0 ∨ IsUpperHalfPlaneStable f := by
  let q : MvPolynomial σ ℂ := MvPolynomial.C (-Complex.I) * g
  apply upperHalfPlaneStableOrZero_of_positive_ray f q
  intro t ht z hz
  let w : Option σ → ℂ
    | none => Complex.I / (t : ℂ)
    | some i => z i
  have hw : ∀ i, 0 < (w i).im := by
    intro i
    cases i with
    | none =>
        simp [w, Complex.div_im, ht]
    | some i => simpa [w] using hz i
  have hne := hstable w hw
  intro hzero
  have hzero' : f.eval z - (t : ℂ) * Complex.I * g.eval z = 0 := by
    simpa [q, sub_eq_add_neg, mul_assoc] using hzero
  apply hne
  have hwcomp : w ∘ some = z := by rfl
  rw [linearExtension_eval, hwcomp]
  calc
    g.eval z + w none * f.eval z =
        (Complex.I / (t : ℂ)) *
          (f.eval z - (t : ℂ) * Complex.I * g.eval z) := by
            dsimp [w]
            field_simp [ht.ne']
            have hII (x : ℂ) : Complex.I * (Complex.I * x) = -x := by
              rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
            calc
              g.eval z * (t : ℂ) + Complex.I * f.eval z =
                  Complex.I * f.eval z + g.eval z * (t : ℂ) := by ring
              _ = Complex.I * f.eval z -
                  Complex.I * (Complex.I * (g.eval z * (t : ℂ))) := by
                    rw [hII]
                    ring
              _ = Complex.I *
                  (f.eval z - g.eval z * Complex.I * (t : ℂ)) := by ring
    _ = 0 := by rw [hzero']; ring

/-- Substitution of a real-boundary value preserves stability, with the zero
polynomial allowed.  Here the boundary value is zero; translations give the
usual general statement. -/
theorem linearExtension_constantCoefficient_stableOrZero
    {σ : Type*} [Fintype σ]
    {g f : MvPolynomial σ ℂ}
    (hstable : IsUpperHalfPlaneStable (linearExtension g f)) :
    g = 0 ∨ IsUpperHalfPlaneStable g := by
  let q : MvPolynomial σ ℂ := MvPolynomial.C Complex.I * f
  apply upperHalfPlaneStableOrZero_of_positive_ray g q
  intro t ht z hz
  let w : Option σ → ℂ
    | none => Complex.I * (t : ℂ)
    | some i => z i
  have hw : ∀ i, 0 < (w i).im := by
    intro i
    cases i with
    | none => simpa [w] using ht
    | some i => simpa [w] using hz i
  have hne := hstable w hw
  have hwcomp : w ∘ some = z := by rfl
  intro hzero
  apply hne
  rw [linearExtension_eval, hwcomp]
  have hzero' : g.eval z + (t : ℂ) * Complex.I * f.eval z = 0 := by
    simpa [q, mul_assoc] using hzero
  linear_combination hzero'

/-- Ratio characterization for a polynomial affine in one new variable. -/
theorem linearExtension_stable_iff_ratio
    {σ : Type*} {g f : MvPolynomial σ ℂ}
    (hf : IsUpperHalfPlaneStable f) :
    IsUpperHalfPlaneStable (linearExtension g f) ↔
      ∀ z : σ → ℂ, (∀ i, 0 < (z i).im) →
        0 ≤ (g.eval z / f.eval z).im := by
  constructor
  · intro h z hz
    have hfz := hf z hz
    by_contra hneg
    have him : 0 < (-g.eval z / f.eval z).im := by
      rw [neg_div]
      simpa using (lt_of_not_ge hneg)
    let w : Option σ → ℂ
      | none => -g.eval z / f.eval z
      | some i => z i
    have hw : ∀ i, 0 < (w i).im := by
      intro i
      cases i with
      | none => exact him
      | some i => simpa [w] using hz i
    have hne := h w hw
    apply hne
    have hwcomp : w ∘ some = z := by rfl
    rw [linearExtension_eval, hwcomp]
    dsimp [w]
    field_simp [hfz]
    ring
  · intro h z hz
    have hbase : ∀ i, 0 < ((z ∘ some) i).im := fun i ↦ hz (some i)
    have hfz := hf (z ∘ some) hbase
    intro hzero
    have hy : z none = -g.eval (z ∘ some) / f.eval (z ∘ some) := by
      apply (eq_div_iff hfz).2
      have := hzero
      simp only [linearExtension_eval] at this
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_comm] using this
    have him := h (z ∘ some) hbase
    have hyim : (z none).im ≤ 0 := by
      rw [hy, neg_div]
      simpa using neg_nonpos.mpr him
    exact (not_lt_of_ge hyim) (hz none)

/-- The elementary inverse-shift identity in the Lieb--Sokal proof. -/
theorem inverseShiftExtension_stable
    {σ : Type*} [Fintype σ]
    {f₀ f₁ : MvPolynomial σ ℂ}
    (hf : IsUpperHalfPlaneStable (linearExtension f₀ f₁)) :
    IsUpperHalfPlaneStable
      (linearExtension (-MvPolynomial.rename some f₁)
        (linearExtension f₀ f₁)) := by
  intro z hz
  let y : ℂ := z none
  let u : Option σ → ℂ := z ∘ some
  let shifted : Option σ → ℂ
    | none => u none - 1 / y
    | some i => u (some i)
  have hy : 0 < y.im := by simpa [y] using hz none
  have hyne : y ≠ 0 := by
    intro h
    rw [h] at hy
    simp at hy
  have him_inv : (1 / y).im < 0 := by
    rw [one_div, Complex.inv_im]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hy) (Complex.normSq_pos.mpr hyne)
  have hshifted : ∀ i, 0 < (shifted i).im := by
    intro i
    cases i with
    | none =>
        dsimp [shifted, u]
        have hu := hz (some none)
        linarith
    | some i => simpa [shifted, u] using hz (some (some i))
  have hne := hf shifted hshifted
  intro hzero
  apply hne
  have hzero' :
      -f₁.eval (u ∘ some) +
          y * (f₀.eval (u ∘ some) + u none * f₁.eval (u ∘ some)) = 0 := by
    simpa [linearExtension_eval, MvPolynomial.eval_rename, y, u] using hzero
  rw [linearExtension_eval]
  have hshiftcomp : shifted ∘ some = u ∘ some := by rfl
  rw [hshiftcomp]
  change f₀.eval (u ∘ some) +
      (u none - 1 / y) * f₁.eval (u ∘ some) = 0
  calc
    f₀.eval (u ∘ some) +
        (u none - 1 / y) * f₁.eval (u ∘ some) =
      (1 / y) *
        (-f₁.eval (u ∘ some) +
          y * (f₀.eval (u ∘ some) + u none * f₁.eval (u ∘ some))) := by
            field_simp [hyne]
            ring
    _ = 0 := by rw [hzero']; ring

/-- Coordinate form of the Lieb--Sokal lemma.  The proof uses only the ratio
characterization above, the inverse shift, and boundary closure. -/
theorem liebSokal_linear_contraction
    {σ : Type*} [Fintype σ]
    (g : MvPolynomial (Option σ) ℂ) (f₀ f₁ : MvPolynomial σ ℂ)
    (hstable : IsUpperHalfPlaneStable
      (linearExtension g (linearExtension f₀ f₁))) :
    g - MvPolynomial.rename some f₁ = 0 ∨
      IsUpperHalfPlaneStable (g - MvPolynomial.rename some f₁) := by
  have hfOr := linearExtension_linearCoefficient_stableOrZero hstable
  rcases hfOr with hfzero | hf
  · have hf₁zero : f₁ = 0 := by
      apply MvPolynomial.funext
      intro z
      let w₀ : Option σ → ℂ
        | none => 0
        | some i => z i
      let w₁ : Option σ → ℂ
        | none => 1
        | some i => z i
      have h₀ := congrArg (fun P : MvPolynomial (Option σ) ℂ ↦ P.eval w₀) hfzero
      have h₁ := congrArg (fun P : MvPolynomial (Option σ) ℂ ↦ P.eval w₁) hfzero
      have hw₀ : w₀ ∘ some = z := by rfl
      have hw₁ : w₁ ∘ some = z := by rfl
      simp [linearExtension_eval, w₀, w₁, hw₀, hw₁] at h₀ h₁
      change f₁.eval z = 0
      linear_combination h₁ - h₀
    subst f₁
    simpa using linearExtension_constantCoefficient_stableOrZero hstable
  · have hinverse := inverseShiftExtension_stable hf
    have hratio₁ := (linearExtension_stable_iff_ratio hf).1 hstable
    have hratio₂ := (linearExtension_stable_iff_ratio hf).1 hinverse
    have hcombined : IsUpperHalfPlaneStable
        (linearExtension (g - MvPolynomial.rename some f₁)
          (linearExtension f₀ f₁)) := by
      apply (linearExtension_stable_iff_ratio hf).2
      intro z hz
      have h₁ := hratio₁ z hz
      have h₂ := hratio₂ z hz
      simp only [MvPolynomial.eval_neg, neg_div] at h₂
      rw [MvPolynomial.eval_sub, sub_eq_add_neg, add_div, neg_div]
      simpa only [Complex.add_im, Complex.neg_im] using add_nonneg h₁ h₂
    exact linearExtension_constantCoefficient_stableOrZero hcombined

/-! ## Specializing an arbitrary multiaffine coordinate -/

def IsComplexMultiaffine
    {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  ∀ i, p.degreeOf i ≤ 1

theorem IsUpperHalfPlaneStable.rename
    {σ τ : Type*} {p : MvPolynomial σ ℂ}
    (hp : IsUpperHalfPlaneStable p) (f : σ → τ) :
    IsUpperHalfPlaneStable (MvPolynomial.rename f p) := by
  intro z hz
  rw [MvPolynomial.eval_rename]
  exact hp (z ∘ f) (fun i ↦ hz (f i))

noncomputable def optionConstantCoefficient
    {σ : Type*} (p : MvPolynomial (Option σ) ℂ) : MvPolynomial σ ℂ :=
  (MvPolynomial.optionEquivLeft ℂ σ p).coeff 0

noncomputable def optionLinearCoefficient
    {σ : Type*} (p : MvPolynomial (Option σ) ℂ) : MvPolynomial σ ℂ :=
  (MvPolynomial.optionEquivLeft ℂ σ p).coeff 1

theorem optionEquivLeft_rename_some
    {σ : Type*} (p : MvPolynomial σ ℂ) :
    MvPolynomial.optionEquivLeft ℂ σ (MvPolynomial.rename some p) =
      Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

theorem option_eq_linearExtension
    {σ : Type*} (p : MvPolynomial (Option σ) ℂ)
    (hdegree : p.degreeOf none ≤ 1) :
    p = linearExtension (optionConstantCoefficient p)
      (optionLinearCoefficient p) := by
  apply (MvPolynomial.optionEquivLeft ℂ σ).injective
  have hnat : (MvPolynomial.optionEquivLeft ℂ σ p).natDegree ≤ 1 := by
    simpa [MvPolynomial.natDegree_optionEquivLeft] using hdegree
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hnat]
  simp only [linearExtension, map_add, map_mul,
    MvPolynomial.optionEquivLeft_X_none, optionEquivLeft_rename_some]
  dsimp [optionConstantCoefficient, optionLinearCoefficient]
  ring

theorem linearExtension_eq_zero_iff
    {σ : Type*} {g f : MvPolynomial σ ℂ} :
    linearExtension g f = 0 ↔ g = 0 ∧ f = 0 := by
  constructor
  · intro h
    have h' := congrArg (MvPolynomial.optionEquivLeft ℂ σ) h
    simp only [linearExtension, map_add, map_mul,
      MvPolynomial.optionEquivLeft_X_none, optionEquivLeft_rename_some, map_zero] at h'
    constructor
    · have := congrArg (fun P : Polynomial (MvPolynomial σ ℂ) ↦ P.coeff 0) h'
      simpa using this
    · have := congrArg (fun P : Polynomial (MvPolynomial σ ℂ) ↦ P.coeff 1) h'
      simpa using this
  · rintro ⟨rfl, rfl⟩
    simp [linearExtension]
theorem linearExtension_multiaffine
    {σ : Type*} {g f : MvPolynomial σ ℂ}
    (hg : IsComplexMultiaffine g) (hf : IsComplexMultiaffine f) :
    IsComplexMultiaffine (linearExtension g f) := by
  classical
  intro j
  cases j with
  | none =>
      rw [← MvPolynomial.natDegree_optionEquivLeft]
      simp only [linearExtension, map_add, map_mul,
        MvPolynomial.optionEquivLeft_X_none, optionEquivLeft_rename_some]
      rw [show Polynomial.C g + Polynomial.X * Polynomial.C f =
          Polynomial.C f * Polynomial.X + Polynomial.C g by ring]
      exact Polynomial.natDegree_linear_le (a := f) (b := g)
  | some i =>
      apply le_trans (MvPolynomial.degreeOf_add_le (some i) _ _)
      apply max_le
      · simpa using
          (MvPolynomial.degreeOf_rename_of_injective (Option.some_injective σ) i).trans_le (hg i)
      · apply le_trans (MvPolynomial.degreeOf_mul_le (some i) _ _)
        have hx : (MvPolynomial.X none : MvPolynomial (Option σ) ℂ).degreeOf (some i) = 0 :=
          MvPolynomial.degreeOf_X_of_ne (by simp)
        rw [hx, zero_add]
        simpa using
          (MvPolynomial.degreeOf_rename_of_injective (Option.some_injective σ) i).trans_le (hf i)

/-- Specializing the adjoined variable to a real number preserves stability,
again allowing the zero polynomial. -/
theorem linearExtension_specialize_real_stableOrZero
    {σ : Type*} [Fintype σ]
    {g f : MvPolynomial σ ℂ} (c : ℝ)
    (hstable : IsUpperHalfPlaneStable (linearExtension g f)) :
    g + MvPolynomial.C (c : ℂ) * f = 0 ∨
      IsUpperHalfPlaneStable (g + MvPolynomial.C (c : ℂ) * f) := by
  have hshift : IsUpperHalfPlaneStable
      (linearExtension (g + MvPolynomial.C (c : ℂ) * f) f) := by
    intro z hz
    let w : Option σ → ℂ
      | none => z none + (c : ℂ)
      | some i => z (some i)
    have hw : ∀ i, 0 < (w i).im := by
      intro i
      cases i with
      | none => simpa [w] using hz none
      | some i => simpa [w] using hz (some i)
    have hne := hstable w hw
    have hwcomp : w ∘ some = z ∘ some := by rfl
    intro hzero
    apply hne
    rw [linearExtension_eval, hwcomp]
    have hzero' := hzero
    rw [linearExtension_eval] at hzero'
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C] at hzero'
    dsimp [w]
    linear_combination hzero'
  exact linearExtension_constantCoefficient_stableOrZero hshift

/-- Coordinate specialization in a polynomial whose selected variable has
degree at most one. -/
theorem option_specialize_real_stableOrZero
    {σ : Type*} [Fintype σ]
    (p : MvPolynomial (Option σ) ℂ) (c : ℝ)
    (hdegree : p.degreeOf none ≤ 1)
    (hstable : IsUpperHalfPlaneStable p) :
    optionConstantCoefficient p +
        MvPolynomial.C (c : ℂ) * optionLinearCoefficient p = 0 ∨
      IsUpperHalfPlaneStable
        (optionConstantCoefficient p +
          MvPolynomial.C (c : ℂ) * optionLinearCoefficient p) := by
  rw [option_eq_linearExtension p hdegree] at hstable
  exact linearExtension_specialize_real_stableOrZero c hstable

theorem degreeOf_optionConstantCoefficient_le
    {σ : Type*} (p : MvPolynomial (Option σ) ℂ) (i : σ) :
    (optionConstantCoefficient p).degreeOf i ≤ p.degreeOf (some i) := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  have hm' : m.optionElim 0 ∈ p.support := by
    exact (MvPolynomial.mem_support_coeff_optionEquivLeft (R := ℂ)).mp hm
  simpa using MvPolynomial.monomial_le_degreeOf (some i) hm'

theorem degreeOf_optionLinearCoefficient_le
    {σ : Type*} (p : MvPolynomial (Option σ) ℂ) (i : σ) :
    (optionLinearCoefficient p).degreeOf i ≤ p.degreeOf (some i) := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  have hm' : m.optionElim 1 ∈ p.support := by
    exact (MvPolynomial.mem_support_coeff_optionEquivLeft (R := ℂ)).mp hm
  simpa using MvPolynomial.monomial_le_degreeOf (some i) hm'

theorem option_specialization_multiaffine
    {σ : Type*} (p : MvPolynomial (Option σ) ℂ) (c : ℝ)
    (hp : IsComplexMultiaffine p) :
    IsComplexMultiaffine
      (optionConstantCoefficient p +
        MvPolynomial.C (c : ℂ) * optionLinearCoefficient p) := by
  intro i
  apply le_trans (MvPolynomial.degreeOf_add_le i _ _)
  apply max_le
  · exact (degreeOf_optionConstantCoefficient_le p i).trans (hp (some i))
  · exact (MvPolynomial.degreeOf_C_mul_le _ i _).trans
      ((degreeOf_optionLinearCoefficient_le p i).trans (hp (some i)))

noncomputable def coordinateReindex
    {σ : Type*} (p : MvPolynomial σ ℂ) (i : σ) :
    MvPolynomial (Option {j : σ // j ≠ i}) ℂ := by
  classical
  exact MvPolynomial.rename (Equiv.optionSubtypeNe i).symm p

noncomputable def coordinateSpecialization
    {σ : Type*} (p : MvPolynomial σ ℂ) (i : σ) (c : ℝ) :
    MvPolynomial {j : σ // j ≠ i} ℂ := by
  classical
  exact optionConstantCoefficient (coordinateReindex p i) +
    MvPolynomial.C (c : ℂ) * optionLinearCoefficient (coordinateReindex p i)

theorem coordinateReindex_stable
    {σ : Type*} {p : MvPolynomial σ ℂ} (i : σ)
    (hp : IsUpperHalfPlaneStable p) :
    IsUpperHalfPlaneStable (coordinateReindex p i) := by
  classical
  simpa [coordinateReindex] using hp.rename (Equiv.optionSubtypeNe i).symm

theorem coordinateReindex_multiaffine
    {σ : Type*} {p : MvPolynomial σ ℂ} (i : σ)
    (hp : IsComplexMultiaffine p) :
    IsComplexMultiaffine (coordinateReindex p i) := by
  classical
  intro j
  let e := Equiv.optionSubtypeNe i
  have hdegree := MvPolynomial.degreeOf_rename_of_injective e.symm.injective (e j)
    (p := p)
  have hp' := hp (e j)
  change MvPolynomial.degreeOf j (MvPolynomial.rename e.symm p) ≤ 1
  convert hdegree.trans_le hp' using 1
  simp

theorem coordinateSpecialization_stableOrZero
    {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℂ) (i : σ) (c : ℝ)
    (hmulti : IsComplexMultiaffine p)
    (hstable : IsUpperHalfPlaneStable p) :
    coordinateSpecialization p i c = 0 ∨
      IsUpperHalfPlaneStable (coordinateSpecialization p i c) := by
  classical
  let p' := coordinateReindex p i
  have hdegree : p'.degreeOf none ≤ 1 :=
    coordinateReindex_multiaffine i hmulti none
  simpa [coordinateSpecialization, p'] using
    option_specialize_real_stableOrZero p' c hdegree
      (coordinateReindex_stable i hstable)

theorem coordinateSpecialization_multiaffine
    {σ : Type*} (p : MvPolynomial σ ℂ) (i : σ) (c : ℝ)
    (hp : IsComplexMultiaffine p) :
    IsComplexMultiaffine (coordinateSpecialization p i c) := by
  classical
  exact option_specialization_multiaffine (coordinateReindex p i) c
    (coordinateReindex_multiaffine i hp)

end BeyondBethe
