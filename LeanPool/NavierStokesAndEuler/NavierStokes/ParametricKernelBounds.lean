/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatKernelBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.RCLike.Basic

/-!
# Joint parameter derivatives of the normalized flat kernel

The estimates use actual total Fréchet derivatives and finite profile-jet
bounds. The parameter space need not be finite-dimensional for these bounds.
-/

@[expose] public section


noncomputable section

open Set
open scoped ContDiff BigOperators

namespace NavierStokes.ParametricKernelBounds

open FlatKernelBounds

private theorem nat_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))

/-- Combine finitely many polynomial bounds, allowing distinct initial constants and degrees. -/
theorem finite_polynomial_majorant {X : Type*} [NormedAddCommGroup X]
    (f : ℕ → X → ℝ → ℝ) (R : ℝ) (n : ℕ) :
    (∀ k ≤ n, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ y t,
      ‖y‖ ≤ R → 0 ≤ t → f k y t ≤ C * (1 + t) ^ N) →
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ k ≤ n, ∀ y t,
      ‖y‖ ≤ R → 0 ≤ t → f k y t ≤ C * (1 + t) ^ N := by
  induction n with
  | zero =>
      intro h
      obtain ⟨C, N, hC, hb⟩ := h 0 le_rfl
      refine ⟨C, N, hC, ?_⟩
      intro k hk y t hy ht
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact hb y t hy ht
  | succ n ih =>
      intro h
      obtain ⟨C, N, hC, hb⟩ := ih (fun k hk => h k (hk.trans (Nat.le_succ n)))
      obtain ⟨D, M, hD, hd⟩ := h (n + 1) le_rfl
      refine ⟨C + D, N + M, add_nonneg hC hD, ?_⟩
      intro k hk y t hy ht
      have ht1 : 1 ≤ 1 + t := by linarith
      have hp0 : 0 ≤ (1 + t) ^ (N + M) := pow_nonneg (by linarith) _
      rcases lt_or_eq_of_le hk with hlt | rfl
      · calc
          f k y t ≤ C * (1 + t) ^ N := hb k (Nat.le_of_lt_succ hlt) y t hy ht
          _ ≤ C * (1 + t) ^ (N + M) := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ ht1 (Nat.le_add_right N M)) hC
          _ ≤ (C + D) * (1 + t) ^ (N + M) := mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right hD) hp0
      · calc
          f (n + 1) y t ≤ D * (1 + t) ^ M := hd y t hy ht
          _ ≤ D * (1 + t) ^ (N + M) := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ ht1 (Nat.le_add_left M N)) hD
          _ ≤ (C + D) * (1 + t) ^ (N + M) := mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left hC) hp0

section General

variable {X F G : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_pair_le {f : X → F} {g : X → G}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ n (fun y => (f y, g y)) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n g x‖ := by
  have hp := hf.prodMk hg
  have hfst := (ContinuousLinearMap.fst ℝ F G).iteratedFDeriv_comp_left
    (hp.contDiffAt (x := x)) (nat_le_smooth n)
  have hsnd := (ContinuousLinearMap.snd ℝ F G).iteratedFDeriv_comp_left
    (hp.contDiffAt (x := x)) (nat_le_smooth n)
  have heq : iteratedFDeriv ℝ n (fun y => (f y, g y)) x =
      (iteratedFDeriv ℝ n f x).prod (iteratedFDeriv ℝ n g x) := by
    apply ContinuousMultilinearMap.ext
    intro m
    apply Prod.ext
    · exact (congrArg (fun A => A m) hfst).symm
    · exact (congrArg (fun A => A m) hsnd).symm
  rw [heq, ContinuousMultilinearMap.opNorm_prod]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

theorem norm_iteratedFDeriv_linear_le (L : X →L[ℝ] F) (n : ℕ) (hn : 1 ≤ n) (x : X) :
    ‖iteratedFDeriv ℝ n L x‖ ≤ ‖L‖ := by
  cases n with
  | zero => simp at hn
  | succ n =>
      rw [← norm_iteratedFDeriv_fderiv]
      rw [show fderiv ℝ (L : X → F) = fun _ => L by
        funext y
        exact L.fderiv]
      cases n with
      | zero => simp
      | succ n => simp [iteratedFDeriv_succ_const]

theorem norm_iteratedFDeriv_mul_le_of_bounds {f g : X → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : X)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hfb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * C * D := by
  apply (norm_iteratedFDeriv_mul_le hf hg x (nat_le_smooth n)).trans
  calc
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C * D := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hfb i hin) (by positivity))
          (hgb (n - i) (Nat.sub_le n i)) (norm_nonneg _)
          (mul_nonneg (by positivity) hC)
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * C * D := by
        simp only [Finset.sum_mul]

end General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_scalar_snd_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (y : E × ℝ) :
    ‖iteratedFDeriv ℝ n (fun z : E × ℝ => f z.2) y‖ ≤
      |iteratedDeriv n f y.2| := by
  have heq := (ContinuousLinearMap.snd ℝ E ℝ).iteratedFDeriv_comp_right
    hf y (nat_le_smooth n)
  change ‖iteratedFDeriv ℝ n (f ∘ (ContinuousLinearMap.snd ℝ E ℝ)) y‖ ≤ _
  rw [heq]
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq
    (by simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs])

/-- Coordinate expr, given by `.mul .x .invRoot`. -/
def coordinateExpr : Expr := .mul .x .invRoot

theorem coordinate_eq_expr (x t : ℝ) :
    coordinate x t = coordinateExpr.eval (fun _ => 0) x t := by
  simp [coordinateExpr, Expr.eval, coordinate, div_eq_mul_inv]

theorem coordinate_contDiff {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (fun x => coordinate x t) := by
  simp_rw [coordinate_eq_expr]
  exact coordinateExpr.contDiff_eval contDiff_const ht

theorem coordinate_derivative_bound (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x t : ℝ, |x| ≤ R → 0 ≤ t →
      |iteratedDeriv n (fun y => coordinate y t) x| ≤ C * (1 + t) ^ N := by
  obtain ⟨C, N, hC, hbound⟩ :=
    ((Expr.diff^[n]) coordinateExpr).polynomialBound (b := fun _ => 0) contDiff_const hR
  refine ⟨C, N, hC, ?_⟩
  intro x t hx ht
  simp_rw [coordinate_eq_expr]
  rw [coordinateExpr.iteratedDeriv_eval contDiff_const ht n]
  exact hbound x t hx ht

/-- Transform, given by `(y.1, coordinate y.2 t)`. -/
def transform (t : ℝ) (y : E × ℝ) : E × ℝ := (y.1, coordinate y.2 t)

theorem transform_contDiff {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (transform (E := E) t) :=
  contDiff_fst.prodMk ((coordinate_contDiff ht).comp contDiff_snd)

omit [NormedSpace ℝ E] in
theorem norm_transform_le {t : ℝ} (ht : 0 ≤ t) (y : E × ℝ) :
    ‖transform t y‖ ≤ ‖y‖ := by
  simp only [transform, Prod.norm_def, Real.norm_eq_abs]
  exact max_le_max_left _ (abs_coordinate_le ht)

theorem norm_iteratedFDeriv_transform_le (n : ℕ) (hn : 1 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) (y : E × ℝ) :
    ‖iteratedFDeriv ℝ n (transform t) y‖ ≤
      1 + |iteratedDeriv n (fun x => coordinate x t) y.2| := by
  apply (norm_iteratedFDeriv_pair_le contDiff_fst
    ((coordinate_contDiff ht).comp contDiff_snd) n y).trans
  apply add_le_add
  · exact (norm_iteratedFDeriv_linear_le (ContinuousLinearMap.fst ℝ E ℝ) n hn y).trans
      (ContinuousLinearMap.norm_fst_le ℝ E ℝ)
  · exact norm_iteratedFDeriv_scalar_snd_le (coordinate_contDiff ht) n y

theorem transform_derivative_bound (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ y : E × ℝ, ∀ t : ℝ,
      ‖y‖ ≤ R → 0 ≤ t →
      ‖iteratedFDeriv ℝ n (transform t) y‖ ≤ C * (1 + t) ^ N := by
  rcases n.eq_zero_or_pos with rfl | hn
  · refine ⟨R, 0, hR, ?_⟩
    intro y t hy ht
    simpa using (norm_transform_le ht y).trans hy
  · obtain ⟨C, N, hC, hbound⟩ := coordinate_derivative_bound n hR
    refine ⟨C + 1, N, by positivity, ?_⟩
    intro y t hy ht
    have hcoord : |y.2| ≤ R := by
      simpa only [Real.norm_eq_abs] using (norm_snd_le y).trans hy
    have hpow : 1 ≤ (1 + t) ^ N := by
      simpa using pow_le_pow_right₀ (by linarith : 1 ≤ 1 + t) (Nat.zero_le N)
    calc
      ‖iteratedFDeriv ℝ n (transform t) y‖ ≤
        1 + |iteratedDeriv n (fun x => coordinate x t) y.2| :=
          norm_iteratedFDeriv_transform_le n hn ht y
      _ ≤ 1 + C * (1 + t) ^ N := add_le_add_right (hbound y.2 t hcoord ht) 1
      _ ≤ (C + 1) * (1 + t) ^ N := by nlinarith

/-- Amplitude, given by `denominator x t ^ j / denominator x t ^ 3`. -/
def amplitude (j : ℕ) (x t : ℝ) : ℝ := denominator x t ^ j / denominator x t ^ 3

theorem amplitude_contDiff (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (fun x => amplitude j x t) := by
  have heq : (fun x => amplitude j x t) = fun x => (kernelExpr j).eval (fun _ => 1) x t := by
    funext x
    simp [amplitude, kernelExpr, Expr.eval, div_eq_mul_inv, inv_pow]
  rw [heq]
  exact (kernelExpr j).contDiff_eval contDiff_const ht

theorem amplitude_derivative_bound (j n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x t : ℝ, |x| ≤ R → 0 ≤ t →
      |iteratedDeriv n (fun y => amplitude j y t) x| ≤ C * (1 + t) ^ N := by
  simpa only [amplitude, mul_one] using
    (unweighted_iteratedDeriv_bound (b := fun _ => 1) contDiff_const j n hR)

theorem amplitude_joint_derivative_bound (j n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ y : E × ℝ, ∀ t : ℝ,
      ‖y‖ ≤ R → 0 ≤ t →
      ‖iteratedFDeriv ℝ n (fun z : E × ℝ => amplitude j z.2 t) y‖ ≤
        C * (1 + t) ^ N := by
  obtain ⟨C, N, hC, hbound⟩ := amplitude_derivative_bound j n hR
  refine ⟨C, N, hC, ?_⟩
  intro y t hy ht
  have hcoord : |y.2| ≤ R := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le y).trans hy
  exact (norm_iteratedFDeriv_scalar_snd_le (amplitude_contDiff j ht) n y).trans
    (hbound y.2 t hcoord ht)

/-- Raw kernel, given by `amplitude j y.2 t * b (transform t y)`. -/
def rawKernel (j : ℕ) (b : E × ℝ → ℝ) (y : E × ℝ) (t : ℝ) : ℝ :=
  amplitude j y.2 t * b (transform t y)

/-- Kernel, given by `(1 / 2 : ℝ) * Real.exp (-c * t) * (denominator y.2 t ^ j / denominator y.2
t ^ 3) * b (y.1, coordinate y.2 t)`. -/
def kernel (c : ℝ) (j : ℕ) (b : E × ℝ → ℝ) (y : E × ℝ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp (-c * t) *
    (denominator y.2 t ^ j / denominator y.2 t ^ 3) *
    b (y.1, coordinate y.2 t)

theorem rawKernel_contDiff (j : ℕ) {b : E × ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (fun y => rawKernel j b y t) :=
  ((amplitude_contDiff j ht).comp contDiff_snd).mul (hb.comp (transform_contDiff ht))

/-- The profile composed with the coordinate transform has polynomially bounded
total derivatives, using only profile jets through the requested order. -/
theorem profile_comp_derivative_bound {b : E × ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R) {B : ℝ} (hB : 0 ≤ B)
    (hjets : ∀ k ≤ n, ∀ z : E × ℝ, ‖z‖ ≤ R → ‖iteratedFDeriv ℝ k b z‖ ≤ B) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ y : E × ℝ, ∀ t : ℝ,
      ‖y‖ ≤ R → 0 ≤ t →
      ‖iteratedFDeriv ℝ n (b ∘ transform t) y‖ ≤ C * (1 + t) ^ N := by
  obtain ⟨A, M, hA, htransform⟩ := finite_polynomial_majorant
    (fun k (y : E × ℝ) t => ‖iteratedFDeriv ℝ k (transform t) y‖) R n
    (fun k _ => transform_derivative_bound k hR)
  refine ⟨(n.factorial : ℝ) * B * (1 + A) ^ n, M * n, by positivity, ?_⟩
  intro y t hy ht
  have ht1 : 1 ≤ 1 + t := by linarith
  have hpow : 1 ≤ (1 + t) ^ M := by
    simpa using pow_le_pow_right₀ ht1 (Nat.zero_le M)
  have hD : 1 ≤ (1 + A) * (1 + t) ^ M := by nlinarith
  have hcomp := norm_iteratedFDeriv_comp_le hb (transform_contDiff ht)
    (nat_le_smooth n) y
    (fun k hk => hjets k hk (transform t y) ((norm_transform_le ht y).trans hy))
    (D := (1 + A) * (1 + t) ^ M) (fun k hk1 hkn => ?_)
  · calc
      ‖iteratedFDeriv ℝ n (b ∘ transform t) y‖ ≤
        (n.factorial : ℝ) * B * ((1 + A) * (1 + t) ^ M) ^ n := hcomp
      _ = ((n.factorial : ℝ) * B * (1 + A) ^ n) * (1 + t) ^ (M * n) := by
        rw [mul_pow, ← pow_mul]
        ring
  · calc
      ‖iteratedFDeriv ℝ k (transform t) y‖ ≤ A * (1 + t) ^ M :=
        htransform k hkn y t hy ht
      _ ≤ (1 + A) * (1 + t) ^ M := by nlinarith
      _ ≤ ((1 + A) * (1 + t) ^ M) ^ k := by
        simpa only [pow_one] using pow_le_pow_right₀ hD hk1

theorem rawKernel_iteratedFDeriv_bound {b : E × ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (j n : ℕ) {R : ℝ} (hR : 0 ≤ R) {B : ℝ} (hB : 0 ≤ B)
    (hjets : ∀ k ≤ n, ∀ z : E × ℝ, ‖z‖ ≤ R → ‖iteratedFDeriv ℝ k b z‖ ≤ B) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ y : E × ℝ, ∀ t : ℝ,
      ‖y‖ ≤ R → 0 ≤ t →
      ‖iteratedFDeriv ℝ n (fun z => rawKernel j b z t) y‖ ≤ C * (1 + t) ^ N := by
  obtain ⟨A, M, hA, hamp⟩ := finite_polynomial_majorant
    (fun k (y : E × ℝ) t =>
      ‖iteratedFDeriv ℝ k (fun z : E × ℝ => amplitude j z.2 t) y‖) R n
    (fun k _ => amplitude_joint_derivative_bound j k hR)
  obtain ⟨D, N, hD, hprofile⟩ := finite_polynomial_majorant
    (fun k (y : E × ℝ) t => ‖iteratedFDeriv ℝ k (b ∘ transform t) y‖) R n
    (fun k hk => profile_comp_derivative_bound hb k hR hB
      (fun i hi z hz => hjets i (hi.trans hk) z hz))
  refine ⟨(∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * A * D,
    M + N, by positivity, ?_⟩
  intro y t hy ht
  have hbnd := norm_iteratedFDeriv_mul_le_of_bounds
    ((amplitude_contDiff j ht).comp contDiff_snd) (hb.comp (transform_contDiff ht)) n y
    (C := A * (1 + t) ^ M) (D := D * (1 + t) ^ N) (by positivity) (by positivity)
    (fun i hi => hamp i hi y t hy ht) (fun i hi => hprofile i hi y t hy ht)
  calc
    ‖iteratedFDeriv ℝ n (fun z => rawKernel j b z t) y‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) *
        (A * (1 + t) ^ M) * (D * (1 + t) ^ N) := hbnd
    _ = ((∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * A * D) *
        (1 + t) ^ (M + N) := by
      rw [pow_add]
      ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem kernel_eq_raw (c : ℝ) (j : ℕ) (b : E × ℝ → ℝ) (y : E × ℝ) (t : ℝ) :
    kernel c j b y t = ((1 / 2 : ℝ) * Real.exp (-c * t)) * rawKernel j b y t := by
  simp only [kernel, rawKernel, amplitude, transform]
  ring

/-- Total parameter derivatives of the concrete kernel have an exponential times
polynomial majorant. No bound for kernel derivatives is assumed. -/
theorem kernel_iteratedFDeriv_bound_of_jetBounds {b : E × ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (c : ℝ) (j n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {B : ℝ} (hB : 0 ≤ B)
    (hjets : ∀ k ≤ n, ∀ z : E × ℝ, ‖z‖ ≤ R → ‖iteratedFDeriv ℝ k b z‖ ≤ B) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ y : E × ℝ, ∀ t : ℝ,
      ‖y‖ ≤ R → 0 ≤ t →
      ‖iteratedFDeriv ℝ n (fun z => kernel c j b z t) y‖ ≤
        C * (1 + t) ^ N * Real.exp (-c * t) := by
  obtain ⟨C, N, hC, hbound⟩ := rawKernel_iteratedFDeriv_bound hb j n hR hB hjets
  refine ⟨C / 2, N, by positivity, ?_⟩
  intro y t hy ht
  have heq : (fun z => kernel c j b z t) =
      ((1 / 2 : ℝ) * Real.exp (-c * t)) • (fun z => rawKernel j b z t) := by
    funext z
    exact kernel_eq_raw c j b z t
  have hs : ContDiff ℝ n (fun z => rawKernel j b z t) :=
    (rawKernel_contDiff j hb ht).of_le (nat_le_smooth n)
  rw [heq, iteratedFDeriv_const_smul_apply hs.contDiffAt]
  apply (ContinuousMultilinearMap.opNorm_smul_le
    ((1 / 2 : ℝ) * Real.exp (-c * t))
    (iteratedFDeriv ℝ n (fun z => rawKernel j b z t) y)).trans
  rw [Real.norm_eq_abs,
    abs_of_pos (show 0 < (1 / 2 : ℝ) * Real.exp (-c * t) by positivity)]
  calc
    (1 / 2 * Real.exp (-c * t)) *
        ‖iteratedFDeriv ℝ n (fun z => rawKernel j b z t) y‖ ≤
      (1 / 2 * Real.exp (-c * t)) * (C * (1 + t) ^ N) :=
        mul_le_mul_of_nonneg_left (hbound y t hy ht) (by positivity)
    _ = C / 2 * (1 + t) ^ N * Real.exp (-c * t) := by ring

end NavierStokes.ParametricKernelBounds
