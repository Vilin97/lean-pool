/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Derivative bounds for the normalized flat primitive kernel

The expression algebra below is closed under actual differentiation in `x`.
It bounds all derivatives of the concrete square-root kernel from finitely
many derivatives of its smooth profile and proves continuity in the integral
parameter. Exponential-majorant integrability is supplied separately.
-/

@[expose] public section


noncomputable section

open Set
open scoped ContDiff

namespace NavierStokes.FlatKernelBounds

/-- Denominator, given by `Real.sqrt (1 + x ^ 2 * t)`. -/
def denominator (x t : ℝ) : ℝ := Real.sqrt (1 + x ^ 2 * t)

/-- Coordinate, given by `x / denominator x t`. -/
def coordinate (x t : ℝ) : ℝ := x / denominator x t

theorem base_pos {x t : ℝ} (ht : 0 ≤ t) : 0 < 1 + x ^ 2 * t := by
  positivity

theorem denominator_pos {x t : ℝ} (ht : 0 ≤ t) : 0 < denominator x t :=
  Real.sqrt_pos.2 (base_pos ht)

theorem denominator_ne_zero {x t : ℝ} (ht : 0 ≤ t) : denominator x t ≠ 0 :=
  ne_of_gt (denominator_pos ht)

theorem denominator_sq {x t : ℝ} (ht : 0 ≤ t) :
    denominator x t ^ 2 = 1 + x ^ 2 * t :=
  Real.sq_sqrt (le_of_lt (base_pos ht))

theorem one_le_denominator {x t : ℝ} (ht : 0 ≤ t) : 1 ≤ denominator x t := by
  apply Real.one_le_sqrt.2
  nlinarith [mul_nonneg (sq_nonneg x) ht]

theorem hasDerivAt_denominator {x t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun y => denominator y t)
      (x * t * (denominator x t)⁻¹) x := by
  have hbase : HasDerivAt (fun y : ℝ => 1 + y ^ 2 * t) (2 * x * t) x := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
      (((hasDerivAt_id x).pow 2).mul_const t).const_add 1
  convert! hbase.sqrt (ne_of_gt (base_pos ht)) using 1
  simp only [denominator, div_eq_mul_inv, mul_inv_rev]
  ring

theorem hasDerivAt_inv_denominator {x t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun y => (denominator y t)⁻¹)
      (-(x * t) * ((denominator x t)⁻¹) ^ 3) x := by
  convert! (hasDerivAt_denominator ht).inv (denominator_ne_zero ht) using 1
  field_simp

theorem hasDerivAt_coordinate {x t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun y => coordinate y t) ((denominator x t)⁻¹ ^ 3) x := by
  have h := (hasDerivAt_id x).mul (hasDerivAt_inv_denominator ht)
  convert! h using 1
  have hd := denominator_ne_zero (x := x) ht
  have hsq := denominator_sq (x := x) ht
  simp only [id_eq] at *
  field_simp [hd]
  nlinarith [congrArg (fun z : ℝ => z * denominator x t) hsq]

/-- Finite expressions in the variables needed by every kernel derivative. -/
inductive Expr where
  | const (c : ℝ)
  | x
  | t
  | root
  | invRoot
  | jet (k : ℕ)
  | add (e f : Expr)
  | mul (e f : Expr)

/-- Eval used in flat kernel bounds. -/
def Expr.eval : Expr → (ℝ → ℝ) → ℝ → ℝ → ℝ
  | .const c, _, _, _ => c
  | .x, _, xv, _ => xv
  | .t, _, _, tv => tv
  | .root, _, xv, tv => denominator xv tv
  | .invRoot, _, xv, tv => (denominator xv tv)⁻¹
  | .jet k, b, xv, tv => iteratedDeriv k b (coordinate xv tv)
  | .add e f, b, xv, tv => e.eval b xv tv + f.eval b xv tv
  | .mul e f, b, xv, tv => e.eval b xv tv * f.eval b xv tv

/-- Pow as an element of `ℕ → Expr | 0 => .const 1 | n + 1 => .mul (e.pow n) e`. -/
def Expr.pow (e : Expr) : ℕ → Expr
  | 0 => .const 1
  | n + 1 => .mul (e.pow n) e

@[simp] theorem Expr.eval_pow (e : Expr) (n : ℕ) (b : ℝ → ℝ) (x t : ℝ) :
    (e.pow n).eval b x t = (e.eval b x t) ^ n := by
  induction n with
  | zero => simp [Expr.pow, Expr.eval]
  | succ n ih => simp [Expr.pow, Expr.eval, ih, pow_succ]

/-- Diff used in flat kernel bounds. -/
def Expr.diff : Expr → Expr
  | .const _ => .const 0
  | .x => .const 1
  | .t => .const 0
  | .root => .mul (.mul .x .t) .invRoot
  | .invRoot => .mul (.const (-1)) (.mul (.mul .x .t) (Expr.invRoot.pow 3))
  | .jet k => .mul (.jet (k + 1)) (Expr.invRoot.pow 3)
  | .add e f => .add e.diff f.diff
  | .mul e f => .add (.mul e.diff f) (.mul e f.diff)

theorem Expr.hasDerivAt_eval (e : Expr) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) {x t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun y => e.eval b y t) (e.diff.eval b x t) x := by
  induction e with
  | const c => exact hasDerivAt_const x c
  | x => exact hasDerivAt_id x
  | t => exact hasDerivAt_const x t
  | root => exact hasDerivAt_denominator ht
  | invRoot =>
      simpa [Expr.diff, Expr.eval, Expr.eval_pow, neg_mul] using
        (hasDerivAt_inv_denominator (x := x) ht)
  | jet k =>
      have hk : HasDerivAt (iteratedDeriv k b)
          (iteratedDeriv (k + 1) b (coordinate x t)) (coordinate x t) := by
        rw [iteratedDeriv_succ]
        exact ((hb.differentiable_iteratedDeriv k
          (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))) _).hasDerivAt
      simpa only [Function.comp_def, Expr.diff, Expr.eval, Expr.eval_pow] using
        hk.comp x (hasDerivAt_coordinate ht)
  | add e f ihe ihf => exact HasDerivAt.add ihe ihf
  | mul e f ihe ihf => exact ihe.mul ihf

theorem Expr.iteratedDeriv_eval (e : Expr) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    iteratedDeriv n (fun x => e.eval b x t) =
      fun x => ((Expr.diff^[n]) e).eval b x t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext x
      simpa only [Function.iterate_succ_apply'] using
        (((Expr.diff^[n]) e).hasDerivAt_eval hb ht).deriv

theorem Expr.contDiff_eval (e : Expr) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (fun x => e.eval b x t) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [e.iteratedDeriv_eval hb ht n]
  exact fun x => (((Expr.diff^[n]) e).hasDerivAt_eval hb ht).differentiableAt

theorem abs_coordinate_le {x t : ℝ} (ht : 0 ≤ t) :
    |coordinate x t| ≤ |x| := by
  rw [coordinate, abs_div, abs_of_pos (denominator_pos ht)]
  exact div_le_self (abs_nonneg x) (one_le_denominator ht)

theorem denominator_le_polynomial {R x t : ℝ} (hR : 0 ≤ R)
    (hx : |x| ≤ R) (ht : 0 ≤ t) :
    denominator x t ≤ (1 + R ^ 2) * (1 + t) := by
  have hsq : x ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_abs x,
      mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hR (abs_nonneg x))]
  have hd : denominator x t ≤ 1 + x ^ 2 * t := by
    nlinarith [denominator_sq (x := x) ht, one_le_denominator (x := x) ht,
      sq_nonneg (denominator x t - 1)]
  exact hd.trans (by nlinarith [mul_le_mul_of_nonneg_right hsq ht, sq_nonneg R])

theorem abs_inv_denominator_le_one {x t : ℝ} (ht : 0 ≤ t) :
    |(denominator x t)⁻¹| ≤ 1 := by
  rw [abs_of_pos (inv_pos.mpr (denominator_pos ht))]
  simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
    (one_le_denominator (x := x) ht)

/-- A bound uniform in a closed `x` interval and polynomial in nonnegative `t`. -/
def PolynomialBound (R : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
    ∀ x t : ℝ, |x| ≤ R → 0 ≤ t → |F x t| ≤ C * (1 + t) ^ N

theorem PolynomialBound.add {R : ℝ} {F G : ℝ → ℝ → ℝ}
    (hF : PolynomialBound R F) (hG : PolynomialBound R G) :
    PolynomialBound R (fun x t => F x t + G x t) := by
  obtain ⟨C, N, hC, hF⟩ := hF
  obtain ⟨D, M, hD, hG⟩ := hG
  refine ⟨C + D, N + M, add_nonneg hC hD, ?_⟩
  intro x t hx ht
  have hbase : 1 ≤ 1 + t := by linarith
  have hN : (1 + t) ^ N ≤ (1 + t) ^ (N + M) :=
    pow_le_pow_right₀ hbase (Nat.le_add_right N M)
  have hM : (1 + t) ^ M ≤ (1 + t) ^ (N + M) :=
    pow_le_pow_right₀ hbase (Nat.le_add_left M N)
  calc
    |F x t + G x t| ≤ |F x t| + |G x t| := abs_add_le _ _
    _ ≤ C * (1 + t) ^ N + D * (1 + t) ^ M := add_le_add (hF x t hx ht) (hG x t hx ht)
    _ ≤ C * (1 + t) ^ (N + M) + D * (1 + t) ^ (N + M) :=
      add_le_add (mul_le_mul_of_nonneg_left hN hC) (mul_le_mul_of_nonneg_left hM hD)
    _ = (C + D) * (1 + t) ^ (N + M) := by ring

theorem PolynomialBound.mul {R : ℝ} {F G : ℝ → ℝ → ℝ}
    (hF : PolynomialBound R F) (hG : PolynomialBound R G) :
    PolynomialBound R (fun x t => F x t * G x t) := by
  obtain ⟨C, N, hC, hF⟩ := hF
  obtain ⟨D, M, hD, hG⟩ := hG
  refine ⟨C * D, N + M, mul_nonneg hC hD, ?_⟩
  intro x t hx ht
  calc
    |F x t * G x t| = |F x t| * |G x t| := abs_mul _ _
    _ ≤ (C * (1 + t) ^ N) * (D * (1 + t) ^ M) :=
      mul_le_mul (hF x t hx ht) (hG x t hx ht) (abs_nonneg _)
        (mul_nonneg hC (pow_nonneg (by linarith) _))
    _ = (C * D) * (1 + t) ^ (N + M) := by rw [pow_add]; ring

/-- The greatest profile derivative order present in a finite expression. -/
def Expr.jetOrder : Expr → ℕ
  | .jet k => k
  | .add e f => max e.jetOrder f.jetOrder
  | .mul e f => max e.jetOrder f.jetOrder
  | _ => 0

/-- Only finitely many profile jets are needed for a given expression bound. -/
theorem Expr.polynomialBound_of_jetBound (e : Expr) {b : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R)
    (hjets : ∀ k ≤ e.jetOrder, ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, |y| ≤ R → |iteratedDeriv k b y| ≤ C) :
    PolynomialBound R (e.eval b) := by
  induction e with
  | const c => exact ⟨|c|, 0, abs_nonneg c, by intro x t hx ht; simp [Expr.eval]⟩
  | x => exact ⟨R, 0, hR, by intro x t hx ht; simpa [Expr.eval] using hx⟩
  | t =>
      exact ⟨1, 1, by norm_num, by intro x t hx ht; simp [Expr.eval, abs_of_nonneg ht]⟩
  | root =>
      refine ⟨1 + R ^ 2, 1, by positivity, ?_⟩
      intro x t hx ht
      simpa [Expr.eval, abs_of_pos (denominator_pos ht)] using
        denominator_le_polynomial hR hx ht
  | invRoot =>
      refine ⟨1, 0, by norm_num, ?_⟩
      intro x t hx ht
      simpa [Expr.eval] using (abs_inv_denominator_le_one (x := x) ht)
  | jet k =>
      obtain ⟨C, hC, hbound⟩ := hjets k (le_refl _)
      refine ⟨C, 0, hC, ?_⟩
      intro x t hx ht
      simpa [Expr.eval] using hbound (coordinate x t) ((abs_coordinate_le ht).trans hx)
  | add e f ihe ihf =>
      exact (ihe (fun k hk => hjets k (hk.trans (le_max_left _ _)))).add
        (ihf (fun k hk => hjets k (hk.trans (le_max_right _ _))))
  | mul e f ihe ihf =>
      exact (ihe (fun k hk => hjets k (hk.trans (le_max_left _ _)))).mul
        (ihf (fun k hk => hjets k (hk.trans (le_max_right _ _))))

theorem bounded_profile_jet {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (R : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, |y| ≤ R → |iteratedDeriv k b y| ≤ C := by
  have hcont := hb.continuous_iteratedDeriv k
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-R) R) hcont.continuousOn
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro y hy
  have hbnd : |iteratedDeriv k b y| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC y (abs_le.mp hy)
  exact hbnd.trans (le_abs_self C)

theorem Expr.polynomialBound (e : Expr) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) {R : ℝ} (hR : 0 ≤ R) :
    PolynomialBound R (e.eval b) :=
  e.polynomialBound_of_jetBound hR (fun k _ => bounded_profile_jet hb R k)

theorem continuous_denominator_t (x : ℝ) : Continuous (denominator x) := by
  exact (continuous_const.add (continuous_const.mul continuous_id)).sqrt

theorem continuousOn_coordinate_t (x : ℝ) :
    ContinuousOn (coordinate x) (Ici 0) := by
  exact continuous_const.continuousOn.div (continuous_denominator_t x).continuousOn
    (fun t ht => denominator_ne_zero ht)

theorem Expr.continuousOn_eval_t (e : Expr) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (x : ℝ) :
    ContinuousOn (fun t => e.eval b x t) (Ici 0) := by
  induction e with
  | const c => exact continuous_const.continuousOn
  | x => exact continuous_const.continuousOn
  | t => exact continuous_id.continuousOn
  | root => exact (continuous_denominator_t x).continuousOn
  | invRoot =>
      exact (continuous_denominator_t x).continuousOn.inv₀
        (fun t ht => denominator_ne_zero ht)
  | jet k =>
      exact (hb.continuous_iteratedDeriv k
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).comp_continuousOn
          (continuousOn_coordinate_t x)
  | add e f ihe ihf => exact ihe.add ihf
  | mul e f ihe ihf => exact ihe.mul ihf

theorem Expr.jetOrder_pow_le (e : Expr) (n : ℕ) :
    (e.pow n).jetOrder ≤ e.jetOrder := by
  induction n with
  | zero => simp [Expr.pow, Expr.jetOrder]
  | succ n ih => exact max_le ih le_rfl

theorem Expr.jetOrder_diff_le (e : Expr) : e.diff.jetOrder ≤ e.jetOrder + 1 := by
  induction e with
  | const c => simp [Expr.diff, Expr.jetOrder]
  | x => simp [Expr.diff, Expr.jetOrder]
  | t => simp [Expr.diff, Expr.jetOrder]
  | root => simp [Expr.diff, Expr.jetOrder]
  | invRoot => simp [Expr.diff, Expr.jetOrder, Expr.pow]
  | jet k => simp [Expr.diff, Expr.jetOrder, Expr.pow]
  | add e f ihe ihf =>
      exact max_le (ihe.trans (Nat.add_le_add_right (le_max_left _ _) 1))
        (ihf.trans (Nat.add_le_add_right (le_max_right _ _) 1))
  | mul e f ihe ihf =>
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
      · exact ihe.trans (Nat.add_le_add_right (le_max_left _ _) 1)
      · exact (le_max_right _ _).trans (Nat.le_add_right _ _)
      · exact (le_max_left _ _).trans (Nat.le_add_right _ _)
      · exact ihf.trans (Nat.add_le_add_right (le_max_right _ _) 1)

theorem Expr.jetOrder_iterate_diff_le (e : Expr) (n : ℕ) :
    ((Expr.diff^[n]) e).jetOrder ≤ e.jetOrder + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ((Expr.diff^[n]) e).jetOrder_diff_le.trans
        (by simpa only [Nat.add_assoc] using Nat.add_le_add_right ih 1)

/-- Kernel expr, given by `.mul (.mul (Expr.root.pow j) (Expr.invRoot.pow 3)) (.jet 0)`. -/
def kernelExpr (j : ℕ) : Expr :=
  .mul (.mul (Expr.root.pow j) (Expr.invRoot.pow 3)) (.jet 0)

theorem kernelExpr_jetOrder (j : ℕ) : (kernelExpr j).jetOrder = 0 := by
  have hroot := Expr.root.jetOrder_pow_le j
  have hinv := Expr.invRoot.jetOrder_pow_le 3
  have hroot' : (Expr.root.pow j).jetOrder = 0 := Nat.eq_zero_of_le_zero hroot
  have hinv' : (Expr.invRoot.pow 3).jetOrder = 0 := Nat.eq_zero_of_le_zero hinv
  simp [kernelExpr, Expr.jetOrder, hroot', hinv']

/-- Kernel, given by `(1 / 2 : ℝ) * Real.exp (-c * t) * (denominator x t ^ j / denominator x t ^
3) * b (coordinate x t)`. -/
def kernel (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp (-c * t) *
    (denominator x t ^ j / denominator x t ^ 3) * b (coordinate x t)

theorem kernel_eq_expr (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x t : ℝ) :
    kernel c j b x t = ((1 / 2 : ℝ) * Real.exp (-c * t)) * (kernelExpr j).eval b x t := by
  simp [kernel, kernelExpr, Expr.eval, Expr.eval_pow, div_eq_mul_inv, inv_pow, mul_assoc]

theorem Expr.iteratedDeriv_const_mul_eval (e : Expr) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) {t : ℝ} (ht : 0 ≤ t) (w : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x => w * e.eval b x t) =
      fun x => w * ((Expr.diff^[n]) e).eval b x t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext x
      simpa only [Function.iterate_succ_apply'] using
        ((((Expr.diff^[n]) e).hasDerivAt_eval hb ht).const_mul w).deriv

theorem iteratedDeriv_kernel {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (c : ℝ) (j n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv n (fun x => kernel c j b x t) =
      fun x => ((1 / 2 : ℝ) * Real.exp (-c * t)) *
        ((Expr.diff^[n]) (kernelExpr j)).eval b x t := by
  simp_rw [kernel_eq_expr]
  exact (kernelExpr j).iteratedDeriv_const_mul_eval hb ht _ n

theorem kernel_contDiff_x {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (c : ℝ) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (fun x => kernel c j b x t) := by
  simp_rw [kernel_eq_expr]
  exact contDiff_const.mul ((kernelExpr j).contDiff_eval hb ht)

theorem kernel_iteratedDeriv_contDiff_x {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (c : ℝ) (j n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (iteratedDeriv n (fun x => kernel c j b x t)) := by
  rw [iteratedDeriv_kernel hb c j n ht]
  exact contDiff_const.mul (((Expr.diff^[n]) (kernelExpr j)).contDiff_eval hb ht)

theorem unweighted_iteratedDeriv_bound {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (j n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x t : ℝ, |x| ≤ R → 0 ≤ t →
      |iteratedDeriv n (fun y => (denominator y t ^ j / denominator y t ^ 3) *
        b (coordinate y t)) x| ≤ C * (1 + t) ^ N := by
  obtain ⟨C, N, hC, hbound⟩ := ((Expr.diff^[n]) (kernelExpr j)).polynomialBound hb hR
  refine ⟨C, N, hC, ?_⟩
  intro x t hx ht
  have hcore : (fun y => (denominator y t ^ j / denominator y t ^ 3) *
      b (coordinate y t)) = fun y => (kernelExpr j).eval b y t := by
    funext y
    simp [kernelExpr, Expr.eval, div_eq_mul_inv, inv_pow]
  rw [hcore, (kernelExpr j).iteratedDeriv_eval hb ht n]
  exact hbound x t hx ht

/-- An order-`n` bound uses only the first `n` profile jets on `[-R,R]`.
The global smoothness assumption identifies the expression with the actual derivative. -/
theorem kernel_iteratedDeriv_bound_of_jetBounds {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (c : ℝ) (j n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hjets : ∀ k ≤ n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, |y| ≤ R → |iteratedDeriv k b y| ≤ C) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x t : ℝ, |x| ≤ R → 0 ≤ t →
      |iteratedDeriv n (fun y => kernel c j b y t) x| ≤
        C * (1 + t) ^ N * Real.exp (-c * t) := by
  have horder : ((Expr.diff^[n]) (kernelExpr j)).jetOrder ≤ n := by
    simpa only [kernelExpr_jetOrder, Nat.zero_add] using
      (kernelExpr j).jetOrder_iterate_diff_le n
  obtain ⟨C, N, hC, hbound⟩ :=
    ((Expr.diff^[n]) (kernelExpr j)).polynomialBound_of_jetBound hR
      (fun k hk => hjets k (hk.trans horder))
  refine ⟨C / 2, N, by positivity, ?_⟩
  intro x t hx ht
  rw [iteratedDeriv_kernel hb c j n ht]
  rw [abs_mul, abs_of_nonneg (show 0 ≤ (1 / 2 : ℝ) * Real.exp (-c * t) by positivity)]
  calc
    (1 / 2 * Real.exp (-c * t)) *
        |((Expr.diff^[n]) (kernelExpr j)).eval b x t| ≤
      (1 / 2 * Real.exp (-c * t)) * (C * (1 + t) ^ N) :=
        mul_le_mul_of_nonneg_left (hbound x t hx ht) (by positivity)
    _ = C / 2 * (1 + t) ^ N * Real.exp (-c * t) := by ring

theorem kernel_iteratedDeriv_bound {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (c : ℝ) (j n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x t : ℝ, |x| ≤ R → 0 ≤ t →
      |iteratedDeriv n (fun y => kernel c j b y t) x| ≤
        C * (1 + t) ^ N * Real.exp (-c * t) :=
  kernel_iteratedDeriv_bound_of_jetBounds hb c j n hR
    (fun k _ => bounded_profile_jet hb R k)

theorem kernel_iteratedDeriv_continuousOn_t {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (c : ℝ) (j n : ℕ) (x : ℝ) :
    ContinuousOn (fun t => iteratedDeriv n (fun y => kernel c j b y t) x) (Ici 0) := by
  have hweight : Continuous (fun t : ℝ => (1 / 2 : ℝ) * Real.exp (-c * t)) :=
    continuous_const.mul (continuous_const.mul continuous_id).rexp
  apply (hweight.continuousOn.mul
    (((Expr.diff^[n]) (kernelExpr j)).continuousOn_eval_t hb x)).congr
  intro t ht
  exact congrFun (iteratedDeriv_kernel hb c j n ht) x

end NavierStokes.FlatKernelBounds
