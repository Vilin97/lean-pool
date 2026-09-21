/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Basic

/-! # Hazard -/

namespace FD1D

noncomputable section

/-!
# Local two-child hazard algebra

This file formalizes equations (1), (4), and (5) from
`hierarchical_quantile_matching.md`.  The namespace contains only local
quantities for a parent with natural-valued child counts `x` and `y`.

At an empty parent the paper extends both child hazards by the parent hazard.
The policy split is immaterial there; we set it to `(1 / 2, 1 / 2)`, which
keeps all `q = N * h` propagation identities valid without a separate API.
-/

namespace LocalHazard

/-- The parent count, coerced to `ℝ`. -/
def N (x y : ℕ) : ℝ := (x : ℝ) + (y : ℝ)

/-- The denominator `D = 2xy + a(x+y)` at a nonempty parent. -/
def D (a : ℝ) (x y : ℕ) : ℝ :=
  2 * (x : ℝ) * (y : ℝ) + a * N x y

/-- The policy's conditional probability of choosing the left child. -/
def dL (a : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then 1 / 2 else (x : ℝ) * ((y : ℝ) + a) / D a x y

/-- The policy's conditional probability of choosing the right child. -/
def dR (a : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then 1 / 2 else (y : ℝ) * ((x : ℝ) + a) / D a x y

/-- The left child hazard, including the paper's extension at an empty node. -/
def hL (a h : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then h else h * N x y * ((y : ℝ) + a) / D a x y

/-- The right child hazard, including the paper's extension at an empty node. -/
def hR (a h : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then h else h * N x y * ((x : ℝ) + a) / D a x y

/-- Parent deletion mass under the invariant `q = N h`. -/
def q (h : ℝ) (x y : ℕ) : ℝ := N x y * h

/-- Left deletion mass obtained from the policy split. -/
def qL (a h : ℝ) (x y : ℕ) : ℝ := q h x y * dL a x y

/-- Right deletion mass obtained from the policy split. -/
def qR (a h : ℝ) (x y : ℕ) : ℝ := q h x y * dR a x y

/-- The signed child-mass imbalance `b = q_L - q_R`. -/
def b (a h : ℝ) (x y : ℕ) : ℝ := qL a h x y - qR a h x y

/-- The average hazard increment in `h_L = h + V + w`. -/
def V (a h : ℝ) (x y : ℕ) : ℝ := (hL a h x y + hR a h x y) / 2 - h

/-- The antisymmetric hazard increment in `h_L = h + V + w`. -/
def w (a h : ℝ) (x y : ℕ) : ℝ := (hL a h x y - hR a h x y) / 2

/-- The normalized child-count imbalance `rho = (x-y)/(x+y)`. -/
def rho (x y : ℕ) : ℝ := ((x : ℝ) - (y : ℝ)) / N x y

/-- The parent discrepancy variable `t = (p-q)/a`. -/
def t (a p h : ℝ) (x y : ℕ) : ℝ := (p - q h x y) / a

/-- The left child discrepancy variable. -/
def tL (a p h : ℝ) (x y : ℕ) : ℝ := (p / 2 - qL a h x y) / a

/-- The right child discrepancy variable. -/
def tR (a p h : ℝ) (x y : ℕ) : ℝ := (p / 2 - qR a h x y) / a

theorem N_nonneg (x y : ℕ) : 0 ≤ N x y := by
  unfold N
  positivity

theorem N_pos {x y : ℕ} (hne : x + y ≠ 0) : 0 < N x y := by
  have hxy : 0 < x + y := Nat.pos_of_ne_zero hne
  unfold N
  exact_mod_cast hxy

theorem N_ne_zero {x y : ℕ} (hne : x + y ≠ 0) : N x y ≠ 0 :=
  (N_pos hne).ne'

theorem count_add_a_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < (k : ℝ) + a := by
  positivity

theorem D_pos {a : ℝ} {x y : ℕ} (ha : 0 < a) (hne : x + y ≠ 0) :
    0 < D a x y := by
  have hx : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  have hy : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
  have hN : 0 < N x y := N_pos hne
  unfold D
  positivity

theorem D_ne_zero {a : ℝ} {x y : ℕ} (ha : 0 < a) (hne : x + y ≠ 0) :
    D a x y ≠ 0 :=
  (D_pos ha hne).ne'

theorem N_add_two_mul_a_pos {a : ℝ} (ha : 0 < a) (x y : ℕ) :
    0 < N x y + 2 * a := by
  have hN := N_nonneg x y
  linarith

theorem N_add_two_mul_a_ne_zero {a : ℝ} (ha : 0 < a) (x y : ℕ) :
    N x y + 2 * a ≠ 0 :=
  (N_add_two_mul_a_pos ha x y).ne'

theorem dL_add_dR {a : ℝ} {x y : ℕ} (ha : 0 < a) :
    dL a x y + dR a x y = 1 := by
  by_cases hne : x + y = 0
  · norm_num [dL, dR, hne]
  · have hD := D_ne_zero ha hne
    simp only [dL, dR, ite_eq_right hne]
    field_simp [hD]
    unfold D N
    ring

theorem qL_add_qR {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    qL a h x y + qR a h x y = q h x y := by
  rw [qL, qR, ← mul_add, dL_add_dR ha, mul_one]

/-- Algebraic propagation of `q = N h` to the left child. -/
theorem q_mul_dL_eq_count_mul_hL {a h qParent : ℝ} {x y : ℕ}
    (ha : 0 < a) (hq : qParent = N x y * h) :
    qParent * dL a x y = (x : ℝ) * hL a h x y := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [dL, hL, hq, N]
  · have hD := D_ne_zero ha hne
    rw [hq]
    simp only [dL, hL, ite_eq_right hne]
    field_simp [hD]

/-- Algebraic propagation of `q = N h` to the right child. -/
theorem q_mul_dR_eq_count_mul_hR {a h qParent : ℝ} {x y : ℕ}
    (ha : 0 < a) (hq : qParent = N x y * h) :
    qParent * dR a x y = (y : ℝ) * hR a h x y := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [dR, hR, hq, N]
  · have hD := D_ne_zero ha hne
    rw [hq]
    simp only [dR, hR, ite_eq_right hne]
    field_simp [hD]

theorem qL_eq_count_mul_hL {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    qL a h x y = (x : ℝ) * hL a h x y := by
  exact q_mul_dL_eq_count_mul_hL ha rfl

theorem qR_eq_count_mul_hR {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    qR a h x y = (y : ℝ) * hR a h x y := by
  exact q_mul_dR_eq_count_mul_hR ha rfl

theorem hL_pos {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    0 < hL a h x y := by
  by_cases hne : x + y = 0
  · simp [hL, hne, hh]
  · have hN := N_pos hne
    have hD := D_pos ha hne
    have hya := count_add_a_pos ha y
    simp only [hL, ite_eq_right hne]
    positivity

theorem hR_pos {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    0 < hR a h x y := by
  by_cases hne : x + y = 0
  · simp [hR, hne, hh]
  · have hN := N_pos hne
    have hD := D_pos ha hne
    have hxa := count_add_a_pos ha x
    simp only [hR, ite_eq_right hne]
    positivity

/-- Equation `b = -a(h_L-h_R)`, including the empty-node extension. -/
theorem b_eq_neg_a_mul_hazardDiff {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    b a h x y = -a * (hL a h x y - hR a h x y) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    simp [b, qL, qR, q, dL, dR, hL, hR, N]
  · have hD := D_ne_zero ha hne
    simp only [b, qL, qR, q, dL, dR, hL, hR, ite_eq_right hne]
    field_simp [hD, D, N]
    ring

theorem b_eq_neg_two_mul_a_mul_w {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    b a h x y = -2 * a * w a h x y := by
  rw [b_eq_neg_a_mul_hazardDiff ha]
  simp only [w]
  ring

theorem rho_sq_le_one {x y : ℕ} (hne : x + y ≠ 0) : rho x y ^ 2 ≤ 1 := by
  have hx : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  have hy : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
  have hN : 0 < N x y := N_pos hne
  unfold rho
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hN)).2
  have hxy : 0 ≤ (x : ℝ) * (y : ℝ) := mul_nonneg hx hy
  simp only [N]
  nlinarith

/-- The exact identity in equation (1). -/
theorem hazardIncrement_eq {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    (hL a h x y ^ 2 + hR a h x y ^ 2) / 2 - h ^ 2 =
      b a h x y ^ 2 / a ^ 2 *
        ((3 - rho x y ^ 2) / 4 + a / N x y) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [hL, hR, b, qL, qR, q, dL, dR, rho, N]
  · have hD := D_ne_zero ha hne
    have hN := N_ne_zero hne
    have ha0 := ha.ne'
    simp only [hL, hR, b, qL, qR, q, dL, dR, rho, ite_eq_right hne]
    field_simp [hD, hN, ha0]
    unfold D N
    ring

/-- The lower bound in equation (1). -/
theorem hazardIncrement_ge {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    b a h x y ^ 2 / (2 * a ^ 2) ≤
      (hL a h x y ^ 2 + hR a h x y ^ 2) / 2 - h ^ 2 := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [hL, hR, b, qL, qR, q, dL, dR, N]
  · have hN : 0 < N x y := N_pos hne
    have hrho := rho_sq_le_one hne
    have haN : 0 ≤ a / N x y := (div_pos ha hN).le
    have hfactor :
        (1 : ℝ) / 2 ≤ (3 - rho x y ^ 2) / 4 + a / N x y := by
      linarith
    have hba : 0 ≤ b a h x y ^ 2 / a ^ 2 := by positivity
    rw [hazardIncrement_eq ha]
    calc
      b a h x y ^ 2 / (2 * a ^ 2) =
          (b a h x y ^ 2 / a ^ 2) * (1 / 2) := by ring
      _ ≤ (b a h x y ^ 2 / a ^ 2) *
          ((3 - rho x y ^ 2) / 4 + a / N x y) :=
        mul_le_mul_of_nonneg_left hfactor hba

theorem hL_eq_h_add_V_add_w (a h : ℝ) (x y : ℕ) :
    hL a h x y = h + V a h x y + w a h x y := by
  simp only [V, w]
  ring

theorem hR_eq_h_add_V_sub_w (a h : ℝ) (x y : ℕ) :
    hR a h x y = h + V a h x y - w a h x y := by
  simp only [V, w]
  ring

theorem V_eq {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    V a h x y =
      h * ((x : ℝ) - (y : ℝ)) ^ 2 / (2 * D a x y) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [V, hL, hR, D, N]
  · have hD := D_ne_zero ha hne
    simp only [V, hL, hR, ite_eq_right hne]
    field_simp [hD]
    unfold D N
    ring

theorem w_eq {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    w a h x y =
      h * N x y * ((y : ℝ) - (x : ℝ)) / (2 * D a x y) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [w, hL, hR, D, N]
  · have hD := D_ne_zero ha hne
    simp only [w, hL, hR, ite_eq_right hne]
    field_simp [hD]
    ring

theorem V_nonneg {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 ≤ h) :
    0 ≤ V a h x y := by
  rw [V_eq ha]
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [D, N]
  · have hD := D_pos ha hne
    positivity

theorem normalizedV_le {a : ℝ} {x y : ℕ} (ha : 0 < a) :
    ((x : ℝ) - (y : ℝ)) ^ 2 / (2 * D a x y) ≤ N x y / (2 * a) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [D, N]
  · have hx : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
    have hy : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
    have hN : 0 < N x y := N_pos hne
    have hD : 0 < D a x y := D_pos ha hne
    have hxy : 0 ≤ (x : ℝ) * (y : ℝ) := mul_nonneg hx hy
    have hdelta : ((x : ℝ) - (y : ℝ)) ^ 2 ≤ N x y ^ 2 := by
      simp only [N]
      nlinarith
    have haDelta :
        a * ((x : ℝ) - (y : ℝ)) ^ 2 ≤ a * N x y ^ 2 :=
      mul_le_mul_of_nonneg_left hdelta ha.le
    have hDlower : a * N x y ≤ D a x y := by
      simp only [D]
      nlinarith
    have hND : N x y * (a * N x y) ≤ N x y * D a x y :=
      mul_le_mul_of_nonneg_left hDlower hN.le
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * D a x y)
      (by positivity : 0 < 2 * a)).2
    nlinarith [haDelta, hND]

theorem V_div_h_eq {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    V a h x y / h =
      ((x : ℝ) - (y : ℝ)) ^ 2 / (2 * D a x y) := by
  rw [V_eq ha]
  field_simp [hh.ne']

/-- The bound `V/h ≤ N/(2a)` from equation (4). -/
theorem V_div_h_le {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    V a h x y / h ≤ N x y / (2 * a) := by
  rw [V_div_h_eq ha hh]
  exact normalizedV_le ha

/-- The exact quadratic identity for `w` in equation (4). -/
theorem w_sq_eq {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    w a h x y ^ 2 =
      N x y / (N x y + 2 * a) * V a h x y * (h + V a h x y) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [w, V, hL, hR, N]
  · have hD := D_ne_zero ha hne
    have hNa := N_add_two_mul_a_ne_zero ha x y
    rw [w_eq ha, V_eq ha]
    field_simp [hD, hNa]
    unfold D N
    ring

theorem N_div_N_add_two_mul_a_nonneg {a : ℝ} (ha : 0 < a) (x y : ℕ) :
    0 ≤ N x y / (N x y + 2 * a) := by
  exact div_nonneg (N_nonneg x y) (N_add_two_mul_a_pos ha x y).le

theorem N_div_N_add_two_mul_a_le_one {a : ℝ} (ha : 0 < a) (x y : ℕ) :
    N x y / (N x y + 2 * a) ≤ 1 := by
  apply (div_le_one (N_add_two_mul_a_pos ha x y)).2
  linarith

theorem abs_w_le_V_add_half_h {a h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) :
    |w a h x y| ≤ V a h x y + h / 2 := by
  have hV : 0 ≤ V a h x y := V_nonneg ha hh
  have hsum : 0 ≤ h + V a h x y := add_nonneg hh hV
  have hprod : 0 ≤ V a h x y * (h + V a h x y) :=
    mul_nonneg hV hsum
  have hratio := N_div_N_add_two_mul_a_le_one ha x y
  have hwsq : w a h x y ^ 2 ≤ V a h x y * (h + V a h x y) := by
    rw [w_sq_eq ha]
    calc
      N x y / (N x y + 2 * a) * V a h x y * (h + V a h x y) =
          (N x y / (N x y + 2 * a)) *
            (V a h x y * (h + V a h x y)) := by ring
      _ ≤ 1 * (V a h x y * (h + V a h x y)) :=
        mul_le_mul_of_nonneg_right hratio hprod
      _ = V a h x y * (h + V a h x y) := one_mul _
  have htarget : 0 ≤ V a h x y + h / 2 := by positivity
  have htargetSq :
      w a h x y ^ 2 ≤ (V a h x y + h / 2) ^ 2 := by
    nlinarith [sq_nonneg h]
  have habsSq :
      |w a h x y| ^ 2 ≤ (V a h x y + h / 2) ^ 2 := by
    simpa using htargetSq
  nlinarith [abs_nonneg (w a h x y)]

/-- The left relation `t_L = t/2 + w` from equation (4). -/
theorem tL_eq {a p h : ℝ} {x y : ℕ} (ha : 0 < a) :
    tL a p h x y = t a p h x y / 2 + w a h x y := by
  have hqsum := qL_add_qR (a := a) (h := h) (x := x) (y := y) ha
  have hbw := b_eq_neg_two_mul_a_mul_w (a := a) (h := h) (x := x) (y := y) ha
  simp only [b] at hbw
  simp only [tL, t]
  field_simp [ha.ne']
  nlinarith

/-- The right relation `t_R = t/2 - w` from equation (4). -/
theorem tR_eq {a p h : ℝ} {x y : ℕ} (ha : 0 < a) :
    tR a p h x y = t a p h x y / 2 - w a h x y := by
  have hqsum := qL_add_qR (a := a) (h := h) (x := x) (y := y) ha
  have hbw := b_eq_neg_two_mul_a_mul_w (a := a) (h := h) (x := x) (y := y) ha
  simp only [b] at hbw
  simp only [tR, t]
  field_simp [ha.ne']
  nlinarith

theorem tL_le_half_hL {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) (ht : t a p h x y ≤ h / 2) :
    tL a p h x y ≤ hL a h x y / 2 := by
  have hw := abs_w_le_V_add_half_h (x := x) (y := y) ha hh
  have hw' : w a h x y ≤ V a h x y + h / 2 :=
    le_trans (le_abs_self _) hw
  rw [tL_eq ha, hL_eq_h_add_V_add_w]
  linarith

theorem tR_le_half_hR {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) (ht : t a p h x y ≤ h / 2) :
    tR a p h x y ≤ hR a h x y / 2 := by
  have hw := abs_w_le_V_add_half_h (x := x) (y := y) ha hh
  have hw' : -w a h x y ≤ V a h x y + h / 2 := by
    calc
      -w a h x y ≤ |-w a h x y| := le_abs_self _
      _ = |w a h x y| := abs_neg _
      _ ≤ V a h x y + h / 2 := hw
  rw [tR_eq ha, hR_eq_h_add_V_sub_w]
  linarith

/-- Propagation of the invariant `t/h ≤ 1/2` to the left child. -/
theorem t_div_h_le_half_left {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (ht : t a p h x y / h ≤ 1 / 2) :
    tL a p h x y / hL a h x y ≤ 1 / 2 := by
  have ht' : t a p h x y ≤ h / 2 := by
    apply (div_le_iff₀ hh).mp at ht
    linarith
  have hchild : 0 < hL a h x y := hL_pos ha hh
  apply (div_le_iff₀ hchild).2
  have := tL_le_half_hL ha hh.le ht'
  linarith

/-- Propagation of the invariant `t/h ≤ 1/2` to the right child. -/
theorem t_div_h_le_half_right {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (ht : t a p h x y / h ≤ 1 / 2) :
    tR a p h x y / hR a h x y ≤ 1 / 2 := by
  have ht' : t a p h x y ≤ h / 2 := by
    apply (div_le_iff₀ hh).mp at ht
    linarith
  have hchild : 0 < hR a h x y := hR_pos ha hh
  apply (div_le_iff₀ hchild).2
  have := tR_le_half_hR ha hh.le ht'
  linarith

/-- The sharper first inequality used in equation (5). -/
theorem p_le_N_add_half_a_mul_h {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (ht : t a p h x y ≤ h / 2) :
    p ≤ (N x y + a / 2) * h := by
  unfold t at ht
  have ht' := (div_le_iff₀ ha).mp ht
  simp only [q] at ht'
  nlinarith

/-- Equation (5): `p ≤ (N+a)h`. -/
theorem p_le_N_add_a_mul_h {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) (ht : t a p h x y ≤ h / 2) :
    p ≤ (N x y + a) * h := by
  calc
    p ≤ (N x y + a / 2) * h := p_le_N_add_half_a_mul_h ha ht
    _ ≤ (N x y + a) * h := by
      apply mul_le_mul_of_nonneg_right _ hh
      linarith

theorem p_le_N_add_a_mul_h_of_ratio {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (ht : t a p h x y / h ≤ 1 / 2) :
    p ≤ (N x y + a) * h := by
  apply p_le_N_add_a_mul_h ha hh.le
  have ht' := (div_le_iff₀ hh).mp ht
  linarith

end LocalHazard

end

end FD1D
