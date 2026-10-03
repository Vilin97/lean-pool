/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The tail integral `∫_{20}^{400} (x F(x) + 27/16)/x³ dx`

On the grid `t_i = 20 + i/3` (`i ≤ 1140`) the fractional parts `{x}` and `{3x/40}` are affine on
each piece. With `P = 74 g(1-g) - λ f(1-f)` and `C = (74/α) G₀(g) - λ G₀(f)`,
`G₀(v) = v(1-v)(2v-1)/6`, we have `P' = F + λ` and `C' = P - Pbar` on each piece, and `P`, `C` are
continuous across the breakpoints. Two integrations by parts on each piece and telescoping give
`∑_i ∫_{t_i}^{t_{i+1}} (x F + 27/16)/x³ ≤ tailBound`.
-/

public section

open Finset intervalIntegral

namespace Zeta5Irrational

/-- The grid. -/
@[expose] noncomputable def tT (i : ℕ) : ℝ :=
  20 + i / 3

/-- Integer part of the left endpoint `tT i` of a tail interval. -/
@[expose] def qT (i : ℕ) : ℕ :=
  (60 + i) / 3

/-- Integer part of `3 / 40 * tT i`, used to fix the second fractional part. -/
@[expose] def qT' (i : ℕ) : ℕ :=
  (60 + i) / 40

/-- `F` on the piece `i`. -/
@[expose] noncomputable def FT (i : ℕ) (x : ℝ) : ℝ :=
  37 / 10 + 37 / 20 * (x - qT i) - 111 / 10 * (3 / 40 * x - qT' i)

/-- The tail majorant on piece `i`, including the additive error `27 / 16`. -/
@[expose] noncomputable def gT (i : ℕ) (x : ℝ) : ℝ :=
  x * FT i x + 27 / 16

/-- The quadratic oscillation contributed by the two fractional parts on tail piece `i`. -/
noncomputable def PT (i : ℕ) (x : ℝ) : ℝ :=
  74 * ((3 / 40 * x - qT' i) * (1 - (3 / 40 * x - qT' i))) -
    37 / 40 * ((x - qT i) * (1 - (x - qT i)))

/-- Polynomial primitive of the centered quadratic `v * (1 - v) - 1 / 6`. -/
noncomputable def G0 (v : ℝ) : ℝ :=
  v * (1 - v) * (2 * v - 1) / 6

/-- Primitive for the centered tail oscillation `PT i - Pbar` on piece `i`. -/
noncomputable def CT (i : ℕ) (x : ℝ) : ℝ :=
  74 * 40 / 3 * G0 (3 / 40 * x - qT' i) - 37 / 40 * G0 (x - qT i)

/-- `Pbar = (74 - λ)/6`. -/
noncomputable def Pbar : ℝ :=
  2923 / 240

/-! ### The pieces -/

lemma tT_succ (i : ℕ) : tT (i + 1) = tT i + 1 / 3 := by unfold tT; push_cast; ring

lemma qT_le (i : ℕ) : (qT i : ℝ) ≤ tT i := by
  unfold qT tT
  have h := Nat.div_mul_le_self (60 + i) 3
  have : ((60 + i) / 3 : ℕ) * (3 : ℝ) ≤ 60 + i := by exact_mod_cast h
  linarith

lemma tT_succ_le (i : ℕ) : tT (i + 1) ≤ qT i + 1 := by
  unfold qT tT
  have h := Nat.lt_div_mul_add (a := 60 + i) (show 0 < 3 by norm_num)
  have : ((60 + i : ℕ) : ℝ) + 1 ≤ ((60 + i) / 3 : ℕ) * 3 + 3 := by
    exact_mod_cast (by omega : 60 + i + 1 ≤ (60 + i) / 3 * 3 + 3)
  push_cast at this ⊢
  linarith

lemma qT'_le (i : ℕ) : (qT' i : ℝ) ≤ 3 / 40 * tT i := by
  unfold qT' tT
  have h := Nat.div_mul_le_self (60 + i) 40
  have : ((60 + i) / 40 : ℕ) * (40 : ℝ) ≤ 60 + i := by exact_mod_cast h
  linarith

lemma tT_succ_le' (i : ℕ) : 3 / 40 * tT (i + 1) ≤ qT' i + 1 := by
  unfold qT' tT
  have : ((60 + i : ℕ) : ℝ) + 1 ≤ ((60 + i) / 40 : ℕ) * 40 + 40 := by
    exact_mod_cast (by omega : 60 + i + 1 ≤ (60 + i) / 40 * 40 + 40)
  push_cast at this ⊢
  linarith

lemma tT_pos (i : ℕ) : 20 ≤ tT i := by
  unfold tT; have : (0 : ℝ) ≤ (i : ℝ) / 3 := by positivity
  linarith

/-- On the closed piece the local coordinates lie in `[0, 1]`. -/
lemma piece_coords {i : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (tT i) (tT (i + 1))) :
    0 ≤ x - qT i ∧ x - qT i ≤ 1 ∧ 0 ≤ 3 / 40 * x - qT' i ∧ 3 / 40 * x - qT' i ≤ 1 := by
  have h1 := qT_le i; have h2 := tT_succ_le i; have h3 := qT'_le i; have h4 := tT_succ_le' i
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### Derivatives -/

lemma hasDerivAt_PT (i : ℕ) (x : ℝ) : HasDerivAt (PT i) (FT i x + 37 / 40) x := by
  have :
    HasDerivAt (PT i)
      (74 * ((3 / 40) * (1 - (3 / 40 * x - qT' i)) + (3 / 40 * x - qT' i) * (-(3 / 40))) -
        37 / 40 * (1 * (1 - (x - qT i)) + (x - qT i) * (-1)))
      x := by
    unfold PT
    apply HasDerivAt.sub
    · apply HasDerivAt.const_mul
      apply HasDerivAt.mul
      · simpa using ((hasDerivAt_id x).const_mul (3 / 40)).sub_const (qT' i : ℝ)
      · simpa using (((hasDerivAt_id x).const_mul (3 / 40)).sub_const (qT' i : ℝ)).const_sub 1
    · apply HasDerivAt.const_mul
      apply HasDerivAt.mul
      · simpa using (hasDerivAt_id x).sub_const (qT i : ℝ)
      · simpa using ((hasDerivAt_id x).sub_const (qT i : ℝ)).const_sub 1
  convert this using 1
  unfold FT; ring

lemma hasDerivAt_G0 (v : ℝ) : HasDerivAt G0 (v * (1 - v) - 1 / 6) v := by
  have : HasDerivAt G0 ((-6 * v ^ 2 + 6 * v - 1) / 6) v := by
    have e : G0 = fun v => (-2 * v ^ 3 + 3 * v ^ 2 - v) / 6 := by funext v; unfold G0; ring
    rw [e]
    have :=
      ((((hasDerivAt_pow 3 v).const_mul (-2)).add ((hasDerivAt_pow 2 v).const_mul 3)).sub
            (hasDerivAt_id v)).div_const
        6
    exact this.congr_deriv (by norm_num; ring)
  exact this.congr_deriv (by ring)

lemma hasDerivAt_CT (i : ℕ) (x : ℝ) : HasDerivAt (CT i) (PT i x - Pbar) x := by
  have h1 :=
    (hasDerivAt_G0 (3 / 40 * x - qT' i)).comp x
      (((hasDerivAt_id x).const_mul (3 / 40)).sub_const (qT' i : ℝ))
  have h2 := (hasDerivAt_G0 (x - qT i)).comp x ((hasDerivAt_id x).sub_const (qT i : ℝ))
  have := (h1.const_mul (74 * 40 / 3)).sub (h2.const_mul (37 / 40))
  have e :
    CT i =
      (fun y => 74 * 40 / 3 * (G0 ∘ fun x => 3 / 40 * id x - (qT' i : ℝ)) y) - fun y =>
        37 / 40 * (G0 ∘ fun x => id x - (qT i : ℝ)) y :=
    by funext y; simp [CT, Function.comp]
  rw [e]
  exact this.congr_deriv (by unfold PT Pbar; ring)

/-! ### Continuity across breakpoints -/

lemma step3 (i : ℕ) :
    (qT (i + 1) : ℝ) = qT i ∨ ((qT (i + 1) : ℝ) = qT i + 1 ∧ tT (i + 1) = qT (i + 1)) := by
  unfold qT tT
  rcases
    (show
      (60 + (i + 1)) / 3 = (60 + i) / 3 ∨
        ((60 + (i + 1)) / 3 = (60 + i) / 3 + 1 ∧ 60 + (i + 1) = 3 * ((60 + (i + 1)) / 3))
      by omega) with
    h | ⟨h1, h2⟩
  · left; rw [h]
  · right
    refine ⟨by rw [h1]; push_cast; ring, ?_⟩
    have : ((60 + (i + 1) : ℕ) : ℝ) = 3 * (((60 + (i + 1)) / 3 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this ⊢; linarith

lemma step40 (i : ℕ) :
    (qT' (i + 1) : ℝ) = qT' i ∨
      ((qT' (i + 1) : ℝ) = qT' i + 1 ∧ 3 / 40 * tT (i + 1) = qT' (i + 1)) := by
  unfold qT' tT
  rcases
    (show
      (60 + (i + 1)) / 40 = (60 + i) / 40 ∨
        ((60 + (i + 1)) / 40 = (60 + i) / 40 + 1 ∧ 60 + (i + 1) = 40 * ((60 + (i + 1)) / 40))
      by omega) with
    h | ⟨h1, h2⟩
  · left; rw [h]
  · right
    refine ⟨by rw [h1]; push_cast; ring, ?_⟩
    have : ((60 + (i + 1) : ℕ) : ℝ) = 40 * (((60 + (i + 1)) / 40 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this ⊢; linarith

lemma PT_cont (i : ℕ) : PT i (tT (i + 1)) = PT (i + 1) (tT (i + 1)) := by
  unfold PT
  rcases step3 i with h3 | ⟨h3, e3⟩ <;> rcases step40 i with h4 | ⟨h4, e4⟩
  · rw [h3, h4]
  · rw [h3]; rw [h4] at e4 ⊢; rw [e4]; ring
  · rw [h4]; rw [h3] at e3 ⊢; rw [e3]; ring
  · rw [h3] at e3 ⊢; rw [h4] at e4 ⊢; rw [e3] at e4 ⊢; rw [e4]; ring

lemma CT_cont (i : ℕ) : CT i (tT (i + 1)) = CT (i + 1) (tT (i + 1)) := by
  unfold CT G0
  rcases step3 i with h3 | ⟨h3, e3⟩ <;> rcases step40 i with h4 | ⟨h4, e4⟩
  · rw [h3, h4]
  · rw [h3]; rw [h4] at e4 ⊢; rw [e4]; ring
  · rw [h4]; rw [h3] at e3 ⊢; rw [e3]; ring
  · rw [h3] at e3 ⊢; rw [h4] at e4 ⊢; rw [e3] at e4 ⊢; rw [e4]; ring

/-! ### The antiderivative on a piece -/

/-- `Φ_i(x) = P/x² + 2C/x³ - Pbar/x² + λ/x - (27/32)/x²`. -/
noncomputable def PhiT (i : ℕ) (x : ℝ) : ℝ :=
  PT i x / x ^ 2 + 2 * CT i x / x ^ 3 - Pbar / x ^ 2 + 37 / 40 / x - 27 / 32 / x ^ 2

lemma hasDerivAt_PhiT (i : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (PhiT i) (gT i x / x ^ 3 - 6 * CT i x / x ^ 4) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
  have d1 := (hasDerivAt_PT i x).div h2 (pow_ne_zero 2 hx0)
  have d2 := ((hasDerivAt_CT i x).const_mul 2).div h3 (pow_ne_zero 3 hx0)
  have d3 := (hasDerivAt_const x Pbar).div h2 (pow_ne_zero 2 hx0)
  have d4 := (hasDerivAt_const x (37 / 40 : ℝ)).div (hasDerivAt_id x) hx0
  have d5 := (hasDerivAt_const x (27 / 32 : ℝ)).div h2 (pow_ne_zero 2 hx0)
  have := (((d1.add d2).sub d3).add d4).sub d5
  have e :
    PhiT i =
      (((fun y => PT i y / y ^ 2) + fun y => 2 * CT i y / y ^ 3) - fun y => Pbar / y ^ 2) +
          (fun y => 37 / 40 / id y) -
        fun y => 27 / 32 / y ^ 2 :=
    by funext y; simp [PhiT]
  rw [e]
  refine this.congr_deriv ?_
  simp only [id]
  unfold gT FT PT
  field_simp
  ring

lemma continuous_gT (i : ℕ) : Continuous (gT i) := by unfold gT FT; fun_prop

lemma continuous_CT (i : ℕ) : Continuous (CT i) := by unfold CT G0; fun_prop

lemma continuousOn_div_pow {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : ContinuousOn (fun x => f x / x ^ k) (Set.uIcc a b) := by
  apply ContinuousOn.div hf.continuousOn (continuous_pow k).continuousOn
  intro x hx
  have : 0 < x := by rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1]
  positivity

lemma abs_G0_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : |G0 v| ≤ 1 / 60 := by
  unfold G0
  set w := v * (1 - v) with hw
  have hw0 : 0 ≤ w := mul_nonneg h0 (sub_nonneg.mpr h1)
  have e : (v * (1 - v) * (2 * v - 1)) ^ 2 = w ^ 2 * (1 - 4 * w) := by rw [hw]; ring
  have hfac : w ^ 2 * (1 - 4 * w) - 1 / 108 = -((w - 1 / 6) ^ 2 * (4 * w + 1 / 3)) := by ring
  have h2 : (v * (1 - v) * (2 * v - 1)) ^ 2 ≤ 1 / 100 := by
    rw [e]
    have : 0 ≤ (w - 1 / 6) ^ 2 * (4 * w + 1 / 3) := mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  rw [abs_le]
  constructor <;> nlinarith [h2]

lemma abs_CT_le {i : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (tT i) (tT (i + 1))) : |CT i x| ≤ 17 := by
  obtain ⟨h1, h2, h3, h4⟩ := piece_coords hx
  have a1 := abs_G0_le h3 h4
  have a2 := abs_G0_le h1 h2
  unfold CT
  rw [abs_le] at a1 a2 ⊢
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2]

/-- **One piece.** -/
lemma piece_bound (i : ℕ) :
    ∫ x in tT i..tT (i + 1), gT i x / x ^ 3 ≤
      PhiT i (tT (i + 1)) - PhiT i (tT i) + 34 * (1 / tT i ^ 3 - 1 / tT (i + 1) ^ 3) := by
  have ha := tT_pos i
  have hb := tT_pos (i + 1)
  have hab : tT i ≤ tT (i + 1) := by rw [tT_succ]; linarith
  have ha0 : (0 : ℝ) < tT i := by linarith
  have hb0 : (0 : ℝ) < tT (i + 1) := by linarith
  have hpos : ∀ x ∈ Set.uIcc (tT i) (tT (i + 1)), 0 < x := by
    intro x hx;
    rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1]
  have hint1 :
    IntervalIntegrable (fun x => gT i x / x ^ 3) MeasureTheory.volume (tT i) (tT (i + 1)) :=
    (continuousOn_div_pow (continuous_gT i) 3 ha0 hb0).intervalIntegrable
  have hint2 :
    IntervalIntegrable (fun x => CT i x / x ^ 4) MeasureTheory.volume (tT i) (tT (i + 1)) :=
    (continuousOn_div_pow (continuous_CT i) 4 ha0 hb0).intervalIntegrable
  have hftc :
    ∫ x in tT i..tT (i + 1), (gT i x / x ^ 3 - 6 * CT i x / x ^ 4) =
      PhiT i (tT (i + 1)) - PhiT i (tT i) := by
    apply integral_eq_sub_of_hasDerivAt
    · intro x hx; exact hasDerivAt_PhiT i (hpos x hx)
    · have :
        (fun x => gT i x / x ^ 3 - 6 * CT i x / x ^ 4) = fun x =>
          gT i x / x ^ 3 - 6 * (CT i x / x ^ 4) :=
        by funext x; ring
      rw [this]; exact hint1.sub (hint2.const_mul 6)
  have hA :
    IntervalIntegrable (fun x => gT i x / x ^ 3 - 6 * CT i x / x ^ 4) MeasureTheory.volume (tT i)
      (tT (i + 1)) := by
    have :
      (fun x => gT i x / x ^ 3 - 6 * CT i x / x ^ 4) = fun x =>
        gT i x / x ^ 3 - 6 * (CT i x / x ^ 4) :=
      by funext x; ring
    rw [this]; exact hint1.sub (hint2.const_mul 6)
  have hsplit :
    ∫ x in tT i..tT (i + 1), gT i x / x ^ 3 =
      (∫ x in tT i..tT (i + 1), (gT i x / x ^ 3 - 6 * CT i x / x ^ 4)) +
        6 * ∫ x in tT i..tT (i + 1), CT i x / x ^ 4 := by
    have e1 :
      ∫ x in tT i..tT (i + 1), gT i x / x ^ 3 =
        ∫ x in tT i..tT (i + 1), ((gT i x / x ^ 3 - 6 * CT i x / x ^ 4) + 6 * (CT i x / x ^ 4)) :=
      by congr 1; funext x; ring
    rw [e1, intervalIntegral.integral_add hA (hint2.const_mul 6),
      intervalIntegral.integral_const_mul]
      -- the bound on `∫ C/x⁴`
  have hC :
    ∫ x in tT i..tT (i + 1), CT i x / x ^ 4 ≤ 17 / 3 * (1 / tT i ^ 3 - 1 / tT (i + 1) ^ 3) := by
    have hmono : ∫ x in tT i..tT (i + 1), CT i x / x ^ 4 ≤ ∫ x in tT i..tT (i + 1), 17 / x ^ 4 := by
      apply intervalIntegral.integral_mono_on hab hint2
      · exact (continuousOn_div_pow continuous_const 4 ha0 hb0).intervalIntegrable
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have := abs_CT_le hx
        rw [abs_le] at this
        exact div_le_div_of_nonneg_right this.2 (by positivity)
    have hval :
      ∫ x in tT i..tT (i + 1), 17 / x ^ 4 = 17 / 3 * (1 / tT i ^ 3 - 1 / tT (i + 1) ^ 3) := by
      rw [integral_eq_sub_of_hasDerivAt (f := fun x => -(17 / 3) / x ^ 3)]
      · field_simp; ring
      · intro x hx
        have hx0 := hpos x hx
        have :=
          ((hasDerivAt_const x (-(17 / 3) : ℝ)).div (hasDerivAt_pow 3 x) (pow_ne_zero 3 hx0.ne'))
        refine this.congr_deriv ?_
        norm_num
        field_simp
      · exact (continuousOn_div_pow continuous_const 4 ha0 hb0).intervalIntegrable
    linarith
  rw [hsplit, hftc]
  linarith

lemma PhiT_cont (i : ℕ) : PhiT i (tT (i + 1)) = PhiT (i + 1) (tT (i + 1)) := by
  unfold PhiT;
  rw [PT_cont, CT_cont]

lemma tele_phi (N : ℕ) :
    ∑ i ∈ range N, (PhiT i (tT (i + 1)) - PhiT i (tT i)) = PhiT N (tT N) - PhiT 0 (tT 0) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, PhiT_cont]; ring

lemma tele_cube (N : ℕ) :
    ∑ i ∈ range N, 34 * (1 / tT i ^ 3 - 1 / tT (i + 1) ^ 3) =
      34 * (1 / tT 0 ^ 3 - 1 / tT N ^ 3) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

/-- **The tail sum**: `∑_i ∫_{t_i}^{t_{i+1}} g_i/x³ ≤ -6843153/128000000 ≈ -0.05346`. -/
theorem tail_sum_le :
    ∑ i ∈ range 1140, ∫ x in tT i..tT (i + 1), gT i x / x ^ 3 ≤ -6843153 / 128000000 := by
  have h := Finset.sum_le_sum fun i (_ : i ∈ range 1140) => piece_bound i
  have tele1 := tele_phi 1140
  have tele2 := tele_cube 1140
  rw [Finset.sum_add_distrib, tele1, tele2] at h
  refine h.trans (le_of_eq ?_)
  have e0 : tT 0 = 20 := by unfold tT; norm_num
  have e1 : tT 1140 = 400 := by unfold tT; norm_num
  have q0 : qT 0 = 20 := by decide
  have q0' : qT' 0 = 1 := by decide
  have q1 : qT 1140 = 400 := by decide
  have q1' : qT' 1140 = 30 := by decide
  rw [e0, e1]
  unfold PhiT PT CT G0 Pbar
  rw [q0, q0', q1, q1']
  norm_num

end Zeta5Irrational
