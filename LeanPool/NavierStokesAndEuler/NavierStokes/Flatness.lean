/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Scalar flatness and fixed power losses

This file isolates the scalar asymptotic argument used in Lemmas 11.2--11.5
of the candidate manuscript. It proves neither the asserted bounds for physical
jets nor the existence, compatibility, or smooth extension of those jets.

All powers here have natural exponents. Constants and neighborhoods may depend
on the requested power, as they do in a flatness statement.
-/

open Filter Topology

namespace NavierStokes.Flatness

variable {α : Type*} {l : Filter α} {q f g : α → ℝ}

/-- Along `l`, `f` is eventually bounded by a constant times every natural
power of the absolute value of the scale `q`. -/
def PowerFlat (l : Filter α) (q f : α → ℝ) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, |f x| ≤ C * |q x| ^ n

/-- An exact scalar estimate: `n + loss` powers of smallness absorb `loss`
powers in a nonzero denominator. No assumption that the scale is small is
needed for this algebraic step. -/
theorem fixed_power_loss_bound {x scale C : ℝ} {n loss : ℕ}
    (hscale : scale ≠ 0) (hx : |x| ≤ C * |scale| ^ (n + loss)) :
    |x / scale ^ loss| ≤ C * |scale| ^ n := by
  rw [abs_div, abs_pow]
  apply (div_le_iff₀ (pow_pos (abs_pos.mpr hscale) loss)).2
  simpa only [pow_add, mul_assoc] using hx

/-- Arbitrary power decay persists after any fixed inverse-power loss. -/
theorem PowerFlat.div_pow (hf : PowerFlat l q f)
    (hq : ∀ᶠ x in l, q x ≠ 0) (loss : ℕ) :
    PowerFlat l q (fun x => f x / q x ^ loss) := by
  intro n
  obtain ⟨C, hC, hbound⟩ := hf (n + loss)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hq, hbound] with x hx hfx
  exact fixed_power_loss_bound hx hfx

/-- Flat estimates are stable under finite addition. -/
theorem PowerFlat.add (hf : PowerFlat l q f) (hg : PowerFlat l q g) :
    PowerFlat l q (fun x => f x + g x) := by
  intro n
  obtain ⟨C, hC, hfb⟩ := hf n
  obtain ⟨D, hD, hgb⟩ := hg n
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  filter_upwards [hfb, hgb] with x hfx hgx
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ C * |q x| ^ n + D * |q x| ^ n := add_le_add hfx hgx
    _ = (C + D) * |q x| ^ n := (add_mul _ _ _).symm

/-- Flat estimates are stable under multiplication. Only boundedness of the
second factor, the `n = 0` case of its flatness, is used. -/
theorem PowerFlat.mul (hf : PowerFlat l q f) (hg : PowerFlat l q g) :
    PowerFlat l q (fun x => f x * g x) := by
  intro n
  obtain ⟨C, hC, hfb⟩ := hf n
  obtain ⟨D, hD, hgb⟩ := hg 0
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  filter_upwards [hfb, hgb] with x hfx hgx
  have hgx' : |g x| ≤ D := by simpa only [pow_zero, mul_one] using hgx
  calc
    |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (C * |q x| ^ n) * D :=
      mul_le_mul hfx hgx' (abs_nonneg _) (mul_nonneg hC (pow_nonneg (abs_nonneg _) _))
    _ = (C * D) * |q x| ^ n := by ring

/-- A flat scalar times a scalar with a fixed power loss remains flat. This
models one factor in the residual product estimates, provided the stated
bounds have already been established for the actual factors. -/
theorem PowerFlat.mul_of_power_bound (hf : PowerFlat l q f)
    (hq : ∀ᶠ x in l, q x ≠ 0) (loss : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hg : ∀ᶠ x in l, |g x| ≤ D / |q x| ^ loss) :
    PowerFlat l q (fun x => f x * g x) := by
  intro n
  obtain ⟨C, hC, hfb⟩ := hf (n + loss)
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  filter_upwards [hq, hfb, hg] with x hqx hfx hgx
  have hden : |q x| ^ loss ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr hqx)
  calc
    |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (C * |q x| ^ (n + loss)) * (D / |q x| ^ loss) :=
      mul_le_mul hfx hgx (abs_nonneg _)
        (mul_nonneg hC (pow_nonneg (abs_nonneg _) _))
    _ = ((C * D) * |q x| ^ n) * (|q x| ^ loss / |q x| ^ loss) := by
      rw [pow_add]
      ring
    _ = (C * D) * |q x| ^ n := by rw [div_self hden, mul_one]

/-- Stage bounds with unbounded natural exponents imply flatness even after
subtracting a fixed natural loss. Each stage has its own constant and eventual
neighborhood; no uniformity of these quantities in the stage is assumed. -/
theorem powerFlat_of_stage_bounds {exponent : ℕ → ℕ} (loss : ℕ)
    (hexponent : ∀ n : ℕ, ∃ j : ℕ, n ≤ exponent j)
    (hq : ∀ᶠ x in l, |q x| ≤ 1)
    (hstage : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x in l, |f x| ≤ C * |q x| ^ (exponent j - loss)) :
    PowerFlat l q f := by
  intro n
  obtain ⟨j, hj⟩ := hexponent (n + loss)
  obtain ⟨C, hC, hb⟩ := hstage j
  have hn : n ≤ exponent j - loss := Nat.le_sub_of_add_le hj
  refine ⟨C, hC, ?_⟩
  filter_upwards [hq, hb] with x hqx hfx
  exact hfx.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (abs_nonneg _) hqx hn) hC)

/-- Flatness gives an actual zero limit when the scale tends to zero.
This is a scalar limit theorem, not a theorem about differentiability. -/
theorem PowerFlat.tendsto_zero (hf : PowerFlat l q f)
    (hq : Tendsto q l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := hf 1
  apply squeeze_zero_norm' (f := f) (a := fun x => C * |q x|)
  · simpa only [Real.norm_eq_abs, pow_one] using hb
  · simpa only [abs_zero, mul_zero] using hq.abs.const_mul C

/-- The zero limit survives every fixed inverse-power loss. -/
theorem PowerFlat.div_pow_tendsto_zero (hf : PowerFlat l q f)
    (hq : Tendsto q l (𝓝 0)) (hq_ne : ∀ᶠ x in l, q x ≠ 0) (loss : ℕ) :
    Tendsto (fun x => f x / q x ^ loss) l (𝓝 0) :=
  (hf.div_pow hq_ne loss).tendsto_zero hq

end NavierStokes.Flatness
