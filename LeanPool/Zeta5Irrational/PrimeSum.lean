/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.NumberTheory.Chebyshev
import LeanPool.Zeta5Irrational.PNT
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Weighted prime sums via the prime number theorem

`∑_{a < p ≤ b} p log p = b θ(b) - a θ(a) - ∫_a^b θ` (Abel summation), and with `θ(x) ~ x`
this gives `∑_{K/d < p ≤ K/c} p log p = K² (1/c² - 1/d²)/2 + o(K²)`.
-/

public section

open Finset Filter Topology MeasureTheory Set Real Asymptotics

namespace Zeta5Irrational

/-- `c p = log p` for primes, `0` otherwise. -/
@[expose] noncomputable def cPrime (k : ℕ) : ℝ :=
  if k.Prime then Real.log k else 0

lemma theta_eq_sum_cPrime (t : ℝ) : Chebyshev.theta t = ∑ k ∈ Icc 0 ⌊t⌋₊, cPrime k := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

/-- The weighted prime sum `∑_{a < p ≤ b} p log p` (as a sum over integers `k` with
`⌊a⌋₊ < k ≤ ⌊b⌋₊`). -/
@[expose] noncomputable def wsum (a b : ℝ) : ℝ :=
  ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (k : ℝ) * cPrime k

/-- Abel summation for the weighted prime sum. -/
lemma wsum_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    wsum a b =
      b * Chebyshev.theta b - a * Chebyshev.theta a - ∫ t in Ioc a b, Chebyshev.theta t := by
  unfold wsum
  have hd : deriv (fun t : ℝ => t) = fun _ => 1 := by funext t; simp
  have h :=
    sum_mul_eq_sub_sub_integral_mul cPrime (f := fun t : ℝ => t) ha hab
      (fun t _ => differentiableAt_id)
      (by rw [hd]; exact integrableOn_const measure_Icc_lt_top.ne)
  simp only [hd, one_mul] at h
  rw [h, ← theta_eq_sum_cPrime, ← theta_eq_sum_cPrime]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  exact (theta_eq_sum_cPrime t).symm

/-- The prime number theorem in `ε`-form: `|θ(y) - y| ≤ ε y` for all large `y`. -/
lemma theta_eventually_close {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, |Chebyshev.theta y - y| ≤ ε * y := by
  have h := theta_asymptotic
  rw [IsEquivalent, IsLittleO] at h
  have h2 := h hε
  rw [IsBigOWith] at h2
  filter_upwards [h2, eventually_ge_atTop 0] with y hy hy0
  simp only [Pi.sub_apply, id, Real.norm_eq_abs, abs_of_nonneg hy0] at hy
  exact hy

/-- `∫_a^b θ` is close to `(b² - a²)/2` when `θ` is close to the identity on `[a, b]`. -/
lemma integral_theta_bounds {a b ε : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ y ∈ Icc a b, |Chebyshev.theta y - y| ≤ ε * y) :
    |(∫ t in Ioc a b, Chebyshev.theta t) - (b ^ 2 - a ^ 2) / 2| ≤ ε * (b ^ 2 - a ^ 2) / 2 := by
  have hint : IntegrableOn Chebyshev.theta (Ioc a b) :=
    (Chebyshev.theta_mono.intervalIntegrable (μ := volume) (a := a) (b := b)).1
  have hsub : IntegrableOn (fun t : ℝ => t) (Ioc a b) :=
    (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hid : ∫ t in Ioc a b, t = (b ^ 2 - a ^ 2) / 2 := by
    rw [← intervalIntegral.integral_of_le hab, integral_id]
  have hε : IntegrableOn (fun t : ℝ => ε * t) (Ioc a b) := hsub.const_mul ε
  calc
    |(∫ t in Ioc a b, Chebyshev.theta t) - (b ^ 2 - a ^ 2) / 2| =
        ‖∫ t in Ioc a b, (Chebyshev.theta t - t)‖ :=
      by rw [← hid, ← integral_sub hint hsub, Real.norm_eq_abs]
    _ ≤ ∫ t in Ioc a b, ‖Chebyshev.theta t - t‖ := (norm_integral_le_integral_norm _)
    _ ≤ ∫ t in Ioc a b, ε * t := by
      refine setIntegral_mono_on (hint.sub hsub).norm hε measurableSet_Ioc fun t ht => ?_
      rw [Real.norm_eq_abs]
      exact h t (Ioc_subset_Icc_self ht)
    _ = ε * (b ^ 2 - a ^ 2) / 2 := by rw [integral_const_mul, hid]; ring

/-- The bound `|wsum a b - (b² - a²)/2| ≤ 2 η b²` when `|θ(y) - y| ≤ η y` on `[a, b]`. -/
lemma wsum_close {a b η : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (_hη : 0 ≤ η)
    (h : ∀ y ∈ Icc a b, |Chebyshev.theta y - y| ≤ η * y) :
    |wsum a b - (b ^ 2 - a ^ 2) / 2| ≤ 2 * η * b ^ 2 := by
  rw [wsum_eq ha hab]
  have h1 := h b ⟨hab, le_rfl⟩
  have h2 := h a ⟨le_rfl, hab⟩
  have h3 := integral_theta_bounds ha hab h
  have hb : 0 ≤ b := ha.trans hab
  have e1 : |b * Chebyshev.theta b - b ^ 2| ≤ η * b ^ 2 := by
    rw [show b * Chebyshev.theta b - b ^ 2 = b * (Chebyshev.theta b - b) by ring, abs_mul,
      abs_of_nonneg hb]
    nlinarith
  have e2 : |a * Chebyshev.theta a - a ^ 2| ≤ η * a ^ 2 := by
    rw [show a * Chebyshev.theta a - a ^ 2 = a * (Chebyshev.theta a - a) by ring, abs_mul,
      abs_of_nonneg ha]
    nlinarith
  have ha2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  rw [abs_le] at e1 e2 h3 ⊢
  constructor <;> nlinarith

/-- `∑_{K/d < p ≤ K/c} p log p / K² → (1/c² - 1/d²)/2`. -/
theorem wsum_tendsto {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Tendsto (fun K : ℝ => wsum (K / d) (K / c) / K ^ 2) atTop (𝓝 ((1 / c ^ 2 - 1 / d ^ 2) / 2)) :=
  by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hd : 0 < d := hc.trans hcd
  set η := ε * c ^ 2 / 8 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (theta_eventually_close hη)
  refine ⟨max (d * Y₀) 1, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := le_trans (le_max_right _ _) hK
  have hK0 : 0 < K := by linarith
  have hKY : d * Y₀ ≤ K := le_trans (le_max_left _ _) hK
  have ha : 0 ≤ K / d := by positivity
  have hab : K / d ≤ K / c := div_le_div_of_nonneg_left hK0.le hc hcd.le
  have hbound :=
    wsum_close ha hab hη.le
      (fun y hy =>
        hY₀ y
          (by
            have : Y₀ ≤ K / d := by rw [le_div_iff₀ hd]; linarith
            linarith [hy.1]))
  rw [Real.dist_eq]
  have e :
    wsum (K / d) (K / c) / K ^ 2 - (1 / c ^ 2 - 1 / d ^ 2) / 2 =
      (wsum (K / d) (K / c) - ((K / c) ^ 2 - (K / d) ^ 2) / 2) / K ^ 2 :=
    by field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < K ^ 2), div_lt_iff₀ (by positivity)]
  calc
    |wsum (K / d) (K / c) - ((K / c) ^ 2 - (K / d) ^ 2) / 2| ≤ 2 * η * (K / c) ^ 2 := hbound
    _ = ε * K ^ 2 / 4 := by rw [hη_def]; field_simp; ring
    _ < ε * K ^ 2 := by
      have : 0 < ε * K ^ 2 := by positivity
      linarith

end Zeta5Irrational
