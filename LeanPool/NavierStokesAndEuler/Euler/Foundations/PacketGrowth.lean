/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
public import LeanPool.NavierStokesAndEuler.ForMathlib.ElaborationShortcuts

/-!
Order estimates for the scalar ODE occurring in equation (30) of the proposed
Euler packet argument.  These are finite-dimensional ODE results only.
-/

@[expose] public section

-- Numeric exponents elaborate as natural numbers at once: left to the default instance,
-- every `x ^ 2` of a long statement stays pending and is retried after each later binder.
local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace EulerPacketGrowth

open Set Filter Real
open scoped Topology

private theorem eventually_nonneg_right
    {f : ℝ → ℝ} {x d : ℝ} (hd : HasDerivAt f d x)
    (hx : 0 ≤ f x) (hboundary : f x = 0 → 0 < d) :
    ∀ᶠ y in 𝓝[>] x, 0 ≤ f y := by
  rcases hx.eq_or_lt with hx | hx
  · have hpos : 0 < d := hboundary hx.symm
    have hslope : ∀ᶠ y in 𝓝[>] x, 0 < slope f x y :=
      (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)) (Ioi_mem_nhds hpos)
    filter_upwards [hslope, self_mem_nhdsWithin] with y hy hxy
    rw [slope_def_field, ← hx] at hy
    have : 0 < y - x := sub_pos.mpr hxy
    simpa only [ge_iff_le, sub_zero] using ((div_pos_iff_of_pos_right this).mp hy).le
  · exact ((hd.continuousAt.eventually (Ioi_mem_nhds hx)).filter_mono
      nhdsWithin_le_nhds).mono fun _ hy => hy.le

/-- Two differentiable functions remain nonnegative if every boundary point
of the nonnegative quadrant has a strictly inward derivative. -/
theorem pair_nonneg_of_strict_boundary
    {f g df dg : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (df t) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (dg t) t)
    (hf0 : 0 ≤ f 0) (hg0 : 0 ≤ g 0)
    (hboundary : ∀ t ∈ Ico 0 T, 0 ≤ f t → 0 ≤ g t →
      (f t = 0 → 0 < df t) ∧ (g t = 0 → 0 < dg t)) :
    ∀ t ∈ Icc 0 T, 0 ≤ f t ∧ 0 ≤ g t := by
  let s : Set ℝ := {t | 0 ≤ f t ∧ 0 ≤ g t}
  have hfc : ContinuousOn f (Icc 0 T) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc 0 T) :=
    fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hs : IsClosed (s ∩ Icc 0 T) := by
    have hpair : ContinuousOn (fun t => (f t, g t)) (Icc 0 T) := hfc.prodMk hgc
    have hc : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} :=
      (isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_const continuous_snd)
    simpa only [inter_comm, preimage_ofPred_eq] using
      hpair.preimage_isClosed_of_isClosed isClosed_Icc hc
  apply hs.Icc_subset_of_forall_exists_gt ⟨hf0, hg0⟩
  intro t ht y hy
  have hti : t ∈ Icc 0 T := Ico_subset_Icc_self ht.2
  have hb := hboundary t ht.2 ht.1.1 ht.1.2
  have he := (eventually_nonneg_right (hf t hti) ht.1.1 hb.1).and
    (eventually_nonneg_right (hg t hti) ht.1.2 hb.2)
  exact nonempty_of_mem (inter_mem he (Ioc_mem_nhdsGT hy))

/-- Positivity for a cooperative pair of differential inequalities.  The
nonnegative quadrant is invariant; positivity is not an additional hypothesis. -/
theorem cooperative_nonneg_of_bounded
    {f g df dg a b : ℝ → ℝ} {T K : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (df t) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (dg t) t)
    (hf0 : 0 ≤ f 0) (hg0 : 0 ≤ g 0)
    (ha : ∀ t ∈ Icc 0 T, 0 ≤ a t ∧ a t ≤ K)
    (hb : ∀ t ∈ Icc 0 T, 0 ≤ b t ∧ b t ≤ K)
    (hdf : ∀ t ∈ Icc 0 T, a t * g t ≤ df t)
    (hdg : ∀ t ∈ Icc 0 T, b t * f t ≤ dg t) :
    ∀ t ∈ Icc 0 T, 0 ≤ f t ∧ 0 ≤ g t := by
  have hpert : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Icc 0 T,
      0 ≤ f t + ε * exp ((K + 1) * t) ∧
        0 ≤ g t + ε * exp ((K + 1) * t) := by
    intro ε hε
    have hed : ∀ t : ℝ, HasDerivAt (fun s => ε * exp ((K + 1) * s))
        ((K + 1) * ε * exp ((K + 1) * t)) t := by
      intro t
      apply ((((hasDerivAt_id t).const_mul (K + 1)).exp).const_mul ε).congr_deriv
      dsimp only [id_eq]
      ring
    apply pair_nonneg_of_strict_boundary
      (fun t ht => (hf t ht).add (hed t))
      (fun t ht => (hg t ht).add (hed t))
    · simpa only [Pi.add_apply, mul_zero, exp_zero, mul_one] using add_nonneg hf0 hε.le
    · simpa only [Pi.add_apply, mul_zero, exp_zero, mul_one] using add_nonneg hg0 hε.le
    · intro t ht hft hgt
      dsimp only [Pi.add_apply] at hft hgt ⊢
      have hti : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      have hat := ha t hti
      have hbt := hb t hti
      have hεE : 0 < ε * exp ((K + 1) * t) := mul_pos hε (exp_pos _)
      constructor
      · intro _
        have hmul : a t * (-(ε * exp ((K + 1) * t))) ≤ a t * g t :=
          mul_le_mul_of_nonneg_left (by linarith only [hgt]) hat.1
        have hpos : 0 < (K + 1 - a t) * (ε * exp ((K + 1) * t)) :=
          mul_pos (by linarith only [hat, hat.2]) hεE
        linarith only [hmul, hpos, hdf, hti, hdf t hti]
      · intro _
        have hmul : b t * (-(ε * exp ((K + 1) * t))) ≤ b t * f t :=
          mul_le_mul_of_nonneg_left (by linarith only [hft]) hbt.1
        have hpos : 0 < (K + 1 - b t) * (ε * exp ((K + 1) * t)) :=
          mul_pos (by linarith only [hbt, hbt.2]) hεE
        linarith only [hmul, hpos, hdg, hti, hdg t hti]
  intro t ht
  have hE : exp ((K + 1) * t) ≠ 0 := ne_of_gt (exp_pos _)
  constructor
  · apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [div_mul_cancel₀ _ hE] using
      (hpert (ε / exp ((K + 1) * t)) (div_pos hε (exp_pos _)) t ht).1
  · apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [div_mul_cancel₀ _ hE] using
      (hpert (ε / exp ((K + 1) * t)) (div_pos hε (exp_pos _)) t ht).2

/-- A specialization of cooperative positivity with coefficient bound `2`. -/
theorem cooperative_nonneg
    {f g df dg a b : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (df t) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (dg t) t)
    (hf0 : 0 ≤ f 0) (hg0 : 0 ≤ g 0)
    (ha : ∀ t ∈ Icc 0 T, 0 ≤ a t ∧ a t ≤ 2)
    (hb : ∀ t ∈ Icc 0 T, 0 ≤ b t ∧ b t ≤ 2)
    (hdf : ∀ t ∈ Icc 0 T, a t * g t ≤ df t)
    (hdg : ∀ t ∈ Icc 0 T, b t * f t ≤ dg t) :
    ∀ t ∈ Icc 0 T, 0 ≤ f t ∧ 0 ≤ g t :=
  cooperative_nonneg_of_bounded hf hg hf0 hg0 ha hb hdf hdg

/-- The flux system `V' = F/D`, `F' = c V` dominates the constant-coefficient
system with `D = 2` and `c = 1`.  In particular, its solution is positive and
has a hyperbolic-cosine lower bound, for every nonnegative initial flux. -/
theorem cosh_lower_of_flux_system
    {V F D c : ℝ → ℝ} {T : ℝ}
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (F t / D t) t)
    (hF : ∀ t ∈ Icc 0 T, HasDerivAt F (c t * V t) t)
    (hV0 : V 0 = 1) (hF0 : 0 ≤ F 0)
    (hD : ∀ t ∈ Icc 0 T, 1 ≤ D t ∧ D t ≤ 2)
    (hc : ∀ t ∈ Icc 0 T, 1 ≤ c t ∧ c t ≤ 2) :
    ∀ t ∈ Icc 0 T,
      cosh (t / √2) ≤ V t ∧ √2 * sinh (t / √2) ≤ F t := by
  have hspos : (0 : ℝ) < √2 := by positivity
  have hsne : (√2 : ℝ) ≠ 0 := ne_of_gt hspos
  have hsq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcd : ∀ t : ℝ, HasDerivAt (fun s => cosh (s / √2))
      (sinh (t / √2) / √2) t := by
    intro t
    convert (((hasDerivAt_id t).div_const (√2 : ℝ)).cosh) using 1 <;> simp only [div_eq_mul_inv,
        id_eq, one_mul]
  have hsd : ∀ t : ℝ, HasDerivAt (fun s => √2 * sinh (s / √2))
      (cosh (t / √2)) t := by
    intro t
    apply ((((hasDerivAt_id t).div_const (√2 : ℝ)).sinh).const_mul (√2 : ℝ)).congr_deriv
    dsimp only [id_eq]
    field_simp
  have hcompare := cooperative_nonneg
    (f := fun t => V t - cosh (t / √2))
    (g := fun t => F t - √2 * sinh (t / √2))
    (df := fun t => F t / D t - sinh (t / √2) / √2)
    (dg := fun t => c t * V t - cosh (t / √2))
    (a := fun t => 1 / D t) (b := c)
    (fun t ht => (hV t ht).sub (hcd t))
    (fun t ht => (hF t ht).sub (hsd t))
    (by simp [hV0]) (by simpa only [zero_div, sinh_zero, mul_zero, sub_zero] using hF0)
    (fun t ht => by
      have hdt := hD t ht
      have hdpos : 0 < D t := lt_of_lt_of_le zero_lt_one hdt.1
      constructor
      · positivity
      · have : 1 / D t ≤ 1 := (div_le_one hdpos).mpr hdt.1
        linarith only [this])
    (fun t ht => ⟨le_trans zero_le_one (hc t ht).1, (hc t ht).2⟩)
    (fun t ht => by
      have hdt := hD t ht
      have hdpos : 0 < D t := lt_of_lt_of_le zero_lt_one hdt.1
      have hsinh : 0 ≤ sinh (t / √2) :=
        sinh_nonneg_iff.mpr (div_nonneg ht.1 hspos.le)
      have hinv : 1 / (√2 : ℝ) ≤ √2 / D t := by
        apply (div_le_div_iff₀ hspos hdpos).mpr
        linarith only [hsq, hdt, hdt.2]
      have hmul := mul_nonneg hsinh (sub_nonneg.mpr hinv)
      simp only [div_eq_mul_inv] at hmul ⊢
      linarith only [hmul])
    (fun t ht => by
      have hmul := mul_nonneg (sub_nonneg.mpr (hc t ht).1)
        (cosh_pos (t / √2)).le
      linarith only [hmul])
  intro t ht
  exact ⟨sub_nonneg.mp (hcompare t ht).1, sub_nonneg.mp (hcompare t ht).2⟩

/-- The precise cosine-hyperbolic growth comparison used after equation (30).
The initial derivative is allowed to be arbitrarily large and nonnegative. -/
theorem equation30_cosh_lower
    {β T : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 1 / 2) (hT : 0 ≤ T)
    (hscale : β * T ^ 2 ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t ∈ Icc 0 T,
      cosh (t / √2) ≤ V t ∧
      √2 * sinh (t / √2) ≤ (1 + (β * t ^ 2) ^ 2) * V₁ t := by
  have hcoeff : ∀ t ∈ Icc 0 T,
      0 ≤ β * t ^ 2 ∧ β * t ^ 2 ≤ 1 := by
    intro t ht
    have ht2 : t ^ 2 ≤ T ^ 2 := (sq_le_sq₀ ht.1 hT).mpr ht.2
    exact ⟨mul_nonneg hβ (sq_nonneg _),
      le_trans (mul_le_mul_of_nonneg_left ht2 hβ) hscale⟩
  apply cosh_lower_of_flux_system
    (D := fun t => 1 + (β * t ^ 2) ^ 2)
    (c := fun t => 2 * (1 - β * (β * t ^ 2)))
    (F := fun t => (1 + (β * t ^ 2) ^ 2) * V₁ t)
  · intro t ht
    apply (hV t ht).congr_deriv
    have hD : 1 + (β * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
  · exact hflux
  · exact hV0
  · simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
      one_mul] using hV₁0
  · intro t ht
    obtain ⟨hl, hu⟩ := hcoeff t ht
    constructor
    · exact le_add_of_nonneg_right (sq_nonneg _)
    · have hs : (β * t ^ 2) ^ 2 ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ hl hu 2
      linarith only [hs]
  · intro t ht
    obtain ⟨hl, hu⟩ := hcoeff t ht
    have hp : 0 ≤ β * (β * t ^ 2) := mul_nonneg hβ hl
    have hq : β * (β * t ^ 2) ≤ β := mul_le_of_le_one_right hβ hu
    constructor <;> linarith only [hβsmall, hq, hp]

/-- Equation (30) gives positivity and a nonnegative derivative from the
initial conditions alone, throughout the pre-inversion interval. -/
theorem equation30_positive
    {β T : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 1 / 2) (hT : 0 ≤ T)
    (hscale : β * T ^ 2 ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t ∈ Icc 0 T, 0 < V t ∧ 0 ≤ V₁ t := by
  intro t ht
  obtain ⟨hcosh, hfluxlower⟩ :=
    equation30_cosh_lower hβ hβsmall hT hscale hV hflux hV0 hV₁0 t ht
  constructor
  · exact lt_of_lt_of_le (cosh_pos _) hcosh
  · have hsinh : 0 ≤ √2 * sinh (t / √2) :=
      mul_nonneg (sqrt_nonneg _)
        (sinh_nonneg_iff.mpr (div_nonneg ht.1 (sqrt_nonneg _)))
    have hprod : 0 ≤ (1 + (β * t ^ 2) ^ 2) * V₁ t := hsinh.trans hfluxlower
    exact nonneg_of_mul_nonneg_right hprod (by positivity)

/-- A convenient pure exponential consequence of the hyperbolic-cosine bound. -/
theorem exp_quarter_le_cosh {t : ℝ} (ht : 4 ≤ t) :
    exp (t / 4) ≤ cosh (t / √2) := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hspos : (0 : ℝ) < √2 := by positivity
  have hsq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsle : (√2 : ℝ) ≤ 2 := by nlinarith only [hsq, hspos, sqrt_nonneg (2 : ℝ)]
  have hexp : 2 ≤ exp (t / 4) := by linarith only [ht, add_one_le_exp (t / 4)]
  have harg : t / 4 + t / 4 ≤ t / √2 := by
    apply (le_div_iff₀ hspos).mpr
    have := mul_le_mul_of_nonneg_left hsle ht0
    linarith only [this]
  have hprod : exp (t / 4) * exp (t / 4) ≤ exp (t / √2) := by
    rw [← exp_add]
    exact exp_le_exp.mpr harg
  rw [cosh_eq]
  nlinarith only [hexp, hprod, exp_pos (-(t / √2))]

/-- At `T = 1 / sqrt β`, equation (30) amplifies by at least
`exp (1 / (4 sqrt β))`, uniformly over every nonnegative initial derivative. -/
theorem equation30_endpoint_exponential
    {β : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 1 / 16)
    (hV : ∀ t ∈ Icc 0 (1 / √β), HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 (1 / √β),
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    exp (1 / (4 * √β)) ≤ V (1 / √β) := by
  have hspos : 0 < √β := sqrt_pos.mpr hβ
  have hsne : √β ≠ 0 := ne_of_gt hspos
  have hsq : (√β) ^ 2 = β := sq_sqrt hβ.le
  have hT : 0 ≤ 1 / √β := by positivity
  have hscale : β * (1 / √β) ^ 2 ≤ 1 := by
    have : β * (1 / √β) ^ 2 = 1 := by
      field_simp
      exact hsq.symm
    exact this.le
  have hT4 : 4 ≤ 1 / √β := by
    apply (le_div_iff₀ hspos).mpr
    nlinarith only [hsq, hβ, hβsmall, hspos]
  have hg := (equation30_cosh_lower hβ.le (by linarith) hT hscale hV hflux hV0 hV₁0
    (1 / √β) ⟨hT, le_rfl⟩).1
  have he := exp_quarter_le_cosh hT4
  have heq : (1 / √β) / 4 = 1 / (4 * √β) := by ring
  rw [heq] at he
  exact he.trans hg

/-- Nonnegative initial values give componentwise lower bounds for a
cooperative flux system, with no smallness restriction on the coefficients. -/
theorem flux_lower_initial
    {V F D c : ℝ → ℝ} {T K : ℝ}
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (F t / D t) t)
    (hF : ∀ t ∈ Icc 0 T, HasDerivAt F (c t * V t) t)
    (hV0 : 0 ≤ V 0) (hF0 : 0 ≤ F 0)
    (hD : ∀ t ∈ Icc 0 T, 0 ≤ 1 / D t ∧ 1 / D t ≤ K)
    (hc : ∀ t ∈ Icc 0 T, 0 ≤ c t ∧ c t ≤ K) :
    ∀ t ∈ Icc 0 T, V 0 ≤ V t ∧ F 0 ≤ F t := by
  have hp := cooperative_nonneg_of_bounded
    (f := fun t => V t - V 0) (g := fun t => F t - F 0)
    (df := fun t => F t / D t) (dg := fun t => c t * V t)
    (a := fun t => 1 / D t) (b := c)
    (fun t ht => (hV t ht).sub_const (V 0))
    (fun t ht => (hF t ht).sub_const (F 0))
    (by simp only [sub_self, Std.le_refl]) (by simp only [sub_self, Std.le_refl]) hD hc
    (fun t ht => by
      have hp := mul_nonneg (hD t ht).1 hF0
      simp only [div_eq_mul_inv] at hp ⊢
      linarith only [hp])
    (fun t ht => by linarith only [hc, ht, hV0, mul_nonneg (hc t ht).1 hV0])
  intro t ht
  exact ⟨sub_nonneg.mp (hp t ht).1, sub_nonneg.mp (hp t ht).2⟩

/-- The inverted equation preserves positive `f` and negative `f'` when it is
integrated from `y = 1` towards smaller nonnegative `y`. -/
theorem inversion_positive
    {β a : ℝ} {f f₁ : ℝ → ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 1) (ha : 0 ≤ a)
    (hf : ∀ y ∈ Icc a 1, HasDerivAt f (f₁ y) y)
    (hflux : ∀ y ∈ Icc a 1, HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / β - 2 * y ^ 2) * f y) y)
    (hf1 : 0 < f 1) (hf₁1 : f₁ 1 < 0) :
    ∀ y ∈ Icc a 1, f 1 ≤ f y ∧ 0 < f y ∧ f₁ y < 0 := by
  have htwo : (2 : ℝ) ≤ 2 / β := (le_div_iff₀ hβ).mpr (by linarith only [hβsmall])
  have hmirror : ∀ t ∈ Icc 0 (1 - a), 1 - t ∈ Icc a 1 := by
    intro t ht
    constructor <;> linarith only [ht, ht.1, ht.2]
  have hp := flux_lower_initial
    (V := fun t => f (1 - t))
    (F := fun t => -((1 + (1 - t) ^ 4) * f₁ (1 - t)))
    (D := fun t => 1 + (1 - t) ^ 4)
    (c := fun t => 2 / β - 2 * (1 - t) ^ 2)
    (T := 1 - a) (K := 2 / β + 1)
    (fun t ht => by
      apply ((hf (1 - t) (hmirror t ht)).comp t
        ((hasDerivAt_id t).const_sub 1)).congr_deriv
      have hd : 1 + (1 - t) ^ 4 ≠ 0 := ne_of_gt (by positivity)
      field_simp)
    (fun t ht => by
      apply (((hflux (1 - t) (hmirror t ht)).comp t
        ((hasDerivAt_id t).const_sub 1)).neg).congr_deriv
      ring)
    (by simpa only [sub_zero] using hf1.le)
    (by norm_num; linarith only [hf₁1])
    (fun t ht => by
      have hdge : 1 ≤ 1 + (1 - t) ^ 4 := le_add_of_nonneg_right (by positivity)
      have hdinv : 1 / (1 + (1 - t) ^ 4) ≤ 1 := (div_le_one (zero_lt_one.trans_le hdge)).mpr hdge
      exact ⟨div_nonneg zero_le_one (zero_le_one.trans hdge),
        hdinv.trans (le_add_of_nonneg_left (zero_le_two.trans htwo))⟩)
    (fun t ht => by
      obtain ⟨hyl, hyu⟩ := hmirror t ht
      have hy0 : 0 ≤ 1 - t := le_trans ha hyl
      have hy2 : (1 - t) ^ 2 ≤ 1 := pow_le_one₀ hy0 hyu
      exact ⟨sub_nonneg.mpr ((mul_le_of_le_one_right zero_le_two hy2).trans htwo),
        (sub_le_self _ (mul_nonneg zero_le_two (sq_nonneg _))).trans
          (le_add_of_nonneg_right zero_le_one)⟩)
  intro y hy
  have htime : 1 - y ∈ Icc 0 (1 - a) := by constructor <;> linarith only [hy, hy.1, hy.2]
  have hp' := hp (1 - y) htime
  have hrefl : 1 - (1 - y) = y := by ring
  simp only [sub_zero, hrefl, one_pow, one_add_one_eq_two] at hp'
  refine ⟨hp'.1, hf1.trans_le hp'.1, ?_⟩
  have hpositive : 0 < -((1 + y ^ 4) * f₁ y) := lt_of_lt_of_le (by linarith only [hf₁1]) hp'.2
  have hnegative : (1 + y ^ 4) * f₁ y < 0 := by linarith only [hf₁1, hp']
  exact neg_of_mul_neg_right hnegative (by positivity)

/-- A uniform Riccati upper bound that does not depend on the finite initial
value: a solution of `l' ≤ 2 - l²` obeys `l(t) ≤ 2 + 1/t` for `t > 0`. -/
theorem riccati_upper_bound
    {l dl : ℝ → ℝ} {T : ℝ}
    (hl : ∀ t ∈ Icc 0 T, HasDerivAt l (dl t) t)
    (hineq : ∀ t ∈ Ico 0 T, dl t ≤ 2 - (l t) ^ 2) :
    ∀ t ∈ Ioc 0 T, l t ≤ 2 + 1 / t := by
  have hp : ∀ t ∈ Icc 0 T, t * l t ≤ 1 + 2 * t := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := fun t => t * l t) (f' := fun t => l t + t * dl t)
      (B := fun t => 1 + 2 * t) (B' := fun _ => 2)
    · intro t ht
      exact ((hasDerivAt_id t).mul (hl t ht)).continuousAt.continuousWithinAt
    · intro t ht
      convert! ((hasDerivAt_id t).mul (hl t (Ico_subset_Icc_self ht))).hasDerivWithinAt using 1
      simp only [one_mul, id_eq]
    · norm_num
    · intro t
      simpa using ((hasDerivAt_id t).const_mul 2).const_add 1
    · intro t ht hboundary
      have htpos : 0 < t := by
        rcases ht.1.eq_or_lt with htzero | htpos
        · rw [← htzero]
            at hboundary
          norm_num at hboundary
        · exact htpos
      have hmul := mul_le_mul_of_nonneg_left (hineq t ht) (sq_nonneg t)
      have hsq := congrArg (fun x : ℝ => x ^ 2) hboundary
      apply (mul_lt_mul_iff_right₀ htpos).mp
      nlinarith only [hboundary, htpos, hmul, hsq]
  intro t ht
  have htp := hp t ⟨ht.1.le, ht.2⟩
  calc
    l t = (t * l t) / t := by field_simp [ne_of_gt ht.1]
    _ ≤ (1 + 2 * t) / t := div_le_div_of_nonneg_right htp ht.1.le
    _ = 2 + 1 / t := by field_simp [ne_of_gt ht.1]; ring

/-- Recovering the ordinary second derivative from the differentiated flux. -/
theorem equation30_second_derivative
    {β t : ℝ} {V V₁ : ℝ → ℝ}
    (hflux : HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
      (2 * (1 - β * (β * t ^ 2)) * V t) t) :
    HasDerivAt V₁
      ((2 * (1 - β * (β * t ^ 2)) * V t - 4 * β ^ 2 * t ^ 3 * V₁ t) /
        (1 + (β * t ^ 2) ^ 2)) t := by
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2)
      (4 * β ^ 2 * t ^ 3) t := by
    apply (((((hasDerivAt_id t).fun_pow 2).const_mul β).fun_pow 2).const_add 1).congr_deriv
    dsimp only [Nat.cast_ofNat, id_eq, Nat.add_one_sub_one]
    ring
  have hDne : ∀ s : ℝ, 1 + (β * s ^ 2) ^ 2 ≠ 0 := fun _ => ne_of_gt (by positivity)
  have hq := hflux.div hD (hDne t)
  convert! hq using 1
  · ext s
    change V₁ s = ((1 + (β * s ^ 2) ^ 2) * V₁ s) / (1 + (β * s ^ 2) ^ 2)
    field_simp [hDne s]
  · field_simp

theorem logDerivative_quotient_identity {a k D V W : ℝ} (hD : D ≠ 0) (hV : V ≠ 0) :
    ((a * V - k * W) / D * V - W * W) / V ^ 2 = a / D - k / D * (W / V) - (W / V) ^ 2 := by
  field_simp

/-- The logarithmic derivative in equation (30) is uniformly bounded away
from the initial time, independently of the initial nonnegative slope. -/
theorem equation30_log_derivative_upper
    {β T : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 1 / 2) (hT : 0 ≤ T)
    (hscale : β * T ^ 2 ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t ∈ Ioc 0 T, V₁ t / V t ≤ 2 + 1 / t := by
  have hp := equation30_positive hβ hβsmall hT hscale hV hflux hV0 hV₁0
  let dl : ℝ → ℝ := fun t =>
    2 * (1 - β * (β * t ^ 2)) / (1 + (β * t ^ 2) ^ 2) -
      (4 * β ^ 2 * t ^ 3 / (1 + (β * t ^ 2) ^ 2)) * (V₁ t / V t) -
      (V₁ t / V t) ^ 2
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun t => V₁ t / V t) (dl t) t := by
    intro t ht
    have hVne : V t ≠ 0 := ne_of_gt (hp t ht).1
    have hDne : 1 + (β * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    apply ((equation30_second_derivative (hflux t ht)).div (hV t ht) hVne).congr_deriv
    dsimp only [dl]
    exact logDerivative_quotient_identity hDne hVne
  apply riccati_upper_bound hd
  intro t ht
  have hti : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  have hDge : 1 ≤ 1 + (β * t ^ 2) ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  have hDpos : 0 < 1 + (β * t ^ 2) ^ 2 := zero_lt_one.trans_le hDge
  have hcub : 2 * (1 - β * (β * t ^ 2)) ≤ 2 := by
    linarith only [mul_nonneg hβ (mul_nonneg hβ (sq_nonneg t))]
  have hquot : 2 * (1 - β * (β * t ^ 2)) / (1 + (β * t ^ 2) ^ 2) ≤ 2 := by
    apply (div_le_iff₀ hDpos).mpr
    linarith only [hcub, hDge]
  have ht0 : 0 ≤ t := ht.1
  have hcoef : 0 ≤ 4 * β ^ 2 * t ^ 3 / (1 + (β * t ^ 2) ^ 2) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg β)) (pow_nonneg ht0 3)) hDpos.le
  have hlog : 0 ≤ V₁ t / V t := div_nonneg (hp t hti).2 (hp t hti).1.le
  dsimp only [dl]
  exact sub_le_sub_right ((sub_le_self _ (mul_nonneg hcoef hlog)).trans hquot) _

/-- A coarse Riccati upper barrier for the inverted equation. -/
theorem riccati_le_four
    {z a b : ℝ → ℝ} {T : ℝ}
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (a t - (z t) ^ 2 + b t * z t) t)
    (hz0 : z 0 ≤ 4)
    (ha : ∀ t ∈ Ico 0 T, a t ≤ 2)
    (hb : ∀ t ∈ Ico 0 T, b t ≤ 1) :
    ∀ t ∈ Icc 0 T, z t ≤ 4 := by
  apply image_le_of_deriv_right_lt_deriv_boundary
    (f := z) (f' := fun t => a t - (z t) ^ 2 + b t * z t)
    (B := fun _ => 4) (B' := fun _ => 0)
    (fun t ht => (hz t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hz t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    hz0 (fun t => hasDerivAt_const t 4)
  intro t ht hboundary
  rw [hboundary]
  linarith only [ha, ht, hb, ha t ht, hb t ht]

/-- Quantitative tracking of the stable positive Riccati branch.  This
abstract estimate is applied below with `μ = sqrt(2/(1+y^4))`; all constants
are explicit and do not involve the initial nonnegative slope. -/
theorem riccati_tracking
    {z μ dz dμ : ℝ → ℝ} {T ε : ℝ}
    (hε : 0 < ε)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (dz t) t)
    (hμ : ∀ t ∈ Icc 0 T, HasDerivAt μ (dμ t) t)
    (hzrange : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ 4)
    (hμrange : ∀ t ∈ Icc 0 T, 1 ≤ μ t ∧ μ t ≤ 2)
    (hres : ∀ t ∈ Ico 0 T, |dz t - ((μ t) ^ 2 - (z t) ^ 2)| ≤ 20 * ε)
    (hμderiv : ∀ t ∈ Ico 0 T, |dμ t| ≤ 4 * ε) :
    ∀ t ∈ Icc 0 T, |z t - μ t| ≤ 6 * exp (-t) + 48 * ε := by
  have hBd : ∀ t : ℝ, HasDerivAt (fun s => 6 * exp (-s) + 48 * ε)
      (-6 * exp (-t)) t := by
    intro t
    apply (((hasDerivAt_id t).neg.exp.const_mul 6).add_const (48 * ε)).congr_deriv
    dsimp only [Pi.neg_apply, id_eq]
    ring
  have hBpos : ∀ t : ℝ, 0 ≤ 6 * exp (-t) + 48 * ε := by
    intro t
    positivity
  by_cases hT : 0 ≤ T
  · have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    have hupper : ∀ t ∈ Icc 0 T, z t - μ t ≤ 6 * exp (-t) + 48 * ε := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun t => z t - μ t) (f' := fun t => dz t - dμ t)
        (B := fun t => 6 * exp (-t) + 48 * ε) (B' := fun t => -6 * exp (-t))
        (fun t ht => ((hz t ht).sub (hμ t ht)).continuousAt.continuousWithinAt)
        (fun t ht => ((hz t (Ico_subset_Icc_self ht)).sub
          (hμ t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
        (by norm_num; linarith only [hε, hzrange, hzero, hμrange, (hzrange 0 hzero).2,
            (hμrange 0 hzero).1]) hBd
      intro t ht hboundary
      have hti := Ico_subset_Icc_self ht
      have hsum : 1 ≤ z t + μ t := by linarith only [hzrange, hti, hμrange, (hzrange t hti).1,
          (hμrange t hti).1]
      have hprod := mul_nonneg (sub_nonneg.mpr hsum) (hBpos t)
      obtain ⟨hrlo, hrhi⟩ := abs_le.mp (hres t ht)
      obtain ⟨hμlo, hμhi⟩ := abs_le.mp (hμderiv t ht)
      have hsq : (z t - μ t) * (z t + μ t) = (6 * exp (-t) + 48 * ε) * (z t + μ t) := by
        rw [hboundary]
      linarith only [hε, hprod, hrhi, hμlo, hsq]
    have hlower : ∀ t ∈ Icc 0 T, μ t - z t ≤ 6 * exp (-t) + 48 * ε := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun t => μ t - z t) (f' := fun t => dμ t - dz t)
        (B := fun t => 6 * exp (-t) + 48 * ε) (B' := fun t => -6 * exp (-t))
        (fun t ht => ((hμ t ht).sub (hz t ht)).continuousAt.continuousWithinAt)
        (fun t ht => ((hμ t (Ico_subset_Icc_self ht)).sub
          (hz t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
        (by norm_num; linarith only [hε, hzrange, hzero, hμrange, (hzrange 0 hzero).1,
            (hμrange 0 hzero).2]) hBd
      intro t ht hboundary
      have hti := Ico_subset_Icc_self ht
      have hsum : 1 ≤ z t + μ t := by linarith only [hzrange, hti, hμrange, (hzrange t hti).1,
          (hμrange t hti).1]
      have hprod := mul_nonneg (sub_nonneg.mpr hsum) (hBpos t)
      obtain ⟨hrlo, hrhi⟩ := abs_le.mp (hres t ht)
      obtain ⟨hμlo, hμhi⟩ := abs_le.mp (hμderiv t ht)
      have hsq : (μ t - z t) * (z t + μ t) = (6 * exp (-t) + 48 * ε) * (z t + μ t) := by
        rw [hboundary]
      linarith only [hε, hprod, hrlo, hμhi, hsq]
    intro t ht
    exact abs_le.mpr ⟨by linarith only [hlower, ht, hlower t ht], hupper t ht⟩
  · intro t ht
    exact False.elim (hT (le_trans ht.1 ht.2))

/-- After time `1/(2ε)` the Riccati tracking error is at most `60ε`. -/
theorem riccati_tracking_after_layer
    {z μ dz dμ : ℝ → ℝ} {T ε : ℝ}
    (hε : 0 < ε)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (dz t) t)
    (hμ : ∀ t ∈ Icc 0 T, HasDerivAt μ (dμ t) t)
    (hzrange : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ 4)
    (hμrange : ∀ t ∈ Icc 0 T, 1 ≤ μ t ∧ μ t ≤ 2)
    (hres : ∀ t ∈ Ico 0 T, |dz t - ((μ t) ^ 2 - (z t) ^ 2)| ≤ 20 * ε)
    (hμderiv : ∀ t ∈ Ico 0 T, |dμ t| ≤ 4 * ε) :
    ∀ t ∈ Icc 0 T, 1 / (2 * ε) ≤ t → |z t - μ t| ≤ 60 * ε := by
  intro t ht hlayer
  have htime : 1 ≤ 2 * ε * t := by
    have := (div_le_iff₀ (show 0 < 2 * ε by positivity)).mp hlayer
    linarith only [this]
  have hexp : exp (-t) ≤ 2 * ε := by
    rw [exp_neg]
    rw [← one_div]
    apply (div_le_iff₀ (exp_pos _)).mpr
    have hm := mul_le_mul_of_nonneg_left (add_one_le_exp t) (show 0 ≤ 2 * ε by positivity)
    linarith only [hε, htime, hm]
  have htrack := riccati_tracking hε hz hμ hzrange hμrange hres hμderiv t ht
  linarith only [hexp, htrack]

/-- The positive stationary branch of the rescaled inverted Riccati equation. -/
noncomputable def riccatiRoot (ε t : ℝ) : ℝ :=
  sqrt (2 / (1 + (1 - ε * t) ^ 4))

/-- Its derivative as the spatial coordinate `y = 1 - εt` decreases. -/
noncomputable def riccatiRootDeriv (ε t : ℝ) : ℝ :=
  4 * ε * (1 - ε * t) ^ 3 /
    ((1 + (1 - ε * t) ^ 4) ^ 2 * riccatiRoot ε t)

theorem hasDerivAt_riccatiRoot (ε t : ℝ) :
    HasDerivAt (riccatiRoot ε) (riccatiRootDeriv ε t) t := by
  have hy : HasDerivAt (fun s : ℝ => 1 - ε * s) (-ε) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul ε).const_sub 1
  have hdne : 1 + (1 - ε * t) ^ 4 ≠ 0 := ne_of_gt (by positivity)
  have hqpos : 0 < 2 / (1 + (1 - ε * t) ^ 4) := by positivity
  have hq : HasDerivAt (fun s => 2 / (1 + (1 - ε * s) ^ 4))
      (8 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4) ^ 2) t := by
    apply ((hasDerivAt_const t (2 : ℝ)).div ((hy.fun_pow 4).const_add 1) hdne).congr_deriv
    dsimp only [Nat.cast_ofNat, Nat.add_one_sub_one]
    field_simp
    ring
  apply (hq.sqrt (ne_of_gt hqpos)).congr_deriv
  dsimp only [riccatiRootDeriv, riccatiRoot]
  field_simp [hdne, ne_of_gt (sqrt_pos.mpr hqpos)]
  ring

theorem riccatiRoot_bounds {ε t : ℝ}
    (hy : 0 ≤ 1 - ε * t ∧ 1 - ε * t ≤ 1) :
    1 ≤ riccatiRoot ε t ∧ riccatiRoot ε t ≤ 2 := by
  have hy4 : (1 - ε * t) ^ 4 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hy.1 hy.2 4
  have hdpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
  have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := by
    have : 0 ≤ (1 - ε * t) ^ 4 := by positivity
    linarith only [this]
  constructor
  · apply one_le_sqrt.mpr
    apply (le_div_iff₀ hdpos).mpr
    linarith only [hy4]
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · apply (div_le_iff₀ hdpos).mpr
      linarith only [hdpos, hdge]

theorem riccatiRootDeriv_bounds {ε t : ℝ} (hε : 0 ≤ ε)
    (hy : 0 ≤ 1 - ε * t ∧ 1 - ε * t ≤ 1) :
    0 ≤ riccatiRootDeriv ε t ∧ riccatiRootDeriv ε t ≤ 4 * ε := by
  have hμ := riccatiRoot_bounds hy
  have hy0 := hy.1
  have hy3 : (1 - ε * t) ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hy.1 hy.2 3
  have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := by
    have : 0 ≤ (1 - ε * t) ^ 4 := by positivity
    linarith only [this]
  have hDsq : 1 ≤ (1 + (1 - ε * t) ^ 4) ^ 2 := by nlinarith only [hdge]
  have hden : 1 ≤ (1 + (1 - ε * t) ^ 4) ^ 2 * riccatiRoot ε t :=
    hDsq.trans (le_mul_of_one_le_right (sq_nonneg _) hμ.1)
  have hdenpos : 0 < (1 + (1 - ε * t) ^ 4) ^ 2 * riccatiRoot ε t := by linarith only [hden]
  constructor
  · exact div_nonneg (by positivity) hdenpos.le
  · apply (div_le_iff₀ hdenpos).mpr
    exact mul_le_mul_of_nonneg_left (hy3.trans hden) (by positivity)

/-- Right-hand side of the inverted Riccati equation in the fast coordinate
`t = (1-y)/ε`, where `ε = sqrt β`. -/
noncomputable def invertedRiccati (ε t z : ℝ) : ℝ :=
  (2 - 2 * ε ^ 2 * (1 - ε * t) ^ 2) / (1 + (1 - ε * t) ^ 4) - z ^ 2 +
    (4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4)) * z

/-- Explicit form of the uniform `O(sqrt β)` Riccati estimate in (31).
This theorem uses the exact rescaled ODE and an initial bound of `4`; the
preceding logarithmic-derivative estimate supplies that bound independently
of the nonnegative initial slope. -/
theorem inverted_riccati_squared_error
    {ε T : ℝ} {z : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hscale : ε * T ≤ 1)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (invertedRiccati ε t (z t)) t)
    (hz0 : z 0 ≤ 4) (hzn : ∀ t ∈ Icc 0 T, 0 ≤ z t) :
    ∀ t ∈ Icc 0 T, 1 / (2 * ε) ≤ t →
      |(z t) ^ 2 - 2 / (1 + (1 - ε * t) ^ 4)| ≤ 360 * ε := by
  have hy : ∀ t ∈ Icc 0 T, 0 ≤ 1 - ε * t ∧ 1 - ε * t ≤ 1 := by
    intro t ht
    have hu := mul_le_mul_of_nonneg_left ht.2 hε.le
    have hl := mul_nonneg hε.le ht.1
    exact ⟨by linarith only [hu, hscale], by linarith only [hl]⟩
  have hcoeff : ∀ t ∈ Icc 0 T,
      (2 - 2 * ε ^ 2 * (1 - ε * t) ^ 2) / (1 + (1 - ε * t) ^ 4) ≤ 2 ∧
      0 ≤ 4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4) ∧
      4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4) ≤ 4 * ε := by
    intro t ht
    have hyt := hy t ht
    have hy0 := hyt.1
    have hy3 : (1 - ε * t) ^ 3 ≤ 1 := pow_le_one₀ hyt.1 hyt.2
    have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := le_add_of_nonneg_right (pow_nonneg hy0 4)
    have hdpos : 0 < 1 + (1 - ε * t) ^ 4 := zero_lt_one.trans_le hdge
    have h4ε : 0 ≤ 4 * ε := mul_nonneg (by norm_num) hε.le
    refine ⟨?_, div_nonneg (mul_nonneg h4ε (pow_nonneg hy0 3)) hdpos.le, ?_⟩
    · apply (div_le_iff₀ hdpos).mpr
      linarith only [mul_nonneg (sq_nonneg ε) (sq_nonneg (1 - ε * t)), pow_nonneg hy0 4]
    · apply (div_le_iff₀ hdpos).mpr
      exact mul_le_mul_of_nonneg_left (hy3.trans hdge) h4ε
  have hzfour : ∀ t ∈ Icc 0 T, z t ≤ 4 := by
    apply riccati_le_four hz hz0
    · intro t ht
      exact (hcoeff t (Ico_subset_Icc_self ht)).1
    · intro t ht
      linarith only [(hcoeff t (Ico_subset_Icc_self ht)).2.2, hεsmall]
  have hzrange : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ 4 :=
    fun t ht => ⟨hzn t ht, hzfour t ht⟩
  have hres : ∀ t ∈ Ico 0 T,
      |invertedRiccati ε t (z t) - ((riccatiRoot ε t) ^ 2 - (z t) ^ 2)| ≤ 20 * ε := by
    intro t ht
    have hti := Ico_subset_Icc_self ht
    have hyt := hy t hti
    have hy0 := hyt.1
    have hy2 : (1 - ε * t) ^ 2 ≤ 1 := pow_le_one₀ hyt.1 hyt.2
    have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := le_add_of_nonneg_right (pow_nonneg hy0 4)
    have hdpos : 0 < 1 + (1 - ε * t) ^ 4 := zero_lt_one.trans_le hdge
    have h2ε : 0 ≤ 2 * ε ^ 2 := mul_nonneg zero_le_two (sq_nonneg ε)
    have hqnonneg : 0 ≤ 2 * ε ^ 2 * (1 - ε * t) ^ 2 / (1 + (1 - ε * t) ^ 4) :=
      div_nonneg (mul_nonneg h2ε (sq_nonneg _)) hdpos.le
    have hqupper : 2 * ε ^ 2 * (1 - ε * t) ^ 2 / (1 + (1 - ε * t) ^ 4) ≤ 2 * ε ^ 2 := by
      apply (div_le_iff₀ hdpos).mpr
      exact mul_le_mul_of_nonneg_left (hy2.trans hdge) h2ε
    have hbn := (hcoeff t hti).2.1
    have hbu := (hcoeff t hti).2.2
    have hmulnonneg := mul_nonneg hbn (hzn t hti)
    have hmulupper :
        (4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4)) * z t ≤ 16 * ε := by
      have hm := mul_le_mul hbu (hzfour t hti) (hzn t hti) (mul_nonneg (by norm_num) hε.le)
      linarith only [hm]
    have hsquare : (riccatiRoot ε t) ^ 2 = 2 / (1 + (1 - ε * t) ^ 4) :=
      sq_sqrt (div_nonneg zero_le_two hdpos.le)
    have heq : invertedRiccati ε t (z t) - ((riccatiRoot ε t) ^ 2 - (z t) ^ 2) =
        -(2 * ε ^ 2 * (1 - ε * t) ^ 2 / (1 + (1 - ε * t) ^ 4)) +
          (4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4)) * z t := by
      rw [hsquare]
      unfold invertedRiccati
      ring
    have hqupper' := hqupper.trans (show 2 * ε ^ 2 ≤ 20 * ε by
      linarith only [mul_le_mul_of_nonneg_left (show ε ≤ 10 by linarith only [hεsmall]) hε.le])
    rw [heq]
    generalize 2 * ε ^ 2 * (1 - ε * t) ^ 2 / (1 + (1 - ε * t) ^ 4) = w at hqupper' hqnonneg ⊢
    generalize 4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4) * z t = m at hmulnonneg hmulupper ⊢
    exact abs_le.mpr ⟨by linarith only [hqupper', hmulnonneg],
      by linarith only [hqnonneg, hmulupper, hε]⟩
  have hμderiv : ∀ t ∈ Ico 0 T, |riccatiRootDeriv ε t| ≤ 4 * ε := by
    intro t ht
    have hp := riccatiRootDeriv_bounds hε.le (hy t (Ico_subset_Icc_self ht))
    rw [abs_of_nonneg hp.1]
    exact hp.2
  intro t ht hlayer
  have htrack := riccati_tracking_after_layer hε hz
    (fun s _ => hasDerivAt_riccatiRoot ε s) hzrange
    (fun s hs => riccatiRoot_bounds (hy s hs)) hres hμderiv t ht hlayer
  have hμrange := riccatiRoot_bounds (hy t ht)
  have hsum : |z t + riccatiRoot ε t| ≤ 6 := by
    rw [abs_of_nonneg (add_nonneg (hzn t ht) (zero_le_one.trans hμrange.1))]
    linarith only [hzfour t ht, hμrange.2]
  have hsquare : (riccatiRoot ε t) ^ 2 = 2 / (1 + (1 - ε * t) ^ 4) :=
    sq_sqrt (by positivity)
  rw [← hsquare, sq_sub_sq, abs_mul]
  have hm := mul_le_mul htrack hsum (abs_nonneg _) (mul_nonneg (by norm_num) hε.le)
  linarith only [hm]

/-- The second derivative of a solution of the inverted scalar equation. -/
theorem inversion_second_derivative
    {β y : ℝ} {f f₁ : ℝ → ℝ}
    (hflux : HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / β - 2 * y ^ 2) * f y) y) :
    HasDerivAt f₁ (((2 / β - 2 * y ^ 2) * f y - 4 * y ^ 3 * f₁ y) /
      (1 + y ^ 4)) y := by
  have hD : HasDerivAt (fun z : ℝ => 1 + z ^ 4) (4 * y ^ 3) y := by
    convert! ((hasDerivAt_id y).fun_pow 4).const_add 1 using 1
    norm_num
  have hDne : ∀ z : ℝ, 1 + z ^ 4 ≠ 0 := fun _ => ne_of_gt (by positivity)
  have hq := hflux.div hD (hDne y)
  convert! hq using 1
  · ext z
    change f₁ z = ((1 + z ^ 4) * f₁ z) / (1 + z ^ 4)
    field_simp [hDne z]
  · field_simp

/-- The exact Riccati equation after the substitutions
`y = 1-εt` and `z = -ε f'/f`. -/
theorem hasDerivAt_inverted_logderivative
    {ε t : ℝ} {f f₁ : ℝ → ℝ}
    (hε : ε ≠ 0) (hfpos : f (1 - ε * t) ≠ 0)
    (hf : HasDerivAt f (f₁ (1 - ε * t)) (1 - ε * t))
    (hflux : HasDerivAt (fun y => (1 + y ^ 4) * f₁ y)
      ((2 / ε ^ 2 - 2 * (1 - ε * t) ^ 2) * f (1 - ε * t)) (1 - ε * t)) :
    HasDerivAt (fun s => -ε * f₁ (1 - ε * s) / f (1 - ε * s))
      (invertedRiccati ε t (-ε * f₁ (1 - ε * t) / f (1 - ε * t))) t := by
  have hy : HasDerivAt (fun s : ℝ => 1 - ε * s) (-ε) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul ε).const_sub 1
  have hDne : 1 + (1 - ε * t) ^ 4 ≠ 0 := ne_of_gt (by positivity)
  have hd := (((inversion_second_derivative hflux).comp (h := fun s : ℝ => 1 - ε * s) t
    hy).const_mul (-ε)).div (hf.comp (h := fun s : ℝ => 1 - ε * s) t hy) hfpos
  apply hd.congr_deriv
  dsimp only [Function.comp_apply, invertedRiccati]
  field_simp
  ring

/-- The uniform Riccati estimate directly for solutions of the inverted
scalar equation.  Positivity on the interval follows from the endpoint
conditions; it is not assumed. -/
theorem inversion_riccati_error
    {ε a : ℝ} {f f₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (ha : 0 ≤ a)
    (hf : ∀ y ∈ Icc a 1, HasDerivAt f (f₁ y) y)
    (hflux : ∀ y ∈ Icc a 1, HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / ε ^ 2 - 2 * y ^ 2) * f y) y)
    (hf1 : 0 < f 1) (hf₁1 : f₁ 1 < 0)
    (hinit : -ε * f₁ 1 / f 1 ≤ 4) :
    ∀ y ∈ Icc a (1 / 2),
      |(-ε * f₁ y / f y) ^ 2 - 2 / (1 + y ^ 4)| ≤ 360 * ε := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hp := inversion_positive (sq_pos_of_pos hε) (by nlinarith only [hε, hεsmall] : ε ^ 2 ≤ 1)
    ha hf hflux hf1 hf₁1
  have hmirror : ∀ t ∈ Icc 0 ((1 - a) / ε), 1 - ε * t ∈ Icc a 1 := by
    intro t ht
    have hu : ε * t ≤ 1 - a := by
      have := (le_div_iff₀ hε).mp ht.2
      linarith only [this]
    have hl := mul_nonneg hε.le ht.1
    constructor <;> linarith only [hu, hl]
  have hscale : ε * ((1 - a) / ε) ≤ 1 := by
    field_simp
    linarith only [ha]
  have hz : ∀ t ∈ Icc 0 ((1 - a) / ε),
      HasDerivAt (fun s => -ε * f₁ (1 - ε * s) / f (1 - ε * s))
        (invertedRiccati ε t (-ε * f₁ (1 - ε * t) / f (1 - ε * t))) t := by
    intro t ht
    exact hasDerivAt_inverted_logderivative hεne
      (ne_of_gt (hp (1 - ε * t) (hmirror t ht)).2.1)
      (hf _ (hmirror t ht)) (hflux _ (hmirror t ht))
  have hznonneg : ∀ t ∈ Icc 0 ((1 - a) / ε),
      0 ≤ -ε * f₁ (1 - ε * t) / f (1 - ε * t) := by
    intro t ht
    have hpt := hp (1 - ε * t) (hmirror t ht)
    apply div_nonneg _ hpt.2.1.le
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hε.le) hpt.2.2.le
  have herr := inverted_riccati_squared_error hε hεsmall hscale hz
    (by simpa only [mul_zero, sub_zero, neg_mul] using hinit) hznonneg
  intro y hy
  have hy1 : y ≤ 1 := by linarith only [hε, hεsmall, hy, hy.2]
  have ht : (1 - y) / ε ∈ Icc 0 ((1 - a) / ε) := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hy1) hε.le
    · exact div_le_div_of_nonneg_right (by linarith only [hy, hy.1]) hε.le
  have hlayer : 1 / (2 * ε) ≤ (1 - y) / ε := by
    apply (div_le_div_iff₀ (show 0 < 2 * ε by positivity) hε).mpr
    nlinarith only [hε, hy, hy.2]
  have heq : 1 - ε * ((1 - y) / ε) = y := by field_simp; ring
  simpa only [heq] using herr ((1 - y) / ε) ht hlayer

/-- Inversion of a solution in the original time variable, including the
rescaling `x = ετ`. -/
noncomputable def invertedScalar (ε : ℝ) (V : ℝ → ℝ) (y : ℝ) : ℝ :=
  V (y⁻¹ / ε) / y

/-- The exact derivative of `invertedScalar`, away from `y = 0`. -/
noncomputable def invertedScalarDeriv (ε : ℝ) (V V₁ : ℝ → ℝ) (y : ℝ) : ℝ :=
  -V (y⁻¹ / ε) / y ^ 2 - V₁ (y⁻¹ / ε) / (ε * y ^ 3)

/-- Both differential equations for the rescaled inversion, derived
algebraically from equation (30). -/
theorem invertedScalar_equations
    {ε y : ℝ} {V V₁ : ℝ → ℝ}
    (hε : ε ≠ 0) (hy : y ≠ 0)
    (hV : HasDerivAt V (V₁ (y⁻¹ / ε)) (y⁻¹ / ε))
    (hflux : HasDerivAt (fun t => (1 + (ε ^ 2 * t ^ 2) ^ 2) * V₁ t)
      (2 * (1 - ε ^ 2 * (ε ^ 2 * (y⁻¹ / ε) ^ 2)) * V (y⁻¹ / ε)) (y⁻¹ / ε)) :
    HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ y) y ∧
    HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
      ((2 / ε ^ 2 - 2 * y ^ 2) * invertedScalar ε V y) y := by
  have harg := (hasDerivAt_inv hy).div_const ε
  have h0 := hV.comp (h := fun z : ℝ => z⁻¹ / ε) y harg
  have h1 := (equation30_second_derivative hflux).comp (h := fun z : ℝ => z⁻¹ / ε) y harg
  have h2 := (hasDerivAt_id y).fun_pow 2
  have h3 := ((hasDerivAt_id y).fun_pow 3).const_mul ε
  have h4 := ((hasDerivAt_id y).fun_pow 4).const_add 1
  have hDne : 1 + (ε ^ 2 * (y⁻¹ / ε) ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  constructor
  · apply (h0.div (hasDerivAt_id y) hy).congr_deriv
    dsimp only [id_eq, Function.comp_apply, invertedScalarDeriv]
    field_simp
    ring
  · apply (h4.mul ((h0.neg.div h2 (pow_ne_zero 2 hy)).sub
      (h1.div h3 (mul_ne_zero hε (pow_ne_zero 3 hy))))).congr_deriv
    dsimp only [Nat.cast_ofNat, id_eq, Nat.add_one_sub_one, Pi.sub_apply, Pi.div_apply,
        Pi.neg_apply, Function.comp_apply, invertedScalar]
    field_simp
    ring

/-- At the start of inversion the Riccati variable has an absolute bound,
independent of the original initial nonnegative slope. -/
theorem invertedScalar_initial_bound
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t ∈ Icc 0 (1 / ε), HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 (1 / ε),
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    0 < invertedScalar ε V 1 ∧ invertedScalarDeriv ε V V₁ 1 < 0 ∧
      -ε * invertedScalarDeriv ε V V₁ 1 / invertedScalar ε V 1 ≤ 4 := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hT : 0 ≤ 1 / ε := by positivity
  have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
  have hβsmall : ε ^ 2 ≤ 1 / 2 := by nlinarith only [hε, hεsmall]
  have hp := equation30_positive (sq_nonneg ε) hβsmall hT hscale hV hflux hV0 hV₁0
    (1 / ε) ⟨hT, le_rfl⟩
  have hl := equation30_log_derivative_upper (sq_nonneg ε) hβsmall hT hscale
    hV hflux hV0 hV₁0 (1 / ε) ⟨by positivity, le_rfl⟩
  have hVne : V (1 / ε) ≠ 0 := ne_of_gt hp.1
  dsimp only [invertedScalar, invertedScalarDeriv]
  simp only [inv_one, one_pow, div_one, mul_one, neg_mul]
  refine ⟨hp.1, ?_, ?_⟩
  · have hquot : 0 ≤ V₁ (1 / ε) / ε := div_nonneg hp.2 hε.le
    linarith only [hp, hquot]
  · have heq : -(ε * (-(V (1 / ε)) - V₁ (1 / ε) / ε)) / V (1 / ε) =
        ε + V₁ (1 / ε) / V (1 / ε) := by field_simp; ring
    rw [heq]
    rw [one_div_one_div] at hl
    linarith only [hε, hεsmall, hl]

/-- The full uniform estimate (31) for the scalar equation, including the
rescaling, inversion, positivity, and removal of all dependence on the
original nonnegative initial slope. -/
theorem equation30_inverted_riccati_error
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 / 2 →
      |(-ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y) ^ 2 -
        2 / (1 + y ^ 4)| ≤ 360 * ε := by
  have hinit := invertedScalar_initial_bound hε hεsmall
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  intro y hy hyhalf
  have heqs : ∀ s ∈ Icc y 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ s) s ∧
      HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
        ((2 / ε ^ 2 - 2 * s ^ 2) * invertedScalar ε V s) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hy hs.1
    have harg : 0 ≤ s⁻¹ / ε := by positivity
    exact invertedScalar_equations (ne_of_gt hε) (ne_of_gt hspos)
      (hV _ harg) (hflux _ harg)
  exact inversion_riccati_error hε hεsmall hy.le
    (fun s hs => (heqs s hs).1) (fun s hs => (heqs s hs).2)
    hinit.1 hinit.2.1 hinit.2.2 y ⟨le_rfl, hyhalf⟩

/-- The Wronskian flux of two solutions of `(D u')' = c u` is conserved. -/
theorem flux_wronskian_constant
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t) :
    ∀ t ∈ Icc a b,
      u t * (D t * v₁ t) - (D t * u₁ t) * v t =
        u a * (D a * v₁ a) - (D a * u₁ a) * v a := by
  have hw : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => u s * (D s * v₁ s) - (D s * u₁ s) * v s) 0 t := by
    intro t ht
    apply (((hu t ht).mul (hfv t ht)).sub ((hfu t ht).mul (hv t ht))).congr_deriv
    ring
  exact constant_of_has_deriv_right_zero
    (fun t ht => (hw t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hw t (Ico_subset_Icc_self ht)).hasDerivWithinAt)

/-- The derivative of the quotient of two scalar solutions, expressed using
their initial Wronskian rather than either exponentially large solution. -/
theorem quotient_derivative_of_flux
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      HasDerivAt (fun s => v s / u s)
        ((u a * (D a * v₁ a) - (D a * u₁ a) * v a) / (D t * (u t) ^ 2)) t := by
  intro t ht
  apply ((hv t ht).div (hu t ht) (hupos t ht)).congr_deriv
  have hw := flux_wronskian_constant hu hv hfu hfv t ht
  calc
    (v₁ t * u t - v t * u₁ t) / (u t) ^ 2 =
        (u t * (D t * v₁ t) - (D t * u₁ t) * v t) / (D t * (u t) ^ 2) := by
      field_simp [hD t ht, hupos t ht]
    _ = _ := by rw [hw]

/-- The exact reduction-of-order formula on a closed interval.  Its integral
contains the reciprocal square of the positive reference solution. -/
theorem reduction_of_order
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hDc : ContinuousOn D (Icc a b))
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      v t = u t * (v a / u a +
        (u a * (D a * v₁ a) - (D a * u₁ a) * v a) *
          ∫ s in a..t, 1 / (D s * (u s) ^ 2)) := by
  intro t ht
  have hsubset : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have huc : ContinuousOn u (Icc a b) :=
    fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hic : ContinuousOn (fun s => 1 / (D s * (u s) ^ 2)) (Icc a b) :=
    continuousOn_const.div (hDc.mul (huc.pow 2))
      (fun s hs => mul_ne_zero (hD s hs) (pow_ne_zero 2 (hupos s hs)))
  have hii : IntervalIntegrable (fun s => 1 / (D s * (u s) ^ 2))
      MeasureTheory.volume a t := (hic.mono hsubset).intervalIntegrable
  have hdi := hii.const_mul (u a * (D a * v₁ a) - (D a * u₁ a) * v a)
  have hd := quotient_derivative_of_flux hu hv hfu hfv hD hupos
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => (hd s (hsubset hs)).congr_deriv
      (by simp only [div_eq_mul_inv]; ring)) hdi
  rw [intervalIntegral.integral_const_mul] at hint
  have hune : u t ≠ 0 := hupos t ht
  have hratio : v t / u t = v a / u a +
      (u a * (D a * v₁ a) - (D a * u₁ a) * v a) *
        ∫ s in a..t, 1 / (D s * (u s) ^ 2) := by linarith only [hint]
  rw [← hratio]
  field_simp

/-- Positivity and decrease of the inverted scalar solution for every
positive inversion coordinate. -/
theorem invertedScalar_positive
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 →
      invertedScalar ε V 1 ≤ invertedScalar ε V y ∧
      0 < invertedScalar ε V y ∧ invertedScalarDeriv ε V V₁ y < 0 := by
  have hinit := invertedScalar_initial_bound hε hεsmall
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  intro y hy hy1
  have heqs : ∀ s ∈ Icc y 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ s) s ∧
      HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
        ((2 / ε ^ 2 - 2 * s ^ 2) * invertedScalar ε V s) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hy hs.1
    have harg : 0 ≤ s⁻¹ / ε := by positivity
    exact invertedScalar_equations (ne_of_gt hε) (ne_of_gt hspos)
      (hV _ harg) (hflux _ harg)
  exact inversion_positive (sq_pos_of_pos hε) (by nlinarith only [hε, hεsmall] : ε ^ 2 ≤ 1) hy.le
    (fun s hs => (heqs s hs).1) (fun s hs => (heqs s hs).2)
    hinit.1 hinit.2.1 y ⟨le_rfl, hy1⟩

/-- Growth remains at least the value at `x=1` divided by `x` after
inversion.  This is the lower bound used in the exponential gain estimate. -/
theorem equation30_post_inversion_lower
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ x, 1 ≤ x → V (1 / ε) / x ≤ V (x / ε) ∧ 0 < V (x / ε) := by
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : 0 < 1 / x := by positivity
  have hy1 : 1 / x ≤ 1 := (div_le_one hxpos).mpr hx
  have hp := invertedScalar_positive hε hεsmall hV hflux hV0 hV₁0 (1 / x) hypos hy1
  have hid : invertedScalar ε V (1 / x) = x * V (x / ε) := by
    simp only [invertedScalar, one_div, inv_inv, div_inv_eq_mul, mul_comm]
  have hid1 : invertedScalar ε V 1 = V (1 / ε) := by simp only [invertedScalar, inv_one, one_div,
      div_one]
  rw [hid, hid1] at hp
  constructor
  · apply (div_le_iff₀ hxpos).mpr
    linarith only [hp, hp.1]
  · exact pos_of_mul_pos_right hp.2.1 hxpos.le

/-- A solution with the source's initial conditions stays positive for every
nonnegative original time, including beyond the inversion point. -/
theorem equation30_global_positive
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 0 ≤ t → 0 < V t := by
  intro t ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  by_cases hpre : t ≤ 1 / ε
  · have hT : 0 ≤ 1 / ε := by positivity
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    exact (equation30_positive (sq_nonneg ε) (by nlinarith only [hε, hεsmall]) hT hscale
      (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨ht, hpre⟩).1
  · have hx : 1 ≤ ε * t := by
      have := (div_le_iff₀ hε).mp (le_of_not_ge hpre)
      linarith only [this]
    have hp := (equation30_post_inversion_lower hε hεsmall hV hflux hV0 hV₁0 (ε * t) hx).2
    simpa only [mul_div_cancel_left₀ t hεne] using hp

/-- Reduction of order in the source's normalization `V₀(0)=1`,
`V₀'(0)=0`, `Vλ(0)=1`, `Vλ'(0)=λ`. -/
theorem equation30_reduction_of_order
    {ε lam : ℝ} {U U₁ V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV0 : V 0 = 1) (hV₁0 : V₁ 0 = lam) :
    ∀ t, 0 ≤ t → V t = U t *
      (1 + lam * ∫ s in (0 : ℝ)..t, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2)) := by
  have hup := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  intro t ht
  have hr := reduction_of_order
    (a := 0) (b := t)
    (D := fun s => 1 + (ε ^ 2 * s ^ 2) ^ 2)
    (c := fun s => 2 * (1 - ε ^ 2 * (ε ^ 2 * s ^ 2)))
    (fun s hs => hU s hs.1) (fun s hs => hV s hs.1)
    (fun s hs => hfluxU s hs.1) (fun s hs => hfluxV s hs.1)
    (continuous_const.add ((continuous_const.mul (continuous_pow 2)).pow 2)).continuousOn
    (fun _ _ => ne_of_gt (by positivity))
    (fun s hs => ne_of_gt (hup s hs.1)) t ⟨ht, le_rfl⟩
  simpa only [hU0, hU₁0, hV0, hV₁0, div_one, one_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero, mul_one, zero_mul, sub_zero] using hr

/-- A fixed upper bound for the zero-slope reference solution on `[0,1]`. -/
theorem equation30_zero_slope_prefix_upper
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t ∈ Icc 0 1, HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t ∈ Icc 0 1,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    ∀ t ∈ Icc 0 1, U t ≤ exp 3 := by
  have heps : ε ^ 2 ≤ 1 / 2 := (pow_le_pow_left₀ hε.le hεsmall 2).trans (by norm_num)
  have hp := equation30_positive (sq_nonneg ε) heps (by norm_num : (0 : ℝ) ≤ 1)
    (by rw [one_pow, mul_one]; linarith only [heps] : ε ^ 2 * (1 : ℝ) ^ 2 ≤ 1)
    hU hfluxU hU0 (by rw [hU₁0])
  have hsum : ∀ t ∈ Icc 0 1,
      U t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t ≤ exp (3 * t) := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := (fun t => U t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t :))
      (f' := fun t => U₁ t + 2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t)
      (B := fun t => exp (3 * t)) (B' := fun t => 3 * exp (3 * t))
      (fun t ht => ((hU t ht).add (hfluxU t ht)).continuousAt.continuousWithinAt)
      (fun t ht => ((hU t (Ico_subset_Icc_self ht)).add
        (hfluxU t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (by simp only [hU0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
          add_zero, hU₁0, exp_zero, Std.le_refl])
      (fun t => by
        apply (((hasDerivAt_id t).const_mul 3).exp).congr_deriv
        dsimp only [id_eq]
        ring)
    intro t ht hboundary
    have hti := Ico_subset_Icc_self ht
    have hpt := hp t hti
    have hD : 1 ≤ 1 + (ε ^ 2 * t ^ 2) ^ 2 := by linarith only [sq_nonneg (ε ^ 2 * t ^ 2)]
    have hfirst := mul_le_mul_of_nonneg_right hD hpt.2
    have hc : 2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) ≤ 2 := by
      linarith only [mul_nonneg (sq_nonneg ε) (mul_nonneg (sq_nonneg ε) (sq_nonneg t))]
    have hsecond := mul_le_mul_of_nonneg_right hc hpt.1.le
    linarith only [hboundary, hpt, hfirst, hsecond, exp_pos (3 * t)]
  intro t ht
  have hpt := hp t ht
  have hFn : 0 ≤ (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t :=
    mul_nonneg (add_nonneg zero_le_one (sq_nonneg _)) hpt.2
  have he : exp (3 * t) ≤ exp 3 := exp_le_exp.mpr (by linarith only [ht, ht.2])
  linarith only [hFn, he, hsum, ht, hsum t ht]

/-- The reduction-of-order integral at time `1` has a positive absolute
lower bound.  No numerical approximations occur in the constant. -/
theorem equation30_reduction_integral_one_lower
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t ∈ Icc 0 1, HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t ∈ Icc 0 1,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    1 / (2 * exp 6) ≤
      ∫ s in (0 : ℝ)..1, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2) := by
  have heps : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le (hεsmall.trans (by norm_num))
  have hp := equation30_positive (sq_nonneg ε)
    ((pow_le_pow_left₀ hε.le hεsmall 2).trans (by norm_num)) (by norm_num : (0 : ℝ) ≤ 1)
    (by rw [one_pow, mul_one]; exact heps : ε ^ 2 * (1 : ℝ) ^ 2 ≤ 1)
    hU hfluxU hU0 (by rw [hU₁0])
  have hu := equation30_zero_slope_prefix_upper hε hεsmall hU hfluxU hU0 hU₁0
  have huc : ContinuousOn U (Icc 0 1) := fun t ht => (hU t ht).continuousAt.continuousWithinAt
  have hic : ContinuousOn (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      (Icc 0 1) := by
    apply continuousOn_const.div
    · exact (continuous_const.add
        ((continuous_const.mul (continuous_pow 2)).pow 2)).continuousOn.mul (huc.pow 2)
    · intro t ht
      exact ne_of_gt (mul_pos (by positivity) (sq_pos_of_pos (hp t ht).1))
  have hint : IntervalIntegrable (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hic
  have hbound : ∀ t ∈ Icc 0 1,
      1 / (2 * exp 6) ≤ 1 / ((1 + (ε ^ 2 * t ^ 2) ^ 2) * (U t) ^ 2) := by
    intro t ht
    have hpt := hp t ht
    have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2
    have hinside : 0 ≤ ε ^ 2 * t ^ 2 ∧ ε ^ 2 * t ^ 2 ≤ 1 :=
      ⟨mul_nonneg (sq_nonneg ε) (sq_nonneg t),
        (mul_le_of_le_one_right (sq_nonneg ε) ht2).trans heps⟩
    have hD : 1 + (ε ^ 2 * t ^ 2) ^ 2 ≤ 2 := by
      linarith only [pow_le_one₀ (n := 2) hinside.1 hinside.2]
    have hUsq : (U t) ^ 2 ≤ (exp 3) ^ 2 := (sq_le_sq₀ hpt.1.le (exp_pos 3).le).mpr (hu t ht)
    have hprod := mul_le_mul hD hUsq (sq_nonneg (U t)) (by norm_num : (0 : ℝ) ≤ 2)
    have he : (exp (3 : ℝ)) ^ 2 = exp 6 := by
      rw [pow_two, ← exp_add]
      norm_num
    rw [he] at hprod
    exact one_div_le_one_div_of_le
      (mul_pos (by positivity) (sq_pos_of_pos hpt.1)) hprod
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / (2 * exp 6))
      MeasureTheory.volume 0 1) hint hbound
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hi

/-- The same absolute lower bound holds for the reduction integral at every
later time, because its integrand is nonnegative. -/
theorem equation30_reduction_integral_lower
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    ∀ t, 1 ≤ t → 1 / (2 * exp 6) ≤
      ∫ s in (0 : ℝ)..t, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2) := by
  have hpos := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hI1 := equation30_reduction_integral_one_lower hε hεsmall
    (fun s hs => hU s hs.1) (fun s hs => hfluxU s hs.1) hU0 hU₁0
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have huc : ContinuousOn U (Icc 0 t) := fun s hs => (hU s hs.1).continuousAt.continuousWithinAt
  have hic : ContinuousOn (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      (Icc 0 t) := by
    apply continuousOn_const.div
    · exact (by fun_prop : ContinuousOn (fun s : ℝ => 1 + (ε ^ 2 * s ^ 2) ^ 2) (Icc 0 t)).mul
        (huc.pow 2)
    · intro s hs
      exact ne_of_gt (mul_pos (by positivity) (sq_pos_of_pos (hpos s hs.1)))
  have hint : IntervalIntegrable (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le ht0] using hic
  have hmono := intervalIntegral.integral_mono_interval (a := (0 : ℝ)) (b := 1)
    (c := (0 : ℝ)) (d := t) le_rfl zero_le_one ht
    (Filter.Eventually.of_forall (fun s : ℝ => by positivity)) hint
  exact hI1.trans hmono

/-- The solution with slope `lam ≥ 0` dominates the zero-slope reference
solution by a fixed multiple of `(1+lam)` after time `1`. -/
theorem equation30_slope_uniform_lower
    {ε lam : ℝ} {U U₁ V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hlam : 0 ≤ lam)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV0 : V 0 = 1) (hV₁0 : V₁ 0 = lam) :
    ∀ t, 1 ≤ t → ((1 + lam) / (2 * exp 6)) * U t ≤ V t := by
  have hpos := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  rw [equation30_reduction_of_order hε hεsmall hU hV hfluxU hfluxV hU0 hU₁0 hV0 hV₁0 t ht0]
  have hI := equation30_reduction_integral_lower hε hεsmall hU hfluxU hU0 hU₁0 t ht
  have hc : 1 / (2 * exp 6) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * exp 6)).mpr
    linarith only [hε, hεsmall, add_one_le_exp (6 : ℝ)]
  have hi : (1 + lam) / (2 * exp 6) ≤
      1 + lam * ∫ s in (0 : ℝ)..t, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hI hlam
    simp only [div_eq_mul_inv] at hc hm ⊢
    linarith only [hc, hm]
  linarith only [hi, hpos, ht0, mul_le_mul_of_nonneg_right hi (hpos t ht0).le]

/-- Before `x=1`, the original scalar solution is nondecreasing. -/
theorem equation30_prefix_monotone
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    MonotoneOn V (Icc 0 (1 / ε)) := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
  have hp := equation30_positive (sq_nonneg ε) (by nlinarith only [hε, hεsmall])
    (by positivity : 0 ≤ 1 / ε) hscale
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (1 / ε))
    (fun t ht => (hV t ht.1).continuousAt.continuousWithinAt)
    (fun t ht => (hV t (interior_subset ht).1).hasDerivWithinAt)
  intro t ht
  exact (hp t (interior_subset ht)).2

/-- In inversion coordinates the scalar solution is nonincreasing. -/
theorem invertedScalar_antitone
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    AntitoneOn (invertedScalar ε V) (Ioc 0 1) := by
  have hd : ∀ y ∈ Ioc 0 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ y) y := by
    intro y hy
    have harg : 0 ≤ y⁻¹ / ε := div_nonneg (inv_nonneg.mpr hy.1.le) hε.le
    exact (invertedScalar_equations (ne_of_gt hε) (ne_of_gt hy.1)
      (hV _ harg) (hflux _ harg)).1
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc (0 : ℝ) 1)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
  intro y hy
  have hyy := interior_subset hy
  exact (invertedScalar_positive hε hεsmall hV hflux hV0 hV₁0 y hyy.1 hyy.2).2.2.le

/-- After `x=1`, the product `t V(t)` is nondecreasing. -/
theorem equation30_weighted_monotone
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    MonotoneOn (fun t => t * V t) (Ici (1 / ε)) := by
  have hanti := invertedScalar_antitone hε hεsmall hV hflux hV0 hV₁0
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hcalc : ∀ r : ℝ, invertedScalar ε V (1 / (ε * r)) = ε * (r * V r) := by
    intro r
    have harg : (1 / (ε * r))⁻¹ / ε = r := by rw [one_div, inv_inv]; field_simp
    rw [invertedScalar, harg, one_div, div_inv_eq_mul]
    ring
  intro s hs t ht hst
  have hthreshold : 0 < 1 / ε := by positivity
  have hspos : 0 < s := hthreshold.trans_le hs
  have htpos : 0 < t := hthreshold.trans_le ht
  have hεs : 1 ≤ ε * s := by have := (div_le_iff₀ hε).mp hs; linarith only [this]
  have hεt : 1 ≤ ε * t := by have := (div_le_iff₀ hε).mp ht; linarith only [this]
  have hys : 1 / (ε * s) ∈ Ioc 0 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hεs⟩
  have hyt : 1 / (ε * t) ∈ Ioc 0 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hεt⟩
  have hyorder : 1 / (ε * t) ≤ 1 / (ε * s) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hst hε.le)
  have hm := hanti hyt hys hyorder
  rw [hcalc s, hcalc t] at hm
  exact (mul_le_mul_iff_right₀ hε).mp hm

/-- The reference solution can decrease only by a polynomial factor on a
bounded time interval.  This is the ratio estimate used in the relative
propagator argument. -/
theorem equation30_relative_ratio
    {ε Θ : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ Θ → V s ≤ Θ * V t := by
  have hpos := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0
  have hpre := equation30_prefix_monotone hε hεsmall hV hflux hV0 hV₁0
  have hpost := equation30_weighted_monotone hε hεsmall hV hflux hV0 hV₁0
  have hthreshold : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith only [hε, hεsmall])
  have hthreshold0 : 0 ≤ 1 / ε := by positivity
  intro s t hs hst ht
  have ht0 : 0 ≤ t := hs.trans hst
  have htpos := hpos t ht0
  by_cases htp : t ≤ 1 / ε
  · have hm := hpre ⟨hs, hst.trans htp⟩ ⟨ht0, htp⟩ hst
    exact hm.trans (le_mul_of_one_le_left htpos.le hΘ)
  · have htpost : 1 / ε ≤ t := le_of_not_ge htp
    by_cases hsp : s ≤ 1 / ε
    · have hbefore := hpre ⟨hs, hsp⟩ ⟨hthreshold0, le_rfl⟩ hsp
      have hafter := hpost (show 1 / ε ∈ Ici (1 / ε) by simp) htpost htpost
      have hmidpos := hpos (1 / ε) hthreshold0
      exact hbefore.trans ((le_mul_of_one_le_left hmidpos.le hthreshold).trans
        (hafter.trans (mul_le_mul_of_nonneg_right ht htpos.le)))
    · have hspost : 1 / ε ≤ s := le_of_not_ge hsp
      have hm := hpost hspost htpost hst
      have hspos := hpos s hs
      exact (le_mul_of_one_le_left hspos.le (hthreshold.trans hspost)).trans
        (hm.trans (mul_le_mul_of_nonneg_right ht htpos.le))

/-- The exact logarithmic-derivative equation wherever the scalar solution
does not vanish. -/
theorem equation30_hasDerivAt_logderivative
    {ε t : ℝ} {V V₁ : ℝ → ℝ}
    (hV : HasDerivAt V (V₁ t) t)
    (hflux : HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
      (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hVne : V t ≠ 0) :
    HasDerivAt (fun s => V₁ s / V s)
      (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) / (1 + (ε ^ 2 * t ^ 2) ^ 2) -
        (4 * (ε ^ 2) ^ 2 * t ^ 3 / (1 + (ε ^ 2 * t ^ 2) ^ 2)) * (V₁ t / V t) -
        (V₁ t / V t) ^ 2) t := by
  have hDne : 1 + (ε ^ 2 * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  exact ((equation30_second_derivative hflux).div hV hVne).congr_deriv
    (logDerivative_quotient_identity hDne hVne)

/-- The derivative of `t V(t)` is strictly positive after inversion. -/
theorem equation30_post_inversion_positive_derivative
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 1 / ε ≤ t → 0 < V t + t * V₁ t := by
  intro t ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : 0 < 1 / ε) ht
  have htne : t ≠ 0 := ne_of_gt htpos
  have hεt : 1 ≤ ε * t := by have := (div_le_iff₀ hε).mp ht; linarith only [this]
  have hypos : 0 < 1 / (ε * t) := by positivity
  have hy1 : 1 / (ε * t) ≤ 1 := (div_le_one (by positivity)).mpr hεt
  have hp := (invertedScalar_positive hε hεsmall hV hflux hV0 hV₁0
    (1 / (ε * t)) hypos hy1).2.2
  have harg : (1 / (ε * t))⁻¹ / ε = t := by rw [one_div, inv_inv]; field_simp
  have heq : invertedScalarDeriv ε V V₁ (1 / (ε * t)) =
      -((ε * t) ^ 2 * (V t + t * V₁ t)) := by
    rw [invertedScalarDeriv, harg]
    field_simp
    ring
  rw [heq] at hp
  have hprod : 0 < (ε * t) ^ 2 * (V t + t * V₁ t) := by linarith only [hp]
  exact pos_of_mul_pos_right hprod (sq_nonneg _)

/-- A uniform absolute logarithmic-derivative bound for the zero-slope
reference solution, valid on the whole forward interval. -/
theorem equation30_zero_slope_logderivative_bound
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    ∀ t, 0 ≤ t → |U₁ t / U t| ≤ 2 := by
  have hpos := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hupper : ∀ t, 0 ≤ t → U₁ t / U t ≤ 2 := by
    intro T hT
    have hd : ∀ t ∈ Icc 0 T,
        HasDerivAt (fun s => U₁ s / U s)
          (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) / (1 + (ε ^ 2 * t ^ 2) ^ 2) -
            (4 * (ε ^ 2) ^ 2 * t ^ 3 / (1 + (ε ^ 2 * t ^ 2) ^ 2)) * (U₁ t / U t) -
            (U₁ t / U t) ^ 2) t :=
      fun t ht => equation30_hasDerivAt_logderivative (hU t ht.1) (hfluxU t ht.1)
        (ne_of_gt (hpos t ht.1))
    have hfence := image_le_of_deriv_right_lt_deriv_boundary
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (B := fun _ => 2) (B' := fun _ => 0)
      (by simp only [hU₁0, hU0, div_one, Nat.ofNat_nonneg]) (fun t => hasDerivAt_const t 2)
      (fun t ht hboundary => by
        have ht0 := ht.1
        have hDge : 1 ≤ 1 + (ε ^ 2 * t ^ 2) ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
        have hDpos : 0 < 1 + (ε ^ 2 * t ^ 2) ^ 2 := zero_lt_one.trans_le hDge
        have hquo : 2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) /
            (1 + (ε ^ 2 * t ^ 2) ^ 2) ≤ 2 := by
          apply (div_le_iff₀ hDpos).mpr
          linarith only [mul_nonneg (sq_nonneg ε) (mul_nonneg (sq_nonneg ε) (sq_nonneg t)),
            sq_nonneg (ε ^ 2 * t ^ 2)]
        have hcoef : 0 ≤ 4 * (ε ^ 2) ^ 2 * t ^ 3 / (1 + (ε ^ 2 * t ^ 2) ^ 2) :=
          div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (pow_nonneg ht0 3))
            hDpos.le
        rw [hboundary]
        linarith only [hquo, hcoef])
    exact hfence ⟨hT, le_rfl⟩
  intro t ht
  apply abs_le.mpr
  refine ⟨?_, hupper t ht⟩
  by_cases hpre : t ≤ 1 / ε
  · have hεne : ε ≠ 0 := ne_of_gt hε
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 :=
      le_of_eq (by rw [div_pow, one_pow, mul_one_div, div_self (pow_ne_zero 2 hεne)])
    have hp := (equation30_positive (sq_nonneg ε)
      ((pow_le_pow_left₀ hε.le hεsmall 2).trans (by norm_num))
      (by positivity : 0 ≤ 1 / ε) hscale
      (fun s hs => hU s hs.1) (fun s hs => hfluxU s hs.1) hU0 (by rw [hU₁0]) t ⟨ht, hpre⟩).2
    have hq := div_nonneg hp (hpos t ht).le
    linarith only [hq]
  · have htpost : 1 / ε ≤ t := le_of_not_ge hpre
    have ht1 : 1 ≤ t := by
      have hbase : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith only [hεsmall])
      exact hbase.trans htpost
    have hcomb := equation30_post_inversion_positive_derivative hε hεsmall hU hfluxU hU0
      (by rw [hU₁0]) t htpost
    have hprod : 0 < t * (U₁ t + U t) := by
      linarith only [hcomb, mul_nonneg (sub_nonneg.mpr ht1) (hpos t ht).le]
    have hsum := pos_of_mul_pos_right hprod ht
    apply (le_div_iff₀ (hpos t ht)).mpr
    linarith only [hsum, hpos t ht]

/-- Reduction of order normalized by the reference value at the initial
time.  This is the form used for relative, rather than absolute, stability. -/
theorem reduction_of_order_relative
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hDc : ContinuousOn D (Icc a b))
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      v t = (u t / u a) * (v a + D a * (v₁ a - (u₁ a / u a) * v a) *
        ∫ s in a..t, (u a / u s) ^ 2 / D s) := by
  intro t ht
  have hane : u a ≠ 0 := hupos a ⟨le_rfl, ht.1.trans ht.2⟩
  have hint : (∫ s in a..t, (u a / u s) ^ 2 / D s) =
      (u a) ^ 2 * ∫ s in a..t, 1 / (D s * (u s) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext s
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hint, reduction_of_order hu hv hfu hfv hDc hD hupos t ht]
  field_simp

/-- The derivative counterpart of normalized reduction of order. -/
theorem reduction_of_order_derivative_relative
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      v₁ t = (u₁ t / u t) * v t +
        (u a / u t) * D a * (v₁ a - (u₁ a / u a) * v a) / D t := by
  intro t ht
  have hane : u a ≠ 0 := hupos a ⟨le_rfl, ht.1.trans ht.2⟩
  have hw := flux_wronskian_constant hu hv hfu hfv t ht
  field_simp [hupos t ht, hD t ht]
  linarith only [hw]

/-- A polynomial bound for the normalized reduction integral. -/
theorem relative_reduction_integral_bound
    {D u : ℝ → ℝ} {a b Θ : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ)
    (hDc : ContinuousOn D (Icc a b)) (huc : ContinuousOn u (Icc a b))
    (hD : ∀ s ∈ Icc a b, 1 ≤ D s)
    (hu : ∀ s ∈ Icc a b, 0 < u s)
    (hratio : ∀ s ∈ Icc a b, u a ≤ Θ * u s) :
    0 ≤ (∫ s in a..b, (u a / u s) ^ 2 / D s) ∧
      (∫ s in a..b, (u a / u s) ^ 2 / D s) ≤ Θ ^ 3 := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcont : ContinuousOn (fun s => (u a / u s) ^ 2 / D s) (Icc a b) :=
    ((continuousOn_const.div huc (fun s hs => ne_of_gt (hu s hs))).pow 2).div hDc
      (fun s hs => ne_of_gt (lt_of_lt_of_le zero_lt_one (hD s hs)))
  have hint : IntervalIntegrable (fun s => (u a / u s) ^ 2 / D s) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hcont
  have hbound : ∀ s ∈ Icc a b, (u a / u s) ^ 2 / D s ≤ Θ ^ 2 := by
    intro s hs
    have hq0 : 0 ≤ u a / u s := div_nonneg (hu a haI).le (hu s hs).le
    have hq : u a / u s ≤ Θ := (div_le_iff₀ (hu s hs)).mpr (hratio s hs)
    have hΘ0 : 0 ≤ Θ := hq0.trans hq
    have hq2 : (u a / u s) ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ hq0 hΘ0).mpr hq
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hD s hs))).mpr
    have hm := mul_le_mul_of_nonneg_left (hD s hs) (sq_nonneg Θ)
    linarith only [hq2, hm]
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro s hs
    exact div_nonneg (sq_nonneg _) (le_trans zero_le_one (hD s hs))
  · have hi := intervalIntegral.integral_mono_on hab hint
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Θ ^ 2) MeasureTheory.volume a b)
          hbound
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    have hm := mul_le_mul_of_nonneg_right (show b - a ≤ Θ by linarith only [ha, hb]) (sq_nonneg Θ)
    linarith only [hi, hm]

/-- A relative propagator estimate with an explicit polynomial loss.
The large reference amplitude enters only through `u b / u a`. -/
theorem relative_propagator_bound
    {D c u u₁ v v₁ : ℝ → ℝ} {a b Θ : ℝ}
    (hΘ : 1 ≤ Θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hDc : ContinuousOn D (Icc a b))
    (hD : ∀ t ∈ Icc a b, 1 ≤ D t ∧ D t ≤ 2 * Θ ^ 4)
    (hupos : ∀ t ∈ Icc a b, 0 < u t)
    (hlog : ∀ t ∈ Icc a b, |u₁ t / u t| ≤ 2)
    (hratio : ∀ t ∈ Icc a b, u a ≤ Θ * u t) :
    |v b| + |v₁ b| ≤ 20 * Θ ^ 8 * (u b / u a) * (|v a| + |v₁ a|) := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have huane : u a ≠ 0 := ne_of_gt (hupos a haI)
  have hubne : u b ≠ 0 := ne_of_gt (hupos b hbI)
  have hDne : ∀ t ∈ Icc a b, D t ≠ 0 :=
    fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one (hD t ht).1)
  have huc : ContinuousOn u (Icc a b) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  let N : ℝ := |v a| + |v₁ a|
  let E : ℝ := v₁ a - (u₁ a / u a) * v a
  let R : ℝ := u b / u a
  let J : ℝ := ∫ s in a..b, (u a / u s) ^ 2 / D s
  have hN : 0 ≤ N := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hR : 0 < R := div_pos (hupos b hbI) (hupos a haI)
  have hJ := relative_reduction_integral_bound ha hab hb hDc huc
    (fun t ht => (hD t ht).1) hupos hratio
  change 0 ≤ J ∧ J ≤ Θ ^ 3 at hJ
  have hE : |E| ≤ 2 * N := by
    calc
      |E| ≤ |v₁ a| + |(u₁ a / u a) * v a| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (v₁ a) ((u₁ a / u a) * v a)
      _ = |v₁ a| + |u₁ a / u a| * |v a| := by rw [abs_mul]
      _ ≤ |v₁ a| + 2 * |v a| :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (hlog a haI) (abs_nonneg (v a)))
      _ ≤ 2 * N := by dsimp only [N]; linarith only [abs_nonneg (v₁ a)]
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hpow78 : Θ ^ 7 ≤ Θ ^ 8 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow68 : Θ ^ 6 ≤ Θ ^ 8 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow8 : 1 ≤ Θ ^ 8 := one_le_pow₀ hΘ
  have hDNJ : D a * |E| * J ≤ 4 * Θ ^ 8 * N := by
    have hΘ4 : 0 ≤ 2 * Θ ^ 4 := mul_nonneg zero_le_two (pow_nonneg hΘ0 4)
    have hm := mul_le_mul
      (mul_le_mul (hD a haI).2 hE (abs_nonneg _) hΘ4) hJ.2 hJ.1
      (mul_nonneg hΘ4 (mul_nonneg zero_le_two hN))
    have hp := mul_le_mul_of_nonneg_right hpow78 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hN)
    linarith only [hm, hp]
  have hval := reduction_of_order_relative hu hv hfu hfv hDc hDne
    (fun t ht => ne_of_gt (hupos t ht)) b hbI
  change v b = R * (v a + D a * E * J) at hval
  have hvbound : |v b| ≤ R * (5 * Θ ^ 8 * N) := by
    rw [hval, abs_mul, abs_of_pos hR]
    apply mul_le_mul_of_nonneg_left _ hR.le
    have htri := abs_add_le (v a) (D a * E * J)
    have hDan : 0 ≤ D a := le_trans zero_le_one (hD a haI).1
    rw [abs_mul, abs_mul, abs_of_nonneg hDan, abs_of_nonneg hJ.1] at htri
    have hn : |v a| ≤ N := le_add_of_nonneg_right (abs_nonneg _)
    have hp := mul_le_mul_of_nonneg_right hpow8 hN
    linarith only [htri, hn, hp, hDNJ]
  have hq0 : 0 ≤ u a / u b := div_nonneg (hupos a haI).le (hupos b hbI).le
  have hq : u a / u b ≤ Θ := (div_le_iff₀ (hupos b hbI)).mpr (hratio b hbI)
  have hq2 : (u a / u b) ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ hq0 hΘ0).mpr hq
  have hsecond : (u a / u b) ^ 2 * D a * |E| / D b ≤ 4 * Θ ^ 8 * N := by
    have hnum : (u a / u b) ^ 2 * D a * |E| ≤ 4 * Θ ^ 8 * N := by
      have hm := mul_le_mul
        (mul_le_mul hq2 (hD a haI).2 (le_trans zero_le_one (hD a haI).1) (sq_nonneg Θ))
        hE (abs_nonneg _) (mul_nonneg (sq_nonneg Θ) (mul_nonneg zero_le_two (pow_nonneg hΘ0 4)))
      have hp := mul_le_mul_of_nonneg_right hpow68 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hN)
      linarith only [hm, hp]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hD b hbI).1)).mpr
    have hm := mul_le_mul_of_nonneg_left (hD b hbI).1
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (pow_nonneg hΘ0 8)) hN)
    linarith only [hnum, hm]
  have hder := reduction_of_order_derivative_relative hu hv hfu hfv hDne
    (fun t ht => ne_of_gt (hupos t ht)) b hbI
  have heq : (u a / u b) * D a * E / D b = R * ((u a / u b) ^ 2 * D a * E / D b) := by
    have h1 : R * (u a / u b) = 1 := (div_mul_div_cancel₀ huane).trans (div_self hubne)
    calc (u a / u b) * D a * E / D b = (R * (u a / u b)) * ((u a / u b) * D a * E / D b) := by
          rw [h1, one_mul]
      _ = R * ((u a / u b) ^ 2 * D a * E / D b) := by ring
  change v₁ b = (u₁ b / u b) * v b + (u a / u b) * D a * E / D b at hder
  rw [heq] at hder
  have hv₁bound : |v₁ b| ≤ 2 * |v b| + R * (4 * Θ ^ 8 * N) := by
    rw [hder]
    calc
      |(u₁ b / u b) * v b + R * ((u a / u b) ^ 2 * D a * E / D b)|
          ≤ |(u₁ b / u b) * v b| + |R * ((u a / u b) ^ 2 * D a * E / D b)| := abs_add_le _ _
      _ = |u₁ b / u b| * |v b| + R * ((u a / u b) ^ 2 * D a * |E| / D b) := by
        simp only [abs_mul, abs_div, abs_pow, abs_of_pos hR,
          abs_of_pos (hupos a haI), abs_of_pos (hupos b hbI),
          abs_of_nonneg (le_trans zero_le_one (hD a haI).1),
          abs_of_nonneg (le_trans zero_le_one (hD b hbI).1)]
      _ ≤ 2 * |v b| + R * (4 * Θ ^ 8 * N) := by
        exact add_le_add (mul_le_mul_of_nonneg_right (hlog b hbI) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hsecond hR.le)
  change |v b| + |v₁ b| ≤ 20 * Θ ^ 8 * R * N
  have hRN : 0 ≤ Θ ^ 8 * R * N := mul_nonneg (mul_nonneg (pow_nonneg hΘ0 8) hR.le) hN
  linarith only [hvbound, hv₁bound, hRN]

/-- The ideal scalar propagator has only a polynomial loss relative to the
zero-slope growing solution.  This proves the reference propagator estimate
used before (32), with the explicit constant `20`. -/
theorem equation30_relative_propagator
    {ε Θ a b : ℝ} {U U₁ Y Y₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t) t) :
    |Y b| + |Y₁ b| ≤ 20 * Θ ^ 8 * (U b / U a) * (|Y a| + |Y₁ a|) := by
  have hp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hl := equation30_zero_slope_logderivative_bound hε hεsmall hU hfluxU hU0 hU₁0
  have hr := equation30_relative_ratio hε hεsmall hΘ hU hfluxU hU0 (by rw [hU₁0])
  apply relative_propagator_bound hΘ ha hab hb
    (fun t ht => hU t (ha.trans ht.1)) hY
    (fun t ht => hfluxU t (ha.trans ht.1)) hfluxY
    (continuous_const.add ((continuous_const.mul (continuous_pow 2)).pow 2)).continuousOn
  · intro t ht
    have ht0 : 0 ≤ t := ha.trans ht.1
    have htΘ : t ≤ Θ := ht.2.trans hb
    have heps4 : ε ^ 4 ≤ 1 :=
      (pow_le_pow_left₀ hε.le (hεsmall.trans (by norm_num)) 4).trans_eq (one_pow 4)
    have ht4 : t ^ 4 ≤ Θ ^ 4 := pow_le_pow_left₀ ht0 htΘ 4
    have hΘ4 : 1 ≤ Θ ^ 4 := one_le_pow₀ hΘ
    have hm := mul_le_mul heps4 ht4 (pow_nonneg ht0 4) zero_le_one
    constructor <;> linarith only [hΘ4, hm, sq_nonneg (ε ^ 2 * t ^ 2)]
  · intro t ht
    exact hp t (ha.trans ht.1)
  · intro t ht
    exact hl t (ha.trans ht.1)
  · intro t ht
    exact hr a t ha ht.1 (ht.2.trans hb)

/-- The coarse upper barrier for the exact inverted Riccati equation. -/
theorem inverted_riccati_le_four
    {ε T : ℝ} {z : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hscale : ε * T ≤ 1)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (invertedRiccati ε t (z t)) t)
    (hz0 : z 0 ≤ 4) :
    ∀ t ∈ Icc 0 T, z t ≤ 4 := by
  apply riccati_le_four hz hz0
  · intro t ht
    have ht0 := ht.1
    have hDpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
    apply (div_le_iff₀ hDpos).mpr
    linarith only [mul_nonneg (sq_nonneg ε) (sq_nonneg (1 - ε * t)),
        show 0 ≤ (1 - ε * t) ^ 4 by positivity]
  · intro t ht
    have hprod := mul_le_mul_of_nonneg_left ht.2.le hε.le
    have hprod0 := mul_nonneg hε.le ht.1
    have hy0 : 0 ≤ 1 - ε * t := by linarith only [hscale, hprod]
    have hy1 : 1 - ε * t ≤ 1 := by linarith only [hprod0]
    have hy3 : (1 - ε * t) ^ 3 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hy0 hy1 3
    have hDpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hy3 (show 0 ≤ 4 * ε by positivity)
    linarith only [hεsmall, hm, show 0 ≤ (1 - ε * t) ^ 4 by positivity]

/-- The inverted logarithmic derivative remains in `[0,4]`, derived
directly from the scalar equation and its endpoint conditions. -/
theorem inversion_riccati_range
    {ε a : ℝ} {f f₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (ha : 0 ≤ a)
    (hf : ∀ y ∈ Icc a 1, HasDerivAt f (f₁ y) y)
    (hflux : ∀ y ∈ Icc a 1, HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / ε ^ 2 - 2 * y ^ 2) * f y) y)
    (hf1 : 0 < f 1) (hf₁1 : f₁ 1 < 0)
    (hinit : -ε * f₁ 1 / f 1 ≤ 4) :
    ∀ y ∈ Icc a 1, 0 ≤ -ε * f₁ y / f y ∧ -ε * f₁ y / f y ≤ 4 := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hp := inversion_positive (sq_pos_of_pos hε) (by nlinarith only [hε, hεsmall] : ε ^ 2 ≤ 1)
    ha hf hflux hf1 hf₁1
  have hmirror : ∀ t ∈ Icc 0 ((1 - a) / ε), 1 - ε * t ∈ Icc a 1 := by
    intro t ht
    have hu : ε * t ≤ 1 - a := by
      have := (le_div_iff₀ hε).mp ht.2
      linarith only [this]
    have hl := mul_nonneg hε.le ht.1
    constructor <;> linarith only [hu, hl]
  have hscale : ε * ((1 - a) / ε) ≤ 1 := by field_simp; linarith only [ha]
  have hz : ∀ t ∈ Icc 0 ((1 - a) / ε),
      HasDerivAt (fun s => -ε * f₁ (1 - ε * s) / f (1 - ε * s))
        (invertedRiccati ε t (-ε * f₁ (1 - ε * t) / f (1 - ε * t))) t := by
    intro t ht
    exact hasDerivAt_inverted_logderivative hεne
      (ne_of_gt (hp (1 - ε * t) (hmirror t ht)).2.1)
      (hf _ (hmirror t ht)) (hflux _ (hmirror t ht))
  have hbound := inverted_riccati_le_four hε hεsmall hscale hz (by simpa only [mul_zero, sub_zero,
      neg_mul] using hinit)
  intro y hy
  have ht : (1 - y) / ε ∈ Icc 0 ((1 - a) / ε) :=
    ⟨div_nonneg (sub_nonneg.mpr hy.2) hε.le,
      div_le_div_of_nonneg_right (by linarith only [hy, hy.1]) hε.le⟩
  have heq : 1 - ε * ((1 - y) / ε) = y := by field_simp; ring
  constructor
  · exact div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hε.le) (hp y hy).2.2.le) (hp y hy).2.1.le
  · simpa only [heq] using hbound ((1 - y) / ε) ht

/-- The absolute Riccati range for the original scalar initial value problem. -/
theorem equation30_inverted_riccati_range
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 →
      0 ≤ -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y ∧
      -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y ≤ 4 := by
  have hinit := invertedScalar_initial_bound hε hεsmall
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  intro y hy hy1
  have heqs : ∀ s ∈ Icc y 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ s) s ∧
      HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
        ((2 / ε ^ 2 - 2 * s ^ 2) * invertedScalar ε V s) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hy hs.1
    have harg : 0 ≤ s⁻¹ / ε := by positivity
    exact invertedScalar_equations (ne_of_gt hε) (ne_of_gt hspos)
      (hV _ harg) (hflux _ harg)
  exact inversion_riccati_range hε hεsmall hy.le
    (fun s hs => (heqs s hs).1) (fun s hs => (heqs s hs).2)
    hinit.1 hinit.2.1 hinit.2.2 y ⟨le_rfl, hy1⟩

/-- The ideal next-frame numerator in inversion coordinates. -/
def idealFrameNumerator (ε y z : ℝ) : ℝ :=
  -1 + (1 + y ^ 4) * z ^ 2 + ε ^ 2 * y ^ 2 - 2 * ε * z * y ^ 3

/-- The ideal next-frame denominator divided by `x²`, where `y=1/x`. -/
def idealFrameDenominator (ε y z : ℝ) : ℝ :=
  1 - ε ^ 2 * y ^ 2 + 2 * ε * z * y ^ 3

/-- The two exact algebraic identities used for the ideal frame renewal. -/
theorem ideal_frame_identities {ε y z : ℝ} (hy : y ≠ 0) :
    (y⁻¹) ^ 2 + ε ^ 2 + (-2 * ε * y⁻¹) * (ε * y - z * y ^ 2) =
      idealFrameDenominator ε y z / y ^ 2 ∧
    -1 + ε ^ 2 * (y⁻¹) ^ 2 + (1 + (y⁻¹) ^ 4) * (ε * y - z * y ^ 2) ^ 2 +
      (y⁻¹) ^ 2 * (-2 * ε * y⁻¹) * (ε * y - z * y ^ 2) = idealFrameNumerator ε y z := by
  constructor <;> simp only [idealFrameDenominator, idealFrameNumerator] <;> field_simp <;> ring

/-- Explicit ideal frame-renewal bounds obtained from the Riccati estimate.
The constants are deliberately generous absolute constants. -/
theorem ideal_frame_bounds
    {ε y z : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4)
    (hy : 0 ≤ y) (hysmall : y ≤ 1 / 2) (hz : 0 ≤ z) (hzupper : z ≤ 4)
    (herr : |z ^ 2 - 2 / (1 + y ^ 4)| ≤ 360 * ε) :
    1 / 2 ≤ idealFrameDenominator ε y z ∧
      |idealFrameNumerator ε y z - 1| ≤ 730 * ε ∧
      |idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1| ≤
        y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 ∧
      |idealFrameNumerator ε y z / idealFrameDenominator ε y z - 1| ≤ 1500 * ε := by
  have hy1 : y ≤ 1 := hysmall.trans (by norm_num)
  have hy2 : y ^ 2 ≤ 1 := pow_le_one₀ hy hy1
  have hy3 : y ^ 3 ≤ 1 := pow_le_one₀ hy hy1
  have hy4 : y ^ 4 ≤ 1 := pow_le_one₀ hy hy1
  have hy3n : 0 ≤ y ^ 3 := pow_nonneg hy 3
  have hy4n : 0 ≤ y ^ 4 := pow_nonneg hy 4
  have hDpos : 0 < 1 + y ^ 4 := add_pos_of_pos_of_nonneg one_pos hy4n
  have hDn : 0 ≤ 1 + y ^ 4 := hDpos.le
  have hTn : 0 ≤ ε ^ 2 * y ^ 2 := mul_nonneg (sq_nonneg ε) (sq_nonneg y)
  have hTsquare : ε ^ 2 * y ^ 2 ≤ ε ^ 2 := mul_le_of_le_one_right (sq_nonneg ε) hy2
  have hTsmall : ε ^ 2 * y ^ 2 ≤ 1 / 16 :=
    hTsquare.trans ((pow_le_pow_left₀ hε hεsmall 2).trans_eq (by norm_num))
  have hTε : ε ^ 2 * y ^ 2 ≤ ε :=
    hTsquare.trans (pow_le_of_le_one hε (hεsmall.trans (by norm_num)) two_ne_zero)
  have h2ε : 0 ≤ 2 * ε := mul_nonneg zero_le_two hε
  have hUn : 0 ≤ 2 * ε * z * y ^ 3 := mul_nonneg (mul_nonneg h2ε hz) hy3n
  have hUlocal : 2 * ε * z * y ^ 3 ≤ 8 * ε * y ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hzupper (mul_nonneg h2ε hy3n)
    linarith only [hm]
  have hUε : 2 * ε * z * y ^ 3 ≤ 8 * ε := by
    have hm := mul_le_mul_of_nonneg_left hy3 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hε)
    linarith only [hm, hUlocal]
  have hB : 1 / 2 ≤ idealFrameDenominator ε y z := by
    unfold idealFrameDenominator
    linarith only [hTsmall, hUn]
  have hroot : 1 ≤ sqrt (1 + y ^ 4) := one_le_sqrt.mpr (le_add_of_nonneg_right hy4n)
  have hrootpos : 0 < sqrt (1 + y ^ 4) := zero_lt_one.trans_le hroot
  have hrootupper : sqrt (1 + y ^ 4) ≤ 1 + y ^ 4 :=
    sqrt_le_self_iff.mpr (Or.inr (le_add_of_nonneg_right hy4n))
  have hDerr : |(1 + y ^ 4) * (z ^ 2 - 2 / (1 + y ^ 4))| ≤ 720 * ε := by
    rw [abs_mul, abs_of_nonneg hDn]
    have hm := mul_le_mul_of_nonneg_left herr hDn
    have hu := mul_le_mul_of_nonneg_right (show 1 + y ^ 4 ≤ 2 by linarith only [hy4])
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 360) hε)
    linarith only [hm, hu]
  have hNrewrite : idealFrameNumerator ε y z - 1 =
      (1 + y ^ 4) * (z ^ 2 - 2 / (1 + y ^ 4)) + ε ^ 2 * y ^ 2 - 2 * ε * z * y ^ 3 := by
    rw [mul_sub, mul_div_cancel₀ (2 : ℝ) hDpos.ne']
    unfold idealFrameNumerator
    ring
  have hN : |idealFrameNumerator ε y z - 1| ≤ 730 * ε := by
    rw [hNrewrite]
    generalize (1 + y ^ 4) * (z ^ 2 - 2 / (1 + y ^ 4)) = w at hDerr ⊢
    obtain ⟨hl, hu⟩ := abs_le.mp hDerr
    apply abs_le.mpr
    constructor <;> linarith only [hl, hu, hTn, hTε, hUn, hUε, hε]
  have hA : |idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1| ≤
      y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 := by
    have heq : idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1 =
        (idealFrameDenominator ε y z - sqrt (1 + y ^ 4)) / sqrt (1 + y ^ 4) := by
      rw [sub_div, div_self hrootpos.ne']
    rw [heq, abs_div, abs_of_pos hrootpos]
    apply (div_le_iff₀ hrootpos).mpr
    have h8 : 0 ≤ 8 * ε * y ^ 3 := mul_nonneg (mul_nonneg (by norm_num) hε) hy3n
    have hsmall : |idealFrameDenominator ε y z - sqrt (1 + y ^ 4)| ≤
        y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 := by
      unfold idealFrameDenominator
      apply abs_le.mpr
      constructor <;> linarith only [hroot, hrootupper, hUlocal, hTn, hUn, hy4n, h8]
    have hm := mul_le_mul_of_nonneg_left hroot (add_nonneg (add_nonneg hy4n hTn) h8)
    linarith only [hsmall, hm]
  refine ⟨hB, hN, hA, ?_⟩
  have hBpos : 0 < idealFrameDenominator ε y z := lt_of_lt_of_le (by norm_num) hB
  have heq : idealFrameNumerator ε y z / idealFrameDenominator ε y z - 1 =
      (idealFrameNumerator ε y z - idealFrameDenominator ε y z) / idealFrameDenominator ε y z := by
    rw [sub_div, div_self hBpos.ne']
  rw [heq, abs_div, abs_of_pos hBpos]
  apply (div_le_iff₀ hBpos).mpr
  have hdiff : |idealFrameNumerator ε y z - idealFrameDenominator ε y z| ≤ 739 * ε := by
    obtain ⟨hl, hu⟩ := abs_le.mp hN
    unfold idealFrameDenominator
    apply abs_le.mpr
    constructor <;> linarith only [hl, hu, hTn, hTε, hUn, hUε]
  have hm := mul_le_mul_of_nonneg_left hB (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1500) hε)
  linarith only [hdiff, hm, hε]

/-- Ideal frame renewal follows from the scalar initial value problem;
the Riccati range and approximation are proved upstream in this file. -/
theorem equation30_ideal_frame_bounds
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 / 2 →
      let z := -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y
      1 / 2 ≤ idealFrameDenominator ε y z ∧
        |idealFrameNumerator ε y z - 1| ≤ 730 * ε ∧
        |idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1| ≤
          y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 ∧
        |idealFrameNumerator ε y z / idealFrameDenominator ε y z - 1| ≤ 1500 * ε := by
  intro y hy hysmall
  have hr := equation30_inverted_riccati_range hε hεsmall hV hflux hV0 hV₁0 y hy (by linarith only [
      hε, hεsmall, hysmall])
  have he := equation30_inverted_riccati_error hε hεsmall hV hflux hV0 hV₁0 y hy hysmall
  exact ideal_frame_bounds hε.le hεsmall hy.le hysmall hr.1 hr.2 he

/-- The ideal shear contribution to the target-frame compression has the
required negative sign and reciprocal target-scale lower magnitude. -/
theorem ideal_target_compression
    {H ε x : ℝ} (hH : 0 ≤ H) (hε : 0 ≤ ε) (hx : 1 ≤ x) :
    -2 * H * ε * x ^ 3 / (1 + x ^ 4) ≤ -H * ε / x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hDpos : 0 < 1 + x ^ 4 := by positivity
  apply (div_le_div_iff₀ hDpos hxpos).mpr
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
  have hp := mul_nonneg (mul_nonneg hH hε) (sub_nonneg.mpr hx4)
  linarith only [hp]

end EulerPacketGrowth
