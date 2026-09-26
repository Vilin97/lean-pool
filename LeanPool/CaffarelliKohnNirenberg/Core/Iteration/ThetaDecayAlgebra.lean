/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RpowSquares

/-!
# The algebraic combination step of the combined decay inequality

This file formalizes the purely algebraic step in the proof of
`lem:theta-decay` of `paper/ckn.tex`, the "Combined decay inequality".  The
paper combines three analytic estimates into the one-step decay of the
combined quantity

  `θ(z,ρ) = α(z,ρ) + β(z,ρ) + κ⁻⁴δ(z,ρ)²`   (`eq:theta`)

at the smaller radius `κρ`, where `κ ∈ (0,1/2]` is the scale ratio.  The three
inputs, each carried here as a hypothesis, are the Caccioppoli inequality
`eq:caccioppoli`, the pressure decay estimate `eq:pressure-decay` of
`thm:pressure-decay`, and the Gagliardo–Nirenberg inequality `eq:gagliardo`
of `cor:gagliardo`.

The conclusions formalized are the two displayed inequalities
`eq:theta-decay-1` and `eq:theta-decay-2` of the lemma:

  `θ(κρ) ≤ C₂₇ κ^{2/3} θ(ρ) + C₂₇ κ^{-5}(β(ρ)^{1/2} + β(ρ)) θ(ρ)
            + C₂₈ κ^{-1/2} θ(ρ)^{1/2} λ(ρ)^{1/2} + C₂₈ κ^{-3} λ(ρ)`,

and, when `θ(ρ) ≤ 1`, the same with `β(ρ)^{1/2} + β(ρ)` replaced by
`2 θ(ρ)^{1/2}`.  The constants `C₂₇` and `C₂₈` are the explicit combinations
`thetaDecayC₂₇` and `thetaDecayC₂₈` of the input constants `C₉, C₁₄, C₁₅,
C₂₅, C₂₆` displayed at the end of the paper's proof.

No analytic content enters: every step is an elementary real inequality, using
`√β ≤ √θ` from `β ≤ θ`, `δ ≤ κ²√θ` from `κ⁻⁴δ² ≤ θ`, the Young-type
square-root bounds for `√γ`, and the power comparisons `κ ≤ κ^{2/3}` and
`κ⁻¹ ≤ κ^{-5}` valid for `0 < κ ≤ 1/2`.
-/

public section

noncomputable section

namespace CKN

/-! ### The quantity and the constants of `lem:theta-decay` -/

/-- The combined quantity `θ = α + β + κ⁻⁴δ²` of `eq:theta`.

The fourth power of the scale ratio enters as `κ ^ (-4 : ℝ)` so that the
statement is uniform with the remaining real powers of `κ` in the decay
estimates; for `κ > 0` this is the paper's `κ⁻⁴`. -/
@[expose]
def thetaValue (κ α β δ : ℝ) : ℝ := α + β + κ ^ (-4 : ℝ) * δ ^ 2

/-- The absolute constant `C₂₇` of `eq:theta-decay-1`, in terms of the input
constants `C₉` (Gagliardo–Nirenberg), `C₁₄` (pressure) and `C₂₅`
(Caccioppoli): the paper's `3C₁₄² + C₂₅(1 + 2C₉^{1/2}) + 2C₂₅C₉^{1/2}`. -/
def thetaDecayC₂₇ (C₉ C₁₄ C₂₅ : ℝ) : ℝ :=
  3 * C₁₄ ^ 2 + C₂₅ * (1 + 2 * Real.sqrt C₉) + 2 * C₂₅ * Real.sqrt C₉

/-- The constant `C₂₈ = C₂₈(q)` of `eq:theta-decay-1`, in terms of `C₉`,
`C₁₅` (pressure) and `C₂₆` (Caccioppoli): the paper's `3C₁₅² + 2C₂₆C₉^{1/2}`. -/
def thetaDecayC₂₈ (C₉ C₁₅ C₂₆ : ℝ) : ℝ :=
  3 * C₁₅ ^ 2 + 2 * C₂₆ * Real.sqrt C₉

/-! ### Elementary real inequalities -/

/-- The three-square inequality `(x+y+z)² ≤ 3(x²+y²+z²)`, used for the square
of the three-term pressure bound. -/
private lemma sq_sum_three_le (x y z : ℝ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith only [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

/-- A product of two real powers of a positive base adds the exponents. -/
private lemma rpow_mul_of_add {κ : ℝ} (hκ : 0 < κ) {a b c : ℝ} (h : a + b = c) :
    κ ^ a * κ ^ b = κ ^ c := by
  rw [← Real.rpow_add hκ, h]



/-- `κ^{-4}κ⁻¹ = κ^{-5}` for `κ > 0`. -/
private lemma rpow_neg_four_mul_neg_one {κ : ℝ} (hκ : 0 < κ) :
    κ ^ (-4 : ℝ) * κ ^ (-1 : ℝ) = κ ^ (-5 : ℝ) :=
  rpow_mul_of_add hκ (by norm_num : (-4 : ℝ) + -1 = -5)

/-- `κ^{-4}κ = κ^{-3}` for `κ > 0`. -/
private lemma rpow_neg_four_mul_one {κ : ℝ} (hκ : 0 < κ) :
    κ ^ (-4 : ℝ) * κ = κ ^ (-3 : ℝ) := by
  calc κ ^ (-4 : ℝ) * κ = κ ^ (-4 : ℝ) * κ ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = κ ^ ((-4 : ℝ) + 1) := (Real.rpow_add hκ _ _).symm
    _ = κ ^ (-3 : ℝ) := by norm_num

/-- `√(x+y) ≤ √x + √y` for `x, y ≥ 0`. -/
private lemma sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith only [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x,
      Real.sqrt_nonneg y, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  rwa [Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt x + Real.sqrt y)] at h

/-- `√T · √(√T) · √(√b) ≤ T` when `0 ≤ b ≤ T`; this is the bound
`b^{1/4}T^{1/4} ≤ T^{1/2}` used term by term in the paper's energy estimate. -/
private lemma sqrt_mul_sqrt_sqrt_le {T b : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T) :
    Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt b) ≤ T := by
  have hT : 0 ≤ T := le_trans hb hbT
  refine le_of_sq_le_sq ?_ hT
  have hsqrtTb : Real.sqrt (T * b) ≤ T := by
    refine le_of_sq_le_sq ?_ hT
    rw [Real.sq_sqrt (by positivity : 0 ≤ T * b)]
    nlinarith only [hbT, hT]
  calc (Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt b)) ^ 2
      = T * Real.sqrt T * Real.sqrt b := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hT, Real.sq_sqrt (Real.sqrt_nonneg T),
          Real.sq_sqrt (Real.sqrt_nonneg b)]
    _ = T * Real.sqrt (T * b) := by rw [Real.sqrt_mul hT]; ring
    _ ≤ T * T := mul_le_mul_of_nonneg_left hsqrtTb hT
    _ = T ^ 2 := by ring

/-- `√(√T) · √(√b) ≤ √T` when `b ≤ T`. -/
private lemma sqrt_sqrt_mul_sqrt_sqrt_le {T b : ℝ} (hbT : b ≤ T) :
    Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt b) ≤ Real.sqrt T := by
  calc Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt b)
      ≤ Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt T) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hbT))
          (Real.sqrt_nonneg _)
    _ = Real.sqrt T := by rw [Real.mul_self_sqrt (Real.sqrt_nonneg T)]

/-- The pressure bound `δ ≤ κ²√T` implied by `κ^{-4}δ² ≤ T`. -/
private lemma delta_le_kappa_sq_sqrt {κ δ T : ℝ} (hκ : 0 < κ)
    (h : κ ^ (-4 : ℝ) * δ ^ 2 ≤ T) : δ ≤ κ ^ (2 : ℝ) * Real.sqrt T := by
  have hκ4 : 0 < κ ^ (4 : ℝ) := Real.rpow_pos_of_pos hκ 4
  have hcancel : κ ^ (4 : ℝ) * κ ^ (-4 : ℝ) = 1 := by
    rw [rpow_mul_of_add hκ (by norm_num : (4 : ℝ) + -4 = 0), Real.rpow_zero]
  have hsq : δ ^ 2 ≤ κ ^ (4 : ℝ) * T := by
    have h' := mul_le_mul_of_nonneg_left h hκ4.le
    rwa [← mul_assoc, hcancel, one_mul] at h'
  have hT : 0 ≤ T := le_trans (by positivity : 0 ≤ κ ^ (-4 : ℝ) * δ ^ 2) h
  have hκsq : (κ ^ (2 : ℝ)) ^ 2 = κ ^ (4 : ℝ) := by
    rw [pow_two, rpow_mul_of_add hκ (by norm_num : (2 : ℝ) + 2 = 4)]
  have hrhs : (κ ^ (2 : ℝ) * Real.sqrt T) ^ 2 = κ ^ (4 : ℝ) * T := by
    rw [mul_pow, hκsq, Real.sq_sqrt hT]
  refine le_of_sq_le_sq ?_ (by positivity)
  rwa [hrhs]

/-! ### The combination step -/

private lemma thetaDecay_algebra_hγsqrt_1 :
    ∀ {κ C₉ α β γ δ : ℝ},
      (0 : ℝ) ≤ C₉ →
        γ ≤ C₉ * √α * √β + C₉ * α →
          let T : ℝ := α + β + κ ^ (-4 : ℝ) * δ ^ (2 : ℕ);
          (0 : ℝ) ≤ T → α ≤ T → √γ ≤ √C₉ * (√√T * √√β + √T)
    := by
  intro κ C₉ α β γ δ hC₉ hC T hT_nonneg hαT
  have hγ' : γ ≤ C₉ * (Real.sqrt T * Real.sqrt β + T) := by
    have h1 : C₉ * Real.sqrt α * Real.sqrt β ≤ C₉ * (Real.sqrt T * Real.sqrt β) := by
      have h : Real.sqrt α * Real.sqrt β ≤ Real.sqrt T * Real.sqrt β :=
        mul_le_mul (Real.sqrt_le_sqrt hαT) le_rfl (Real.sqrt_nonneg β)
          (Real.sqrt_nonneg T)
      calc C₉ * Real.sqrt α * Real.sqrt β = C₉ * (Real.sqrt α * Real.sqrt β) := by ring
        _ ≤ C₉ * (Real.sqrt T * Real.sqrt β) := mul_le_mul_of_nonneg_left h hC₉
    have h2 : C₉ * α ≤ C₉ * T := mul_le_mul_of_nonneg_left hαT hC₉
    calc γ ≤ C₉ * Real.sqrt α * Real.sqrt β + C₉ * α := hC
      _ ≤ C₉ * (Real.sqrt T * Real.sqrt β) + C₉ * T := add_le_add h1 h2
      _ = C₉ * (Real.sqrt T * Real.sqrt β + T) := by ring
  calc Real.sqrt γ ≤ Real.sqrt (C₉ * (Real.sqrt T * Real.sqrt β + T)) :=
        Real.sqrt_le_sqrt hγ'
    _ = Real.sqrt C₉ * Real.sqrt (Real.sqrt T * Real.sqrt β + T) := by
        rw [Real.sqrt_mul hC₉]
    _ ≤ Real.sqrt C₉ * (Real.sqrt (Real.sqrt T * Real.sqrt β) + Real.sqrt T) :=
        mul_le_mul_of_nonneg_left
          (sqrt_add_le' (mul_nonneg (Real.sqrt_nonneg T) (Real.sqrt_nonneg β))
            hT_nonneg)
          (Real.sqrt_nonneg C₉)
    _ = Real.sqrt C₉ *
          (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) + Real.sqrt T) := by
        rw [Real.sqrt_mul (Real.sqrt_nonneg T)]

private lemma thetaDecay_algebra_hT2_2 :
    ∀ {κ C₉ C₂₅ α β γ δ : ℝ},
      (0 : ℝ) < κ →
        (0 : ℝ) ≤ C₂₅ →
          let T : ℝ := α + β + κ ^ (-4 : ℝ) * δ ^ (2 : ℕ);
          (0 : ℝ) ≤ T →
            α ≤ T →
              √T * √√T * √√β ≤ T →
                κ ^ (-1 : ℝ) ≤ κ ^ (-5 : ℝ) →
                  √γ ≤ √C₉ * (√√T * √√β + √T) →
                    C₂₅ * κ ^ (-1 : ℝ) * √α * √β * √γ ≤ (2 : ℝ) * C₂₅ * √C₉ * κ ^ (-5 : ℝ) * √β * T
    := by
  intro κ C₉ C₂₅ α β γ δ hκ hC₂₅ T hT_nonneg hαT hcore hκinv_le hγsqrt
  have hprod : Real.sqrt α * Real.sqrt β * Real.sqrt γ ≤
      2 * Real.sqrt C₉ * Real.sqrt β * T := by
    have h1 : Real.sqrt α * Real.sqrt β * Real.sqrt γ ≤ Real.sqrt C₉ *
        (Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) * Real.sqrt β
          + Real.sqrt T * Real.sqrt β * Real.sqrt T) := by
      calc Real.sqrt α * Real.sqrt β * Real.sqrt γ
          ≤ Real.sqrt T * Real.sqrt β *
              (Real.sqrt C₉ *
                (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) + Real.sqrt T)) :=
            mul_le_mul
              (mul_le_mul (Real.sqrt_le_sqrt hαT) le_rfl (Real.sqrt_nonneg β)
                (Real.sqrt_nonneg T))
              hγsqrt (Real.sqrt_nonneg γ)
              (mul_nonneg (Real.sqrt_nonneg T) (Real.sqrt_nonneg β))
        _ = Real.sqrt C₉ *
              (Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β)
                  * Real.sqrt β
                + Real.sqrt T * Real.sqrt β * Real.sqrt T) := by ring
    have hb1 : Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β)
          * Real.sqrt β ≤ T * Real.sqrt β :=
      mul_le_mul_of_nonneg_right hcore (Real.sqrt_nonneg β)
    have hb2 : Real.sqrt T * Real.sqrt β * Real.sqrt T ≤ T * Real.sqrt β := by
      have heq : Real.sqrt T * Real.sqrt β * Real.sqrt T = T * Real.sqrt β := by
        rw [mul_assoc, mul_comm (Real.sqrt β) (Real.sqrt T), ← mul_assoc,
          Real.mul_self_sqrt hT_nonneg]
      exact le_of_eq heq
    have h2 : Real.sqrt C₉ *
          (Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) * Real.sqrt β
            + Real.sqrt T * Real.sqrt β * Real.sqrt T) ≤
        Real.sqrt C₉ * (T * Real.sqrt β + T * Real.sqrt β) :=
      mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (Real.sqrt_nonneg C₉)
    calc Real.sqrt α * Real.sqrt β * Real.sqrt γ ≤ _ := h1
      _ ≤ Real.sqrt C₉ * (T * Real.sqrt β + T * Real.sqrt β) := h2
      _ = 2 * Real.sqrt C₉ * Real.sqrt β * T := by ring
  have hcoef : C₂₅ * κ ^ (-1 : ℝ) ≤ C₂₅ * κ ^ (-5 : ℝ) :=
    mul_le_mul_of_nonneg_left hκinv_le hC₂₅
  calc C₂₅ * κ ^ (-1 : ℝ) * Real.sqrt α * Real.sqrt β * Real.sqrt γ
      = C₂₅ * κ ^ (-1 : ℝ) * (Real.sqrt α * Real.sqrt β * Real.sqrt γ) := by ring
    _ ≤ C₂₅ * κ ^ (-1 : ℝ) * (2 * Real.sqrt C₉ * Real.sqrt β * T) :=
        mul_le_mul_of_nonneg_left hprod
          (mul_nonneg hC₂₅ (Real.rpow_nonneg hκ.le _))
    _ = 2 * C₂₅ * Real.sqrt C₉ * κ ^ (-1 : ℝ) * Real.sqrt β * T := by ring
    _ ≤ 2 * C₂₅ * Real.sqrt C₉ * κ ^ (-5 : ℝ) * Real.sqrt β * T := by
        calc 2 * C₂₅ * Real.sqrt C₉ * κ ^ (-1 : ℝ) * Real.sqrt β * T
            = (2 * Real.sqrt C₉ * Real.sqrt β * T) * (C₂₅ * κ ^ (-1 : ℝ)) := by ring
          _ ≤ (2 * Real.sqrt C₉ * Real.sqrt β * T) * (C₂₅ * κ ^ (-5 : ℝ)) :=
              mul_le_mul_of_nonneg_left hcoef
                (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg C₉))
                  (Real.sqrt_nonneg β)) hT_nonneg)
          _ = 2 * C₂₅ * Real.sqrt C₉ * κ ^ (-5 : ℝ) * Real.sqrt β * T := by ring

private lemma thetaDecay_algebra_hT3_3 :
    ∀ {κ C₉ C₂₅ : ℝ}  {β γ δ : ℝ},
      (0 : ℝ) < κ →
        (0 : ℝ) ≤ C₂₅ →
          ∀ (T : ℝ),
            (0 : ℝ) ≤ T →
              δ ≤ κ ^ (2 : ℝ) * √T →
                √T * √√T * √√β ≤ T →
                  κ ≤ κ ^ (2 / 3 : ℝ) →
                    √γ ≤ √C₉ * (√√T * √√β + √T) →
                      C₂₅ * κ ^ (-1 : ℝ) * δ * √γ ≤ (2 : ℝ) * C₂₅ * √C₉ * κ ^ (2 / 3 : ℝ) * T
    := by
  intro κ C₉ C₂₅  β γ δ hκ hC₂₅ T hT_nonneg hδT hcore hκpow23 hγsqrt
  have hprod : δ * Real.sqrt γ ≤ 2 * Real.sqrt C₉ * κ ^ (2 : ℝ) * T := by
    have h1 : δ * Real.sqrt γ ≤ Real.sqrt C₉ * κ ^ (2 : ℝ) *
        (Real.sqrt T * (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β))
          + Real.sqrt T * Real.sqrt T) := by
      calc δ * Real.sqrt γ
          ≤ (κ ^ (2 : ℝ) * Real.sqrt T) *
              (Real.sqrt C₉ *
                (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) + Real.sqrt T)) :=
            mul_le_mul hδT hγsqrt (Real.sqrt_nonneg γ)
              (mul_nonneg (Real.rpow_nonneg hκ.le _) (Real.sqrt_nonneg T))
        _ = Real.sqrt C₉ * κ ^ (2 : ℝ) *
              (Real.sqrt T * (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β))
                + Real.sqrt T * Real.sqrt T) := by ring
    rw [Real.mul_self_sqrt hT_nonneg] at h1
    have hcore' : Real.sqrt T * (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β)) ≤ T := by
      rw [← mul_assoc]; exact hcore
    have h2 : Real.sqrt C₉ * κ ^ (2 : ℝ) *
          (Real.sqrt T * (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β)) + T) ≤
        Real.sqrt C₉ * κ ^ (2 : ℝ) * (T + T) :=
      mul_le_mul_of_nonneg_left (add_le_add hcore' le_rfl)
        (mul_nonneg (Real.sqrt_nonneg C₉) (Real.rpow_nonneg hκ.le _))
    calc δ * Real.sqrt γ ≤ _ := h1
      _ ≤ Real.sqrt C₉ * κ ^ (2 : ℝ) * (T + T) := h2
      _ = 2 * Real.sqrt C₉ * κ ^ (2 : ℝ) * T := by ring
  have hpow : κ ^ (-1 : ℝ) * κ ^ (2 : ℝ) = κ := by
    rw [rpow_mul_of_add hκ (by norm_num : (-1 : ℝ) + 2 = 1), Real.rpow_one]
  calc C₂₅ * κ ^ (-1 : ℝ) * δ * Real.sqrt γ
      = C₂₅ * κ ^ (-1 : ℝ) * (δ * Real.sqrt γ) := by ring
    _ ≤ C₂₅ * κ ^ (-1 : ℝ) * (2 * Real.sqrt C₉ * κ ^ (2 : ℝ) * T) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg hC₂₅ (Real.rpow_nonneg hκ.le _))
    _ = 2 * C₂₅ * Real.sqrt C₉ * (κ ^ (-1 : ℝ) * κ ^ (2 : ℝ)) * T := by ring
    _ = 2 * C₂₅ * Real.sqrt C₉ * κ * T := by rw [hpow]
    _ ≤ 2 * C₂₅ * Real.sqrt C₉ * κ ^ (2 / 3 : ℝ) * T := by
        have hcoefnn : 0 ≤ 2 * C₂₅ * Real.sqrt C₉ * T :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₂₅) (Real.sqrt_nonneg C₉))
            hT_nonneg
        calc 2 * C₂₅ * Real.sqrt C₉ * κ * T
            = (2 * C₂₅ * Real.sqrt C₉ * T) * κ := by ring
          _ ≤ (2 * C₂₅ * Real.sqrt C₉ * T) * κ ^ (2 / 3 : ℝ) :=
              mul_le_mul_of_nonneg_left hκpow23 hcoefnn
          _ = 2 * C₂₅ * Real.sqrt C₉ * κ ^ (2 / 3 : ℝ) * T := by ring

private lemma thetaDecay_algebra_hP_4 :
    ∀ {κ C₁₄ C₁₅ α β δ lam δr : ℝ},
      (0 : ℝ) < κ →
        (0 : ℝ) ≤ δr →
          δr ≤
              C₁₄ * κ ^ (-1 / 2 : ℝ) * √α * √β + C₁₄ * κ ^ (1 / 3 : ℝ) * δ +
                C₁₅ * κ ^ (1 / 2 : ℝ) * √lam →
            ∀ (T : ℝ),
              κ ^ (-4 : ℝ) * (C₁₄ * κ ^ (-1 / 2 : ℝ) * √α * √β) ^ (2 : ℕ) ≤
                  C₁₄ ^ (2 : ℕ) * κ ^ (-5 : ℝ) * β * T →
                κ ^ (-4 : ℝ) * (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ (2 : ℕ) ≤
                    C₁₄ ^ (2 : ℕ) * κ ^ (2 / 3 : ℝ) * T →
                  κ ^ (-4 : ℝ) * (C₁₅ * κ ^ (1 / 2 : ℝ) * √lam) ^ (2 : ℕ) ≤
                      C₁₅ ^ (2 : ℕ) * κ ^ (-3 : ℝ) * lam →
                    κ ^ (-4 : ℝ) * δr ^ (2 : ℕ) ≤
                      (3 : ℝ) * C₁₄ ^ (2 : ℕ) * κ ^ (-5 : ℝ) * β * T +
                          (3 : ℝ) * C₁₄ ^ (2 : ℕ) * κ ^ (2 / 3 : ℝ) * T +
                        (3 : ℝ) * C₁₅ ^ (2 : ℕ) * κ ^ (-3 : ℝ) * lam
    := by
  intro κ C₁₄ C₁₅ α β δ lam δr hκ hδr hB T hX2 hY2 hZ2
  have hδr2 : δr ^ 2 ≤ 3 * ((C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2
      + (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2
      + (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2) := by
    have h1 : δr ^ 2 ≤ (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β
        + C₁₄ * κ ^ (1 / 3 : ℝ) * δ + C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2 :=
      pow_le_pow_left₀ hδr hB 2
    have h2 := sq_sum_three_le (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β)
      (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam)
    linarith only [h1, h2]
  calc κ ^ (-4 : ℝ) * δr ^ 2
      ≤ κ ^ (-4 : ℝ) * (3 * ((C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2
          + (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2
          + (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2)) :=
        mul_le_mul_of_nonneg_left hδr2 (Real.rpow_nonneg hκ.le _)
    _ = 3 * (κ ^ (-4 : ℝ) * (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2
          + κ ^ (-4 : ℝ) * (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2
          + κ ^ (-4 : ℝ) * (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2) := by ring
    _ ≤ 3 * (C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T + C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T
          + C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
        exact add_le_add (add_le_add hX2 hY2) hZ2
    _ = 3 * C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T + 3 * C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T
          + 3 * C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam := by ring

private lemma thetaDecay_algebra_hg2_5 :
    ∀ {κ C₉ C₁₄ C₂₅ α β δ : ℝ},
      (0 : ℝ) ≤ β →
        let T : ℝ := α + β + κ ^ (-4 : ℝ) * δ ^ (2 : ℕ);
        (0 : ℝ) ≤ T →
          (0 : ℝ) ≤ κ ^ (-5 : ℝ) →
            (2 : ℝ) * C₂₅ * √C₉ ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ →
              (3 : ℝ) * C₁₄ ^ (2 : ℕ) ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ →
                (2 : ℝ) * C₂₅ * √C₉ * κ ^ (-5 : ℝ) * √β * T +
                    (3 : ℝ) * C₁₄ ^ (2 : ℕ) * κ ^ (-5 : ℝ) * β * T ≤
                  thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ) * (√β + β) * T
    := by
  intro κ C₉ C₁₄ C₂₅ α β δ hβ T hT_nonneg hκn5nn hcoefB1 hcoefB2
  have hcoefB : 2 * C₂₅ * Real.sqrt C₉ * Real.sqrt β + 3 * C₁₄ ^ 2 * β ≤
      thetaDecayC₂₇ C₉ C₁₄ C₂₅ * (Real.sqrt β + β) := by
    have h1 : 2 * C₂₅ * Real.sqrt C₉ * Real.sqrt β ≤
        thetaDecayC₂₇ C₉ C₁₄ C₂₅ * Real.sqrt β :=
      mul_le_mul_of_nonneg_right hcoefB1 (Real.sqrt_nonneg β)
    have h2 : 3 * C₁₄ ^ 2 * β ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ * β :=
      mul_le_mul_of_nonneg_right hcoefB2 hβ
    calc 2 * C₂₅ * Real.sqrt C₉ * Real.sqrt β + 3 * C₁₄ ^ 2 * β
        ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ * Real.sqrt β + thetaDecayC₂₇ C₉ C₁₄ C₂₅ * β :=
          add_le_add h1 h2
      _ = thetaDecayC₂₇ C₉ C₁₄ C₂₅ * (Real.sqrt β + β) := by ring
  rw [show 2 * C₂₅ * Real.sqrt C₉ * κ ^ (-5 : ℝ) * Real.sqrt β * T
        + 3 * C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T
      = (2 * C₂₅ * Real.sqrt C₉ * Real.sqrt β + 3 * C₁₄ ^ 2 * β) * κ ^ (-5 : ℝ) * T
      from by ring]
  calc (2 * C₂₅ * Real.sqrt C₉ * Real.sqrt β + 3 * C₁₄ ^ 2 * β) * κ ^ (-5 : ℝ) * T
      = (2 * C₂₅ * Real.sqrt C₉ * Real.sqrt β + 3 * C₁₄ ^ 2 * β)
          * (κ ^ (-5 : ℝ) * T) := by ring
    _ ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ * (Real.sqrt β + β) * (κ ^ (-5 : ℝ) * T) :=
        mul_le_mul_of_nonneg_right hcoefB (mul_nonneg hκn5nn hT_nonneg)
    _ = thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ) * (Real.sqrt β + β) * T := by ring

/-- **The combination step of `lem:theta-decay`.**  The three analytic inputs of
the lemma — the Caccioppoli inequality `eq:caccioppoli` (constants `C₂₅`,
`C₂₆`), the pressure decay estimate `eq:pressure-decay` (constants `C₁₄`,
`C₁₅`), and the Gagliardo–Nirenberg inequality `eq:gagliardo` (constant
`C₉`) — together imply the first displayed decay estimate `eq:theta-decay-1`
for `θ = α + β + κ⁻⁴δ²` at the ratio `κ ∈ (0,1/2]`.

The hypotheses `hA`, `hB`, `hC` are exactly the paper's (A), (B), (C) at the
radii `r = κρ` (left-hand quantities `αr, βr, δr`) and `ρ` (right-hand
quantities `α, β, γ, δ, λ`); the conclusion carries the constants
`thetaDecayC₂₇` and `thetaDecayC₂₈`. -/
theorem thetaDecay_algebra
    {κ C₉ C₁₄ C₁₅ C₂₅ C₂₆ α β γ δ lam αr βr δr : ℝ}
    (hκ : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hC₉ : 0 ≤ C₉)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hlam : 0 ≤ lam)
    (hδr : 0 ≤ δr)
    (hA : αr + βr ≤ C₂₅ * κ * α
        + C₂₅ * κ⁻¹ * Real.sqrt α * Real.sqrt β * Real.sqrt γ
        + C₂₅ * κ⁻¹ * δ * Real.sqrt γ
        + C₂₆ * κ ^ (-1 / 2 : ℝ) * Real.sqrt γ * Real.sqrt lam)
    (hB : δr ≤ C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β
        + C₁₄ * κ ^ (1 / 3 : ℝ) * δ
        + C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam)
    (hC : γ ≤ C₉ * Real.sqrt α * Real.sqrt β + C₉ * α) :
    thetaValue κ αr βr δr ≤
      thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (2 / 3 : ℝ) * thetaValue κ α β δ
        + thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ)
            * (Real.sqrt β + β) * thetaValue κ α β δ
        + thetaDecayC₂₈ C₉ C₁₅ C₂₆ * κ ^ (-1 / 2 : ℝ)
            * Real.sqrt (thetaValue κ α β δ) * Real.sqrt lam
        + thetaDecayC₂₈ C₉ C₁₅ C₂₆ * κ ^ (-3 : ℝ) * lam := by
  simp only [thetaValue]
  have hκ1 : κ ≤ 1 := by linarith only [hκhalf]
  have hκδ2 : 0 ≤ κ ^ (-4 : ℝ) * δ ^ 2 := by positivity
  set T : ℝ := α + β + κ ^ (-4 : ℝ) * δ ^ 2 with hT
  have hT_nonneg : 0 ≤ T := by rw [hT]; linarith only [hα, hβ, hκδ2]
  have hαT : α ≤ T := by rw [hT]; linarith only [hβ, hκδ2]
  have hβT : β ≤ T := by rw [hT]; linarith only [hα, hκδ2]
  have hκδ2T : κ ^ (-4 : ℝ) * δ ^ 2 ≤ T := by rw [hT]; linarith only [hα, hβ]
  have hδT : δ ≤ κ ^ (2 : ℝ) * Real.sqrt T := delta_le_kappa_sq_sqrt hκ hκδ2T
  have hcore : Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) ≤ T :=
    sqrt_mul_sqrt_sqrt_le hβ hβT
  have hsqrtβsqrt : Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) ≤ Real.sqrt T :=
    sqrt_sqrt_mul_sqrt_sqrt_le hβT
  have hκpow23 : κ ≤ κ ^ (2 / 3 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hκ hκ1 (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hκinv_le : κ ^ (-1 : ℝ) ≤ κ ^ (-5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hκ hκ1 (by norm_num : (-5 : ℝ) ≤ -1)
  rw [show κ⁻¹ = κ ^ (-1 : ℝ) from (Real.rpow_neg_one κ).symm] at hA
  have hκ23nn : 0 ≤ κ ^ (2 / 3 : ℝ) := Real.rpow_nonneg hκ.le _
  have hκn5nn : 0 ≤ κ ^ (-5 : ℝ) := Real.rpow_nonneg hκ.le _
  have hκnhnn : 0 ≤ κ ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hκ.le _
  have hκn3nn : 0 ≤ κ ^ (-3 : ℝ) := Real.rpow_nonneg hκ.le _
  have hθ₂₇nn : 0 ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ := by
    rw [thetaDecayC₂₇]; positivity
  have hθ₂₈nn : 0 ≤ thetaDecayC₂₈ C₉ C₁₅ C₂₆ := by
    rw [thetaDecayC₂₈]; positivity
  -- The square root of the Gagliardo–Nirenberg output.
  have hγsqrt := @thetaDecay_algebra_hγsqrt_1 κ C₉ α β γ δ hC₉ hC hT_nonneg hαT
  -- The four Caccioppoli terms.
  have hT1 : C₂₅ * κ * α ≤ C₂₅ * κ ^ (2 / 3 : ℝ) * T := by
    have h1 : C₂₅ * κ * α ≤ C₂₅ * κ * T :=
      mul_le_mul_of_nonneg_left hαT (mul_nonneg hC₂₅ hκ.le)
    have h2 : C₂₅ * κ * T ≤ C₂₅ * κ ^ (2 / 3 : ℝ) * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκpow23 hC₂₅) hT_nonneg
    linarith only [h1, h2]
  have hT2 := @thetaDecay_algebra_hT2_2 κ C₉ C₂₅ α β γ δ hκ hC₂₅ hT_nonneg hαT hcore hκinv_le hγsqrt
  have hT3 := @thetaDecay_algebra_hT3_3 κ C₉ C₂₅  β γ δ hκ hC₂₅ T hT_nonneg hδT hcore hκpow23
    hγsqrt
  have hT4 : C₂₆ * κ ^ (-1 / 2 : ℝ) * Real.sqrt γ * Real.sqrt lam ≤
      2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam := by
    have hγle : Real.sqrt γ ≤ 2 * Real.sqrt C₉ * Real.sqrt T := by
      calc Real.sqrt γ ≤ Real.sqrt C₉ *
            (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) + Real.sqrt T) := hγsqrt
        _ ≤ Real.sqrt C₉ * (Real.sqrt T + Real.sqrt T) :=
            mul_le_mul_of_nonneg_left (add_le_add hsqrtβsqrt le_rfl)
              (Real.sqrt_nonneg C₉)
        _ = 2 * Real.sqrt C₉ * Real.sqrt T := by ring
    calc C₂₆ * κ ^ (-1 / 2 : ℝ) * Real.sqrt γ * Real.sqrt lam
        = C₂₆ * κ ^ (-1 / 2 : ℝ) * (Real.sqrt γ * Real.sqrt lam) := by ring
      _ ≤ C₂₆ * κ ^ (-1 / 2 : ℝ) *
            (2 * Real.sqrt C₉ * Real.sqrt T * Real.sqrt lam) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hγle (Real.sqrt_nonneg lam))
            (mul_nonneg hC₂₆ hκnhnn)
      _ = 2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam := by ring
  have hE : αr + βr ≤ C₂₅ * κ ^ (2 / 3 : ℝ) * T
      + 2 * C₂₅ * Real.sqrt C₉ * κ ^ (-5 : ℝ) * Real.sqrt β * T
      + 2 * C₂₅ * Real.sqrt C₉ * κ ^ (2 / 3 : ℝ) * T
      + 2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam := by
    linarith only [hA, hT1, hT2, hT3, hT4]
  -- The pressure square, via `(s₁+s₂+s₃)² ≤ 3(s₁²+s₂²+s₃²)`.
  have hXsq : (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2
      = C₁₄ ^ 2 * κ ^ (-1 : ℝ) * α * β := by
    rw [mul_pow, mul_pow, mul_pow, CKN.Foundation.Euclidean.rpow_neg_half_sq hκ, Real.sq_sqrt hα,
      Real.sq_sqrt hβ]
  have hYsq : (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2 = C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * δ ^ 2 := by
    rw [mul_pow, mul_pow, CKN.Foundation.Euclidean.rpow_third_sq hκ]
  have hZsq : (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2 = C₁₅ ^ 2 * κ * lam := by
    rw [mul_pow, mul_pow, CKN.Foundation.Euclidean.rpow_half_sq hκ, Real.sq_sqrt hlam]
  have hX2 : κ ^ (-4 : ℝ) * (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2 ≤
      C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T := by
    rw [hXsq]
    calc κ ^ (-4 : ℝ) * (C₁₄ ^ 2 * κ ^ (-1 : ℝ) * α * β)
        = C₁₄ ^ 2 * (κ ^ (-4 : ℝ) * κ ^ (-1 : ℝ)) * (α * β) := by ring
      _ = C₁₄ ^ 2 * κ ^ (-5 : ℝ) * (α * β) := by rw [rpow_neg_four_mul_neg_one hκ]
      _ ≤ C₁₄ ^ 2 * κ ^ (-5 : ℝ) * (T * β) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hαT hβ)
            (mul_nonneg (sq_nonneg C₁₄) (Real.rpow_nonneg hκ.le _))
      _ = C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T := by ring
  have hY2 : κ ^ (-4 : ℝ) * (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2 ≤
      C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T := by
    rw [hYsq]
    calc κ ^ (-4 : ℝ) * (C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * δ ^ 2)
        = C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * (κ ^ (-4 : ℝ) * δ ^ 2) := by ring
      _ ≤ C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T :=
          mul_le_mul_of_nonneg_left hκδ2T
            (mul_nonneg (sq_nonneg C₁₄) (Real.rpow_nonneg hκ.le _))
  have hZ2 : κ ^ (-4 : ℝ) * (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2 ≤
      C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam := by
    rw [hZsq]
    have hcongr : κ ^ (-4 : ℝ) * (C₁₅ ^ 2 * κ * lam) = C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam := by
      rw [show κ ^ (-4 : ℝ) * (C₁₅ ^ 2 * κ * lam) = C₁₅ ^ 2 * (κ ^ (-4 : ℝ) * κ) * lam
            from by ring, rpow_neg_four_mul_one hκ]
    rw [hcongr]
  have hP := @thetaDecay_algebra_hP_4 κ C₁₄ C₁₅ α β δ lam δr hκ hδr hB T hX2 hY2 hZ2
  have hS : αr + βr + κ ^ (-4 : ℝ) * δr ^ 2 ≤
      (C₂₅ * κ ^ (2 / 3 : ℝ) * T
        + 2 * C₂₅ * Real.sqrt C₉ * κ ^ (-5 : ℝ) * Real.sqrt β * T
        + 2 * C₂₅ * Real.sqrt C₉ * κ ^ (2 / 3 : ℝ) * T
        + 2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam)
      + (3 * C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T + 3 * C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T
        + 3 * C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam) := by
    linarith only [hE, hP]
  -- Group the coefficients and compare with the paper's `C₂₇`, `C₂₈`.
  have hcoefA : C₂₅ + 2 * C₂₅ * Real.sqrt C₉ + 3 * C₁₄ ^ 2 ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ := by
    rw [thetaDecayC₂₇]
    nlinarith only [hC₂₅, Real.sqrt_nonneg C₉]
  have hcoefB1 : 2 * C₂₅ * Real.sqrt C₉ ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ := by
    rw [thetaDecayC₂₇]
    nlinarith only [sq_nonneg C₁₄, hC₂₅, Real.sqrt_nonneg C₉]
  have hcoefB2 : 3 * C₁₄ ^ 2 ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ := by
    rw [thetaDecayC₂₇]
    nlinarith only [hC₂₅, Real.sqrt_nonneg C₉]
  have hcoefC1 : 2 * C₂₆ * Real.sqrt C₉ ≤ thetaDecayC₂₈ C₉ C₁₅ C₂₆ := by
    rw [thetaDecayC₂₈]
    nlinarith only [sq_nonneg C₁₅, Real.sqrt_nonneg C₉]
  have hcoefC2 : 3 * C₁₅ ^ 2 ≤ thetaDecayC₂₈ C₉ C₁₅ C₂₆ := by
    rw [thetaDecayC₂₈]
    nlinarith only [hC₂₆, Real.sqrt_nonneg C₉]
  have hg1 : C₂₅ * κ ^ (2 / 3 : ℝ) * T + 2 * C₂₅ * Real.sqrt C₉ * κ ^ (2 / 3 : ℝ) * T
      + 3 * C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T ≤
      thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (2 / 3 : ℝ) * T := by
    rw [show C₂₅ * κ ^ (2 / 3 : ℝ) * T + 2 * C₂₅ * Real.sqrt C₉ * κ ^ (2 / 3 : ℝ) * T
          + 3 * C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T
        = (C₂₅ + 2 * C₂₅ * Real.sqrt C₉ + 3 * C₁₄ ^ 2) * κ ^ (2 / 3 : ℝ) * T from by ring]
    calc (C₂₅ + 2 * C₂₅ * Real.sqrt C₉ + 3 * C₁₄ ^ 2) * κ ^ (2 / 3 : ℝ) * T
        = (C₂₅ + 2 * C₂₅ * Real.sqrt C₉ + 3 * C₁₄ ^ 2) * (κ ^ (2 / 3 : ℝ) * T) := by ring
      _ ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ * (κ ^ (2 / 3 : ℝ) * T) :=
          mul_le_mul_of_nonneg_right hcoefA (mul_nonneg hκ23nn hT_nonneg)
      _ = thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (2 / 3 : ℝ) * T := by ring
  have hg2 := @thetaDecay_algebra_hg2_5 κ C₉ C₁₄ C₂₅ α β δ hβ hT_nonneg hκn5nn hcoefB1 hcoefB2
  have hg3 : 2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam ≤
      thetaDecayC₂₈ C₉ C₁₅ C₂₆ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam := by
    calc 2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam
        = (2 * C₂₆ * Real.sqrt C₉) * (κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam) := by ring
      _ ≤ thetaDecayC₂₈ C₉ C₁₅ C₂₆
            * (κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam) :=
          mul_le_mul_of_nonneg_right hcoefC1
            (mul_nonneg (mul_nonneg hκnhnn (Real.sqrt_nonneg T)) (Real.sqrt_nonneg lam))
      _ = thetaDecayC₂₈ C₉ C₁₅ C₂₆ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam := by ring
  have hg4 : 3 * C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam ≤
      thetaDecayC₂₈ C₉ C₁₅ C₂₆ * κ ^ (-3 : ℝ) * lam :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefC2 hκn3nn) hlam
  refine hS.trans ?_
  have hgroup : (C₂₅ * κ ^ (2 / 3 : ℝ) * T
        + 2 * C₂₅ * Real.sqrt C₉ * κ ^ (-5 : ℝ) * Real.sqrt β * T
        + 2 * C₂₅ * Real.sqrt C₉ * κ ^ (2 / 3 : ℝ) * T
        + 2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam)
      + (3 * C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T + 3 * C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T
        + 3 * C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam)
      = (C₂₅ * κ ^ (2 / 3 : ℝ) * T + 2 * C₂₅ * Real.sqrt C₉ * κ ^ (2 / 3 : ℝ) * T
          + 3 * C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T)
        + (2 * C₂₅ * Real.sqrt C₉ * κ ^ (-5 : ℝ) * Real.sqrt β * T
          + 3 * C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T)
        + 2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam
        + 3 * C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam := by ring
  rw [hgroup]
  exact add_le_add (add_le_add (add_le_add hg1 hg2) hg3) hg4

/-- **The small-`θ` form of the combination step of `lem:theta-decay`.**  This is
`eq:theta-decay-2`: under the additional hypothesis `θ(ρ) ≤ 1` the second term of
`thetaDecay_algebra` weakens, because `β^{1/2} + β ≤ 2θ(ρ)^{1/2}`.  The analytic
inputs `hA`, `hB`, `hC` are the same as in `thetaDecay_algebra`. -/
theorem thetaDecay_algebra_small
    {κ C₉ C₁₄ C₁₅ C₂₅ C₂₆ α β γ δ lam αr βr δr : ℝ}
    (hκ : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hC₉ : 0 ≤ C₉)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hlam : 0 ≤ lam)
    (hδr : 0 ≤ δr)
    (hθ : thetaValue κ α β δ ≤ 1)
    (hA : αr + βr ≤ C₂₅ * κ * α
        + C₂₅ * κ⁻¹ * Real.sqrt α * Real.sqrt β * Real.sqrt γ
        + C₂₅ * κ⁻¹ * δ * Real.sqrt γ
        + C₂₆ * κ ^ (-1 / 2 : ℝ) * Real.sqrt γ * Real.sqrt lam)
    (hB : δr ≤ C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β
        + C₁₄ * κ ^ (1 / 3 : ℝ) * δ
        + C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam)
    (hC : γ ≤ C₉ * Real.sqrt α * Real.sqrt β + C₉ * α) :
    thetaValue κ αr βr δr ≤
      thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (2 / 3 : ℝ) * thetaValue κ α β δ
        + 2 * thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ)
            * Real.sqrt (thetaValue κ α β δ) * thetaValue κ α β δ
        + thetaDecayC₂₈ C₉ C₁₅ C₂₆ * κ ^ (-1 / 2 : ℝ)
            * Real.sqrt (thetaValue κ α β δ) * Real.sqrt lam
        + thetaDecayC₂₈ C₉ C₁₅ C₂₆ * κ ^ (-3 : ℝ) * lam := by
  set T : ℝ := thetaValue κ α β δ with hTdef
  have hmain := thetaDecay_algebra hκ hκhalf hC₉ hC₂₅ hC₂₆ hα hβ hlam
    hδr hA hB hC
  rw [← hTdef] at hmain
  have hκδ2 : 0 ≤ κ ^ (-4 : ℝ) * δ ^ 2 := by positivity
  have hTnn : 0 ≤ T := by rw [hTdef, thetaValue]; linarith only [hα, hβ, hκδ2]
  have hβT : β ≤ T := by rw [hTdef, thetaValue]; linarith only [hα, hκδ2]
  have hTle1 : T ≤ 1 := by rw [hTdef]; exact hθ
  have hT_le_sqrtT : T ≤ Real.sqrt T := by
    refine le_of_sq_le_sq ?_ (Real.sqrt_nonneg T)
    rw [Real.sq_sqrt hTnn]
    nlinarith only [hTnn, hTle1]
  have hsum : Real.sqrt β + β ≤ 2 * Real.sqrt T := by
    have h1 : Real.sqrt β ≤ Real.sqrt T := Real.sqrt_le_sqrt hβT
    have h2 : β ≤ Real.sqrt T := le_trans hβT hT_le_sqrtT
    linarith only [h1, h2]
  have hθ₂₇nn : 0 ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ := by rw [thetaDecayC₂₇]; positivity
  have hterm : thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ) * (Real.sqrt β + β) * T ≤
      2 * thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ) * Real.sqrt T * T := by
    have hcoefnn : 0 ≤ thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ) * T :=
      mul_nonneg (mul_nonneg hθ₂₇nn (Real.rpow_nonneg hκ.le _)) hTnn
    calc thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ) * (Real.sqrt β + β) * T
        = (thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ) * T) * (Real.sqrt β + β) := by ring
      _ ≤ (thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ) * T) * (2 * Real.sqrt T) :=
          mul_le_mul_of_nonneg_left hsum hcoefnn
      _ = 2 * thetaDecayC₂₇ C₉ C₁₄ C₂₅ * κ ^ (-5 : ℝ) * Real.sqrt T * T := by ring
  refine hmain.trans ?_
  exact add_le_add (add_le_add (add_le_add le_rfl hterm) le_rfl) le_rfl

end CKN
