/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketRay
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketPerturbation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Packet Bridge
-/

@[expose] public section

noncomputable section

open Set

namespace EulerPacketBridge

open EulerPacketPerturbation EulerPacketRay

/-- The first component of the ideal normalized velocity vector field. -/
noncomputable def idealVelocityFirst (β t U V : ℝ) : ℝ :=
  -2 * V + 2 * (β * t ^ 2) * (((β * t ^ 2) + β) * V + (-2 * β * t) * U) /
    (1 + (β * t ^ 2) ^ 2)

/-- The exact forced scalar flux equation obtained from the two velocity
components.  The forcing is the actual vector-field discrepancy. -/
theorem velocity_scalar_flux
    {β t u₁ v₁ : ℝ} {U V : ℝ → ℝ}
    (hU : HasDerivAt U u₁ t) (hV : HasDerivAt V v₁ t) :
    HasDerivAt V (-U t + (v₁ + U t)) t ∧
    HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * (-U s))
      (2 * (1 - β * (β * t ^ 2)) * V t + (1 + (β * t ^ 2) ^ 2) *
        (-u₁ + idealVelocityFirst β t (U t) (V t))) t := by
  refine ⟨hV.congr_deriv (by ring), ?_⟩
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2) (4 * β ^ 2 * t ^ 3) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul β).pow 2).const_add 1 using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  apply (hD.mul hU.neg).congr_deriv
  have hden : 1 + (β * t ^ 2) ^ 2 ≠ 0 := by positivity
  dsimp [idealVelocityFirst]
  field_simp
  ring

theorem continuousOn_idealVelocityFirst
    {β : ℝ} {I : Set ℝ} {U V : ℝ → ℝ}
    (hU : ContinuousOn U I) (hV : ContinuousOn V I) :
    ContinuousOn (fun t => idealVelocityFirst β t (U t) (V t)) I := by
  unfold idealVelocityFirst
  have hden : ∀ t ∈ I, 1 + (β * t ^ 2) ^ 2 ≠ 0 := by intro t _; positivity
  have hId : ContinuousOn (fun t : ℝ => t) I := continuousOn_id
  fun_prop

/-- Any continuously differentiable velocity solution inherits the precise
relative scalar stability estimate once its vector field has been bounded.
The preceding matrix and ray theorems provide that bound. -/
theorem velocity_relative_error_order29
    {σ Θ T e lam : ℝ} {F F₁ G G₁ Z Z₁ U U₁ V V₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 ≤ T) (hT : T ≤ Θ) (he : 0 ≤ e) (hlam : 0 ≤ lam)
    (hsmall : 40 * e * Θ ^ 21 ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hG : ∀ t, 0 ≤ t → HasDerivAt G (G₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxG : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * G₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * G t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U (U₁ t) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hU₁c : ContinuousOn U₁ (Icc 0 T)) (hV₁c : ContinuousOn V₁ (Icc 0 T))
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hU0 : U 0 = -lam) (hV0 : V 0 = 1) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ t ∈ Icc 0 T,
      |U₁ t - idealVelocityFirst (σ ^ 2) t (U t) (V t)| + |V₁ t + U t| ≤
        (e * Θ ^ 12) * (|U t| + |V t|)) :
    ∀ t ∈ Icc 0 T,
      |V t - Z t| + |U t + Z₁ t| ≤ 800 * e * Θ ^ 29 * (1 + lam) * F t := by
  let f : ℝ → ℝ := fun t => V₁ t + U t
  let g : ℝ → ℝ := fun t => -U₁ t + idealVelocityFirst (σ ^ 2) t (U t) (V t)
  have hUc : ContinuousOn U (Icc 0 T) := fun t ht => (hU t ht).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun t ht => (hV t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc 0 T) := hV₁c.add hUc
  have hgc : ContinuousOn g (Icc 0 T) := hU₁c.neg.add (continuousOn_idealVelocityFirst hUc hVc)
  have hY : ∀ t ∈ Icc 0 T, HasDerivAt V ((-U t) + f t) t := by
    intro t ht
    exact (velocity_scalar_flux (β := σ ^ 2) (hU t ht) (hV t ht)).1
  have hfluxY : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * (-U s))
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * V t + (1 + (σ ^ 2 * t ^ 2) ^ 2) * g t) t := by
    intro t ht
    exact (velocity_scalar_flux (β := σ ^ 2) (hU t ht) (hV t ht)).2
  have hforcing : ∀ t ∈ Icc 0 T, |f t| + |g t| ≤ (e * Θ ^ 12) * (|V t| + |-U t|) := by
    intro t ht
    have hh := herror t ht
    have hg : |g t| = |U₁ t - idealVelocityFirst (σ ^ 2) t (U t) (V t)| := by
      dsimp [g]
      rw [neg_add_eq_sub, abs_sub_comm]
    rw [hg, abs_neg]
    dsimp [f]
    linarith only [hh]
  have hminusU0 : -U 0 = lam := by rw [hU0, neg_neg]
  have hresult := equation30_relative_error_order29 hσ hσsmall hΘ hT0 hT he hlam hsmall
    hF hG hfluxF hfluxG hF0 hF₁0 hG₁0 hY hfluxY hZ hfluxZ
    hV0 hminusU0 hZ0 hZ₁0 hfc hgc hforcing
  intro t ht
  have hh := hresult t ht
  have hid : -U t - Z₁ t = -(U t + Z₁ t) := by ring
  simpa only [hid, abs_neg] using hh

/-- Ray coefficient bounds imply the velocity vector-field discrepancy.
The ray error and the nonvanishing third coordinate are conclusions of
the actual ray ODE, not premises. -/
theorem ray_controlled_velocity_error
    {β Θ T e ε : ℝ} {R A C : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e) (hsmall : 10000 * e * Θ ^ 5 ≤ 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry β i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry β i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ i j, |C t i j - idealUnprojectedEntry i j| ≤ 5 * e)
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e) :
    ∀ t ∈ Icc 0 T, 1 / 2 ≤ N t ∧ ∀ U V : ℝ,
      |velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) U V -
          idealVelocityFirst β t U V| +
        |velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) U V + U| ≤
          200000 * e * Θ ^ 12 * (|U| + |V|) := by
  have hΘ0 : 0 ≤ Θ := by linarith
  have hsmallR : 400 * (4 * e) * Θ ^ 5 ≤ 1 := by
    have hnonneg : 0 ≤ e * Θ ^ 5 := by positivity
    linarith only [hsmall, hnonneg]
  have hinitialR : norm3 (P 0) (Q 0) (N 0 - 1) ≤ 4 * e := by linarith
  have hray := ray_closeness_of_coefficient_error hβ hβupper hΘ hT0 hT
    (by positivity : 0 ≤ 4 * e) hsmallR hRc hP hQ hN hRclose hinitialR
  intro t ht
  obtain ⟨herr, hn⟩ := hray t ht
  refine ⟨hn, ?_⟩
  intro U V
  have herrorP : |P t - β * t ^ 2| ≤ 800 * e * Θ ^ 5 := by
    unfold norm3 at herr
    linarith only [herr, abs_nonneg (Q t + 2 * β * t), abs_nonneg (N t - 1)]
  have herrorQ : |Q t - (-2 * β * t)| ≤ 800 * e * Θ ^ 5 := by
    unfold norm3 at herr
    have hid : Q t - (-2 * β * t) = Q t + 2 * β * t := by ring
    rw [hid]
    linarith only [herr, abs_nonneg (P t - β * t ^ 2), abs_nonneg (N t - 1)]
  have herrorN : |N t - 1| ≤ 800 * e * Θ ^ 5 := by
    unfold norm3 at herr
    linarith only [herr, abs_nonneg (P t - β * t ^ 2), abs_nonneg (Q t + 2 * β * t)]
  have htΘ : t ≤ Θ := ht.2.trans hT
  have ht2 : t ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ ht.1 hΘ0).mpr htΘ
  have hP₀ : |β * t ^ 2| ≤ Θ ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hβ (sq_nonneg t))]
    have hh := mul_le_mul_of_nonneg_right hβupper (sq_nonneg t)
    linarith only [hh, ht2]
  have hQ₀ : |-2 * β * t| ≤ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hβ, abs_of_nonneg ht.1]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have htTheta2 : t ≤ Θ ^ 2 := by nlinarith only [htΘ, hΘ]
    have hh := mul_le_mul_of_nonneg_right hβupper ht.1
    linarith only [hh, htTheta2]
  have hβabs : |β| ≤ 1 := by rwa [abs_of_nonneg hβ]
  exact velocity_rhs_error hΘ he hε hεe hsmall hβabs
    (hAclose t ht) (hCclose t ht) hP₀ hQ₀ herrorP herrorQ herrorN

theorem continuousOn_velocity_rhs
    {ε : ℝ} {I : Set ℝ} {A C : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N U V : ℝ → ℝ}
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) I)
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) I)
    (hP : ContinuousOn P I) (hQ : ContinuousOn Q I) (hN : ContinuousOn N I)
    (hU : ContinuousOn U I) (hV : ContinuousOn V I)
    (hNne : ∀ t ∈ I, N t ≠ 0) :
    ContinuousOn (fun t => velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) I ∧
    ContinuousOn (fun t => velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) I := by
  have hW : ContinuousOn (fun t => velocityThird (P t) (Q t) (N t) (U t) (V t)) I := by
    unfold velocityThird
    exact ((hP.mul hU).add (hQ.mul hV)).neg.div hN hNne
  have hD : ContinuousOn (fun t => rayDenominator ε (P t) (Q t) (N t)) I := by
    unfold rayDenominator
    fun_prop
  have hDne : ∀ t ∈ I, rayDenominator ε (P t) (Q t) (N t) ≠ 0 := by
    intro t ht
    have hn : 0 < N t ^ 2 := sq_pos_of_ne_zero (hNne t ht)
    unfold rayDenominator
    positivity
  have hJ : ContinuousOn (fun t => velocityNumerator (A t) (P t) (Q t) (N t)
      (U t) (V t) (velocityThird (P t) (Q t) (N t) (U t) (V t))) I := by
    unfold velocityNumerator
    fun_prop
  constructor
  · exact ((((hCc 0 0).mul hU).add ((hCc 0 1).mul hV)).add
      ((hCc 0 2).mul hW)).neg.add (((hP.const_mul 2).mul hJ).div hD hDne)
  · exact ((((hCc 1 0).mul hU).add ((hCc 1 1).mul hV)).add
      ((hCc 1 2).mul hW)).neg.add (((hQ.const_mul (2 * ε ^ 2)).mul hJ).div hD hDne)

/-- The complete finite-dimensional stability bridge: actual ray and
velocity equations with controlled matrix coefficients imply the relative
`Θ^29` error.  All denominator and Duhamel bounds are derived above. -/
theorem controlled_velocity_relative_error
    {σ Θ T e ε lam : ℝ} {F F₁ G G₁ Z Z₁ U V P Q N : ℝ → ℝ}
    {R A C : ℝ → Fin 3 → Fin 3 → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 ≤ T) (hT : T ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hlam : 0 ≤ lam) (hsmall : 8000000 * e * Θ ^ 21 ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hG : ∀ t, 0 ≤ t → HasDerivAt G (G₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxG : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * G₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * G t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) t)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U
      (velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V
      (velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry (σ ^ 2) i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ i j, |C t i j - idealUnprojectedEntry i j| ≤ 5 * e)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hrayInitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e)
    (hU0 : U 0 = -lam) (hV0 : V 0 = 1) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam) :
    ∀ t ∈ Icc 0 T,
      |V t - Z t| + |U t + Z₁ t| ≤ 160000000 * e * Θ ^ 29 * (1 + lam) * F t := by
  have hσsq : σ ^ 2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have hgeomSmall : 10000 * e * Θ ^ 5 ≤ 1 := by
    have hh := pow_le_pow_right₀ hΘ (show 5 ≤ 21 by decide)
    have hm := mul_le_mul_of_nonneg_left hh he
    have hp : 0 ≤ e * Θ ^ 21 := by positivity
    linarith only [hsmall, hm, hp]
  have hcontrol := ray_controlled_velocity_error (sq_nonneg σ) hσsq hΘ hT0 hT he hε hεe
    hgeomSmall hRc hP hQ hN hRclose hAclose hCclose hrayInitial
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousAt.continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousAt.continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousAt.continuousWithinAt
  have hUc : ContinuousOn U (Icc 0 T) := fun t ht => (hU t ht).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun t ht => (hV t ht).continuousAt.continuousWithinAt
  have hNne : ∀ t ∈ Icc 0 T, N t ≠ 0 := by
    intro t ht
    have hh := (hcontrol t ht).1
    linarith
  obtain ⟨hU₁c, hV₁c⟩ := continuousOn_velocity_rhs (ε := ε) hAc hCc hPc hQc hNc hUc hVc hNne
  have hsmall' : 40 * (200000 * e) * Θ ^ 21 ≤ 1 := by linarith only [hsmall]
  have herror : ∀ t ∈ Icc 0 T,
      |velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t) -
        idealVelocityFirst (σ ^ 2) t (U t) (V t)| +
      |velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t) + U t| ≤
        ((200000 * e) * Θ ^ 12) * (|U t| + |V t|) := by
    intro t ht
    exact (hcontrol t ht).2 (U t) (V t)
  have hh := velocity_relative_error_order29 hσ hσsmall hΘ hT0 hT
    (by positivity : 0 ≤ 200000 * e) hlam hsmall'
    hF hG hfluxF hfluxG hF0 hF₁0 hG₁0 hU hV hU₁c hV₁c hZ hfluxZ hU0 hV0 hZ0 hZ₁0 herror
  intro t ht
  have h := hh t ht
  linarith only [h]

end EulerPacketBridge
