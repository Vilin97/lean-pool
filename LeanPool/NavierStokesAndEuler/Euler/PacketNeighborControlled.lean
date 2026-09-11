/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBridge
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketExistence
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameStability
import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocitySystem
import LeanPool.NavierStokesAndEuler.Euler.PacketWithinRay
import Mathlib.Algebra.Order.Star.Real
import LeanPool.NavierStokesAndEuler.Euler.ClosedIntervalDerivativeExtension
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketPerturbation

/-!
The normalized physical equations retain the actual neighboring initial
discrepancy.  The scalar comparison solutions below are constructed, and
the third ray coordinate and all denominator bounds follow from the ray
equation.
-/

section

/-!
Relative stability with an actual initial velocity discrepancy.  This keeps
the neighbor-data contribution in the Duhamel estimate rather than requiring
the perturbed velocity to have exactly the center initial data.
-/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerPacketRay EulerPacketBridge EulerPacketPerturbation
  EulerClosedIntervalDerivativeExtension

theorem velocity_difference_bound
    {σ Θ T e : ℝ} {F F₁ G G₁ Z Z₁ U U₁ V V₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 ≤ T) (hT : T ≤ Θ) (he : 0 ≤ e) (hsmall : 40 * e * Θ ^ 21 ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hG : ∀ t, 0 ≤ t → HasDerivAt G (G₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxG : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * G₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * G t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U (U₁ t) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hU₁c : ContinuousOn U₁ (Icc 0 T)) (hV₁c : ContinuousOn V₁ (Icc 0 T))
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (herror : ∀ t ∈ Icc 0 T,
      |U₁ t - idealVelocityFirst (σ ^ 2) t (U t) (V t)| + |V₁ t + U t| ≤
        (e * Θ ^ 12) * (|U t| + |V t|)) :
    ∀ t ∈ Icc 0 T, |V t-Z t|+|U t+Z₁ t| ≤
      20*Θ^8*F t*(|V 0-Z 0|+|U 0+Z₁ 0|)+800*e*Θ^29*F t*(|V 0|+|U 0|) := by
  let f : ℝ → ℝ := fun t => V₁ t+U t
  let g : ℝ → ℝ := fun t => -U₁ t+idealVelocityFirst (σ^2) t (U t) (V t)
  have hUc : ContinuousOn U (Icc 0 T) := fun t ht => (hU t ht).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun t ht => (hV t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc 0 T) := hV₁c.add hUc
  have hgc : ContinuousOn g (Icc 0 T) := hU₁c.neg.add (continuousOn_idealVelocityFirst hUc hVc)
  have hY : ∀ t ∈ Icc 0 T, HasDerivAt V (-U t+f t) t := by
    intro t ht
    exact (velocity_scalar_flux (β := σ^2) (hU t ht) (hV t ht)).1
  have hfluxY : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*(-U s))
      (2*(1-σ^2*(σ^2*t^2))*V t+(1+(σ^2*t^2)^2)*g t) t := by
    intro t ht
    exact (velocity_scalar_flux (β := σ^2) (hU t ht) (hV t ht)).2
  have hforcing : ∀ t ∈ Icc 0 T, |f t|+|g t| ≤ (e*Θ^12)*(|V t|+|-U t|) := by
    intro t ht
    have hg : |g t| = |U₁ t-idealVelocityFirst (σ^2) t (U t) (V t)| := by
      dsimp [g]
      rw [neg_add_eq_sub, abs_sub_comm]
    rw [hg, abs_neg]
    dsimp [f]
    linarith only [herror t ht]
  have hδ : 0 ≤ e*Θ^12 := by positivity
  have hs : 20*Θ^8*(e*Θ^12)*(T-0) ≤ 1/2 := by
    have hm := mul_le_mul_of_nonneg_left hT (show 0 ≤ 20*e*Θ^20 by positivity)
    linarith only [hsmall, hm]
  have hh := equation30_perturbed_difference_bound hσ hσsmall hΘ (by norm_num : (0:ℝ) ≤ 0)
    hT0 hT hδ hs hF hG hfluxF hfluxG hF0 hF₁0 hG₁0 hY hfluxY hZ hfluxZ hfc hgc hforcing
  have habs (x y : ℝ) : |-x-y| = |x+y| := by rw [show -x-y = -(x+y) by ring, abs_neg]
  intro t ht
  have h := hh t ht
  simp only [hF0, div_one, habs, abs_neg] at h
  convert! h using 1
  ring

theorem velocity_difference_bound_within
    {σ Θ T e : ℝ} {F F₁ G G₁ Z Z₁ U U₁ V V₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 < T) (hT : T ≤ Θ) (he : 0 ≤ e) (hsmall : 40 * e * Θ ^ 21 ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hG : ∀ t, 0 ≤ t → HasDerivAt G (G₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxG : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * G₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * G t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hU : ∀ t ∈ Icc 0 T, HasDerivWithinAt U (U₁ t) (Icc 0 T) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivWithinAt V (V₁ t) (Icc 0 T) t)
    (hU₁c : ContinuousOn U₁ (Icc 0 T)) (hV₁c : ContinuousOn V₁ (Icc 0 T))
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (herror : ∀ t ∈ Icc 0 T,
      |U₁ t - idealVelocityFirst (σ ^ 2) t (U t) (V t)| + |V₁ t + U t| ≤
        (e * Θ ^ 12) * (|U t| + |V t|)) :
    ∀ t ∈ Icc 0 T, |V t-Z t|+|U t+Z₁ t| ≤
      20*Θ^8*F t*(|V 0-Z 0|+|U 0+Z₁ 0|)+800*e*Θ^29*F t*(|V 0|+|U 0|) := by
  obtain ⟨U', hUeq, hU'⟩ := exists_extension hT0 hU
  obtain ⟨V', hVeq, hV'⟩ := exists_extension hT0 hV
  have he' : ∀ t ∈ Icc 0 T,
      |U₁ t-idealVelocityFirst (σ^2) t (U' t) (V' t)|+|V₁ t+U' t| ≤
        (e*Θ^12)*(|U' t|+|V' t|) := by
    intro t ht
    simpa only [hUeq ht, hVeq ht] using herror t ht
  have hh := velocity_difference_bound hσ hσsmall hΘ hT0.le hT he hsmall hF hG hfluxF hfluxG
    hF0 hF₁0 hG₁0 hU' hV' hU₁c hV₁c hZ hfluxZ he'
  have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  intro t ht
  simpa only [hUeq ht, hVeq ht, hUeq h0, hVeq h0] using hh t ht

/-- Converting the retained initial discrepancy to the source's neighbor
normalization costs no additional power of `Θ`. -/
theorem neighbor_initial_error_bound
    {Θ e η lam Ft u₀ v₀ L : ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hlam : 0 ≤ lam) (hFt : 0 ≤ Ft)
    (hi : |v₀ - 1| + |u₀ + lam| ≤ η)
    (hb : L ≤ 20 * Θ ^ 8 * Ft * (|v₀ - 1| + |u₀ + lam|) + 800 * e * Θ ^ 29 * Ft * (|v₀| + |u₀|)) :
    L ≤ (20*η*Θ^8+800*e*Θ^29*(1+lam+η))*Ft := by
  have hv := abs_add_le (v₀-1) 1
  have hu := abs_add_le (u₀+lam) (-lam)
  simp only [sub_add_cancel, abs_one, add_neg_cancel_right, abs_neg, abs_of_nonneg hlam] at hv hu
  have hnorm : |v₀|+|u₀| ≤ 1+lam+η := by linarith only [hv, hu, hi]
  have h1 := mul_le_mul_of_nonneg_left hi (show 0 ≤ 20*Θ^8*Ft by positivity)
  have h2 := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 800*e*Θ^29*Ft by positivity)
  linarith only [hb, h1, h2]

end EulerPacketMovingFrame

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set Real EulerPacketRay EulerPacketBridge EulerPacketGrowth
   EulerPacketFrameStability EulerPacketExistence

theorem ray_controlled_velocity_error_within
    {β Θ T e ε : ℝ} {R A C : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 < T) (hT : T ≤ Θ)
    (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e) (hsmall : 10000 * e * Θ ^ 5 ≤ 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivWithinAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) (Icc 0 T) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivWithinAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) (Icc 0 T) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry β i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry β i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ j,
      |C t 0 j - idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |C t 1 j - idealUnprojectedEntry 1 j| ≤ 5 * e)
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e) :
    ∀ t ∈ Icc 0 T,
      (norm3 (P t-β*t^2) (Q t+2*β*t) (N t-1) ≤ 800*e*Θ^5 ∧ 1/2 ≤ N t) ∧
      ∀ U V : ℝ,
        |velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) U V-idealVelocityFirst β t U V| +
          |velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) U V+U| ≤
            200000*e*Θ^12*(|U|+|V|) := by
  have hΘ0 : 0 ≤ Θ := by linarith only [hΘ]
  have hs : 400*(4*e)*Θ^5 ≤ 1 := by linarith only [hsmall, mul_nonneg he (pow_nonneg hΘ0 5)]
  have hi : norm3 (P 0) (Q 0) (N 0-1) ≤ 4*e := hinitial.trans (by linarith only [he])
  have hnear := ray_closeness_within hβ hβupper hΘ hT0 hT
    (show 0 ≤ 4*e by positivity) hs hRc hP hQ hN hRclose hi
  intro t ht
  obtain ⟨herr, hn⟩ := hnear t ht
  have herr' : norm3 (P t-β*t^2) (Q t+2*β*t) (N t-1) ≤ 800*e*Θ^5 := by
    linarith only [herr]
  refine ⟨⟨herr', hn⟩, ?_⟩
  intro U V
  have herrorP : |P t-β*t^2| ≤ 800*e*Θ^5 := by
    unfold norm3 at herr'
    linarith only [herr', abs_nonneg (Q t+2*β*t), abs_nonneg (N t-1)]
  have herrorQ : |Q t-(-2*β*t)| ≤ 800*e*Θ^5 := by
    have heq : Q t-(-2*β*t) = Q t+2*β*t := by ring
    rw [heq]
    unfold norm3 at herr'
    linarith only [herr', abs_nonneg (P t-β*t^2), abs_nonneg (N t-1)]
  have herrorN : |N t-1| ≤ 800*e*Θ^5 := by
    unfold norm3 at herr'
    linarith only [herr', abs_nonneg (P t-β*t^2), abs_nonneg (Q t+2*β*t)]
  have htΘ : t ≤ Θ := ht.2.trans hT
  have ht2 : t^2 ≤ Θ^2 := (sq_le_sq₀ ht.1 hΘ0).mpr htΘ
  have hP₀ : |β*t^2| ≤ Θ^2 := by
    rw [abs_of_nonneg (mul_nonneg hβ (sq_nonneg t))]
    linarith only [mul_le_mul_of_nonneg_right hβupper (sq_nonneg t), ht2]
  have hQ₀ : |-2*β*t| ≤ 2*Θ^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hβ, abs_of_nonneg ht.1]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith only [mul_le_mul_of_nonneg_right hβupper ht.1, htΘ, hΘ, sq_nonneg (Θ-1)]
  have hb : |β| ≤ 1 := by rwa [abs_of_nonneg hβ]
  exact velocity_rhs_error_firstTwo hΘ he hε hεe hsmall hb (hAclose t ht)
    (hCclose t ht) hP₀ hQ₀ herrorP herrorQ herrorN

theorem controlled_neighbor_relative_error_within
    {σ Θ T e ε lam : ℝ} {F F₁ G G₁ Z Z₁ U V P Q N : ℝ → ℝ}
    {R A C : ℝ → Fin 3 → Fin 3 → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 < T) (hT : T ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hlam : 0 ≤ lam) (hsmall : 8000000 * e * Θ ^ 21 ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hG : ∀ t, 0 ≤ t → HasDerivAt G (G₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxG : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * G₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * G t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivWithinAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) (Icc 0 T) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivWithinAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) (Icc 0 T) t)
    (hU : ∀ t ∈ Icc 0 T, HasDerivWithinAt U
      (velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) (Icc 0 T) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivWithinAt V
      (velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) (Icc 0 T) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry (σ ^ 2) i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ j,
      |C t 0 j - idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |C t 1 j - idealUnprojectedEntry 1 j| ≤ 5 * e)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hrayInitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e)
    (hvelocityInitial : |V 0 - 1| + |U 0 + lam| ≤ e)
    (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam) :
    ∀ t ∈ Icc 0 T,
      |V t-Z t|+|U t+Z₁ t| ≤ 400000000*e*Θ^29*(1+lam)*F t := by
  have hΘ0 : 0 ≤ Θ := by linarith only [hΘ]
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have hgeom : 10000*e*Θ^5 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 21)) he
    linarith only [hsmall, hh, mul_nonneg he (pow_nonneg hΘ0 21)]
  have he1 : e ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hΘ : 1 ≤ Θ^21) he
    linarith only [hsmall, hh, he]
  have hcontrol := ray_controlled_velocity_error_within (sq_nonneg σ) hσ2 hΘ hT0 hT
    he hε hεe hgeom hRc hP hQ hN hRclose hAclose hCclose hrayInitial
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousWithinAt
  have hUc : ContinuousOn U (Icc 0 T) := fun t ht => (hU t ht).continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun t ht => (hV t ht).continuousWithinAt
  have hNne : ∀ t ∈ Icc 0 T, N t ≠ 0 := by
    intro t ht
    linarith only [(hcontrol t ht).1.2]
  obtain ⟨hU₁c, hV₁c⟩ := continuousOn_velocity_rhs (ε := ε) hAc hCc hPc hQc hNc hUc hVc hNne
  have hs : 40*(200000*e)*Θ^21 ≤ 1 := by linarith only [hsmall]
  have herror := velocity_difference_bound_within hσ hσsmall hΘ hT0 hT
    (show 0 ≤ 200000*e by positivity) hs hF hG hfluxF hfluxG hF0 hF₁0 hG₁0
    hU hV hU₁c hV₁c hZ hfluxZ (fun t ht => (hcontrol t ht).2 (U t) (V t))
  have hcoef : 20*e*Θ^8+800*(200000*e)*Θ^29*(1+lam+e) ≤ 400000000*e*Θ^29*(1+lam) := by
    have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 8 ≤ 29))
      (show 0 ≤ 20*e by positivity)
    have h2 := mul_le_mul_of_nonneg_left (show 1+lam+e ≤ 2*(1+lam) by linarith only [he1, hlam])
      (show 0 ≤ 160000000*e*Θ^29 by positivity)
    linarith only [h1, h2, mul_nonneg (mul_nonneg he (pow_nonneg hΘ0 29)) hlam,
      mul_nonneg he (pow_nonneg hΘ0 29)]
  intro t ht
  have hFp : 0 ≤ F t := (equation30_global_positive hσ hσsmall hF hfluxF hF0
    (by rw [hF₁0]) t ht.1).le
  have hh := herror t ht
  rw [hZ0, hZ₁0] at hh
  have hb := neighbor_initial_error_bound hΘ (show 0 ≤ 200000*e by
      positivity) hlam hFp hvelocityInitial hh
  exact hb.trans (mul_le_mul_of_nonneg_right hcoef hFp)

/-- Neighbor stability constant, given by `1000000000*exp 6`. -/
def neighborStabilityConstant : ℝ := 1000000000*exp 6

theorem neighborStabilityConstant_ge : 1000000000 ≤ neighborStabilityConstant := by
  have h : 1 ≤ exp (6:ℝ) := one_le_exp_iff.mpr (by norm_num)
  unfold neighborStabilityConstant
  linarith only [h]

theorem controlled_neighbor_stage_references_within
    {σ Θ T e ε lam : ℝ} {U V P Q N : ℝ → ℝ} {R A C : ℝ → Fin 3 → Fin 3 → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 < T) (hT : T ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hlam : 0 ≤ lam) (hsmall : 1000000 * neighborStabilityConstant * e * Θ ^ 40 ≤ 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivWithinAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) (Icc 0 T) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivWithinAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) (Icc 0 T) t)
    (hU : ∀ t ∈ Icc 0 T, HasDerivWithinAt U
      (velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) (Icc 0 T) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivWithinAt V
      (velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) (Icc 0 T) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry (σ ^ 2) i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ j,
      |C t 0 j - idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |C t 1 j - idealUnprojectedEntry 1 j| ≤ 5 * e)
    (hrayInitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e)
    (hvelocityInitial : |V 0 - 1| + |U 0 + lam| ≤ e) :
    ∃ F F₁ Z Z₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = lam ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧ (∀ t, HasDerivAt Z (Z₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*F₁ s)
        (2*(1-σ^2*(σ^2*t^2))*F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
        (2*(1-σ^2*(σ^2*t^2))*Z t) t) ∧
      (∀ t ∈ Icc 0 T, |V t-Z t|+|U t+Z₁ t| ≤ 400000000*e*Θ^29*(1+lam)*F t) ∧
      (∀ t ∈ Icc 1 T, 0 < V t ∧ |V t/Z t-1| ≤ neighborStabilityConstant*e*Θ^29 ∧
        |U t/V t+Z₁ t/Z t| ≤ 10*(neighborStabilityConstant*e*Θ^29)) := by
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  obtain ⟨F, F₁, G, G₁, hF0, hF₁0, _, hG₁0, hF, hG, hfluxF, hfluxG⟩ :=
    equation30_exists_fundamental_system (sq_nonneg σ) hσ2
  obtain ⟨Z, Z₁, hZ0, hZ₁0, hZ, hfluxZ⟩ := equation30_exists_global (sq_nonneg σ) hσ2 1 lam
  have hK := neighborStabilityConstant_ge
  have hΘ0 : 0 ≤ Θ := by linarith only [hΘ]
  have hsmallODE : 8000000*e*Θ^21 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 21 ≤ 40)) he
    have hprod := mul_nonneg (show 0 ≤ neighborStabilityConstant-8 by linarith only [hK])
      (mul_nonneg he (pow_nonneg hΘ0 40))
    linarith only [hsmall, hm, hprod]
  have herror := controlled_neighbor_relative_error_within hσ hσsmall hΘ hT0 hT he hε hεe
    hlam hsmallODE (fun t _ => hF t) (fun t _ => hG t) (fun t _ => hfluxF t) (fun t _ => hfluxG t)
    hF0 hF₁0 hG₁0 hRc hAc hCc hP hQ hN hU hV hRclose hAclose hCclose
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hrayInitial hvelocityInitial hZ0 hZ₁0
  refine ⟨F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfluxF, hfluxZ, herror, ?_⟩
  intro t ht
  let δ := 400000000*e*Θ^29
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hs : 4*exp 6*δ ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 29 ≤ 40))
      (show 0 ≤ neighborStabilityConstant*e by positivity [neighborStabilityConstant])
    have hn : 0 ≤ neighborStabilityConstant*e*Θ^40 := by positivity [neighborStabilityConstant]
    dsimp [δ]
    unfold neighborStabilityConstant at hm hn hsmall
    linarith only [hm, hn, hsmall]
  have herror' : |V t-Z t|+|U t+Z₁ t| ≤ δ*(1+lam)*F t :=
    herror t ⟨by linarith only [ht.1], ht.2⟩
  have hc := equation30_relative_state_consequences hσ hσsmall hlam ht.1 hδ hs
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 herror'
  refine ⟨hc.1, ?_, ?_⟩
  · dsimp [δ]
      at hc
    unfold neighborStabilityConstant
    linarith only [hc.2.1, mul_nonneg (mul_nonneg (exp_pos (6:ℝ)).le he) (pow_nonneg hΘ0 29)]
  · dsimp [δ]
      at hc
    unfold neighborStabilityConstant
    linarith only [hc.2.2, mul_nonneg (mul_nonneg (exp_pos (6:ℝ)).le he) (pow_nonneg hΘ0 29)]

end EulerPacketMovingFrame
