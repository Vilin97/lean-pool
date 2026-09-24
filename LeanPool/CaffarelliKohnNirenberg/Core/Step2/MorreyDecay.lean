/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.UpperSemicontinuity
public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.ThetaUpperSemicontinuity
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyDecayAux
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.Iteration
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.PointwiseEnergy

/-!
# Morrey Decay

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

open MorreyDecayAux


private lemma morreyDecay_contraction
    {C₂₇ C₂₈ T Tnext b L : ℝ}
    (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hbsmall : b ≤ iterationEpsilonStar C₂₇)
    (hdec : Tnext ≤
      C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * T +
        C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) * (b ^ (1 / 2 : ℝ) + b) * T +
        C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) *
          L ^ (1 / 2 : ℝ) + C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * L) :
    Tnext ≤ (3 / 8 : ℝ) * T + iterationC₂₉ C₂₇ C₂₈ * L := by
  let κ := iterationKappa C₂₇
  let ε := iterationEpsilon
  let εStar := iterationEpsilonStar C₂₇
  let C₂₉ := iterationC₂₉ C₂₇ C₂₈
  have hκ : 0 < κ := iterationKappa_pos hC₂₇
  have hκone : κ ≤ 1 := (iterationKappa_le_half C₂₇).trans (by norm_num)
  have hε : 0 < ε := by norm_num [ε, iterationEpsilon]
  have hεStar : 0 < εStar := iterationEpsilonStar_pos hC₂₇
  have hfirst : C₂₇ * κ ^ (2 / 3 : ℝ) * T ≤
      (1 / 8 : ℝ) * T := by
    have hA := iterationKappa_prop₁ hC₂₇
    have hκpow : κ ^ (2 / 3 : ℝ) ≤ κ ^ (2 / 3 - ε) :=
      Real.rpow_le_rpow_of_exponent_ge hκ hκone
        (by linarith only [hε])
    have hcoef : C₂₇ * κ ^ (2 / 3 : ℝ) ≤ (1 / 8 : ℝ) :=
      (mul_le_mul_of_nonneg_left hκpow hC₂₇.le).trans hA
    exact mul_le_mul_of_nonneg_right hcoef hT
  have hsecond : C₂₇ * κ ^ (-5 : ℝ) *
      (b ^ (1 / 2 : ℝ) + b) * T ≤ (1 / 8 : ℝ) * T := by
    have hbs : b ^ (1 / 2 : ℝ) ≤ εStar ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow hb hbsmall
      norm_num
    have hsum : b ^ (1 / 2 : ℝ) + b ≤
        εStar ^ (1 / 2 : ℝ) + εStar := by
      linarith only [hbs, hbsmall]
    have hκpow : κ ^ (-5 : ℝ) ≤ κ ^ (-5 - ε) :=
      Real.rpow_le_rpow_of_exponent_ge hκ hκone
        (by linarith only [hε])
    have hsum0 : 0 ≤ εStar ^ (1 / 2 : ℝ) + εStar := by positivity
    have hcoef : C₂₇ * κ ^ (-5 : ℝ) *
        (b ^ (1 / 2 : ℝ) + b) ≤ (1 / 8 : ℝ) := by
      calc
        C₂₇ * κ ^ (-5 : ℝ) * (b ^ (1 / 2 : ℝ) + b) ≤
            C₂₇ * κ ^ (-5 : ℝ) *
              (εStar ^ (1 / 2 : ℝ) + εStar) := by
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
        _ ≤ 2 * C₂₇ * κ ^ (-5 - ε) *
              (εStar ^ (1 / 2 : ℝ) + εStar) := by
          have hcoef' := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hκpow hC₂₇.le) hsum0
          have hright0 : 0 ≤ C₂₇ * κ ^ (-5 - ε) *
              (εStar ^ (1 / 2 : ℝ) + εStar) := by positivity
          nlinarith only [hcoef', hright0]
        _ ≤ (1 / 8 : ℝ) := iterationKappa_prop₃ hC₂₇
    exact mul_le_mul_of_nonneg_right hcoef hT
  have hyoung : C₂₈ * κ ^ (-1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) *
      L ^ (1 / 2 : ℝ) ≤
      (1 / 8 : ℝ) * T + 2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * L := by
    have hθsq : (T ^ (1 / 2 : ℝ)) ^ 2 = T := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hT]
    have hLsq : (L ^ (1 / 2 : ℝ)) ^ 2 = L := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hL]
    have hκhalf : (κ ^ (-1 / 2 : ℝ)) ^ 2 = κ ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
      congr 1
      ring
    calc
      C₂₈ * κ ^ (-1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) =
          T ^ (1 / 2 : ℝ) *
            (C₂₈ * κ ^ (-1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) := by ring
      _ ≤ (1 / 8 : ℝ) * (T ^ (1 / 2 : ℝ)) ^ 2 +
            2 * (C₂₈ * κ ^ (-1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) ^ 2 := by
        nlinarith only [sq_nonneg (T ^ (1 / 2 : ℝ) -
          4 * (C₂₈ * κ ^ (-1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)))]
      _ = (1 / 8 : ℝ) * T + 2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * L := by
        simp only [mul_pow, hθsq, hLsq, hκhalf]
        ring
  have htail : 2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * L +
      C₂₈ * κ ^ (-3 : ℝ) * L ≤ C₂₉ * L := by
    have hκpow1 : κ ^ (-1 : ℝ) ≤ κ ^ (-1 - 2 * ε) :=
      Real.rpow_le_rpow_of_exponent_ge hκ hκone
        (by linarith only [hε])
    have hκpow2 : κ ^ (-3 : ℝ) ≤ κ ^ (-3 - ε) :=
      Real.rpow_le_rpow_of_exponent_ge hκ hκone
        (by linarith only [hε])
    have hmid : 2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * L +
        C₂₈ * κ ^ (-3 : ℝ) * L ≤
        (2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε) +
          C₂₈ * κ ^ (-3 - ε)) * L := by
      calc
        2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * L +
            C₂₈ * κ ^ (-3 : ℝ) * L ≤
            2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε) * L +
              C₂₈ * κ ^ (-3 - ε) * L := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hκpow1 (by positivity))
              hL)
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hκpow2 hC₂₈.le)
              hL)
        _ = (2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε) +
            C₂₈ * κ ^ (-3 - ε)) * L := by ring
    exact hmid
  nlinarith only [hdec, hfirst, hsecond, hyoung, htail]

/-! The remaining assembly uses the standing constants from the iteration
convention; the one-step decay display is its only analytic hypothesis. -/
theorem morreyDecay_of_thetaDecay
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hq : 5 / 2 < q) {z₀ : ParabolicPoint}
    (hz₀ : z₀ ∈ spaceTimeSet Ω I) {C₂₇ C₂₈ : ℝ}
    (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hThetaDecay : ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
        C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * theta (iterationKappa C₂₇) u Du p z ρ +
          C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
            (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
              theta (iterationKappa C₂₇) u Du p z ρ +
          C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
            theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
              lambda q f z ρ ^ (1 / 2 : ℝ) +
          C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ ∧
      (theta (iterationKappa C₂₇) u Du p z ρ ≤ 1 →
        theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
          C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
              theta (iterationKappa C₂₇) u Du p z ρ +
            2 * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
              theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
              theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                lambda q f z ρ ^ (1 / 2 : ℝ) +
            C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ))
    (hβlim : Filter.limsup (fun r : ℝ =>
        (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
            ENNReal.ofReal (spatialGradientSq u Du w))
      (𝓝[>] (0 : ℝ)) <
        ENNReal.ofReal ((iterationEpsilonStar C₂₇) ^ (2 : ℕ))) :
    ∃ r₂ M : ℝ, 0 < r₂ ∧ 1 ≤ M ∧
      Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I ∧
      (∀ z, z ∈ Metric.ball z₀ r₂ → ∀ r : ℝ, 0 < r → r < r₂ →
        max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
          M * r ^ (2 / 5 : ℝ)) := by
  let κ : ℝ := iterationKappa C₂₇
  let η : ℝ := iterationEta C₂₇
  let εStar : ℝ := iterationEpsilonStar C₂₇
  let Λ₀ : ℝ := iterationLambda₀ C₂₇ C₂₈
  let C₂₉ : ℝ := iterationC₂₉ C₂₇ C₂₈
  let ε : ℝ := iterationEpsilon
  let ηd : ℝ := min η (min (η ^ 2 / 8) (κ ^ 4 * η / 8))
  have hκ : 0 < κ := by dsimp [κ]; exact iterationKappa_pos hC₂₇
  have hκle : κ ≤ 1 / 2 := by dsimp [κ]; exact iterationKappa_le_half C₂₇
  have hκone : κ ≤ 1 := hκle.trans (by norm_num)
  have hη : 0 < η := by dsimp [η]; exact iterationEta_pos hC₂₇
  have hηle : η ≤ 1 := by dsimp [η]; exact iterationEta_le_one C₂₇
  have hηd : 0 < ηd := by
    dsimp [ηd]
    exact lt_min hη (lt_min (by positivity) (by positivity))
  have hε : 0 < ε := by dsimp [ε]; norm_num [iterationEpsilon]
  have hεStar : 0 < εStar := by
    dsimp [εStar]
    exact iterationEpsilonStar_pos hC₂₇
  have hσ : 1 < 3 - 5 / q := by
    have hqpos : 0 < q := lt_trans (by norm_num) hq
    have hfive : 5 / q < (2 : ℝ) := by
      apply (div_lt_iff₀ hqpos).2
      nlinarith only [hq]
    linarith only [hfive]
  have hεσ : ε ≤ 3 - 5 / q := by
    dsimp [ε, iterationEpsilon]
    nlinarith only [hσ]
  have hC₂₉ : 0 < C₂₉ := by dsimp [C₂₉]; exact iterationC₂₉_pos hC₂₇ hC₂₈
  have hΛ : C₂₉ * Λ₀ = η / 2 := by
    dsimp [C₂₉, Λ₀, η]
    exact iterationC₂₉_mul_Lambda₀ hC₂₇ hC₂₈
  obtain ⟨Ropen, hRopen, hRopenSub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1).mem_nhds hz₀)
  let Rbig : ℝ := Ropen / 4
  have hRbig : 0 < Rbig := by dsimp [Rbig]; positivity
  let zbig : ParabolicPoint := (z₀.1, z₀.2 + Rbig ^ 2)
  let Rbig' : ℝ := 2 * Rbig
  have hRbig' : 0 < Rbig' := by dsimp [Rbig']; positivity
  have hbigSub : closure (parabolicCylinder zbig.1 zbig.2 Rbig') ⊆
      spaceTimeSet Ω I := by
    intro y hy
    rw [closure_parabolicCylinder hRbig'] at hy
    apply hRopenSub
    rw [Metric.mem_ball, dist_eq_parabolicDist]
    change max (vec3EuclideanNorm (y.1 - z₀.1))
        (Real.sqrt |y.2 - z₀.2|) < Ropen
    apply max_lt
    · have hspace : vec3EuclideanNorm (y.1 - z₀.1) ≤ Rbig' := by
        exact hy.1
      dsimp [Rbig', Rbig] at hspace ⊢
      linarith only [hspace, hRopen]
    · apply (Real.sqrt_lt' hRopen).2
      have htime : |y.2 - z₀.2| ≤ 3 * Rbig ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith only [hy.2.1, hy.2.2]
      have htime' : 3 * Rbig ^ 2 < Ropen ^ 2 := by
        dsimp [Rbig]
        nlinarith only [sq_pos_of_pos hRopen]
      exact lt_of_le_of_lt htime htime'
  have hforceBig : (∫⁻ w in parabolicCylinder zbig.1 zbig.2 Rbig',
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) < ⊤ :=
    sws_force_integral_lt_top hsol hRbig' hbigSub
  let Froot : ℝ :=
    (∫⁻ w in parabolicCylinder zbig.1 zbig.2 Rbig',
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^ (1 / q : ℝ)
  have hFroot : 0 ≤ Froot := by
    dsimp [Froot]
    positivity
  have hpowTendsto : Tendsto (fun r : ℝ => r ^ (3 - 5 / q) * Froot)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hσpos : 0 < 3 - 5 / q := lt_trans (by norm_num) hσ
    have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (hid.rpow_const_nhds_zero hσpos).mul_const Froot
  have hforceEvent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      r ^ (3 - 5 / q) * Froot < Λ₀ :=
    (tendsto_order.1 hpowTendsto).2 _
      (by dsimp [Λ₀]; exact iterationLambda₀_pos hC₂₇ hC₂₈)
  obtain ⟨rforce, hrforce, hforceBall⟩ :=
    Metric.mem_nhdsWithin_iff.mp hforceEvent
  have hquotEvent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
            ENNReal.ofReal (spatialGradientSq u Du w) <
        ENNReal.ofReal (εStar ^ (2 : ℕ)) := by
    exact eventually_lt_of_limsup_lt (by simpa [εStar] using hβlim)
  have hβevent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      beta u Du z₀ r < εStar := by
    filter_upwards [hquotEvent, eventually_mem_nhdsWithin,
      (eventually_lt_nhds hRopen).filter_mono nhdsWithin_le_nhds] with r hq hr hRr
    change 0 < r at hr
    have hsubr : closure (parabolicCylinder z₀.1 z₀.2 r) ⊆
        spaceTimeSet Ω I := by
      intro y hy
      have hyc := step2_closure_cylinder_subset_closedBall hr hy
      apply hRopenSub
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hyc) hRr
    have heq := sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq
      hsol z₀ hr hsubr
    rw [heq] at hq
    rw [← ENNReal.ofReal_inv_of_pos hr,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ r⁻¹)] at hq
    have hq' : ENNReal.ofReal (beta u Du z₀ r ^ 2) <
        ENNReal.ofReal (εStar ^ (2 : ℕ)) := by
      convert hq using 1
      congr 1
      field_simp
    have hroot : beta u Du z₀ r ^ 2 < εStar ^ (2 : ℕ) := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hq'
    have hβnonneg : 0 ≤ beta u Du z₀ r := by
      unfold beta
      positivity
    nlinarith only [hroot, hβnonneg, hεStar]
  obtain ⟨U, hU, h0U, hUsub⟩ := mem_nhdsWithin.1 hβevent
  obtain ⟨Rβ, hRβ, hRβsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  let rbase : ℝ := min (Ropen / 8) (min (Rβ / 2) (rforce / 2))
  have hrbase : 0 < rbase := by
    dsimp [rbase]
    positivity
  have hrbaseR : rbase < Ropen := by
    dsimp [rbase]
    have hle : min (Ropen / 8) (min (Rβ / 2) (rforce / 2)) ≤ Ropen / 8 :=
      min_le_left _ _
    linarith only [hle, hRopen]
  have hrbaseβ : rbase < Rβ := by
    dsimp [rbase]
    have hle₁ : min (Ropen / 8) (min (Rβ / 2) (rforce / 2)) ≤
        min (Rβ / 2) (rforce / 2) := min_le_right _ _
    have hle₂ : min (Rβ / 2) (rforce / 2) ≤ Rβ / 2 := min_le_left _ _
    linarith only [hle₁, hle₂, hRβ]
  have hrbaseForce : rbase < rforce := by
    dsimp [rbase]
    have hle₁ : min (Ropen / 8) (min (Rβ / 2) (rforce / 2)) ≤
        min (Rβ / 2) (rforce / 2) := min_le_right _ _
    have hle₂ : min (Rβ / 2) (rforce / 2) ≤ rforce / 2 := min_le_right _ _
    linarith only [hle₁, hle₂, hrforce]
  have hbaseSub : closure (parabolicCylinder z₀.1 z₀.2 rbase) ⊆
      spaceTimeSet Ω I := by
    intro y hy
    have hyc := step2_closure_cylinder_subset_closedBall hrbase hy
    apply hRopenSub
    rw [Metric.mem_ball]
    have htri := dist_triangle y z₀ z₀
    change dist y (z₀.1, z₀.2) < Ropen
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hyc) hrbaseR
  have hforceBase : (∫⁻ w in parabolicCylinder z₀.1 z₀.2 rbase,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) < ⊤ :=
    sws_force_integral_lt_top hsol hrbase hbaseSub
  let lambdaBase := lambda q f z₀ rbase
  have hlambdaBase : 0 ≤ lambdaBase := by
    dsimp [lambdaBase, lambda]
    positivity
  let lambdaSmall : ℝ := min Λ₀ (ηd / (16 * C₂₉))
  have hlambdaSmall : 0 < lambdaSmall := by
    dsimp [lambdaSmall]
    exact lt_min (by dsimp [Λ₀]; exact iterationLambda₀_pos hC₂₇ hC₂₈)
      (by positivity)
  have hκlt : κ < 1 := lt_of_le_of_lt hκle (by norm_num)
  let a : ℝ := κ ^ (3 - 5 / q)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    exact Real.rpow_lt_one hκ.le hκlt (by linarith only [hσ])
  have hlambdaTendsto : Tendsto (fun n : ℕ => a ^ n * lambdaBase)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).mul_const lambdaBase
  have hlambdaEvent : ∀ᶠ n : ℕ in atTop, a ^ n * lambdaBase < lambdaSmall :=
    (tendsto_order.1 hlambdaTendsto).2 _ hlambdaSmall
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlambdaEvent
  let r₄ : ℝ := κ ^ N * rbase
  have hr₄ : 0 < r₄ := by dsimp [r₄]; positivity
  have hr₄base : r₄ ≤ rbase := by
    dsimp [r₄]
    simpa [mul_comm] using
      (mul_le_of_le_one_right hrbase.le (pow_le_one₀ hκ.le hκone) :
        rbase * κ ^ N ≤ rbase)
  have hsub₄ : closure (parabolicCylinder z₀.1 z₀.2 r₄) ⊆
      spaceTimeSet Ω I :=
    (closure_parabolicCylinder_mono hr₄.le hr₄base).trans hbaseSub
  have hβsmall : ∀ {r : ℝ}, 0 < r → r ≤ rbase →
      beta u Du z₀ r ≤ εStar := by
    intro r hr hrb
    apply le_of_lt
    apply hUsub
    exact ⟨hRβsub (by
      rw [Metric.mem_ball]
      simpa [Real.dist_eq, abs_of_pos hr] using lt_of_le_of_lt hrb hrbaseβ), hr⟩
  have hlambda₄ : lambda q f z₀ r₄ ≤ lambdaSmall := by
    have hmono := lambda_mono_radius_of_sws hsol z₀ hr₄ hr₄base hbaseSub
    have hratio : r₄ / rbase = κ ^ N := by
      dsimp [r₄]
      field_simp
    have hpow : (κ ^ N) ^ (3 - 5 / q) = a ^ N := by
      dsimp [a]
      calc
        (κ ^ N) ^ (3 - 5 / q) = (κ ^ (N : ℝ)) ^ (3 - 5 / q) := by
          rw [Real.rpow_natCast]
        _ = κ ^ ((N : ℝ) * (3 - 5 / q)) := by
          rw [Real.rpow_mul hκ.le]
        _ = κ ^ ((3 - 5 / q) * (N : ℝ)) := by
          congr 1
          ring
        _ = (κ ^ (3 - 5 / q)) ^ N := by
          rw [Real.rpow_mul hκ.le, Real.rpow_natCast]
    rw [hratio, hpow] at hmono
    exact hmono.trans
      (le_of_lt (hN N le_rfl))

  let Θ : ℕ → ℝ := fun n => theta κ u Du p z₀ (κ ^ n * r₄)
  let L : ℕ → ℝ := fun n => lambda q f z₀ (κ ^ n * r₄)
  have hΘnonneg : ∀ n, 0 ≤ Θ n := by
    intro n
    dsimp [Θ]
    unfold theta alpha beta delta
    positivity
  have hLdecay : ∀ n, 0 ≤ L n ∧ L n ≤
      κ ^ ((n : ℝ) * (3 - 5 / q)) * L 0 := by
    intro n
    have hρ : 0 < κ ^ n * r₄ := by positivity
    have hρr : κ ^ n * r₄ ≤ r₄ := by
      simpa [mul_comm] using
        (mul_le_of_le_one_right hr₄.le (pow_le_one₀ hκ.le hκone) :
          r₄ * κ ^ n ≤ r₄)
    have hmono := lambda_mono_radius_of_sws hsol z₀ hρ hρr hsub₄
    have hratio : (κ ^ n * r₄) / r₄ = κ ^ n := by
      field_simp
    have hpow : (κ ^ n) ^ (3 - 5 / q) =
        κ ^ ((n : ℝ) * (3 - 5 / q)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
    have hnonneg : 0 ≤ L n := by
      dsimp [L, lambda]
      positivity
    refine ⟨hnonneg, ?_⟩
    rw [hratio, hpow] at hmono
    simpa [L] using hmono
  have hL0small : L 0 ≤ lambdaSmall := by
    simpa [L] using hlambda₄
  have hLsource : ∀ n, C₂₉ * L n ≤ ηd / 16 := by
    intro n
    have hpow : κ ^ ((n : ℝ) * (3 - 5 / q)) ≤ 1 := by
      apply Real.rpow_le_one hκ.le hκone
      positivity
    have hLn : L n ≤ lambdaSmall := by
      calc
        L n ≤ κ ^ ((n : ℝ) * (3 - 5 / q)) * L 0 := (hLdecay n).2
        _ ≤ L 0 := by
          rw [mul_comm]
          exact mul_le_of_le_one_right (hLdecay 0).1 hpow
        _ ≤ lambdaSmall := hL0small
    have hsmall : C₂₉ * lambdaSmall ≤ ηd / 16 := by
      dsimp [lambdaSmall]
      have hmin := min_le_right Λ₀ (ηd / (16 * C₂₉))
      have hmul := mul_le_mul_of_nonneg_left hmin hC₂₉.le
      convert hmul using 1; field_simp
    exact (mul_le_mul_of_nonneg_left hLn hC₂₉.le).trans hsmall
  have hrec : ∀ n, Θ (n + 1) ≤ (3 / 8 : ℝ) * Θ n + C₂₉ * L n := by
    intro n
    have hρ : 0 < κ ^ n * r₄ := by positivity
    have hρr : κ ^ n * r₄ ≤ r₄ := by
      simpa [mul_comm] using
        (mul_le_of_le_one_right hr₄.le (pow_le_one₀ hκ.le hκone) :
          r₄ * κ ^ n ≤ r₄)
    have hρsub : closure (parabolicCylinder z₀.1 z₀.2 (κ ^ n * r₄)) ⊆
        spaceTimeSet Ω I :=
      (closure_parabolicCylinder_mono hρ.le hρr).trans hsub₄
    have hβn : beta u Du z₀ (κ ^ n * r₄) ≤ εStar :=
      hβsmall hρ (hρr.trans hr₄base)
    have hdec := (hThetaDecay hρ hρsub).1
    have hb : 0 ≤ beta u Du z₀ (κ ^ n * r₄) := by
      unfold beta
      positivity
    have hstep := morreyDecay_contraction hC₂₇ hC₂₈ (hΘnonneg n)
      (hLdecay n).1 hb hβn hdec
    have hnext : Θ (n + 1) = theta κ u Du p z₀ (κ * (κ ^ n * r₄)) := by
      dsimp [Θ]
      congr 1
      rw [pow_succ]
      ring
    rw [hnext]
    exact hstep
  obtain ⟨n₀, hn₀⟩ := exists_small_normalized hηd hrec hLsource
  let R₀ : ℝ := κ ^ n₀ * r₄
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    positivity
  have hR₀r₄ : R₀ ≤ r₄ := by
    dsimp [R₀]
    simpa using (mul_le_mul_of_nonneg_right
      (pow_le_one₀ hκ.le hκone : κ ^ n₀ ≤ 1) hr₄.le)
  have hsub₀ : closure (parabolicCylinder z₀.1 z₀.2 R₀) ⊆
      spaceTimeSet Ω I :=
    (closure_parabolicCylinder_mono hR₀.le hR₀r₄).trans hsub₄
  have hθ₀ : theta κ u Du p z₀ R₀ ≤ ηd / 4 := by
    simpa [R₀, Θ] using hn₀
  have hθ₀η : theta κ u Du p z₀ R₀ ≤ η := by
    have hdη : ηd ≤ η := min_le_left _ _
    nlinarith only [hθ₀, hdη, hηd]
  have hηd_sq : ηd ≤ η ^ 2 / 8 := by
    exact (min_le_right η _).trans (min_le_left _ _)
  have hηd_delta : ηd ≤ κ ^ 4 * η / 8 := by
    exact (min_le_right η _).trans (min_le_right _ _)
  have hθ₀ηsq : theta κ u Du p z₀ R₀ ≤ η ^ 2 / 32 := by
    calc
      theta κ u Du p z₀ R₀ ≤ ηd / 4 := hθ₀
      _ ≤ (η ^ 2 / 8) / 4 := div_le_div_of_nonneg_right hηd_sq (by norm_num)
      _ = η ^ 2 / 32 := by ring
  have hηsqle : η ^ 2 ≤ η := by
    nlinarith only [hη, hηle]
  have hrect₀ : euclideanClosedBall z₀.1 R₀ ×ˢ
      Icc (z₀.2 - R₀ ^ 2) z₀.2 ⊆ spaceTimeSet Ω I := by
    intro y hy
    apply hsub₀
    rw [closure_parabolicCylinder hR₀]
    refine ⟨?_, hy.2⟩
    change vec3EuclideanNorm (y.1 - z₀.1) ≤ R₀
    have heq : CKN.vecEuclideanNorm (y.1 - z₀.1) =
        vec3EuclideanNorm (y.1 - z₀.1) := by
      simp [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot, pow_two]
    rw [← heq]
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR₀.le).1 hy.1
  let ϱ : ℝ := 5 / 7 * R₀
  have hϱ : 0 < ϱ := by
    dsimp [ϱ]
    positivity
  have hϱR : ϱ < R₀ := by
    dsimp [ϱ]
    nlinarith only [hR₀]
  have hratio : R₀ / ϱ = 7 / 5 := by
    dsimp [ϱ]
    field_simp
  have husc := theta_usc_of_sws_with_alpha_bound hsol hϱ hϱR hrect₀ hz₀.2
  have hα₀ : 0 ≤ alpha u z₀ R₀ := by
    unfold alpha
    positivity
  have hβ₀ : 0 ≤ beta u Du z₀ R₀ := by
    unfold beta
    positivity
  have hδ₀sq : 0 ≤ delta p z₀ R₀ ^ 2 := sq_nonneg _
  have hcomp₀ := max_components_le_theta (p := p) hκ hκone hα₀ hβ₀
  have hα₀le : alpha u z₀ R₀ ≤ theta κ u Du p z₀ R₀ :=
    (le_max_left _ _ |>.trans (le_max_left _ _)).trans hcomp₀
  have hβ₀le : beta u Du z₀ R₀ ≤ theta κ u Du p z₀ R₀ :=
    (le_max_right _ _ |>.trans (le_max_left _ _)).trans hcomp₀
  have hδ₀le : delta p z₀ R₀ ^ 2 ≤ theta κ u Du p z₀ R₀ :=
    (le_max_right _ _).trans hcomp₀
  have hα₀sq : alpha u z₀ R₀ ^ 2 ≤ theta κ u Du p z₀ R₀ := by
    have hα₀one : alpha u z₀ R₀ ≤ 1 := hα₀le.trans (hθ₀η.trans hηle)
    have hsq : alpha u z₀ R₀ ^ 2 ≤ alpha u z₀ R₀ := by
      nlinarith only [hα₀, hα₀one]
    exact hsq.trans hα₀le
  have hαlim : Filter.limsup (fun z : ParabolicPoint => alpha u z ϱ ^ 2)
      (𝓝 z₀) < η ^ 2 / 16 := by
    have hfactor : (R₀ / ϱ) * alpha u z₀ R₀ ^ 2 ≤
        (7 / 5 : ℝ) * theta κ u Du p z₀ R₀ := by
      rw [hratio]
      exact mul_le_mul_of_nonneg_left hα₀sq (by norm_num)
    calc
      Filter.limsup (fun z : ParabolicPoint => alpha u z ϱ ^ 2) (𝓝 z₀) ≤
          (R₀ / ϱ) * alpha u z₀ R₀ ^ 2 := husc.1
      _ ≤ (7 / 5 : ℝ) * theta κ u Du p z₀ R₀ := hfactor
      _ < η ^ 2 / 16 := by nlinarith only [hθ₀ηsq, hη]
  have hθ₀nonneg : 0 ≤ theta κ u Du p z₀ R₀ := by
    unfold theta
    positivity
  have hβϱ : beta u Du z₀ ϱ < η / 4 := by
    have hβmono := beta_mono_radius_of_sws hsol z₀ hϱ hϱR.le hsub₀
    rw [hratio] at hβmono
    have hfactor : (7 / 5 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow (by norm_num : 0 ≤ (7 / 5 : ℝ))
        (by norm_num : (7 / 5 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      nlinarith only [h]
    have hmul : (7 / 5 : ℝ) ^ (1 / 2 : ℝ) * beta u Du z₀ R₀ ≤
        2 * theta κ u Du p z₀ R₀ := by
      calc
        (7 / 5 : ℝ) ^ (1 / 2 : ℝ) * beta u Du z₀ R₀ ≤
            (7 / 5 : ℝ) ^ (1 / 2 : ℝ) * theta κ u Du p z₀ R₀ :=
          mul_le_mul_of_nonneg_left hβ₀le (by positivity)
        _ ≤ 2 * theta κ u Du p z₀ R₀ := by
          exact mul_le_mul_of_nonneg_right hfactor hθ₀nonneg
    exact (hβmono.trans hmul).trans_lt (by
      nlinarith only [hθ₀ηsq, hη, hηsqle])
  have hδϱ : delta p z₀ ϱ ^ 2 < κ ^ 4 * η / 4 := by
    have hδmono := delta_sq_mono_radius_of_sws hsol z₀ hϱ hϱR.le hsub₀
    rw [hratio] at hδmono
    have hfactor₁ : (7 / 5 : ℝ) ^ (4 / 3 : ℝ) ≤ (7 / 5 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hfactor : (7 / 5 : ℝ) ^ (4 / 3 : ℝ) ≤ 2 := by
      have hpow : (7 / 5 : ℝ) ^ (2 : ℝ) = 49 / 25 := by
        norm_num [Real.rpow_natCast]
      exact hfactor₁.trans (by rw [hpow]; norm_num)
    have hmul : (7 / 5 : ℝ) ^ (4 / 3 : ℝ) * delta p z₀ R₀ ^ 2 ≤
        2 * theta κ u Du p z₀ R₀ := by
      calc
        (7 / 5 : ℝ) ^ (4 / 3 : ℝ) * delta p z₀ R₀ ^ 2 ≤
            (7 / 5 : ℝ) ^ (4 / 3 : ℝ) * theta κ u Du p z₀ R₀ :=
          mul_le_mul_of_nonneg_left hδ₀le (by positivity)
        _ ≤ 2 * theta κ u Du p z₀ R₀ :=
          mul_le_mul_of_nonneg_right hfactor hθ₀nonneg
    have htarget : 2 * theta κ u Du p z₀ R₀ < κ ^ 4 * η / 4 := by
      have hκη : 0 < κ ^ 4 * η := by positivity
      nlinarith only [hθ₀, hηd_delta, hη, hκη]
    exact (hδmono.trans hmul).trans_lt htarget
  have hαevent : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      alpha u z ϱ ^ 2 < η ^ 2 / 16 := by
    exact eventually_lt_of_limsup_lt hαlim husc.2.2.2
  have hβeventϱ : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      beta u Du z ϱ < η / 4 :=
    husc.2.1.eventually (eventually_lt_nhds hβϱ)
  have hδeventϱ : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      delta p z ϱ ^ 2 < κ ^ 4 * η / 4 := by
    exact (husc.2.2.1.pow 2).eventually (eventually_lt_nhds hδϱ)
  have hαevent' : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      alpha u z ϱ < η / 4 := by
    filter_upwards [hαevent] with z hz
    have hnonneg : 0 ≤ alpha u z ϱ := by
      unfold alpha
      positivity
    nlinarith only [hz, hnonneg, hη, hηsqle]
  have hκprod : κ ^ (-4 : ℝ) * κ ^ (4 : ℕ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hκ]
    norm_num
  have htransfer : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      theta κ u Du p z ϱ ≤ η := by
    filter_upwards [hαevent', hβeventϱ, hδeventϱ] with z hαz hβz hδz
    have hδterm : κ ^ (-4 : ℝ) * delta p z ϱ ^ 2 < η / 4 := by
      calc
        κ ^ (-4 : ℝ) * delta p z ϱ ^ 2 <
            κ ^ (-4 : ℝ) * (κ ^ (4 : ℕ) * η / 4) :=
          mul_lt_mul_of_pos_left hδz (by positivity)
        _ = (κ ^ (-4 : ℝ) * κ ^ (4 : ℕ) * η) / 4 := by ring
        _ = η / 4 := by rw [hκprod, one_mul]
    unfold theta
    nlinarith only [hαz, hβz, hδterm, hη]
  obtain ⟨rE, hrE, hballE⟩ := Metric.mem_nhds_iff.mp htransfer

  let r₂ : ℝ := min (rE / 2) (min (ϱ / 2) (min (Ropen / 8) (Rbig / 8)))
  have hr₂ : 0 < r₂ := by
    dsimp [r₂]
    positivity
  have hr₂E : r₂ < rE := by
    dsimp [r₂]
    have hle₁ : min (rE / 2) (min (ϱ / 2) (min (Ropen / 8) (Rbig / 8))) ≤
        rE / 2 := min_le_left _ _
    linarith only [hle₁, hrE]
  have hr₂ϱ : r₂ < ϱ := by
    dsimp [r₂]
    have hle₁ : min (rE / 2) (min (ϱ / 2) (min (Ropen / 8) (Rbig / 8))) ≤
        min (ϱ / 2) (min (Ropen / 8) (Rbig / 8)) := min_le_right _ _
    have hle₂ : min (ϱ / 2) (min (Ropen / 8) (Rbig / 8)) ≤ ϱ / 2 :=
      min_le_left _ _
    linarith only [hle₁, hle₂, hϱ]
  have hr₂Ropen : r₂ ≤ Ropen / 8 := by
    dsimp [r₂]
    exact ((min_le_right (rE / 2)
      (min (ϱ / 2) (min (Ropen / 8) (Rbig / 8)))).trans
      (min_le_right (ϱ / 2) (min (Ropen / 8) (Rbig / 8)))).trans
      (min_le_left (Ropen / 8) (Rbig / 8))
  have hr₂Rbig : r₂ ≤ Rbig / 8 := by
    dsimp [r₂]
    exact ((min_le_right (rE / 2)
      (min (ϱ / 2) (min (Ropen / 8) (Rbig / 8)))).trans
      (min_le_right (ϱ / 2) (min (Ropen / 8) (Rbig / 8)))).trans
      (min_le_right (Ropen / 8) (Rbig / 8))
  have hR₀base : R₀ ≤ rbase := hR₀r₄.trans hr₄base
  have hbaseRopen : rbase ≤ Ropen / 8 := by
    dsimp [rbase]
    exact min_le_left _ _
  have hϱRopen : ϱ ≤ Ropen / 8 := by
    dsimp [ϱ]
    nlinarith only [hR₀, hR₀base, hbaseRopen]
  have hϱRbig : ϱ ≤ Rbig / 2 := by
    dsimp [Rbig]
    nlinarith only [hϱRopen]
  have hsumRbig : ϱ + r₂ < Rbig := by
    nlinarith only [hϱRbig, hr₂Rbig, hRbig]
  have hsumRopen : ϱ + r₂ < Ropen := by
    nlinarith only [hϱRopen, hr₂Ropen, hRopen]
  have hball₂ : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I := by
    intro y hy
    apply hRopenSub
    exact Metric.ball_subset_ball (by nlinarith only [hr₂Ropen, hRopen]) hy
  have hzrhosub : ∀ z ∈ Metric.ball z₀ r₂,
      closure (parabolicCylinder z.1 z.2 ϱ) ⊆ spaceTimeSet Ω I := by
    intro z hz y hy
    apply hRopenSub
    rw [Metric.mem_ball]
    have hyc : dist y z ≤ ϱ := by
      change y ∈ Metric.closedBall z ϱ
      rw [Metric.mem_closedBall, dist_eq_parabolicDist]
      rw [closure_parabolicCylinder hϱ] at hy
      change max (vec3EuclideanNorm (y.1 - z.1))
          (Real.sqrt |y.2 - z.2|) ≤ ϱ
      apply max_le hy.1
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · rw [abs_le]
        constructor <;> nlinarith only [hy.2.1, hy.2.2]
    have hzd : dist z z₀ < r₂ := Metric.mem_ball.mp hz
    exact lt_of_le_of_lt (dist_triangle y z z₀)
      (lt_of_le_of_lt (add_le_add hyc hzd.le) hsumRopen)
  have hmoveSub : ∀ z ∈ Metric.ball z₀ r₂,
      parabolicCylinder z.1 z.2 ϱ ⊆
        parabolicCylinder zbig.1 zbig.2 Rbig' := by
    intro z hz y hy
    have hyballz := parabolicCylinder_subset_metricBall_sameCenter z hϱ hy
    have hyball₀ : y ∈ Metric.ball z₀ (ϱ + r₂) := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (dist_triangle y z z₀)
        (add_lt_add (Metric.mem_ball.mp hyballz) (Metric.mem_ball.mp hz))
    have hyouter := metricBall_subset_parabolicCylinder_doubled z₀
      (add_pos hϱ hr₂) hyball₀
    change vec3EuclideanNorm (y.1 - z₀.1) < 2 * (ϱ + r₂) ∧
      (z₀.2 + (ϱ + r₂) ^ 2 - (2 * (ϱ + r₂)) ^ 2 < y.2 ∧
        y.2 ≤ z₀.2 + (ϱ + r₂) ^ 2) at hyouter
    dsimp [zbig, Rbig']
    change vec3EuclideanNorm (y.1 - z₀.1) < 2 * Rbig ∧
      (z₀.2 + Rbig ^ 2 - (2 * Rbig) ^ 2 < y.2 ∧
        y.2 ≤ z₀.2 + Rbig ^ 2)
    have hsquare : (ϱ + r₂) ^ 2 ≤ Rbig ^ 2 :=
      (sq_le_sq₀ (by positivity) hRbig.le).2 hsumRbig.le
    constructor
    · nlinarith only [hyouter.1, hsumRbig]
    · constructor
      · nlinarith only [hyouter.2.1, hsquare]
      · nlinarith only [hyouter.2.2, hsquare]
  have hlamz : ∀ z ∈ Metric.ball z₀ r₂, lambda q f z ϱ ≤ Λ₀ := by
    intro z hz
    have hL := lambda_le_of_subset hsol hϱ (hmoveSub z hz) hforceBig
    have hbaseRforce : rbase ≤ rforce / 2 := by
      dsimp [rbase]
      exact (min_le_right (Ropen / 8) (min (Rβ / 2) (rforce / 2))).trans
        (min_le_right (Rβ / 2) (rforce / 2))
    have hϱforce : ϱ < rforce := by
      dsimp [ϱ]
      nlinarith only [hR₀, hR₀base, hbaseRforce, hrforce]
    have hforce : ϱ ^ (3 - 5 / q) * Froot < Λ₀ := by
      apply hforceBall
      constructor
      · rw [Metric.mem_ball]
        simpa [Real.dist_eq, abs_of_pos hϱ] using hϱforce
      · exact hϱ
    have hL' : lambda q f z ϱ ≤ ϱ ^ (3 - 5 / q) * Froot := by
      simpa [Froot] using hL
    exact hL'.trans hforce.le
  let K : ℝ := κ ^ (-4 / 3 - ε) * η * ϱ ^ (-ε)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  let M : ℝ := max 1 K
  have hM : 1 ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  refine ⟨r₂, M, hr₂, hM, hball₂, ?_⟩
  intro z hz r hr hrr
  have hθz : theta κ u Du p z ϱ ≤ η := by
    exact hballE (Metric.ball_subset_ball (le_of_lt hr₂E) hz)
  have hiterz := iteration_of_thetaDecay (C₂₇ := C₂₇) (C₂₈ := C₂₈)
    hsol hC₂₇ hC₂₈ hϱ (hzrhosub z hz) hθz (hlamz z hz) hThetaDecay
  have hrrϱ : r ≤ ϱ := (le_of_lt hrr).trans (le_of_lt hr₂ϱ)
  have hθraw : theta κ u Du p z r ≤
      κ ^ (-4 / 3 - ε) * η * ϱ ^ (-ε) * r ^ ε := by
    simpa [κ, η, ε] using hiterz.2 r hr hrrϱ
  have hθK : theta κ u Du p z r ≤ K * r ^ (2 / 5 : ℝ) := by
    have hεeq : ε = 2 / 5 := by norm_num [ε, iterationEpsilon]
    simpa [K, hεeq] using hθraw
  have hMmul : K * r ^ (2 / 5 : ℝ) ≤ M * r ^ (2 / 5 : ℝ) := by
    exact mul_le_mul_of_nonneg_right (by dsimp [M]; exact le_max_right _ _)
      (by positivity)
  exact (max_components_le_theta hκ hκone (by unfold alpha; positivity)
    (by unfold beta; positivity)).trans (hθK.trans hMmul)

end CKN
