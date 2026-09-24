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
private lemma morreyDecay_hbigSub_1 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint},
      ∀ Ropen > (0 : ℝ),
        Metric.ball z₀ Ropen ⊆ spaceTimeSet Ω I →
          let Rbig : ℝ := Ropen / (4 : ℝ);
          let zbig : ParabolicPoint := (z₀.1, z₀.2 + Rbig ^ (2 : ℕ));
          let Rbig' : ℝ := (2 : ℝ) * Rbig;
          (0 : ℝ) < Rbig' → closure (parabolicCylinder zbig.1 zbig.2 Rbig') ⊆ spaceTimeSet Ω I
    := by
  intro Ω I z₀ Ropen hRopen hRopenSub Rbig zbig Rbig' hRbig' y hy
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

private lemma morreyDecay_hβevent_2 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        (5 / 2 : ℝ) < q →
          ∀ {z₀ : ParabolicPoint} {C₂₇ : ℝ},
            let εStar : ℝ := iterationEpsilonStar C₂₇;
            (0 : ℝ) < εStar →
              ∀ Ropen > (0 : ℝ),
                Metric.ball z₀ Ropen ⊆ spaceTimeSet Ω I →
                  (∀ᶠ (r : ℝ) in 𝓝[>] (0 : ℝ),
                      (ENNReal.ofReal r)⁻¹ *
                          ∫⁻ (w : ParabolicPoint) in parabolicCylinder z₀.1 z₀.2 r,
                            ENNReal.ofReal (spatialGradientSq u Du w) <
                        ENNReal.ofReal (εStar ^ (2 : ℕ))) →
                    ∀ᶠ (r : ℝ) in 𝓝[>] (0 : ℝ), beta u Du z₀ r < εStar
    := by
  intro Ω I q u Du p f hsol hq z₀ C₂₇ εStar hεStar Ropen hRopen hRopenSub hquotEvent
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

private lemma morreyDecay_hlambda₄_3 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {C₂₇ C₂₈ : ℝ},
          let κ : ℝ := iterationKappa C₂₇;
          let η : ℝ := iterationEta C₂₇;
          let Λ₀ : ℝ := iterationLambda₀ C₂₇ C₂₈;
          let C₂₉ : ℝ := iterationC₂₉ C₂₇ C₂₈;
          let ηd : ℝ := min η (min (η ^ (2 : ℕ) / (8 : ℝ)) (κ ^ (4 : ℕ) * η / (8 : ℝ)));
          (0 : ℝ) < κ →
            ∀ (Ropen rforce Rβ : ℝ),
              let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
              (0 : ℝ) < rbase →
                closure (parabolicCylinder z₀.1 z₀.2 rbase) ⊆ spaceTimeSet Ω I →
                  let lambdaBase : ℝ := lambda q f z₀ rbase;
                  let lambdaSmall : ℝ := min Λ₀ (ηd / ((16 : ℝ) * C₂₉));
                  let a : ℝ := κ ^ ((3 : ℝ) - (5 : ℝ) / q);
                  ∀ (N : ℕ),
                    (∀ (b : ℕ), N ≤ b → a ^ b * lambdaBase < lambdaSmall) →
                      let r₄ : ℝ := κ ^ N * rbase;
                      (0 : ℝ) < r₄ → r₄ ≤ rbase → lambda q f z₀ r₄ ≤ lambdaSmall
    := by
  intro Ω I q u Du p f hsol z₀ C₂₇ C₂₈ κ η Λ₀ C₂₉ ηd hκ Ropen rforce Rβ rbase hrbase hbaseSub
    lambdaBase lambdaSmall a N hN r₄ hr₄ hr₄base
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

private lemma morreyDecay_hLdecay_4 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {C₂₇ : ℝ},
          let κ : ℝ := iterationKappa C₂₇;
          (0 : ℝ) < κ →
            κ ≤ (1 : ℝ) →
              ∀ Ropen > (0 : ℝ),
                ∀ rforce > (0 : ℝ),
                  ∀ Rβ > (0 : ℝ),
                    let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
                    ∀ (N : ℕ),
                      let r₄ : ℝ := κ ^ N * rbase;
                      (0 : ℝ) < r₄ →
                        closure (parabolicCylinder z₀.1 z₀.2 r₄) ⊆ spaceTimeSet Ω I →
                          let L : ℕ → ℝ := fun (n : ℕ) => lambda q f z₀ (κ ^ n * r₄);
                          ∀ (n : ℕ),
                            (0 : ℝ) ≤ L n ∧
                              L n ≤ κ ^ ((↑n : ℝ) * ((3 : ℝ) - (5 : ℝ) / q)) * L (0 : ℕ)
    := by
  intro Ω I q u Du p f hsol z₀ C₂₇ κ hκ hκone Ropen hRopen rforce hrforce Rβ hRβ rbase N r₄ hr₄
    hsub₄ L n
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

private lemma morreyDecay_hLsource_5 :
    ∀ {q : ℝ} {f : ParabolicPoint → Vec3} {z₀ : ParabolicPoint} {C₂₇ C₂₈ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      let η : ℝ := iterationEta C₂₇;
      let Λ₀ : ℝ := iterationLambda₀ C₂₇ C₂₈;
      let C₂₉ : ℝ := iterationC₂₉ C₂₇ C₂₈;
      let ηd : ℝ := min η (min (η ^ (2 : ℕ) / (8 : ℝ)) (κ ^ (4 : ℕ) * η / (8 : ℝ)));
      (0 : ℝ) < κ →
        κ ≤ (1 : ℝ) →
          (0 : ℝ) < ηd →
            (1 : ℝ) < (3 : ℝ) - (5 : ℝ) / q →
              (0 : ℝ) < C₂₉ →
                ∀ (Ropen rforce Rβ : ℝ),
                  let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
                  let lambdaSmall : ℝ := min Λ₀ (ηd / ((16 : ℝ) * C₂₉));
                  ∀ (N : ℕ),
                    let r₄ : ℝ := κ ^ N * rbase;
                    let L : ℕ → ℝ := fun (n : ℕ) => lambda q f z₀ (κ ^ n * r₄);
                    (∀ (n : ℕ),
                        (0 : ℝ) ≤ L n ∧
                          L n ≤ κ ^ ((↑n : ℝ) * ((3 : ℝ) - (5 : ℝ) / q)) * L (0 : ℕ)) →
                      L (0 : ℕ) ≤ lambdaSmall → ∀ (n : ℕ), C₂₉ * L n ≤ ηd / (16 : ℝ)
    := by
  intro q f z₀ C₂₇ C₂₈ κ η Λ₀ C₂₉ ηd hκ hκone hηd hσ hC₂₉ Ropen rforce Rβ rbase lambdaSmall N r₄ L
    hLdecay
    hL0small n
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

private lemma morreyDecay_hrec_6 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {z₀ : ParabolicPoint} {C₂₇ C₂₈ : ℝ},
      (0 : ℝ) < C₂₇ →
        (0 : ℝ) < C₂₈ →
          (∀ {z : ParabolicPoint} {ρ : ℝ},
              (0 : ℝ) < ρ →
                closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
                  theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
                      C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                              theta (iterationKappa C₂₇) u Du p z ρ +
                            C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                                (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
                              theta (iterationKappa C₂₇) u Du p z ρ +
                          C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                              theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                            lambda q f z ρ ^ (1 / 2 : ℝ) +
                        C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ ∧
                    (theta (iterationKappa C₂₇) u Du p z ρ ≤ (1 : ℝ) →
                      theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
                        C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                                theta (iterationKappa C₂₇) u Du p z ρ +
                              (2 : ℝ) * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                                theta (iterationKappa C₂₇) u Du p z ρ +
                            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                                theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                              lambda q f z ρ ^ (1 / 2 : ℝ) +
                          C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ)) →
            let κ : ℝ := iterationKappa C₂₇;
            let εStar : ℝ := iterationEpsilonStar C₂₇;
            let C₂₉ : ℝ := iterationC₂₉ C₂₇ C₂₈;
            (0 : ℝ) < κ →
              κ ≤ (1 : ℝ) →
                ∀ Ropen > (0 : ℝ),
                  ∀ rforce > (0 : ℝ),
                    ∀ Rβ > (0 : ℝ),
                      let rbase : ℝ :=
                        min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
                      ∀ (N : ℕ),
                        let r₄ : ℝ := κ ^ N * rbase;
                        (0 : ℝ) < r₄ →
                          r₄ ≤ rbase →
                            closure (parabolicCylinder z₀.1 z₀.2 r₄) ⊆ spaceTimeSet Ω I →
                              (∀ {r : ℝ}, (0 : ℝ) < r → r ≤ rbase → beta u Du z₀ r ≤ εStar) →
                                let Θ : ℕ → ℝ := fun (n : ℕ) => theta κ u Du p z₀ (κ ^ n * r₄);
                                let L : ℕ → ℝ := fun (n : ℕ) => lambda q f z₀ (κ ^ n * r₄);
                                (∀ (n : ℕ), (0 : ℝ) ≤ Θ n) →
                                  (∀ (n : ℕ),
                                      (0 : ℝ) ≤ L n ∧
                                        L n ≤
                                          κ ^ ((↑n : ℝ) * ((3 : ℝ) - (5 : ℝ) / q)) * L (0 : ℕ)) →
                                    ∀ (n : ℕ), Θ (n + (1 : ℕ)) ≤ (3 / 8 : ℝ) * Θ n + C₂₉ * L n
    := by
  intro Ω I q u Du p f z₀ C₂₇ C₂₈ hC₂₇ hC₂₈ hThetaDecay κ εStar C₂₉ hκ hκone Ropen hRopen rforce
    hrforce Rβ hRβ
    rbase N r₄ hr₄ hr₄base hsub₄ hβsmall Θ L hΘnonneg hLdecay n
  have hρ : 0 < κ ^ n * r₄ := by positivity
  have hρr : κ ^ n * r₄ ≤ r₄ := by
    simpa [mul_comm] using
      (mul_le_of_le_one_right hr₄.le (pow_le_one₀ hκ.le hκone) :
        r₄ * κ ^ n ≤ r₄)
  have hρsub :=
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

private lemma morreyDecay_hrect₀_7 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      ∀ (Ropen rforce Rβ : ℝ),
        let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
        ∀ (N : ℕ),
          let r₄ : ℝ := κ ^ N * rbase;
          ∀ (n₀ : ℕ),
            let R₀ : ℝ := κ ^ n₀ * r₄;
            (0 : ℝ) < R₀ →
              closure (parabolicCylinder z₀.1 z₀.2 R₀) ⊆ spaceTimeSet Ω I →
                euclideanClosedBall z₀.1 R₀ ×ˢ Icc (z₀.2 - R₀ ^ (2 : ℕ)) z₀.2 ⊆ spaceTimeSet Ω I
    := by
  intro Ω I z₀ C₂₇ κ Ropen rforce Rβ rbase N r₄ n₀ R₀ hR₀ hsub₀ y hy
  apply hsub₀
  rw [closure_parabolicCylinder hR₀]
  refine ⟨?_, hy.2⟩
  change vec3EuclideanNorm (y.1 - z₀.1) ≤ R₀
  have heq : CKN.vecEuclideanNorm (y.1 - z₀.1) =
      vec3EuclideanNorm (y.1 - z₀.1) := by
    simp [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot, pow_two]
  rw [← heq]
  exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR₀.le).1 hy.1

private lemma morreyDecay_hβϱ_8 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {C₂₇ : ℝ},
          let κ : ℝ := iterationKappa C₂₇;
          let η : ℝ := iterationEta C₂₇;
          (0 : ℝ) < η →
            ∀ (Ropen rforce Rβ : ℝ),
              let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
              ∀ (N : ℕ),
                let r₄ : ℝ := κ ^ N * rbase;
                ∀ (n₀ : ℕ),
                  let R₀ : ℝ := κ ^ n₀ * r₄;
                  closure (parabolicCylinder z₀.1 z₀.2 R₀) ⊆ spaceTimeSet Ω I →
                    theta κ u Du p z₀ R₀ ≤ η ^ (2 : ℕ) / (32 : ℝ) →
                      η ^ (2 : ℕ) ≤ η →
                        let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
                        (0 : ℝ) < ϱ →
                          ϱ < R₀ →
                            R₀ / ϱ = (7 / 5 : ℝ) →
                              beta u Du z₀ R₀ ≤ theta κ u Du p z₀ R₀ →
                                (0 : ℝ) ≤ theta κ u Du p z₀ R₀ → beta u Du z₀ ϱ < η / (4 : ℝ)
    := by
  intro Ω I q u Du p f hsol z₀ C₂₇ κ η hη Ropen rforce Rβ rbase N r₄ n₀ R₀ hsub₀ hθ₀ηsq hηsqle ϱ
    hϱ hϱR hratio hβ₀le hθ₀nonneg
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

private lemma morreyDecay_hδϱ_9 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {C₂₇ : ℝ},
          let κ : ℝ := iterationKappa C₂₇;
          let η : ℝ := iterationEta C₂₇;
          let ηd : ℝ := min η (min (η ^ (2 : ℕ) / (8 : ℝ)) (κ ^ (4 : ℕ) * η / (8 : ℝ)));
          (0 : ℝ) < κ →
            (0 : ℝ) < η →
              ∀ (Ropen rforce Rβ : ℝ),
                let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
                ∀ (N : ℕ),
                  let r₄ : ℝ := κ ^ N * rbase;
                  ∀ (n₀ : ℕ),
                    let R₀ : ℝ := κ ^ n₀ * r₄;
                    closure (parabolicCylinder z₀.1 z₀.2 R₀) ⊆ spaceTimeSet Ω I →
                      theta κ u Du p z₀ R₀ ≤ ηd / (4 : ℝ) →
                        ηd ≤ κ ^ (4 : ℕ) * η / (8 : ℝ) →
                          let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
                          (0 : ℝ) < ϱ →
                            ϱ < R₀ →
                              R₀ / ϱ = (7 / 5 : ℝ) →
                                delta p z₀ R₀ ^ (2 : ℕ) ≤ theta κ u Du p z₀ R₀ →
                                  (0 : ℝ) ≤ theta κ u Du p z₀ R₀ →
                                    delta p z₀ ϱ ^ (2 : ℕ) < κ ^ (4 : ℕ) * η / (4 : ℝ)
    := by
  intro Ω I q u Du p f hsol z₀ C₂₇ κ η ηd hκ hη Ropen rforce Rβ rbase N r₄ n₀ R₀ hsub₀ hθ₀
    hηd_delta ϱ hϱ hϱR hratio hδ₀le hθ₀nonneg
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

private lemma morreyDecay_htransfer_10 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      let η : ℝ := iterationEta C₂₇;
      (0 : ℝ) < κ →
        (0 : ℝ) < η →
          ∀ (Ropen rforce Rβ : ℝ),
            let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
            ∀ (N : ℕ),
              let r₄ : ℝ := κ ^ N * rbase;
              ∀ (n₀ : ℕ),
                let R₀ : ℝ := κ ^ n₀ * r₄;
                let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
                (∀ᶠ (z : ParabolicPoint) in 𝓝 z₀, beta u Du z ϱ < η / (4 : ℝ)) →
                  (∀ᶠ (z : ParabolicPoint) in 𝓝 z₀,
                      delta p z ϱ ^ (2 : ℕ) < κ ^ (4 : ℕ) * η / (4 : ℝ)) →
                    (∀ᶠ (z : ParabolicPoint) in 𝓝 z₀, alpha u z ϱ < η / (4 : ℝ)) →
                      κ ^ (-4 : ℝ) * κ ^ (4 : ℕ) = (1 : ℝ) →
                        ∀ᶠ (z : ParabolicPoint) in 𝓝 z₀, theta κ u Du p z ϱ ≤ η
    := by
  intro u Du p z₀ C₂₇ κ η hκ hη Ropen rforce Rβ rbase N r₄ n₀ R₀ ϱ hβeventϱ hδeventϱ hαevent' hκprod
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

private lemma morreyDecay_hzrhosub_11 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      (0 : ℝ) < κ →
        ∀ Ropen > (0 : ℝ),
          Metric.ball z₀ Ropen ⊆ spaceTimeSet Ω I →
            let Rbig : ℝ := Ropen / (4 : ℝ);
            ∀ rforce > (0 : ℝ),
              ∀ Rβ > (0 : ℝ),
                let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
                ∀ (N : ℕ),
                  let r₄ : ℝ := κ ^ N * rbase;
                  ∀ (n₀ : ℕ),
                    let R₀ : ℝ := κ ^ n₀ * r₄;
                    let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
                    (0 : ℝ) < ϱ →
                      ∀ (rE : ℝ),
                        let r₂ : ℝ :=
                          min (rE / (2 : ℝ))
                            (min (ϱ / (2 : ℝ)) (min (Ropen / (8 : ℝ)) (Rbig / (8 : ℝ))));
                        ϱ + r₂ < Ropen →
                          ∀ z ∈ Metric.ball z₀ r₂,
                            closure (parabolicCylinder z.1 z.2 ϱ) ⊆ spaceTimeSet Ω I
    := by
  intro Ω I z₀ C₂₇ κ hκ Ropen hRopen hRopenSub Rbig rforce hrforce Rβ hRβ rbase N r₄ n₀ R₀ ϱ hϱ rE
    r₂ hsumRopen
    z hz y hy
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

private lemma morreyDecay_hmoveSub_12 :
    ∀ {z₀ : ParabolicPoint} {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      (0 : ℝ) < κ →
        ∀ Ropen > (0 : ℝ),
          let Rbig : ℝ := Ropen / (4 : ℝ);
          (0 : ℝ) < Rbig →
            let zbig : ParabolicPoint := (z₀.1, z₀.2 + Rbig ^ (2 : ℕ));
            let Rbig' : ℝ := (2 : ℝ) * Rbig;
            ∀ rforce > (0 : ℝ),
              ∀ Rβ > (0 : ℝ),
                let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
                ∀ (N : ℕ),
                  let r₄ : ℝ := κ ^ N * rbase;
                  ∀ (n₀ : ℕ),
                    let R₀ : ℝ := κ ^ n₀ * r₄;
                    let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
                    (0 : ℝ) < ϱ →
                      ∀ rE > (0 : ℝ),
                        let r₂ : ℝ :=
                          min (rE / (2 : ℝ))
                            (min (ϱ / (2 : ℝ)) (min (Ropen / (8 : ℝ)) (Rbig / (8 : ℝ))));
                        (0 : ℝ) < r₂ →
                          ϱ + r₂ < Rbig →
                            ∀ z ∈ Metric.ball z₀ r₂,
                              parabolicCylinder z.1 z.2 ϱ ⊆ parabolicCylinder zbig.1 zbig.2 Rbig'
    := by
  intro z₀ C₂₇ κ hκ Ropen hRopen Rbig hRbig zbig Rbig' rforce hrforce Rβ hRβ rbase N r₄ n₀ R₀ ϱ hϱ
    rE hrE r₂ hr₂
    hsumRbig z hz y hy
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

private lemma morreyDecay_hlamz_13 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {C₂₇ C₂₈ : ℝ},
          let κ : ℝ := iterationKappa C₂₇;
          let Λ₀ : ℝ := iterationLambda₀ C₂₇ C₂₈;
          ∀ (Ropen : ℝ),
            let Rbig : ℝ := Ropen / (4 : ℝ);
            let zbig : ParabolicPoint := (z₀.1, z₀.2 + Rbig ^ (2 : ℕ));
            let Rbig' : ℝ := (2 : ℝ) * Rbig;
            ∫⁻ (w : ParabolicPoint) in parabolicCylinder zbig.1 zbig.2 Rbig',
                  ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q <
                ∞ →
              let Froot : ℝ :=
                (∫⁻ (w : ParabolicPoint) in parabolicCylinder zbig.1 zbig.2 Rbig',
                      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^
                  ((1 : ℝ) / q);
              ∀ rforce > (0 : ℝ),
                Metric.ball (0 : ℝ) rforce ∩ Ioi (0 : ℝ) ⊆
                    {x : ℝ | (fun (r : ℝ) => r ^ ((3 : ℝ) - (5 : ℝ) / q) * Froot < Λ₀) x} →
                  ∀ (Rβ : ℝ),
                    let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
                    ∀ (N : ℕ),
                      let r₄ : ℝ := κ ^ N * rbase;
                      ∀ (n₀ : ℕ),
                        let R₀ : ℝ := κ ^ n₀ * r₄;
                        (0 : ℝ) < R₀ →
                          let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
                          (0 : ℝ) < ϱ →
                            ∀ (rE : ℝ),
                              let r₂ : ℝ :=
                                min (rE / (2 : ℝ))
                                  (min (ϱ / (2 : ℝ)) (min (Ropen / (8 : ℝ)) (Rbig / (8 : ℝ))));
                              R₀ ≤ rbase →
                                (∀ z ∈ Metric.ball z₀ r₂,
                                    parabolicCylinder z.1 z.2 ϱ ⊆
                                      parabolicCylinder zbig.1 zbig.2 Rbig') →
                                  ∀ z ∈ Metric.ball z₀ r₂, lambda q f z ϱ ≤ Λ₀
    := by
  intro Ω I q u Du p f hsol z₀ C₂₇ C₂₈ κ Λ₀ Ropen Rbig zbig Rbig' hforceBig Froot rforce hrforce
    hforceBall Rβ
    rbase N r₄ n₀ R₀ hR₀ ϱ hϱ rE r₂ hR₀base hmoveSub z hz
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

private lemma morreyDecay_hσ_1 :
    ∀ {q : ℝ}, (5 / 2 : ℝ) < q → (1 : ℝ) < (3 : ℝ) - (5 : ℝ) / q
    := by
  intro q hq
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  have hfive : 5 / q < (2 : ℝ) := by
    apply (div_lt_iff₀ hqpos).2
    nlinarith only [hq]
  linarith only [hfive]

private lemma morreyDecay_hrbaseβ_2 :
    ∀ (Ropen rforce Rβ : ℝ),
      Rβ > (0 : ℝ) →
        let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
        rbase < Rβ
    := by
  intro Ropen rforce Rβ hRβ rbase
  dsimp [rbase]
  have hle₁ : min (Ropen / 8) (min (Rβ / 2) (rforce / 2)) ≤
      min (Rβ / 2) (rforce / 2) := min_le_right _ _
  have hle₂ : min (Rβ / 2) (rforce / 2) ≤ Rβ / 2 := min_le_left _ _
  linarith only [hle₁, hle₂, hRβ]

private lemma morreyDecay_hrbaseForce_3 :
    ∀ (Ropen rforce : ℝ),
      rforce > (0 : ℝ) →
        ∀ (Rβ : ℝ),
          let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
          rbase < rforce
    := by
  intro Ropen rforce hrforce Rβ rbase
  dsimp [rbase]
  have hle₁ : min (Ropen / 8) (min (Rβ / 2) (rforce / 2)) ≤
      min (Rβ / 2) (rforce / 2) := min_le_right _ _
  have hle₂ : min (Rβ / 2) (rforce / 2) ≤ rforce / 2 := min_le_right _ _
  linarith only [hle₁, hle₂, hrforce]

private lemma morreyDecay_hbaseSub_4 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} (Ropen : ℝ),
      Metric.ball z₀ Ropen ⊆ spaceTimeSet Ω I →
        ∀ (rforce Rβ : ℝ),
          let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
          (0 : ℝ) < rbase →
            rbase < Ropen → closure (parabolicCylinder z₀.1 z₀.2 rbase) ⊆ spaceTimeSet Ω I
    := by
  intro Ω I z₀ Ropen hRopenSub rforce Rβ rbase hrbase hrbaseR y hy
  have hyc := step2_closure_cylinder_subset_closedBall hrbase hy
  apply hRopenSub
  rw [Metric.mem_ball]
  change dist y (z₀.1, z₀.2) < Ropen
  exact lt_of_le_of_lt (Metric.mem_closedBall.mp hyc) hrbaseR

private lemma morreyDecay_hβsmall_5 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {z₀ : ParabolicPoint}
      {C₂₇ : ℝ},
      let εStar : ℝ := iterationEpsilonStar C₂₇;
      ∀ (Ropen rforce : ℝ) (U : Set ℝ),
        U ∩ Ioi (0 : ℝ) ⊆ {x : ℝ | (fun (r : ℝ) => beta u Du z₀ r < iterationEpsilonStar C₂₇) x} →
          ∀ (Rβ : ℝ),
            Metric.ball (0 : ℝ) Rβ ⊆ U →
              let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
              rbase < Rβ → ∀ {r : ℝ}, (0 : ℝ) < r → r ≤ rbase → beta u Du z₀ r ≤ εStar
    := by
  intro u Du z₀ C₂₇ εStar Ropen rforce U hUsub Rβ hRβsub rbase hrbaseβ r hr hrb
  apply le_of_lt
  apply hUsub
  exact ⟨hRβsub (by
    rw [Metric.mem_ball]
    simpa [Real.dist_eq, abs_of_pos hr] using lt_of_le_of_lt hrb hrbaseβ), hr⟩

private lemma morreyDecay_hαlim_6 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      let η : ℝ := iterationEta C₂₇;
      (0 : ℝ) < η →
        ∀ (Ropen rforce Rβ : ℝ),
          let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
          ∀ (N : ℕ),
            let r₄ : ℝ := κ ^ N * rbase;
            ∀ (n₀ : ℕ),
              let R₀ : ℝ := κ ^ n₀ * r₄;
              theta κ u Du p z₀ R₀ ≤ η ^ (2 : ℕ) / (32 : ℝ) →
                let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
                R₀ / ϱ = (7 / 5 : ℝ) →
                  (limsup (fun (z : ParabolicPoint) => alpha u z ϱ ^ (2 : ℕ)) (𝓝 z₀) ≤
                        R₀ / ϱ * alpha u z₀ R₀ ^ (2 : ℕ) ∧
                      Tendsto (fun (z : ParabolicPoint) => beta u Du z ϱ) (𝓝 z₀)
                          (𝓝 (beta u Du z₀ ϱ)) ∧
                        Tendsto (fun (z : ParabolicPoint) => delta p z ϱ) (𝓝 z₀)
                            (𝓝 (delta p z₀ ϱ)) ∧
                          IsBoundedUnder (fun (x1 x2 : ℝ) => x1 ≤ x2) (𝓝 z₀)
                            fun (z : ParabolicPoint) => alpha u z ϱ ^ (2 : ℕ)) →
                    alpha u z₀ R₀ ^ (2 : ℕ) ≤ theta κ u Du p z₀ R₀ →
                      limsup (fun (z : ParabolicPoint) => alpha u z ϱ ^ (2 : ℕ)) (𝓝 z₀) <
                        η ^ (2 : ℕ) / (16 : ℝ)
    := by
  intro u Du p z₀ C₂₇ κ η hη Ropen rforce Rβ rbase N r₄ n₀ R₀ hθ₀ηsq ϱ hratio husc hα₀sq
  have hfactor : (R₀ / ϱ) * alpha u z₀ R₀ ^ 2 ≤
      (7 / 5 : ℝ) * theta κ u Du p z₀ R₀ := by
    rw [hratio]
    exact mul_le_mul_of_nonneg_left hα₀sq (by norm_num)
  calc
    Filter.limsup (fun z : ParabolicPoint => alpha u z ϱ ^ 2) (𝓝 z₀) ≤
        (R₀ / ϱ) * alpha u z₀ R₀ ^ 2 := husc.1
    _ ≤ (7 / 5 : ℝ) * theta κ u Du p z₀ R₀ := hfactor
    _ < η ^ 2 / 16 := by nlinarith only [hθ₀ηsq, hη]

private lemma morreyDecay_hαevent'_7 :
    ∀ {u : ParabolicPoint → Vec3} {z₀ : ParabolicPoint} {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      let η : ℝ := iterationEta C₂₇;
      (0 : ℝ) < κ →
        (0 : ℝ) < η →
          ∀ Ropen > (0 : ℝ),
            ∀ rforce > (0 : ℝ),
              ∀ Rβ > (0 : ℝ),
                let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
                ∀ (N : ℕ),
                  let r₄ : ℝ := κ ^ N * rbase;
                  ∀ (n₀ : ℕ),
                    let R₀ : ℝ := κ ^ n₀ * r₄;
                    η ^ (2 : ℕ) ≤ η →
                      let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
                      (∀ᶠ (z : ParabolicPoint) in 𝓝 z₀,
                          alpha u z ϱ ^ (2 : ℕ) < η ^ (2 : ℕ) / (16 : ℝ)) →
                        ∀ᶠ (z : ParabolicPoint) in 𝓝 z₀, alpha u z ϱ < η / (4 : ℝ)
    := by
  intro u z₀ C₂₇ κ η hκ hη Ropen hRopen rforce hrforce Rβ hRβ rbase N r₄ n₀ R₀ hηsqle ϱ hαevent
  filter_upwards [hαevent] with z hz
  have hnonneg : 0 ≤ alpha u z ϱ := by
    unfold alpha
    positivity
  nlinarith only [hz, hnonneg, hη, hηsqle]

private lemma morreyDecay_hr₂ϱ_8 :
    ∀ {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      ∀ (Ropen : ℝ),
        let Rbig : ℝ := Ropen / (4 : ℝ);
        ∀ (rforce Rβ : ℝ),
          let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
          ∀ (N : ℕ),
            let r₄ : ℝ := κ ^ N * rbase;
            ∀ (n₀ : ℕ),
              let R₀ : ℝ := κ ^ n₀ * r₄;
              let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
              (0 : ℝ) < ϱ →
                ∀ (rE : ℝ),
                  let r₂ : ℝ :=
                    min (rE / (2 : ℝ)) (min (ϱ / (2 : ℝ)) (min (Ropen / (8 : ℝ)) (Rbig / (8 : ℝ))));
                  r₂ < ϱ
    := by
  intro C₂₇ κ Ropen Rbig rforce Rβ rbase N r₄ n₀ R₀ ϱ hϱ rE r₂
  dsimp [r₂]
  have hle₁ : min (rE / 2) (min (ϱ / 2) (min (Ropen / 8) (Rbig / 8))) ≤
      min (ϱ / 2) (min (Ropen / 8) (Rbig / 8)) := min_le_right _ _
  have hle₂ : min (ϱ / 2) (min (Ropen / 8) (Rbig / 8)) ≤ ϱ / 2 :=
    min_le_left _ _
  linarith only [hle₁, hle₂, hϱ]

private lemma morreyDecay_hr₂Ropen_9 :
    ∀ {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      ∀ (Ropen : ℝ),
        let Rbig : ℝ := Ropen / (4 : ℝ);
        ∀ (rforce Rβ : ℝ),
          let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
          ∀ (N : ℕ),
            let r₄ : ℝ := κ ^ N * rbase;
            ∀ (n₀ : ℕ),
              let R₀ : ℝ := κ ^ n₀ * r₄;
              let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
              ∀ (rE : ℝ),
                let r₂ : ℝ :=
                  min (rE / (2 : ℝ)) (min (ϱ / (2 : ℝ)) (min (Ropen / (8 : ℝ)) (Rbig / (8 : ℝ))));
                r₂ ≤ Ropen / (8 : ℝ)
    := by
  intro C₂₇ κ Ropen Rbig rforce Rβ rbase N r₄ n₀ R₀ ϱ rE r₂
  dsimp [r₂]
  exact ((min_le_right (rE / 2)
    (min (ϱ / 2) (min (Ropen / 8) (Rbig / 8)))).trans
    (min_le_right (ϱ / 2) (min (Ropen / 8) (Rbig / 8)))).trans
    (min_le_left (Ropen / 8) (Rbig / 8))

private lemma morreyDecay_hr₂Rbig_10 :
    ∀ {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      ∀ (Ropen : ℝ),
        let Rbig : ℝ := Ropen / (4 : ℝ);
        ∀ (rforce Rβ : ℝ),
          let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
          ∀ (N : ℕ),
            let r₄ : ℝ := κ ^ N * rbase;
            ∀ (n₀ : ℕ),
              let R₀ : ℝ := κ ^ n₀ * r₄;
              let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
              ∀ (rE : ℝ),
                let r₂ : ℝ :=
                  min (rE / (2 : ℝ)) (min (ϱ / (2 : ℝ)) (min (Ropen / (8 : ℝ)) (Rbig / (8 : ℝ))));
                r₂ ≤ Rbig / (8 : ℝ)
    := by
  intro C₂₇ κ Ropen Rbig rforce Rβ rbase N r₄ n₀ R₀ ϱ rE r₂
  dsimp [r₂]
  exact ((min_le_right (rE / 2)
    (min (ϱ / 2) (min (Ropen / 8) (Rbig / 8)))).trans
    (min_le_right (ϱ / 2) (min (Ropen / 8) (Rbig / 8)))).trans
    (min_le_right (Ropen / 8) (Rbig / 8))

private lemma morreyDecay_hpowTendsto_1 :
    ∀ {q : ℝ} {f : ParabolicPoint → Vec3} {z₀ : ParabolicPoint},
      (1 : ℝ) < (3 : ℝ) - (5 : ℝ) / q →
        ∀ (Ropen : ℝ),
          let Rbig : ℝ := Ropen / (4 : ℝ);
          let zbig : ParabolicPoint := (z₀.1, z₀.2 + Rbig ^ (2 : ℕ));
          let Rbig' : ℝ := (2 : ℝ) * Rbig;
          let Froot : ℝ :=
            (∫⁻ (w : ParabolicPoint) in parabolicCylinder zbig.1 zbig.2 Rbig',
                  ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^
              ((1 : ℝ) / q);
          Tendsto (fun (r : ℝ) => r ^ ((3 : ℝ) - (5 : ℝ) / q) * Froot) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))
    := by
  intro q f z₀ hσ Ropen Rbig zbig Rbig' Froot
  have hσpos : 0 < 3 - 5 / q := lt_trans (by norm_num) hσ
  have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa using (hid.rpow_const_nhds_zero hσpos).mul_const Froot

private lemma morreyDecay_hrbaseR_2 :
    ∀ Ropen > (0 : ℝ),
      ∀ (rforce Rβ : ℝ),
        let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
        rbase < Ropen
    := by
  intro Ropen hRopen rforce Rβ rbase
  dsimp [rbase]
  have hle : min (Ropen / 8) (min (Rβ / 2) (rforce / 2)) ≤ Ropen / 8 :=
    min_le_left _ _
  linarith only [hle, hRopen]

private lemma morreyDecay_hlambdaSmall_3 :
    ∀ {C₂₇ C₂₈ : ℝ},
      (0 : ℝ) < C₂₇ →
        (0 : ℝ) < C₂₈ →
          let κ : ℝ := iterationKappa C₂₇;
          let η : ℝ := iterationEta C₂₇;
          let Λ₀ : ℝ := iterationLambda₀ C₂₇ C₂₈;
          let C₂₉ : ℝ := iterationC₂₉ C₂₇ C₂₈;
          let ηd : ℝ := min η (min (η ^ (2 : ℕ) / (8 : ℝ)) (κ ^ (4 : ℕ) * η / (8 : ℝ)));
          (0 : ℝ) < κ →
            (0 : ℝ) < η →
              (0 : ℝ) < C₂₉ →
                let lambdaSmall : ℝ := min Λ₀ (ηd / ((16 : ℝ) * C₂₉));
                (0 : ℝ) < lambdaSmall
    := by
  intro C₂₇ C₂₈ hC₂₇ hC₂₈ κ η Λ₀ C₂₉ ηd hκ hη hC₂₉ lambdaSmall
  dsimp [lambdaSmall]
  exact lt_min (by dsimp [Λ₀]; exact iterationLambda₀_pos hC₂₇ hC₂₈)
    (by positivity)

private lemma morreyDecay_hr₄base_4 :
    ∀ {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      (0 : ℝ) < κ →
        κ ≤ (1 : ℝ) →
          ∀ (Ropen rforce Rβ : ℝ),
            let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
            (0 : ℝ) < rbase →
              ∀ (N : ℕ),
                let r₄ : ℝ := κ ^ N * rbase;
                r₄ ≤ rbase
    := by
  intro C₂₇ κ hκ hκone Ropen rforce Rβ rbase hrbase N r₄
  dsimp [r₄]
  simpa [mul_comm] using
    (mul_le_of_le_one_right hrbase.le (pow_le_one₀ hκ.le hκone) :
      rbase * κ ^ N ≤ rbase)

private lemma morreyDecay_hΘnonneg_5 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      (0 : ℝ) < κ →
        ∀ Ropen > (0 : ℝ),
          ∀ rforce > (0 : ℝ),
            ∀ Rβ > (0 : ℝ),
              let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
              ∀ (N : ℕ),
                let r₄ : ℝ := κ ^ N * rbase;
                let Θ : ℕ → ℝ := fun (n : ℕ) => theta κ u Du p z₀ (κ ^ n * r₄);
                ∀ (n : ℕ), (0 : ℝ) ≤ Θ n
    := by
  intro u Du p z₀ C₂₇ κ hκ Ropen hRopen rforce hrforce Rβ hRβ rbase N r₄ Θ n
  dsimp [Θ]
  unfold theta alpha beta delta
  positivity

private lemma morreyDecay_hR₀r₄_6 :
    ∀ {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      (0 : ℝ) < κ →
        κ ≤ (1 : ℝ) →
          ∀ (Ropen rforce Rβ : ℝ),
            let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
            ∀ (N : ℕ),
              let r₄ : ℝ := κ ^ N * rbase;
              (0 : ℝ) < r₄ →
                ∀ (n₀ : ℕ),
                  let R₀ : ℝ := κ ^ n₀ * r₄;
                  R₀ ≤ r₄
    := by
  intro C₂₇ κ hκ hκone Ropen rforce Rβ rbase N r₄ hr₄ n₀ R₀
  dsimp [R₀]
  simpa using (mul_le_mul_of_nonneg_right
    (pow_le_one₀ hκ.le hκone : κ ^ n₀ ≤ 1) hr₄.le)

private lemma morreyDecay_hθ₀ηsq_7 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      let η : ℝ := iterationEta C₂₇;
      let ηd : ℝ := min η (min (η ^ (2 : ℕ) / (8 : ℝ)) (κ ^ (4 : ℕ) * η / (8 : ℝ)));
      ∀ (Ropen rforce Rβ : ℝ),
        let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
        ∀ (N : ℕ),
          let r₄ : ℝ := κ ^ N * rbase;
          ∀ (n₀ : ℕ),
            let R₀ : ℝ := κ ^ n₀ * r₄;
            theta κ u Du p z₀ R₀ ≤ ηd / (4 : ℝ) →
              ηd ≤ η ^ (2 : ℕ) / (8 : ℝ) → theta κ u Du p z₀ R₀ ≤ η ^ (2 : ℕ) / (32 : ℝ)
    := by
  intro u Du p z₀ C₂₇ κ η ηd Ropen rforce Rβ rbase N r₄ n₀ R₀ hθ₀ hηd_sq
  calc
    theta κ u Du p z₀ R₀ ≤ ηd / 4 := hθ₀
    _ ≤ (η ^ 2 / 8) / 4 := div_le_div_of_nonneg_right hηd_sq (by norm_num)
    _ = η ^ 2 / 32 := by ring

private lemma morreyDecay_hα₀sq_8 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      let η : ℝ := iterationEta C₂₇;
      η ≤ (1 : ℝ) →
        ∀ (Ropen rforce Rβ : ℝ),
          let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
          ∀ (N : ℕ),
            let r₄ : ℝ := κ ^ N * rbase;
            ∀ (n₀ : ℕ),
              let R₀ : ℝ := κ ^ n₀ * r₄;
              theta κ u Du p z₀ R₀ ≤ η →
                (0 : ℝ) ≤ alpha u z₀ R₀ →
                  alpha u z₀ R₀ ≤ theta κ u Du p z₀ R₀ →
                    alpha u z₀ R₀ ^ (2 : ℕ) ≤ theta κ u Du p z₀ R₀
    := by
  intro u Du p z₀ C₂₇ κ η hηle Ropen rforce Rβ rbase N r₄ n₀ R₀ hθ₀η hα₀ hα₀le
  have hα₀one : alpha u z₀ R₀ ≤ 1 := hα₀le.trans (hθ₀η.trans hηle)
  have hsq : alpha u z₀ R₀ ^ 2 ≤ alpha u z₀ R₀ := by
    nlinarith only [hα₀, hα₀one]
  exact hsq.trans hα₀le

private lemma morreyDecay_hr₂E_9 :
    ∀ {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      ∀ (Ropen : ℝ),
        let Rbig : ℝ := Ropen / (4 : ℝ);
        ∀ (rforce Rβ : ℝ),
          let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
          ∀ (N : ℕ),
            let r₄ : ℝ := κ ^ N * rbase;
            ∀ (n₀ : ℕ),
              let R₀ : ℝ := κ ^ n₀ * r₄;
              let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
              ∀ rE > (0 : ℝ),
                let r₂ : ℝ :=
                  min (rE / (2 : ℝ)) (min (ϱ / (2 : ℝ)) (min (Ropen / (8 : ℝ)) (Rbig / (8 : ℝ))));
                r₂ < rE
    := by
  intro C₂₇ κ Ropen Rbig rforce Rβ rbase N r₄ n₀ R₀ ϱ rE hrE r₂
  dsimp [r₂]
  have hle₁ : min (rE / 2) (min (ϱ / 2) (min (Ropen / 8) (Rbig / 8))) ≤
      rE / 2 := min_le_left _ _
  linarith only [hle₁, hrE]

private lemma morreyDecay_hball₂_10 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {C₂₇ : ℝ},
      let κ : ℝ := iterationKappa C₂₇;
      ∀ Ropen > (0 : ℝ),
        Metric.ball z₀ Ropen ⊆ spaceTimeSet Ω I →
          let Rbig : ℝ := Ropen / (4 : ℝ);
          ∀ (rforce Rβ : ℝ),
            let rbase : ℝ := min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ)));
            ∀ (N : ℕ),
              let r₄ : ℝ := κ ^ N * rbase;
              ∀ (n₀ : ℕ),
                let R₀ : ℝ := κ ^ n₀ * r₄;
                let ϱ : ℝ := (5 / 7 : ℝ) * R₀;
                ∀ (rE : ℝ),
                  let r₂ : ℝ :=
                    min (rE / (2 : ℝ)) (min (ϱ / (2 : ℝ)) (min (Ropen / (8 : ℝ)) (Rbig / (8 : ℝ))));
                  (have r₂ : ℝ :=
                      min (rE / (2 : ℝ))
                        (min
                          ((5 / 7 : ℝ) *
                              (iterationKappa C₂₇ ^ n₀ *
                                (iterationKappa C₂₇ ^ N *
                                  min (Ropen / (8 : ℝ)) (min (Rβ / (2 : ℝ)) (rforce / (2 : ℝ))))) /
                            (2 : ℝ))
                          (min (Ropen / (8 : ℝ)) (Ropen / (4 : ℝ) / (8 : ℝ))));
                    r₂ ≤ Ropen / (8 : ℝ)) →
                    Metric.ball z₀ ((2 : ℝ) * r₂) ⊆ spaceTimeSet Ω I
    := by
  intro Ω I z₀ C₂₇ κ Ropen hRopen hRopenSub Rbig rforce Rβ rbase N r₄ n₀ R₀ ϱ rE r₂ hr₂Ropen y hy
  apply hRopenSub
  exact Metric.ball_subset_ball (by nlinarith only [hr₂Ropen, hRopen]) hy

private lemma morreyDecay_of_uniform_theta_bound
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {z₀ : ParabolicPoint} {κ K r₂ ϱ : ℝ}
    (hκ : 0 < κ) (hκone : κ ≤ 1) (hr₂ : 0 < r₂)
    (hball : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I) (hr₂ϱ : r₂ ≤ ϱ)
    (hbound : ∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r ≤ ϱ →
      theta κ u Du p z r ≤ K * r ^ (2 / 5 : ℝ)) :
    ∃ r₂ M : ℝ, 0 < r₂ ∧ 1 ≤ M ∧
      Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I ∧
      (∀ z, z ∈ Metric.ball z₀ r₂ → ∀ r : ℝ, 0 < r → r < r₂ →
        max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
          M * r ^ (2 / 5 : ℝ)) := by
  refine ⟨r₂, max 1 K, hr₂, le_max_left _ _, hball, ?_⟩
  intro z hz r hr hrr
  apply (max_components_le_theta hκ hκone (by unfold alpha; positivity)
    (by unfold beta; positivity)).trans
  exact (hbound z hz r hr ((le_of_lt hrr).trans hr₂ϱ)).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

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
  have hεStar : 0 < εStar := by
    dsimp [εStar]
    exact iterationEpsilonStar_pos hC₂₇
  have hσ := morreyDecay_hσ_1 hq
  have hC₂₉ : 0 < C₂₉ := by dsimp [C₂₉]; exact iterationC₂₉_pos hC₂₇ hC₂₈
  obtain ⟨Ropen, hRopen, hRopenSub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1).mem_nhds hz₀)
  let Rbig : ℝ := Ropen / 4
  have hRbig : 0 < Rbig := by dsimp [Rbig]; positivity
  let zbig : ParabolicPoint := (z₀.1, z₀.2 + Rbig ^ 2)
  let Rbig' : ℝ := 2 * Rbig
  have hRbig' : 0 < Rbig' := by dsimp [Rbig']; positivity
  have hbigSub := morreyDecay_hbigSub_1 Ropen hRopen hRopenSub hRbig'
  have hforceBig :=
    sws_force_integral_lt_top hsol hRbig' hbigSub
  let Froot : ℝ :=
    (∫⁻ w in parabolicCylinder zbig.1 zbig.2 Rbig',
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^ (1 / q : ℝ)
  have hpowTendsto := @morreyDecay_hpowTendsto_1 q f z₀ hσ Ropen
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
  have hβevent := morreyDecay_hβevent_2 hsol hq hεStar Ropen hRopen hRopenSub hquotEvent
  obtain ⟨U, hU, h0U, hUsub⟩ := mem_nhdsWithin.1 hβevent
  obtain ⟨Rβ, hRβ, hRβsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  let rbase : ℝ := min (Ropen / 8) (min (Rβ / 2) (rforce / 2))
  have hrbase : 0 < rbase := by
    dsimp [rbase]
    positivity
  have hrbaseR := @morreyDecay_hrbaseR_2 Ropen hRopen rforce Rβ
  have hrbaseβ := @morreyDecay_hrbaseβ_2 Ropen rforce Rβ hRβ
  have hbaseSub := morreyDecay_hbaseSub_4 Ropen hRopenSub rforce Rβ hrbase hrbaseR
  let lambdaBase := lambda q f z₀ rbase
  let lambdaSmall : ℝ := min Λ₀ (ηd / (16 * C₂₉))
  have hlambdaSmall := morreyDecay_hlambdaSmall_3 hC₂₇ hC₂₈ hκ hη hC₂₉
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
  have hr₄base := morreyDecay_hr₄base_4 hκ hκone Ropen rforce Rβ hrbase N
  have hsub₄ :=
    (closure_parabolicCylinder_mono hr₄.le hr₄base).trans hbaseSub
  have hβsmall := @morreyDecay_hβsmall_5 u Du z₀ C₂₇ Ropen rforce U hUsub Rβ hRβsub hrbaseβ
  have hlambda₄ : lambda q f z₀ r₄ ≤ lambdaSmall := by
    exact morreyDecay_hlambda₄_3 hsol hκ Ropen rforce Rβ hrbase
      hbaseSub N hN hr₄ hr₄base
  let Θ : ℕ → ℝ := fun n => theta κ u Du p z₀ (κ ^ n * r₄)
  let L : ℕ → ℝ := fun n => lambda q f z₀ (κ ^ n * r₄)
  have hΘnonneg := @morreyDecay_hΘnonneg_5 u Du p z₀ C₂₇ hκ Ropen hRopen rforce hrforce Rβ hRβ N
  have hLdecay := morreyDecay_hLdecay_4 hsol hκ hκone Ropen hRopen rforce hrforce Rβ hRβ N hr₄ hsub₄
  have hL0small : L 0 ≤ lambdaSmall := by
    simpa [L] using hlambda₄
  have hLsource := morreyDecay_hLsource_5 hκ hκone hηd hσ hC₂₉ Ropen rforce Rβ N hLdecay hL0small
  have hrec : ∀ n, Θ (n + 1) ≤ (3 / 8 : ℝ) * Θ n + C₂₉ * L n := by
    exact morreyDecay_hrec_6 hC₂₇ hC₂₈ hThetaDecay hκ hκone Ropen
      hRopen rforce hrforce Rβ hRβ N hr₄ hr₄base hsub₄ hβsmall hΘnonneg hLdecay
  obtain ⟨n₀, hn₀⟩ := exists_small_normalized hηd hrec hLsource
  let R₀ : ℝ := κ ^ n₀ * r₄
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    positivity
  have hR₀r₄ := morreyDecay_hR₀r₄_6 hκ hκone Ropen rforce Rβ N hr₄ n₀
  have hsub₀ :=
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
  have hθ₀ηsq := morreyDecay_hθ₀ηsq_7 Ropen rforce Rβ N n₀ hθ₀ hηd_sq
  have hηsqle : η ^ 2 ≤ η := by
    nlinarith only [hη, hηle]
  have hrect₀ := morreyDecay_hrect₀_7 Ropen rforce Rβ N n₀ hR₀ hsub₀
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
  have hcomp₀ := max_components_le_theta (p := p) hκ hκone hα₀ hβ₀
  have hα₀le : alpha u z₀ R₀ ≤ theta κ u Du p z₀ R₀ :=
    (le_max_left _ _ |>.trans (le_max_left _ _)).trans hcomp₀
  have hβ₀le : beta u Du z₀ R₀ ≤ theta κ u Du p z₀ R₀ :=
    (le_max_right _ _ |>.trans (le_max_left _ _)).trans hcomp₀
  have hδ₀le : delta p z₀ R₀ ^ 2 ≤ theta κ u Du p z₀ R₀ :=
    (le_max_right _ _).trans hcomp₀
  have hα₀sq := morreyDecay_hα₀sq_8 hηle Ropen rforce Rβ N n₀ hθ₀η hα₀ hα₀le
  have hαlim := morreyDecay_hαlim_6 hη Ropen rforce Rβ N n₀ hθ₀ηsq hratio husc hα₀sq
  have hθ₀nonneg : 0 ≤ theta κ u Du p z₀ R₀ := by
    unfold theta
    positivity
  have hβϱ := morreyDecay_hβϱ_8 hsol hη Ropen rforce Rβ N n₀ hsub₀ hθ₀ηsq
    hηsqle hϱ hϱR hratio hβ₀le hθ₀nonneg
  have hδϱ := morreyDecay_hδϱ_9 hsol hκ hη Ropen rforce Rβ N n₀ hsub₀ hθ₀
    hηd_delta hϱ hϱR hratio hδ₀le hθ₀nonneg
  have hαevent : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      alpha u z ϱ ^ 2 < η ^ 2 / 16 := by
    exact eventually_lt_of_limsup_lt hαlim husc.2.2.2
  have hβeventϱ :=
    husc.2.1.eventually (eventually_lt_nhds hβϱ)
  have hδeventϱ : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      delta p z ϱ ^ 2 < κ ^ 4 * η / 4 := by
    exact (husc.2.2.1.pow 2).eventually (eventually_lt_nhds hδϱ)
  have hαevent' := morreyDecay_hαevent'_7 hκ hη Ropen hRopen rforce hrforce Rβ hRβ N n₀
    hηsqle hαevent
  have hκprod : κ ^ (-4 : ℝ) * κ ^ (4 : ℕ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hκ]
    norm_num
  have htransfer := morreyDecay_htransfer_10 hκ hη Ropen rforce Rβ N n₀ hβeventϱ
    hδeventϱ hαevent' hκprod
  obtain ⟨rE, hrE, hballE⟩ := Metric.mem_nhds_iff.mp htransfer
  let r₂ : ℝ := min (rE / 2) (min (ϱ / 2) (min (Ropen / 8) (Rbig / 8)))
  have hr₂ : 0 < r₂ := by
    dsimp [r₂]
    positivity
  have hr₂E := @morreyDecay_hr₂E_9 C₂₇ Ropen rforce Rβ N n₀ rE hrE
  have hr₂ϱ := morreyDecay_hr₂ϱ_8 Ropen rforce Rβ N n₀ hϱ rE
  have hr₂Ropen := @morreyDecay_hr₂Ropen_9 C₂₇ Ropen rforce Rβ N n₀ rE
  have hr₂Rbig : r₂ ≤ Rbig / 8 := by
    exact morreyDecay_hr₂Rbig_10 Ropen rforce Rβ N n₀ rE
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
  have hball₂ := morreyDecay_hball₂_10 Ropen hRopen hRopenSub rforce Rβ N n₀ rE hr₂Ropen
  have hzrhosub := morreyDecay_hzrhosub_11 hκ Ropen hRopen hRopenSub rforce hrforce Rβ
    hRβ N n₀ hϱ rE hsumRopen
  have hmoveSub := @morreyDecay_hmoveSub_12 z₀ C₂₇ hκ Ropen hRopen hRbig rforce hrforce Rβ hRβ N
    n₀ hϱ rE hrE hr₂ hsumRbig
  have hlamz := morreyDecay_hlamz_13 hsol Ropen hforceBig rforce
    hrforce hforceBall Rβ N n₀ hR₀ hϱ rE hR₀base hmoveSub
  apply morreyDecay_of_uniform_theta_bound (K := κ ^ (-4 / 3 - ε) * η * ϱ ^ (-ε))
    hκ hκone hr₂ hball₂ (le_of_lt hr₂ϱ)
  intro z hz r hr hrϱ
  have hθz := hballE (Metric.ball_subset_ball (le_of_lt hr₂E) hz)
  have hiterz := iteration_of_thetaDecay (C₂₇ := C₂₇) (C₂₈ := C₂₈)
    hsol hC₂₇ hC₂₈ hϱ (hzrhosub z hz) hθz (hlamz z hz) hThetaDecay
  simpa [κ, η, ε, iterationEpsilon] using hiterz.2 r hr hrϱ

end CKN
