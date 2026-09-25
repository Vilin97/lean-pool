/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvariance
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantities
public import LeanPool.CaffarelliKohnNirenberg.Core.TheoremA.Start
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedSources
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.WideInitialMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.StartSmallness
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyDecayAux

/-!
# Small-data decay for Theorem A

Steps 1 and 2 of the proof of `thm:A`. `theoremA_morrey_decay_of_inputs` is
Step 1: the start lemma `lem:thmA-start` at every centre of the one-sided
cylinder `Q_{3/4}`, followed by the scale iteration `prop:iteration` at the
fixed radius `r₅ = κ/4`, giving the decay `eq:thmA-morrey` with the constant
`M = κ^{-4/3-ε} η r₅^{-ε}` and `ε = 2/5`. The manuscript calls `M` absolute;
what is proved and used here is that it is fixed before the domain and the
solution.

`theoremA_initial_morrey_wide_of_inputs` is Step 2: the one-sided Morrey
transfer, giving the three memberships of `eq:step2-morrey` on the cylinder
of radius `11/16`. The manuscript states them on `Q₂^♯` of radius `5/8`; the
larger radius is proved because the bootstrap round consumes the outer
cylinder and returns the inner one, and the transfer argument needs only
that the radius is below `3/4`. The Hölder conclusion of `thm:A` is not
here: it additionally requires the causal localization and source estimates
of Step 3, through the top time face.
-/

@[expose] public section

section

/-!
# Scaling

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-! The rescaling identities used to move a centre to the unit cylinder. -/

/-- The parabolic rescaling preserves suitability and transports all four
scale quantities to the original centre at the dilated radius. -/
theorem thmA_scaling_data
    (κ μ : ℝ) (hμ : 0 < μ)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (r : ℝ) (hr : 0 < r) :
    IsSuitableWeakSolutionIntegrable (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) q
        (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
        (rescalePressure μ z₀ p) (rescaleForce μ z₀ f) ∧
      theta κ (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
          (rescalePressure μ z₀ p) ((0 : Vec3), (0 : ℝ)) r =
        theta κ u Du p z₀ (μ * r) ∧
      beta (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
          ((0 : Vec3), (0 : ℝ)) r = beta u Du z₀ (μ * r) ∧
      gamma (rescaleVelocity μ z₀ u) ((0 : Vec3), (0 : ℝ)) r =
        gamma u z₀ (μ * r) ∧
      delta (rescalePressure μ z₀ p) ((0 : Vec3), (0 : ℝ)) r =
        delta p z₀ (μ * r) ∧
      lambda q (rescaleForce μ z₀ f) ((0 : Vec3), (0 : ℝ)) r =
        lambda q f z₀ (μ * r) := by
  have hres := isSuitableWeakSolutionIntegrable_rescale hsol z₀ hμ
  refine ⟨hres, ?_, ?_, ?_, ?_, ?_⟩
  · exact theta_rescale_of_sws hsol κ μ hμ z₀ r hr
  · exact beta_rescale μ hμ z₀ u Du r
  · exact gamma_rescale μ hμ z₀ u r hr
  · exact delta_rescale μ hμ z₀ p r hr
  · exact lambda_rescale q μ
      (lt_trans (by norm_num : (0 : ℝ) < 5 / 2) hsol.2.2.2.1) hμ z₀ f r hr

/-- A start estimate at the rescaled unit centre transports to the original
centre.  The constants occur before the solution data, as in the paper. -/
theorem thmA_scaling_step
    (κ μ η Λ₀ : ℝ) (hμ : 0 < μ)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (hstart :
      theta κ (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
          (rescalePressure μ z₀ p) ((0 : Vec3), (0 : ℝ)) (1 / 4) ≤ η ∧
      lambda q (rescaleForce μ z₀ f) ((0 : Vec3), (0 : ℝ)) (1 / 4) ≤ Λ₀) :
    theta κ u Du p z₀ (μ / 4) ≤ η ∧
      lambda q f z₀ (μ / 4) ≤ Λ₀ := by
  have hμ4 : 0 < (1 / 4 : ℝ) := by norm_num
  have htheta := (thmA_scaling_data κ μ hμ hsol z₀ (1 / 4) hμ4).2.1
  have hlambda := (thmA_scaling_data κ μ hμ hsol z₀ (1 / 4) hμ4).2.2.2.2.2
  have harg : μ * (1 / 4 : ℝ) = μ / 4 := by ring
  rw [harg] at htheta hlambda
  exact ⟨htheta.symm ▸ hstart.1, hlambda.symm ▸ hstart.2⟩

end CKN
end

end

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame


noncomputable section

namespace CKN

private theorem theoremA_quarter_subset_unit
    {z : ParabolicPoint}
    (hz : z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0) :
    parabolicCylinder z.1 z.2 (1 / 4) ⊆ parabolicCylinder 0 0 1 := by
  intro w hw
  rcases hz with ⟨hzx, hzt⟩
  rcases hw with ⟨hwx, hwt⟩
  refine ⟨?_, ?_⟩
  · change vec3EuclideanNorm (w.1 - 0) < 1
    rw [sub_zero]
    have htriangle : vec3EuclideanNorm w.1 ≤
        vec3EuclideanNorm (w.1 - z.1) + vec3EuclideanNorm z.1 := by
      simpa only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub, sub_add_cancel] using
        (norm_add_le (WithLp.toLp 2 (w.1 - z.1)) (WithLp.toLp 2 z.1))
    have hwx' : vec3EuclideanNorm (w.1 - z.1) < 1 / 4 := hwx
    have hzx' : vec3EuclideanNorm z.1 < 3 / 4 := by
      simpa only [mem_vec3Ball, sub_zero] using hzx
    linarith only [htriangle, hwx', hzx']
  · refine ⟨?_, hwt.2.trans hzt.2⟩
    have ht := hwt.1
    have hzlow := hzt.1
    norm_num at ht ⊢
    linarith only [ht, hzlow]

/-- A positive uniform small-data threshold yields the decay portion of
`thm:A`. It is chosen before the domain and the solution. No smallness
inequality for numerical parameters is left as a hypothesis. -/
theorem theoremA_morrey_decay_of_inputs
    (q C₂₅ C₂₆ C₂₇ C₂₈ C₃₂ : ℝ)
    (hq : 5 / 2 < q) (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆) (hC₃₂ : 0 ≤ C₃₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (_ : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (_ : closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I)
    (_ : (∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (_ : ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      alpha u z r + beta u Du z r ≤
        C₂₅ * ((r / ρ) * gamma u z ρ +
          (r / ρ) ^ (-1 : ℝ) * gamma u z ρ ^ (3 / 2 : ℝ) +
          (r / ρ) ^ (-1 : ℝ) * delta p z ρ * gamma u z ρ ^ (1 / 2 : ℝ)) +
        C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u z ρ ^ (1 / 2 : ℝ) *
          lambda q f z ρ ^ (1 / 2 : ℝ))
    (_ : ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      pressureD p z r ≤ C₃₂ *
        ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ +
          (r / ρ) * pressureD p z ρ +
          (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ)))
    (_ : ∀ {w : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder w.1 w.2 ρ) ⊆ spaceTimeSet Ω I →
      theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
        C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * theta (iterationKappa C₂₇) u Du p w ρ +
          C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
            (beta u Du w ρ ^ (1 / 2 : ℝ) + beta u Du w ρ) *
              theta (iterationKappa C₂₇) u Du p w ρ +
          C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
            theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
              lambda q f w ρ ^ (1 / 2 : ℝ) +
          C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ ∧
      (theta (iterationKappa C₂₇) u Du p w ρ ≤ 1 →
        theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
          C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ +
            2 * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                theta (iterationKappa C₂₇) u Du p w ρ +
            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                lambda q f w ρ ^ (1 / 2 : ℝ) +
            C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ)),
    ∀ z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0,
      ∀ r : ℝ, 0 < r → r ≤ iterationKappa C₂₇ / 4 →
        max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ (2 : ℕ)) ≤
          (iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) *
            iterationEta C₂₇ * (iterationKappa C₂₇ / 4) ^ (-iterationEpsilon)) *
              r ^ (2 / 5 : ℝ)
 := by
  obtain ⟨ε₀, hε₀, hstartAll⟩ := thmA_start_of_inputs
    q C₂₅ C₂₆ C₂₇ C₂₈ C₃₂ hq hC₂₇ hC₂₈ hC₂₅ hC₂₆ hC₃₂
  refine ⟨ε₀, hε₀, ?_⟩
  intro Ω I u Du p f hsol hQ₁ hthmA hCaccGamma hLin34 hThetaDecay
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hκhalf := iterationKappa_le_half C₂₇
  have hκone : iterationKappa C₂₇ ≤ 1 := by linarith only [hκhalf]
  have hstart := hstartAll hsol hQ₁ hthmA hCaccGamma hLin34
  intro z hz r hr hrr
  have hstartAtZ := hstart z hz
  have hscaledStartData := thmA_scaling_data (iterationKappa C₂₇)
    (iterationKappa C₂₇) hκ hsol z (1 / 4) (by norm_num)
  have hκquarter : iterationKappa C₂₇ * (1 / 4 : ℝ) =
      iterationKappa C₂₇ / 4 := by ring
  have hnormalizedStart :
      theta (iterationKappa C₂₇)
          (rescaleVelocity (iterationKappa C₂₇) z u)
          (rescaleGradient (iterationKappa C₂₇) z Du)
          (rescalePressure (iterationKappa C₂₇) z p)
          ((0 : Vec3), (0 : ℝ)) (1 / 4) ≤ iterationEta C₂₇ ∧
        lambda q (rescaleForce (iterationKappa C₂₇) z f)
          ((0 : Vec3), (0 : ℝ)) (1 / 4) ≤ iterationLambda₀ C₂₇ C₂₈ := by
    constructor
    · rw [hscaledStartData.2.1, hκquarter]
      exact hstartAtZ.1
    · rw [hscaledStartData.2.2.2.2.2, hκquarter]
      exact hstartAtZ.2
  have hstartByScaling := thmA_scaling_step
    (iterationKappa C₂₇) (iterationKappa C₂₇)
    (iterationEta C₂₇) (iterationLambda₀ C₂₇ C₂₈) hκ hsol z hnormalizedStart
  have hr₅ : 0 < iterationKappa C₂₇ / 4 := div_pos hκ (by norm_num)
  have hquarter : closure (parabolicCylinder z.1 z.2 (1 / 4)) ⊆
      spaceTimeSet Ω I := (closure_mono (theoremA_quarter_subset_unit hz)).trans hQ₁
  have hclosure : closure (parabolicCylinder z.1 z.2 (iterationKappa C₂₇ / 4)) ⊆
      spaceTimeSet Ω I :=
    (closure_parabolicCylinder_mono hr₅.le
      (by linarith only [hκone])).trans hquarter
  have hdecay := (iteration_of_thetaDecay hsol hC₂₇ hC₂₈ hr₅ hclosure
    hstartByScaling.1 hstartByScaling.2 hThetaDecay).2 r hr hrr
  have hcomponents := MorreyDecayAux.max_components_le_theta (u := u) (Du := Du) (p := p)
    (z := z) (r := r) hκ hκone (by unfold alpha; positivity) (by unfold beta; positivity)
  exact hcomponents.trans (by simpa only [iterationEpsilon_eq] using hdecay)

/-- The small-data start, iteration, and one-sided cylinder transfer give
uniform initial Morrey bounds for velocity, gradient, and pressure on the cylinder
of radius eleven sixteenths. The constants and positive threshold precede every solution. -/
theorem theoremA_initial_morrey_wide_of_inputs
    (q C₂₅ C₂₆ C₂₇ C₂₈ C₃₂ : ℝ)
    (hq : 5 / 2 < q) (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆) (hC₃₂ : 0 ≤ C₃₂) :
    let M := iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) *
      iterationEta C₂₇ * (iterationKappa C₂₇ / 4) ^ (-iterationEpsilon);
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N : ℕ,
    ∀ {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (_ : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (_ : closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I)
    (_ : (∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (_ : ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      alpha u z r + beta u Du z r ≤
        C₂₅ * ((r / ρ) * gamma u z ρ +
          (r / ρ) ^ (-1 : ℝ) * gamma u z ρ ^ (3 / 2 : ℝ) +
          (r / ρ) ^ (-1 : ℝ) * delta p z ρ * gamma u z ρ ^ (1 / 2 : ℝ)) +
        C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u z ρ ^ (1 / 2 : ℝ) *
          lambda q f z ρ ^ (1 / 2 : ℝ))
    (_ : ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      pressureD p z r ≤ C₃₂ *
        ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ +
          (r / ρ) * pressureD p z ρ +
          (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ)))
    (_ : ∀ {w : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder w.1 w.2 ρ) ⊆ spaceTimeSet Ω I →
      theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
        C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * theta (iterationKappa C₂₇) u Du p w ρ +
          C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
            (beta u Du w ρ ^ (1 / 2 : ℝ) + beta u Du w ρ) *
              theta (iterationKappa C₂₇) u Du p w ρ +
          C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
            theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
              lambda q f w ρ ^ (1 / 2 : ℝ) +
          C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ ∧
      (theta (iterationKappa C₂₇) u Du p w ρ ≤ 1 →
        theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
          C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ +
            2 * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                theta (iterationKappa C₂₇) u Du p w ρ +
            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                lambda q f w ρ ^ (1 / 2 : ℝ) +
            C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ)),
    (∀ i : Fin 3, morreyNorm 3 (25 / 3 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => u z i)) ≤
        oneSidedVelocityMorreyBound M (iterationKappa C₂₇ / 4) ε₀) ∧
    (∀ i j : Fin 3, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => Du z i j)) ≤
        oneSidedGradientMorreyBound M (iterationKappa C₂₇ / 4) N) ∧
    morreyNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator p) ≤
        oneSidedPressureMorreyBound M (iterationKappa C₂₇ / 4) ε₀ := by
  dsimp only
  obtain ⟨ε₀, hε₀, hroute⟩ := theoremA_morrey_decay_of_inputs
    q C₂₅ C₂₆ C₂₇ C₂₈ C₃₂ hq hC₂₇ hC₂₈ hC₂₅ hC₂₆ hC₃₂
  let M := iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) *
      iterationEta C₂₇ * (iterationKappa C₂₇ / 4) ^ (-iterationEpsilon)
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hη : 0 < iterationEta C₂₇ := iterationEta_pos hC₂₇
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hr₀ : 0 < iterationKappa C₂₇ / 4 := by positivity
  have hrquarter : iterationKappa C₂₇ / 4 ≤ 1 / 4 := by
    linarith only [iterationKappa_le_half C₂₇]
  obtain ⟨N, hwideAll⟩ := wide_initial_morrey_of_decay M
    (iterationKappa C₂₇ / 4) ε₀ hM hr₀ hrquarter
  refine ⟨ε₀, hε₀, N, ?_⟩
  intro Ω I u Du p f hsol hQ₁ hdata hCaccGamma hLin34 hThetaDecay
  have hdec : ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ iterationKappa C₂₇ / 4 →
        max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
          M * r ^ (2 / 5 : ℝ) := by
    have hd := hroute hsol hQ₁ hdata hCaccGamma hLin34 hThetaDecay
    intro z hz r hr hrr
    have hz' : z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0 := by
      refine ⟨hz.1, ?_, hz.2.2⟩
      have hlow := hz.2.1
      norm_num at hlow
      exact hlow
    exact hd z hz' r hr hrr
  exact hwideAll hsol hQ₁ hdata hdec


end CKN
