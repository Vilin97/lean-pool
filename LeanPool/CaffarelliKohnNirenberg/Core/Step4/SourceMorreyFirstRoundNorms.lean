/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyFirstRoundSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradientPackage

/-!
# Source norms of the first velocity-improvement round

The first round of `prop:bootstrap` starts from a velocity in
`M^{3,25/3}` and a gradient in `M^{2,25/8}` on a parabolic ball, and the
pressure gradient of `eq:local-equation` is already known in `M^{6/5,25/11}`
there.  The exponents of the heat slot are the paper's
`1/κ₂ = 1/τ + 1/τ₃ = 3/25 + 8/25 = 11/25`, so the localized source
`localizedGradientSourceG` lies in `M^{6/5,25/11}`.

The derivative slot `localizedGradientSourceH` is a bounded multiple of the
velocity itself, so its integrability exponent stays at `3`: it is estimated
in `M^{3,25/6}` directly, by lowering only the Morrey exponent from `25/3`.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3
open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

private lemma first_round_norm_neg {P θ : ℝ} (g : ParabolicPoint → ℝ) :
    morreyNorm P θ (fun z => -g z) = morreyNorm P θ g := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]

private lemma first_round_norm_sub_le {P θ : ℝ} (hP : 1 ≤ P)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) :
    morreyNorm P θ (fun z => f z - g z) ≤
      morreyNorm P θ f + morreyNorm P θ g := by
  have h := morrey_norm_add_le (τ := θ) hP hf hg.neg
  change morreyNorm P θ (fun z => f z + -g z) ≤
    morreyNorm P θ f + morreyNorm P θ (fun z => -g z) at h
  rw [first_round_norm_neg] at h
  simpa only [sub_eq_add_neg] using h

private lemma first_round_gradient_source_morrey_hUBle_1 :
    ∀ {u : ParabolicPoint → Vec3} {Ω' : Set Vec3} {J : Set ℝ} (z₀ : ParabolicPoint) (R : ℝ),
      let B : Set ParabolicPoint := Metric.ball z₀ R;
      let S : Set ParabolicPoint := spaceTimeSet Ω' J;
      ∀ (i : Fin 3),
        Morrey.morreyNorm 3 (25 / 3) (B.indicator (S.indicator fun z => u z i)) ≤
          Morrey.morreyNorm 3 (25 / 3) (B.indicator fun z => u z i)
    := by
  intro u Ω' J z₀ R B S i
  refine morreyNorm_mono (by norm_num) ?_
  intro z
  by_cases hzB : z ∈ B
  · rw [indicator_of_mem hzB]
    by_cases hzS : z ∈ S
    · rw [indicator_of_mem hzS, indicator_of_mem hzB]
    · rw [indicator_of_notMem hzS, abs_zero]
      simpa only [abs_zero] using abs_nonneg (B.indicator (fun z => u z i) z)
  · rw [indicator_of_notMem hzB]
    simpa only [abs_zero] using abs_nonneg (B.indicator (fun z => u z i) z)

private lemma first_round_gradient_source_morrey_hDBle_2 :
    ∀ {Du : ParabolicPoint → Fin 3 → Vec3} {Ω' : Set Vec3} {J : Set ℝ} (z₀ : ParabolicPoint)
      (R : ℝ),
      let B : Set ParabolicPoint := Metric.ball z₀ R;
      let S : Set ParabolicPoint := spaceTimeSet Ω' J;
      ∀ (i j : Fin 3),
        Morrey.morreyNorm 2 (25 / 8) (B.indicator (S.indicator fun z => Du z i j)) ≤
          Morrey.morreyNorm 2 (25 / 8) (B.indicator fun z => Du z i j)
    := by
  intro Du Ω' J z₀ R B S i j
  refine morreyNorm_mono (by norm_num) ?_
  intro z
  by_cases hzB : z ∈ B
  · rw [indicator_of_mem hzB]
    by_cases hzS : z ∈ S
    · rw [indicator_of_mem hzS, indicator_of_mem hzB]
    · rw [indicator_of_notMem hzS, abs_zero]
      simpa only [abs_zero] using
        abs_nonneg (B.indicator (fun z => Du z i j) z)
  · rw [indicator_of_notMem hzB]
    simpa only [abs_zero] using
      abs_nonneg (B.indicator (fun z => Du z i j) z)

private lemma first_round_gradient_source_morrey_hlapAE_3 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → ℝ},
      let φp : ParabolicPoint → ℝ := φ;
      Membership.mem (γ := Set (Vec3 × ℝ → ℝ)) (spaceTimeTestFunction Ω I) φp →
        AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
          (fun (z : ParabolicPoint) => spatialLaplacian (fun x => φ (x, z.2)) z.1) volume
    := by
  intro Ω I φ φp hφ
  change AEMeasurable (fun z : ParabolicPoint =>
    ∑ j, spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z) volume
  have h0 : AEMeasurable
      (fun z : ParabolicPoint => spatialSecondPartial φ 0 0 z) volume :=
    ((spatialSecondPartial_contDiff_full hφ.1 0 0).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have h1 : AEMeasurable
      (fun z : ParabolicPoint => spatialSecondPartial φ 1 1 z) volume :=
    ((spatialSecondPartial_contDiff_full hφ.1 1 1).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have h2 : AEMeasurable
      (fun z : ParabolicPoint => spatialSecondPartial φ 2 2 z) volume :=
    ((spatialSecondPartial_contDiff_full hφ.1 2 2).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable
  simpa [Fin.sum_univ_succ, Pi.add_def] using h0.add (h1.add h2)

private lemma first_round_gradient_source_morrey_hconvAE_4 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {φ : Vec3 × ℝ → ℝ}
      {Ω' : Set Vec3} {J : Set ℝ},
      let S : Set ParabolicPoint := spaceTimeSet Ω' J;
      let φp : ParabolicPoint → ℝ := φ;
      MeasurableSet S →
        (∀ z ∉ S, φp z = 0) →
          (∀ (i : Fin 3),
              AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace) (fun z => u z i)
                (Measure.restrict volume S)) →
            (∀ (i j : Fin 3),
                AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace) (fun z => Du z i j)
                  (Measure.restrict volume S)) →
              AEMeasurable (_m := MeasureSpace.toMeasurableSpace) φp volume →
                ∀ (i : Fin 3),
                  AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                    (fun (z : ParabolicPoint) => φp z * Core.Step3.localizedConvection u Du z i)
                    volume
    := by
  intro u Du φ Ω' J S φp hSmeas hφzeroS hucomp hDucomp hφAE i
  have hc : AEMeasurable (fun z : ParabolicPoint => ∑ j, u z j * Du z i j)
      (volume.restrict S) := by
    have h0 : AEMeasurable (fun z : ParabolicPoint => u z 0 * Du z i 0)
        (volume.restrict S) := (hucomp 0).mul (hDucomp i 0)
    have h1 : AEMeasurable (fun z : ParabolicPoint => u z 1 * Du z i 1)
        (volume.restrict S) := (hucomp 1).mul (hDucomp i 1)
    have h2 : AEMeasurable (fun z : ParabolicPoint => u z 2 * Du z i 2)
        (volume.restrict S) := (hucomp 2).mul (hDucomp i 2)
    simpa [Fin.sum_univ_succ, Pi.add_def] using h0.add (h1.add h2)
  have h := aemeasurable_mul_of_restrict_of_zero_outside hSmeas hφAE hc
    (fun z hz => hφzeroS z hz)
  simpa only [localizedConvection] using h

private lemma first_round_gradient_source_morrey_hconvN_5 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {φ : Vec3 × ℝ → ℝ}
      {Ω' : Set Vec3} {J : Set ℝ} (z₀ : ParabolicPoint) (R : ℝ),
      let B : Set ParabolicPoint := Metric.ball z₀ R;
      let S : Set ParabolicPoint := spaceTimeSet Ω' J;
      let φp : ParabolicPoint → ℝ := φ;
      ∀ (C : ℝ),
        0 < C →
          (∀ z ∉ B, φp z = 0) →
            (∀ (z : ParabolicPoint), |φp z| ≤ C) →
              (∀ (i : Fin 3),
                  AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                    (B.indicator (S.indicator fun z => u z i)) volume) →
                (∀ (i j : Fin 3),
                    AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                      (B.indicator (S.indicator fun z => Du z i j)) volume) →
                  (∀ (i : Fin 3),
                      Morrey.morreyNorm 3 (25 / 3) (B.indicator (S.indicator fun z => u z i)) <
                        ∞) →
                    (∀ (i j : Fin 3),
                        Morrey.morreyNorm 2 (25 / 8)
                            (B.indicator (S.indicator fun z => Du z i j)) <
                          ∞) →
                      (∀ (i : Fin 3),
                          Eq (α := ParabolicPoint → ℝ)
                            (fun z => φp z * Core.Step3.localizedConvection u Du z i) fun z =>
                            φp z *
                              ∑ j : Fin 3,
                                HMul.hMul (α := ℝ) (B.indicator (S.indicator fun w => u w j) z)
                                  (B.indicator (S.indicator fun w => Du w i j) z)) →
                        ∀ (i : Fin 3),
                          (Morrey.morreyNorm (6 / 5) (25 / 11) fun z =>
                              φp z * Core.Step3.localizedConvection u Du z i) <
                            ∞
    := by
  intro u Du φ Ω' J z₀ R B S φp C hC hφzero hvalue hUBoxAE hDuBoxAE hUB hDB hconvEq i
  rw [hconvEq i]
  have hprod (j : Fin 3) : morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (fun z => B.indicator (S.indicator (fun w => u w j)) z *
        B.indicator (S.indicator (fun w => Du w i j)) z) < ∞ :=
    (source_product_morrey_bound (P := (6 / 5 : ℝ))
      (P₁ := 3) (P₂ := 2) (θ := 25 / 11) (θ₁ := 25 / 3) (θ₂ := 25 / 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hUBoxAE j) (hDuBoxAE i j) (hUB j) (hDB i j)).1
  have htermAE (j : Fin 3) : AEMeasurable
      (fun z => B.indicator (S.indicator (fun w => u w j)) z *
        B.indicator (S.indicator (fun w => Du w i j)) z) volume :=
    (hUBoxAE j).mul (hDuBoxAE i j)
  have h12 : morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (fun z => B.indicator (S.indicator (fun w => u w 1)) z *
          B.indicator (S.indicator (fun w => Du w i 1)) z +
        B.indicator (S.indicator (fun w => u w 2)) z *
          B.indicator (S.indicator (fun w => Du w i 2)) z) < ∞ :=
    (morrey_norm_add_le (P := (6 / 5 : ℝ)) (τ := 25 / 11)
      (by norm_num) (htermAE 1) (htermAE 2)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hprod 1, hprod 2⟩)
  have hall : morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (fun z => ∑ j, B.indicator (S.indicator (fun w => u w j)) z *
        B.indicator (S.indicator (fun w => Du w i j)) z) < ∞ := by
    have hfinite := (morrey_norm_add_le (P := (6 / 5 : ℝ)) (τ := 25 / 11)
      (by norm_num) (htermAE 0) ((htermAE 1).add (htermAE 2))).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hprod 0, h12⟩)
    simpa [Fin.sum_univ_succ, add_assoc] using hfinite
  have hsum' : morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (B.indicator (fun z => ∑ j,
        B.indicator (S.indicator (fun w => u w j)) z *
          B.indicator (S.indicator (fun w => Du w i j)) z)) < ∞ := by
    have heq : B.indicator (fun z => ∑ j,
        B.indicator (S.indicator (fun w => u w j)) z *
          B.indicator (S.indicator (fun w => Du w i j)) z) =
        (fun z => ∑ j, B.indicator (S.indicator (fun w => u w j)) z *
          B.indicator (S.indicator (fun w => Du w i j)) z) := by
      funext z
      by_cases hz : z ∈ B
      · simp only [indicator_of_mem hz]
      · simp only [indicator_of_notMem hz, zero_mul, Finset.sum_const_zero]
    rw [heq]
    exact hall
  exact (morrey_norm_mul_le_indicator (6 / 5) (25 / 11) C (by norm_num)
    hC.le B φp
    (fun z => ∑ j, B.indicator (S.indicator (fun w => u w j)) z *
      B.indicator (S.indicator (fun w => Du w i j)) z)
    hvalue (fun z hz => hφzero z hz)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum')

private lemma first_round_gradient_source_morrey_hforceN_6 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ},
          localBox Ω I Ω' J →
            ∀ (z₀ : ParabolicPoint) (R : ℝ),
              0 < R →
                5 / 2 < q →
                  let B : Set ParabolicPoint := Metric.ball z₀ R;
                  let φp : ParabolicPoint → ℝ := φ;
                  Membership.mem (γ := Set (Vec3 × ℝ → ℝ)) (spaceTimeTestFunction Ω I) φp →
                    @tsupport (Vec3 × ℝ) ℝ _ instTopologicalSpaceProd φp ⊆ Ω' ×ˢ J →
                      φp = φ →
                        (∀ z ∉ B, φp z = 0) →
                          B ⊆ parabolicCylinder z₀.1 (z₀.2 + R ^ 2) (2 * R) →
                            (∀ (i : Fin 3),
                                AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                                  (fun (z : ParabolicPoint) => φp z * f z i) volume) →
                              ∀ (i : Fin 3),
                                (Morrey.morreyNorm (6 / 5) (25 / 11) fun z => φp z * f z i) < ∞
    := by
  intro Ω I q u Du p f hsol φ Ω' J hbox z₀ R hR hq B φp hφ hφbox hφpdef hφzero hballC hforceAE i
  have hbase : morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => φp z * f z i) < ∞ := by
    simpa only [hφpdef] using
      localized_gradient_force_morrey_of_sws hsol hφ hbox hφbox i
  exact morreyNorm_lt_top_of_lower_exponents (P := (6 / 5 : ℝ))
    (P₀ := (6 / 5 : ℝ)) (θ := 25 / 11) (θ₀ := min q (25 / 9 : ℝ)) (B := B)
    (z₀ := (z₀.1, z₀.2 + R ^ 2)) (R := 2 * R)
    (by norm_num) (le_refl _)
    (le_min (by linarith only [hq]) (by norm_num))
    (by norm_num)
    (le_min (by linarith only [hq]) (by norm_num))
    (by positivity) hballC (hforceAE i)
    (fun z hz => by simp only [hφzero z hz, zero_mul]) hbase

private lemma first_round_gradient_source_morrey_hGnorm_7 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {f : ParabolicPoint → Vec3}
      {φ : Vec3 × ℝ → ℝ} {Dp : ParabolicPoint → Vec3},
      let φp : ParabolicPoint → ℝ := φ;
      (∀ (i : Fin 3),
          AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
            (fun (z : ParabolicPoint) => timePartial φ z * u z i) volume) →
        (∀ (i : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (z : ParabolicPoint) => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i)
              volume) →
          (∀ (i : Fin 3),
              AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                (fun (z : ParabolicPoint) => φp z * Core.Step3.localizedConvection u Du z i)
                volume) →
            (∀ (i : Fin 3),
                AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                  (fun (z : ParabolicPoint) => φp z * f z i) volume) →
              (∀ (i : Fin 3),
                  AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                    (fun (z : ParabolicPoint) => φp z * Dp z i) volume) →
                (∀ (i : Fin 3),
                    (Morrey.morreyNorm (6 / 5) (25 / 11) fun z => timePartial φ z * u z i) < ∞) →
                  (∀ (i : Fin 3),
                      (Morrey.morreyNorm (6 / 5) (25 / 11) fun z =>
                          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) <
                        ∞) →
                    (∀ (i : Fin 3),
                        (Morrey.morreyNorm (6 / 5) (25 / 11) fun z =>
                            φp z * Core.Step3.localizedConvection u Du z i) <
                          ∞) →
                      (∀ (i : Fin 3),
                          (Morrey.morreyNorm (6 / 5) (25 / 11) fun z => φp z * f z i) < ∞) →
                        (∀ (i : Fin 3),
                            (Morrey.morreyNorm (6 / 5) (25 / 11) fun z => φp z * Dp z i) < ∞) →
                          ∀ (i : Fin 3),
                            (Morrey.morreyNorm (6 / 5) (25 / 11) fun z =>
                                Core.Step4.localizedGradientSourceG φ u Du f Dp z i) <
                              ∞
    := by
  intro u Du f φ Dp φp htimeMulAE hlapMulAE hconvAE hforceAE hDpAE' htimeN hlapN hconvN hforceN
    hDpFin i
  have h12ae : AEMeasurable (fun z => timePartial φ z * u z i +
      spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) volume :=
    (htimeMulAE i).add (hlapMulAE i)
  have h12 : morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (fun z => timePartial φ z * u z i +
        spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) < ∞ :=
    (morrey_norm_add_le (P := (6 / 5 : ℝ)) (τ := 25 / 11)
      (by norm_num) (htimeMulAE i) (hlapMulAE i)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨htimeN i, hlapN i⟩)
  have h123ae : AEMeasurable (fun z =>
      (timePartial φ z * u z i +
        spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
        φp z * localizedConvection u Du z i) volume :=
    h12ae.sub (hconvAE i)
  have h123 : morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (fun z => (timePartial φ z * u z i +
        spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
        φp z * localizedConvection u Du z i) < ∞ :=
    (first_round_norm_sub_le (by norm_num) h12ae (hconvAE i)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨h12, hconvN i⟩)
  have h1234ae : AEMeasurable (fun z =>
      ((timePartial φ z * u z i +
        spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
        φp z * localizedConvection u Du z i) + φp z * f z i) volume :=
    h123ae.add (hforceAE i)
  have h1234 : morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (fun z => ((timePartial φ z * u z i +
        spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
        φp z * localizedConvection u Du z i) + φp z * f z i) < ∞ :=
    (morrey_norm_add_le (P := (6 / 5 : ℝ)) (τ := 25 / 11)
      (by norm_num) h123ae (hforceAE i)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨h123, hforceN i⟩)
  have hGle := (first_round_norm_sub_le (P := (6 / 5 : ℝ))
      (θ := 25 / 11) (by norm_num) h1234ae (hDpAE' i)).trans_lt
    (ENNReal.add_lt_top.mpr ⟨h1234, hDpFin i⟩)
  simpa [localizedGradientSourceG, localizedEquationG, localizedConvection,
    sub_eq_add_neg] using hGle

private lemma first_round_gradient_source_morrey_hHnorm_8 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      (z₀ : ParabolicPoint) (R : ℝ),
      let B : Set ParabolicPoint := Metric.ball z₀ R;
      let S : Set ParabolicPoint := spaceTimeSet Ω' J;
      ∀ (C : ℝ),
        0 < C →
          (∀ (j : Fin 3), ∀ z ∉ B, spatialPartial φ j z = 0) →
            (∀ (j : Fin 3) (z : ParabolicPoint), |spatialPartial φ j z| ≤ C) →
              (∀ (i : Fin 3),
                  Morrey.morreyNorm 3 (25 / 6) (B.indicator (S.indicator fun z => u z i)) < ∞) →
                (∀ (j i : Fin 3),
                    Eq (α := ParabolicPoint → ℝ)
                      (fun z => Core.Step4.localizedGradientSourceH φ u j z i) fun z =>
                      -2 * spatialPartial φ j z * S.indicator (fun w => u w i) z) →
                  ∀ (j i : Fin 3),
                    (Morrey.morreyNorm 3 (25 / 6) fun z =>
                        Core.Step4.localizedGradientSourceH φ u j z i) <
                      ∞
    := by
  intro u φ Ω' J z₀ R B S C hC hspzero hsp hUsix hHtarget j i
  rw [hHtarget j i]
  refine (morrey_norm_mul_le_indicator 3 (25 / 6) (2 * C) (by norm_num)
    (by positivity) B (fun z => -2 * spatialPartial φ j z)
    (S.indicator (fun w => u w i)) (fun z => ?_)
    (fun z hz => by simp only [hspzero j z hz, mul_zero])).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hUsix i))
  calc
    |(-2 : ℝ) * spatialPartial φ j z| = 2 * |spatialPartial φ j z| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * C := mul_le_mul_of_nonneg_left (hsp j z) (by norm_num)

private lemma first_round_gradient_source_morrey_hnotphi_1 :
    ∀ {φ : Vec3 × ℝ → ℝ} (z₀ : ParabolicPoint) (R : ℝ),
      let B : Set ParabolicPoint := Metric.ball z₀ R;
      let φp : ParabolicPoint → ℝ := φ;
      @tsupport (Vec3 × ℝ) ℝ _ instTopologicalSpaceProd φp ⊆ ⇑parabolicHomeomorph.symm ⁻¹' B → ∀ z
        ∉ B, (z.1, z.2) ∉ tsupport φ
    := by
  intro φ z₀ R B φp hφcarrier z hz hm
  apply hz
  have hm' := hφcarrier hm
  change parabolicHomeomorph.symm (z.1, z.2) ∈ Metric.ball z₀ R at hm'
  change z ∈ Metric.ball z₀ R
  rw [show z = (z.1, z.2) from rfl]
  simpa only [parabolicHomeomorph_symm_apply] using hm'

private lemma first_round_gradient_source_morrey_hlapzero_2 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → ℝ} (z₀ : ParabolicPoint) (R : ℝ),
      let B : Set ParabolicPoint := Metric.ball z₀ R;
      let φp : ParabolicPoint → ℝ := φ;
      Membership.mem (γ := Set (Vec3 × ℝ → ℝ)) (spaceTimeTestFunction Ω I) φp →
        (∀ z ∉ B, (z.1, z.2) ∉ tsupport φ) →
          ∀ z ∉ B, spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0
    := by
  intro Ω I φ z₀ R B φp hφ hnotphi z hz
  change (∑ j : Fin 3, spatialSecondPartial
    (show ParabolicPoint → ℝ from φ) j j z) = 0
  refine Finset.sum_eq_zero ?_
  intro j _
  exact spatialSecondPartial_zero_of_not_mem_tsupport_public hφ.1
    (hnotphi z hz) j j

private lemma first_round_gradient_source_morrey_hlapzeroS_3 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ},
      let S : Set ParabolicPoint := spaceTimeSet Ω' J;
      let φp : ParabolicPoint → ℝ := φ;
      Membership.mem (γ := Set (Vec3 × ℝ → ℝ)) (spaceTimeTestFunction Ω I) φp →
        (∀ z ∉ S, (z.1, z.2) ∉ tsupport φ) →
          ∀ z ∉ S, spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0
    := by
  intro Ω I φ Ω' J S φp hφ hnotphiS z hz
  change (∑ j : Fin 3, spatialSecondPartial
    (show ParabolicPoint → ℝ from φ) j j z) = 0
  exact Finset.sum_eq_zero (fun j _ =>
    spatialSecondPartial_zero_of_not_mem_tsupport_public hφ.1
      (hnotphiS z hz) j j)

private lemma first_round_gradient_source_morrey_htimeN_4 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      (z₀ : ParabolicPoint) (R : ℝ),
      let B : Set ParabolicPoint := Metric.ball z₀ R;
      let S : Set ParabolicPoint := spaceTimeSet Ω' J;
      ∀ (C : ℝ),
        0 < C →
          (∀ z ∉ B, timePartial φ z = 0) →
            (∀ (z : ParabolicPoint), |timePartial φ z| ≤ C) →
              (∀ (i : Fin 3),
                  Morrey.morreyNorm (6 / 5) (25 / 11) (B.indicator (S.indicator fun z => u z i)) <
                    ∞) →
                (∀ (i : Fin 3),
                    Eq (α := ParabolicPoint → ℝ) (fun z => timePartial φ z * u z i) fun z =>
                      timePartial φ z * S.indicator (fun w => u w i) z) →
                  ∀ (i : Fin 3),
                    (Morrey.morreyNorm (6 / 5) (25 / 11) fun z => timePartial φ z * u z i) < ∞
    := by
  intro u φ Ω' J z₀ R B S C hC htimezero htime hUmix htimeEq i
  rw [htimeEq i]
  exact (morrey_norm_mul_le_indicator (6 / 5) (25 / 11) C (by norm_num) hC.le
    B (fun z => timePartial φ z) (S.indicator (fun w => u w i)) htime
    (fun z hz => htimezero z hz)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hUmix i))

private lemma first_round_gradient_source_morrey_hlapN_5 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      (z₀ : ParabolicPoint) (R : ℝ),
      let B : Set ParabolicPoint := Metric.ball z₀ R;
      let S : Set ParabolicPoint := spaceTimeSet Ω' J;
      ∀ (C : ℝ),
        0 < C →
          (∀ z ∉ B, spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0) →
            (∀ (z : ParabolicPoint), |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C) →
              (∀ (i : Fin 3),
                  Morrey.morreyNorm (6 / 5) (25 / 11) (B.indicator (S.indicator fun z => u z i)) <
                    ∞) →
                (∀ (i : Fin 3),
                    Eq (α := ParabolicPoint → ℝ)
                      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) fun z =>
                      spatialLaplacian (fun x => φ (x, z.2)) z.1 *
                        S.indicator (fun w => u w i) z) →
                  ∀ (i : Fin 3),
                    (Morrey.morreyNorm (6 / 5) (25 / 11) fun z =>
                        spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) <
                      ∞
    := by
  intro u φ Ω' J z₀ R B S C hC hlapzero hlap hUmix hlapEq i
  rw [hlapEq i]
  exact (morrey_norm_mul_le_indicator (6 / 5) (25 / 11) C (by norm_num) hC.le
    B (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1)
    (S.indicator (fun w => u w i)) hlap
    (fun z hz => hlapzero z hz)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hUmix i))

private lemma first_round_gradient_source_morrey_hconvEq_6 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {φ : Vec3 × ℝ → ℝ}
      {Ω' : Set Vec3} {J : Set ℝ} (z₀ : ParabolicPoint) (R : ℝ),
      let B : Set ParabolicPoint := Metric.ball z₀ R;
      let S : Set ParabolicPoint := spaceTimeSet Ω' J;
      let φp : ParabolicPoint → ℝ := φ;
      (∀ z ∉ B, φp z = 0) →
        (∀ z ∉ S, φp z = 0) →
          ∀ (i : Fin 3),
            Eq (α := ParabolicPoint → ℝ) (fun z => φp z * Core.Step3.localizedConvection u Du z i)
              fun z =>
              φp z *
                ∑ j : Fin 3,
                  HMul.hMul (α := ℝ) (B.indicator (S.indicator fun w => u w j) z)
                    (B.indicator (S.indicator fun w => Du w i j) z)
    := by
  intro u Du φ Ω' J z₀ R B S φp hφzero hφzeroS i
  funext z
  by_cases hzB : z ∈ B
  · simp only [indicator_of_mem hzB]
    by_cases hzS : z ∈ S
    · simp only [indicator_of_mem hzS, localizedConvection]
    · simp only [indicator_of_notMem hzS, hφzeroS z hzS, zero_mul]
  · simp only [indicator_of_notMem hzB, hφzero z hzB, zero_mul]

private lemma first_round_gradient_source_morrey_hDpFin_7 :
    ∀ {φ : Vec3 × ℝ → ℝ} (z₀ : ParabolicPoint) (R : ℝ) {Dp : ParabolicPoint → Vec3},
      let B : Set ParabolicPoint := Metric.ball z₀ R;
      morreyVecMem (6 / 5) (25 / 11) B Dp →
        let φp : ParabolicPoint → ℝ := φ;
        ∀ (C : ℝ),
          0 < C →
            (∀ z ∉ B, φp z = 0) →
              (∀ (z : ParabolicPoint), |φp z| ≤ C) →
                ∀ (i : Fin 3), (Morrey.morreyNorm (6 / 5) (25 / 11) fun z => φp z * Dp z i) < ∞
    := by
  intro φ z₀ R Dp B hDpN φp C hC hφzero hvalue i
  have hN : morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (B.indicator (fun z => Dp z i)) < ∞ :=
    (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans_lt
      (hDpN i)
  exact (morrey_norm_mul_le_indicator (6 / 5) (25 / 11) C (by norm_num)
    hC.le B φp (fun z => Dp z i) hvalue hφzero).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN)

private lemma first_round_gradient_source_morrey_hHtarget_8 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ},
      let S : Set ParabolicPoint := spaceTimeSet Ω' J;
      (∀ (j : Fin 3), ∀ z ∉ S, spatialPartial φ j z = 0) →
        ∀ (j i : Fin 3),
          Eq (α := ParabolicPoint → ℝ) (fun z => Core.Step4.localizedGradientSourceH φ u j z i)
            fun z => -2 * spatialPartial φ j z * S.indicator (fun w => u w i) z
    := by
  intro u φ Ω' J S hspzeroS j i
  funext z
  by_cases hzS : z ∈ S
  · simp only [indicator_of_mem hzS, localizedGradientSourceH,
      localizedEquationH, Pi.smul_apply, smul_eq_mul]
  · simp only [indicator_of_notMem hzS, hspzeroS j z hzS,
      localizedGradientSourceH, localizedEquationH, Pi.smul_apply,
      smul_eq_mul, mul_zero, zero_mul]

/-- The two source slots of `eq:local-equation` at the first-round exponents.
The heat slot lands in `M^{6/5,25/11}` and the derivative slot in
`M^{3,25/6}`, both on the arbitrary parabolic ball carrying the cutoff. -/
theorem first_round_gradient_source_morrey_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    (z₀ : ParabolicPoint) (R : ℝ) (hR : 0 < R)
    (hφcarrier : tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ R)
    (hU : morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u)
    (hDuNorm : ∀ i, morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z₀ R) (fun z => Du z i))
    {Dp : ParabolicPoint → Vec3}
    (hDpAE : ∀ i, AEMeasurable (fun z => Dp z i)
      (volume.restrict (Metric.ball z₀ R)))
    (hDpN : morreyVecMem (6 / 5 : ℝ) (25 / 11 : ℝ) (Metric.ball z₀ R) Dp) :
    (∀ i, morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (fun z => localizedGradientSourceG φ u Du f Dp z i) < ∞) ∧
    (∀ j i, morreyNorm 3 (25 / 6 : ℝ)
      (fun z => localizedGradientSourceH φ u j z i) < ∞) := by
  have hq : 5 / 2 < q := hsol.2.2.2.1
  set B : Set ParabolicPoint := Metric.ball z₀ R with hBdef
  set S : Set ParabolicPoint := spaceTimeSet Ω' J with hSdef
  set φp : ParabolicPoint → ℝ := φ with hφpdef
  have hBmeas : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hSmeas : MeasurableSet S := hbox.1.measurableSet.prod
    hbox.2.2.2.1.measurableSet
  obtain ⟨C, hC, hcoeff⟩ := exists_cutoff_derivative_bound hφ.1 hφ.2.1
  -- vanishing outside the carrier ball
  have hnotphi (z : ParabolicPoint) (hz : z ∉ B) := @first_round_gradient_source_morrey_hnotphi_1
    φ z₀ R hφcarrier z hz
  have hφzero (z : ParabolicPoint) (hz : z ∉ B) : φp z = 0 := by
    change φ (z.1, z.2) = 0
    exact image_eq_zero_of_notMem_tsupport (hnotphi z hz)
  have htimezero (z : ParabolicPoint) (hz : z ∉ B) : timePartial φ z = 0 :=
    timePartial_zero_of_not_mem_tsupport_public hφ.1 (hnotphi z hz)
  have hspzero (j : Fin 3) (z : ParabolicPoint) (hz : z ∉ B) :
      spatialPartial φ j z = 0 :=
    spatialPartial_zero_of_not_mem_tsupport_public hφ.1 (hnotphi z hz) j
  have hlapzero (z : ParabolicPoint) (hz : z ∉ B) :=
    @first_round_gradient_source_morrey_hlapzero_2 Ω I φ z₀ R hφ hnotphi z hz
  -- vanishing outside the local product box
  have hnotphiS (z : ParabolicPoint) (hz : z ∉ S) :
      (z.1, z.2) ∉ tsupport φ := by
    intro hm
    exact hz (hφbox hm)
  have hφzeroS (z : ParabolicPoint) (hz : z ∉ S) : φp z = 0 := by
    change φ (z.1, z.2) = 0
    exact image_eq_zero_of_notMem_tsupport (hnotphiS z hz)
  have htimezeroS (z : ParabolicPoint) (hz : z ∉ S) : timePartial φ z = 0 :=
    timePartial_zero_of_not_mem_tsupport_public hφ.1 (hnotphiS z hz)
  have hspzeroS (j : Fin 3) (z : ParabolicPoint) (hz : z ∉ S) :
      spatialPartial φ j z = 0 :=
    spatialPartial_zero_of_not_mem_tsupport_public hφ.1 (hnotphiS z hz) j
  have hlapzeroS (z : ParabolicPoint) (hz : z ∉ S) :=
    @first_round_gradient_source_morrey_hlapzeroS_3 Ω I φ Ω' J hφ hnotphiS z hz
  -- uniform coefficient bounds
  have hvalue (z : ParabolicPoint) : |φp z| ≤ C := (hcoeff (z.1, z.2)).1
  have htime (z : ParabolicPoint) : |timePartial φ z| ≤ C := by
    simpa only [timePartial] using (hcoeff (z.1, z.2)).2.1
  have hlap (z : ParabolicPoint) :
      |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C :=
    (hcoeff (z.1, z.2)).2.2.2
  have hsp (j : Fin 3) (z : ParabolicPoint) :
      |spatialPartial φ j z| ≤ C := by
    change |spatialPartial φ j (z.1, z.2)| ≤ C
    exact (hcoeff (z.1, z.2)).2.2.1 j
  -- solution data on the local box
  obtain ⟨hu, hDuData, hpmeas, hfmeas, hEssSup, henergy, hp, hf, hgrad⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  have hucomp (i : Fin 3) : AEMeasurable (fun z => u z i)
      (volume.restrict S) :=
    aemeasurable_pi_iff.mp hu.aemeasurable i
  have hDucomp (i j : Fin 3) : AEMeasurable (fun z => Du z i j)
      (volume.restrict S) :=
    aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hDuData.aemeasurable i) j
  have hfcomp (i : Fin 3) : AEMeasurable (fun z => f z i)
      (volume.restrict S) :=
    aemeasurable_pi_iff.mp hfmeas.aemeasurable i
  have huBox (i : Fin 3) : AEMeasurable
      (S.indicator (fun z => u z i)) volume :=
    (aemeasurable_indicator_iff hSmeas).mpr (hucomp i)
  have hDuBox (i j : Fin 3) : AEMeasurable
      (S.indicator (fun z => Du z i j)) volume :=
    (aemeasurable_indicator_iff hSmeas).mpr (hDucomp i j)
  have hUBoxAE (i : Fin 3) : AEMeasurable
      (B.indicator (S.indicator (fun z => u z i))) volume :=
    (huBox i).indicator hBmeas
  have hDuBoxAE (i j : Fin 3) : AEMeasurable
      (B.indicator (S.indicator (fun z => Du z i j))) volume :=
    (hDuBox i j).indicator hBmeas
  -- Morrey data transferred to the doubly truncated fields
  have hUbase (i : Fin 3) : morreyNorm 3 (25 / 3 : ℝ)
      (B.indicator (fun z => u z i)) < ∞ :=
    (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans_lt (hU i)
  have hDbase (i j : Fin 3) : morreyNorm 2 (25 / 8 : ℝ)
      (B.indicator (fun z => Du z i j)) < ∞ :=
    (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans_lt
      (hDuNorm i j)
  have hUBle (i : Fin 3) := @first_round_gradient_source_morrey_hUBle_1 u Ω' J z₀ R i
  have hDBle (i j : Fin 3) := @first_round_gradient_source_morrey_hDBle_2 Du Ω' J z₀ R i j
  have hUB (i : Fin 3) : morreyNorm 3 (25 / 3 : ℝ)
      (B.indicator (S.indicator (fun z => u z i))) < ∞ :=
    (hUBle i).trans_lt (hUbase i)
  have hDB (i j : Fin 3) : morreyNorm 2 (25 / 8 : ℝ)
      (B.indicator (S.indicator (fun z => Du z i j))) < ∞ :=
    (hDBle i j).trans_lt (hDbase i j)
  have hballC : B ⊆ parabolicCylinder z₀.1 (z₀.2 + R ^ 2) (2 * R) :=
    metricBall_subset_parabolicCylinder_doubled z₀ hR
  have hUmix (i : Fin 3) : morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (B.indicator (S.indicator (fun z => u z i))) < ∞ :=
    morreyNorm_lt_top_of_lower_exponents (P := (6 / 5 : ℝ)) (P₀ := 3)
      (θ := 25 / 11) (θ₀ := 25 / 3) (B := B)
      (z₀ := (z₀.1, z₀.2 + R ^ 2)) (R := 2 * R)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by positivity) hballC (hUBoxAE i)
      (fun z hz => indicator_of_notMem hz _) (hUB i)
  have hUsix (i : Fin 3) : morreyNorm 3 (25 / 6 : ℝ)
      (B.indicator (S.indicator (fun z => u z i))) < ∞ :=
    morreyNorm_lt_top_of_lower_exponents (P := (3 : ℝ)) (P₀ := 3)
      (θ := 25 / 6) (θ₀ := 25 / 3) (B := B)
      (z₀ := (z₀.1, z₀.2 + R ^ 2)) (R := 2 * R)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by positivity) hballC (hUBoxAE i)
      (fun z hz => indicator_of_notMem hz _) (hUB i)
  -- global measurability of the cutoff coefficients
  have hφAE : AEMeasurable φp volume :=
    (hφ.1.continuous.comp continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have htimeAE : AEMeasurable
      (fun z : ParabolicPoint => timePartial φ z) volume :=
    ((timePartial_contDiff_full hφ.1).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have hlapAE := @first_round_gradient_source_morrey_hlapAE_3 Ω I φ hφ
  have htimeMulAE (i : Fin 3) : AEMeasurable
      (fun z => timePartial φ z * u z i) volume :=
    aemeasurable_mul_of_restrict_of_zero_outside hSmeas htimeAE
      (hucomp i) htimezeroS
  have hlapMulAE (i : Fin 3) : AEMeasurable
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) volume :=
    aemeasurable_mul_of_restrict_of_zero_outside hSmeas hlapAE
      (hucomp i) hlapzeroS
  have hconvAE (i : Fin 3) := @first_round_gradient_source_morrey_hconvAE_4 u Du φ Ω' J hSmeas
    hφzeroS hucomp hDucomp hφAE i
  have hforceAE (i : Fin 3) : AEMeasurable (fun z => φp z * f z i) volume :=
    aemeasurable_mul_of_restrict_of_zero_outside hSmeas hφAE
      (hfcomp i) (fun z hz => hφzeroS z hz)
  have hDpAE' (i : Fin 3) : AEMeasurable
      (fun z => φp z * Dp z i) volume :=
    aemeasurable_mul_of_restrict_of_zero_outside hBmeas hφAE
      (hDpAE i) hφzero
  -- the four heat-slot terms
  have htimeEq (i : Fin 3) :
      (fun z => timePartial φ z * u z i) =
        (fun z => timePartial φ z * S.indicator (fun w => u w i) z) := by
    funext z
    by_cases hzS : z ∈ S
    · rw [indicator_of_mem hzS]
    · rw [indicator_of_notMem hzS, htimezeroS z hzS, zero_mul, zero_mul]
  have hlapEq (i : Fin 3) :
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) =
        (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 *
          S.indicator (fun w => u w i) z) := by
    funext z
    by_cases hzS : z ∈ S
    · rw [indicator_of_mem hzS]
    · rw [indicator_of_notMem hzS, hlapzeroS z hzS, zero_mul, zero_mul]
  have htimeN (i : Fin 3) := @first_round_gradient_source_morrey_htimeN_4 u φ Ω' J z₀ R C hC
    htimezero htime hUmix htimeEq i
  have hlapN (i : Fin 3) := @first_round_gradient_source_morrey_hlapN_5 u φ Ω' J z₀ R C hC
    hlapzero hlap hUmix hlapEq i
  have hconvEq (i : Fin 3) := @first_round_gradient_source_morrey_hconvEq_6 u Du φ Ω' J z₀ R
    hφzero hφzeroS i
  have hconvN (i : Fin 3) := @first_round_gradient_source_morrey_hconvN_5 u Du φ Ω' J z₀ R C hC
    hφzero hvalue hUBoxAE hDuBoxAE hUB hDB hconvEq i
  have hforceN (i : Fin 3) := @first_round_gradient_source_morrey_hforceN_6 Ω I q u Du p f hsol φ
    Ω' J hbox z₀ R hR hq hφ hφbox hφpdef hφzero hballC hforceAE i
  have hDpFin (i : Fin 3) := @first_round_gradient_source_morrey_hDpFin_7 φ z₀ R Dp hDpN C hC
    hφzero hvalue i
  -- the heat slot
  have hGnorm (i : Fin 3) := @first_round_gradient_source_morrey_hGnorm_7 u Du f φ Dp htimeMulAE
    hlapMulAE hconvAE hforceAE hDpAE' htimeN hlapN hconvN hforceN hDpFin i
  -- the derivative slot
  have hHtarget (j i : Fin 3) := @first_round_gradient_source_morrey_hHtarget_8 u φ Ω' J hspzeroS
    j i
  have hHnorm (j i : Fin 3) := @first_round_gradient_source_morrey_hHnorm_8 u φ Ω' J z₀ R C hC
    hspzero hsp hUsix hHtarget j i
  exact ⟨hGnorm, hHnorm⟩

end CKN.Core.Step4
