/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradientPackage
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ProducerRegularity
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Bootstrap
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapSourceBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapDerivativeSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents

/-!
# Source Morrey Gradient Instances

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3

noncomputable section

namespace CKN.Core.Step4

end CKN.Core.Step4

namespace CKN.Core.Endgame

/-- The quantitative first-round source data in the exact slots used by the
bootstrap consumer.  The derivative slot carries the Duhamel sign. -/
theorem first_round_source_package_of_step2
    (q ε₀ C : ℝ) (KU KD KP : ℝ≥0∞)
    (hq : 5 / 2 < q) (hC : 0 ≤ C)
    (hKU : KU < ⊤) (hKD : KD < ⊤) (hKP : KP < ⊤)
    {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → ℝ}
    {u f Dp : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hφrange : ∀ z : Vec3 × ℝ, 0 ≤ φ z ∧ φ z ≤ 1)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (11 / 16))
    (hder : ∀ z : Vec3 × ℝ, z.2 ≤ 0 →
      |timePartial φ z| ≤ C ∧
      (∀ j, |spatialPartial φ j z| ≤ C) ∧
      |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C)
    (hU : ∀ i, morreyNorm 3 (25 / 3)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
        (fun z => u z i)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
        (fun z => Du z i j)) ≤ KD)
    (hDp : ∀ i, AEMeasurable
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
        (fun z => Dp z i)) volume)
    (hP : ∀ i, morreyNorm (6 / 5) (25 / 11)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
        (fun z => Dp z i)) ≤ KP)
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀) :
    let F : ParabolicPoint → Vec3 :=
      fun z i => causalGradientSourceComponent φ u Du f Dp i z
    let H : Fin 3 → ParabolicPoint → Vec3 := fun j z i =>
      -causalDerivativeComponent φ u j i z
    (∀ i, AEMeasurable (fun z => F z i) volume) ∧
    (∀ j i, AEMeasurable (fun z => H j z i) volume) ∧
    (∀ i, morreyNorm (6 / 5) (25 / 11) (fun z => F z i) ≤
      bootstrapGradientMorreyBound q ε₀ C KU KD KP) ∧
    (∀ j i, morreyNorm 3 (25 / 6) (fun z => H j z i) ≤
      ENNReal.ofReal (2 * C) * KU) ∧
    morreyNorm (6 / 5) (25 / 11)
      (fun z => vec3EuclideanNorm (F z)) < ∞ ∧
    (∀ j, morreyNorm 3 (25 / 6)
      (fun z => vec3EuclideanNorm (H j z)) < ∞) ∧
    (∀ z ∉ parabolicCylinder (0 : Vec3) 0 (11 / 16), F z = 0) ∧
    (∀ j z, z ∉ parabolicCylinder (0 : Vec3) 0 (11 / 16) → H j z = 0) := by
  let F : ParabolicPoint → Vec3 :=
    fun z i => causalGradientSourceComponent φ u Du f Dp i z
  let H : Fin 3 → ParabolicPoint → Vec3 := fun j z i =>
    -causalDerivativeComponent φ u j i z
  have hKF : bootstrapGradientMorreyBound q ε₀ C KU KD KP < ⊤ :=
    bootstrapGradientMorreyBound_lt_top q ε₀ C hq hKU hKD hKP
  have hKG : ENNReal.ofReal (2 * C) * KU < ⊤ := by
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKU
  have hFcomp := bootstrap_gradient_source_of_suitableWeakSolution
    q ε₀ C KU KD KP hq hC hsol hdom hφ hφrange hsupp
    (fun z hz => ⟨(hder z hz).1, (hder z hz).2.2⟩) hU hD hDp hP hsmall
  have hHcomp := bootstrap_derivative_source_of_suitableWeakSolution
    C KU hC hsol hdom hφ hsupp (fun z hz => (hder z hz).2.1) hU
  have hFae : ∀ i, AEMeasurable (fun z => F z i) volume := by
    intro i
    simpa only [F] using (hFcomp i).1
  have hHae : ∀ j i, AEMeasurable (fun z => H j z i) volume := by
    intro j i
    convert (hHcomp j i).1.neg using 1
  have hFcompN : ∀ i, morreyNorm (6 / 5) (25 / 11)
      (fun z => F z i) < ∞ := by
    intro i
    simpa only [F] using (hFcomp i).2.trans_lt hKF
  have hHcompN : ∀ j i, morreyNorm 3 (25 / 6)
      (fun z => H j z i) < ∞ := by
    intro j i
    simpa only [H, morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg] using
      (hHcomp j i).2.trans_lt hKG
  have hFbound : ∀ i, morreyNorm (6 / 5) (25 / 11)
      (fun z => F z i) ≤ bootstrapGradientMorreyBound q ε₀ C KU KD KP := by
    intro i
    simpa only [F] using (hFcomp i).2
  have hHbound : ∀ j i, morreyNorm 3 (25 / 6)
      (fun z => H j z i) ≤ ENNReal.ofReal (2 * C) * KU := by
    intro j i
    simpa only [H, morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg] using
      (hHcomp j i).2
  have hFvec : morreyNorm (6 / 5) (25 / 11)
      (fun z => vec3EuclideanNorm (F z)) < ∞ :=
    morrey_norm_euclidean_lt_top_of_components (by norm_num) hFae hFcompN
  have hHvec : ∀ j, morreyNorm 3 (25 / 6)
      (fun z => vec3EuclideanNorm (H j z)) < ∞ := by
    intro j
    exact morrey_norm_euclidean_lt_top_of_components (by norm_num) (hHae j)
      (hHcompN j)
  have hFzero : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 (11 / 16), F z = 0 := by
    intro z hz
    funext i
    by_cases ht : z.2 ≤ 0
    · have hzero := (bootstrap_literal_sources_zero_on_past
        hφ.1 hsupp u Du f Dp ht hz).1
      have ht' : z ∈ {w : ParabolicPoint | w.2 ≤ 0} := ht
      change causalGradientSourceComponent φ u Du f Dp i z = 0
      unfold causalGradientSourceComponent
      rw [indicator_of_mem ht']
      exact congrFun hzero i
    · have ht' : z ∉ {w : ParabolicPoint | w.2 ≤ 0} := ht
      change causalGradientSourceComponent φ u Du f Dp i z = 0
      unfold causalGradientSourceComponent
      rw [indicator_of_notMem ht']
  have hHzero : ∀ j z, z ∉ parabolicCylinder (0 : Vec3) 0 (11 / 16) → H j z = 0 := by
    intro j z hz
    funext i
    by_cases ht : z.2 ≤ 0
    · have hzero := (bootstrap_literal_sources_zero_on_past
        hφ.1 hsupp u Du f Dp ht hz).2 j
      have hzeroi := congrFun hzero i
      have ht' : z ∈ {w : ParabolicPoint | w.2 ≤ 0} := ht
      change -causalDerivativeComponent φ u j i z = 0
      unfold causalDerivativeComponent
      rw [indicator_of_mem ht', hzeroi]
      simp only [Pi.zero_apply, neg_zero]
    · have ht' : z ∉ {w : ParabolicPoint | w.2 ≤ 0} := ht
      change -causalDerivativeComponent φ u j i z = 0
      unfold causalDerivativeComponent
      rw [indicator_of_notMem ht', neg_zero]
  exact ⟨hFae, hHae, hFbound, hHbound, hFvec, hHvec, hFzero, hHzero⟩

end CKN.Core.Endgame
