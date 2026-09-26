/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.LocalizedEquationGradientData
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMeasurability

/-!
# Localized Equation Gradient Measurability

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

open CKN.Foundation.Parabolic
open CKN.Core.Step3


noncomputable section

namespace CKN.Core.Step4

theorem localized_gradient_source_aemeasurable_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {Dp : ParabolicPoint → Vec3}
    (hDp : ∀ i : Fin 3,
      AEMeasurable (fun z => Dp z i)
        (volume.restrict (spaceTimeSet Ω' J))) :
    (∀ i : Fin 3, AEMeasurable
      (fun z => localizedGradientSourceG φ u Du f Dp z i) volume) ∧
    (∀ j i : Fin 3, AEMeasurable
      (fun z => -localizedGradientSourceH φ u j z i) volume) := by
  rcases hsol with ⟨hΩ, hI, hIord, hq, hfSol, hdata, hS2, hS3, hS4⟩
  rcases hφ with ⟨hφd, hφc, hφΩ⟩
  obtain ⟨hu, hDu, hpmeas, hfmeas, hEssSup, henergy, hp, hf, hgrad⟩ :=
    hdata Ω' J hbox
  have hJmeas : MeasurableSet J := hbox.2.2.2.1.measurableSet
  have hSmeas : MeasurableSet (spaceTimeSet Ω' J) :=
    hbox.1.measurableSet.prod hJmeas
  have hφae : AEMeasurable (show ParabolicPoint → ℝ from φ) volume :=
    hφd.continuous.aemeasurable
  have htimeae : AEMeasurable
      (fun z : ParabolicPoint => timePartial φ z) volume :=
    (timePartial_contDiff_full hφd).continuous.aemeasurable
  have hspae (j : Fin 3) : AEMeasurable
      (fun z : ParabolicPoint => spatialPartial φ j z) volume :=
    (spatialPartial_contDiff hφd j).continuous.aemeasurable
  have hlapae : AEMeasurable
      (fun z : ParabolicPoint =>
        spatialLaplacian (fun x => φ (x, z.2)) z.1) volume := by
    change AEMeasurable (fun z : ParabolicPoint =>
      ∑ j : Fin 3, spatialSecondPartial
        (show ParabolicPoint → ℝ from φ) j j z) volume
    exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun j _ =>
      (spatialSecondPartial_contDiff_full hφd j j).continuous.aemeasurable)
  have hzero (a : ParabolicPoint → ℝ)
      (ha : ∀ z ∉ tsupport φ, a z = 0) :
      ∀ z ∉ spaceTimeSet Ω' J, a z = 0 := by
    intro z hz
    apply ha
    intro hzφ
    apply hz
    exact hφbox hzφ
  have hlocal_mul {a b c : ParabolicPoint → ℝ}
      (ha : AEMeasurable a volume)
      (hb : AEMeasurable b (volume.restrict (spaceTimeSet Ω' J)))
      (hc : AEMeasurable c (volume.restrict (spaceTimeSet Ω' J)))
      (ha0 : ∀ z ∉ spaceTimeSet Ω' J, a z = 0) :
      AEMeasurable (fun z => a z * b z * c z) volume := by
    have hbc : AEMeasurable (fun z => b z * c z)
        (volume.restrict (spaceTimeSet Ω' J)) := hb.mul hc
    have habc :=
      CKN.Core.Endgame.aemeasurable_mul_of_restrict_of_zero_outside
        hSmeas ha hbc ha0
    simpa [mul_assoc] using habc
  have hlocal_mul2 {a b : ParabolicPoint → ℝ}
      (ha : AEMeasurable a volume)
      (hb : AEMeasurable b (volume.restrict (spaceTimeSet Ω' J)))
      (ha0 : ∀ z ∉ spaceTimeSet Ω' J, a z = 0) :
      AEMeasurable (fun z => a z * b z) volume := by
    have h := hlocal_mul (c := fun _ : ParabolicPoint => (1 : ℝ))
      ha hb (aemeasurable_const : AEMeasurable
        (fun _ : ParabolicPoint => (1 : ℝ))
          (volume.restrict (spaceTimeSet Ω' J))) ha0
    simpa using h
  have hucomp (i : Fin 3) :
      AEMeasurable (fun z => u z i)
        (volume.restrict (spaceTimeSet Ω' J)) :=
    aemeasurable_pi_iff.mp hu.aemeasurable i
  have hDucomp (i j : Fin 3) :
      AEMeasurable (fun z => Du z i j)
        (volume.restrict (spaceTimeSet Ω' J)) :=
    aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hDu.aemeasurable i) j
  have hfcomp (i : Fin 3) :
      AEMeasurable (fun z => f z i)
        (volume.restrict (spaceTimeSet Ω' J)) :=
    aemeasurable_pi_iff.mp hfmeas.aemeasurable i
  have hDpcomp (i : Fin 3) :
      AEMeasurable (fun z => Dp z i)
        (volume.restrict (spaceTimeSet Ω' J)) := hDp i
  have htimezero : ∀ z ∉ spaceTimeSet Ω' J, timePartial φ z = 0 := by
    apply hzero
    intro z hz
    exact timePartial_zero_of_not_mem_tsupport_public hφd hz
  have hlapzero : ∀ z ∉ spaceTimeSet Ω' J,
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
    intro z hz
    have hnot : (z.1, z.2) ∉ tsupport φ := by
      intro hmem
      exact hz (hφbox hmem)
    change (∑ j : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from φ) j j z) = 0
    apply Finset.sum_eq_zero
    intro j hj
    exact spatialSecondPartial_zero_of_not_mem_tsupport_public hφd hnot j j
  have hφzero : ∀ z ∉ spaceTimeSet Ω' J, φ z = 0 := by
    apply hzero
    intro z hz
    exact image_eq_zero_of_notMem_tsupport hz
  have hspzero (j : Fin 3) : ∀ z ∉ spaceTimeSet Ω' J,
      spatialPartial φ j z = 0 := by
    apply hzero
    intro z hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hφd hz j
  have hG (i : Fin 3) : AEMeasurable
      (fun z => localizedGradientSourceG φ u Du f Dp z i) volume := by
    have ht := hlocal_mul2 htimeae (hucomp i) htimezero
    have hl := hlocal_mul2 hlapae (hucomp i) hlapzero
    have hf' := hlocal_mul2 hφae (hfcomp i) hφzero
    have hdp' := hlocal_mul2 hφae (hDpcomp i) hφzero
    have hsum : AEMeasurable
        (fun z : ParabolicPoint =>
          timePartial (show ParabolicPoint → ℝ from φ) z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i -
          (show ParabolicPoint → ℝ from φ) z * (∑ j, u z j * Du z i j) +
          (show ParabolicPoint → ℝ from φ) z * f z i -
          (show ParabolicPoint → ℝ from φ) z * Dp z i)
        volume := by
      have hc : AEMeasurable (fun z : ParabolicPoint =>
          (show ParabolicPoint → ℝ from φ) z *
          (∑ j, u z j * Du z i j)) volume := by
        have hc' := Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
          (fun j _ => hlocal_mul2 hφae
            (hucomp j |>.mul (hDucomp i j)) hφzero)
        convert hc' using 1
        funext z
        simp only [Finset.sum_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rfl
      exact (((ht.add hl).sub hc).add hf').sub hdp'
    refine hsum.congr (Filter.Eventually.of_forall (fun z => ?_))
    dsimp [localizedGradientSourceG, localizedEquationG,
      localizedConvection]
  have hH (j i : Fin 3) : AEMeasurable
      (fun z => -localizedGradientSourceH φ u j z i) volume := by
    have hm := hlocal_mul2 (hspae j) (hucomp i) (hspzero j)
    have hm' := hm.mul (aemeasurable_const : AEMeasurable
      (fun _ : ParabolicPoint => (2 : ℝ)) volume)
    refine hm'.congr (Filter.Eventually.of_forall (fun z => ?_))
    dsimp [localizedGradientSourceH, localizedEquationH]
    change spatialPartial (show ParabolicPoint → ℝ from φ) j z * u z i * 2 =
      -(((-2 * spatialPartial (show ParabolicPoint → ℝ from φ) j z) • u z) i)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨hG, hH⟩

end CKN.Core.Step4
