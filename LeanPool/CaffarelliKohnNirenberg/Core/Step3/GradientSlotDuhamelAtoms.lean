/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.LocalizedEquationGradientData

/-!
# Gradient Slot Duhamel Atoms

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

open CKN.Foundation.Parabolic
open CKN.Core.Step4


noncomputable section

namespace CKN.Core.Step3

/-- A smooth factor that vanishes off the support of a cutoff function
factorizes against an integrable density on a local space-time box, and its
own support stays inside that box.  This collects the three conditions
`compact_factor_integrable` asks for, so that each tested term below is
handled uniformly. -/
private lemma gradient_slot_factor_data {Ω' : Set Vec3} {J : Set ℝ}
    {φ : Vec3 × ℝ → ℝ} (hφc : HasCompactSupport φ)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {b : Vec3 × ℝ → ℝ} (hbd : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbz : ∀ z, z ∉ tsupport φ → b z = 0) :
    Continuous b ∧ HasCompactSupport b ∧
      tsupport b ⊆ (spaceTimeSet Ω' J : Set (Vec3 × ℝ)) := by
  refine ⟨hbd.continuous, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact hφc.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact hbz z hnot
  · have hsub : tsupport b ⊆ tsupport φ := by
      apply closure_minimal
      · intro z hz
        by_contra hnot
        apply hz
        exact hbz z hnot
      · exact isClosed_tsupport φ
    simpa [spaceTimeSet] using hsub.trans hφbox

/-- Integrability of the atoms of the cutoff-tested local equation of paper
label `lem:local-equation`.  Given a suitable weak solution, a spatial test
cutoff `φ` supported in a local box, a second smooth compactly supported
factor `ψ`, and a pressure gradient integrable on that box, every term of the
tested equation — the time derivative slot, the force term, the convective
products, the gradient slot, the mixed derivative slots, the pressure slot,
the pressure-gradient slot, and the localization of the convection — is
integrable on all of space-time. -/
theorem gradientSlot_tested_integrable_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {Dp : ParabolicPoint → Vec3}
    (hDpInt : ∀ i : Fin 3, Integrable (fun z => Dp z i)
      (volume.restrict (spaceTimeSet Ω' J)))
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
    (i : Fin 3) :
    Integrable (fun z : ParabolicPoint =>
      u z i * (timePartial φ z * ψ z)) volume ∧
    Integrable (fun z : ParabolicPoint => f z i * (φ z * ψ z)) volume ∧
    (∀ j : Fin 3, Integrable (fun z : ParabolicPoint =>
      u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) volume) ∧
    (∀ j : Fin 3, Integrable (fun z : ParabolicPoint =>
      Du z i j * (spatialPartial φ j z * ψ z)) volume) ∧
    (∀ j : Fin 3, Integrable (fun z : ParabolicPoint =>
      u z i * (spatialPartial φ j z * spatialPartial ψ j z)) volume) ∧
    (∀ j : Fin 3, Integrable (fun z : ParabolicPoint =>
      u z i * (spatialSecondPartial φ j j z * ψ z)) volume) ∧
    Integrable (fun z : ParabolicPoint =>
      p z * spatialPartial (fun w => φ w * ψ w) i z) volume ∧
    Integrable (fun z : ParabolicPoint => Dp z i * (φ z * ψ z)) volume ∧
    Integrable (fun z : ParabolicPoint =>
      (φ z * ψ z) * localizedConvection u Du z i) volume := by
  rcases hsol with ⟨_hΩ, _hI, _hIord, hq, _hfSol, hdata, _hS2, _hS3, _hS4⟩
  rcases hφ with ⟨hφd, hφc, _hφΩ⟩
  rcases hψ with ⟨hψd, _hψc, _hψΩ⟩
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  have : IsFiniteMeasure μ :=
    local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
  obtain ⟨hu, hDu, _hpmeas, _hfmeas, _hEssSup, henergy, hp, hf, _hgrad⟩ :=
    hdata Ω' J hbox
  have hLp := local_memLp_two_of_energy (hu := hu) (hDu := hDu) henergy
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [ENNReal.one_le_ofReal]
    linarith only [hq]
  have huComp (i : Fin 3) : MemLp (fun z => u z i) 2 μ :=
    hLp.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hDuComp (i j : Fin 3) : MemLp (fun z => Du z i j) 2 μ :=
    (hLp.2.continuousLinearMap_comp
      (ContinuousLinearMap.proj i :
        (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
      (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
  have hUi (i : Fin 3) : Integrable (fun z => u z i) μ :=
    (huComp i).integrable (by norm_num)
  have hDij (i j : Fin 3) : Integrable (fun z => Du z i j) μ :=
    (hDuComp i j).integrable (by norm_num)
  have hUU (i j : Fin 3) : Integrable (fun z => u z i * u z j) μ :=
    (huComp i).integrable_mul (huComp j)
  have hUD (i j : Fin 3) : Integrable (fun z => u z j * Du z i j) μ :=
    (huComp j).integrable_mul (hDuComp i j)
  have hfComp (i : Fin 3) : MemLp (fun z => f z i) (ENNReal.ofReal q) μ :=
    hf.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hpInt : Integrable p μ := hp.integrable (by norm_num)
  have hDpInt' (i : Fin 3) : Integrable (fun z => Dp z i) μ := hDpInt i
  have hφψd : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => φ z * ψ z) :=
    hφd.mul hψd
  have hφψ_ts : tsupport (fun z : Vec3 × ℝ => φ z * ψ z) ⊆ tsupport φ := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      change φ z * ψ z = 0
      rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]
    · exact isClosed_tsupport φ
  have hφψz : ∀ z, z ∉ tsupport φ → (φ z * ψ z) = 0 := fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hbox_mul {a : ParabolicPoint → ℝ} (ha : Integrable a μ)
      {b : Vec3 × ℝ → ℝ} (hbd : ContDiff ℝ (⊤ : ℕ∞) b)
      (hbz : ∀ z, z ∉ tsupport φ → b z = 0) :
      Integrable (fun z => a z * b z) volume := by
    obtain ⟨hbcont, hbc, hbs⟩ := gradient_slot_factor_data hφc hφbox hbd hbz
    exact compact_factor_integrable (by simpa [μ] using ha) hbcont hbc hbs
  have h1 : Integrable (fun z : ParabolicPoint =>
      u z i * (timePartial φ z * ψ z)) volume :=
    hbox_mul (hUi i) ((timePartial_contDiff_full hφd).mul hψd)
      (fun z hz => by
        rw [timePartial_zero_of_not_mem_tsupport_public hφd hz, zero_mul])
  have h2 : Integrable (fun z : ParabolicPoint =>
      f z i * (φ z * ψ z)) volume :=
    hbox_mul ((hfComp i).integrable hq1) hφψd hφψz
  have h3 (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) volume :=
    hbox_mul (hUU i j) (spatialPartial_contDiff hφψd j)
      (fun z hz => spatialPartial_zero_of_not_mem_tsupport_public hφψd
        (fun hmem => hz (hφψ_ts hmem)) j)
  have h4 (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      Du z i j * (spatialPartial φ j z * ψ z)) volume :=
    hbox_mul (hDij i j) ((spatialPartial_contDiff hφd j).mul hψd)
      (fun z hz => by
        rw [spatialPartial_zero_of_not_mem_tsupport_public hφd hz j, zero_mul])
  have h5 (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      u z i * (spatialPartial φ j z * spatialPartial ψ j z)) volume :=
    hbox_mul (hUi i)
      ((spatialPartial_contDiff hφd j).mul (spatialPartial_contDiff hψd j))
      (fun z hz => by
        rw [spatialPartial_zero_of_not_mem_tsupport_public hφd hz j, zero_mul])
  have h6 (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      u z i * (spatialSecondPartial φ j j z * ψ z)) volume :=
    hbox_mul (hUi i) ((spatialSecondPartial_contDiff_full hφd j j).mul hψd)
      (fun z hz => by
        rw [spatialSecondPartial_zero_of_not_mem_tsupport_public hφd hz j j,
          zero_mul])
  have h7 : Integrable (fun z : ParabolicPoint =>
      p z * spatialPartial (fun w => φ w * ψ w) i z) volume :=
    hbox_mul hpInt (spatialPartial_contDiff hφψd i)
      (fun z hz => spatialPartial_zero_of_not_mem_tsupport_public hφψd
        (fun hmem => hz (hφψ_ts hmem)) i)
  have h8 : Integrable (fun z : ParabolicPoint =>
      Dp z i * (φ z * ψ z)) volume :=
    hbox_mul (hDpInt' i) hφψd hφψz
  have hconv : Integrable (fun z : ParabolicPoint =>
      localizedConvection u Du z i) μ := by
    have hsum : Integrable (fun z => ∑ j ∈ (Finset.univ : Finset (Fin 3)),
        u z j * Du z i j) μ :=
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hUD i j)
    refine hsum.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp [localizedConvection]
  have h9 : Integrable (fun z : ParabolicPoint =>
      (φ z * ψ z) * localizedConvection u Du z i) volume := by
    have h := hbox_mul hconv hφψd hφψz
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    exact mul_comm _ _
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end CKN.Core.Step3
