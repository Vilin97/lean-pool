/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationDuhamel
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# Localized Equation Gradient Data

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

open CKN.Foundation.Parabolic
open CKN.Core.Step3


noncomputable section

namespace CKN.Core.Step4

private lemma gradient_source_support_of_phi
    {φ : Vec3 × ℝ → ℝ} {V : Type} [Zero V]
    (hφc : HasCompactSupport φ) (v : ParabolicPoint → V)
    (hzv : ∀ z, parabolicHomeomorph z ∉ tsupport φ → v z = 0) :
    HasCompactSupport v := by
  let K : Set ParabolicPoint := parabolicHomeomorph ⁻¹' tsupport φ
  have hK : IsCompact K :=
    parabolicHomeomorph.isCompact_preimage.2 hφc.isCompact
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hnot
  apply hz
  apply hzv z
  simpa only [K, Set.mem_preimage, parabolicHomeomorph_apply] using hnot

theorem localized_gradient_source_data_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {Dp : ParabolicPoint → Vec3}
    (hDpInt : ∀ i : Fin 3,
      Integrable (fun z => Dp z i)
        (volume.restrict (spaceTimeSet Ω' J))) :
    (∀ i : Fin 3, Integrable
      (fun z => localizedGradientSourceG φ u Du f Dp z i) volume) ∧
    (∀ j i : Fin 3, Integrable
      (fun z => -localizedGradientSourceH φ u j z i) volume) ∧
    (∀ i : Fin 3, HasCompactSupport
      (fun z => localizedGradientSourceG φ u Du f Dp z i)) ∧
    (∀ j i : Fin 3, HasCompactSupport
      (fun z => -localizedGradientSourceH φ u j z i)) := by
  rcases hsol with ⟨hΩ, hI, hIord, hq, hfSol, hdata, hS2, hS3, hS4⟩
  rcases hφ with ⟨hφd, hφc, hφΩ⟩
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  haveI : IsFiniteMeasure μ :=
    CKN.Core.Step3.local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
  obtain ⟨hu, hDu, hpmeas, hfmeas, hEssSup, henergy, hp, hf, hgrad⟩ :=
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
  have hfComp (i : Fin 3) : MemLp (fun z => f z i)
      (ENNReal.ofReal q) μ :=
    hf.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hpInt : Integrable p μ := hp.integrable (by norm_num)
  have hφtime : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial φ z) :=
    timePartial_contDiff_full hφd
  have hφtime_c : HasCompactSupport
      (fun z : Vec3 × ℝ => timePartial φ z) := by
    apply HasCompactSupport.of_support_subset_isCompact hφc.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact timePartial_zero_of_not_mem_tsupport_public hφd hnot
  have hφtime_ts : tsupport (fun z : Vec3 × ℝ => timePartial φ z) ⊆
      tsupport φ := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      exact timePartial_zero_of_not_mem_tsupport_public hφd hnot
    · exact isClosed_tsupport φ
  have hφsp (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial φ j z) :=
    spatialPartial_contDiff hφd j
  have hφsp_c (j : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialPartial φ j z) := by
    apply HasCompactSupport.of_support_subset_isCompact hφc.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hφd hnot j
  have hφsp_ts (j : Fin 3) :
      tsupport (fun z : Vec3 × ℝ => spatialPartial φ j z) ⊆ tsupport φ := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      exact spatialPartial_zero_of_not_mem_tsupport_public hφd hnot j
    · exact isClosed_tsupport φ
  let lapφ : Vec3 × ℝ → ℝ := fun z =>
    ∑ j : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from φ) j j z
  have hlap : ContDiff ℝ (⊤ : ℕ∞) lapφ := by
    dsimp [lapφ]
    exact ContDiff.sum (fun j _ => spatialSecondPartial_contDiff_full hφd j j)
  have hlap_c : HasCompactSupport lapφ := by
    apply HasCompactSupport.of_support_subset_isCompact hφc.isCompact
    intro z hz
    by_contra hnot
    apply hz
    dsimp [lapφ]
    apply Finset.sum_eq_zero
    intro j hj
    exact spatialSecondPartial_zero_of_not_mem_tsupport_public hφd hnot j j
  have hlap_ts : tsupport lapφ ⊆ tsupport φ := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      dsimp [lapφ]
      apply Finset.sum_eq_zero
      intro j hj
      exact spatialSecondPartial_zero_of_not_mem_tsupport_public hφd hnot j j
    · exact isClosed_tsupport φ
  have hbox_factor {a : ParabolicPoint → ℝ}
      (ha : Integrable a μ) {b : Vec3 × ℝ → ℝ}
      (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ tsupport φ)
      (hb : Continuous b) : Integrable (fun z => a z * b z) volume := by
    have hprod : HasCompactSupport b := hbc
    have hsupport : tsupport b ⊆ (spaceTimeSet Ω' J : Set (Vec3 × ℝ)) :=
      hbs.trans hφbox
    exact compact_factor_integrable (a := a) (b := b)
      (by simpa [μ] using ha) hb hprod hsupport
  have hGt (i : Fin 3) : Integrable
      (fun z => u z i * timePartial φ z) volume := by
    simpa using hbox_factor (hUi i) hφtime_c hφtime_ts hφtime.continuous
  have hGlap (i : Fin 3) : Integrable
      (fun z => u z i * lapφ (z.1, z.2)) volume := by
    convert hbox_factor (hUi i) hlap_c hlap_ts hlap.continuous using 1
    funext z
    rfl
  have hGconv (i j : Fin 3) : Integrable
      (fun z => (show ParabolicPoint → ℝ from φ) z * u z j * Du z i j) volume := by
    have h := hbox_factor (hUD i j) hφc (by exact subset_rfl) hφd.continuous
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hGforce (i : Fin 3) : Integrable
      (fun z => f z i * (show ParabolicPoint → ℝ from φ) z) volume := by
    have h := hbox_factor ((hfComp i).integrable hq1)
      hφc (by exact subset_rfl) hφd.continuous
    simpa using h
  have hDp (i : Fin 3) : Integrable
      (fun z => (show ParabolicPoint → ℝ from φ) z * Dp z i) volume := by
    have h := hbox_factor (hDpInt i) hφc (by exact subset_rfl)
      hφd.continuous
    simpa [mul_comm] using h
  have hF (i : Fin 3) : Integrable
      (fun z => localizedGradientSourceG φ u Du f Dp z i) volume := by
    have hsum := (hGt i).add ((hGlap i).sub
      ((integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _ => hGconv i j)).sub (hGforce i)))
    have hsum' := hsum.sub (hDp i)
    refine hsum'.congr (Filter.Eventually.of_forall (fun z => ?_))
    dsimp [localizedGradientSourceG, localizedEquationG, localizedConvection,
      lapφ]
    rw [show spatialLaplacian (fun x => φ (x, z.2)) z.1 =
        ∑ j : Fin 3, spatialSecondPartial
          (show ParabolicPoint → ℝ from φ) j j (z.1, z.2) by rfl]
    simp only [Finset.sum_mul, Finset.mul_sum]
    ring_nf
  have hH (j i : Fin 3) : Integrable
      (fun z => -localizedGradientSourceH φ u j z i) volume := by
    have h := hbox_factor (hUi i) (b := fun z : Vec3 × ℝ =>
      spatialPartial φ j z) (hφsp_c j) (hφsp_ts j) (hφsp j).continuous
    have h := h.mul_const (2 : ℝ)
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    dsimp [localizedGradientSourceH, localizedEquationH]
    change u z i * spatialPartial (show ParabolicPoint → ℝ from φ) j z * 2 =
      -(((-2 * spatialPartial (show ParabolicPoint → ℝ from φ) j z) • u z) i)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hsupport_of_phi {V : Type} [Zero V] (v : ParabolicPoint → V)
      (hzv : ∀ z, parabolicHomeomorph z ∉ tsupport φ → v z = 0) :
      HasCompactSupport v :=
    gradient_source_support_of_phi hφc v hzv
  have hφzero (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : φ z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa [parabolicHomeomorph_apply] using hz
    change φ (z.1, z.2) = 0
    exact image_eq_zero_of_notMem_tsupport hz'
  have htimezero (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : timePartial φ z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa [parabolicHomeomorph_apply] using hz
    exact timePartial_zero_of_not_mem_tsupport_public hφd hz'
  have hspzero (j : Fin 3) (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) :
      spatialPartial φ j z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa [parabolicHomeomorph_apply] using hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hφd hz' j
  have hlapzero (z : Vec3 × ℝ) (hz : z ∉ tsupport φ) : lapφ z = 0 := by
    dsimp [lapφ]
    apply Finset.sum_eq_zero
    intro j hj
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa [parabolicHomeomorph_apply] using hz
    exact spatialSecondPartial_zero_of_not_mem_tsupport_public hφd hz j j
  have hFSupport (i : Fin 3) : HasCompactSupport
      (fun z => localizedGradientSourceG φ u Du f Dp z i) := by
    apply hsupport_of_phi
    intro z hz
    dsimp [localizedGradientSourceG, localizedEquationG]
    rw [hφzero z hz, htimezero z hz]
    have hlapz : spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
      change lapφ (z.1, z.2) = 0
      exact hlapzero (z.1, z.2) (by simpa [parabolicHomeomorph_apply] using hz)
    rw [hlapz]
    ring
  have hHSupport (j i : Fin 3) : HasCompactSupport
      (fun z => -localizedGradientSourceH φ u j z i) := by
    apply hsupport_of_phi
    intro z hz
    dsimp [localizedGradientSourceH, localizedEquationH]
    rw [hspzero j z hz]
    simp
  exact ⟨hF, hH, hFSupport, hHSupport⟩

end CKN.Core.Step4
