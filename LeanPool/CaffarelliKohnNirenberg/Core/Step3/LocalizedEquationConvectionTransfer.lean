/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationGradientTransfers

/-!
# Localized Equation Convection Transfer

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

open CKN.Foundation.Parabolic
open CKN.Core.Step4


noncomputable section

namespace CKN.Core.Step3

private lemma gradient_mem_solution_test
    {Ω : Set Vec3} {I : Set ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    {ζ : Vec3 × ℝ → ℝ}
    (hζ : ζ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
    (hζbox : tsupport ζ ⊆ Ω' ×ˢ J)
    (hbox : localBox Ω I Ω' J) :
    ζ ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
  refine ⟨hζ.1, hζ.2.1, ?_⟩
  intro z hz
  have hzbox := hζbox hz
  exact ⟨hbox.2.2.1 (subset_closure hzbox.1),
    hbox.2.2.2.2.2 (subset_closure hzbox.2)⟩

private lemma local_trace_pairing_zero
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    {ζ : Vec3 × ℝ → ℝ}
    (hζ : ζ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
    (hζbox : tsupport ζ ⊆ Ω' ×ˢ J) :
    (∫ z : ParabolicPoint, (∑ j, Du z j j) * ζ z) = 0 := by
  obtain ⟨hu, hDu, -, -, -, henergy, -, -, hgrad⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  have : IsFiniteMeasure μ := local_box_isFiniteMeasure
    hbox.2.1 hbox.2.2.2.2.1
  have hLp := local_memLp_two_of_energy (hu := hu) (hDu := hDu) henergy
  have huComp (j : Fin 3) : MemLp (fun z => u z j) 2 μ :=
    hLp.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
  have hDuComp (j k : Fin 3) : MemLp (fun z => Du z j k) 2 μ :=
    (hLp.2.continuousLinearMap_comp
      (ContinuousLinearMap.proj j : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
      (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)
  have hζsp (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial ζ j z) :=
    spatialPartial_contDiff hζ.1 j
  have hζspc (j : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialPartial ζ j z) := by
    apply HasCompactSupport.of_support_subset_isCompact hζ.2.1.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hζ.1 hnot j
  have hζspts (j : Fin 3) : tsupport
      (fun z : Vec3 × ℝ => spatialPartial ζ j z) ⊆ tsupport ζ := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      exact spatialPartial_zero_of_not_mem_tsupport_public hζ.1 hnot j
    · exact isClosed_tsupport ζ
  have htransfer (j : Fin 3) :
      (∫ z : ParabolicPoint, Du z j j * ζ z) =
        -(∫ z : ParabolicPoint, u z j * spatialPartial ζ j z) := by
    have hleft : Integrable (fun z : ParabolicPoint => Du z j j * ζ z) volume :=
      compact_factor_integrable (a := fun z => Du z j j) (b := ζ)
        (by simpa [μ] using (hDuComp j j).integrable (by norm_num))
        hζ.1.continuous hζ.2.1 hζbox
    have hright : Integrable (fun z : ParabolicPoint =>
        u z j * spatialPartial ζ j z) volume :=
      compact_factor_integrable (a := fun z => u z j)
        (b := fun z : Vec3 × ℝ => spatialPartial ζ j z)
        (by simpa [μ] using (huComp j).integrable (by norm_num))
        (hζsp j).continuous (hζspc j) (hζspts j |>.trans hζbox)
    have hzeroLeft : ∀ z ∉ spaceTimeSet Ω' J,
        Du z j j * ζ z = 0 := by
      intro z hz
      have hz' : (z.1, z.2) ∉ tsupport ζ := by
        intro hz'
        apply hz
        exact hζbox hz'
      have hzero := image_eq_zero_of_notMem_tsupport hz'
      change Du z j j * ζ (z.1, z.2) = 0
      rw [hzero, mul_zero]
    have hzeroRight : ∀ z ∉ spaceTimeSet Ω' J,
        u z j * spatialPartial ζ j z = 0 := by
      intro z hz
      have hz' : (z.1, z.2) ∉ tsupport ζ := by
        intro hz'
        apply hz
        exact hζbox hz'
      have hzero := spatialPartial_zero_of_not_mem_tsupport_public hζ.1 hz' j
      change u z j * spatialPartial ζ j (z.1, z.2) = 0
      rw [hzero, mul_zero]
    have hgradj : ∀ᵐ t ∂volume.restrict J,
        HasWeakPartialDerivOn Ω' j (fun x => u (x, t) j)
          (fun x => Du (x, t) j j) := by
      filter_upwards [hgrad j] with t ht
      exact ht j
    have htransfer' := spacetime_weak_partial_transfer
      (Ω' := Ω') (J := J) (a := fun z => u z j)
      (d := fun z => Du z j j) (b := ζ) (j := j)
      hbox.2.2.2.1.measurableSet hleft hright hzeroLeft hzeroRight hgradj
      (fun t => (CKN.slice_testFunction hζ.1 hζ.2.1 hζbox t).1)
      (fun t => (CKN.slice_testFunction hζ.1 hζ.2.1 hζbox t).2.1)
      (fun t => (CKN.slice_testFunction hζ.1 hζ.2.1 hζbox t).2.2)
    exact htransfer'
  have htraceInt : Integrable (fun z : ParabolicPoint => ∑ j, Du z j j) μ := by
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
      (hDuComp j j).integrable (by norm_num))
  have htraceSum :
      (∫ z : ParabolicPoint, (∑ j, Du z j j) * ζ z) =
        ∑ j, ∫ z : ParabolicPoint, Du z j j * ζ z := by
    calc
      (∫ z : ParabolicPoint, (∑ j, Du z j j) * ζ z) =
          ∫ z : ParabolicPoint, ∑ j, Du z j j * ζ z := by
            apply integral_congr_ae
            filter_upwards [] with z
            rw [Finset.sum_mul]
      _ = ∑ j, ∫ z : ParabolicPoint, Du z j j * ζ z := by
        exact integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
          compact_factor_integrable (a := fun z => Du z j j) (b := ζ)
            (by simpa [μ] using (hDuComp j j).integrable (by norm_num))
            hζ.1.continuous hζ.2.1 hζbox)
  have hrightInt (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      u z j * spatialPartial ζ j z) volume :=
    compact_factor_integrable (a := fun z => u z j)
      (b := fun z : Vec3 × ℝ => spatialPartial ζ j z)
      (by simpa [μ] using (huComp j).integrable (by norm_num))
      (hζsp j).continuous (hζspc j) (hζspts j |>.trans hζbox)
  have hrightSum : Integrable (fun z : ParabolicPoint =>
      ∑ j, u z j * spatialPartial ζ j z) volume :=
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hrightInt j)
  have hsolutionTest := hsol.2.2.2.2.2.2.1 ζ
    (gradient_mem_solution_test hζ hζbox hbox)
  have hzeroOutside : ∀ z ∉ spaceTimeSet Ω I,
      (∑ j, u z j * spatialPartial ζ j z) = 0 := by
    intro z hz
    have hz' : (z.1, z.2) ∉ tsupport ζ := by
      intro hz'
      apply hz
      exact ⟨hbox.2.2.1 (subset_closure (hζbox hz').1),
        hbox.2.2.2.2.2 (subset_closure (hζbox hz').2)⟩
    apply Finset.sum_eq_zero
    intro j hj
    have hzero := spatialPartial_zero_of_not_mem_tsupport_public hζ.1 hz' j
    change u z j * spatialPartial ζ j (z.1, z.2) = 0
    rw [hzero, mul_zero]
  have hsolutionGlobal :
      (∫ z : ParabolicPoint, ∑ j, u z j * spatialPartial ζ j z) = 0 := by
    calc
      (∫ z : ParabolicPoint, ∑ j, u z j * spatialPartial ζ j z) =
          ∫ z in spaceTimeSet Ω I, ∑ j, u z j * spatialPartial ζ j z := by
            exact (setIntegral_eq_integral_of_forall_compl_eq_zero
              hzeroOutside).symm
      _ = 0 := hsolutionTest.2
  calc
    (∫ z : ParabolicPoint, (∑ j, Du z j j) * ζ z) =
        ∑ j, ∫ z : ParabolicPoint, Du z j j * ζ z := htraceSum
    _ = -∑ j, ∫ z : ParabolicPoint, u z j * spatialPartial ζ j z := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      exact htransfer j
    _ = -(∫ z : ParabolicPoint, ∑ j, u z j * spatialPartial ζ j z) := by
      rw [integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hrightInt j)]
    _ = 0 := by rw [hsolutionGlobal, neg_zero]

private lemma local_trace_zero_on_nonzero
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ) :
    ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      φ z * ψ z ≠ 0 → ∑ j, Du (z.1, z.2) j j = 0 := by
  let b : Vec3 × ℝ → ℝ := fun z => φ z * ψ z
  let U : Set (Vec3 × ℝ) := {z | b z ≠ 0}
  have hbcont : Continuous b := hφ.1.continuous.mul hψ.1.continuous
  have hUopen : IsOpen U := by
    exact isOpen_ne_fun hbcont continuous_const
  have hUbox : U ⊆ Ω' ×ˢ J := by
    intro z hz
    have hzφ : φ z ≠ 0 := by
      intro hzφ
      exact hz (by simp [b, hzφ])
    exact hφbox (subset_tsupport (f := φ) (Function.mem_support.mpr hzφ))
  have htraceProd : IntegrableOn
      (fun z : Vec3 × ℝ => ∑ j, Du (z.1, z.2) j j)
      (Ω' ×ˢ J) volume := by
    obtain ⟨hu, hDu, -, -, -, henergy, -, -, -⟩ :=
      hsol.2.2.2.2.2.1 Ω' J hbox
    let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
    have : IsFiniteMeasure μ := local_box_isFiniteMeasure
      hbox.2.1 hbox.2.2.2.2.1
    have hLp := local_memLp_two_of_energy (hu := hu) (hDu := hDu) henergy
    have hDuComp (j k : Fin 3) : MemLp (fun z => Du z j k) 2 μ :=
      (hLp.2.continuousLinearMap_comp
        (ContinuousLinearMap.proj j : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
        (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)
    have htrace : Integrable (fun z : ParabolicPoint => ∑ j, Du z j j) μ :=
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        (hDuComp j j).integrable (by norm_num))
    change Integrable (fun z : ParabolicPoint => ∑ j, Du z j j)
      (volume.restrict (spaceTimeSet Ω' J))
    exact htrace
  have htraceLoc : LocallyIntegrableOn
      (fun z : Vec3 × ℝ => ∑ j, Du (z.1, z.2) j j) U volume := by
    exact htraceProd.locallyIntegrableOn.mono_set (fun z hz => hUbox hz)
  have hpair : ∀ ζ : Vec3 × ℝ → ℝ,
      ζ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport ζ ⊆ U →
      (∫ z : Vec3 × ℝ,
        ζ z * (∑ j, Du (z.1, z.2) j j)) = 0 := by
    intro ζ hζ hζU
    have hζbox : tsupport ζ ⊆ Ω' ×ˢ J := hζU.trans hUbox
    have hzero := local_trace_pairing_zero hsol hbox hζ hζbox
    change (∫ z : ParabolicPoint, ζ z * (∑ j, Du z j j)) = 0
    simpa only [mul_comm] using hzero
  have htraceU := hUopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    htraceLoc (by
      intro ζ hζ hζc hζU
      exact hpair ζ ⟨hζ, hζc, by simp [spaceTimeSet]⟩ hζU)
  filter_upwards [htraceU] with z hz
  intro hnonzero
  apply hz
  change b z ≠ 0
  simpa only [b] using hnonzero

theorem localized_convection_transfer_no_trace
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
    (i : Fin 3) :
    (∑ j, ∫ z, u z i * u z j *
      spatialPartial (fun w => φ w * ψ w) j z) =
      -(∫ z, (φ z * ψ z) * localizedConvection u Du z i) := by
  let Ψ : Vec3 × ℝ → Vec3 := fun z k => if k = i then ψ z else 0
  have hΨ : Ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ := by
    refine ⟨?_, ?_, by simp [spaceTimeSet]⟩
    · rw [contDiff_pi]
      intro k
      by_cases hki : k = i
      · subst k
        simpa [Ψ] using hψ.1
      · simpa [Ψ, hki] using (contDiff_const (c := (0 : ℝ)))
    · apply HasCompactSupport.of_support_subset_isCompact hψ.2.1.isCompact
      intro z hz
      by_contra hnot
      apply hz
      have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport hnot
      funext k
      simp [Ψ, hzero]
  have hconv (j : Fin 3) := localized_convection_transfer_of_sws
    hsol hφ hbox hφbox hΨ i j
  have hφψd : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => φ z * ψ z) :=
    hφ.1.mul hψ.1
  have hφψc : HasCompactSupport (fun z : Vec3 × ℝ => φ z * ψ z) :=
    hφ.2.1.mul_right (f' := ψ)
  have hφψbox : tsupport (fun z : Vec3 × ℝ => φ z * ψ z) ⊆ Ω' ×ˢ J :=
    (tsupport_mul_subset_left (f := φ) (g := ψ)).trans hφbox
  have htrace := local_trace_zero_on_nonzero hsol hφ hbox hφbox hψ
  have htraceP : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      φ (z.1, z.2) * ψ (z.1, z.2) ≠ 0 →
        ∑ j, Du z j j = 0 := by
    change ∀ᵐ z : Vec3 × ℝ ∂((volume : Measure Vec3).prod volume),
      φ z * ψ z ≠ 0 → ∑ j, Du (z.1, z.2) j j = 0
    exact htrace
  have hφψspc (j : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from fun w => φ w * ψ w) j (z.1, z.2)) := by
    apply HasCompactSupport.of_support_subset_isCompact hφψc.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hφψd hnot j
  have hφψspts (j : Fin 3) : tsupport
      (fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from fun w => φ w * ψ w) j (z.1, z.2)) ⊆
      tsupport (fun z : Vec3 × ℝ => φ z * ψ z) := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      exact spatialPartial_zero_of_not_mem_tsupport_public hφψd hnot j
    · exact isClosed_tsupport (fun z : Vec3 × ℝ => φ z * ψ z)
  obtain ⟨hu, hDu, -, -, -, henergy, -, -, -⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  have : IsFiniteMeasure μ := local_box_isFiniteMeasure
    hbox.2.1 hbox.2.2.2.2.1
  have hLp := local_memLp_two_of_energy (hu := hu) (hDu := hDu) henergy
  have huComp (j : Fin 3) : MemLp (fun z => u z j) 2 μ :=
    hLp.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
  have hDuComp (j k : Fin 3) : MemLp (fun z => Du z j k) 2 μ :=
    (hLp.2.continuousLinearMap_comp
      (ContinuousLinearMap.proj j : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
      (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)
  have hleftInt (j : Fin 3) : Integrable
      (fun z => u z i * u z j * spatialPartial
        (fun w => φ w * ψ w) j z) volume := by
    have huu : Integrable (fun z => u z i * u z j) μ :=
      (huComp i).integrable_mul (huComp j)
    exact compact_factor_integrable (a := fun z => u z i * u z j)
      (b := fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from fun w => φ w * ψ w) j (z.1, z.2))
      (by simpa [μ] using huu)
      (spatialPartial_contDiff hφψd j).continuous (hφψspc j)
      ((hφψspts j).trans hφψbox)
  have hrightInt (j : Fin 3) : Integrable
      (fun z => (Du z i j * u z j + u z i * Du z j j) *
        (φ z * ψ z)) volume := by
    have hA : Integrable (fun z => Du z i j * u z j) μ := by
      have h := (huComp j).integrable_mul (hDuComp i j)
      change Integrable (fun z => u z j * Du z i j) μ at h
      convert h using 1
      funext z
      ring
    have hB : Integrable (fun z => u z i * Du z j j) μ :=
      (huComp i).integrable_mul (hDuComp j j)
    have hsum : Integrable (fun z =>
        Du z i j * u z j + u z i * Du z j j) μ := by
      have h := hA.add hB
      change Integrable (fun z =>
        Du z i j * u z j + u z i * Du z j j) μ at h
      exact h
    exact compact_factor_integrable (a := fun z =>
      Du z i j * u z j + u z i * Du z j j)
      (b := fun z : Vec3 × ℝ => φ z * ψ z) (by
        simpa [μ] using hsum)
      hφψd.continuous hφψc hφψbox
  have hsumLeft := integral_finsetSum (Finset.univ : Finset (Fin 3))
    (fun j _ => hleftInt j)
  have hsumRight := integral_finsetSum (Finset.univ : Finset (Fin 3))
    (fun j _ => hrightInt j)
  calc
      (∑ j, ∫ z, u z i * u z j *
        spatialPartial (fun w => φ w * ψ w) j z) =
        -∑ j, ∫ z, (Du z i j * u z j + u z i * Du z j j) *
          (φ z * ψ z) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simpa [Ψ] using hconv j
    _ = -(∫ z : ParabolicPoint, ∑ j, (Du z i j * u z j + u z i * Du z j j) *
        (φ z * ψ z)) := by
      rw [integral_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _ => hrightInt j)]
    _ = -(∫ z : ParabolicPoint, (φ z * ψ z) * localizedConvection u Du z i) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [htraceP] with z hz
      change
        (∑ j, (Du z i j * u z j + u z i * Du z j j) *
            (φ (z.1, z.2) * ψ (z.1, z.2))) =
          (φ (z.1, z.2) * ψ (z.1, z.2)) *
            localizedConvection u Du z i
      by_cases hb : φ (z.1, z.2) * ψ (z.1, z.2) = 0
      · simp [hb]
      · have htr := hz hb
        dsimp [localizedConvection]
        let c : ℝ := φ (z.1, z.2) * ψ (z.1, z.2)
        change (∑ j, (Du z i j * u z j + u z i * Du z j j) * c) =
          c * (∑ j, u z j * Du z i j)
        calc
          (∑ j, (Du z i j * u z j + u z i * Du z j j) * c) =
              ∑ j, (Du z i j * u z j * c + u z i * Du z j j * c) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = (∑ j, Du z i j * u z j * c) +
              (∑ j, u z i * Du z j j * c) := by
                rw [Finset.sum_add_distrib]
          _ = c * (∑ j, u z j * Du z i j) +
              u z i * c * (∑ j, Du z j j) := by
                congr 1
                · calc
                    (∑ j, Du z i j * u z j * c) =
                        ∑ j, c * (u z j * Du z i j) := by
                          apply Finset.sum_congr rfl
                          intro j hj
                          ring
                    _ = c * (∑ j, u z j * Du z i j) := by
                          rw [Finset.mul_sum]
                · calc
                    (∑ j, u z i * Du z j j * c) =
                        ∑ j, u z i * c * Du z j j := by
                          apply Finset.sum_congr rfl
                          intro j hj
                          ring
                    _ = u z i * c * (∑ j, Du z j j) := by
                          rw [Finset.mul_sum]
          _ = c * (∑ j, u z j * Du z i j) := by
                rw [htr, mul_zero, add_zero]

end CKN.Core.Step3
