/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationLaplacian

/-!
# Localized Equation Tested

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.Step3
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential
theorem localized_divergence_tested_of_sws {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I) {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J) {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ) :
    (∫ z, ∑ i, localizedVelocity (show ParabolicPoint → ℝ from φ) u z i *
      (-(timePartial (fun w => ψ w i) z) - ∑ j, spatialSecondPartial (fun w => ψ w i) j j z)) =
      (∫ z, ∑ i, localizedDivergenceG φ u Du p f z i * ψ z i) +
        ∑ i, ∑ j, ∫ z,
          localizedDivergenceH φ u p j z i *
            spatialPartial (fun w => ψ w i) j z := by
  have hsol' : IsSuitableWeakSolutionIntegrable Ω I q u Du p f := hsol
  have hφ' : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I := hφ
  have hψ' : ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ := hψ
  rcases hsol with ⟨hΩ, hI, hIord, hq, hfSol, hdata, hS2, hS3, hS4⟩
  rcases hφ with ⟨hφd, hφc, hφΩ⟩
  rcases hψ with ⟨hψd, hψc, hψΩ⟩
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  haveI : IsFiniteMeasure μ := local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
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
      (ContinuousLinearMap.proj i : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
      (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
  have hpInt : Integrable p μ := hp.integrable (by norm_num)
  have hfInt : Integrable f μ := hf.integrable hq1
  have hφtime : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial φ z) := timePartial_contDiff_full hφd
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
  have hψi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => ψ z i) :=
    (contDiff_apply ℝ ℝ i).comp hψd
  have hψtime (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial (fun w => ψ w i) z) :=
    timePartial_contDiff_full (hψi i)
  have hψsp (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => ψ w i) j z) :=
    spatialPartial_contDiff (hψi i) j
  have hψsecond (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial
        (fun w => ψ w i) j j z) :=
    spatialSecondPartial_contDiff_full (hψi i) j j
  have hbox_factor {a : ParabolicPoint → ℝ}
      (ha : Integrable a μ) {α : Vec3 × ℝ → ℝ}
      (hαc : HasCompactSupport α)
      (hαts : tsupport α ⊆ tsupport φ)
      (hα : Continuous α) {b : Vec3 × ℝ → ℝ} (hb : Continuous b) :
      Integrable (fun z => a z * (α z * b z)) volume := by
    have hbc : HasCompactSupport (fun z : Vec3 × ℝ => α z * b z) :=
      hαc.mul_right (f' := b)
    have hbs : tsupport (fun z : Vec3 × ℝ => α z * b z) ⊆
        (spaceTimeSet Ω' J : Set (Vec3 × ℝ)) := by
      exact (tsupport_mul_subset_left (f := α) (g := b)).trans
        (hαts.trans hφbox)
    exact compact_factor_integrable (a := a)
      (b := fun z : Vec3 × ℝ => α z * b z)
      (by simpa only [μ] using ha) (hα.mul hb) hbc hbs
  have hUi (i : Fin 3) : Integrable (fun z => u z i) μ :=
    (huComp i).integrable (by norm_num)
  have hDij (i j : Fin 3) : Integrable (fun z => Du z i j) μ :=
    (hDuComp i j).integrable (by norm_num)
  have hUU (i j : Fin 3) : Integrable (fun z => u z i * u z j) μ :=
    (huComp i).integrable_mul (huComp j)
  have hfComp (i : Fin 3) : MemLp (fun z => f z i) (ENNReal.ofReal q) μ :=
    hf.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hVt (i : Fin 3) : Integrable
      (fun z => u z i * (φ z * timePartial (fun w => ψ w i) z)) volume := by
    exact hbox_factor (hUi i) hφc (by exact subset_rfl) hφd.continuous
      (hψtime i).continuous
  have hVsecond (i j : Fin 3) : Integrable
      (fun z => u z i * (φ z * spatialSecondPartial
        (fun w => ψ w i) j j z)) volume := by
    exact hbox_factor (hUi i) hφc (by exact subset_rfl) hφd.continuous
      (hψsecond i j).continuous
  have hConvPsi (i j : Fin 3) : Integrable
      (fun z => u z i * u z j * (φ z * spatialPartial
        (fun w => ψ w i) j z)) volume := by
    have h := hbox_factor (hUU i j) hφc (by exact subset_rfl) hφd.continuous
      (hψsp i j).continuous
    convert h using 1
  have hGradPsi (i j : Fin 3) : Integrable
      (fun z => Du z i j * (φ z * spatialPartial
        (fun w => ψ w i) j z)) volume := by
    exact hbox_factor (hDij i j) hφc (by exact subset_rfl) hφd.continuous
      (hψsp i j).continuous
  have hPressPsi (i : Fin 3) : Integrable
      (fun z => p z * (φ z * spatialPartial
        (fun w => ψ w i) i z)) volume := by
    exact hbox_factor hpInt hφc (by exact subset_rfl) hφd.continuous
      (hψsp i i).continuous
  have hForce (i : Fin 3) : Integrable
      (fun z => f z i * (φ z * ψ z i)) volume := by
    exact hbox_factor ((hfComp i).integrable hq1) hφc (by exact subset_rfl)
      hφd.continuous
      (hψi i).continuous
  have hGtime (i : Fin 3) : Integrable
      (fun z => u z i * (timePartial φ z * ψ z i)) volume := by
    exact hbox_factor (hUi i) hφtime_c hφtime_ts hφtime.continuous
      (hψi i).continuous
  have hGconv (i j : Fin 3) : Integrable
      (fun z => u z i * u z j * (spatialPartial φ j z * ψ z i)) volume := by
    have h := hbox_factor (hUU i j) (hφsp_c j) (hφsp_ts j)
      (hφsp j).continuous
      (hψi i).continuous
    convert h using 1
  have hGgrad (i j : Fin 3) : Integrable
      (fun z => Du z i j * (spatialPartial φ j z * ψ z i)) volume := by
    exact hbox_factor (hDij i j) (hφsp_c j) (hφsp_ts j)
      (hφsp j).continuous
      (hψi i).continuous
  have hGpress (i : Fin 3) : Integrable
      (fun z => p z * (spatialPartial φ i z * ψ z i)) volume := by
    exact hbox_factor hpInt (hφsp_c i) (hφsp_ts i) (hφsp i).continuous
      (hψi i).continuous
  have hGforce (i : Fin 3) : Integrable
      (fun z => f z i * (φ z * ψ z i)) volume := hForce i
  have hHconv (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => (φ z * u z i * u z j) *
        spatialPartial (fun w => ψ w i) j z) volume := by
    have h := hConvPsi i j
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  have hHgrad (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => (u z i * spatialPartial φ j z) *
        spatialPartial (fun w => ψ w i) j z) volume := by
    have h := hbox_factor (hUi i) (hφsp_c j) (hφsp_ts j)
      (hφsp j).continuous
      (hψsp i j).continuous
    simpa only [mul_assoc] using h
  have hHpress (i : Fin 3) : Integrable
      (fun z : ParabolicPoint => (p z * φ z) * spatialPartial
        (fun w => ψ w i) i z) volume := by
    have h := hbox_factor hpInt hφc (by exact subset_rfl) hφd.continuous
      (hψsp i i).continuous
    simpa only [mul_assoc] using h
  have hLtime : Integrable (fun z => ∑ i,
      u z i * (φ z * timePartial (fun w => ψ w i) z)) volume :=
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hVt i)
  have hLsecond : Integrable (fun z => ∑ i, ∑ j,
      u z i * (φ z * spatialSecondPartial (fun w => ψ w i) j j z)) volume := by
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        hVsecond i j))
  have hLconv : Integrable (fun z => ∑ i, ∑ j,
      u z i * u z j * (φ z * spatialPartial
        (fun w => ψ w i) j z)) volume := by
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        hConvPsi i j))
  have hLgrad : Integrable (fun z => ∑ i, ∑ j,
      Du z i j * (φ z * spatialPartial
        (fun w => ψ w i) j z)) volume := by
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        hGradPsi i j))
  have hLpress : Integrable (fun z => p z * ∑ i,
      φ z * spatialPartial (fun w => ψ w i) i z) volume := by
    have hi : Integrable (fun z => ∑ i,
        p z * (φ z * spatialPartial (fun w => ψ w i) i z)) volume :=
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hPressPsi i)
    convert hi using 1
    funext z
    rw [Finset.mul_sum]
  have hLforce : Integrable (fun z => ∑ i,
      f z i * (φ z * ψ z i)) volume :=
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hForce i)
  have hG : Integrable (fun z : ParabolicPoint => ∑ i,
      localizedDivergenceG φ u Du p f z i * ψ z i) volume := by
    have hGi (i : Fin 3) : Integrable
        (fun z : ParabolicPoint =>
          localizedDivergenceG φ u Du p f z i * ψ z i) volume := by
      have h2 : Integrable (fun z : ParabolicPoint => ∑ j,
          u z i * u z j * (spatialPartial φ j z * ψ z i)) volume :=
        integrable_finsetSum (Finset.univ : Finset (Fin 3))
          (fun j _ => hGconv i j)
      have h3 : Integrable (fun z : ParabolicPoint => ∑ j,
          Du z i j * (spatialPartial φ j z * ψ z i)) volume :=
        integrable_finsetSum (Finset.univ : Finset (Fin 3))
          (fun j _ => hGgrad i j)
      have h4 := hGpress i
      have h5 := hGforce i
      have hsum := (hGtime i).add (h2.sub (h3.sub (h4.add h5)))
      refine hsum.congr (Filter.Eventually.of_forall (fun z => ?_))
      simp only [localizedDivergenceG, Pi.add_apply, Pi.sub_apply, add_mul,
        sub_mul, Finset.sum_mul]
      simp_rw [mul_assoc, mul_left_comm, mul_comm]
      ring
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (fun i _ => hGi i)
  have hH : Integrable (fun z : ParabolicPoint => ∑ i, ∑ j,
      localizedDivergenceH φ u p j z i * spatialPartial
        (fun w => ψ w i) j z) volume := by
    have hHij (i j : Fin 3) : Integrable
        (fun z : ParabolicPoint => localizedDivergenceH φ u p j z i *
          spatialPartial (fun w => ψ w i) j z) volume := by
      by_cases hij : i = j
      · subst j
        have hsum := (hHconv i i).add (hHgrad i i)
        have hsum' := hsum.add (hHpress i)
        refine hsum'.congr (Filter.Eventually.of_forall (fun z => ?_))
        simp only [Pi.add_apply, localizedDivergenceH, ↓reduceIte]
        ring
      · have hsum := (hHconv i j).add (hHgrad i j)
        refine hsum.congr (Filter.Eventually.of_forall (fun z => ?_))
        simp only [Pi.add_apply, localizedDivergenceH, hij, ↓reduceIte, add_zero]
        ring
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hHij i j))
  let φp : ParabolicPoint → ℝ := fun z => φ (z.1, z.2)
  have hφp_eq : φp = (show ParabolicPoint → ℝ from φ) := by
    funext z
    rfl
  let ψp : ParabolicPoint → Vec3 := fun z => ψ (z.1, z.2)
  have hψp_eq : ψp = (show ParabolicPoint → Vec3 from ψ) := by
    funext z
    rfl
  have htimeProd (i : Fin 3) (z : ParabolicPoint) :
      timePartial (fun w => (φ • ψ) w i) z =
        timePartial φp z * ψp z i + φp z * timePartial
          (fun w => ψ w i) z := by
    have h := timePartial_mul_full hφd (hψi i) z
    convert h using 1
    all_goals rfl
  have hspaceProd (i j : Fin 3) (z : ParabolicPoint) :
      spatialPartial (fun w => (φ • ψ) w i) j z =
        spatialPartial φp j z * ψp z i + φp z * spatialPartial
          (fun w => ψ w i) j z := by
    have h := spatialPartial_mul_full hφd (hψi i) j z
    convert h using 1
    all_goals rfl
  have hηtest : (φ • ψ) ∈
      spaceTimeTestFunction (V := Vec3) Ω I := by
    refine ⟨hφd.smul hψd, hψc.smul_left, ?_⟩
    exact (tsupport_smul_subset_left φ ψ).trans hφΩ
  have hS3test := hS3 (φ • ψ) hηtest
  let R : ParabolicPoint → ℝ := fun z =>
    (-(∑ i, u z i * timePartial (fun w => (φ • ψ) w i) z))
      - ∑ i, ∑ j, u z i * u z j *
          spatialPartial (fun w => (φ • ψ) w i) j z
      + ∑ i, ∑ j, Du z i j *
          spatialPartial (fun w => (φ • ψ) w i) j z
      - p z * ∑ i, spatialPartial (fun w => (φ • ψ) w i) i z
      - ∑ i, f z i * (φ • ψ) z i
  have hS3zero : (∫ z in spaceTimeSet Ω I, R z) = 0 := by
    simpa only using hS3test.2
  let F : ParabolicPoint → ℝ := fun z =>
    (-(∑ i, u z i * (φp z * timePartial (fun w => ψp w i) z)))
      - ∑ i, ∑ j, u z i * u z j *
          (φp z * spatialPartial (fun w => ψp w i) j z)
      + ∑ i, ∑ j, Du z i j *
          (φp z * spatialPartial (fun w => ψp w i) j z)
      - p z * ∑ i, φp z * spatialPartial (fun w => ψp w i) i z
      - ∑ i, localizedDivergenceG φ u Du p f z i * ψp z i
  have hF : Integrable F volume := by
    dsimp [F]
    rw [hφp_eq, hψp_eq]
    exact (((hLtime.neg.sub hLconv).add hLgrad).sub hLpress).sub hG
  have hRF : R = F := by
    funext z
    dsimp [R, F]
    simp_rw [htimeProd, hspaceProd]
    have hforce (i : Fin 3) : (φ • ψ) z i = φp z * ψp z i := by
      rfl
    simp_rw [hforce]
    have hGpoint (i : Fin 3) :
        localizedDivergenceG φ u Du p f z i * ψp z i =
          (timePartial (show ParabolicPoint → ℝ from φ) z * u z i +
            ∑ j, u z i * u z j * spatialPartial φp j z -
            ∑ j, Du z i j *
              spatialPartial φp j z +
            p z * spatialPartial φp i z +
            f z i * φp z) * ψp z i := by
      rfl
    simp_rw [hGpoint]
    simp only [Finset.sum_add_distrib, add_mul, sub_mul, Finset.sum_mul]
    simp only [mul_add]
    have hconv (i : Fin 3) :
        (∑ j, u z i * u z j *
            (spatialPartial φp j z * ψp z i)) =
          ∑ j, u z i * u z j * spatialPartial φp j z * ψp z i := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hgrad (i : Fin 3) :
        (∑ j, Du z i j *
            (spatialPartial φp j z * ψp z i)) =
          ∑ j, Du z i j * spatialPartial φp j z * ψp z i := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hconvAll :
        (∑ i, ∑ j, u z i * u z j *
          (spatialPartial φp j z * ψp z i)) =
          ∑ i, ∑ j, u z i * u z j * spatialPartial φp j z * ψp z i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hconv i
    have hgradAll :
        (∑ i, ∑ j, Du z i j *
          (spatialPartial φp j z * ψp z i)) =
          ∑ i, ∑ j, Du z i j * spatialPartial φp j z * ψp z i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hgrad i
    rw [hconvAll, hgradAll, hφp_eq, hψp_eq]
    simp only [Finset.mul_sum]
    simp_rw [mul_assoc, mul_left_comm, mul_comm]
    abel
  have hFzero : ∀ z ∉ spaceTimeSet Ω I, F z = 0 := by
    intro z hz
    have hnot : parabolicHomeomorph z ∉ tsupport φ := by
      intro hzφ
      apply hz
      rw [show spaceTimeSet Ω I = parabolicHomeomorph ⁻¹' (Ω ×ˢ I) by
        rw [spaceTimeSet, parabolicHomeomorph_preimage]]
      exact hφΩ hzφ
    have hφzero : φ (z.1, z.2) = 0 :=
      image_eq_zero_of_notMem_tsupport hnot
    have hφzero' : φ z = 0 := by
      change φ (z.1, z.2) = 0
      exact hφzero
    have htzero : timePartial φ (z.1, z.2) = 0 :=
      timePartial_zero_of_not_mem_tsupport_public hφd hnot
    have htzero' : timePartial φ z = 0 := by
      change timePartial φ (z.1, z.2) = 0
      exact htzero
    have hszero (j : Fin 3) : spatialPartial φ j (z.1, z.2) = 0 :=
      spatialPartial_zero_of_not_mem_tsupport_public hφd hnot j
    have hszero' (j : Fin 3) : spatialPartial φ j z = 0 := by
      change spatialPartial φ j (z.1, z.2) = 0
      exact hszero j
    have hφpzero : φp z = 0 := by
      rw [hφp_eq]
      exact hφzero'
    simp only [localizedDivergenceG, hφpzero, zero_mul, mul_zero, Finset.sum_const_zero,
      neg_zero, sub_self, add_zero, htzero', hszero', hφzero', F]
  have hFglobal : (∫ z, F z) = 0 := by
    calc
      (∫ z, F z) = ∫ z in spaceTimeSet Ω I, F z := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hFzero]
      _ = ∫ z in spaceTimeSet Ω I, R z := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => hRF.symm ▸ rfl)
      _ = 0 := hS3zero
  have hLap := laplacian_transfer_of_sws hsol' hφ' hbox hφbox hψ'
  let A : ParabolicPoint → ℝ := fun z =>
    ∑ i, u z i * (φp z * timePartial (fun w => ψp w i) z)
  let B : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, u z i * (φp z * spatialSecondPartial
      (fun w => ψp w i) j j z)
  let G₀ : ParabolicPoint → ℝ := fun z =>
    ∑ i, localizedDivergenceG φ u Du p f z i * ψp z i
  let H₀ : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, localizedDivergenceH φ u p j z i * spatialPartial
      (fun w => ψp w i) j z
  let U : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, u z i * spatialPartial φp j z * spatialPartial
      (fun w => ψp w i) j z
  let K : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, (φp z * Du z i j + u z i * spatialPartial φp j z) *
      spatialPartial (fun w => ψp w i) j z
  have hA : Integrable A volume := by
    dsimp [A]
    rw [hφp_eq, hψp_eq]
    exact hLtime
  have hB : Integrable B volume := by
    dsimp [B]
    rw [hφp_eq, hψp_eq]
    exact hLsecond
  have hG₀ : Integrable G₀ volume := by
    dsimp [G₀]
    rw [hψp_eq]
    exact hG
  have hH₀ : Integrable H₀ volume := by
    dsimp [H₀]
    rw [hψp_eq]
    exact hH
  have hU : Integrable U volume := by
    have hU' : Integrable (fun z => ∑ i, ∑ j,
        u z i * spatialPartial φ j z * spatialPartial
          (fun w => ψ w i) j z) volume :=
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
        integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
          hHgrad i j))
    dsimp [U]
    rw [hφp_eq, hψp_eq]
    exact hU'
  have hK : Integrable K volume := by
    have hC : Integrable (fun z => ∑ i, ∑ j,
        Du z i j * (φp z * spatialPartial (fun w => ψp w i) j z)) volume := by
      rw [hφp_eq, hψp_eq]
      exact hLgrad
    have hCU := hC.add hU
    refine hCU.congr (Filter.Eventually.of_forall (fun z => ?_))
    dsimp [K, U]
    simp only [Finset.sum_add_distrib, add_mul]
    have hfirst :
        (∑ i, ∑ j, Du z i j * (φp z * spatialPartial
            (fun w => ψp w i) j z)) =
          ∑ i, ∑ j, φp z * Du z i j * spatialPartial
            (fun w => ψp w i) j z := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hfirst]
  have hLap' : (∫ z, B z) = -∫ z, K z := by
    have hLap₀ :
        (∫ z : ParabolicPoint, ∑ i, φp z * u z i * ∑ j,
          spatialSecondPartial (fun w => ψp w i) j j z) =
          -∫ z : ParabolicPoint, ∑ i, ∑ j,
            (φp z * Du z i j + u z i * spatialPartial φp j z) *
              spatialPartial (fun w => ψp w i) j z := by
      rw [Integration.volume_parabolicPoint_eq_prod]
      change (∫ z : Vec3 × ℝ, ∑ i, φ z * u z i * ∑ j,
          spatialSecondPartial (fun w : Vec3 × ℝ => ψ w i) j j z) =
        -∫ z : Vec3 × ℝ, ∑ i, ∑ j,
          (φ z * Du z i j + u z i * spatialPartial φ j z) *
            spatialPartial (fun w : Vec3 × ℝ => ψ w i) j z
      exact hLap
    calc
      (∫ z, B z) = ∫ z, ∑ i, φp z * u z i * ∑ j,
          spatialSecondPartial (fun w => ψp w i) j j z := by
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp [B]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = -∫ z, K z := by simpa only [K] using hLap₀
  have hdiag (z : ParabolicPoint) :
      (∑ i, ∑ j, (if i = j then p z * φp z else 0) *
        spatialPartial (fun w => ψp w i) j z) =
        ∑ i, p z * φp z * spatialPartial (fun w => ψp w i) i z := by
    classical
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hGpoint₀ (z : ParabolicPoint) (i : Fin 3) :
      localizedDivergenceG φ u Du p f z i * ψp z i =
        (timePartial φp z * u z i +
          ∑ j, u z i * u z j * spatialPartial φp j z -
          ∑ j, Du z i j * spatialPartial φp j z +
          p z * spatialPartial φp i z + f z i * φp z) * ψp z i := by
    rw [hφp_eq]
    rfl
  have hHpoint₀ (z : ParabolicPoint) (i j : Fin 3) :
      localizedDivergenceH φ u p j z i * spatialPartial
          (fun w => ψp w i) j z =
        (φp z * u z i * u z j + u z i * spatialPartial φp j z +
          if i = j then p z * φp z else 0) * spatialPartial
            (fun w => ψp w i) j z := by
    rw [hφp_eq]
    rfl
  have hpoint (z : ParabolicPoint) : F z + G₀ z + H₀ z = -A z + K z := by
    dsimp [F, A, G₀, H₀, K]
    simp_rw [hGpoint₀, hHpoint₀]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul,
      sub_mul, Finset.sum_mul, Finset.mul_sum]
    rw [hdiag]
    simp_rw [mul_assoc, mul_left_comm, mul_comm]
    abel
  have hpointInt :
      (∫ z, F z) + (∫ z, G₀ z) + (∫ z, H₀ z) =
        (-(∫ z, A z)) + (∫ z, K z) := by
    calc
      _ = (∫ z, F z + G₀ z) + (∫ z, H₀ z) := by
        rw [integral_add hF hG₀]
      _ = ∫ z, (F z + G₀ z) + H₀ z := by
        symm
        exact integral_add (hF.add hG₀) hH₀
      _ = ∫ z, -A z + K z := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = _ := by
        calc
          (∫ z, -A z + K z) = (∫ z, -A z) + (∫ z, K z) :=
            integral_add hA.neg hK
          _ = _ := by rw [integral_neg]
  have hrel : (-(∫ z, A z)) + (∫ z, K z) =
      (∫ z, G₀ z) + (∫ z, H₀ z) := by
    calc
      _ = (∫ z, F z) + (∫ z, G₀ z) + (∫ z, H₀ z) := hpointInt.symm
      _ = _ := by rw [hFglobal]; simp only [zero_add]
  have hHij (i j : Fin 3) : Integrable
      (fun z => localizedDivergenceH φ u p j z i * spatialPartial
        (fun w => ψ w i) j z) volume := by
    by_cases hij : i = j
    · subst j
      have hs := (hHconv i i).add (hHgrad i i)
      refine (hs.add (hHpress i)).congr
        (Filter.Eventually.of_forall (fun z => ?_))
      simp only [Pi.add_apply, localizedDivergenceH, ↓reduceIte]
      ring
    · have hs := (hHconv i j).add (hHgrad i j)
      refine hs.congr (Filter.Eventually.of_forall (fun z => ?_))
      simp only [Pi.add_apply, localizedDivergenceH, hij, ↓reduceIte, add_zero]
      ring
  have hHsum :
      (∫ z, H₀ z) = ∑ i, ∑ j, ∫ z,
        localizedDivergenceH φ u p j z i * spatialPartial
          (fun w => ψ w i) j z := by
    rw [show H₀ = fun z => ∑ i, ∑ j,
      localizedDivergenceH φ u p j z i * spatialPartial
        (fun w => ψ w i) j z by
      funext z
      dsimp [H₀]
      rw [hψp_eq]]
    change (∫ z, ∑ i, ∑ j,
      localizedDivergenceH φ u p j z i * spatialPartial
        (fun w => ψ w i) j z) = _
    rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))]
      intro j hj
      exact hHij i j
    · intro i hi
      exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _ => hHij i j)
  calc
    (∫ z, ∑ i, localizedVelocity (show ParabolicPoint → ℝ from φ) u z i *
        (-(timePartial (fun w => ψ w i) z) -
          ∑ j, spatialSecondPartial (fun w => ψ w i) j j z)) =
        (-(∫ z, A z)) - (∫ z, B z) := by
      rw [show (fun z => ∑ i, localizedVelocity
          (show ParabolicPoint → ℝ from φ) u z i *
          (-(timePartial (fun w => ψ w i) z) -
            ∑ j, spatialSecondPartial (fun w => ψ w i) j j z)) =
          (fun z => -A z - B z) by
        funext z
        rw [← hφp_eq, ← hψp_eq]
        dsimp [localizedVelocity, A, B]
        change (∑ x, (φp z * u z x) *
            (-(timePartial (fun w => ψp w x) z) -
              ∑ j, spatialSecondPartial (fun w => ψp w x) j j z)) =
          -∑ x, u z x * (φp z * timePartial (fun w => ψp w x) z) -
            ∑ x, ∑ j, u z x * (φp z * spatialSecondPartial
              (fun w => ψp w x) j j z)
        simp_rw [mul_sub, mul_neg, Finset.mul_sum]
        simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
        ring_nf]
      calc
        (∫ z, -A z - B z) = (∫ z, -A z) - (∫ z, B z) :=
          integral_sub hA.neg hB
        _ = (-(∫ z, A z)) - (∫ z, B z) := by rw [integral_neg]
    _ = (-(∫ z, A z)) + (∫ z, K z) := by rw [hLap']; ring_nf
    _ = (∫ z, G₀ z) + (∫ z, H₀ z) := hrel
    _ = (∫ z, ∑ i, localizedDivergenceG φ u Du p f z i * ψ z i) +
        ∑ i, ∑ j, ∫ z, localizedDivergenceH φ u p j z i *
          spatialPartial (fun w => ψ w i) j z := by
      rw [hHsum]
      congr 1
end CKN.Core.Step3
