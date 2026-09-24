/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationTested
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.DuhamelAdjoint
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationDuhamelKernels

/-!
# Localized Equation Duhamel

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.Step3
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential

lemma localized_divergence_scalar_tested_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    (i : Fin 3) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ) :
    (∫ z, localizedVelocity (show ParabolicPoint → ℝ from φ) u z i *
        (-(timePartial ψ z) - ∑ j, spatialSecondPartial ψ j j z)) =
      (∫ z, localizedDivergenceG φ u Du p f z i * ψ z) +
        ∑ j, ∫ z, localizedDivergenceH φ u p j z i * spatialPartial ψ j z := by
  let Ψ : Vec3 × ℝ → Vec3 := fun z k => if k = i then ψ z else 0
  have hΨd : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    rw [contDiff_pi]
    intro k
    by_cases hki : k = i
    · subst k
      simpa [Ψ] using hψ.1
    · change ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => if k = i then ψ z else 0)
      simp [hki]
      exact contDiff_const
  have hΨc : HasCompactSupport Ψ := by
    apply HasCompactSupport.of_support_subset_isCompact hψ.2.1.isCompact
    intro z hz
    by_contra hnot
    apply hz
    have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport hnot
    funext k
    simp [Ψ, hzero]
  have hΨ : Ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ := by
    refine ⟨hΨd, hΨc, ?_⟩
    simp [spaceTimeSet]
  have h := localized_divergence_tested_of_sws hsol hφ hbox hφbox hΨ
  have htime (k : Fin 3) :
      timePartial (fun w => if k = i then ψ w else 0) =
        fun z => if k = i then timePartial ψ z else 0 := by
    funext z
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
    · simp [hki, timePartial]
  have hsecond (k j : Fin 3) :
      spatialSecondPartial (fun w => if k = i then ψ w else 0) j j =
        fun z => if k = i then spatialSecondPartial ψ j j z else 0 := by
    funext z
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
    · simp [hki, spatialSecondPartial, spatialPartial]
  have hspatial (k j : Fin 3) :
      spatialPartial (fun w => if k = i then ψ w else 0) j =
        fun z => if k = i then spatialPartial ψ j z else 0 := by
    funext z
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
    · simp [hki, spatialPartial]
  simp only [Ψ] at h
  simp_rw [htime, hsecond, hspatial] at h
  classical
  simp only [Finset.mul_sum, mul_sub, mul_neg, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib] at h
  simp [Finset.sum_ite_eq', Finset.sum_const_zero, mul_zero] at h
  have hleft :
      (∫ z, localizedVelocity φ u z i *
        (-timePartial ψ z - ∑ j, spatialSecondPartial ψ j j z)) =
        ∫ z, -(localizedVelocity φ u z i *
          timePartial ψ z) - ∑ j, localizedVelocity
            φ u z i * spatialSecondPartial ψ j j z := by
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [mul_sub, Finset.mul_sum, mul_neg]
  have hright :
      (∑ x, ∑ j, ∫ z, if x = i then
        localizedDivergenceH φ u p j z x * spatialPartial ψ j z else 0) =
        ∑ j, ∫ z, localizedDivergenceH φ u p j z i * spatialPartial ψ j z := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    have hterm (x : Fin 3) :
        (∫ z, if x = i then
          localizedDivergenceH φ u p j z x * spatialPartial ψ j z else 0) =
          if x = i then
            ∫ z, localizedDivergenceH φ u p j z i * spatialPartial ψ j z
          else 0 := by
      by_cases hxi : x = i
      · subst x
        simp
      · simp [hxi]
    simp_rw [hterm]
    simp
  rw [hright] at h
  exact hleft.trans h

theorem localized_divergence_source_data_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J) :
    (∀ i : Fin 3, Integrable (fun z =>
      localizedVelocity (show ParabolicPoint → ℝ from φ) u z i) volume) ∧
    (∀ i : Fin 3, Integrable
      (fun z => localizedDivergenceG φ u Du p f z i) volume) ∧
    (∀ j i : Fin 3, Integrable
      (fun z => localizedDivergenceH φ u p j z i) volume) ∧
    HasCompactSupport (localizedVelocity (show ParabolicPoint → ℝ from φ) u) ∧
    (∀ i : Fin 3, HasCompactSupport
      (fun z => localizedDivergenceG φ u Du p f z i)) ∧
    (∀ j i : Fin 3, HasCompactSupport
      (fun z => localizedDivergenceH φ u p j z i)) := by
  rcases hsol with ⟨hΩ, hI, hIord, hq, hfSol, hdata, hS2, hS3, hS4⟩
  rcases hφ with ⟨hφd, hφc, hφΩ⟩
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
  have hfComp (i : Fin 3) : MemLp (fun z => f z i) (ENNReal.ofReal q) μ :=
    hf.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hφtime : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial φ z) := timePartial_contDiff_full hφd
  have hφtime_c : HasCompactSupport
      (fun z : Vec3 × ℝ => timePartial φ z) := by
    apply HasCompactSupport.of_support_subset_isCompact hφc.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact timePartial_zero_of_not_mem_tsupport_public hφd hnot
  have hφtime_ts : tsupport (fun z : Vec3 × ℝ => timePartial φ z) ⊆ tsupport φ := by
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
  have hbox_factor {a : ParabolicPoint → ℝ}
      (ha : Integrable a μ) {α : Vec3 × ℝ → ℝ}
      (hαc : HasCompactSupport α) (hαts : tsupport α ⊆ tsupport φ)
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
      (by simpa [μ] using ha) (hα.mul hb) hbc hbs
  have hUi (i : Fin 3) : Integrable (fun z => u z i) μ :=
    (huComp i).integrable (by norm_num)
  have hDij (i j : Fin 3) : Integrable (fun z => Du z i j) μ :=
    (hDuComp i j).integrable (by norm_num)
  have hUU (i j : Fin 3) : Integrable (fun z => u z i * u z j) μ :=
    (huComp i).integrable_mul (huComp j)
  have hGtime (i : Fin 3) : Integrable
      (fun z => u z i * timePartial φ z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hUi i) hφtime_c hφtime_ts hφtime.continuous continuous_const
    simpa using h
  have hV (i : Fin 3) : Integrable (fun z =>
      localizedVelocity (show ParabolicPoint → ℝ from φ) u z i) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hUi i) hφc (by exact subset_rfl) hφd.continuous continuous_const
    simpa [localizedVelocity, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h
  have hGconv (i j : Fin 3) : Integrable
      (fun z => u z i * u z j * spatialPartial φ j z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hUU i j) (hφsp_c j) (hφsp_ts j) (hφsp j).continuous continuous_const
    simpa using h
  have hGgrad (i j : Fin 3) : Integrable
      (fun z => Du z i j * spatialPartial φ j z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hDij i j) (hφsp_c j) (hφsp_ts j) (hφsp j).continuous continuous_const
    simpa using h
  have hGpress (i : Fin 3) : Integrable
      (fun z => p z * spatialPartial φ i z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      hpInt (hφsp_c i) (hφsp_ts i) (hφsp i).continuous continuous_const
    simpa using h
  have hGforce (i : Fin 3) : Integrable
      (fun z => f z i * φ z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      ((hfComp i).integrable hq1) hφc (by exact subset_rfl)
      hφd.continuous continuous_const
    simpa using h
  have hG (i : Fin 3) : Integrable
      (fun z => localizedDivergenceG φ u Du p f z i) volume := by
    have hsum := (hGtime i).add
      ((integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _ => hGconv i j)).sub
        ((integrable_finsetSum (Finset.univ : Finset (Fin 3))
          (fun j _ => hGgrad i j)).sub ((hGpress i).add (hGforce i))))
    refine hsum.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [localizedDivergenceG, Pi.add_apply, Pi.sub_apply]
    ring
  have hHconv (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => φ z * u z i * u z j) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hUU i j) hφc (by exact subset_rfl) hφd.continuous continuous_const
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hHgrad (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => u z i * spatialPartial φ j z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hUi i) (hφsp_c j) (hφsp_ts j) (hφsp j).continuous continuous_const
    simpa using h
  have hHpress (i : Fin 3) : Integrable
      (fun z : ParabolicPoint => p z * φ z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      hpInt hφc (by exact subset_rfl) hφd.continuous continuous_const
    simpa using h
  have hH (j i : Fin 3) : Integrable
      (fun z => localizedDivergenceH φ u p j z i) volume := by
    by_cases hij : i = j
    · subst j
      have hsum := (hHconv i i).add (hHgrad i i)
      refine (hsum.add (hHpress i)).congr
        (Filter.Eventually.of_forall (fun z => ?_))
      simp [localizedDivergenceH]
    · have hsum := (hHconv i j).add (hHgrad i j)
      refine hsum.congr (Filter.Eventually.of_forall (fun z => ?_))
      simp [localizedDivergenceH, hij]
  let Kφ : Set ParabolicPoint := parabolicHomeomorph ⁻¹' tsupport φ
  have hKφ : IsCompact Kφ := parabolicHomeomorph.isCompact_preimage.2 hφc.isCompact
  have hsupport_of_phi {V : Type} [Zero V] (v : ParabolicPoint → V)
      (hzv : ∀ z, parabolicHomeomorph z ∉ tsupport φ → v z = 0) :
      HasCompactSupport v := by
    apply HasCompactSupport.of_support_subset_isCompact hKφ
    intro z hz
    by_contra hnot
    apply hz
    apply hzv z
    simpa only [Kφ, Set.mem_preimage, parabolicHomeomorph_apply] using hnot
  have hφzero (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : φ z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa [parabolicHomeomorph_apply] using hz
    change φ (z.1, z.2) = 0
    exact image_eq_zero_of_notMem_tsupport hz'
  have htszero (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : timePartial φ z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa [parabolicHomeomorph_apply] using hz
    exact timePartial_zero_of_not_mem_tsupport_public hφd hz'
  have hspzero (j : Fin 3) (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : spatialPartial φ j z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa [parabolicHomeomorph_apply] using hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hφd hz' j
  have hvSupport : HasCompactSupport
      (localizedVelocity (show ParabolicPoint → ℝ from φ) u) := by
    apply hsupport_of_phi
    intro z hz
    funext i
    simp [localizedVelocity, hφzero z hz]
  have hGSupport (i : Fin 3) : HasCompactSupport
      (fun z => localizedDivergenceG φ u Du p f z i) := by
    apply hsupport_of_phi
    intro z hz
    dsimp [localizedDivergenceG]
    rw [hφzero z hz, htszero z hz]
    have hsum1 : (∑ j, u z i * u z j * spatialPartial φ j z) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hspzero j z hz]
      simp
    have hsum2 : (∑ j, Du z i j * spatialPartial φ j z) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hspzero j z hz]
      simp
    rw [hsum1, hsum2, hspzero i z hz]
    simp
  have hHSupport (j i : Fin 3) : HasCompactSupport
      (fun z => localizedDivergenceH φ u p j z i) := by
    apply hsupport_of_phi
    intro z hz
    dsimp [localizedDivergenceH]
    rw [hφzero z hz, hspzero j z hz]
    simp
  exact ⟨hV, hG, hH, hvSupport, hGSupport, hHSupport⟩

noncomputable def duhamel_support_data_of_compact_support
    {v g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    (hv : HasCompactSupport v)
    (hg : ∀ i : Fin 3, HasCompactSupport (fun z => g z i))
    (hh : ∀ j i : Fin 3, HasCompactSupport (fun z => h j z i)) :
    DuhamelSupportData v g h := by
  have hvi (i : Fin 3) : HasCompactSupport (fun z => v z i) := by
    apply HasCompactSupport.of_support_subset_isCompact hv.isCompact
    intro z hz
    by_contra hnot
    apply hz
    have hvzero : v z = 0 := image_eq_zero_of_notMem_tsupport hnot
    exact congrFun hvzero i
  let K : Set ParabolicPoint :=
    (⋃ i : Fin 3, tsupport (fun z => v z i)) ∪
      (⋃ i : Fin 3, tsupport (fun z => g z i)) ∪
      (⋃ j : Fin 3, ⋃ i : Fin 3, tsupport (fun z => h j z i))
  have hK : IsCompact K := by
    dsimp [K]
    have hV : IsCompact (⋃ i : Fin 3, tsupport (fun z => v z i)) :=
      isCompact_iUnion (fun i : Fin 3 => (hvi i).isCompact)
    have hG : IsCompact (⋃ i : Fin 3, tsupport (fun z => g z i)) :=
      isCompact_iUnion (fun i : Fin 3 => (hg i).isCompact)
    have hH : IsCompact (⋃ j : Fin 3, ⋃ i : Fin 3,
        tsupport (fun z => h j z i)) :=
      isCompact_iUnion (fun j : Fin 3 =>
        isCompact_iUnion (fun i : Fin 3 => (hh j i).isCompact))
    exact hV.union hG |>.union hH
  have hKx : IsCompact (K.image (fun z : ParabolicPoint =>
      vec3EuclideanNorm z.1)) := by
    have hnorm : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact hK.image (hnorm.comp continuous_fst_parabolicPoint)
  have hKt : IsCompact (K.image (fun z : ParabolicPoint => z.2)) :=
    hK.image continuous_snd_parabolicPoint
  let C : ℝ := Classical.choose hKx.bddAbove
  have hC : ∀ x : ℝ, x ∈ K.image (fun z : ParabolicPoint =>
      vec3EuclideanNorm z.1) → x ≤ C := Classical.choose_spec hKx.bddAbove
  let a : ℝ := Classical.choose hKt.bddBelow
  have ha : ∀ x : ℝ, x ∈ K.image (fun z : ParabolicPoint => z.2) → a ≤ x :=
    Classical.choose_spec hKt.bddBelow
  let b : ℝ := Classical.choose hKt.bddAbove
  have hb : ∀ x : ℝ, x ∈ K.image (fun z : ParabolicPoint => z.2) → x ≤ b :=
    Classical.choose_spec hKt.bddAbove
  let r : ℝ := max (C + 1) (|b - a| + 2)
  let R : ℝ := r + 1
  let t₀ : ℝ := b + 1
  have hr : 0 ≤ r := by
    dsimp [r]
    exact le_max_of_le_right (by positivity)
  have hrR : r < R := by
    dsimp [R]
    linarith only
  have hrtime : b - a + 1 < r ^ 2 := by
    have habs : b - a ≤ |b - a| := le_abs_self _
    have hrbig : |b - a| + 2 ≤ r := le_max_right _ _
    have hrone : 1 < r := by
      have : 0 ≤ |b - a| := abs_nonneg _
      linarith only [this, hrbig]
    nlinarith only [habs, hrbig, hrone, sq_nonneg (r - 1)]
  have hKsupport : ∀ z ∈ K,
      z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ 2) t₀ := by
    intro z hz
    have hzC : vec3EuclideanNorm z.1 ≤ C :=
      hC (vec3EuclideanNorm z.1) ⟨z, hz, rfl⟩
    have hza : a ≤ z.2 := ha z.2 ⟨z, hz, rfl⟩
    have hzb : z.2 ≤ b := hb z.2 ⟨z, hz, rfl⟩
    have hrpos : 0 < r := by
      dsimp [r]
      exact lt_of_lt_of_le (by positivity) (le_max_right _ _)
    refine ⟨?_, ?_⟩
    · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hrpos).2
      simpa [r, vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
        CKN.vecDot, pow_two] using
        (hzC.trans_lt (lt_of_lt_of_le
          (by linarith only [(zero_lt_one : (0 : ℝ) < 1)] : C < C + 1)
          (le_max_left _ _)))
    · constructor
      · dsimp [t₀]
        linarith only [hrtime, hza]
      · dsimp [t₀]
        linarith only [hzb]
  refine ⟨r, R, t₀, hr, hrR, ?_, ?_, ?_⟩
  · intro i z hz
    exact hKsupport z (Or.inl (Or.inl (mem_iUnion.2 ⟨i, hz⟩)))
  · intro i z hz
    exact hKsupport z (Or.inl (Or.inr (mem_iUnion.2 ⟨i, hz⟩)))
  · intro j i z hz
    exact hKsupport z (Or.inr (mem_iUnion.2 ⟨j,
      mem_iUnion.2 ⟨i, hz⟩⟩))

private lemma parabolic_sub_measurePreserving (y : ParabolicPoint) :
    MeasurePreserving (fun x : ParabolicPoint => pointSub x y)
      (volume : Measure ParabolicPoint) volume := by
  have h := (measurePreserving_add_right (volume : Measure Vec3) (-y.1)).prod
    (measurePreserving_add_right (volume : Measure ℝ) (-y.2))
  rw [Integration.volume_parabolicPoint_eq_prod]
  change MeasurePreserving (fun x : Vec3 × ℝ =>
    (x.1 + -y.1, x.2 + -y.2)) (volume.prod volume) (volume.prod volume)
  convert h using 1
  rfl

private lemma parabolic_integrableOn_shift_of_locallyIntegrable
    {k : ParabolicPoint → ℝ} (hk : LocallyIntegrable k volume)
    {K : Set ParabolicPoint} (hK : IsCompact K) (y : ParabolicPoint) :
    IntegrableOn (fun x : ParabolicPoint => k (pointSub x y)) K volume := by
  let S : Set ParabolicPoint := (fun x : ParabolicPoint => pointSub x y) '' K
  have hS : IsCompact S := by
    apply hK.image
    change Continuous (fun x : ParabolicPoint =>
      parabolicHomeomorph.symm (x.1 - y.1, x.2 - y.2))
    apply parabolicHomeomorph.continuous_symm.comp
    exact ((continuous_fst_parabolicPoint : Continuous (fun x : ParabolicPoint => x.1)).sub
      (continuous_const : Continuous (fun _ : ParabolicPoint => y.1))).prodMk
      ((continuous_snd_parabolicPoint : Continuous (fun x : ParabolicPoint => x.2)).sub
        (continuous_const : Continuous (fun _ : ParabolicPoint => y.2)))
  have hkS : IntegrableOn k S volume := hk.integrableOn_isCompact hS
  have hInd := hkS.integrable_indicator hS.measurableSet
  have hcomp := (parabolic_sub_measurePreserving y).integrable_comp
    hInd.aestronglyMeasurable |>.mpr hInd
  have heq : (fun x : ParabolicPoint =>
      S.indicator k (pointSub x y)) =
      (fun x : ParabolicPoint => K.indicator
        (fun z : ParabolicPoint => k (pointSub z y)) x) := by
    funext x
    by_cases hx : x ∈ K
    · have hxy : pointSub x y ∈ S := ⟨x, hx, rfl⟩
      simp only [Set.indicator_of_mem hxy, Set.indicator_of_mem hx]
    · have hxy : pointSub x y ∉ S := by
        rintro ⟨z, hz, hzx⟩
        have hzx' : z = x := by
          apply Prod.ext
          · exact sub_left_injective (b := y.1)
              (by simpa [pointSub] using congrArg Prod.fst hzx)
          · exact sub_left_injective (b := y.2)
              (by simpa [pointSub] using congrArg Prod.snd hzx)
        exact hx (by simpa only [hzx'] using hz)
      simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxy]
  have hcomp' : Integrable (fun x : ParabolicPoint =>
      S.indicator k (pointSub x y)) volume := by
    change Integrable (fun x : ParabolicPoint =>
      S.indicator k (pointSub x y)) volume at hcomp
    exact hcomp
  rw [heq] at hcomp'
  exact (integrable_indicator_iff hK.measurableSet).mp hcomp'

private lemma parabolic_setIntegral_norm_shift_le
    {k : ParabolicPoint → ℝ} (hk : LocallyIntegrable k volume)
    {K L : Set ParabolicPoint} (hK : IsCompact K) (hL : IsCompact L)
    (y : ParabolicPoint)
    (hsub : (fun x : ParabolicPoint => pointSub x y) '' K ⊆ L) :
    (∫ x in K, ‖k (pointSub x y)‖) ≤ ∫ z in L, ‖k z‖ := by
  have hkn : LocallyIntegrable (fun z : ParabolicPoint => ‖k z‖) volume := by
    have hkOn : LocallyIntegrableOn k (Set.univ : Set ParabolicPoint) volume :=
      locallyIntegrableOn_univ.mpr hk
    exact locallyIntegrableOn_univ.mp hkOn.norm
  have hshift : IntegrableOn (fun x : ParabolicPoint =>
      ‖k (pointSub x y)‖) K volume := parabolic_integrableOn_shift_of_locallyIntegrable
        hkn hK y
  have hleft := hshift.integrable_indicator hK.measurableSet
  have hright0 := hkn.integrableOn_isCompact hL
  have hright := hright0.integrable_indicator hL.measurableSet
  have hcomp := (parabolic_sub_measurePreserving y).integrable_comp
    hright.aestronglyMeasurable |>.mpr hright
  have hcomp' : Integrable (fun x : ParabolicPoint =>
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y)) volume := by
    change Integrable (fun x : ParabolicPoint =>
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y)) volume at hcomp
    exact hcomp
  have hle : ∀ᵐ x : ParabolicPoint, K.indicator
      (fun z : ParabolicPoint => ‖k (pointSub z y)‖) x ≤
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y) := by
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · have hxy : pointSub x y ∈ L := hsub ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxy]
    · rw [Set.indicator_of_notMem hx]
      by_cases hLxy : pointSub x y ∈ L
      · rw [Set.indicator_of_mem hLxy]
        exact norm_nonneg _
      · rw [Set.indicator_of_notMem hLxy]
  have hint := integral_mono_ae hleft hcomp' hle
  rw [integral_indicator hK.measurableSet] at hint
  let e := (Homeomorph.subRight y.1).prodCongr (Homeomorph.subRight y.2)
  have htrans := (parabolic_sub_measurePreserving y).integral_comp
    e.measurableEmbedding (L.indicator (fun z : ParabolicPoint => ‖k z‖))
  have htrans' : (∫ x : ParabolicPoint,
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y)) =
      ∫ z : ParabolicPoint, L.indicator (fun z : ParabolicPoint => ‖k z‖) z := by
    simpa [e, pointSub] using htrans
  rw [htrans', integral_indicator hL.measurableSet] at hint
  exact hint

private lemma parabolic_potential_integrableOn_of_compact_integrable
    {k g : ParabolicPoint → ℝ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) (hg : Integrable g volume) (hgc : HasCompactSupport g)
    {K : Set ParabolicPoint} (hK : IsCompact K) :
    IntegrableOn (fun x : ParabolicPoint =>
      ∫ y, k (pointSub x y) * g y) K volume := by
  let S : Set ParabolicPoint := tsupport g
  have hS : IsCompact S := hgc.isCompact
  let L : Set ParabolicPoint :=
    (fun z : ParabolicPoint × ParabolicPoint =>
      pointSub z.1 z.2) '' (K ×ˢ S)
  have hL : IsCompact L := by
    apply (hK.prod hS).image
    change Continuous (fun z : ParabolicPoint × ParabolicPoint =>
      parabolicHomeomorph.symm (z.1.1 - z.2.1, z.1.2 - z.2.2))
    apply parabolicHomeomorph.continuous_symm.comp
    have h11 : Continuous (fun z : ParabolicPoint × ParabolicPoint => z.1.1) :=
      continuous_fst_parabolicPoint.comp continuous_fst
    have h21 : Continuous (fun z : ParabolicPoint × ParabolicPoint => z.2.1) :=
      continuous_fst_parabolicPoint.comp continuous_snd
    have h12 : Continuous (fun z : ParabolicPoint × ParabolicPoint => z.1.2) :=
      continuous_snd_parabolicPoint.comp continuous_fst
    have h22 : Continuous (fun z : ParabolicPoint × ParabolicPoint => z.2.2) :=
      continuous_snd_parabolicPoint.comp continuous_snd
    exact (h11.sub h21).prodMk (h12.sub h22)
  have hLInt : IntegrableOn (fun z : ParabolicPoint => ‖k z‖) L volume :=
    (hk.integrableOn_isCompact hL).norm
  let μ : Measure ParabolicPoint := volume.restrict K
  let F : ParabolicPoint × ParabolicPoint → ℝ :=
    fun z => k (pointSub z.1 z.2) * g z.2
  have hFmeas : AEStronglyMeasurable F (μ.prod volume) := by
    have hk' : Measurable (fun z : ParabolicPoint × ParabolicPoint =>
        k (pointSub z.1 z.2)) := by
      apply hkm.comp
      exact ((measurable_fst.fst : Measurable (fun z : ParabolicPoint × ParabolicPoint => z.1.1)).sub
        (measurable_snd.fst : Measurable (fun z : ParabolicPoint × ParabolicPoint => z.2.1))).prodMk
        ((measurable_fst.snd : Measurable (fun z : ParabolicPoint × ParabolicPoint => z.1.2)).sub
          (measurable_snd.snd : Measurable (fun z : ParabolicPoint × ParabolicPoint => z.2.2)))
    exact (hk'.aestronglyMeasurable.mul
      hg.aestronglyMeasurable.comp_snd)
  have hprod : Integrable F (μ.prod volume) := by
    apply (integrable_prod_iff' hFmeas).2
    constructor
    · filter_upwards [] with y
      have hshift := parabolic_integrableOn_shift_of_locallyIntegrable
        hk hK y
      have hmul := hshift.integrable.const_mul (g y)
      simpa only [F, Function.comp_apply, mul_comm] using hmul
    · have hmeas : AEStronglyMeasurable
          (fun y : ParabolicPoint => ∫ x, ‖F (x,y)‖ ∂μ) volume :=
        hFmeas.prod_swap.norm.integral_prod_right'
      have hmajor : Integrable (fun y : ParabolicPoint =>
          (∫ z in L, ‖k z‖) * ‖g y‖) volume :=
        hg.norm.const_mul _
      apply hmajor.mono hmeas
      filter_upwards [] with y
      by_cases hy : y ∈ S
      · have hsub : (fun x : ParabolicPoint => pointSub x y) '' K ⊆ L := by
          rintro z ⟨x, hx, rfl⟩
          exact ⟨⟨x,y⟩, ⟨hx, hy⟩, rfl⟩
        have hbound := parabolic_setIntegral_norm_shift_le hk hK hL y hsub
        dsimp [F, μ]
        rw [abs_of_nonneg (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => abs_nonneg _))]
        rw [abs_of_nonneg (mul_nonneg (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)) (abs_nonneg _))]
        simp_rw [abs_mul, mul_comm]
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
      · have hgy : g y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [F, hgy]
  have hpot := hprod.integral_prod_left
  change Integrable (fun x : ParabolicPoint =>
      ∫ y, k (pointSub x y) * g y) (volume.restrict K)
  exact hpot

def parabolicHomeomorphReal' : ParabolicPoint ≃ₜ Vec3 × ℝ :=
  parabolicHomeomorph

private lemma compact_parabolicMetricClosedBall' {z : ParabolicPoint} {r : ℝ} :
    IsCompact (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) := by
  let R : ℝ := max r (r ^ 2)
  have hprod : IsCompact (@Metric.closedBall (Vec3 × ℝ) inferInstance
      (parabolicHomeomorphReal' z) R) := isCompact_closedBall _ _
  have hsub : parabolicHomeomorphReal' ''
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) ⊆
      @Metric.closedBall (Vec3 × ℝ) inferInstance (parabolicHomeomorphReal' z) R := by
    rintro q ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, Prod.dist_eq]
    rw [Metric.mem_closedBall, dist_eq_parabolicDist] at hp
    rcases max_le_iff.mp hp with ⟨hspace, htime⟩
    have hsq : |p.2 - z.2| ≤ r ^ 2 := (Real.sqrt_le_iff.mp htime).2
    apply max_le
    · change dist p.1 z.1 ≤ R
      rw [dist_pi_le_iff (le_max_of_le_right (sq_nonneg r))]
      intro i
      have hspace' : ‖p.1 - z.1‖ ≤ r :=
        (CKN.space_norm_le_euclideanNorm (p.1 - z.1)).trans hspace
      simpa [Real.dist_eq, abs_sub_comm] using
        (le_trans (norm_le_pi_norm (p.1 - z.1) i)
          (hspace'.trans (le_max_left _ _)))
    · change |p.2 - z.2| ≤ R
      exact hsq.trans (le_max_right _ _)
  have himage : IsCompact (parabolicHomeomorphReal' ''
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)) := by
    apply hprod.of_isClosed_subset
    · exact parabolicHomeomorphReal'.isClosed_image.mpr isClosed_closedBall
    · exact hsub
  exact (parabolicHomeomorphReal'.isCompact_image).mp (by simpa using himage)

lemma parabolic_potential_locallyIntegrable_of_compact_integrable
    {k g : ParabolicPoint → ℝ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) (hg : Integrable g volume) (hgc : HasCompactSupport g) :
    LocallyIntegrable (fun x : ParabolicPoint =>
      ∫ y, k (pointSub x y) * g y) volume := by
  intro x
  let K : Set ParabolicPoint :=
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace x 1
  have hK : IsCompact K := compact_parabolicMetricClosedBall'
  have hpot := parabolic_potential_integrableOn_of_compact_integrable
    hk hkm hg hgc hK
  let U : Set ParabolicPoint :=
    @Metric.ball ParabolicPoint parabolicPseudoMetricSpace x 1
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hxU : x ∈ U := Metric.mem_ball_self (by norm_num)
  have hUK : U ⊆ K := Metric.ball_subset_closedBall
  exact ⟨U, hUopen.mem_nhds hxU, hpot.mono_set hUK⟩

end CKN.Core.Step3
