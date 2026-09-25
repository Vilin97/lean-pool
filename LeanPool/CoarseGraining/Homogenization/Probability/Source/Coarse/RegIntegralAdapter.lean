/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.SmoothSigma

/-!
# Coarse-to-regular integral adapter

This module compares the source coarse integral sigma algebra with the smooth
integral sigma algebra on regular coefficient fields.  It deliberately does
not equip the adapter with measurability into the canonical regular carrier.
-/

@[expose] public section

namespace Homogenization.Source.Coarse

open MeasureTheory

private theorem continuous_euclideanNorm {d : ℕ} :
    Continuous (euclideanNorm (d := d)) := by
  change Continuous (fun x : Vec d => euclideanNorm x)
  simp_rw [euclideanNorm_eq_norm_ofVec]
  exact (PiLp.continuous_toLp 2 fun _ : Fin d => ℝ).norm

private theorem locallyIntegrable_coarse_entry {d : ℕ} (a : Carrier d)
    (i j : Fin d) : LocallyIntegrable (fun x : Vec d => a x i j) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_euclideanNorm.continuousOn
  let R : ℝ := max 1 (C + 1)
  have hR : 1 ≤ R := le_max_left _ _
  obtain ⟨ε, hε, hεone, hEll⟩ := a.2.2 R hR
  refine Measure.integrableOn_of_bounded (M := ε⁻¹) (hK.measure_lt_top).ne
    (a.2.1 i j).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  have hxC : euclideanNorm x ≤ C := by
    have h := hC x hx
    simpa only [Real.norm_eq_abs] using le_trans (le_abs_self _) h
  have hxR : x ∈ euclideanBall R := by
    change euclideanNorm x < max 1 (C + 1)
    exact hxC.trans_lt ((lt_add_one C).trans_le (le_max_right _ _))
  have hentry := abs_apply_le_of_isEllipticMatrix (hEll x hxR) i j
  simpa [Real.norm_eq_abs] using hentry

/-- The total regular-field realization of a coarse source carrier. -/
def coarseToRegular {d : ℕ} (a : Carrier d) : RegCoeffField d where
  toFun := a
  entry_measurable := a.2.1
  entry_locInt := locallyIntegrable_coarse_entry a

/-- The coarse-to-regular realization preserves every literal field value. -/
@[simp] theorem coarseToRegular_apply {d : ℕ} (a : Carrier d) (x : Vec d) :
    coarseToRegular a x = a x :=
  rfl

private theorem entryTestR_coarseToRegular_eq_bilinearTest {d : ℕ}
    (i j : Fin d) (φ : Vec d → ℝ) (a : Carrier d) :
    entryTestR i j φ (coarseToRegular a) =
      bilinearTest (Pi.single j 1) (Pi.single i 1) φ a := by
  unfold entryTestR bilinearTest
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp [vecDot, matVecMul, Pi.single_apply]

private noncomputable def regularBilinearTest {d : ℕ} (e e' : Vec d)
    (φ : Vec d → ℝ) (a : RegCoeffField d) : ℝ :=
  ∫ x, vecDot e' (matVecMul (a x) e) * φ x ∂volume

private theorem regularBilinearTest_eq_sum_entryTestR {d : ℕ}
    (e e' : Vec d) (φ : Vec d → ℝ) (hφ : SmoothCompactProbe φ)
    (a : RegCoeffField d) :
    regularBilinearTest e e' φ a =
      ∑ i, ∑ j, (e' i * e j) * entryTestR i j φ a := by
  have hprobe : IsProbeR φ := IsProbeR.of_smooth hφ.smooth hφ.compact
  have hpoint : ∀ x : Vec d,
      vecDot e' (matVecMul (a x) e) * φ x =
        ∑ i, ∑ j, (e' i * e j) * (a x i j * φ x) := by
    intro x
    unfold vecDot matVecMul
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold regularBilinearTest
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      rfl
    · intro j _
      exact (integrable_entry_mul_probe i j hprobe a).const_mul (e' i * e j)
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact (integrable_entry_mul_probe i j hprobe a).const_mul (e' i * e j)

private theorem measurable_regularBilinearTest_smooth {d : ℕ} {U : Set (Vec d)}
    (e e' : Vec d) (φ : Vec d → ℝ) (hφ : SmoothCompactProbe φ)
    (hφU : tsupport φ ⊆ U) :
    @Measurable (RegCoeffField d) ℝ (SmoothLocalSigmaR U) _
      (regularBilinearTest e e' φ) := by
  have hentry : ∀ i j : Fin d,
      @Measurable (RegCoeffField d) ℝ (SmoothLocalSigmaR U) _ (entryTestR i j φ) := by
    intro i j t ht
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨i, j, φ, hφ.smooth, hφ.compact, hφU, t, ht, rfl⟩
  have hfun : regularBilinearTest e e' φ =
      fun a => ∑ i, ∑ j, (e' i * e j) * entryTestR i j φ a := by
    funext a
    exact regularBilinearTest_eq_sum_entryTestR e e' φ hφ a
  rw [hfun]
  refine Finset.measurable_sum (s := Finset.univ) (f := fun i =>
    fun a => ∑ j, (e' i * e j) * entryTestR i j φ a) ?_
  intro i _
  refine Finset.measurable_sum (s := Finset.univ) (f := fun j =>
    fun a => (e' i * e j) * entryTestR i j φ a) ?_
  intro j _
  exact (hentry i j).const_mul (e' i * e j)

/-- The coarse-to-regular realization is measurable from coarse local integral
information into the smooth regular local integral sigma algebra. -/
theorem measurable_coarseToRegular_smoothLocal {d : ℕ} (U : Set (Vec d))
    (hU : MeasurableSet U) :
    @Measurable (Carrier d) (RegCoeffField d) (localSigma U hU)
      (SmoothLocalSigmaR U) coarseToRegular := by
  let : MeasurableSpace (Carrier d) := localSigma U hU
  let : MeasurableSpace (RegCoeffField d) := SmoothLocalSigmaR U
  apply measurable_generateFrom
  rintro s ⟨i, j, φ, hφsmooth, hφcompact, hφU, ⟨t, ht, rfl⟩⟩
  change MeasurableSet ((fun a : Carrier d => entryTestR i j φ (coarseToRegular a)) ⁻¹' t)
  have hfun : (fun a : Carrier d => entryTestR i j φ (coarseToRegular a)) =
      bilinearTest (Pi.single j 1) (Pi.single i 1) φ := by
    funext a
    exact entryTestR_coarseToRegular_eq_bilinearTest i j φ a
  rw [hfun]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨Pi.single j 1, Pi.single i 1, φ, ⟨hφsmooth, hφcompact⟩, hφU, t, ht, rfl⟩

/-- The coarse local integral sigma algebra is exactly the pullback of the
smooth compact-support integral sigma algebra on regular coefficient fields. -/
theorem coarseLocalSigma_eq_comap_smoothLocalSigmaR {d : ℕ} (U : Set (Vec d))
    (hU : MeasurableSet U) :
    localSigma U hU =
      MeasurableSpace.comap coarseToRegular (SmoothLocalSigmaR U) := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨e, e', φ, hφ, hφU, t, ht, rfl⟩
    let q : Set (RegCoeffField d) := regularBilinearTest e e' φ ⁻¹' t
    have hq : @MeasurableSet (RegCoeffField d) (SmoothLocalSigmaR U) q :=
      measurable_regularBilinearTest_smooth e e' φ hφ hφU ht
    have hfun : bilinearTest e e' φ = regularBilinearTest e e' φ ∘ coarseToRegular := by
      funext a
      rfl
    rw [hfun]
    exact MeasurableSpace.measurableSet_comap.mpr ⟨q, hq, rfl⟩
  · exact (measurable_coarseToRegular_smoothLocal U hU).comap_le

/-- The global coarse integral sigma algebra is the pullback of the global
smooth regular integral sigma algebra. -/
theorem globalSigma_eq_comap_smoothGlobalSigmaR (d : ℕ) :
    globalSigma d =
      MeasurableSpace.comap coarseToRegular (SmoothGlobalSigmaR d) := by
  simpa [globalSigma, SmoothGlobalSigmaR] using
    coarseLocalSigma_eq_comap_smoothLocalSigmaR (d := d) Set.univ MeasurableSet.univ

/-- The coarse-to-regular realization is measurable for the global smooth
integral sigma algebras. -/
theorem measurable_coarseToRegular_smoothGlobal {d : ℕ} :
    @Measurable (Carrier d) (RegCoeffField d) (globalSigma d)
      (SmoothGlobalSigmaR d) coarseToRegular := by
  simpa [globalSigma, SmoothGlobalSigmaR] using!
    measurable_coarseToRegular_smoothLocal (d := d) Set.univ MeasurableSet.univ

/-- Coarse local integral information is measurable in the pullback of the
existing enriched regular local sigma algebra. -/
theorem coarseLocalSigma_le_comap_localSigmaR {d : ℕ} (U : Set (Vec d))
    (hU : MeasurableSet U) :
    localSigma U hU ≤ MeasurableSpace.comap coarseToRegular (LocalSigmaR U) := by
  rw [coarseLocalSigma_eq_comap_smoothLocalSigmaR U hU]
  exact MeasurableSpace.comap_mono (smoothLocalSigmaR_le_localSigmaR U)

end Homogenization.Source.Coarse
