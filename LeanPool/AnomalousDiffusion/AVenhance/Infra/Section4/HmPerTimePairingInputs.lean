/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPerTimeAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPairingFubini
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPairingPrefix

/-! Pairing inputs for a positive-time Hm cell. Spacetime L² bounds are
converted to the time-slice data used by the regular and flux Cauchy
estimates. The time-continuity of the scalar pairings is kept as an explicit
interface; the actual-flow continuity lemmas can discharge it. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization

namespace AVenhance.Infra.Section4

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def HmPerTimePairingInputs.hmPairingClosedCube : Set (Vec 2) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem HmPerTimePairingInputs.hmPairingClosedCube_compact : IsCompact
    HmPerTimePairingInputs.hmPairingClosedCube :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem HmPerTimePairingInputs.hmPairingUnitCube_ae_eq_closedCube :
    AVenhance.unitCube =ᵐ[(volume : Measure (Vec 2))] HmPerTimePairingInputs.hmPairingClosedCube
        := by
  simpa [volume_pi, AVenhance.unitCube, HmPerTimePairingInputs.hmPairingClosedCube] using
    (Measure.univ_pi_Ioo_ae_eq_Icc
      (f := fun _ : Fin 2 => (0 : ℝ)) (g := fun _ : Fin 2 => (1 : ℝ)))

/-- Clamp time between two endpoints for the per-time Hm pairing. -/
def HmPerTimePairingInputs.hmPairingTimeClamp (a b t : ℝ) : ℝ := max a (min t b)

theorem HmPerTimePairingInputs.hmPairingTimeClamp_continuous (a b : ℝ) :
    Continuous (HmPerTimePairingInputs.hmPairingTimeClamp a b) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem HmPerTimePairingInputs.hmPairingTimeClamp_mem {a b t : ℝ} (hab : a ≤ b) :
    HmPerTimePairingInputs.hmPairingTimeClamp a b t ∈ Set.Icc a b := by
  constructor
  · exact le_max_left _ _
  · exact max_le_iff.mpr ⟨hab, min_le_right _ _⟩

theorem HmPerTimePairingInputs.hmPairingTimeClamp_eq {a b t : ℝ} (ht : t ∈ Set.Icc a b) :
    HmPerTimePairingInputs.hmPairingTimeClamp a b t = t := by
  simp [HmPerTimePairingInputs.hmPairingTimeClamp, ht.1, ht.2]

theorem HmPerTimePairingInputs.hm_spaceGrad_continuous_of_contDiff
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (AVenhance.spaceGrad f) := by
  apply continuous_pi_iff.mpr
  intro i
  change Continuous (fun x => fderiv ℝ f x (Homogenization.basisVec i))
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- Joint continuity of the scalar fields on a positive time cell implies
continuity of both time pairings. For the flux term, periodic integration by
parts rewrites the gradient--vector pairing as the integral of `F * div V`;
this uses only joint continuity of the divergence field. -/
theorem hm_pairing_continuity_of_joint_fields
    {F G : ℝ → Vec 2 → ℝ} {V : ℝ → Vec 2 → Vec 2}
    {a b : ℝ} (hab : a ≤ b)
    (hFJoint : ContinuousOn
      (fun p : ℝ × Vec 2 => F p.1 p.2)
      (Set.Icc a b ×ˢ (Set.univ : Set (Vec 2))))
    (hGJoint : ContinuousOn
      (fun p : ℝ × Vec 2 => G p.1 p.2)
      (Set.Icc a b ×ˢ (Set.univ : Set (Vec 2))))
    (hDivJoint : ContinuousOn
      (fun p : ℝ × Vec 2 => AVenhance.vecDiv (V p.1) p.2)
      (Set.Icc a b ×ˢ (Set.univ : Set (Vec 2))))
    (hFper : ∀ t, t ∈ Set.Icc a b → IsZ2Periodic (F t))
    (hVper : ∀ t, t ∈ Set.Icc a b → ∀ i : Fin 2,
      IsZ2Periodic (fun x => V t x i))
    (hF : ∀ t, t ∈ Set.Icc a b → ContDiff ℝ 1 (F t))
    (hV : ∀ t, t ∈ Set.Icc a b → ContDiff ℝ 1 (V t)) :
    ContinuousOn (hmRegularPairing (F := F) (G := G)) (Set.Icc a b) ∧
    ContinuousOn (hmFluxPairing (F := F) (V := V)) (Set.Icc a b) := by
  let clampMap : ℝ × Vec 2 → ℝ × Vec 2 := fun p =>
    (HmPerTimePairingInputs.hmPairingTimeClamp a b p.1, p.2)
  have hclampMap : Continuous clampMap := by
    exact ((HmPerTimePairingInputs.hmPairingTimeClamp_continuous a b).comp continuous_fst).prodMk
      continuous_snd
  have hclampMapMem : ∀ p : ℝ × Vec 2,
      clampMap p ∈ Set.Icc a b ×ˢ (Set.univ : Set (Vec 2)) := by
    intro p
    exact ⟨HmPerTimePairingInputs.hmPairingTimeClamp_mem hab, Set.mem_univ _⟩
  have hFext : Continuous (fun p : ℝ × Vec 2 =>
      F (HmPerTimePairingInputs.hmPairingTimeClamp a b p.1) p.2) := by
    have h := hFJoint.comp_continuous hclampMap hclampMapMem
    change Continuous ((fun q : ℝ × Vec 2 => F q.1 q.2) ∘ clampMap)
    exact h
  have hGext : Continuous (fun p : ℝ × Vec 2 =>
      G (HmPerTimePairingInputs.hmPairingTimeClamp a b p.1) p.2) := by
    have h := hGJoint.comp_continuous hclampMap hclampMapMem
    change Continuous ((fun q : ℝ × Vec 2 => G q.1 q.2) ∘ clampMap)
    exact h
  have hDivExt : Continuous (fun p : ℝ × Vec 2 =>
      AVenhance.vecDiv (V (HmPerTimePairingInputs.hmPairingTimeClamp a b p.1)) p.2) := by
    have h := hDivJoint.comp_continuous hclampMap hclampMapMem
    change Continuous ((fun q : ℝ × Vec 2 => AVenhance.vecDiv (V q.1) q.2) ∘ clampMap)
    exact h
  let regExt : ℝ → Vec 2 → ℝ := fun t x =>
    F (HmPerTimePairingInputs.hmPairingTimeClamp a b t) x * G
        (HmPerTimePairingInputs.hmPairingTimeClamp a b t) x
  have hRegExtJoint : Continuous (Function.uncurry regExt) := by
    change Continuous (fun p : ℝ × Vec 2 =>
      F (HmPerTimePairingInputs.hmPairingTimeClamp a b p.1) p.2 *
        G (HmPerTimePairingInputs.hmPairingTimeClamp a b p.1) p.2)
    exact hFext.mul hGext
  have hRegParam : Continuous (fun t : ℝ =>
      ∫ x in HmPerTimePairingInputs.hmPairingClosedCube, regExt t x) :=
    continuous_parametric_integral_of_continuous
      (f := regExt) hRegExtJoint HmPerTimePairingInputs.hmPairingClosedCube_compact
  let fluxExt : ℝ → Vec 2 → ℝ := fun t x =>
    F (HmPerTimePairingInputs.hmPairingTimeClamp a b t) x *
      AVenhance.vecDiv (V (HmPerTimePairingInputs.hmPairingTimeClamp a b t)) x
  have hFluxExtJoint : Continuous (Function.uncurry fluxExt) := by
    change Continuous (fun p : ℝ × Vec 2 =>
      F (HmPerTimePairingInputs.hmPairingTimeClamp a b p.1) p.2 *
        AVenhance.vecDiv (V (HmPerTimePairingInputs.hmPairingTimeClamp a b p.1)) p.2)
    exact hFext.mul hDivExt
  have hFluxParam : Continuous (fun t : ℝ =>
      ∫ x in HmPerTimePairingInputs.hmPairingClosedCube, fluxExt t x) :=
    continuous_parametric_integral_of_continuous
      (f := fluxExt) hFluxExtJoint HmPerTimePairingInputs.hmPairingClosedCube_compact
  have hRegEq (t : ℝ) (ht : t ∈ Set.Icc a b) :
      hmRegularPairing (F := F) (G := G) t =
        ∫ x in HmPerTimePairingInputs.hmPairingClosedCube, regExt t x := by
    unfold hmRegularPairing
    calc
      _ = ∫ x in HmPerTimePairingInputs.hmPairingClosedCube, F t x * G t x :=
        setIntegral_congr_set HmPerTimePairingInputs.hmPairingUnitCube_ae_eq_closedCube
      _ = ∫ x in HmPerTimePairingInputs.hmPairingClosedCube, regExt t x := by
        simp [regExt, HmPerTimePairingInputs.hmPairingTimeClamp_eq ht]
  have hFluxEq (t : ℝ) (ht : t ∈ Set.Icc a b) :
      hmFluxPairing (F := F) (V := V) t =
        ∫ x in HmPerTimePairingInputs.hmPairingClosedCube, fluxExt t x := by
    have hIBP := hm_periodic_divergence_pairing
      (hF t ht) (hV t ht) (hFper t ht) (hVper t ht)
    unfold hmFluxPairing
    calc
      _ = ∫ x in AVenhance.unitCube, F t x * AVenhance.vecDiv (V t) x :=
        hIBP.symm
      _ = ∫ x in HmPerTimePairingInputs.hmPairingClosedCube, F t x * AVenhance.vecDiv (V t) x :=
        setIntegral_congr_set HmPerTimePairingInputs.hmPairingUnitCube_ae_eq_closedCube
      _ = ∫ x in HmPerTimePairingInputs.hmPairingClosedCube, fluxExt t x := by
        simp [fluxExt, HmPerTimePairingInputs.hmPairingTimeClamp_eq ht]
  refine ⟨hRegParam.continuousOn.congr hRegEq,
    hFluxParam.continuousOn.congr hFluxEq⟩

/-- On a positive cell, spacetime L² bounds for the regular source, the Hm
gradient, and the divergence remainder give the local pairing inputs used by
the per-time half-cell assembler. The two vector bounds carry the explicit
`√2` conversion from the Pi norm on `Vec 2` to Euclidean energy. -/
theorem hm_per_time_pairing_inputs_of_spacetime_eLpNorm
    {F G : ℝ → Vec 2 → ℝ} {V : ℝ → Vec 2 → Vec 2}
    {a b anchor QG Qgrad QV : ℝ}
    (ha : 0 < a) (hb : b ≤ 1)
    (hanchor : anchor ∈ Set.Icc a b)
    (hFcont : ∀ s, 0 < s → Continuous (F s))
    (hGcont : ∀ s, 0 < s → Continuous (G s))
    (hGradCont : ∀ s, 0 < s → Continuous (AVenhance.spaceGrad (F s)))
    (hVcont : ∀ s, 0 < s → Continuous (V s))
    (hGmeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => G z.1 z.2)
      (volume.restrict AVenhance.timeCube))
    (hQG : 0 ≤ QG)
    (hGbound : eLpNorm (fun z : ℝ × Vec 2 => G z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal QG)
    (hGradMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (F z.1) z.2)
      (volume.restrict AVenhance.timeCube))
    (hGradMagMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => Real.sqrt
        (vecNormSq (AVenhance.spaceGrad (F z.1) z.2)))
      (volume.restrict AVenhance.timeCube))
    (hQgrad : 0 ≤ Qgrad)
    (hGradBound : eLpNorm
      (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (F z.1) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal Qgrad)
    (hVmeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => V z.1 z.2)
      (volume.restrict AVenhance.timeCube))
    (hVmagMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => Real.sqrt (vecNormSq (V z.1 z.2)))
      (volume.restrict AVenhance.timeCube))
    (hQV : 0 ≤ QV)
    (hVbound : eLpNorm (fun z : ℝ × Vec 2 => V z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal QV)
    (hRegPairCont : ContinuousOn
      (hmRegularPairing (F := F) (G := G)) (Set.Icc a b))
    (hFluxPairCont : ContinuousOn
      (hmFluxPairing (F := F) (V := V)) (Set.Icc a b)) :
    (∀ s ∈ Set.Icc a b,
      IntervalIntegrable (hmRegularPairing (F := F) (G := G)) volume anchor s) ∧
    (∀ s ∈ Set.Icc a b,
      IntervalIntegrable (hmFluxPairing (F := F) (V := V)) volume anchor s) ∧
    (∀ H' : ℝ,
      (∀ s ∈ Set.Icc a b,
        Real.sqrt (AVenhance.l2NormSq (F s)) ≤ H') →
      ∀ s ∈ Set.Icc a b,
        |∫ r in anchor..s, hmRegularPairing (F := F) (G := G) r| ≤
          Real.sqrt (max anchor s - min anchor s) * QG * H') ∧
    (∀ s ∈ Set.Icc a b,
      |∫ r in anchor..s, hmFluxPairing (F := F) (V := V) r| ≤
        (Real.sqrt 2 * Qgrad) * (Real.sqrt 2 * QV)) := by
  have hGdata := hm_time_slice_l2_data_of_spacetime_eLpNorm
    hGmeas hQG hGbound
  have hGradData := hm_vector_time_slice_l2_data_of_spacetime_eLpNorm
    (V := fun t => AVenhance.spaceGrad (F t))
    hGradMeas hGradMagMeas hQgrad hGradBound
  have hVdata := hm_vector_time_slice_l2_data_of_spacetime_eLpNorm
    hVmeas hVmagMeas hQV hVbound
  have hGlocal := hm_time_l2_data_restrict (A := 0) (B := 1)
    (a := a) (b := b) (Q := QG) (by linarith) hb
    hGdata.1 hGdata.2.1 hGdata.2.2
  have hGradlocal := hm_time_l2_data_restrict (A := 0) (B := 1)
    (a := a) (b := b) (Q := Real.sqrt 2 * Qgrad) (by linarith) hb
    hGradData.1 hGradData.2.1 hGradData.2.2
  have hVlocal := hm_time_l2_data_restrict (A := 0) (B := 1)
    (a := a) (b := b) (Q := Real.sqrt 2 * QV) (by linarith) hb
    hVdata.1 hVdata.2.1 hVdata.2.2
  have hRegAbsInt : Integrable
      (fun s => |hmRegularPairing (F := F) (G := G) s|)
      (volume.restrict (Set.Ioc a b)) := by
    have hIcc := hRegPairCont.abs.integrableOn_Icc (μ := volume)
    exact hIcc.mono_set Ioc_subset_Icc_self
  have hFluxAbsInt : Integrable
      (fun s => |hmFluxPairing (F := F) (V := V) s|)
      (volume.restrict (Set.Ioc a b)) := by
    have hIcc := hFluxPairCont.abs.integrableOn_Icc (μ := volume)
    exact hIcc.mono_set Ioc_subset_Icc_self
  have hRegInterval : ∀ s ∈ Set.Icc a b,
      IntervalIntegrable (hmRegularPairing (F := F) (G := G)) volume anchor s := by
    intro s hs
    by_cases hle : anchor ≤ s
    · apply ContinuousOn.intervalIntegrable_of_Icc hle
      exact hRegPairCont.mono (by
        intro r hr
        exact ⟨le_trans hanchor.1 hr.1, le_trans hr.2 hs.2⟩)
    · have hrev : s ≤ anchor := le_of_not_ge hle
      apply (ContinuousOn.intervalIntegrable_of_Icc hrev ?_).symm
      exact hRegPairCont.mono (by
        intro r hr
        exact ⟨le_trans hs.1 hr.1, le_trans hr.2 hanchor.2⟩)
  have hFluxInterval : ∀ s ∈ Set.Icc a b,
      IntervalIntegrable (hmFluxPairing (F := F) (V := V)) volume anchor s := by
    intro s hs
    by_cases hle : anchor ≤ s
    · apply ContinuousOn.intervalIntegrable_of_Icc hle
      exact hFluxPairCont.mono (by
        intro r hr
        exact ⟨le_trans hanchor.1 hr.1, le_trans hr.2 hs.2⟩)
    · have hrev : s ≤ anchor := le_of_not_ge hle
      apply (ContinuousOn.intervalIntegrable_of_Icc hrev ?_).symm
      exact hFluxPairCont.mono (by
        intro r hr
        exact ⟨le_trans hs.1 hr.1, le_trans hr.2 hanchor.2⟩)
  have hRegBound : ∀ H' : ℝ,
      (∀ s ∈ Set.Icc a b,
        Real.sqrt (AVenhance.l2NormSq (F s)) ≤ H') →
      ∀ s ∈ Set.Icc a b,
        |∫ r in anchor..s, hmRegularPairing (F := F) (G := G) r| ≤
          Real.sqrt (max anchor s - min anchor s) * QG * H' := by
    intro H' hEnvelope s hs
    have hH' : 0 ≤ H' := by
      exact (Real.sqrt_nonneg _).trans (hEnvelope anchor hanchor)
    have hpair := hm_regular_pairing_integral_bound_of_full_cell_l2
      hanchor hs hH' hQG hEnvelope
      (fun r hr => hFcont r (lt_of_lt_of_le ha hr.1))
      (fun r hr => hGcont r (lt_of_lt_of_le ha hr.1))
      hGlocal.1 hGlocal.2.1 hGlocal.2.2 hRegAbsInt
    have hdist : |s - anchor| = max anchor s - min anchor s :=
      (max_sub_min_eq_abs anchor s).symm
    rw [hdist] at hpair
    exact hpair
  have hFluxBound : ∀ s ∈ Set.Icc a b,
      |∫ r in anchor..s, hmFluxPairing (F := F) (V := V) r| ≤
        (Real.sqrt 2 * Qgrad) * (Real.sqrt 2 * QV) := by
    intro s hs
    exact hm_flux_pairing_integral_bound_of_full_cell_l2
      hanchor hs (mul_nonneg (Real.sqrt_nonneg 2) hQgrad)
      (mul_nonneg (Real.sqrt_nonneg 2) hQV)
      (fun r hr => hGradCont r (lt_of_lt_of_le ha hr.1))
      (fun r hr => hVcont r (lt_of_lt_of_le ha hr.1))
      hGradlocal.1 hVlocal.1 hGradlocal.2.1
      hVlocal.2.1 hFluxAbsInt
  exact ⟨hRegInterval, hFluxInterval, hRegBound, hFluxBound⟩

/-- Uniform-in-time form of the local pairing bridge, with a varying positive
base point `c t`. This supplies exactly the four pairing fields consumed by
`frozen_hm_positive_time_bounds_of_pairings_per_time`. -/
theorem hm_per_time_pairing_data_of_spacetime_eLpNorm
    {F G : ℝ → Vec 2 → ℝ} {V : ℝ → Vec 2 → Vec 2}
    {c : ℝ → ℝ} {QG Qgrad QV : ℝ}
    (hEndpoint : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 → 0 < c t ∧ c t ≤ 1)
    (hFcont : ∀ s, 0 < s → Continuous (F s))
    (hGcont : ∀ s, 0 < s → Continuous (G s))
    (hGradCont : ∀ s, 0 < s → Continuous (AVenhance.spaceGrad (F s)))
    (hVcont : ∀ s, 0 < s → Continuous (V s))
    (hGmeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => G z.1 z.2)
      (volume.restrict AVenhance.timeCube))
    (hQG : 0 ≤ QG)
    (hGbound : eLpNorm (fun z : ℝ × Vec 2 => G z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal QG)
    (hGradMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (F z.1) z.2)
      (volume.restrict AVenhance.timeCube))
    (hGradMagMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => Real.sqrt
        (vecNormSq (AVenhance.spaceGrad (F z.1) z.2)))
      (volume.restrict AVenhance.timeCube))
    (hQgrad : 0 ≤ Qgrad)
    (hGradBound : eLpNorm
      (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (F z.1) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal Qgrad)
    (hVmeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => V z.1 z.2)
      (volume.restrict AVenhance.timeCube))
    (hVmagMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => Real.sqrt (vecNormSq (V z.1 z.2)))
      (volume.restrict AVenhance.timeCube))
    (hQV : 0 ≤ QV)
    (hVbound : eLpNorm (fun z : ℝ × Vec 2 => V z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal QV)
    (hRegPairCont : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ContinuousOn (hmRegularPairing (F := F) (G := G))
        (Set.Icc (min (c t) t) (max (c t) t)))
    (hFluxPairCont : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ContinuousOn (hmFluxPairing (F := F) (V := V))
        (Set.Icc (min (c t) t) (max (c t) t))) :
    (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc (min (c t) t) (max (c t) t),
        IntervalIntegrable (hmRegularPairing (F := F) (G := G)) volume (c t) s) ∧
    (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc (min (c t) t) (max (c t) t),
        IntervalIntegrable (hmFluxPairing (F := F) (V := V)) volume (c t) s) ∧
    (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 → ∀ H : ℝ,
      (∀ s ∈ Set.Icc (min (c t) t) (max (c t) t),
        Real.sqrt (AVenhance.l2NormSq (F s)) ≤ H) →
      ∀ s ∈ Set.Icc (min (c t) t) (max (c t) t),
        |∫ r in (c t)..s, hmRegularPairing (F := F) (G := G) r| ≤
          Real.sqrt (max (c t) t - min (c t) t) * QG * H) ∧
    (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc (min (c t) t) (max (c t) t),
        |∫ r in (c t)..s, hmFluxPairing (F := F) (V := V) r| ≤
          (Real.sqrt 2 * Qgrad) * (Real.sqrt 2 * QV)) := by
  have hlocal (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) := by
    let a := min (c t) t
    let b := max (c t) t
    have ha : 0 < a := lt_min (hEndpoint t ht).1 ht.1
    have hb : b ≤ 1 := max_le_iff.mpr ⟨(hEndpoint t ht).2, ht.2⟩
    have hanchor : c t ∈ Set.Icc a b := by
      exact ⟨min_le_left _ _, le_max_left _ _⟩
    exact hm_per_time_pairing_inputs_of_spacetime_eLpNorm
      (F := F) (G := G) (V := V) (a := a) (b := b) (anchor := c t)
      ha hb hanchor
      hFcont hGcont hGradCont hVcont hGmeas hQG hGbound
      hGradMeas hGradMagMeas hQgrad hGradBound hVmeas hVmagMeas hQV hVbound
      (hRegPairCont t ht) (hFluxPairCont t ht)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht s hs
    simpa [min_comm, max_comm] using (hlocal t ht).1 s hs
  · intro t ht s hs
    simpa [min_comm, max_comm] using (hlocal t ht).2.1 s hs
  · intro t ht H hEnvelope s hs
    have hH : 0 ≤ H := by
      exact (Real.sqrt_nonneg _).trans (hEnvelope (c t) ⟨min_le_left _ _, le_max_left _ _⟩)
    have hdist : |s - c t| ≤ |t - c t| := by
      by_cases hct : c t ≤ t
      · have hcs : c t ≤ s := by simpa [min_eq_left hct] using hs.1
        have hst : s ≤ t := by simpa [max_eq_right hct] using hs.2
        rw [abs_of_nonneg (sub_nonneg.mpr hcs), abs_of_nonneg (sub_nonneg.mpr hct)]
        exact sub_le_sub_right hst (c t)
      · have htc : t ≤ c t := le_of_not_ge hct
        have hts : t ≤ s := by simpa [min_eq_right htc] using hs.1
        have hsc : s ≤ c t := by simpa [max_eq_left htc] using hs.2
        rw [abs_of_nonpos (sub_nonpos.mpr hsc), abs_of_nonpos (sub_nonpos.mpr htc)]
        linarith
    have hlength : max (c t) s - min (c t) s ≤ max (c t) t - min (c t) t := by
      rw [max_sub_min_eq_abs, max_sub_min_eq_abs]
      exact hdist
    have hroot := Real.sqrt_le_sqrt hlength
    have hlocal := (hlocal t ht).2.2.1 H hEnvelope s hs
    calc
      _ ≤ Real.sqrt (max (c t) s - min (c t) s) * QG * H := hlocal
      _ ≤ Real.sqrt (max (c t) t - min (c t) t) * QG * H := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hroot hQG) hH
  · intro t ht s hs
    simpa [min_comm, max_comm] using (hlocal t ht).2.2.2 s hs

/-- Obtain the time-pairing continuity from positive-time joint continuity of
`F`, the regular source, and `div V`. This is the interface to the actual-flow
regularity producer: its periodic C¹ fields and its joint source formulas
give these hypotheses cell by cell. -/
theorem hm_per_time_pairing_data_of_joint_fields_and_spacetime_eLpNorm
    {F G : ℝ → Vec 2 → ℝ} {V : ℝ → Vec 2 → Vec 2}
    {c : ℝ → ℝ} {QG Qgrad QV : ℝ}
    (hEndpoint : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 → 0 < c t ∧ c t ≤ 1)
    (hFper : ∀ t, 0 < t → IsZ2Periodic (F t))
    (hVper : ∀ t, 0 < t → ∀ i : Fin 2,
      IsZ2Periodic (fun x => V t x i))
    (hF : ∀ t, 0 < t → ContDiff ℝ 1 (F t))
    (hV : ∀ t, 0 < t → ContDiff ℝ 1 (V t))
    (hFJoint : ContinuousOn
      (fun p : ℝ × Vec 2 => F p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hGJoint : ContinuousOn
      (fun p : ℝ × Vec 2 => G p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hDivJoint : ContinuousOn
      (fun p : ℝ × Vec 2 => AVenhance.vecDiv (V p.1) p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hGmeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => G z.1 z.2)
      (volume.restrict AVenhance.timeCube))
    (hQG : 0 ≤ QG)
    (hGbound : eLpNorm (fun z : ℝ × Vec 2 => G z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal QG)
    (hGradMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (F z.1) z.2)
      (volume.restrict AVenhance.timeCube))
    (hGradMagMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => Real.sqrt
        (vecNormSq (AVenhance.spaceGrad (F z.1) z.2)))
      (volume.restrict AVenhance.timeCube))
    (hQgrad : 0 ≤ Qgrad)
    (hGradBound : eLpNorm
      (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (F z.1) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal Qgrad)
    (hVmeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => V z.1 z.2)
      (volume.restrict AVenhance.timeCube))
    (hVmagMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => Real.sqrt (vecNormSq (V z.1 z.2)))
      (volume.restrict AVenhance.timeCube))
    (hQV : 0 ≤ QV)
    (hVbound : eLpNorm (fun z : ℝ × Vec 2 => V z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal QV) :
    (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc (min (c t) t) (max (c t) t),
        IntervalIntegrable (hmRegularPairing (F := F) (G := G)) volume (c t) s) ∧
    (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc (min (c t) t) (max (c t) t),
        IntervalIntegrable (hmFluxPairing (F := F) (V := V)) volume (c t) s) ∧
    (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 → ∀ H : ℝ,
      (∀ s ∈ Set.Icc (min (c t) t) (max (c t) t),
        Real.sqrt (AVenhance.l2NormSq (F s)) ≤ H) →
      ∀ s ∈ Set.Icc (min (c t) t) (max (c t) t),
        |∫ r in (c t)..s, hmRegularPairing (F := F) (G := G) r| ≤
          Real.sqrt (max (c t) t - min (c t) t) * QG * H) ∧
    (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc (min (c t) t) (max (c t) t),
        |∫ r in (c t)..s, hmFluxPairing (F := F) (V := V) r| ≤
          (Real.sqrt 2 * Qgrad) * (Real.sqrt 2 * QV)) := by
  have hFcont : ∀ t, 0 < t → Continuous (F t) := by
    intro t ht
    exact (hF t ht).continuous
  have hGcont : ∀ t, 0 < t → Continuous (G t) := by
    intro t ht
    have heval : Continuous (fun x : Vec 2 => (t, x)) :=
      continuous_const.prodMk continuous_id
    exact hGJoint.comp_continuous heval (fun x => ⟨ht, Set.mem_univ x⟩)
  have hGradCont : ∀ t, 0 < t →
      Continuous (AVenhance.spaceGrad (F t)) := by
    intro t ht
    exact HmPerTimePairingInputs.hm_spaceGrad_continuous_of_contDiff (hF t ht)
  have hVcont : ∀ t, 0 < t → Continuous (V t) := by
    intro t ht
    exact (hV t ht).continuous
  have hRegPairCont : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ContinuousOn (hmRegularPairing (F := F) (G := G))
        (Set.Icc (min (c t) t) (max (c t) t)) := by
    intro t ht
    let a := min (c t) t
    let b := max (c t) t
    have ha : 0 < a := lt_min (hEndpoint t ht).1 ht.1
    have hsubset : Set.Icc a b ×ˢ (Set.univ : Set (Vec 2)) ⊆
        Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) := by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      exact ⟨lt_of_lt_of_le ha hs.1, Set.mem_univ _⟩
    have hcont := hm_pairing_continuity_of_joint_fields
      (F := F) (G := G) (V := V) (a := a) (b := b) min_le_max
      (hFJoint.mono hsubset) (hGJoint.mono hsubset) (hDivJoint.mono hsubset)
      (fun s hs => hFper s (lt_of_lt_of_le ha hs.1))
      (fun s hs i => hVper s (lt_of_lt_of_le ha hs.1) i)
      (fun s hs => hF s (lt_of_lt_of_le ha hs.1))
      (fun s hs => hV s (lt_of_lt_of_le ha hs.1))
    simpa [a, b] using hcont.1
  have hFluxPairCont : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ContinuousOn (hmFluxPairing (F := F) (V := V))
        (Set.Icc (min (c t) t) (max (c t) t)) := by
    intro t ht
    let a := min (c t) t
    let b := max (c t) t
    have ha : 0 < a := lt_min (hEndpoint t ht).1 ht.1
    have hsubset : Set.Icc a b ×ˢ (Set.univ : Set (Vec 2)) ⊆
        Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) := by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      exact ⟨lt_of_lt_of_le ha hs.1, Set.mem_univ _⟩
    have hcont := hm_pairing_continuity_of_joint_fields
      (F := F) (G := G) (V := V) (a := a) (b := b) min_le_max
      (hFJoint.mono hsubset) (hGJoint.mono hsubset) (hDivJoint.mono hsubset)
      (fun s hs => hFper s (lt_of_lt_of_le ha hs.1))
      (fun s hs i => hVper s (lt_of_lt_of_le ha hs.1) i)
      (fun s hs => hF s (lt_of_lt_of_le ha hs.1))
      (fun s hs => hV s (lt_of_lt_of_le ha hs.1))
    simpa [a, b] using hcont.2
  exact hm_per_time_pairing_data_of_spacetime_eLpNorm
    hEndpoint hFcont hGcont hGradCont hVcont hGmeas hQG hGbound
    hGradMeas hGradMagMeas hQgrad hGradBound hVmeas hVmagMeas hQV hVbound
    hRegPairCont hFluxPairCont

end AVenhance.Infra.Section4

end
