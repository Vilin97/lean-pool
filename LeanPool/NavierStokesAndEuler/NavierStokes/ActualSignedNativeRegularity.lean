/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatDyadicExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedUnmaskedBinding

/-!
# Native regularity of the actual signed cut sources

The dyadic factor is retained literally.  The estimates below first turn
the actual radial flat-weight classes into bounded jets, including at the
radial edges; no smooth continuation of the unmasked request at a dyadic
face is assumed.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSignedNativeRegularity

open Set Function Filter WeightedClasses
open CorrectionInitialization
open scoped Topology ContDiff


/-- Full point: an abbreviation for `ActualWaveRegularityData.FullPoint`. -/
abbrev FullPoint := ActualWaveRegularityData.FullPoint

theorem half_weight_bounded {cL cR L : ℝ} (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0 : ℝ) L,
      (max 1 (WeightedRadialPrimitive.delta L t)⁻¹) ^ m *
        Real.sqrt (WeightedRadialPrimitive.zeta cL cR L t) ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((WeightedRadialPrimitive.wholeMajorant_continuous (half_pos hcL) (half_pos hcR) L
        m).continuousOn :
      ContinuousOn _ (Icc (0 : ℝ) L))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht
  have hi : 1 ≤ (WeightedRadialPrimitive.delta L t)⁻¹ :=
    (one_le_inv₀ (WeightedRadialPrimitive.delta_pos ht)).mpr
      (WeightedRadialPrimitive.delta_le_one L t)
  rw [max_eq_right hi, WaveEdgeExtension.sqrt_zeta ht]
  have hw := WeightedRadialPrimitive.weight_le_wholeMajorant
    (half_pos hcL).le (half_pos hcR).le m ht
  have hm := (le_abs_self (WeightedRadialPrimitive.wholeMajorant (cL/2) (cR/2) L m t)).trans
    ((hC t ⟨ht.1.le, ht.2.le⟩).trans (le_max_left C 0))
  simpa only [WeightedRadialPrimitive.weight, inv_pow, div_eq_mul_inv, mul_comm] using hw.trans hm

theorem radial_weight_bounded (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : FullPoint,
      ActualWaveRegularityData.radius x ∈
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
      WaveEdgeExtension.edgeGrowth ActualWaveRegularityData.radius
          (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) x ^ m *
        Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) ≤ C := by
  obtain ⟨C, hC, hb⟩ := half_weight_bounded
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num : (0:ℝ)<4))
    (show (0:ℝ)<1 by norm_num) m
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [ActualWaveRegularityData.strip_zeta]
  exact hb _ (WeightedRadialPrimitive.logPosition_mem
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal) hx)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radial_jets_zero_outside {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0)
    (n m : ℕ) {x : FullPoint}
    (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
    (ho : ActualWaveRegularityData.radius x ∉
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    iteratedFDeriv ℝ m (f n) x = 0 := by
  by_cases hc : ActualWaveRegularityData.radius x ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
  · have he : ActualWaveRegularityData.radius x = PrimaryTargetBounds.leftRadius
      ActualPrimary.nominal ∨
        ActualWaveRegularityData.radius x = PrimaryTargetBounds.rightRadius ActualPrimary.nominal
            := by
      rcases not_and_or.mp ho with ha | hb
      · exact Or.inl (le_antisymm (le_of_not_gt ha) hc.1)
      · exact Or.inr (le_antisymm hc.2 (le_of_not_gt hb))
    exact (ActualWaveRegularityData.full_regular_of_class hf hz n).2 m x hx he
  · have hΩ := ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion
    have hρ := (ActualWaveRegularityData.radius_smooth.contDiffAt (hΩ.mem_nhds hx)).continuousAt
    have hg : f n =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hΩ.mem_nhds hx, hρ (isClosed_Icc.isOpen_compl.mem_nhds hc)] with y hy hout
      exact hz n y hy (fun h => hout ⟨h.1.le, h.2.le⟩)
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hg m, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply]

theorem radial_class_bounded_jets {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0)
    (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion,
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j (f n) x‖ ≤ C := by
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  obtain ⟨D, hD, hd⟩ := radial_weight_bounded p
  let K := C * ActualSignedStageControls.fullStrip.epsilon n ^ α *
    ActualSignedStageControls.fullStrip.slow n ^ p
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg hC (Real.rpow_pos_of_pos (ActualSignedStageControls.fullStrip.epsilon_pos n) α).le)
    (pow_nonneg (zero_le_one.trans (ActualSignedStageControls.fullStrip.one_le_slow n)) p)
  refine ⟨K*D, mul_nonneg hK hD, ?_⟩
  intro x hx j hj
  by_cases hi : ActualWaveRegularityData.radius x ∈
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
  · have hm : x ∈ ActualSignedStageControls.fullStrip.domain := by
      rw [ActualWaveRegularityData.strip_domain_eq]
      exact ⟨hx, hi⟩
    have he := hb n x hm j hj
    simp only [majorant, ActualWaveRegularityData.strip_growth, mul_pow] at he
    calc
      _ ≤ K * (WaveEdgeExtension.edgeGrowth ActualWaveRegularityData.radius
          (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) x ^ p *
          Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) := by
        convert! he using 1
        dsimp [K]
        ring
      _ ≤ K * D := mul_le_mul_of_nonneg_left (hd x hi) hK
  · rw [radial_jets_zero_outside hf hz n j hx hi, norm_zero]
    exact mul_nonneg hK hD

theorem norm_iteratedFDeriv_linear_pull {D F V : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : D →L[ℝ] F) {Ω : Set F} (hΩ : IsOpen Ω) {g : F → V}
    (hg : ContDiffOn ℝ ∞ g Ω) (m : ℕ) {x : D} (hx : e x ∈ Ω) :
    ‖iteratedFDeriv ℝ m (g ∘ e) x‖ ≤ ‖iteratedFDeriv ℝ m g (e x)‖ * ‖e‖ ^ m := by
  have he := e.iteratedFDerivWithin_comp_right hg hΩ.uniqueDiffOn
    (hΩ.preimage e.continuous).uniqueDiffOn hx
      (show (m : WithTop ℕ∞) ≤ ∞ from le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)))
  rw [iteratedFDerivWithin_of_isOpen m (hΩ.preimage e.continuous) hx,
    iteratedFDerivWithin_of_isOpen m hΩ hx] at he
  rw [he]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ m g (e x)).norm_compContinuousLinearMap_le (fun _ => e)

theorem radial_class_pull_local_bounds {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0)
    (e : D →L[ℝ] FullPoint) (Ω : Set D) (q : D → ℝ)
    (hmap : MapsTo e (WaveEdgeExtension.windowDomain Ω q (1 / 2) 2)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)) (n : ℕ) :
    FlatDyadicExtension.LocalJetBounds Ω q (f n ∘ e) := by
  intro x _hx _he m
  obtain ⟨C, hC, hb⟩ := radial_class_bounded_jets hf hz n m
  let Q : ℝ := max 1 ‖e‖
  have hQ : 1 ≤ Q := le_max_left _ _
  refine ⟨C * Q ^ m, mul_nonneg hC (pow_nonneg (zero_le_one.trans hQ) m),
      Filter.Eventually.of_forall ?_⟩
  intro y hy j hj
  have hbound := norm_iteratedFDeriv_linear_pull e
    (ActualWaveRegularity.fullDomain_open ActualPrimary.standardRegion)
    (ActualWaveRegularityData.full_regular_of_class hf hz n).1 j (hmap hy)
  refine hbound.trans (mul_le_mul (hb (e y) (hmap hy) j hj) ?_ (pow_nonneg (norm_nonneg e) j) hC)
  exact (pow_le_pow_left₀ (norm_nonneg e) (le_max_right 1 ‖e‖) j).trans
    (pow_le_pow_right₀ hQ hj)

theorem radial_class_dyadic_pull_smooth {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0)
    (e : D →L[ℝ] FullPoint) {Ω : Set D} (hΩ : IsOpen Ω) {q : D → ℝ}
    (hq : ContDiffOn ℝ ∞ q Ω)
    (hmap : MapsTo e (WaveEdgeExtension.windowDomain Ω q (1 / 2) 2)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun y => SquaredPartition.dyadicProfile (q y) • f n (e y)) Ω ∧
    ∀ x ∈ Ω, q x = 1/2 ∨ q x = 2 → ∀ m,
      iteratedFDeriv ℝ m (fun y => SquaredPartition.dyadicProfile (q y) • f n (e y)) x = 0 := by
  exact FlatDyadicExtension.dyadic_product_smooth_and_flat hΩ hq
    ((ActualWaveRegularityData.full_regular_of_class hf hz n).1.comp e.contDiff.contDiffOn hmap)
    (radial_class_pull_local_bounds hf hz e Ω q hmap n)

/-- Native: an abbreviation for `ActualSignedPhysicalData.Native`. -/
abbrev Native := ActualSignedPhysicalData.Native
/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label B N0`. -/
abbrev Label (B N0 : ℕ) := ActualSignedPhysicalBinding.Label B N0

/-- Native cylinder map as an element of `Native →L[ℝ] PhysicalSignedWave.Cylinder`. -/
noncomputable def nativeCylinderMap : Native →L[ℝ] PhysicalSignedWave.Cylinder :=
  let r := ContinuousLinearMap.fst ℝ ℝ (TorusInverse.Plane × TorusInverse.Plane)
  let s := ContinuousLinearMap.snd ℝ ℝ (TorusInverse.Plane × TorusInverse.Plane)
  let tz := (ContinuousLinearMap.fst ℝ TorusInverse.Plane TorusInverse.Plane).comp s
  let y := (ContinuousLinearMap.snd ℝ TorusInverse.Plane TorusInverse.Plane).comp s
  let swap := (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
  (r.prod ((swap.comp tz).prod y)).prod 0

theorem nativeCylinderMap_apply (y : Native) :
    nativeCylinderMap y = ActualSignedPhysicalData.nativeCylinder y := rfl

/-- Native to common, given by `(ActualSignedPhysicalBinding.toCommonCylinder
l).toContinuousLinearMap.comp nativeCylinderMap`. -/
noncomputable def nativeToCommon {B N0 : ℕ} (l : Label B N0) : Native →L[ℝ] FullPoint :=
  (ActualSignedPhysicalBinding.toCommonCylinder l).toContinuousLinearMap.comp nativeCylinderMap

theorem nativeToCommon_apply {B N0 : ℕ} (l : Label B N0) (y : Native) :
    nativeToCommon l y = ActualSignedPhysicalBinding.toCommonCylinder l
      (ActualSignedPhysicalData.nativeCylinder y) := rfl

/-- Native Q, given by `SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) y.2.1`. -/
noncomputable def nativeQ (y : Native) : ℝ :=
  SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) y.2.1

theorem nativeQ_smooth : ContDiffOn ℝ ∞ nativeQ ActualSignedPhysicalData.nativePast := by
  intro y hy
  exact ((SimilarityCoordinates.coordinateQ_smooth
    (by linarith [ActualPrimary.outgoing.data.h_pos])
    (by linarith [ActualPrimary.outgoing.data.h_lt_half]) hy).comp y
      contDiffAt_snd.fst).contDiffWithinAt

theorem nativeToCommon_maps {B N0 : ℕ} (l : Label B N0) :
    MapsTo (nativeToCommon l)
      (WaveEdgeExtension.windowDomain ActualSignedPhysicalData.nativePast nativeQ (1/2) 2)
      (ActualWaveRegularity.fullDomain ActualPrimary.standardRegion) := by
  intro y hy
  exact ⟨⟨hy.1, hy.2⟩, mem_univ _⟩

theorem radial_class_native_smooth {B N0 : ℕ} (l : Label B N0)
    {f : ℕ → FullPoint → E} {α : ℝ}
    (hf : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α f)
    (hz : ∀ n x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f n x = 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun y => SquaredPartition.dyadicProfile (nativeQ y) • f n (nativeToCommon l y))
      ActualSignedPhysicalData.nativePast ∧
      ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
        iteratedFDeriv ℝ m (fun z => SquaredPartition.dyadicProfile (nativeQ z) • f n
            (nativeToCommon l z)) y = 0 :=
  radial_class_dyadic_pull_smooth hf hz (nativeToCommon l)
    ActualSignedPhysicalData.nativePast_open nativeQ_smooth (nativeToCommon_maps l) n

theorem primary_mask_zero_outside {B N0 : ℕ} (l : Label B N0) (n : ℕ)
    (x : PhysicalSignedWave.Cylinder)
    (ho : SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) (x.1.2.1.2, x.1.2.1.1) ∉ Ioo (1 /
        2
        : ℝ) 2) :
    (ActualSignedPhysicalBinding.primary l).mask n x = 0 := by
  change ActualPrimary.spatialMask l.1 (x.1.1,x.1.2.1) = 0
  by_contra hn
  exact ho (ActualPrimary.spatialMask_q_range l.1 (x.1.1,x.1.2.1) hn)

theorem referenceScalar_zero_outside {B N0 : ℕ} (l : Label B N0)
    (request : ℕ → PhysicalSignedWave.Cylinder → SignedWaveUpdate.Vec2)
    (j : Fin 2) (n : ℕ) (x : PhysicalSignedWave.Cylinder)
    (ho : SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) (x.1.2.1.2, x.1.2.1.1) ∉ Ioo (1 /
        2
        : ℝ) 2) :
    ActualPeriodizedSignedRealization.referenceScalar (ActualSignedPhysicalBinding.primary l)
        request j n x = 0 := by
  simp only [ActualPeriodizedSignedRealization.referenceScalar, SignedWaveUpdate.signedScalar,
    primary_mask_zero_outside l n x ho, mul_zero]

section ActualCoefficients

open ActualSignedUnmaskedBounds

variable {B N0 : ℕ}

theorem own_native_smooth {f : Label B N0 → TorusInverse.Frequency → ℕ → FullPoint → E} {α : ℝ}
    (hf : LabelSumBounds.UniformClass ActualSignedStageControls.fullStrip
      (fun (i : Label B N0 × TorusInverse.Frequency) n x =>
        Real.sqrt (ActualSignedStageControls.fullStrip.zeta x) * ActualSignedStageControls.envelope
            i.1 n x)
      α (ownField f))
    (hz : ∀ l k x, x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion →
      ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) → f l k (reference l) x = 0)
    (l : Label B N0) (k : TorusInverse.Frequency) :
    ContDiffOn ℝ ∞ (fun y => SquaredPartition.dyadicProfile (nativeQ y) •
      f l k (reference l) (nativeToCommon l y)) ActualSignedPhysicalData.nativePast ∧
      ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
        iteratedFDeriv ℝ m (fun z => SquaredPartition.dyadicProfile (nativeQ z) •
          f l k (reference l) (nativeToCommon l z)) y = 0 := by
  have hc : MemClass ActualSignedStageControls.fullStrip
      (fun _ x => Real.sqrt (ActualSignedStageControls.fullStrip.zeta x)) α (ownField f (l,k)) := by
    apply (hf.each (l,k)).mono_weight (fun _ _ _ => Real.sqrt_nonneg _)
    intro n x _
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _)
      (ActualPrimaryBounds.fullEnvelope_le_one (l.2,l.1) n x)
  have hzero (n : ℕ) (x : FullPoint)
      (hx : x ∈ ActualWaveRegularity.fullDomain ActualPrimary.standardRegion)
      (ho : ActualWaveRegularityData.radius x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) : ownField f (l,k) n x = 0 := by
    by_cases hn : n = reference l
    · subst n
      rw [ownField_reference]
      exact hz l k x hx ho
    · rw [ownField_other f (l,k) hn]
  have hh := radial_class_native_smooth l hc hzero (reference l)
  simpa only [ownField, ite_eq_left rfl, ite_true] using hh

variable {request : ℕ → FullPoint → SignedWaveUpdate.Vec2} {β : ℝ}
  (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
    (fun (_ : Label B N0) _ x => ActualSignedStageControls.fullStrip.zeta x) β
    ActualSignedStageControls.phaseCell (fun _ n _ x => request n x q))

include hR in
theorem potential_smooth_and_flat (l : Label B N0) (k : TorusInverse.Frequency) :
    ContDiffOn ℝ ∞ (fun y => SquaredPartition.dyadicProfile (nativeQ y) •
      potential request l k (reference l) (nativeToCommon l y)) ActualSignedPhysicalData.nativePast
          ∧
      ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
        iteratedFDeriv ℝ m (fun z => SquaredPartition.dyadicProfile (nativeQ z) •
          potential request l k (reference l) (nativeToCommon l z)) y = 0 := by
  exact own_native_smooth (own_potential_pressure_class hR).1
    (fun l k x hx ho => (own_zero_outside request l k hx ho).2.2) l k

include hR in
theorem pressure_smooth_and_flat (l : Label B N0) (k : TorusInverse.Frequency) :
    ContDiffOn ℝ ∞ (fun y => SquaredPartition.dyadicProfile (nativeQ y) •
      pressure request l k (reference l) (nativeToCommon l y)) ActualSignedPhysicalData.nativePast ∧
      ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
        iteratedFDeriv ℝ m (fun z => SquaredPartition.dyadicProfile (nativeQ z) •
          pressure request l k (reference l) (nativeToCommon l z)) y = 0 := by
  exact own_native_smooth (own_potential_pressure_class hR).2
    (fun l k x hx ho => (own_zero_outside request l k hx ho).2.1) l k

end ActualCoefficients

section LiteralNativeSources

open ActualSignedUnmaskedBinding

variable {B N0 : ℕ}
  (P : SignedStressPrimitive.Patch) (u : CorrectionState.State LocalSignedRequest.Point)
  (H : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion P.a P.b
    (ActualPrimary.commonContext B) u)
  (hp : GaugeMomentBalances.MovingField ActualPrimary.standardRegion P.a P.b u.pressure)

/-- The only gates are the original discrete label, harmonic, and band gates. -/
theorem native_potential_source_factor (L : NativeLabel B N0)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) :
    ActualSignedPhysicalData.nativePotentialSource ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n =
    if I.1.1 = (L : PhysicalWaveSum.BandLabel) ∧ I.1.2.val = 1 ∧ n = L.val.1 then
      fun y => SquaredPartition.dyadicProfile (nativeQ y) •
        ActualSignedUnmaskedBounds.potential (request (B := B) P u)
            (ActualSignedExterior.actualLabel L) I.2
          (ActualSignedUnmaskedBounds.reference (ActualSignedExterior.actualLabel L))
          (nativeToCommon (ActualSignedExterior.actualLabel L) y)
    else fun _ => 0 := by
  classical
  funext y
  by_cases hL : I.1.1 = (L : PhysicalWaveSum.BandLabel)
  · have hm : I.1.1 ∈ (branch P u H hp L).active := by
      change I.1.1 ∈ {(L : PhysicalWaveSum.BandLabel)}
      exact mem_singleton_iff.mpr hL
    have hv : I.1.1.val = L.val := congrArg Subtype.val hL
    erw [ActualSignedPhysicalData.nativePotentialSource, dite_eq_left hm]
    simp only [hL, true_and]
    by_cases hi : I.1.2.val = 1 ∧ n = L.val.1
    · simp only [ite_eq_left hi]
      exact native_potential_factor P u H hp L I.2 y
    · simp only [ite_eq_right hi]
  · have hm : I.1.1 ∉ (branch P u H hp L).active := by
      change I.1.1 ∉ {(L : PhysicalWaveSum.BandLabel)}
      exact fun h => hL (mem_singleton_iff.mp h)
    simp only [ActualSignedPhysicalData.nativePotentialSource, dite_eq_right hm, hL, false_and,
        ite_false]

theorem native_pressure_source_factor (L : NativeLabel B N0)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) :
    ActualSignedPhysicalData.nativePressureSource ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n =
    if I.1.1 = (L : PhysicalWaveSum.BandLabel) ∧ I.1.2.val = 1 ∧ n = L.val.1 then
      fun y => SquaredPartition.dyadicProfile (nativeQ y) •
        ActualSignedUnmaskedBounds.pressure (request (B := B) P u)
            (ActualSignedExterior.actualLabel L) I.2
          (ActualSignedUnmaskedBounds.reference (ActualSignedExterior.actualLabel L))
          (nativeToCommon (ActualSignedExterior.actualLabel L) y)
    else fun _ => 0 := by
  classical
  funext y
  by_cases hL : I.1.1 = (L : PhysicalWaveSum.BandLabel)
  · have hm : I.1.1 ∈ (branch P u H hp L).active := by
      change I.1.1 ∈ {(L : PhysicalWaveSum.BandLabel)}
      exact mem_singleton_iff.mpr hL
    have hv : I.1.1.val = L.val := congrArg Subtype.val hL
    erw [ActualSignedPhysicalData.nativePressureSource, dite_eq_left hm]
    simp only [hL, true_and]
    by_cases hi : I.1.2.val = 1 ∧ n = L.val.1
    · simp only [ite_eq_left hi]
      exact native_pressure_factor P u H hp L I.2 y
    · simp only [ite_eq_right hi]
  · have hm : I.1.1 ∉ (branch P u H hp L).active := by
      change I.1.1 ∉ {(L : PhysicalWaveSum.BandLabel)}
      exact fun h => hL (mem_singleton_iff.mp h)
    simp only [ActualSignedPhysicalData.nativePressureSource, dite_eq_right hm, hL, false_and,
        ite_false]

omit P u H hp in
theorem zero_native_smooth_and_flat :
    ContDiffOn ℝ ∞ (fun _ : Native => (0 : E)) ActualSignedPhysicalData.nativePast ∧
      ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
        iteratedFDeriv ℝ m (fun _ : Native => (0 : E)) y = 0 := by
  refine ⟨contDiffOn_const, fun _ _ _ _ => ?_⟩
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply]

variable {β : ℝ}
  (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
    (fun (_ : Label B N0) _ x => ActualSignedStageControls.fullStrip.zeta x) β
    ActualSignedStageControls.phaseCell (fun _ n _ x => request (B := B) P u n x q))

include hR in
theorem native_potential_smooth_and_flat (L : NativeLabel B N0)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) :
    ContDiffOn ℝ ∞ (ActualSignedPhysicalData.nativePotentialSource ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n)
        ActualSignedPhysicalData.nativePast ∧
    ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
      iteratedFDeriv ℝ m (ActualSignedPhysicalData.nativePotentialSource ActualPrimary.slots
        ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n) y = 0 := by
  rw [native_potential_source_factor]
  split_ifs
  · exact potential_smooth_and_flat hR (ActualSignedExterior.actualLabel L) I.2
  · exact zero_native_smooth_and_flat

include hR in
theorem native_pressure_smooth_and_flat (L : NativeLabel B N0)
    (I : ActualSignedPhysicalData.SourceIndex) (n : ℕ) :
    ContDiffOn ℝ ∞ (ActualSignedPhysicalData.nativePressureSource ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n)
        ActualSignedPhysicalData.nativePast ∧
    ∀ y ∈ ActualSignedPhysicalData.nativePast, nativeQ y = 1/2 ∨ nativeQ y = 2 → ∀ m,
      iteratedFDeriv ℝ m (ActualSignedPhysicalData.nativePressureSource ActualPrimary.slots
        ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) I n) y = 0 := by
  rw [native_pressure_source_factor]
  split_ifs
  · exact pressure_smooth_and_flat hR (ActualSignedExterior.actualLabel L) I.2
  · exact zero_native_smooth_and_flat

include hR in
/-- Full positive-time native regularity of the same actual signed family.
Only the actual request jets are used; no native output smoothness is assumed. -/
theorem nativeRegular (L : NativeLabel B N0) :
    ActualSignedPhysicalData.NativeRegular ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch P u H hp L) where
  potential I n := (native_potential_smooth_and_flat P u H hp hR L I n).1
  pressure I n := (native_pressure_smooth_and_flat P u H hp hR L I n).1

end LiteralNativeSources

section ActualResiduals

open ActualSignedUnmaskedBinding

variable {B N0 : ℕ}

/-- The request estimate is derived from the two measured mean residuals
of the same reconstructed state. -/
theorem request_jets_from_residuals
    (u : CorrectionState.State LocalSignedRequest.Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (ActualPrimary.commonContext B) u)
    (hfixed : VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (ActualPrimary.commonContext B) u = u)
    (hθ : MeanClass ActualInitialization.geometry.strip α
      (u.thetaResidual (ActualPrimary.commonContext B)))
    (hz : MeanClass ActualInitialization.geometry.strip α
      (u.axialResidual (ActualPrimary.commonContext B))) :
    ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
      (fun (_ : Label B N0) _ x => ActualSignedStageControls.fullStrip.zeta x) (α-1)
      ActualSignedStageControls.phaseCell
      (fun _ n _ x => request (B := B) ActualInitialization.patch u n x q) := by
  exact ActualSignedStageControls.fullRequest_jets_from_residuals ActualInitialization.geometry
    (ActualPrimary.commonContext B) u α H hfixed hθ hz
      (ActualSignedStageControls.phaseCell (B := B) (N0 := N0))

/-- No regularity hypothesis on a native output or unmasked quotient is
needed: the actual mean residual classes provide all required input jets. -/
theorem nativeRegular_from_residuals
    (u : CorrectionState.State LocalSignedRequest.Point)
    (H : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (ActualPrimary.commonContext B) u)
    (hp : GaugeMomentBalances.MovingField ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b u.pressure)
    (α : ℝ)
    (hfixed : VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (ActualPrimary.commonContext B) u = u)
    (hθ : MeanClass ActualInitialization.geometry.strip α
      (u.thetaResidual (ActualPrimary.commonContext B)))
    (hz : MeanClass ActualInitialization.geometry.strip α
      (u.axialResidual (ActualPrimary.commonContext B)))
    (L : NativeLabel B N0) :
    ActualSignedPhysicalData.NativeRegular ActualPrimary.slots
      ActualPrimary.outgoing.data.h_pos.le (branch ActualInitialization.patch u H hp L) :=
  nativeRegular ActualInitialization.patch u H hp
    (request_jets_from_residuals u α H hfixed hθ hz) L

/-- This is the literal post-particular state used to construct the
canonical signed physical family, with its initialization and gauge intact. -/
theorem cycleNativeRegular
    (x : CorrectionStep.CycleState (Label B N0))
    (H : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b (ActualPrimary.commonContext B)
        ((ActualCycleParameters.fixedParameters B N0).afterParticular
          x.coefficients (ActualPrimary.commonContext B) x.state))
    (hp : GaugeMomentBalances.MovingField ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b
        ((ActualCycleParameters.fixedParameters B N0).afterParticular
          x.coefficients (ActualPrimary.commonContext B) x.state).pressure)
    (α : ℝ)
    (hfixed : VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (ActualPrimary.commonContext B)
        ((ActualCycleParameters.fixedParameters B N0).afterParticular
          x.coefficients (ActualPrimary.commonContext B) x.state) =
        ((ActualCycleParameters.fixedParameters B N0).afterParticular
          x.coefficients (ActualPrimary.commonContext B) x.state))
    (hθ : MeanClass ActualInitialization.geometry.strip α
      (((ActualCycleParameters.fixedParameters B N0).afterParticular
        x.coefficients (ActualPrimary.commonContext B) x.state).thetaResidual
            (ActualPrimary.commonContext B)))
    (hz : MeanClass ActualInitialization.geometry.strip α
      (((ActualCycleParameters.fixedParameters B N0).afterParticular
        x.coefficients (ActualPrimary.commonContext B) x.state).axialResidual
            (ActualPrimary.commonContext B)))
    (L : NativeLabel B N0) :
    ActualSignedPhysicalData.NativeRegular ActualPrimary.slots ActualPrimary.outgoing.data.h_pos.le
      ((ActualSignedExterior.cycleFamily x H hp).singleton L) :=
  nativeRegular_from_residuals _ H hp α hfixed hθ hz L

end ActualResiduals

end NavierStokes.ActualSignedNativeRegularity
