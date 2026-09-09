/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionInitialization
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseStressClasses

@[expose] public section

/-!
# Covariance of the fixed physical primary family

The selected primary phases, native matrices, masks, and physical labels are
those of `CorrectionInitialization.ActualPrimary`.  The finite family is
assembled before averaging.  The fixed starting threshold is retained.
-/

noncomputable section

namespace NavierStokes.ActualPrimaryCovariance

open Set Function Filter
open scoped ContDiff Topology BigOperators
open CorrectionInitialization.ActualPrimary PartitionedCovariance PrimaryFieldAssembly

abbrev Point := LocalSignedRequest.Point
abbrev Slow := PhaseCalculus.Slow
abbrev Plane := TorusInverse.Plane

/-! ## Changing the common auxiliary cover does not change a diagonal average -/

theorem covered_common {m k : ℕ} (hk : k ≤ m) (f : Plane → ℝ) (Y : Plane) :
    covered m f ((CommonCoverSolve.coverPower k).symm Y) = covered (m - k) f Y := by
  simp only [covered, ← cover_power_eq_iterate, ← CommonCoverSolve.coverPower_apply]
  congr 1
  calc
    _ = CommonCoverSolve.coverPower (m - k + k) ((CommonCoverSolve.coverPower k).symm Y) := by
      rw [Nat.sub_add_cancel hk]
    _ = _ := by
      rw [CopySolveCompatibility.coverPower_add, ContinuousLinearEquiv.apply_symm_apply]

theorem wave_common {m k : ℕ} (hk : k ≤ m) (a : ℝ) (f : Plane → ℝ)
    (j : ℤ) (phase : Plane → ℝ) (Y : Plane) (theta : ℝ) :
    wave a m f j phase ((CommonCoverSolve.coverPower k).symm Y) theta =
      wave a (m - k) f j (fun Z => phase ((CommonCoverSolve.coverPower k).symm Z)) Y theta := by
  simp only [wave, covered_common hk]

theorem pair_diagonal_at_cover {D h : ℝ} {vr vt : Plane}
    {sys : SlotSystem D h vr vt} {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (a : ℝ) (n : ℕ)
    (phase : Plane → ℝ) (j i : Fin 2) :
    doubleAverage (fun Y theta =>
      wave a n (P.rawRadial hdet j) (P.modes j) phase Y theta *
      wave a n (P.rawTangent hdet j i) (P.modes j) phase Y theta) =
      a ^ 2 * P.matrix i j := by
  have he := (P.pulses j).wave_covariance vr vt (slotCenter h (signedLabel U j)) hdet
    (P.ci j) sys.radius (P.ci_pos j) sys.radius_pos
    (slotSet h sys.radius vr vt (signedLabel U j)) (sys.injective _)
    (P.rawRadial_support hdet j) (fun i => P.rawTangent_support hdet j i)
    a n phase (P.modes j) (P.modes_ne j) i
  simpa only [PairData.rawRadial, PairData.rawTangent, PairData.matrix, pairMatrix,
    mul_assoc] using he

theorem pair_diagonal_common {D h : ℝ} {vr vt : Plane}
    {sys : SlotSystem D h vr vt} {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) {k : ℕ}
    (hk : k ≤ SlotColoring.nativeIndex h U.1)
    (outer epsilon : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (j i : Fin 2) :
    doubleAverage (fun Y theta =>
      slotVelocity P hdet outer epsilon T q x j ((CommonCoverSolve.coverPower k).symm Y) theta 0 *
      slotVelocity P hdet outer epsilon T q x j ((CommonCoverSolve.coverPower k).symm Y) theta
        i.succ) =
      (outer * amplitude epsilon (mask D U q x) P.matrix T j) ^ 2 * P.matrix i j := by
  simp only [slotVelocity_zero, slotVelocity_succ, PairData.radialWave,
    PairData.tangentWave, wave_common hk]
  exact pair_diagonal_at_cover P hdet _ _ _ j i

theorem pair_diagonal_common_continuous {D h : ℝ} {vr vt : Plane}
    {sys : SlotSystem D h vr vt} {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) {k : ℕ}
    (hk : k ≤ SlotColoring.nativeIndex h U.1)
    (outer epsilon : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (j i : Fin 2) :
    (∀ Y, Continuous (fun theta =>
      slotVelocity P hdet outer epsilon T q x j ((CommonCoverSolve.coverPower k).symm Y) theta 0 *
      slotVelocity P hdet outer epsilon T q x j ((CommonCoverSolve.coverPower k).symm Y) theta
        i.succ)) ∧
    Continuous (fun Y => SmoothLoop.angularMean (fun theta =>
      slotVelocity P hdet outer epsilon T q x j ((CommonCoverSolve.coverPower k).symm Y) theta 0 *
      slotVelocity P hdet outer epsilon T q x j ((CommonCoverSolve.coverPower k).symm Y) theta
        i.succ)) := by
  simp only [slotVelocity_zero, slotVelocity_succ, PairData.radialWave,
    PairData.tangentWave, wave_common hk]
  refine ⟨fun _ => (wave_continuous_theta _ _ _ _ _ _).mul (wave_continuous_theta _ _ _ _ _ _), ?_⟩
  exact angularMean_wave_product_continuous _ _
    (P.rawRadial_continuous hdet j) (P.rawRadial_compact hdet j)
    (P.rawTangent_continuous hdet j i) (P.rawTangent_compact hdet j i)
    (P.modes j) (P.modes_ne j) _

/-! ## Zero masks really remove the selected native fields -/

variable {B N0 : ℕ}

theorem rawVelocity_zero_of_mask (j : Fin 2) (L : Label B N0) (p : Slow)
    (hm : spatialMask L p = 0) (Y : Plane) : rawVelocity j L (p, Y) = 0 := by
  simp only [rawVelocity, hm, zero_mul, amplitude, mul_zero, zero_smul]

theorem commonAmplitude_zero_of_mask (j : Fin 2) (L : Label B N0) (p : Slow)
    (hm : spatialMask L p = 0) (Y : Plane) : commonAmplitude j L p Y = 0 := by
  simp only [commonAmplitude, cutVelocity, rawVelocity_zero_of_mask j L p hm, smul_zero,
    map_zero, tsum_zero]

theorem tangentMode_zero_of_mask (j : Fin 2) (L : Label B N0) (p : Slow)
    (hm : spatialMask L p = 0) (Y : Plane) (theta : ℝ) :
    tangentMode j L p Y theta = 0 := by
  funext i
  simp only [tangentMode, HarmonicCalculus.vectorMode, HarmonicCalculus.mode,
    commonAmplitude_zero_of_mask j L p hm, Pi.zero_apply, zero_mul, Complex.zero_re]

theorem physicalTangentMode_zero_of_mask (j : Fin 2) (L : Label B N0) (p : Slow)
    (hm : spatialMask L p = 0) (Y : Plane) (theta : ℝ) :
    physicalTangentMode j L p Y theta = 0 := by
  rw [physicalTangentMode, tangentMode_zero_of_mask j L p hm, smul_zero]

theorem physicalTangentMode_eq_slot (j : Fin 2) (L : Label B N0) (p : Slow)
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (Y : Plane) (theta : ℝ) :
    physicalTangentMode j L p Y theta = slotVelocity (sourcePair L p hp).pairData vectors_det
      (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h))
      (ChartScales.epsilon h (BaseChartJets.cellBand L))
      (fun i => PrimaryTargetBounds.actualTarget modulation p i)
      (similarityScale L p) (position L p) j Y theta := by
  rw [slotVelocity_outer_scale, physicalTangentMode, tangentMode_eq_source j L p hp,
    SourcePair.actualVelocity_eq]

/-! ## The same physical point in each fixed label's native coordinates -/

noncomputable def nativePoint (n : ℕ) (x : Point) (L : Label B N0) : Slow :=
  nativeSlow L (toAbsolute n x)

theorem nativePoint_auxiliary (n : ℕ) (x : Point) (L : Label B N0) (Y : Plane) :
    nativePoint n (x.1, (x.2.1, Y)) L = nativePoint n x L := rfl

theorem nativePoint_time (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (L : Label B N0) :
    0 < (nativePoint n x L).2.2 := by
  change 0 < ChartScales.Q n * x.2.1.1 / ChartScales.Q (BaseChartJets.cellBand L)
  exact div_pos (mul_pos (ChartScales.Q_pos n) hT) (ChartScales.Q_pos _)

theorem nativePoint_radius (n : ℕ) {x : Point} (hR : 0 < x.1) (L : Label B N0) :
    0 < (nativePoint n x L).1 := by
  change 0 < Real.sqrt (ChartScales.Q n) * x.1 / Real.sqrt (ChartScales.Q (BaseChartJets.cellBand
    L))
  exact div_pos (mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) hR)
    (Real.sqrt_pos.mpr (ChartScales.Q_pos _))

theorem nativePoint_inner (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (L : Label B N0) :
    (BaseChartJets.normalizedCoordinates h (nativePoint n x L)).2 =
      (BaseChartJets.normalizedCoordinates h (BaseContextAssembly.slowCoordinates x)).2 := by
  unfold nativePoint
  rw [nativeSlow_toAbsolute_eq_slowChange]
  exact ActualSignedGeometry.normalized_inner_slowChange (F := outgoing)
    (ChartScales.Q_pos n) (ChartScales.Q_pos _) hT

theorem nativePoint_profileRadius (n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1) (hR : 0 < x.1) (L : Label B N0) :
    PrimaryTargetBounds.profileRadius h (nativePoint n x L) =
      PrimaryTargetBounds.profileRadius h (BaseContextAssembly.slowCoordinates x) := by
  unfold nativePoint
  rw [nativeSlow_toAbsolute_eq_slowChange]
  exact ActualSignedGeometry.profileRadius_slowChange (F := outgoing)
    (ChartScales.Q_pos n) (ChartScales.Q_pos _) hT hR

theorem nativePoint_position (n : ℕ) (x : Point) (L : Label B N0) :
    position L (nativePoint n x L) = physicalPosition n x := by
  have hq := (ChartScales.Q_pos (BaseChartJets.cellBand L)).ne'
  have hs := (Real.sqrt_pos.mpr (ChartScales.Q_pos (BaseChartJets.cellBand L))).ne'
  have hd := (Real.rpow_pos_of_pos (ChartScales.Q_pos (BaseChartJets.cellBand L))
    (CoordinateAlgebra.D h)).ne'
  funext i
  fin_cases i <;>
    simp only [position, nativePoint, nativeSlow, toAbsolute, physicalPosition,
      mul_div_cancel₀ _ hq, mul_div_cancel₀ _ hs, mul_div_cancel₀ _ hd]

theorem nativePoint_scale (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (L : Label B N0) :
    similarityScale L (nativePoint n x L) = physicalScale n x := by
  unfold similarityScale nativePoint
  rw [nativeSlow_toAbsolute_eq_slowChange,
    ActualSignedGeometry.slowChange_eq_transition (ChartScales.Q_pos n) (ChartScales.Q_pos _)]
  change ChartScales.Q (BaseChartJets.cellBand L) *
    SimilarityHomogeneity.chartQ h
      (SimilarityHomogeneity.chartTransition h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand L)) (BaseContextAssembly.slowCoordinates x)) = _
  rw [SimilarityHomogeneity.chartQ_transition outgoing.data.h_pos outgoing.data.h_lt_half
    (ChartScales.Q_pos n) (ChartScales.Q_pos _) hT]
  change _ = ChartScales.Q n * SimilarityHomogeneity.chartQ h (BaseContextAssembly.slowCoordinates
    x)
  field_simp [(ChartScales.Q_pos (BaseChartJets.cellBand L)).ne']

theorem nativePoint_mask (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (L : Label B N0) :
    spatialMask L (nativePoint n x L) = mask (CoordinateAlgebra.D h)
      (PrimaryGeometryAssembly.label nominal L) (physicalScale n x) (physicalPosition n x) := by
  unfold spatialMask
  rw [nativePoint_scale n hT, nativePoint_position]

theorem nativePoint_weight_pos (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (L : Label B N0) :
    0 < PrimaryTargetBounds.movingWeight nominal (nativePoint n x L) := by
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hR := BaseContextAssembly.nativeStrip_radius nominal standardRegion hx
  have hr := ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp hx).2
  unfold PrimaryTargetBounds.movingWeight
  rw [nativePoint_profileRadius n hT hR]
  exact WeightedRadialPrimitive.zeta_pos _ _
    (WeightedRadialPrimitive.logPosition_mem (PrimaryTargetBounds.leftRadius_pos nominal) hr)

theorem nativePoint_reference (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (L : Label B N0)
    (hm : spatialMask L (nativePoint n x L) ≠ 0) :
    nativePoint n x L ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet
      nominal) := by
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hR := BaseContextAssembly.nativeStrip_radius nominal standardRegion hx
  have ha := (BaseContextAssembly.nativeStrip_active nominal standardRegion hx).1
  apply spatialMask_reference L (nativePoint_time n hT L) (nativePoint_radius n hR L).le
  · rw [nativePoint_inner n hT]
    exact ⟨ha.1.le, ha.2.le⟩
  · exact hm

noncomputable def unsignedLabels (B N0 n : ℕ) : Finset (Label B N0) := by
  classical
  exact (CorrectionInitialization.CommonWindow.labels (CoordinateAlgebra.D h)
    (BaseContextAssembly.geometryBound nominal standardRegion) n).preimage
      (PrimaryGeometryAssembly.label nominal) (PrimaryGeometryAssembly.label_injective
        nominal).injOn

theorem activeLabels_product (B N0 n : ℕ) :
    activeLabels standardRegion B N0 n = (unsignedLabels B N0 n).product Finset.univ := rfl

theorem mem_unsignedLabels (n : ℕ) (L : Label B N0) :
    L ∈ unsignedLabels B N0 n ↔ (L, (0 : Fin 2)) ∈ activeLabels standardRegion B N0 n := by
  classical
  simp [activeLabels, unsignedLabels]

theorem active_cover_le (n : ℕ) {L : Label B N0} (hL : L ∈ unsignedLabels B N0 n) :
    CorrectionInitialization.CommonWindow.index h n ≤ ChartScales.nativeIndex h
      (BaseChartJets.cellBand L) := by
  have hm := (mem_activeLabels standardRegion n L 0).mp ((mem_unsignedLabels n L).mp hL)
  obtain ⟨m, hm, hrest⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hrest
  have hband : m = BaseChartJets.cellBand L := congrArg Prod.fst he
  subst m
  exact CorrectionInitialization.CommonWindow.index_le hm

noncomputable def signedLabelOf (l : Label B N0 × Fin 2) : SlotColoring.Label :=
  signedLabel (PrimaryGeometryAssembly.label nominal l.1) l.2

theorem signedLabelOf_injective : Function.Injective (signedLabelOf (B := B) (N0 := N0)) := by
  rintro ⟨L, j⟩ ⟨M, k⟩ he
  change signedLabel (PrimaryGeometryAssembly.label nominal L) j =
    signedLabel (PrimaryGeometryAssembly.label nominal M) k at he
  have hlabel : PrimaryGeometryAssembly.label nominal L = PrimaryGeometryAssembly.label nominal M :=
    Prod.ext (congrArg (fun z : SlotColoring.Label => z.1) he)
      (congrArg (fun z : SlotColoring.Label => z.2.1) he)
  have hLM := PrimaryGeometryAssembly.label_injective nominal hlabel
  subst M
  have hjk : j = k := signedLabel_injective (PrimaryGeometryAssembly.label nominal L) he
  subst k
  rfl

noncomputable def viewTangent (n : ℕ) (x : Point) (l : Label B N0 × Fin 2)
    (Y : Plane) (theta : ℝ) : Fin 3 → ℝ :=
  physicalTangentMode l.2 l.1 (nativePoint n x l.1)
    ((CommonCoverSolve.coverPower (CorrectionInitialization.CommonWindow.index h n)).symm Y) theta

theorem viewTangent_cross_zero (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    {l m : Label B N0 × Fin 2} (hlm : l ≠ m) (Y : Plane) (theta : ℝ) (i : Fin 2) :
    viewTangent n x l Y theta 0 * viewTangent n x m Y theta i.succ = 0 := by
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  by_cases hl : spatialMask l.1 (nativePoint n x l.1) = 0
  · simp only [viewTangent, physicalTangentMode_zero_of_mask l.2 l.1 _ hl, Pi.zero_apply, zero_mul]
  by_cases hm : spatialMask m.1 (nativePoint n x m.1) = 0
  · simp only [viewTangent, physicalTangentMode_zero_of_mask m.2 m.1 _ hm, Pi.zero_apply, mul_zero]
  have hpl := spatialMask_carrier l.1 (nativePoint_time n hT l.1) hl
  have hpm := spatialMask_carrier m.1 (nativePoint_time n hT m.1) hm
  let P := (sourcePair l.1 (nativePoint n x l.1) hpl).pairData
  let Q := (sourcePair m.1 (nativePoint n x m.1) hpm).pairData
  have hq : 0 < physicalScale n x := by
    exact mul_pos (ChartScales.Q_pos n)
      (standardRegion.chartQ_pos ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp
        hx).1)
  have he := slots.wave_cross_zero l.1.val.property.1 m.1.val.property.1
    (fun hsame => hlm (signedLabelOf_injective hsame))
    (P.rawRadial_support vectors_det l.2) (Q.rawTangent_support vectors_det m.2 i)
    hq (physicalPosition n x)
    ((CommonCoverSolve.coverPower (CorrectionInitialization.CommonWindow.index h n)).symm Y) theta
    (ChartScales.Q (BaseChartJets.cellBand l.1) ^ (-CoordinateAlgebra.A h) *
      Real.sqrt (ChartScales.epsilon h (BaseChartJets.cellBand l.1)) *
        SmoothCovariance.amplitudes P.matrix
          (fun k => PrimaryTargetBounds.actualTarget modulation (nativePoint n x l.1) k) l.2)
    (ChartScales.Q (BaseChartJets.cellBand m.1) ^ (-CoordinateAlgebra.A h) *
      Real.sqrt (ChartScales.epsilon h (BaseChartJets.cellBand m.1)) *
        SmoothCovariance.amplitudes Q.matrix
          (fun k => PrimaryTargetBounds.actualTarget modulation (nativePoint n x m.1) k) m.2)
    (P.modes l.2) (Q.modes m.2) (P.phases l.2) (Q.phases m.2)
  simp only [viewTangent, physicalTangentMode_eq_slot l.2 l.1 _ hpl,
    physicalTangentMode_eq_slot m.2 m.1 _ hpm, slotVelocity_zero, slotVelocity_succ,
    PairData.radialWave, PairData.tangentWave, nativePoint_scale n hT, nativePoint_position]
  simp only [P, Q, amplitude, mul_assoc] at he ⊢
  exact he

theorem viewTangent_diagonal_continuous (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (l : Label B N0 × Fin 2) (hl : l ∈ activeLabels standardRegion B N0 n) (i : Fin 2) :
    (∀ Y, Continuous (fun theta => viewTangent n x l Y theta 0 * viewTangent n x l Y theta i.succ))
      ∧
    Continuous (fun Y => SmoothLoop.angularMean
      (fun theta => viewTangent n x l Y theta 0 * viewTangent n x l Y theta i.succ)) := by
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  by_cases hm : spatialMask l.1 (nativePoint n x l.1) = 0
  · simp only [viewTangent, physicalTangentMode_zero_of_mask l.2 l.1 _ hm, Pi.zero_apply, zero_mul]
    exact ⟨fun _ => continuous_const, continuous_const⟩
  have hp := spatialMask_carrier l.1 (nativePoint_time n hT l.1) hm
  let P := (sourcePair l.1 (nativePoint n x l.1) hp).pairData
  have hlabel : l.1 ∈ unsignedLabels B N0 n := by
    rw [activeLabels_product] at hl
    exact (Finset.mem_product.mp hl).1
  have hi := active_cover_le n hlabel
  simpa only [viewTangent, physicalTangentMode_eq_slot l.2 l.1 _ hp] using
    pair_diagonal_common_continuous P vectors_det hi
      (ChartScales.Q (BaseChartJets.cellBand l.1) ^ (-CoordinateAlgebra.A h))
      (ChartScales.epsilon h (BaseChartJets.cellBand l.1))
      (fun j => PrimaryTargetBounds.actualTarget modulation (nativePoint n x l.1) j)
      (similarityScale l.1 (nativePoint n x l.1)) (position l.1 (nativePoint n x l.1)) l.2 i

theorem viewTangent_pair_covariance (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (L : Label B N0) (hL : L ∈ unsignedLabels B N0 n) (i : Fin 2) :
    (∑ j : Fin 2, doubleAverage (fun Y theta =>
      viewTangent n x (L, j) Y theta 0 * viewTangent n x (L, j) Y theta i.succ)) =
      (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) ^ 2 *
        ChartScales.epsilon h (BaseChartJets.cellBand L) * spatialMask L (nativePoint n x L) ^ 2 *
          PrimaryTargetBounds.actualTarget modulation (nativePoint n x L) i := by
  by_cases hm : spatialMask L (nativePoint n x L) = 0
  · simp only [viewTangent, physicalTangentMode_zero_of_mask _ L _ hm, Pi.zero_apply,
      zero_mul, doubleAverage, SmoothLoop.angularMean, TorusAverages.squareAverage,
      intervalIntegral.integral_zero, zero_div, Finset.sum_const_zero, hm, zero_pow (by decide : (2
        : ℕ) ≠ 0), mul_zero]
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hp := spatialMask_carrier L (nativePoint_time n hT L) hm
  have hK := nativePoint_reference n hx L hm
  have hw := nativePoint_weight_pos n hx L
  have hi := active_cover_le n hL
  have he (j : Fin 2) : doubleAverage (fun Y theta =>
      viewTangent n x (L, j) Y theta 0 * viewTangent n x (L, j) Y theta i.succ) =
      doubleAverage (fun Y theta => physicalTangentMode j L (nativePoint n x L) Y theta 0 *
        physicalTangentMode j L (nativePoint n x L) Y theta i.succ) := by
    simp only [viewTangent, physicalTangentMode_eq_slot j L _ hp]
    rw [pair_diagonal_common (sourcePair L (nativePoint n x L) hp).pairData vectors_det hi]
    symm
    simpa only [slotVelocity_zero, slotVelocity_succ] using
      (sourcePair L (nativePoint n x L) hp).pairData.diagonal_covariance vectors_det
        (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h))
        (ChartScales.epsilon h (BaseChartJets.cellBand L))
        (fun k => PrimaryTargetBounds.actualTarget modulation (nativePoint n x L) k)
        (similarityScale L (nativePoint n x L)) (position L (nativePoint n x L)) j i
  simp_rw [he]
  exact physicalTangentMode_diagonal_covariance L (nativePoint n x L) hp hK hw i

noncomputable def viewSum (B N0 n : ℕ) (x : Point) (Y : Plane) (theta : ℝ) : Fin 3 → ℝ :=
  fun i => ∑ l ∈ activeLabels standardRegion B N0 n, viewTangent n x l Y theta i

theorem viewSum_covariance (B N0 n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (i : Fin 2) :
    doubleAverage (fun Y theta => viewSum B N0 n x Y theta 0 * viewSum B N0 n x Y theta i.succ) =
      ∑ L ∈ unsignedLabels B N0 n,
        (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) ^ 2 *
          ChartScales.epsilon h (BaseChartJets.cellBand L) * spatialMask L (nativePoint n x L) ^ 2 *
            PrimaryTargetBounds.actualTarget modulation (nativePoint n x L) i := by
  have hprod : (fun Y theta => viewSum B N0 n x Y theta 0 * viewSum B N0 n x Y theta i.succ) =
      fun Y theta => ∑ l ∈ activeLabels standardRegion B N0 n,
        viewTangent n x l Y theta 0 * viewTangent n x l Y theta i.succ := by
    funext Y theta
    exact sum_product_diagonal _ _ _ (fun _ _ _ _ hne => viewTangent_cross_zero n hx hne Y theta i)
  rw [hprod, doubleAverage_sum _ _
    (fun l hl => (viewTangent_diagonal_continuous n hx l hl i).1)
    (fun l hl => (viewTangent_diagonal_continuous n hx l hl i).2)]
  rw [activeLabels_product]
  rw [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro L hL
  exact viewTangent_pair_covariance n hx L hL i

noncomputable def physicalLeading (n : ℕ) (x : Point) (i : Fin 2) : ℝ :=
  physicalScale n x ^ (-CoordinateAlgebra.A h - 1 / 2) *
    ProfileSpectralCone.stressVector modulation.profiles h
      (BaseChartJets.normalizedCoordinates h (BaseContextAssembly.slowCoordinates x)).2 i

noncomputable def partitionFactor (B N0 n : ℕ) (x : Point) : ℝ :=
  ∑ L ∈ unsignedLabels B N0 n, spatialMask L (nativePoint n x L) ^ 2

theorem viewSum_covariance_factor (B N0 n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (i : Fin 2) :
    doubleAverage (fun Y theta => viewSum B N0 n x Y theta 0 * viewSum B N0 n x Y theta i.succ) =
      partitionFactor B N0 n x * physicalLeading n x i := by
  rw [viewSum_covariance B N0 n hx i, partitionFactor, Finset.sum_mul]
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  apply Finset.sum_congr rfl
  intro L _
  have hs := physical_covariance_factor L (nativePoint n x L) (nativePoint_time n hT L) i
  rw [nativePoint_scale n hT, nativePoint_inner n hT] at hs
  change _ = spatialMask L (nativePoint n x L) ^ 2 * _
  calc
    _ = spatialMask L (nativePoint n x L) ^ 2 *
      ((ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) ^ 2 *
        ChartScales.epsilon h (BaseChartJets.cellBand L) *
          PrimaryTargetBounds.actualTarget modulation (nativePoint n x L) i) := by ring
    _ = _ := congrArg (fun z => spatialMask L (nativePoint n x L) ^ 2 * z) hs

/-! ## Coverage by the fixed chosen labels -/

theorem chosen_threshold_four (B N0 : ℕ) : 4 ≤ (choice B N0).prepared.N :=
  ((choice B N0).prepared.large _ le_rfl).four_le

theorem physicalScale_pos (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    0 < physicalScale n x :=
  mul_pos (ChartScales.Q_pos n)
    (standardRegion.chartQ_pos ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp
      hx).1)

theorem physicalScale_le_two (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    physicalScale n x ≤ 2 := by
  have hq := standardRegion.q_mem x.2.1
    ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp hx).1
  change SimilarityCoordinates.coordinateQ (2 * h) x.2.1 ∈ Icc (1 / 2 : ℝ) 2 at hq
  exact (mul_le_mul_of_nonneg_left hq.2 (ChartScales.Q_pos n).le).trans
    (by nlinarith [ChartScales.Q_le_one n])

theorem physicalScale_forward (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    SimilarityCoordinates.forwardScalar (2 * h) (physicalPosition n x 1) (physicalScale n x) =
      physicalPosition n x 2 := by
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hq := SimilarityCoordinates.coordinateQ_spec
    (by linarith [outgoing.data.h_pos] : 0 < 2 * h)
    (by linarith [outgoing.data.h_lt_half] : 2 * h < 1) hT
  have hs := SimilarityHomogeneity.forwardScalar_scale (ChartScales.Q_pos n) hq.1 (2 * h) x.2.1.2
  change SimilarityCoordinates.forwardScalar (2 * h)
    (ChartScales.Q n ^ CoordinateAlgebra.D h * x.2.1.2)
    (ChartScales.Q n * SimilarityCoordinates.coordinateQ (2 * h) x.2.1) = ChartScales.Q n * x.2.1.1
  simpa only [show (1 - 2 * h) / 2 = CoordinateAlgebra.D h by unfold CoordinateAlgebra.D; ring,
    hq.2] using hs

theorem physicalPosition_normalized (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    physicalPosition n x 0 ^ 2 / (2 * physicalScale n x) =
      (BaseChartJets.normalizedCoordinates h (BaseContextAssembly.slowCoordinates x)).2.1 := by
  have hQ := (ChartScales.Q_pos n).ne'
  have hq : SimilarityCoordinates.coordinateQ (2 * h) x.2.1 ≠ 0 :=
    (show 0 < SimilarityCoordinates.coordinateQ (2 * h) x.2.1 from
      standardRegion.chartQ_pos ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp
        hx).1).ne'
  simp only [physicalPosition, physicalScale, Matrix.cons_val_zero, mul_pow,
    Real.sq_sqrt (ChartScales.Q_pos n).le, BaseChartJets.normalizedCoordinates_eq,
      SimilarityHomogeneity.chartX,
    SimilarityCoordinates.coordinateX, SimilarityHomogeneity.chartQ,
    BaseContextAssembly.slowCoordinates_apply]
  field_simp [hQ, hq]

noncomputable def relativeLabel (B N0 : ℕ) (L : Label B N0) : UnsignedLabel :=
  ((PrimaryGeometryAssembly.label nominal L).1 - (choice B N0).prepared.N,
    (PrimaryGeometryAssembly.label nominal L).2)

theorem relativeLabel_tail (B N0 : ℕ) (L : Label B N0) :
    tailLabel (choice B N0).prepared.N (relativeLabel B N0 L) = PrimaryGeometryAssembly.label
      nominal L := by
  exact Prod.ext (Nat.sub_add_cancel L.property) rfl

theorem relativeLabel_injective (B N0 : ℕ) : Function.Injective (relativeLabel B N0) := by
  intro L M hLM
  apply PrimaryGeometryAssembly.label_injective nominal
  rw [← relativeLabel_tail B N0 L, ← relativeLabel_tail B N0 M, hLM]

theorem partitionFactor_eq_tail (B N0 n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    partitionFactor B N0 n x =
      ∑ᶠ U : UnsignedLabel, mask (CoordinateAlgebra.D h)
        (tailLabel (choice B N0).prepared.N U) (physicalScale n x) (physicalPosition n x) ^ 2 := by
  classical
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hR := BaseContextAssembly.nativeStrip_radius nominal standardRegion hx
  have hq := physicalScale_pos n hx
  have hX := (BaseContextAssembly.nativeStrip_active nominal standardRegion hx).1
  have hfinite : (∑ᶠ U : UnsignedLabel, mask (CoordinateAlgebra.D h)
        (tailLabel (choice B N0).prepared.N U) (physicalScale n x) (physicalPosition n x) ^ 2) =
      ∑ U ∈ (unsignedLabels B N0 n).image (relativeLabel B N0), mask (CoordinateAlgebra.D h)
        (tailLabel (choice B N0).prepared.N U) (physicalScale n x) (physicalPosition n x) ^ 2 := by
    apply finsum_eq_sum_of_support_subset
    intro U hU
    have hm : mask (CoordinateAlgebra.D h) (tailLabel (choice B N0).prepared.N U)
        (physicalScale n x) (physicalPosition n x) ≠ 0 := by
      intro he
      exact hU (by simp [he])
    obtain ⟨L, hL⟩ := PrimaryGeometryAssembly.physicalMask_has_index nominal
      (tailLabel (choice B N0).prepared.N U)
      (show 1 ≤ (tailLabel (choice B N0).prepared.N U).1 by
        have hh := chosen_threshold_four B N0
        change 1 ≤ U.1 + (choice B N0).prepared.N
        omega)
      (Nat.le_add_left _ _) hq
      (show 0 ≤ physicalPosition n x 0 by
        exact (mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) hR).le)
      (show 0 < physicalPosition n x 2 from mul_pos (ChartScales.Q_pos n) hT)
      (physicalScale_forward n hx)
      (by rw [physicalPosition_normalized n hx]; exact ⟨hX.1.le, hX.2.le⟩) hm
    have hmL : mask (CoordinateAlgebra.D h) (PrimaryGeometryAssembly.label nominal L)
        (physicalScale n x) (physicalPosition n x) ≠ 0 := by simpa only [hL] using hm
    have hactive := activeLabels_cover n hx L (0 : Fin 2)
      (PhysicalWaveSum.physicalMask_support_subset _ _ hmL)
    refine Finset.mem_image.mpr ⟨L, (mem_unsignedLabels n L).mpr hactive, ?_⟩
    apply tailLabel_injective (choice B N0).prepared.N
    rw [relativeLabel_tail, hL]
  rw [hfinite, Finset.sum_image (relativeLabel_injective B N0).injOn]
  apply Finset.sum_congr rfl
  intro L _
  rw [relativeLabel_tail, ← nativePoint_mask n hT]

theorem partitionFactor_eq_one (B N0 n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (hq : physicalScale n x ≤ ChartScales.Q (choice B N0).prepared.N) :
    partitionFactor B N0 n x = 1 := by
  rw [partitionFactor_eq_tail B N0 n hx]
  exact physical_mask_tail_sum_sq _ _ (physicalScale_pos n hx) hq _

theorem Q_antitone : Antitone ChartScales.Q := by
  intro m n hmn
  unfold ChartScales.Q SlotColoring.dyadicQ
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (neg_le_neg (by exact_mod_cast hmn : (m : ℝ) ≤ (n : ℝ)))

theorem Q_succ (n : ℕ) : ChartScales.Q (n + 1) = ChartScales.Q n / 2 := by
  unfold ChartScales.Q SlotColoring.dyadicQ
  rw [Nat.cast_add, Nat.cast_one, neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  ring

theorem physicalScale_tail (B N0 : ℕ) {n : ℕ} (hn : (choice B N0).prepared.N + 1 ≤ n)
    {x : Point} (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    physicalScale n x ≤ ChartScales.Q (choice B N0).prepared.N := by
  have hq := standardRegion.q_mem x.2.1
    ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp hx).1
  change SimilarityCoordinates.coordinateQ (2 * h) x.2.1 ∈ Icc (1 / 2 : ℝ) 2 at hq
  have hnQ := Q_antitone hn
  rw [Q_succ] at hnQ
  exact (mul_le_mul_of_nonneg_left hq.2 (ChartScales.Q_pos n).le).trans (by linarith)

/-! ## Covariance of the literal initialized tangent pieces -/

noncomputable def tangentSum (B N0 : ℕ) : CorrectionState.Oscillation Point :=
  fun n z i => ∑ l ∈ activeLabels standardRegion B N0 n,
    (piece standardRegion l.2 l.1).tangentVelocity n z i

noncomputable def tangentCovariance (B N0 : ℕ) (i j : Fin 3) :
    CorrectionState.ScalarField Point :=
  CorrectionState.bilinearCovariance (tangentSum B N0) (tangentSum B N0) i j

noncomputable def leadingStress (i : Fin 2) (n : ℕ) (x : Point) : ℝ :=
  if i = 0 then (BaseContextAssembly.leadingVirtualStress certificate modulation n x).1
  else (BaseContextAssembly.leadingVirtualStress certificate modulation n x).2

theorem tangentSum_eq_viewSum (B N0 n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (Y : Plane) (theta : ℝ) (i : Fin 3) :
    tangentSum B N0 n ((x.1, (x.2.1, Y)), theta) i =
      ChartScales.Q n ^ CoordinateAlgebra.A h * viewSum B N0 n x Y theta i := by
  unfold tangentSum viewSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hr := ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp hx).2
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hR := BaseContextAssembly.nativeStrip_radius nominal standardRegion hx
  have hrad : PrimaryTargetBounds.profileRadius h (nativePoint n x l.1) ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) := by
    rwa [nativePoint_profileRadius n hT hR]
  rw [piece_tangent_representation,
    absoluteTangent_eq l.2 l.1 (toAbsolute n (x.1, (x.2.1, Y)), theta) hrad]
  rfl

theorem chart_physical_leading (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (i : Fin 2) :
    (ChartScales.Q n ^ CoordinateAlgebra.A h) ^ 2 * physicalLeading n x i = leadingStress i n x :=
      by
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hR := BaseContextAssembly.nativeStrip_radius nominal standardRegion hx
  have hq := standardRegion.chartQ_pos
    ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp hx).1
  change 0 < SimilarityCoordinates.coordinateQ (2 * h) x.2.1 at hq
  have hs : (ChartScales.Q n ^ CoordinateAlgebra.A h) ^ 2 *
      physicalScale n x ^ (-CoordinateAlgebra.A h - 1 / 2) =
      ChartScales.epsilon h n *
        SimilarityCoordinates.coordinateQ (2 * h) x.2.1 ^ (-CoordinateAlgebra.A h - 1 / 2) := by
    rw [physicalScale, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le,
      Real.mul_rpow (ChartScales.Q_pos n).le hq.le, ← mul_assoc,
      ← Real.rpow_add (ChartScales.Q_pos n)]
    congr 1
    congr 1
    unfold CoordinateAlgebra.A
    norm_num
    ring
  unfold physicalLeading leadingStress
  rw [← mul_assoc, hs, BaseContextAssembly.leadingVirtualStress_eq certificate modulation n hT hR]
  fin_cases i <;>
    simp [FinalSlowBase.leadingStress, LeadingStressWeights.stress,
      ProfileSpectralCone.stressVector,
      BaseChartJets.normalizedCoordinates_eq, SimilarityHomogeneity.chartQ,
      BaseContextAssembly.slowCoordinates_apply]

theorem mean_tangentCovariance_factor (B N0 n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (i : Fin 2) :
    StateMomentBalances.meanBar (tangentCovariance B N0 0 i.succ) n x =
      partitionFactor B N0 n x * leadingStress i n x := by
  change doubleAverage (fun Y theta => tangentSum B N0 n ((x.1, (x.2.1, Y)), theta) 0 *
    tangentSum B N0 n ((x.1, (x.2.1, Y)), theta) i.succ) = _
  simp_rw [tangentSum_eq_viewSum B N0 n hx]
  have hprod : (fun Y theta =>
      (ChartScales.Q n ^ CoordinateAlgebra.A h * viewSum B N0 n x Y theta 0) *
      (ChartScales.Q n ^ CoordinateAlgebra.A h * viewSum B N0 n x Y theta i.succ)) =
      fun Y theta => (ChartScales.Q n ^ CoordinateAlgebra.A h) ^ 2 *
        (viewSum B N0 n x Y theta 0 * viewSum B N0 n x Y theta i.succ) := by
    funext Y theta
    ring
  rw [hprod, doubleAverage_const_mul, viewSum_covariance_factor B N0 n hx i,
    mul_left_comm, chart_physical_leading n hx i]

theorem mean_tangentCovariance_eq_leading (B N0 : ℕ) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (i : Fin 2) :
    StateMomentBalances.meanBar (tangentCovariance B N0 0 i.succ) n x = leadingStress i n x := by
  rw [mean_tangentCovariance_factor B N0 n hx i,
    partitionFactor_eq_one B N0 n hx (physicalScale_tail B N0 hn hx), one_mul]

theorem mean_tangentCovariance_jets (B N0 : ℕ) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (i : Fin 2) (m : ℕ) :
    iteratedFDeriv ℝ m (StateMomentBalances.meanBar (tangentCovariance B N0 0 i.succ) n) x =
      iteratedFDeriv ℝ m (leadingStress i n) x := by
  apply (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (eventually_of_mem ((BaseContextAssembly.nativeStrip nominal
      standardRegion).isOpen_domain.mem_nhds hx)
      (fun y hy => mean_tangentCovariance_eq_leading B N0 hn hy i)) m).self_of_nhds

/-! ## The exact finite low-band defect -/

noncomputable def dyadicTail (N : ℕ) (q : ℝ) : ℝ :=
  ∑ᶠ n : ℕ, SquaredPartition.dyadicMask ((n + N : ℕ) : ℤ) q ^ 2

theorem mask_tail_eq_dyadicTail (D : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q)
    (x : SlotColoring.Position) :
    (∑ᶠ U : UnsignedLabel, mask D (tailLabel N U) q x ^ 2) = dyadicTail N q := by
  have hf : (support (fun U : UnsignedLabel => mask D (tailLabel N U) q x ^ 2)).Finite := by
    apply (finite_active_masks D N hq x).subset
    intro U hU hz
    exact hU (by simp [hz])
  rw [SquaredPartition.finsum_pair_eq hf]
  have hrow (n : ℕ) : (∑ᶠ k : SlotColoring.Grid, mask D (tailLabel N (n, k)) q x ^ 2) =
      SquaredPartition.dyadicMask ((n + N : ℕ) : ℤ) q ^ 2 := by
    have hk : (support (fun k : SlotColoring.Grid =>
        SquaredPartition.physicalSlowMask D (n + N) k x ^ 2)).Finite := by
      apply ((SquaredPartition.physicalSlowMask_locallyFinite D (n + N)).point_finite x).subset
      intro k hk hz
      exact hk (by simp [hz])
    simp only [mask, physicalMask, signedLabel, tailLabel, mul_pow]
    rw [← mul_finsum _ _, SquaredPartition.physicalSlowMask_sum_sq, mul_one]
  simp_rw [hrow]
  rfl

noncomputable def missingWeight (N : ℕ) (q : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc (-1 : ℤ) ((N : ℤ) - 1), SquaredPartition.dyadicMask m q ^ 2

theorem missingWeight_smooth (N : ℕ) : ContDiff ℝ ∞ (missingWeight N) :=
  ContDiff.sum (fun m _ => (SquaredPartition.dyadicMask_smooth m).pow 2)

theorem missingWeight_compact (N : ℕ) : HasCompactSupport (missingWeight N) := by
  have hall (s : Finset ℤ) : HasCompactSupport (fun q => ∑ m ∈ s, SquaredPartition.dyadicMask m q ^
    2) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℝ))
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact ((SquaredPartition.dyadicMask_compactSupport a).comp_left
        (g := fun z : ℝ => z ^ 2) (by norm_num)).add ih
  exact hall _

theorem dyadicMask_zero_below_minus_one {q : ℝ} (hq : q ≤ 2) {m : ℤ} (hm : m < -1) :
    SquaredPartition.dyadicMask m q = 0 := by
  by_contra hn
  have hs : q ∈ support (SquaredPartition.dyadicMask m) := hn
  rw [SquaredPartition.dyadicMask_support] at hs
  have hmR : (2 : ℝ) ≤ -(m : ℝ) := by exact_mod_cast (show (2 : ℤ) ≤ -m by omega)
  have h4 : (4 : ℝ) ≤ SquaredPartition.integerQ m := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hmR
  linarith [hs.1]

theorem missingWeight_add_tail (N : ℕ) {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    missingWeight N q + dyadicTail N q = 1 := by
  let f : ℤ → ℝ := fun m => SquaredPartition.dyadicMask m q ^ 2
  have hf : (support f).Finite := by
    apply (SquaredPartition.dyadicMask_locallyFinite.point_finite (⟨q, hq⟩ : Ioi (0 : ℝ))).subset
    intro m hm hz
    exact hm (by simp [f, hz])
  have hlo : (∑ᶠ m ∈ Iio (N : ℤ), f m) = missingWeight N q := by
    calc
      _ = ∑ᶠ m ∈ (Finset.Icc (-1 : ℤ) ((N : ℤ) - 1) : Set ℤ), f m := by
        apply finsum_mem_inter_support_eq'
        intro m hm
        have hm1 : -1 ≤ m := by
          by_contra hn
          exact hm (by simp [f, dyadicMask_zero_below_minus_one hq2 (lt_of_not_ge hn)])
        simp only [mem_Iio, Finset.mem_coe, Finset.mem_Icc]
        omega
      _ = _ := finsum_mem_coe_finset _ _
  have hrange : range (fun m : ℕ => ((m + N : ℕ) : ℤ)) = Ici (N : ℤ) := by
    ext k
    constructor
    · rintro ⟨m, rfl⟩
      change (N : ℤ) ≤ ((m + N : ℕ) : ℤ)
      omega
    · intro hk
      refine ⟨(k - N).toNat, ?_⟩
      change (N : ℤ) ≤ k at hk
      change (((k - N).toNat + N : ℕ) : ℤ) = k
      rw [Nat.cast_add, Int.toNat_of_nonneg (by omega)]
      omega
  have hhi : (∑ᶠ m ∈ Ici (N : ℤ), f m) = dyadicTail N q := by
    rw [← hrange, finsum_mem_range (show Injective (fun m : ℕ => ((m + N : ℕ) : ℤ)) by
      intro a b hab
      dsimp only at hab
      exact Nat.add_right_cancel (Int.ofNat_inj.mp hab))]
    rfl
  have hs := finsum_mem_union' (f := f)
    (show Disjoint (Iio (N : ℤ)) (Ici (N : ℤ)) from
      Set.disjoint_left.mpr (by
        intro k hi hj
        exact (not_le_of_gt (show k < (N : ℤ) from hi)) (show (N : ℤ) ≤ k from hj)))
    (hf.subset inter_subset_right) (hf.subset inter_subset_right)
  rw [Iio_union_Ici, finsum_mem_univ, hlo, hhi] at hs
  exact hs.symm.trans (SquaredPartition.dyadicMask_sum_sq hq)

theorem partitionFactor_eq_one_sub_missing (B N0 n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    partitionFactor B N0 n x = 1 - missingWeight (choice B N0).prepared.N (physicalScale n x) := by
  rw [partitionFactor_eq_tail B N0 n hx,
    mask_tail_eq_dyadicTail _ _ (physicalScale_pos n hx)]
  linarith [missingWeight_add_tail (choice B N0).prepared.N (physicalScale_pos n hx)
    (physicalScale_le_two n hx)]

noncomputable def averagedDefect (B N0 : ℕ) (i : Fin 2) : CorrectionState.ScalarField Point :=
  StateMomentBalances.meanBar (tangentCovariance B N0 0 i.succ) - leadingStress i

theorem averagedDefect_eq (B N0 n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (i : Fin 2) :
    averagedDefect B N0 i n x =
      -missingWeight (choice B N0).prepared.N (physicalScale n x) * leadingStress i n x := by
  simp only [averagedDefect, Pi.sub_apply]
  rw [mean_tangentCovariance_factor B N0 n hx i, partitionFactor_eq_one_sub_missing B N0 n hx]
  ring

theorem averagedDefect_zero_tail (B N0 : ℕ) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (i : Fin 2) :
    averagedDefect B N0 i n x = 0 := by
  simp only [averagedDefect, Pi.sub_apply, mean_tangentCovariance_eq_leading B N0 hn hx i, sub_self]

/-! ## All-order bounds for the retained finite prefix -/

open WeightedClasses

/-- An actual class whose fields vanish after a fixed band has every
exponent.  The new constant is one finite sum of powers of the original
positive band scales, chosen before the band and spatial point. -/
theorem memClass_of_finite_bands {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData D} {w : ℕ → D → ℝ} {alpha beta : ℝ} {f : ℕ → D → E}
    (hf : MemClass s w alpha f) (N : ℕ)
    (hz : ∀ n, N ≤ n → ∀ x ∈ s.domain, f n x = 0) : MemClass s w beta f := by
  let K : ℝ := 1 + ∑ n ∈ Finset.range N, s.epsilon n ^ (alpha - beta)
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, s.epsilon n ^ (alpha - beta) :=
    Finset.sum_nonneg (fun n _ => (Real.rpow_pos_of_pos (s.epsilon_pos n) _).le)
  have hK : 0 ≤ K := by dsimp [K]; linarith
  refine ⟨hf.weight_nonneg, hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C * K, mul_nonneg hC hK, p, ?_⟩
  intro n x hx j hj
  by_cases hn : N ≤ n
  · have he : f n =ᶠ[𝓝 x] fun _ => 0 :=
      eventually_of_mem (s.isOpen_domain.mem_nhds hx) (fun y hy => hz n hn y hy)
    rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq he j).self_of_nhds]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using
      majorant_nonneg s w beta (mul_nonneg hC hK) p n x (hf.weight_nonneg n x hx)
  · have hratio : s.epsilon n ^ (alpha - beta) ≤ K := by
      have he := Finset.single_le_sum
        (fun k (_hk : k ∈ Finset.range N) => (Real.rpow_pos_of_pos (s.epsilon_pos k) (alpha -
          beta)).le)
        (Finset.mem_range.mpr (lt_of_not_ge hn))
      exact he.trans (le_add_of_nonneg_left zero_le_one)
    have heps : s.epsilon n ^ alpha = s.epsilon n ^ (alpha - beta) * s.epsilon n ^ beta := by
      rw [← Real.rpow_add (s.epsilon_pos n)]
      congr 1
      ring
    apply (hb n x hx j hj).trans
    unfold majorant
    apply mul_le_mul_of_nonneg_right _ (hf.weight_nonneg n x hx)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (s.growth_nonneg n x) p)
    rw [heps, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC)
      (Real.rpow_pos_of_pos (s.epsilon_pos n) beta).le

theorem physicalScale_unweighted :
    UnweightedClass (BaseContextAssembly.nativeStrip nominal standardRegion) 0 physicalScale := by
  have hq := (BaseStressClasses.coordinates_unweighted nominal standardRegion).map
    (ContinuousLinearMap.fst ℝ ℝ SlowBorelBase.Inner)
  have hband : BandBound (BaseContextAssembly.nativeStrip nominal standardRegion) 0 ChartScales.Q
    := by
    refine ⟨1, zero_le_one, 0, fun n => ?_⟩
    simpa only [Real.norm_of_nonneg (ChartScales.Q_pos n).le, Real.rpow_zero, one_mul,
      pow_zero, mul_one] using ChartScales.Q_le_one n
  have hc := hq.band_smul hband
  simp only [zero_add, smul_eq_mul, BaseStressClasses.coordinates,
    BaseChartJets.normalizedCoordinates_eq, SimilarityHomogeneity.chartQ,
    BaseContextAssembly.slowCoordinates_apply] at hc ⊢
  exact hc

theorem missingWeight_unweighted (N : ℕ) :
    UnweightedClass (BaseContextAssembly.nativeStrip nominal standardRegion) 0
      (fun n x => missingWeight N (physicalScale n x)) := by
  apply BaseStressClasses.class_comp_of_outer_jets (U := Set.univ) isOpen_univ
    (fun _ => (missingWeight_smooth N).contDiffOn) physicalScale_unweighted
    (fun _ _ _ => Set.mem_univ _) (fun _ _ _ => zero_le_one)
  intro j
  obtain ⟨C, hC, hb⟩ := SquaredPartition.exists_uniform_jet_bound
    (missingWeight_smooth N) (missingWeight_compact N) j
  refine ⟨C, hC.le, 0, fun n x _ => ?_⟩
  simpa only [majorant, Real.rpow_zero, pow_zero, mul_one] using hb (physicalScale n x)

theorem leadingStress_meanClass (i : Fin 2) :
    MeanClass (BaseContextAssembly.nativeStrip nominal standardRegion) 1 (leadingStress i) := by
  have hc := BaseStressClasses.leadingVirtualStress_meanClass certificate modulation
    profile.fullTrueCone standardRegion
  fin_cases i
  · have hm := hc.map (ContinuousLinearMap.fst ℝ ℝ ℝ)
    simp [] at hm ⊢
    exact hm
  · have hm := hc.map (ContinuousLinearMap.snd ℝ ℝ ℝ)
    simp [] at hm ⊢
    exact hm

theorem averagedDefect_meanClass_one (B N0 : ℕ) (i : Fin 2) :
    MeanClass (BaseContextAssembly.nativeStrip nominal standardRegion) 1 (averagedDefect B N0 i) :=
      by
  have hc := (CurlClassBounds.class_neg (missingWeight_unweighted (choice B N0).prepared.N)).mul
    (leadingStress_meanClass i)
  have hm : MeanClass (BaseContextAssembly.nativeStrip nominal standardRegion) 1
      (fun n x => -missingWeight (choice B N0).prepared.N (physicalScale n x) * leadingStress i n
        x) := by
    simpa only [MeanClass, UnweightedClass, one_mul, zero_add] using hc
  exact CurlClassBounds.class_congr hm (fun n x hx => (averagedDefect_eq B N0 n hx i).symm)

/-- The finite omitted primary prefix is an actual error in every mean
class, with no new threshold or primary choice and no assumption on the
assembled covariance. -/
theorem averagedDefect_meanClass (B N0 : ℕ) (i : Fin 2) (beta : ℝ) :
    MeanClass (BaseContextAssembly.nativeStrip nominal standardRegion) beta (averagedDefect B N0 i)
      :=
  memClass_of_finite_bands (averagedDefect_meanClass_one B N0 i)
    ((choice B N0).prepared.N + 1)
    (fun _ hn _ hx => averagedDefect_zero_tail B N0 hn hx i)

/-- Every actual spatial derivative of the averaged covariance error has
the same arbitrary exponent; the finite-prefix constants may depend on
the chosen exponent and derivative order. -/
theorem averagedDefect_derivative_meanClass (B N0 : ℕ) (i : Fin 2) (beta : ℝ) :
    MeanClass (BaseContextAssembly.nativeStrip nominal standardRegion) beta
      (fun n => fderiv ℝ (averagedDefect B N0 i n)) :=
  (averagedDefect_meanClass B N0 i beta).fderiv

theorem averagedDefect_radialDiv_meanClass (B N0 : ℕ) (i : Fin 2) (beta weight : ℝ) :
    MeanClass (BaseContextAssembly.nativeStrip nominal standardRegion) beta
      ((commonContext B).operators.radialDiv weight (averagedDefect B N0 i)) := by
  have ho := CommonBaseContext.context_operator_bounds certificate modulation upper B standardRegion
    (CorrectionInitialization.CommonWindow.index_le_native h)
  have hc := ho.radialDiv (averagedDefect_meanClass B N0 i (beta + ChartScales.kappa)) weight
  simp only [add_sub_cancel_right] at hc
  exact hc

/-! ## Direct interfaces for the initial mean balance -/

theorem meanBar_of_fiber_constant (f : CorrectionState.ScalarField Point)
    (hf : ∀ n x Y, f n (x.1, (x.2.1, Y)) = f n x) : StateMomentBalances.meanBar f = f := by
  funext n x
  change (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f n (x.1, (x.2.1, (z, y)))) = f n x
  simp only [hf, intervalIntegral.integral_const, sub_zero, one_smul]

theorem meanBar_leadingStress (i : Fin 2) :
    StateMomentBalances.meanBar (leadingStress i) = leadingStress i :=
  meanBar_of_fiber_constant _ (fun _ _ _ => rfl)

theorem meanBar_virtualTheta (B : ℕ) :
    StateMomentBalances.meanBar (commonContext B).virtualTheta = (commonContext B).virtualTheta :=
  meanBar_of_fiber_constant _ (fun _ _ _ => rfl)

theorem meanBar_virtualAxial (B : ℕ) :
    StateMomentBalances.meanBar (commonContext B).virtualAxial = (commonContext B).virtualAxial :=
  meanBar_of_fiber_constant _ (fun _ _ _ => rfl)

/-- The measured tangent covariance matches the same full virtual stress
up to its actual order-two Borel remainder and the explicitly retained
finite primary prefix.  This supplies both initial averaged radial fluxes. -/
theorem tangent_virtual_bar_meanClass (B N0 : ℕ) :
    MeanClass (BaseContextAssembly.nativeStrip nominal standardRegion) 2
      (StateMomentBalances.meanBar (tangentCovariance B N0 0 1) -
        StateMomentBalances.meanBar (commonContext B).virtualTheta) ∧
    MeanClass (BaseContextAssembly.nativeStrip nominal standardRegion) 2
      (StateMomentBalances.meanBar (tangentCovariance B N0 0 2) -
        StateMomentBalances.meanBar (commonContext B).virtualAxial) := by
  have hhigh := CommonBaseContext.context_higher_stress_classes certificate modulation upper B
    standardRegion (CorrectionInitialization.CommonWindow.index h)
  constructor
  · apply CurlClassBounds.class_congr (CurlClassBounds.class_sub
      (averagedDefect_meanClass B N0 0 2) hhigh.1)
    intro n x _
    rw [meanBar_virtualTheta]
    change (StateMomentBalances.meanBar (tangentCovariance B N0 0 1) n x -
      (BaseContextAssembly.leadingVirtualStress certificate modulation n x).1) -
      ((commonContext B).virtualTheta n x -
        (BaseContextAssembly.leadingVirtualStress certificate modulation n x).1) =
      StateMomentBalances.meanBar (tangentCovariance B N0 0 1) n x - (commonContext B).virtualTheta
        n x
    ring
  · apply CurlClassBounds.class_congr (CurlClassBounds.class_sub
      (averagedDefect_meanClass B N0 1 2) hhigh.2)
    intro n x _
    rw [meanBar_virtualAxial]
    change (StateMomentBalances.meanBar (tangentCovariance B N0 0 2) n x -
      (BaseContextAssembly.leadingVirtualStress certificate modulation n x).2) -
      ((commonContext B).virtualAxial n x -
        (BaseContextAssembly.leadingVirtualStress certificate modulation n x).2) =
      StateMomentBalances.meanBar (tangentCovariance B N0 0 2) n x - (commonContext B).virtualAxial
        n x
    ring

/-! ## Actual closed support and separation on the common chart

The support statements use the literal cut amplitude.  Compactness of the
padded native rectangle gives closed lifted support on the torus, so passing
from nonzero values to topological support requires no false zero-germ
claim at an edge.  The common-chart disjointness statements retain the
intersection with the genuine open domain.
-/

theorem quotientPoint_eq_of_torusEq {x y : Plane} (hxy : SlotGeometry.torusEq x y) :
    TorusAverages.quotientPoint x = TorusAverages.quotientPoint y := by
  rcases hxy with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  apply Prod.ext
  · apply sub_eq_zero.mp
    change (x.1 : UnitAddCircle) - (y.1 : UnitAddCircle) = 0
    rw [← AddCircle.coe_sub]
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨a, by simp only [zsmul_eq_mul, mul_one]; exact ha⟩
  · apply sub_eq_zero.mp
    change (x.2 : UnitAddCircle) - (y.2 : UnitAddCircle) = 0
    rw [← AddCircle.coe_sub]
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨b, by simp only [zsmul_eq_mul, mul_one]; exact hb⟩

theorem quotientPoint_continuous : Continuous TorusAverages.quotientPoint :=
  ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)

theorem orientedRectangle_isCompact (c a b : Plane) (r : ℝ) :
    IsCompact (SlotGeometry.orientedRectangle c a b r) := by
  have he : SlotGeometry.orientedRectangle c a b r =
      (fun z : Plane => c + z.1 • a + z.2 • b) '' (Icc (-r) r ×ˢ Icc (-r) r) := by
    ext x
    constructor
    · rintro ⟨u, v, hu, hv, rfl⟩
      exact ⟨(u, v), ⟨abs_le.mp hu, abs_le.mp hv⟩, rfl⟩
    · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
      exact ⟨u, v, abs_le.mpr hu, abs_le.mpr hv, rfl⟩
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image
    ((continuous_const.add (continuous_fst.smul continuous_const)).add
      (continuous_snd.smul continuous_const))

theorem liftedSupport_isClosed (n : ℕ) {S : Set Plane} (hS : IsCompact S) :
    IsClosed (SlotGeometry.liftedSupport n S) := by
  have he : SlotGeometry.liftedSupport n S =
      (fun Y => TorusAverages.quotientPoint ((SlotGeometry.cover ^ n) Y)) ⁻¹'
        (TorusAverages.quotientPoint '' S) := by
    ext Y
    constructor
    · rintro ⟨x, hx, hYx⟩
      exact ⟨x, hx, (quotientPoint_eq_of_torusEq hYx).symm⟩
    · rintro ⟨x, hx, hYx⟩
      exact ⟨x, hx, quotient_eq_torusEq hYx.symm⟩
  rw [he]
  exact (hS.image quotientPoint_continuous).isClosed.preimage
    (quotientPoint_continuous.comp (SlotGeometry.cover ^ n).continuous)

theorem slotAmplitude_supported {D h : ℝ} {vr vt : Plane}
    {sys : SlotSystem D h vr vt} {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer epsilon : ℝ)
    (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) {Y : Plane}
    (hY : slotAmplitude P hdet outer epsilon T q x j Y ≠ 0) :
    Y ∈ SlotGeometry.liftedSupport (SlotColoring.nativeIndex h U.1)
      (slotSet h sys.radius vr vt (signedLabel U j)) := by
  by_contra hout
  apply hY
  funext i
  have hz : coveredVector P hdet j Y i = 0 := by
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [coveredVector_zero]
      by_contra hn
      exact hout (covered_support (P.rawRadial_support hdet j) _ hn)
    · rw [coveredVector_succ]
      by_contra hn
      exact hout (covered_support (P.rawTangent_support hdet j k) _ hn)
  simp only [slotAmplitude, hz, mul_zero, Complex.ofReal_zero, Pi.zero_apply]

noncomputable def absoluteAuxiliary (n : ℕ) (x : Point) : Plane :=
  (CommonCoverSolve.coverPower (CorrectionInitialization.CommonWindow.index h n)).symm x.2.2

theorem absoluteAuxiliary_continuous (n : ℕ) : Continuous (absoluteAuxiliary n) :=
  (CommonCoverSolve.coverPower (CorrectionInitialization.CommonWindow.index h
    n)).symm.continuous.comp
    (continuous_snd.comp continuous_snd)

noncomputable def physicalWindow (n : ℕ) (x : Point) : LabelSumBounds.WindowPoint :=
  (SquaredPartition.logCoordinate (physicalScale n x), physicalPosition n x)

theorem physicalPosition_continuous (n : ℕ) : Continuous (physicalPosition n) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun x : Point => Real.sqrt (ChartScales.Q n) * x.1)
    fun_prop
  · change Continuous (fun x : Point => ChartScales.Q n ^ CoordinateAlgebra.D h * x.2.1.2)
    fun_prop
  · change Continuous (fun x : Point => ChartScales.Q n * x.2.1.1)
    fun_prop

theorem physicalScale_continuousAt (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    ContinuousAt (physicalScale n) x :=
  ((physicalScale_unweighted.smooth n).contDiffAt
    ((BaseContextAssembly.nativeStrip nominal standardRegion).isOpen_domain.mem_nhds
      hx)).continuousAt

theorem physicalWindow_continuousOn (n : ℕ) :
    ContinuousOn (physicalWindow n) (BaseContextAssembly.nativeStrip nominal standardRegion).domain
      := by
  intro x hx
  exact (((((physicalScale_continuousAt n hx).log (physicalScale_pos n hx).ne').neg).div_const
    (Real.log 2)).prodMk (physicalPosition_continuous n).continuousAt).continuousWithinAt

noncomputable def cutAmplitude (j : Fin 2) (L : Label B N0) (n : ℕ) :
    FullPoint → HarmonicCalculus.ComplexVector :=
  ((chartCoefficients j L).withCutoff (chartCutoff j L)).amplitude n

theorem cutAmplitude_eq_common (j : Fin 2) (L : Label B N0) (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (theta : ℝ) :
    cutAmplitude j L n (x, theta) =
      (ChartScales.Q n ^ CoordinateAlgebra.A h *
        ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) •
      commonAmplitude j L (nativePoint n x L) (absoluteAuxiliary n x) := by
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hR := BaseContextAssembly.nativeStrip_radius nominal standardRegion hx
  have hr := ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp hx).2
  have hrad : PrimaryTargetBounds.profileRadius h (nativePoint n x L) ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) := by
    rwa [nativePoint_profileRadius n hT hR]
  change periodicGaussian j L (absoluteAuxiliary n x) •
      (ChartScales.Q n ^ CoordinateAlgebra.A h •
        (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h) •
          uncutAmplitude j L (nativePoint n x L) (absoluteAuxiliary n x))) = _
  calc
    _ = (ChartScales.Q n ^ CoordinateAlgebra.A h *
        ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h)) •
        (periodicGaussian j L (absoluteAuxiliary n x) •
          uncutAmplitude j L (nativePoint n x L) (absoluteAuxiliary n x)) := by
      simp only [smul_smul]
      congr 1
      ring
    _ = _ := by rw [periodic_cutoff_amplitude j L _ hrad]

theorem cutAmplitude_support (j : Fin 2) (L : Label B N0) (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (theta : ℝ)
    (hn : cutAmplitude j L n (x, theta) ≠ 0) :
    (physicalScale n x, physicalPosition n x) ∈
        PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h) (signedLabelOf (L, j)) ∧
      absoluteAuxiliary n x ∈ SlotGeometry.liftedSupport
        (SlotColoring.nativeIndex h (signedLabelOf (L, j)).1)
        (slotSet h slots.radius radialVector temporalVector (signedLabelOf (L, j))) := by
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hc : commonAmplitude j L (nativePoint n x L) (absoluteAuxiliary n x) ≠ 0 := by
    intro hz
    exact hn (by rw [cutAmplitude_eq_common j L n hx, hz, smul_zero])
  have hm : spatialMask L (nativePoint n x L) ≠ 0 := by
    intro hz
    exact hc (commonAmplitude_zero_of_mask j L _ hz _)
  have hp := spatialMask_carrier L (nativePoint_time n hT L) hm
  constructor
  · apply PhysicalWaveSum.physicalMask_support_subset
    change mask (CoordinateAlgebra.D h) (PrimaryGeometryAssembly.label nominal L)
      (physicalScale n x) (physicalPosition n x) ≠ 0
    rwa [← nativePoint_mask n hT L]
  · rw [commonAmplitude_eq_source j L _ hp, SourcePair.actualAmplitude_eq] at hc
    exact slotAmplitude_supported _ vectors_det _ _ _ _ _ j hc

theorem cutAmplitude_tsupport_physical (j : Fin 2) (L : Label B N0) (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (theta : ℝ)
    (ht : (x, theta) ∈ tsupport (cutAmplitude j L n)) :
    (physicalScale n x, physicalPosition n x) ∈
        PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h) (signedLabelOf (L, j)) ∧
      absoluteAuxiliary n x ∈ SlotGeometry.liftedSupport
        (SlotColoring.nativeIndex h (signedLabelOf (L, j)).1)
        (slotSet h slots.radius radialVector temporalVector (signedLabelOf (L, j))) := by
  let U : Set FullPoint := Prod.fst ⁻¹' (BaseContextAssembly.nativeStrip nominal
    standardRegion).domain
  have hU : IsOpen U := (BaseContextAssembly.nativeStrip nominal
    standardRegion).isOpen_domain.preimage continuous_fst
  have hxU : (x, theta) ∈ U := hx
  constructor
  · exact PhysicalWaveSum.closed_property_on_tsupport hU hxU
      (((physicalScale_continuousAt n hx).prodMk (physicalPosition_continuous n).continuousAt).comp
        continuous_fst.continuousAt)
      (PhysicalWaveSum.labelRegion_closed _ _) (fun y hy hn => (cutAmplitude_support j L n hy y.2
        hn).1) ht
  · exact PhysicalWaveSum.closed_property_on_tsupport hU hxU
      ((absoluteAuxiliary_continuous n).comp continuous_fst).continuousAt
      (liftedSupport_isClosed _ (orientedRectangle_isCompact _ _ _ _))
      (fun y hy hn => (cutAmplitude_support j L n hy y.2 hn).2) ht

theorem cutAmplitude_tsupport (j : Fin 2) (L : Label B N0) (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (theta : ℝ)
    (ht : (x, theta) ∈ tsupport (cutAmplitude j L n)) :
    physicalWindow n x ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabelOf (L, j))
      ∧
      absoluteAuxiliary n x ∈ SlotGeometry.liftedSupport
        (SlotColoring.nativeIndex h (signedLabelOf (L, j)).1)
        (slotSet h slots.radius radialVector temporalVector (signedLabelOf (L, j))) := by
  obtain ⟨hp, hs⟩ := cutAmplitude_tsupport_physical j L n hx theta ht
  exact ⟨LabelSumBounds.labelRegion_subset_closedWindow L.val.property.1 hp
    (physicalScale_pos n hx), hs⟩

theorem piece_support (l : Label B N0 × Fin 2) (n : ℕ) (x : Point)
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (theta : ℝ)
    (ht : (x, theta) ∈ tsupport (((piece standardRegion l.2 l.1).coefficients.withCutoff
      (piece standardRegion l.2 l.1).cutoff).amplitude n)) :
    physicalWindow n x ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabelOf l) ∧
      absoluteAuxiliary n x ∈ SlotGeometry.liftedSupport
        (SlotColoring.nativeIndex h (signedLabelOf l).1)
        (slotSet h slots.radius radialVector temporalVector (signedLabelOf l)) :=
  cutAmplitude_tsupport l.2 l.1 n hx theta ht

theorem cutAmplitude_tsupport_active (l : Label B N0 × Fin 2) (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (theta : ℝ)
    (ht : (x, theta) ∈ tsupport (cutAmplitude l.2 l.1 n)) :
    l ∈ activeLabels standardRegion B N0 n :=
  activeLabels_cover n hx l.1 l.2 (cutAmplitude_tsupport_physical l.2 l.1 n hx theta ht).1

theorem cutAmplitude_inactive_germ (l : Label B N0 × Fin 2) (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (theta : ℝ)
    (hl : l ∉ activeLabels standardRegion B N0 n) :
    cutAmplitude l.2 l.1 n =ᶠ[𝓝 (x, theta)] fun _ => 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun ht => hl (cutAmplitude_tsupport_active l n hx theta ht))

theorem velocity_inactive_germ (l : Label B N0 × Fin 2) (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (theta : ℝ)
    (hl : l ∉ activeLabels standardRegion B N0 n) :
    (piece standardRegion l.2 l.1).velocity n =ᶠ[𝓝 (x, theta)] fun _ => 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro ht
  exact hl (cutAmplitude_tsupport_active l n hx theta
    ((piece standardRegion l.2 l.1).velocity_tsupport_subset_tangent n ht))

theorem cutAmplitude_tsupport_disjoint (n : ℕ) {l m : Label B N0 × Fin 2} (hlm : l ≠ m) :
    Disjoint
      ((Prod.fst ⁻¹' (BaseContextAssembly.nativeStrip nominal standardRegion).domain) ∩
        tsupport (cutAmplitude l.2 l.1 n))
      ((Prod.fst ⁻¹' (BaseContextAssembly.nativeStrip nominal standardRegion).domain) ∩
        tsupport (cutAmplitude m.2 m.1 n)) := by
  apply Set.disjoint_left.mpr
  rintro ⟨x, theta⟩ ⟨hx, hl⟩ ⟨_, hm⟩
  obtain ⟨hwl, hsl⟩ := cutAmplitude_tsupport l.2 l.1 n hx theta hl
  obtain ⟨hwm, hsm⟩ := cutAmplitude_tsupport m.2 m.1 n hx theta hm
  have hne : signedLabelOf l ≠ signedLabelOf m := fun he => hlm (signedLabelOf_injective he)
  exact Set.disjoint_left.mp (slots.disjoint _ _ (LabelSumBounds.closedWindow_adjacency
    l.1.val.property.1 m.1.val.property.1 hne hwl hwm)) hsl hsm

theorem exactAmplitude_tsupport_disjoint (n : ℕ) {l m : Label B N0 × Fin 2} (hlm : l ≠ m) :
    Disjoint
      ((Prod.fst ⁻¹' (BaseContextAssembly.nativeStrip nominal standardRegion).domain) ∩
        tsupport ((piece standardRegion l.2 l.1).exactCoefficients.amplitude n))
      ((Prod.fst ⁻¹' (BaseContextAssembly.nativeStrip nominal standardRegion).domain) ∩
        tsupport ((piece standardRegion m.2 m.1).exactCoefficients.amplitude n)) :=
  (cutAmplitude_tsupport_disjoint n hlm).mono
    (inter_subset_inter_right _ ((piece standardRegion l.2
      l.1).exactAmplitude_tsupport_subset_tangent n))
    (inter_subset_inter_right _ ((piece standardRegion m.2
      m.1).exactAmplitude_tsupport_subset_tangent n))

theorem velocity_tsupport_disjoint (n : ℕ) {l m : Label B N0 × Fin 2} (hlm : l ≠ m) :
    Disjoint
      ((Prod.fst ⁻¹' (BaseContextAssembly.nativeStrip nominal standardRegion).domain) ∩
        tsupport ((piece standardRegion l.2 l.1).velocity n))
      ((Prod.fst ⁻¹' (BaseContextAssembly.nativeStrip nominal standardRegion).domain) ∩
        tsupport ((piece standardRegion m.2 m.1).velocity n)) :=
  (cutAmplitude_tsupport_disjoint n hlm).mono
    (inter_subset_inter_right _ ((piece standardRegion l.2 l.1).velocity_tsupport_subset_tangent n))
    (inter_subset_inter_right _ ((piece standardRegion m.2 m.1).velocity_tsupport_subset_tangent n))

/-! ## Inactive physical labels vanish on entire slow fibers

The radial coordinate is unrestricted here.  A nonzero literal attached
coefficient forces radial interior support and a nonzero actual mask,
which imply membership in the fixed active-label set.  On an inactive
label the entire raw coefficient is therefore zero in an open slow
neighborhood; this also removes its actual curl and Gaussian term.
-/

theorem attachedRawPressure_zero_of_attachedVelocity_zero (j : Fin 2) (L : Label B N0)
    (x : ActualSignedGeometry.Native) (hv : attachedRawVelocity j L x = 0) :
    attachedRawPressure j L x = 0 := by
  by_cases hr : PrimaryTargetBounds.profileRadius h x.1 ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · rw [attachedRawVelocity, WaveEdgeExtension.nativeExtension_inside _ _ hr] at hv
    rw [attachedRawPressure, WaveEdgeExtension.nativeExtension_inside _ _ hr]
    rcases smul_eq_zero.mp hv with hc | ha
    · simp only [outerRawPressure, hc, zero_smul]
    · simp only [outerRawPressure, rawPressure_zero_of_velocity_zero j L x ha, smul_zero]
  · exact WaveEdgeExtension.nativeExtension_outside _ _ hr

theorem active_of_native_nonzero (j : Fin 2) (L : Label B N0) (n : ℕ) {x : Point}
    (hs : x.2.1 ∈ standardRegion.carrier)
    (hr : PrimaryTargetBounds.profileRadius h (nativePoint n x L) ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal))
    (hm : spatialMask L (nativePoint n x L) ≠ 0) :
    (L, j) ∈ activeLabels standardRegion B N0 n := by
  have hT : 0 < x.2.1.1 := standardRegion.time_pos _ hs
  have hR : 0 < x.1 := by
    by_contra hn
    have hnR : (nativePoint n x L).1 ≤ 0 := by
      change Real.sqrt (ChartScales.Q n) * x.1 /
        Real.sqrt (ChartScales.Q (BaseChartJets.cellBand L)) ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (le_of_not_gt hn)) (Real.sqrt_nonneg _)
    have hp : PrimaryTargetBounds.profileRadius h (nativePoint n x L) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnR (Real.sqrt_nonneg _)
    exact (not_lt_of_ge hp) ((PrimaryTargetBounds.leftRadius_pos nominal).trans hr.1)
  have hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain := by
    apply (BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mpr
    refine ⟨hs, ?_⟩
    rwa [nativePoint_profileRadius n hT hR] at hr
  apply activeLabels_cover n hx L j
  apply PhysicalWaveSum.physicalMask_support_subset
  change mask (CoordinateAlgebra.D h) (PrimaryGeometryAssembly.label nominal L)
    (physicalScale n x) (physicalPosition n x) ≠ 0
  rwa [← nativePoint_mask n hT L]

theorem attachedRawVelocity_zero_inactive (l : Label B N0 × Fin 2) (n : ℕ) {x : Point}
    (hs : x.2.1 ∈ standardRegion.carrier) (hl : l ∉ activeLabels standardRegion B N0 n)
    (Y : Plane) : attachedRawVelocity l.2 l.1 (nativePoint n x l.1, Y) = 0 := by
  by_contra hn
  have hr : PrimaryTargetBounds.profileRadius h (nativePoint n x l.1) ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) := by
    by_contra hout
    exact hn (WaveEdgeExtension.nativeExtension_outside _ _ hout)
  have ho : outerRawVelocity l.2 l.1 (nativePoint n x l.1, Y) ≠ 0 := by
    simpa only [attachedRawVelocity, WaveEdgeExtension.nativeExtension_inside nominal
      (outerRawVelocity l.2 l.1) (x := (nativePoint n x l.1, Y)) hr] using hn
  have hm : spatialMask l.1 (nativePoint n x l.1) ≠ 0 := by
    intro hz
    exact ho (by simp only [outerRawVelocity, rawVelocity_zero_of_mask l.2 l.1 _ hz, smul_zero])
  exact hl (active_of_native_nonzero l.2 l.1 n hs hr hm)

theorem nativeCoefficients_inactive (l : Label B N0 × Fin 2) (n : ℕ) {x : Point}
    (hs : x.2.1 ∈ standardRegion.carrier) (theta : ℝ)
    (hl : l ∉ activeLabels standardRegion B N0 n) :
    (chartCoefficients l.2 l.1).amplitude n (x, theta) = 0 ∧
      (chartCoefficients l.2 l.1).pressure n (x, theta) = 0 := by
  have ha (Y : Plane) := attachedRawVelocity_zero_inactive l n hs hl Y
  have hp (Y : Plane) := attachedRawPressure_zero_of_attachedVelocity_zero l.2 l.1 _ (ha Y)
  have hau : uncutAmplitude l.2 l.1 (nativePoint n x l.1) (absoluteAuxiliary n x) = 0 := by
    simp only [uncutAmplitude, ha, map_zero, tsum_zero]
  have hpu : uncutPressure l.2 l.1 (nativePoint n x l.1) (absoluteAuxiliary n x) = 0 := by
    simp only [uncutPressure, hp, tsum_zero]
  constructor
  · change ChartScales.Q n ^ CoordinateAlgebra.A h •
      (ChartScales.Q (BaseChartJets.cellBand l.1) ^ (-CoordinateAlgebra.A h) •
        uncutAmplitude l.2 l.1 (nativePoint n x l.1) (absoluteAuxiliary n x)) = 0
    rw [hau, smul_zero, smul_zero]
  · change ChartScales.Q n ^ (2 * CoordinateAlgebra.A h) •
      (ChartScales.Q (BaseChartJets.cellBand l.1) ^ (-(2 * CoordinateAlgebra.A h)) •
        uncutPressure l.2 l.1 (nativePoint n x l.1) (absoluteAuxiliary n x)) = 0
    rw [hpu, smul_zero, smul_zero]

theorem cutAmplitude_inactive_fullFiber_germ (l : Label B N0 × Fin 2) (n : ℕ) {x : Point}
    (hs : x.2.1 ∈ standardRegion.carrier) (theta : ℝ)
    (hl : l ∉ activeLabels standardRegion B N0 n) :
    cutAmplitude l.2 l.1 n =ᶠ[𝓝 (x, theta)] fun _ => 0 := by
  have hU : IsOpen {z : FullPoint | z.1.2.1 ∈ standardRegion.carrier} :=
    standardRegion.isOpen.preimage continuous_fst.snd.fst
  filter_upwards [hU.mem_nhds hs] with y hy
  change chartCutoff l.2 l.1 n y • (chartCoefficients l.2 l.1).amplitude n y = 0
  rw [(nativeCoefficients_inactive l n hy y.2 hl).1, smul_zero]

theorem piece_velocity_inactive_germ (l : Label B N0 × Fin 2) (n : ℕ) {x : Point}
    (hs : x.2.1 ∈ standardRegion.carrier) (theta : ℝ)
    (hl : l ∉ activeLabels standardRegion B N0 n) :
    (piece standardRegion l.2 l.1).velocity n =ᶠ[𝓝 (x, theta)] fun _ => 0 := by
  have ht := notMem_tsupport_iff_eventuallyEq.mpr (cutAmplitude_inactive_fullFiber_germ l n hs
    theta hl)
  apply notMem_tsupport_iff_eventuallyEq.mp
  exact fun hv => ht ((piece standardRegion l.2 l.1).velocity_tsupport_subset_tangent n hv)

theorem piece_velocity_inactive (l : Label B N0 × Fin 2) (n : ℕ) {x : Point}
    (hs : x.2.1 ∈ standardRegion.carrier) (theta : ℝ)
    (hl : l ∉ activeLabels standardRegion B N0 n) :
    (piece standardRegion l.2 l.1).velocity n (x, theta) = 0 :=
  (piece_velocity_inactive_germ l n hs theta hl).eq_of_nhds

theorem piece_pressure_inactive (l : Label B N0 × Fin 2) (n : ℕ) {x : Point}
    (hs : x.2.1 ∈ standardRegion.carrier) (theta : ℝ)
    (hl : l ∉ activeLabels standardRegion B N0 n) :
    (piece standardRegion l.2 l.1).pressure n (x, theta) = 0 := by
  have hp : (piece standardRegion l.2 l.1).exactCoefficients.pressure n (x, theta) = 0 := by
    change chartCutoff l.2 l.1 n (x, theta) • (chartCoefficients l.2 l.1).pressure n (x, theta) = 0
    rw [(nativeCoefficients_inactive l n hs theta hl).2, smul_zero]
  simp only [CorrectionInitialization.PrimaryPiece.pressure, HarmonicCalculus.mode, hp,
    zero_mul, Complex.zero_re]

theorem piece_excluded_inactive (l : Label B N0 × Fin 2) (n : ℕ) {x : Point}
    (hs : x.2.1 ∈ standardRegion.carrier) (theta : ℝ)
    (hl : l ∉ activeLabels standardRegion B N0 n) :
    (piece standardRegion l.2 l.1).excluded n (x, theta) = 0 := by
  have ha : (piece standardRegion l.2 l.1).coefficients.amplitude n (x, theta) = 0 :=
    (nativeCoefficients_inactive l n hs theta hl).1
  funext i
  simp only [CorrectionInitialization.PrimaryPiece.excluded, HarmonicCalculus.vectorMode,
    HarmonicCalculus.mode, LinearWaveBounds.excludedSlotError, ha, Pi.zero_apply,
    smul_zero, add_zero, zero_mul, Complex.zero_re]

end NavierStokes.ActualPrimaryCovariance
