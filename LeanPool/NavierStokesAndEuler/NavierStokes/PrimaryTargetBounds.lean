/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BasePhaseGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.AlignedProfileSpectralCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryGeometryAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalSignedRequest

@[expose] public section

/-!
# Actual primary covariance and the flat target

The two columns use the two signs of the same representative and the
actual Volterra primary.  Target smallness at the attachment points is
retained as a scalar factor throughout the finite matrix solve.
-/

noncomputable section

open Set Filter Function Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators

namespace NavierStokes.PrimaryTargetBounds

abbrev Plane := MovingFrameODE.Plane
abbrev Slow := PhaseCalculus.Slow
abbrev Mat2 := SmoothCovariance.Mat2
abbrev Vec2 := SmoothCovariance.Vec2


noncomputable def phaseSign (j : Fin 2) : ℝ := if j = 0 then 1 else -1

theorem phaseSign_abs (j : Fin 2) : |phaseSign j| = 1 := by
  fin_cases j <;> norm_num [phaseSign]

/-- The normal and transverse columns in the fixed physical tangent plane. -/
noncomputable def basisMatrix (K : Plane) : Mat2 :=
  fun i j => if j = 0 then MovingFrameODE.quarterTurn K i else K i

noncomputable def modelMatrix (c u : ℝ) (K : Plane) : Mat2 :=
  basisMatrix K * PulseCovariance.signedModel c u

noncomputable def modelNormal (K T : Plane) : ℝ := -⟪T, MovingFrameODE.quarterTurn K⟫_ℝ
noncomputable def modelTransverse (K T : Plane) : ℝ := ⟪T, K⟫_ℝ

theorem basisMatrix_det (K : Plane) (hK : ‖K‖ = 1) : (basisMatrix K).det = -1 := by
  have hs := ViscousPropagator.plane_norm_sq K
  rw [hK, one_pow] at hs
  simp only [basisMatrix, Matrix.det_fin_two, ite_true, show (1 : Fin 2) ≠ 0 by decide,
    ite_false]
  change -K 1 * K 1 - K 0 * K 0 = -1
  nlinarith

theorem modelMatrix_column (c u : ℝ) (K : Plane) (i j : Fin 2) :
    modelMatrix c u K i j =
      c * Real.sqrt (1 + u ^ 2) * MovingFrameODE.quarterTurn K i - phaseSign j * u * K i := by
  fin_cases j <;>
    simp [modelMatrix, basisMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      PulseCovariance.signedModel, PulseCovariance.modelDirection, PulseCovariance.signedSlopes,
      PulseCovariance.radiusProfile, phaseSign] <;> ring

theorem basisMatrix_target (K T : Plane) (hK : ‖K‖ = 1) :
    (basisMatrix K).mulVec (Covariance.target (modelNormal K T) (modelTransverse K T)) =
      (fun i => T i) := by
  have hs := ViscousPropagator.plane_norm_sq K
  rw [hK, one_pow] at hs
  ext i
  fin_cases i <;>
    simp [basisMatrix, Covariance.target, modelNormal, modelTransverse, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, PiLp.inner_apply, MovingFrameODE.quarterTurn] <;>
    nlinarith [congrArg (fun x : ℝ => x * T 0) hs, congrArg (fun x : ℝ => x * T 1) hs]

theorem weights_unique {H : Mat2} {T z : Vec2} (hd : H.det ≠ 0) (he : H.mulVec z = T) :
    SmoothCovariance.weights H T = z := by
  rw [← SmoothCovariance.inverse_formula H T hd, ← he, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hd), Matrix.one_mulVec]

theorem strictCone_mul_left {B H : Mat2} {T : Vec2} (hB : B.det ≠ 0)
    (hH : SmoothCovariance.StrictCone H T) :
    SmoothCovariance.StrictCone (B * H) (B.mulVec T) := by
  have he : SmoothCovariance.weights (B * H) (B.mulVec T) = SmoothCovariance.weights H T :=
    weights_unique (by rw [Matrix.det_mul]; exact mul_ne_zero hB hH.det_ne_zero)
      (by rw [← Matrix.mulVec_mulVec, SmoothCovariance.reconstruct H T hH.det_ne_zero])
  apply (SmoothCovariance.weights_pos_iff _ _).mp
  intro j
  rw [he]
  exact hH.weights_pos j

theorem modelMatrix_strictCone {c u eta : ℝ} {K T : Plane}
    (hc : c < 0) (hu : 0 < u) (heta : 0 < eta) (hK : ‖K‖ = 1)
    (hm : eta ≤ modelNormal K T)
    (hr : |c * modelTransverse K T| ≤
      (PrimaryRepresentatives.slopeRatio u - eta) * modelNormal K T) :
    SmoothCovariance.StrictCone (modelMatrix c u K) (fun i => T i) := by
  have hmp : 0 < modelNormal K T := heta.trans_le hm
  have hratio : |c * modelTransverse K T / modelNormal K T| <
      u / Real.sqrt (1 + u ^ 2) := by
    rw [abs_div, abs_of_pos hmp]
    apply (div_lt_iff₀ hmp).mpr
    have hh := mul_pos heta hmp
    change |c * modelTransverse K T| < PrimaryRepresentatives.slopeRatio u * modelNormal K T
    nlinarith
  have hbase := PulseCovariance.signedModel_strictCone hc hu (Covariance.cone_of_ratio hmp hratio)
  have hh := strictCone_mul_left (B := basisMatrix K) (by rw [basisMatrix_det K hK]; norm_num) hbase
  rwa [basisMatrix_target K T hK] at hh

abbrev ModelPoint := ℝ × (Plane × Plane)

noncomputable def modelSet (M u eta : ℝ) : Set ModelPoint :=
  {p | p.1 ∈ Icc (-M) (-(1 / M)) ∧ ‖p.2.1‖ = 1 ∧ ‖p.2.2‖ = 1 ∧
    eta ≤ modelNormal p.2.1 p.2.2 ∧
    |p.1 * modelTransverse p.2.1 p.2.2| ≤
      (PrimaryRepresentatives.slopeRatio u - eta) * modelNormal p.2.1 p.2.2}

theorem modelNormal_continuous : Continuous (fun p : ModelPoint => modelNormal p.2.1 p.2.2) :=
  ((continuous_snd.snd.inner (MovingFrameODE.quarterTurn.continuous.comp continuous_snd.fst))).neg

theorem modelTransverse_continuous : Continuous (fun p : ModelPoint => modelTransverse p.2.1 p.2.2)
  :=
  continuous_snd.snd.inner continuous_snd.fst

theorem modelSet_compact (M u eta : ℝ) : IsCompact (modelSet M u eta) := by
  have hcomp : IsCompact ((Icc (-M) (-(1 / M))) ×ˢ
      (Metric.sphere (0 : Plane) 1 ×ˢ Metric.sphere (0 : Plane) 1)) :=
    isCompact_Icc.prod ((isCompact_sphere 0 1).prod (isCompact_sphere 0 1))
  have hclosed : IsClosed {p : ModelPoint | eta ≤ modelNormal p.2.1 p.2.2 ∧
      |p.1 * modelTransverse p.2.1 p.2.2| ≤
        (PrimaryRepresentatives.slopeRatio u - eta) * modelNormal p.2.1 p.2.2} :=
    (isClosed_le continuous_const modelNormal_continuous).inter
      (isClosed_le (continuous_fst.mul modelTransverse_continuous).abs
        (continuous_const.mul modelNormal_continuous))
  convert! hcomp.inter_right hclosed using 1
  ext p
  simp only [modelSet, Set.mem_ofPred_eq, mem_inter_iff, mem_prod, Metric.mem_sphere,
    dist_zero_right]
  tauto

theorem modelMatrix_continuous (u : ℝ) (i j : Fin 2) :
    Continuous (fun p : ModelPoint => modelMatrix p.1 u p.2.1 i j) := by
  simp_rw [modelMatrix_column]
  fun_prop

theorem compact_model_data {M u eta : ℝ} (hM : 1 ≤ M) (hu : 0 < u) (heta : 0 < eta) :
    (∀ i j, ContinuousOn (fun p : ModelPoint => modelMatrix p.1 u p.2.1 i j) (modelSet M u eta)) ∧
    (∀ i, ContinuousOn (fun p : ModelPoint => p.2.2 i) (modelSet M u eta)) ∧
    ∀ p ∈ modelSet M u eta,
      SmoothCovariance.StrictCone (modelMatrix p.1 u p.2.1) (fun i => p.2.2 i) := by
  refine ⟨fun i j => (modelMatrix_continuous u i j).continuousOn,
    fun i => (show Continuous (fun p : ModelPoint => p.2.2 i) by fun_prop).continuousOn, ?_⟩
  intro p hp
  have hc : p.1 < 0 := hp.1.2.trans_lt (neg_neg_of_pos (one_div_pos.mpr (zero_lt_one.trans_le hM)))
  exact modelMatrix_strictCone hc hu heta hp.2.1 hp.2.2.2.1 hp.2.2.2.2

noncomputable def modelVector (c s : ℝ) (K : Plane) : Plane :=
  (-s) • K + (c * Real.sqrt (1 + s ^ 2)) • MovingFrameODE.quarterTurn K

theorem modelVector_column (c u : ℝ) (K : Plane) (j i : Fin 2) :
    modelVector c (phaseSign j * u) K i = modelMatrix c u K i j := by
  have hs : (phaseSign j * u) ^ 2 = u ^ 2 := by
    fin_cases j <;> simp [phaseSign]
  rw [modelMatrix_column]
  simp only [modelVector, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hs]
  ring

theorem modelVector_lipschitz (c s t : ℝ) (K : Plane) (hK : ‖K‖ = 1) :
    ‖modelVector c s K - modelVector c t K‖ ≤ (|c| + 1) * |s - t| := by
  have he : modelVector c s K - modelVector c t K =
      (t-s) • K + (c * (PulseCovariance.radiusProfile s - PulseCovariance.radiusProfile t)) •
        MovingFrameODE.quarterTurn K := by
    unfold modelVector PulseCovariance.radiusProfile
    module
  rw [he]
  calc
    _ ≤ ‖(t-s) • K‖ + ‖(c * (PulseCovariance.radiusProfile s - PulseCovariance.radiusProfile t)) •
        MovingFrameODE.quarterTurn K‖ := norm_add_le _ _
    _ = |s-t| + |c| * |PulseCovariance.radiusProfile s - PulseCovariance.radiusProfile t| := by
      simp only [norm_smul, Real.norm_eq_abs, hK, PhaseEstimates.quarterTurn_norm, mul_one, abs_mul,
        abs_sub_comm t s]
    _ ≤ |s-t| + |c| * |s-t| := add_le_add_right
      (mul_le_mul_of_nonneg_left (PulseCovariance.radiusProfile_lipschitz s t) (abs_nonneg c)) _
    _ = _ := by ring

theorem frame_combination_error (k K : Plane) (hk : ‖k‖ = 1) (a b a0 b0 : ℝ) :
    ‖a • k + b • MovingFrameODE.quarterTurn k -
      (a0 • K + b0 • MovingFrameODE.quarterTurn K)‖ ≤
      |a-a0| + |b-b0| + (|a0| + |b0|) * ‖k-K‖ := by
  have he : a • k + b • MovingFrameODE.quarterTurn k -
      (a0 • K + b0 • MovingFrameODE.quarterTurn K) =
      ((a-a0) • k + (b-b0) • MovingFrameODE.quarterTurn k) +
        (a0 • (k-K) + b0 • MovingFrameODE.quarterTurn (k-K)) := by
    rw [map_sub]
    module
  rw [he]
  calc
    _ ≤ ‖(a-a0) • k + (b-b0) • MovingFrameODE.quarterTurn k‖ +
        ‖a0 • (k-K) + b0 • MovingFrameODE.quarterTurn (k-K)‖ := norm_add_le _ _
    _ ≤ (‖(a-a0) • k‖ + ‖(b-b0) • MovingFrameODE.quarterTurn k‖) +
        (‖a0 • (k-K)‖ + ‖b0 • MovingFrameODE.quarterTurn (k-K)‖) :=
      add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ = _ := by
      simp only [norm_smul, Real.norm_eq_abs, PhaseEstimates.quarterTurn_norm, hk, mul_one]
      ring

theorem tangent_ratio_error {n : MovingFrameODE.Space} {K : Plane} {B s delta r h : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hd : delta ≤ B / 2)
    (hn : ‖n - MovingFrameODE.pack (B*s) (B • K)‖ ≤ delta) :
    ‖(-MovingFrameODE.radialSlope n) • MovingFrameODE.normalDirection n +
        r • MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection n) -
      ((-s) • K + h • MovingFrameODE.quarterTurn K)‖ ≤
        (2 * (1 + |s|) + 4 * (|s| + |h|)) * delta / B + |r-h| := by
  have hne := (PhaseEstimates.normal_lower_bounds hB hK hd hn).2.2.1
  have he := frame_combination_error (MovingFrameODE.normalDirection n) K
    (MovingFrameODE.normalDirection_unit hne) (-MovingFrameODE.radialSlope n) r (-s) h
  have hs := PhaseEstimates.radialSlope_close hB hK hd hn
  have hk := PhaseEstimates.normalDirection_close hB hK hd hn
  have hss : |-MovingFrameODE.radialSlope n - -s| = |MovingFrameODE.radialSlope n - s| := by
    rw [← abs_neg]
    congr 1
    ring
  rw [hss, abs_neg] at he
  calc
    _ ≤ |MovingFrameODE.radialSlope n - s| + |r-h| +
        (|s| + |h|) * ‖MovingFrameODE.normalDirection n-K‖ := he
    _ ≤ 2 * (1 + |s|) * delta / B + |r-h| + (|s| + |h|) * (4*delta/B) :=
      add_le_add (add_le_add_left hs _) (mul_le_mul_of_nonneg_left hk (by positivity))
    _ = _ := by ring

noncomputable def pulseRatio (d : PrimaryODE.FrameData Slow) (lam u L : ℝ) (p : Slow) (v : ℝ) :
  Plane :=
  !₂[PrimaryPulseBounds.normalizedPulse d lam u L (p, v/L) 1 /
      PrimaryPulseBounds.normalizedPulse d lam u L (p, v/L) 0,
    PrimaryPulseBounds.normalizedPulse d lam u L (p, v/L) 2 /
      PrimaryPulseBounds.normalizedPulse d lam u L (p, v/L) 0]

theorem pulseRatio_eq (d : PrimaryODE.FrameData Slow) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    {U : Set Slow} (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    {p : Slow} (hp : p ∈ U) {v : ℝ} (hv : v ∈ Icc 0 L)
    (hx : PrimaryODE.radialPrimary hL.le d
      (fun z => PrimaryPulseBounds.referenceP lam u L z.2) p v ≠ 0) :
    pulseRatio d lam u L p v =
      (-d.rho (p,v)) • d.frame (p,v) 0 +
        (PrimaryODE.transversePrimary hL.le d (fun z => PrimaryPulseBounds.referenceP lam u L z.2)
          p v /
          PrimaryODE.radialPrimary hL.le d (fun z => PrimaryPulseBounds.referenceP lam u L z.2) p
            v) •
            d.frame (p,v) 1 := by
  have hLv : L * (v / L) = v := by field_simp
  unfold pulseRatio PrimaryPulseBounds.normalizedPulse
  rw [hLv, PrimaryPulseBounds.fundamental_eq_primary hL U hA hp hv]
  ext i
  fin_cases i <;>
    simp [PrimaryODE.FrameData.ambient, MovingFrameODE.tangent, MovingFrameODE.pack,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PrimaryODE.radialPrimary,
      PrimaryODE.transversePrimary] at * <;>
    field_simp

noncomputable def geometricRatioConstant (M u : ℝ) : ℝ :=
  (2 * (1 + 3*M) + 4 * (3*M + BasePhaseGeometry.eigenBound M)) *
    BasePhaseGeometry.phaseConstant M / BasePhaseGeometry.normalLower M u

noncomputable def ratioConstant (M u gap : ℝ) : ℝ :=
  geometricRatioConstant M u + 4 * BasePhaseGeometry.eigenBound M *
    GrowingMode.coneConstant gap (BasePhaseGeometry.modalConstant M u)

theorem geometricRatioConstant_nonneg {M u : ℝ} (hM : 1 ≤ M) : 0 ≤ geometricRatioConstant M u := by
  have hnormal := (BasePhaseGeometry.normalLower_pos (u := u) hM).le
  have hp := (BasePhaseGeometry.phaseConstant_pos hM).le
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  unfold geometricRatioConstant BasePhaseGeometry.eigenBound
  positivity

theorem ratioConstant_nonneg {M u gap : ℝ} (hM : 1 ≤ M) (hgap : 0 < gap) :
    0 ≤ ratioConstant M u gap := by
  have hg := geometricRatioConstant_nonneg (u := u) hM
  have hC := (BasePhaseGeometry.error_constants_nonneg (u := u) hM).2.1
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  unfold ratioConstant GrowingMode.coneConstant BasePhaseGeometry.eigenBound
  positivity

theorem signedSlot_center {u L : ℝ} (hu : 0 ≤ u) (hL : 0 < L)
    (j : Fin 2) (v : ℝ) :
    |PhaseEstimates.signedSlot (phaseSign j) u L v - phaseSign j * u| =
      u * |v - L / 2| / L := by
  have he : PhaseEstimates.signedSlot (phaseSign j) u L v - phaseSign j * u =
      phaseSign j * u * (v-L/2) / L := by
    unfold PhaseEstimates.signedSlot
    field_simp ; ring
  rw [he, abs_div, abs_mul, abs_mul, phaseSign_abs, one_mul, abs_of_nonneg hu,
    abs_of_pos hL]

section FamilyRatio

open BasePhaseGeometry

variable {ι : Type*} {D : PhaseJetBounds.Domain ι Slow} {h r0 u M : ℝ}
    (a : FamilyData D h r0 u M)
    (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M) (hu : 0 < u) (huM : u ≤ M)
    (hL : 1 / (2 * r0) ≤ M) (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (hlarge : ∀ i, LargeBand h M u (a.band i))

include hh hr hM hu huM hL hslot hlarge

theorem coefficient_continuous (i : ι) :
    ContinuousOn ((a.frame i).coefficient 1) (D.carrier i ×ˢ Icc 0 (a.length i)) :=
  ((a.coefficient_jets hh hr hM hu huM hL hslot hlarge 1).smooth i).continuousOn.mono
    (fun _ hz => ⟨hz.1, a.interval_subset_slot hr i hz.2⟩)

theorem primary_ratio_error (i : ι) {p : Slow} (hp : p ∈ D.carrier i)
    {gap : ℝ} (hgap : 0 < gap)
    (hg : ∀ v ∈ Icc 0 (a.length i),
      gap ≤ ViscousPropagator.referenceEigenvalue (a.lam i) u (a.length i) v)
    (hcone : 2 * GrowingMode.coneConstant gap (modalConstant M u) ≤ D.scale i)
    {v : ℝ} (hv : v ∈ Icc 0 (a.length i)) :
    ‖pulseRatio (a.frame i) (a.lam i) u (a.length i) p v -
      modelVector (a.c0 i) (a.slope i (p,v)) (a.K i)‖ ≤ ratioConstant M u gap / D.scale i := by
  have hlength := a.length_pos hr i
  have hS : 0 < D.scale i := zero_lt_one.trans_le (D.one_le_scale i)
  have hc := a.coefficientControl hh hr hM hu huM hL hslot i (hlarge i) hp
  have hA := coefficient_continuous a hh hr hM hu huM hL hslot hlarge i
  have hslotL : a.length i ≤ (2*r0*ChartScales.Tg) * D.scale i := by
    simpa only [FamilyData.length, a.scale_eq i, mul_assoc] using
      (ChartScales.slotLength_bounds r0 h hr.le hh (hlarge i).four_le).2
  have hP (t : ℝ) (_ht : t ∈ Icc 0 (a.length i)) :=
    PrimaryPulseBounds.referenceP_pos (a.lam i) u (a.length i) t
  have hPeq (t : ℝ) (ht : t ∈ Icc 0 (a.length i)) :
      HasDerivAt (PrimaryPulseBounds.referenceP (a.lam i) u (a.length i))
        (((a.frame i).eigenvalue (p,t) - ViscousPropagator.referenceViscosity (a.lam i) u (a.length
          i) t) *
          PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) t) t := by
    rw [hc.eigenvalue t ht]
    exact PrimaryPulseBounds.referenceP_hasDerivAt _ _ _ _
  have herrors := error_constants_nonneg (u := u) hM
  have hprimary := PrimaryODE.primary_bounds hlength.le (a.frame i)
    (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2)
    hA hp hgap herrors.2.1 herrors.2.2 hS hcone (by simpa using hslotL)
    (ViscousPropagator.referenceViscosity (a.lam i) u (a.length i))
    (fun t ht => by rw [hc.eigenvalue t ht]; exact hg t ht)
    hc.errors hc.viscosity hP hPeq v hv
  have hv' := a.interval_subset_slot hr i hv
  have hnormal := (a.phase_estimates hh hr hM (by simpa only [abs_of_pos hu] using huM)
    hL hslot i (hlarge i) hp hv').1
  have hsmall := a.phase_error_small hh hM i (hlarge i)
  have hB := a.B_pos hh hM i
  have hne := (PhaseEstimates.normal_lower_bounds hB (a.unit i) hsmall hnormal).2.2.1
  have hs := a.slope_bound hr hu.le huM (q := p) hv'
  have hprof := reference_profile_bounds (one_div_pos.mpr (zero_lt_one.trans_le hM))
    (a.ratio_bound i).1 (a.ratio_bound i).2 (a.magnitude_bound hr hu.le huM hv')
  have hH : |PrimaryODE.referenceProfile (a.c0 i) u (a.length i) v| ≤ eigenBound M :=
    hprof.1.trans (by unfold eigenBound; nlinarith [show 0 ≤ M by linarith])
  have hgeom := tangent_ratio_error hB (a.unit i) hsmall hnormal
    (r := PrimaryODE.transversePrimary hlength.le (a.frame i)
      (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) p v /
      PrimaryODE.radialPrimary hlength.le (a.frame i)
        (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) p v)
    (h := PrimaryODE.referenceProfile (a.c0 i) u (a.length i) v)
  have hsq : (a.slope i (p,v))^2 = PulseGrowth.slotMagnitude u (a.length i) v ^ 2 :=
    signedSlot_sq (a.sign i) u (a.length i) v
  have hprofile : PrimaryODE.referenceProfile (a.c0 i) u (a.length i) v =
      a.c0 i * Real.sqrt (1 + (a.slope i (p,v))^2) := by
    rw [hsq]
    rfl
  have he : pulseRatio (a.frame i) (a.lam i) u (a.length i) p v -
      modelVector (a.c0 i) (a.slope i (p,v)) (a.K i) =
      (-MovingFrameODE.radialSlope (a.phase.normal i (p,v))) •
          MovingFrameODE.normalDirection (a.phase.normal i (p,v)) +
        (PrimaryODE.transversePrimary hlength.le (a.frame i)
          (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) p v /
          PrimaryODE.radialPrimary hlength.le (a.frame i)
            (fun z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) z.2) p v) •
          MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (a.phase.normal i (p,v))) -
        ((-a.slope i (p,v)) • a.K i +
          PrimaryODE.referenceProfile (a.c0 i) u (a.length i) v • MovingFrameODE.quarterTurn (a.K
            i)) := by
    rw [pulseRatio_eq (a.frame i) (a.lam i) u hlength hA hp hv hprimary.1.ne']
    simp only [FamilyData.frame, PhaseJetBounds.PhaseFamily.frameData,
      PrimaryODE.FrameData.ofNormalLocal,
      PrimaryODE.localFrame_eq hne, MovingFrameODE.normalFrame_zero, MovingFrameODE.normalFrame_one]
    rw [hprofile]
    rfl
  rw [he]
  apply hgeom.trans
  have hBmin := (a.B_bounds hh hM i).1
  have hcoef : 0 ≤ 2*(1+3*M)+4*(3*M+eigenBound M) := by unfold eigenBound; positivity
  have hph : 0 ≤ phaseConstant M / D.scale i := div_nonneg (phaseConstant_pos hM).le hS.le
  have hgeometric :
      (2*(1+|a.slope i (p,v)|)+4*(|a.slope i (p,v)|+
        |PrimaryODE.referenceProfile (a.c0 i) u (a.length i) v|)) *
          (phaseConstant M / D.scale i) / a.B i ≤ geometricRatioConstant M u / D.scale i := by
    calc
      _ ≤ (2*(1+3*M)+4*(3*M+eigenBound M)) * (phaseConstant M / D.scale i) / a.B i :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hph) hB.le
      _ ≤ (2*(1+3*M)+4*(3*M+eigenBound M)) * (phaseConstant M / D.scale i) / normalLower M u :=
        div_le_div_of_nonneg_left (mul_nonneg hcoef hph) (normalLower_pos hM) hBmin
      _ = _ := by unfold geometricRatioConstant; ring
  have hconeNonneg : 0 ≤ GrowingMode.coneConstant gap (modalConstant M u) := by
    unfold GrowingMode.coneConstant
    exact div_nonneg (mul_nonneg (by norm_num) (by linarith [herrors.2.1])) hgap.le
  have hratiobound := hprimary.2.2.2
  change |PrimaryODE.transversePrimary _ _ _ _ _ / PrimaryODE.radialPrimary _ _ _ _ _ -
    PrimaryODE.referenceProfile (a.c0 i) u (a.length i) v| ≤ _ at hratiobound
  have hratiobound' := hratiobound.trans (mul_le_mul_of_nonneg_right
    (show 4 * |PrimaryODE.referenceProfile (a.c0 i) u (a.length i) v| ≤ 4 * eigenBound M by
      linarith)
    (div_nonneg hconeNonneg hS.le))
  exact (add_le_add hgeometric hratiobound').trans_eq (by unfold ratioConstant; ring)

/-- The actual uncut primary is compared with the central signed model.
The two errors have the concentration-compatible orders `1/L` and
`|v-L/2|/L`; no covariance convergence is a hypothesis. -/
theorem primary_center_error (i : ι) (j : Fin 2) (hsign : a.sigma i = phaseSign j)
    {p : Slow} (hp : p ∈ D.carrier i) {gap : ℝ} (hgap : 0 < gap)
    (hg : ∀ v ∈ Icc 0 (a.length i),
      gap ≤ ViscousPropagator.referenceEigenvalue (a.lam i) u (a.length i) v)
    (hcone : 2 * GrowingMode.coneConstant gap (modalConstant M u) ≤ D.scale i)
    {v : ℝ} (hv : v ∈ Icc 0 (a.length i)) (k : Fin 2) :
    |PrimaryPulseBounds.normalizedPulse (a.frame i) (a.lam i) u (a.length i)
          (p,v / a.length i) k.succ /
        PrimaryPulseBounds.normalizedPulse (a.frame i) (a.lam i) u (a.length i)
          (p,v / a.length i) 0 - modelMatrix (a.c0 i) u (a.K i) k j| ≤
      ((2*r0*ChartScales.Tg) * ratioConstant M u gap) / a.length i +
        ((M+1)*u) * |v-a.length i/2| / a.length i := by
  have hlength := a.length_pos hr i
  have hS : 0 < D.scale i := zero_lt_one.trans_le (D.one_le_scale i)
  have hslotL : a.length i ≤ (2*r0*ChartScales.Tg) * D.scale i := by
    simpa only [FamilyData.length, a.scale_eq i, mul_assoc] using
      (ChartScales.slotLength_bounds r0 h hr.le hh (hlarge i).four_le).2
  have hratio := primary_ratio_error a hh hr hM hu huM hL hslot hlarge i hp hgap hg hcone hv
  have hslope : |a.slope i (p,v) - phaseSign j*u| = u*|v-a.length i/2|/a.length i := by
    simpa only [FamilyData.slope, hsign] using signedSlot_center hu.le hlength j v
  have hmodel := modelVector_lipschitz (a.c0 i) (a.slope i (p,v)) (phaseSign j*u) (a.K i) (a.unit i)
  rw [hslope] at hmodel
  have hbound : ‖pulseRatio (a.frame i) (a.lam i) u (a.length i) p v -
      modelVector (a.c0 i) (phaseSign j*u) (a.K i)‖ ≤
      ratioConstant M u gap / D.scale i + ((M+1)*u)*|v-a.length i/2|/a.length i := by
    apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    apply add_le_add hratio
    apply hmodel.trans
    calc
      _ ≤ (M+1) * (u*|v-a.length i/2|/a.length i) :=
        mul_le_mul_of_nonneg_right (by linarith [(a.ratio_bound i).2]) (by positivity)
      _ = _ := by ring
  have hratioL : ratioConstant M u gap / D.scale i ≤
      ((2*r0*ChartScales.Tg) * ratioConstant M u gap) / a.length i := by
    apply (div_le_div_iff₀ hS hlength).mpr
    nlinarith [mul_le_mul_of_nonneg_left hslotL (ratioConstant_nonneg (u := u) hM hgap)]
  have hcomponent := (PiLp.norm_apply_le
    (pulseRatio (a.frame i) (a.lam i) u (a.length i) p v -
      modelVector (a.c0 i) (phaseSign j*u) (a.K i)) k)
  have he : (pulseRatio (a.frame i) (a.lam i) u (a.length i) p v -
      modelVector (a.c0 i) (phaseSign j*u) (a.K i)) k =
      PrimaryPulseBounds.normalizedPulse (a.frame i) (a.lam i) u (a.length i)
          (p,v / a.length i) k.succ /
        PrimaryPulseBounds.normalizedPulse (a.frame i) (a.lam i) u (a.length i)
          (p,v / a.length i) 0 - modelMatrix (a.c0 i) u (a.K i) k j := by
    rw [PiLp.sub_apply, modelVector_column]
    fin_cases k <;> rfl
  rw [he, Real.norm_eq_abs] at hcomponent
  exact hcomponent.trans (hbound.trans (add_le_add_left hratioL _))

end FamilyRatio

section FamilyPair

open BasePhaseGeometry PrimaryCovarianceBounds

variable {ι : Type*} {D : PhaseJetBounds.Domain ι Slow} {h r0 u M : ℝ}

/-- The two signs share the same actual representative. -/
structure CompatiblePair (a : Fin 2 → FamilyData D h r0 u M) : Prop where
  band : ∀ j i, (a j).band i = (a 0).band i
  ratio : ∀ j i, (a j).c0 i = (a 0).c0 i
  transverse : ∀ j i, (a j).K i = (a 0).K i
  sign : ∀ j i, (a j).sigma i = phaseSign j

/-- The native finite covariance with the original joint label. -/
noncomputable def familyCovariance (vr vt : TorusInverse.Plane)
    (a : Fin 2 → FamilyData D h r0 u M) (i : ι) (p : Slow) : Mat2 :=
  PrimaryPulseBounds.primaryCovariance
    (fun j i => PartitionedCovariance.nativePrefactor vr vt r0 *
      ChartScales.timeCoefficient h ((a j).band i) * (a j).length i)
    (fun j => (a j).frame) (fun j => (a j).lam) (fun _ _ => u)
    (fun j => (a j).length) i p

theorem familyCovariance_eq_native (vr vt : TorusInverse.Plane)
    (a : Fin 2 → FamilyData D h r0 u M) (hc : CompatiblePair a) (i : ι) (p : Slow) :
    familyCovariance vr vt a i p = nativePrimaryCovariance vr vt r0 h
      (fun j _ => (a j).frame i) (fun j _ => (a j).lam i) (fun _ _ => u)
      ((a 0).band i) p := by
  unfold familyCovariance nativePrimaryCovariance PrimaryPulseBounds.primaryCovariance
  ext r c
  change _ * _ = _ * _
  simp only [FamilyData.length, hc.band]

/-- Uniform finite-matrix bounds follow from the actual constructed
phases and their ODEs.  The model point only records the common
representative and a unit target direction. -/
theorem exists_family_bounds (vr vt : TorusInverse.Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M) (hu : 0 < u) (huM : u ≤ M)
    (hL : 1 / (2*r0) ≤ M) (hslot : 4*r0*ChartScales.Tg ≤ M)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, 4 ≤ N ∧ ∃ detGap entryBound inverseLower : ℝ,
      0 < detGap ∧ 1 ≤ entryBound ∧ 0 < inverseLower ∧
      ∀ (ι : Type*) (D : PhaseJetBounds.Domain ι Slow)
        (a : Fin 2 → FamilyData D h r0 u M), CompatiblePair a →
        (∀ j i, LargeBand h M u ((a j).band i)) →
      ∀ i : ι, N ≤ (a 0).band i → ∀ p ∈ D.carrier i, ∀ T : Plane,
        ((a 0).c0 i, (a 0).K i, T) ∈ modelSet M u eta →
      ∀ zeta : ℝ, 0 ≤ zeta →
        ZeroOrderBounds (Real.sqrt (ChartScales.S ((a 0).band i)))
          detGap entryBound inverseLower zeta (familyCovariance vr vt a i p)
          (FlatCovariance.scaledTarget zeta (fun k => T k)) := by
  let R : Set (ℝ × ℝ) := Icc (1/M) M ×ˢ {u}
  have hR : IsCompact R := isCompact_Icc.prod (isCompact_singleton)
  obtain ⟨gap, b, B, hgap, hb, hB, href⟩ := compact_reference_bounds hR
    Prod.fst Prod.snd continuous_fst.continuousOn continuous_snd.continuousOn
    (fun z hz => (one_div_pos.mpr (zero_lt_one.trans_le hM)).trans_le hz.1.1)
    (fun z hz => by simpa only [mem_singleton_iff.mp hz.2] using hu)
  let Kslot := 2*r0*ChartScales.Tg
  let Clo := primaryLower (modalConstant M u) (dampingConstant M) Kslot
  let Chi := primaryUpper (modalConstant M u) (dampingConstant M) Kslot
  have herrors := error_constants_nonneg (u := u) hM
  have hKslot : 0 ≤ Kslot := mul_nonneg (mul_nonneg (by norm_num) hr.le) ChartScales.Tg_pos.le
  have hE : 0 ≤ Kslot * ratioConstant M u gap :=
    mul_nonneg hKslot (ratioConstant_nonneg hM hgap)
  have hF : 0 ≤ (M+1)*u := by positivity
  obtain ⟨hH0, hT0, hcone⟩ := compact_model_data hM hu heta
  obtain ⟨N0, hN04, detGap, entryBound, inverseLower, hd, he, hi, hpair⟩ :=
    compact_chart_pair_bounds (modelSet_compact M u eta)
      (fun p => modelMatrix p.1 u p.2.1) (fun p k => p.2.2 k) hH0 hT0 hcone vr vt hdet
      (B := B) hr hh (primaryLower_pos _ _ _) (primaryUpper_pos _ _ _) hb hE hF
  obtain ⟨N1, hN14, hN1⟩ := eventually_slow_large (2*GrowingMode.coneConstant gap (modalConstant M
    u))
  obtain ⟨N2, hN24, hN2⟩ := eventually_slotRadius_large hr hh 1
  refine ⟨max N0 (max N1 N2), hN04.trans (le_max_left _ _),
    detGap, entryBound, inverseLower, hd, he, hi, ?_⟩
  intro ι D a hc hlarge i hn p hp T hT zeta hzeta
  have hn0 : N0 ≤ (a 0).band i := (le_max_left _ _).trans hn
  have hn1 : N1 ≤ (a 0).band i := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn2 : N2 ≤ (a 0).band i := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn4 := hN04.trans hn0
  have hlength (j : Fin 2) : (a j).length i = ChartScales.slotLength r0 h ((a 0).band i) := by
    simp only [FamilyData.length, hc.band]
  have hS : 0 < D.scale i := zero_lt_one.trans_le (D.one_le_scale i)
  have hA (j : Fin 2) := coefficient_continuous (a j) hh hr hM hu huM hL hslot (hlarge j) i
  have hk (j : Fin 2) := (a j).kinematics hh hr hM
    (by simpa only [abs_of_pos hu] using huM) hL hslot i (hlarge j i) hp
  have href (j : Fin 2) := href ((a j).lam i,u) ⟨(a j).lambda_bound i, rfl⟩
    ((a j).length i) ((a j).length_pos hr i)
  have hconeS : 2*GrowingMode.coneConstant gap (modalConstant M u) ≤ D.scale i := by
    rw [(a 0).scale_eq i]
    exact hN1 _ hn1
  let P : Fin 2 → PartitionedCovariance.Pulse := fun j =>
    PrimaryPulseBounds.canonicalPrimaryPulse ((a j).frame i) ((a j).lam i) u
      ((a j).length_pos hr i) (D.carrier i) (hA j) p hp (hk j)
  have hPulse (j : Fin 2) : PulseCovariance.PulseBounds (slotRadius r0 h ((a 0).band i))
      Clo Chi b B (P j).ψ (P j).x := by
    have hcoeff := (a j).coefficientControl hh hr hM hu huM hL hslot i (hlarge j i) hp
    apply canonicalPrimaryPulse_bounds ((a j).frame i) ((a j).lam i) u
      ((a j).length_pos hr i) (hN2 _ hn2)
      (by rw [slotRadius_sq hr, hlength j])
      (D.carrier i) (hA j) p hp (hk j) hgap hb hB herrors.2.1 herrors.2.2 hS hconeS
    · simpa only [Kslot, FamilyData.length, (a j).scale_eq i, mul_assoc] using
        (ChartScales.slotLength_bounds r0 h hr.le hh (hlarge j i).four_le).2
    · exact hcoeff.eigenvalue
    · exact hcoeff.errors
    · exact hcoeff.viscosity
    · exact href j
  have hratio (j k : Fin 2) (v : ℝ)
      (hv : v ∈ Icc 0 (ChartScales.slotLength r0 h ((a 0).band i))) :
      |(P j).t v k / (P j).x v - modelMatrix ((a 0).c0 i) u ((a 0).K i) k j| ≤
        Kslot*ratioConstant M u gap / ChartScales.slotLength r0 h ((a 0).band i) +
          ((M+1)*u)*|v-ChartScales.slotLength r0 h ((a 0).band i)/2| /
            ChartScales.slotLength r0 h ((a 0).band i) := by
    have hv' : v ∈ Icc 0 ((a j).length i) := by rwa [hlength j]
    rw [canonicalPrimaryPulse_ratio _ _ _ _ _ _ _ _ _ hv']
    simpa only [hlength j, hc.ratio j i, hc.transverse j i, Kslot] using
      primary_center_error (a j) hh hr hM hu huM hL hslot (hlarge j) i j (hc.sign j i)
        hp hgap (fun v hv => (href j v hv).1) hconeS hv' k
  have hbnd := hpair ((a 0).band i) hn0 (((a 0).c0 i),((a 0).K i),T) hT P hPulse hratio zeta hzeta
  have heq : familyCovariance vr vt a i p =
      PartitionedCovariance.pairMatrix vr vt r0
        (fun _ => ChartScales.timeCoefficient h ((a 0).band i)) P := by
    exact PrimaryPulseBounds.primaryCovariance_eq_canonicalPairMatrix _ _ _ _ _ i
      (D.carrier i) p hp (fun j => (a j).length_pos hr i) hA hk vr vt r0
      (fun _ => ChartScales.timeCoefficient h ((a 0).band i))
      (fun j => by rw [hc.band j i])
  rw [heq]
  exact hbnd

end FamilyPair

section Prepared

open PrimaryGeometryAssembly PrimaryCovarianceBounds

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)
    {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : Prepared H v upper B r0 N0)

theorem prepared_pair : CompatiblePair (family H v a) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The mixed target margin is supplied by the actual closed profile
direction and its actual positive representative. -/
theorem prepared_model_mem (L : Index W a.N) {p : Slow}
    (hp : p ∈ PositiveRepresentatives.positivePart (referenceSet W))
    (hpL : p ∈ (domain W a.N).carrier L) :
    ((family H v a 0).c0 L, (family H v a 0).K L, a.target p) ∈
      modelSet a.M a.u a.eta := by
  have hmargin := a.target_margin L p hp hpL
  have hcneg := (a.cone L).c0_neg
  have hcb := (family H v a 0).ratio_bound L
  have hm : a.eta ≤ modelNormal ((family H v a 0).K L) (a.target p) := by
    change a.eta ≤ -⟪a.target p, MovingFrameODE.quarterTurn
      (PrimaryRepresentatives.transverseDirection (shear H v (representative W L)))⟫_ℝ
    rw [PrimaryRepresentatives.quarterTurn_transverseDirection]
    linarith [hmargin.1]
  refine ⟨?_, (family H v a 0).unit L, a.target_unit p hp.1, hm, ?_⟩
  · change -a.M ≤ PrimaryRepresentatives.c0 _ _ ∧ PrimaryRepresentatives.c0 _ _ ≤ -(1/a.M)
    change 1/a.M ≤ |PrimaryRepresentatives.c0 _ _| ∧ |PrimaryRepresentatives.c0 _ _| ≤ a.M at hcb
    rw [abs_of_neg hcneg] at hcb
    constructor <;> linarith
  · have hmpos := a.eta_pos.trans_le hm
    have hratio : |(family H v a 0).c0 L *
        modelTransverse ((family H v a 0).K L) (a.target p)| /
          modelNormal ((family H v a 0).K L) (a.target p) ≤
        PrimaryRepresentatives.slopeRatio a.u - a.eta := by
      have hn : ⟪a.target p, PrimaryRepresentatives.normalDirection
          (shear H v (representative W L))⟫_ℝ < 0 := by linarith [a.eta_pos, hmargin.1]
      rw [abs_div, abs_of_neg hn] at hmargin
      change |PrimaryRepresentatives.c0 _ _ * ⟪a.target p,
          PrimaryRepresentatives.transverseDirection _⟫_ℝ| /
          -⟪a.target p, MovingFrameODE.quarterTurn (PrimaryRepresentatives.transverseDirection
            _)⟫_ℝ ≤ _
      rw [PrimaryRepresentatives.quarterTurn_transverseDirection]
      linarith [hmargin.2]
    exact (div_le_iff₀ hmpos).mp hratio

noncomputable def preparedCovariance (vr vt : TorusInverse.Plane) : Index W a.N → Slow → Mat2 :=
  familyCovariance vr vt (family H v a)

theorem preparedCovariance_eq_construction (vr vt : TorusInverse.Plane) (hr0 : 0 < r0) :
    preparedCovariance H v a vr vt = PrimaryPulseBounds.primaryCovariance
      (fun _ L => PartitionedCovariance.nativePrefactor vr vt r0 *
        ChartScales.timeCoefficient F.data.h (BaseChartJets.cellBand L) *
          ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L))
      (fun j => (construction H v a hr0 j).frame)
      (fun j => (construction H v a hr0 j).lam)
      (fun j => (construction H v a hr0 j).u)
      (fun j => (construction H v a hr0 j).L) := rfl

/-- One later cutoff, with all representatives, targets and phases kept
fixed, supplies the actual normalized determinant and inverse bounds. -/
theorem exists_prepared_bounds (vr vt : TorusInverse.Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (hr0 : 0 < r0) :
    ∃ N : ℕ, a.N ≤ N ∧ ∃ detGap entryBound inverseLower : ℝ,
      0 < detGap ∧ 1 ≤ entryBound ∧ 0 < inverseLower ∧
      ∀ (L : Index W a.N), N ≤ BaseChartJets.cellBand L → ∀ p : Slow,
        p ∈ PositiveRepresentatives.positivePart (referenceSet W) →
        p ∈ (domain W a.N).carrier L → ∀ zeta : ℝ, 0 ≤ zeta →
        ZeroOrderBounds (Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))
          detGap entryBound inverseLower zeta (preparedCovariance H v a vr vt L p)
          (FlatCovariance.scaledTarget zeta (fun k => a.target p k)) := by
  obtain ⟨N, hN4, dg, eb, il, hd, he, hi, hb⟩ := exists_family_bounds vr vt hdet
    F.data.h_pos.le hr0 a.one_le_M a.u_pos a.u_le a.length_bound a.slot_bound a.eta_pos
  refine ⟨max a.N N, le_max_left _ _, dg, eb, il, hd, he, hi, ?_⟩
  intro L hL p hp hpL zeta hzeta
  exact hb (Index W a.N) (domain W a.N) (family H v a) (prepared_pair H v a)
    (fun _ L => a.large _ L.property) L ((le_max_right _ _).trans hL) p hpL (a.target p)
    (prepared_model_mem H v a L hp hpL) zeta hzeta

end Prepared

section MovingWeight

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

noncomputable def leftRadius : ℝ := Real.sqrt (2 * NominalConeAssembly.activeLeft W)
noncomputable def rightRadius : ℝ := Real.sqrt (2 * NominalConeAssembly.activeRight W)

theorem leftRadius_pos : 0 < leftRadius W :=
  Real.sqrt_pos.mpr (mul_pos (by norm_num) (NominalConeAssembly.activeLeft_pos W))

theorem rightRadius_pos : 0 < rightRadius W :=
  Real.sqrt_pos.mpr (mul_pos (by norm_num) (LeadingStressWeights.activeRight_pos W))

theorem radii_ordered : leftRadius W < rightRadius W :=
  Real.sqrt_lt_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)
    (mul_lt_mul_of_pos_left (PrimaryGeometryAssembly.active_order (W := W)) (by norm_num))

/-- These are the radial-log coefficients of the very same product
weight, not a replacement weight with a faster decay. -/
noncomputable def stripWeight (r : ℝ) : ℝ :=
  WeightedRadialPrimitive.zeta (FinalSlowBase.edgeExponent W / 4) 1
    (WeightedRadialPrimitive.logLength (leftRadius W) (rightRadius W))
    (WeightedRadialPrimitive.logPosition (leftRadius W) r)

theorem stripWeight_nonneg (r : ℝ) : 0 ≤ stripWeight W r :=
  mul_nonneg (FlatCutoff.edge_nonneg _ _) (FlatCutoff.edge_nonneg _ _)

theorem edge_double (c x : ℝ) : FlatCutoff.edge c (2*x) = FlatCutoff.edge (c/4) x := by
  by_cases hx : 0 < x
  · rw [FlatCutoff.edge_of_pos _ (by positivity), FlatCutoff.edge_of_pos _ hx]
    congr 1
    field_simp ; ring_nf
  · rw [FlatCutoff.edge_of_nonpos _ (by linarith), FlatCutoff.edge_of_nonpos _ (le_of_not_gt hx)]

theorem log_square_half {r : ℝ} (hr : 0 < r) :
    Real.log (r^2/2) = 2*Real.log r - Real.log 2 := by
  rw [Real.log_div (pow_ne_zero _ hr.ne') (by norm_num), Real.log_pow]
  norm_num

theorem stripWeight_eq (r eta : ℝ) (hr : 0 < r) :
    stripWeight W r = FinalSlowBase.weight W (r^2/2,eta) := by
  have ha := leftRadius_pos W
  have hb := rightRadius_pos W
  have hasq : (leftRadius W)^2/2 = NominalConeAssembly.activeLeft W := by
    rw [leftRadius, Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos
      W).le)]
    ring
  have hbsq : (rightRadius W)^2/2 = NominalConeAssembly.activeRight W := by
    rw [rightRadius, Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos
      W).le)]
    ring
  have halog := log_square_half ha
  have hblog := log_square_half hb
  rw [hasq] at halog
  rw [hbsq] at hblog
  have hl : Real.log (r^2/2) - FinalSlowBase.logLeft W =
      2 * WeightedRadialPrimitive.logPosition (leftRadius W) r := by
    rw [FinalSlowBase.logLeft, WeightedRadialPrimitive.logPosition,
      Real.log_div hr.ne' ha.ne', log_square_half hr, halog]
    ring
  have hh : FinalSlowBase.logRight W - Real.log (r^2/2) =
      2 * (WeightedRadialPrimitive.logLength (leftRadius W) (rightRadius W) -
        WeightedRadialPrimitive.logPosition (leftRadius W) r) := by
    rw [FinalSlowBase.logRight, WeightedRadialPrimitive.logLength,
      WeightedRadialPrimitive.logPosition, Real.log_div hb.ne' ha.ne',
      Real.log_div hr.ne' ha.ne', log_square_half hr, hblog]
    ring
  unfold FinalSlowBase.weight BaseResidual.activeZeta ActiveAnnulusWeight.radialWeight
  rw [ite_eq_left (by positivity : 0 < r^2/2)]
  unfold ActiveAnnulusWeight.weight
  rw [hl, hh, edge_double, edge_double]
  norm_num [stripWeight, WeightedRadialPrimitive.zeta]

noncomputable def profileRadius (h : ℝ) (p : Slow) : ℝ :=
  p.1 / Real.sqrt (BaseChartJets.normalizedCoordinates h p).1

noncomputable def movingWeight (p : Slow) : ℝ := stripWeight W (profileRadius F.data.h p)

theorem movingWeight_nonneg (p : Slow) : 0 ≤ movingWeight W p := stripWeight_nonneg W _

theorem profileRadius_pos {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    0 < profileRadius F.data.h p :=
  div_pos hR (Real.sqrt_pos.mpr (BaseChartJets.normalizedCoordinates_q_pos
    F.data.h_pos F.data.h_lt_half hT))

theorem profileRadius_sq {p : Slow} (hT : 0 < p.2.2) :
    (profileRadius F.data.h p)^2/2 = (BaseChartJets.normalizedCoordinates F.data.h p).2.1 := by
  have hq := BaseChartJets.normalizedCoordinates_q_pos F.data.h_pos F.data.h_lt_half hT
  unfold profileRadius
  rw [div_pow, Real.sq_sqrt hq.le, BaseChartJets.normalizedCoordinates_eq]
  unfold SimilarityHomogeneity.chartX SimilarityCoordinates.coordinateX SimilarityHomogeneity.chartQ
  ring

theorem movingWeight_eq {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    movingWeight W p = FinalSlowBase.weight W (BaseChartJets.normalizedCoordinates F.data.h p).2 :=
      by
  rw [movingWeight, stripWeight_eq W _ _ (profileRadius_pos hT hR), profileRadius_sq hT]

/-- The mean-variable ordering `(R,((T,Z),Y))` uses exactly the same
normalized point `(R,(Z,T))`. -/
noncomputable def meanPoint (x : LocalSignedRequest.Point) : Slow :=
  (x.1,(x.2.1.2,x.2.1.1))

theorem meanPoint_scalar (x : LocalSignedRequest.Point) :
    (BaseChartJets.normalizedCoordinates F.data.h (meanPoint x)).1 =
      MeanRankUpdate.chartQ (2*F.data.h) x := by
  rw [BaseChartJets.normalizedCoordinates_eq]
  rfl

/-- Exact equality with the strip used for the signed correction. -/
theorem movingStripData_zeta (U : LocalSignedRequest.SlowRegion (2*F.data.h))
    (epsilon S : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilon_one : ∀ n, epsilon n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    (x : LocalSignedRequest.Point) :
    (LocalSignedRequest.movingStripData U (leftRadius W) (rightRadius W)
      (FinalSlowBase.edgeExponent W/4) 1 (leftRadius_pos W)
      (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num)) (by norm_num)
      epsilon S hepsilon hepsilon_one hS).zeta x = movingWeight W (meanPoint x) := by
  unfold movingWeight profileRadius
  rw [meanPoint_scalar]
  rfl

theorem weight_zero_of_not_active {w : ℝ × ℝ}
    (hx : ¬w.1 ∈ Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
    FinalSlowBase.weight W w = 0 := by
  by_cases hl : w.1 ≤ NominalConeAssembly.activeLeft W
  · exact ActiveAnnulusWeight.radialWeight_zero_left _ _
      (by simpa only [FinalSlowBase.logLeft, Real.exp_log (NominalConeAssembly.activeLeft_pos W)]
        using hl)
  · have hr : NominalConeAssembly.activeRight W ≤ w.1 := by
      by_contra hn
      exact hx ⟨lt_of_not_ge hl, lt_of_not_ge hn⟩
    exact ActiveAnnulusWeight.radialWeight_zero_right _ _
      (by simpa only [FinalSlowBase.logRight, Real.exp_log (LeadingStressWeights.activeRight_pos
        W)] using hr)

end MovingWeight

section ActualTarget

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- The literal leading covariance target in its own normalized band. -/
noncomputable def actualTarget (p : Slow) : Plane :=
  (BaseChartJets.normalizedCoordinates F.data.h p).1 ^ (-CoordinateAlgebra.A F.data.h - 1/2) •
    ProfileSpectralCone.stressVector v.profiles F.data.h
      (BaseChartJets.normalizedCoordinates F.data.h p).2

noncomputable def targetAmplitude (p : Slow) : ℝ :=
  (BaseChartJets.normalizedCoordinates F.data.h p).1 ^ (-CoordinateAlgebra.A F.data.h - 1/2) *
    ‖ProfileSpectralCone.stressVector v.profiles F.data.h
      (BaseChartJets.normalizedCoordinates F.data.h p).2‖

theorem targetAmplitude_nonneg {p : Slow} (hT : 0 < p.2.2) : 0 ≤ targetAmplitude v p :=
  mul_nonneg (Real.rpow_pos_of_pos (BaseChartJets.normalizedCoordinates_q_pos
    F.data.h_pos F.data.h_lt_half hT) _).le (norm_nonneg _)

theorem stress_norm_le_plane (w : ℝ × ℝ) :
    ‖FinalSlowBase.leadingStress v w‖ ≤ ‖ProfileSpectralCone.stressVector v.profiles F.data.h w‖ :=
      by
  apply max_le
  · exact PiLp.norm_apply_le (ProfileSpectralCone.stressVector v.profiles F.data.h w) 0
  · exact PiLp.norm_apply_le (ProfileSpectralCone.stressVector v.profiles F.data.h w) 1

theorem targetAmplitude_lower (hcone : LeadingStressWeights.FullTrueCone v) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ PositiveRepresentatives.positivePart
      (PrimaryGeometryAssembly.referenceSet W),
      (BaseChartJets.normalizedCoordinates F.data.h p).2.1 ∈
        Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) →
      c * movingWeight W p ≤ targetAmplitude v p := by
  let K := AlignedProfileSpectralCone.referenceSet W
  have hK := AlignedProfileSpectralCone.referenceSet_compact W
  have hs : ContinuousOn (fun p => PositiveRepresentatives.stableQ F.data.h p ^
      (-CoordinateAlgebra.A F.data.h - 1/2)) K := by
    intro p hp
    have hp' := AlignedProfileSpectralCone.reference_point W hp
    exact ((PositiveRepresentatives.stableQ_smoothAt F.data.h_pos.le F.data.h_lt_half.le
      hp'.stable).rpow_const_of_ne
      hp'.scalar.ne').continuousAt.continuousWithinAt
  obtain ⟨k, hk, hb⟩ := hK.exists_forall_le' hs (fun p hp =>
    Real.rpow_pos_of_pos (AlignedProfileSpectralCone.reference_point W hp).scalar _)
  obtain ⟨m, hm, hmB⟩ := FinalSlowBase.leading_lowerBound v hcone
  refine ⟨k*m, mul_pos hk hm, ?_⟩
  intro p hp hx
  have hp' := AlignedProfileSpectralCone.reference_point W hp.1
  have hT : 0 < p.2.2 := hp.2
  have heta := (BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half hT).le
  have hinner : (BaseChartJets.normalizedCoordinates F.data.h p).2 ∈ FinalSlowBase.annulus W :=
    ⟨hx, abs_le.mp heta⟩
  have hf := hb p hp.1
  rw [PositiveRepresentatives.stableQ_eq_chartQ F.data.h_pos F.data.h_lt_half hT] at hf
  have hf' : k ≤ (BaseChartJets.normalizedCoordinates F.data.h p).1 ^
      (-CoordinateAlgebra.A F.data.h - 1/2) := by
    simpa only [BaseChartJets.normalizedCoordinates_eq] using hf
  have hnorm := (hmB _ hinner).trans (stress_norm_le_plane v _)
  rw [movingWeight_eq W hT hp'.radius]
  unfold targetAmplitude
  calc
    k*m*FinalSlowBase.weight W _ = k*(m*FinalSlowBase.weight W _) := by ring
    _ ≤ k*‖ProfileSpectralCone.stressVector v.profiles F.data.h
        (BaseChartJets.normalizedCoordinates F.data.h p).2‖ :=
      mul_le_mul_of_nonneg_left hnorm hk.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hf' (norm_nonneg _)

theorem actualTarget_eq_direction {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0) {p : Slow}
    (hp : p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W))
    (hx : (BaseChartJets.normalizedCoordinates F.data.h p).2.1 ∈
      Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
    actualTarget v p = targetAmplitude v p • a.target p := by
  rw [PrimaryGeometryAssembly.target_eq_normalized_stress H v a hp.1 hp.2 hx]
  unfold actualTarget targetAmplitude PrimaryRepresentatives.normalDirection
  by_cases hz : ProfileSpectralCone.stressVector v.profiles F.data.h
      (BaseChartJets.normalizedCoordinates F.data.h p).2 = 0
  · simp only [hz, smul_zero]
  · rw [smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), mul_one]

theorem stress_zero_of_not_active {w : ℝ × ℝ} (hw : 0 < w.1)
    (heta : w.2 ∈ Icc (-1 : ℝ) 1)
    (hx : ¬w.1 ∈ Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
    ProfileSpectralCone.stressVector v.profiles F.data.h w = 0 := by
  have hz : LeadingStressWeights.stress v.profiles F.data.h w = 0 := by
    by_cases hl : w.1 ≤ NominalConeAssembly.activeLeft W
    · exact LeadingStressWeights.stress_zero_before v hw.le hl heta
    · exact LeadingStressWeights.stress_zero_after v
        (by by_contra hn; exact hx ⟨lt_of_not_ge hl, lt_of_not_ge hn⟩) heta
  ext k
  fin_cases k
  · exact congrArg Prod.fst hz
  · exact congrArg Prod.snd hz

theorem actualTarget_eq_direction_all {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0) {p : Slow}
    (hp : p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W)) :
    actualTarget v p = targetAmplitude v p • a.target p := by
  by_cases hx : (BaseChartJets.normalizedCoordinates F.data.h p).2.1 ∈
      Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)
  · exact actualTarget_eq_direction H v a hp hx
  · have hp' := AlignedProfileSpectralCone.reference_point W hp.1
    have hX := ProfileSpectralCone.normalized_X_pos F.data.h_pos F.data.h_lt_half hp.2 hp'.radius
    have heta := (BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half hp.2).le
    have hz := stress_zero_of_not_active v hX (abs_le.mp heta) hx
    simp only [actualTarget, targetAmplitude, hz, smul_zero, norm_zero, mul_zero, zero_smul]

theorem targetAmplitude_lower_all (hcone : LeadingStressWeights.FullTrueCone v) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ PositiveRepresentatives.positivePart
      (PrimaryGeometryAssembly.referenceSet W), c * movingWeight W p ≤ targetAmplitude v p := by
  obtain ⟨c, hc, hb⟩ := targetAmplitude_lower v hcone
  refine ⟨c, hc, ?_⟩
  intro p hp
  by_cases hx : (BaseChartJets.normalizedCoordinates F.data.h p).2.1 ∈
      Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)
  · exact hb p hp hx
  · have hp' := AlignedProfileSpectralCone.reference_point W hp.1
    rw [movingWeight_eq W hp.2 hp'.radius, weight_zero_of_not_active W hx, mul_zero]
    exact targetAmplitude_nonneg v hp.2

/-- The chart target at its own band is exactly the actual leading
stress times the residual scalar coordinate. -/
theorem covarianceTarget_eq_actual {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1)
    (N : ℕ) (U : PartitionedCovariance.UnsignedLabel) :
    FinalSlowBase.covarianceTarget H v
      (ChartScales.Q (U.1+N) * (BaseChartJets.normalizedCoordinates F.data.h p).1) N U p =
      actualTarget v p := by
  have hq := BaseChartJets.normalizedCoordinates_q_pos F.data.h_pos F.data.h_lt_half hT
  have hX := ProfileSpectralCone.normalized_X_pos F.data.h_pos F.data.h_lt_half hT hR
  have heta := (BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half hT).le
  have he := EntranceAlignedBase.modulated_leading_stress_eq H v hX.le heta
  have hdiv : ChartScales.Q (U.1+N) /
      (ChartScales.Q (U.1+N) * (BaseChartJets.normalizedCoordinates F.data.h p).1) =
      ((BaseChartJets.normalizedCoordinates F.data.h p).1)⁻¹ := by
    field_simp [(ChartScales.Q_pos (U.1+N)).ne']
  have hfactor : (ChartScales.Q (U.1+N) /
      (ChartScales.Q (U.1+N) * (BaseChartJets.normalizedCoordinates F.data.h p).1)) ^
        (PartitionedCovariance.velocityExponent F.data.h + 1/2) =
      (BaseChartJets.normalizedCoordinates F.data.h p).1 ^ (-CoordinateAlgebra.A F.data.h - 1/2) :=
        by
    rw [hdiv, Real.inv_rpow hq.le, ← Real.rpow_neg hq.le]
    congr 1
    unfold PartitionedCovariance.velocityExponent CoordinateAlgebra.A
    ring
  ext k
  fin_cases k <;>
    simp [FinalSlowBase.covarianceTarget, PartitionedCovariance.chartTarget,
      actualTarget, ProfileSpectralCone.stressVector, FinalSlowBase.coefficients,
      he.1, he.2, PiLp.smul_apply, smul_eq_mul] <;>
    exact Or.inl (by simpa only [one_div] using hfactor)

end ActualTarget

section FinalBounds

open PrimaryGeometryAssembly PrimaryCovarianceBounds

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)
    {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
    (a : Prepared H v upper B r0 N0)

/-- The actual primary covariance and the actual leading target satisfy
all order-zero hypotheses used for positive square-root weights, with
the same moving flat weight through both closed attachment edges. -/
theorem exists_actual_bounds (hcone : LeadingStressWeights.FullTrueCone v)
    (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (hr0 : 0 < r0) :
    ∃ N : ℕ, a.N ≤ N ∧ ∃ detGap entryBound inverseLower : ℝ,
      0 < detGap ∧ 1 ≤ entryBound ∧ 0 < inverseLower ∧
      ∀ (L : Index W a.N), N ≤ BaseChartJets.cellBand L → ∀ p : Slow,
        p ∈ PositiveRepresentatives.positivePart (referenceSet W) →
        p ∈ (domain W a.N).carrier L →
        ZeroOrderBounds (Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))
          detGap entryBound inverseLower (movingWeight W p)
          (preparedCovariance H v a vr vt L p) (fun k => actualTarget v p k) := by
  obtain ⟨N, hN, dg, eb, il, hdg, heb, hil, hb⟩ := exists_prepared_bounds H v a vr vt hdet hr0
  obtain ⟨c, hc, hcb⟩ := targetAmplitude_lower_all v hcone
  refine ⟨N, hN, dg, eb, il*c, hdg, heb, mul_pos hil hc, ?_⟩
  intro L hL p hp hpL
  have hbound := hb L hL p hp hpL (targetAmplitude v p) (targetAmplitude_nonneg v hp.2)
  have htarget : FlatCovariance.scaledTarget (targetAmplitude v p) (fun k => a.target p k) =
      (fun k => actualTarget v p k) := by
    rw [actualTarget_eq_direction_all H v a hp]
    rfl
  rw [htarget] at hbound
  refine ⟨hbound.determinant, hbound.entries, ?_⟩
  intro j
  calc
    (il*c)*Real.sqrt (ChartScales.S (BaseChartJets.cellBand L))*movingWeight W p =
        (il*Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))*(c*movingWeight W p) := by ring
    _ ≤ (il*Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))*targetAmplitude v p :=
      mul_le_mul_of_nonneg_left (hcb p hp) (mul_nonneg hil.le (Real.sqrt_nonneg _))
    _ ≤ _ := hbound.weights j

theorem restricted_covariance (vr vt : TorusInverse.Plane) (N : ℕ) (hN : a.N ≤ N)
    (L : Index W N) (p : Slow) :
    preparedCovariance H v (a.restrict N hN) vr vt L p =
      preparedCovariance H v a vr vt (earlierIndex hN L) p := rfl

/-- A single final band threshold suffices.  Restriction retains the
original representative, carrier and phase on each surviving label. -/
theorem exists_restricted_actual_bounds (hcone : LeadingStressWeights.FullTrueCone v)
    (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (hr0 : 0 < r0) :
    ∃ N : ℕ, ∃ hN : a.N ≤ N, ∃ detGap entryBound inverseLower : ℝ,
      0 < detGap ∧ 1 ≤ entryBound ∧ 0 < inverseLower ∧
      ∀ (L : Index W N) (p : Slow),
        p ∈ PositiveRepresentatives.positivePart (referenceSet W) →
        p ∈ (domain W N).carrier L →
        ZeroOrderBounds (Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))
          detGap entryBound inverseLower (movingWeight W p)
          (preparedCovariance H v (a.restrict N hN) vr vt L p) (fun k => actualTarget v p k) := by
  obtain ⟨N, hN, dg, eb, il, hdg, heb, hil, hb⟩ := exists_actual_bounds H v a hcone vr vt hdet hr0
  refine ⟨N, hN, dg, eb, il, hdg, heb, hil, ?_⟩
  intro L p hp hpL
  rw [restricted_covariance H v a vr vt]
  exact hb (earlierIndex hN L) L.property p hp hpL

/-- The source profile supplies the whole geometry.  There is no extra
target orientation, determinant, inverse-weight or ODE-error input. -/
theorem exists_constructed_bounds (hcone : LeadingStressWeights.FullTrueCone v)
    (upper : ℝ) (B : ℕ) (r0 : ℝ) (hr0 : 0 < r0)
    (hbox : 2 * NominalConeAssembly.activeRight W ≤ FinalSlowBase.boxRadius W upper)
    (N0 : ℕ) (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    ∃ a : Prepared H v upper B r0 N0, ∃ detGap entryBound inverseLower : ℝ,
      0 < detGap ∧ 1 ≤ entryBound ∧ 0 < inverseLower ∧
      ∀ (L : Index W a.N) (p : Slow),
        p ∈ PositiveRepresentatives.positivePart (referenceSet W) →
        p ∈ (domain W a.N).carrier L →
        ZeroOrderBounds (Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))
          detGap entryBound inverseLower (movingWeight W p)
          (preparedCovariance H v a vr vt L p) (fun k => actualTarget v p k) := by
  let a := prepared H v hcone upper B r0 hbox N0
  obtain ⟨N, hN, dg, eb, il, hdg, heb, hil, hb⟩ :=
    exists_restricted_actual_bounds H v a hcone vr vt hdet hr0
  exact ⟨a.restrict N hN, dg, eb, il, hdg, heb, hil, hb⟩

end FinalBounds

end NavierStokes.PrimaryTargetBounds

end
