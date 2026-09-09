/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveEdgeExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedGeometry
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Smooth attachment at the native dyadic band boundaries

The dyadic profile is flat at its support endpoints, although it does not
have a zero germ there.  Local smoothness of the actual raw primary is
proved from the fixed prepared family before using that flatness.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.NativeBandExtension

open Set Filter Function PrimaryCopyBounds PhaseJetBounds PrimaryPulseBounds
open scoped Topology ContDiff BigOperators InnerProductSpace

/-- Native: an abbreviation for `WaveEdgeExtension.NativePoint`. -/
abbrev Native := WaveEdgeExtension.NativePoint
/-- Slow type used in native band extension. -/
abbrev Slow := PhaseCalculus.Slow

/-- Use the entrywise matrix norm inherited from the finite function space. -/
noncomputable local instance : NormedAddCommGroup SmoothCovariance.Mat2 :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℝ))

/-- Scalar multiplication is the pointwise real vector-space structure on matrices. -/
noncomputable local instance : NormedSpace ℝ SmoothCovariance.Mat2 :=
  inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℝ))

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

section FlatJets

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem finite_smooth_neighborhood {f : D → E} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ∃ s : Set D, IsOpen s ∧ x ∈ s ∧ ContDiffOn ℝ n f s := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (nat_le_infty n) (by simp)
  obtain ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  exact ⟨u, hu, hxu, hfs.mono hus⟩

/-- All actual tensors vanish at a closure point of an open zero region,
provided the function is locally smooth at that point. -/
theorem jets_zero_at_closure {f : D → E} {s : Set D} {x : D}
    (hs : IsOpen s) (hf : ContDiffAt ℝ ∞ f x) (hx : x ∈ closure s)
    (hz : ∀ y ∈ s, f y = 0) (n : ℕ) : iteratedFDeriv ℝ n f x = 0 := by
  have hc : ContinuousAt (iteratedFDeriv ℝ n f) x :=
    (hf.iteratedFDeriv_right (m := 0) (by simp)).continuousAt
  have : NeBot (𝓝[s] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hlim : Tendsto (fun y => ‖iteratedFDeriv ℝ n f y‖) (𝓝[s] x)
      (𝓝 ‖iteratedFDeriv ℝ n f x‖) := hc.norm.mono_left inf_le_left
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hg : f =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hs.mem_nhds hy] with z hz'
    exact hz z hz'
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hg n, iteratedFDeriv_fun_zero]
  simp

theorem scalar_support_endpoint_jets {f : ℝ → E} {a b : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : support f ⊆ Ioo a b) (n : ℕ) :
    iteratedFDeriv ℝ n f a = 0 ∧ iteratedFDeriv ℝ n f b = 0 := by
  constructor
  · refine jets_zero_at_closure (x := a) (s := Iio a) isOpen_Iio hf.contDiffAt
      (by simp only [closure_Iio, mem_Iic, le_refl]) ?_ n
    intro y hy
    by_contra hn
    exact (not_lt_of_ge hy.le) (hs hn).1
  · refine jets_zero_at_closure (x := b) (s := Ioi b) isOpen_Ioi hf.contDiffAt
      (by simp only [closure_Ioi, mem_Ici, le_refl]) ?_ n
    intro y hy
    by_contra hn
    exact (not_lt_of_ge hy.le) (hs hn).2

theorem dyadicProfile_endpoint_jets (n : ℕ) :
    iteratedFDeriv ℝ n SquaredPartition.dyadicProfile (1 / 2) = 0 ∧
      iteratedFDeriv ℝ n SquaredPartition.dyadicProfile 2 = 0 :=
  scalar_support_endpoint_jets SquaredPartition.dyadicProfile_smooth
    (by rw [SquaredPartition.dyadicProfile_support]) n

theorem transverse_endpoint_jets {r : ℝ} (hr : 0 < r) (n : ℕ) :
    iteratedFDeriv ℝ n (PartitionedCovariance.cutoff r) (-r) = 0 ∧
      iteratedFDeriv ℝ n (PartitionedCovariance.cutoff r) r = 0 :=
  scalar_support_endpoint_jets (f := PartitionedCovariance.cutoff r)
      (SquaredPartition.gridMask_smooth r 0)
    (by rw [PartitionedCovariance.cutoff_support hr]) n

/-- Flatness of a scalar function survives an actual smooth pullback. -/
theorem flat_comp_jets {g : ℝ → ℝ} {q : D → ℝ} {x : D}
    (hg : ContDiff ℝ ∞ g) (hq : ContDiffAt ℝ ∞ q x)
    (hz : ∀ j, iteratedFDeriv ℝ j g (q x) = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y => g (q y)) x = 0 := by
  obtain ⟨s, hs, hxs, hqs⟩ := finite_smooth_neighborhood hq n
  let K : ℝ := 1 + ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j q x‖
  have hK : 1 ≤ K := by
    dsimp only [K]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hbound (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j q x‖ ≤ K := by
    have hb := Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j q x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    exact hb.trans (le_add_of_nonneg_left (by norm_num))
  have hb := norm_iteratedFDerivWithin_comp_le (hg.of_le (nat_le_infty n)).contDiffOn hqs
    (n := n) (by rfl) uniqueDiffOn_univ hs.uniqueDiffOn (mapsTo_univ q s) hxs
    (C := 0) (D := K)
    (by intro j hj; simp only [iteratedFDerivWithin_univ, hz, norm_zero, le_refl])
    (by
      intro j hj hjn
      rw [iteratedFDerivWithin_of_isOpen j hs hxs]
      exact (hbound j hjn).trans (by simpa only [pow_one] using pow_le_pow_right₀ hK hj))
  rw [iteratedFDerivWithin_of_isOpen n hs hxs] at hb
  apply norm_eq_zero.mp
  simp only [mul_zero, zero_mul] at hb
  exact le_antisymm hb (norm_nonneg _)

/-- A flat scalar factor kills every tensor of the actual smooth product. -/
theorem flat_smul_jets {g : D → ℝ} {f : D → E} {x : D}
    (hg : ContDiffAt ℝ ∞ g x) (hf : ContDiffAt ℝ ∞ f x)
    (hz : ∀ j, iteratedFDeriv ℝ j g x = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y => g y • f y) x = 0 := by
  obtain ⟨s, hs, hxs, hgs⟩ := finite_smooth_neighborhood hg n
  obtain ⟨t, ht, hxt, hft⟩ := finite_smooth_neighborhood hf n
  have hb := norm_iteratedFDerivWithin_smul_le
    (hgs.mono (inter_subset_left (t := t))) (hft.mono (inter_subset_right (s := s)))
    (hs.inter ht).uniqueDiffOn (show x ∈ s ∩ t from ⟨hxs, hxt⟩) (n := n) (by rfl)
  simp only [iteratedFDerivWithin_of_isOpen _ (hs.inter ht) ⟨hxs, hxt⟩,
    hz, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

theorem dyadic_product_endpoint {q : D → ℝ} {f : D → E} {x : D}
    (hq : ContDiffAt ℝ ∞ q x) (hf : ContDiffAt ℝ ∞ f x)
    (he : q x = 1 / 2 ∨ q x = 2) :
    ContDiffAt ℝ ∞ (fun y => SquaredPartition.dyadicProfile (q y) • f y) x ∧
      ∀ n, iteratedFDeriv ℝ n (fun y => SquaredPartition.dyadicProfile (q y) • f y) x = 0 := by
  have hc := SquaredPartition.dyadicProfile_smooth.contDiffAt.comp x hq
  refine ⟨hc.smul hf, flat_smul_jets hc hf ?_⟩
  intro j
  apply flat_comp_jets SquaredPartition.dyadicProfile_smooth hq
  intro k
  rcases he with h | h
  · rw [h]; exact (dyadicProfile_endpoint_jets k).1
  · rw [h]; exact (dyadicProfile_endpoint_jets k).2

end FlatJets

/-! ## Local smoothness from the actual matrix and phase construction -/

section LocalAlgebra

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [NormedSpace ℝ D] in
theorem strictCone_eventually {H : D → SmoothCovariance.Mat2}
    {T : D → SmoothCovariance.Vec2} {x : D}
    (hH : ∀ i j, ContinuousAt (fun y => H y i j) x)
    (hT : ∀ i, ContinuousAt (fun y => T y i) x)
    (hx : SmoothCovariance.StrictCone (H x) (T x)) :
    ∀ᶠ y in 𝓝 x, SmoothCovariance.StrictCone (H y) (T y) := by
  have hH' : ContinuousAt H x := continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (hH i))
  have hT' : ContinuousAt T x := continuousAt_pi.mpr hT
  exact (hH'.prodMk hT') (SmoothCovariance.isOpen_strictConeRegion.mem_nhds hx)

theorem cramer_amplitude_contDiffAt {H : D → SmoothCovariance.Mat2}
    {T : D → SmoothCovariance.Vec2} {x : D}
    (hH : ∀ i j, ContDiffAt ℝ ∞ (fun y => H y i j) x)
    (hT : ∀ i, ContDiffAt ℝ ∞ (fun y => T y i) x)
    (hx : SmoothCovariance.StrictCone (H x) (T x)) (j : Fin 2) :
    ContDiffAt ℝ ∞ (fun y => Real.sqrt (SmoothCovariance.weights (H y) (T y) j)) x := by
  have hd : ContDiffAt ℝ ∞ (fun y => (H y).det) x := by
    simp only [Matrix.det_fin_two]
    exact ((hH 0 0).mul (hH 1 1)).sub ((hH 0 1).mul (hH 1 0))
  have hn : ContDiffAt ℝ ∞ (fun y => SmoothCovariance.cramerNumerator (H y) (T y) j) x := by
    fin_cases j
    · exact ((hT 0).mul (hH 1 1)).sub ((hH 0 1).mul (hT 1))
    · exact ((hH 0 0).mul (hT 1)).sub ((hT 0).mul (hH 1 0))
  exact (hn.div hd hx.det_ne_zero).sqrt (hx.weights_pos j).ne'

theorem projectedPressure_contDiffAt (frequency : ℝ)
    {N Ndot u action source : D → ProblemStatement.Space} {x : D}
    (hN : ContDiffAt ℝ ∞ N x) (hNd : ContDiffAt ℝ ∞ Ndot x)
    (hu : ContDiffAt ℝ ∞ u x) (ha : ContDiffAt ℝ ∞ action x)
    (hf : ContDiffAt ℝ ∞ source x) (hn : N x ≠ 0) :
    ContDiffAt ℝ ∞ (ParticularWaveBounds.projectedPressure frequency N Ndot u action source) x := by
  have hp : ContDiffAt ℝ ∞ (fun y => TangentProjection.pressureCoefficient
      (N y) (Ndot y) (u y) (action y) (source y)) x :=
    (((hN.inner ℝ ha).sub (hNd.inner ℝ hu)).add (hN.inner ℝ hf)).div
      (hN.inner ℝ hN) (inner_self_ne_zero.mpr hn)
  exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x hp)).div_const
      (frequency : ℂ)

end LocalAlgebra

/-- Native Q, given by `SimilarityCoordinates.coordinateQ (2 * h) (x.1.2.2, x.1.2.1)`. -/
noncomputable def nativeQ (h : ℝ) (x : Native) : ℝ :=
  SimilarityCoordinates.coordinateQ (2 * h) (x.1.2.2, x.1.2.1)

theorem nativeQ_contDiffAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : Native} (hT : 0 < x.1.2.2) : ContDiffAt ℝ ∞ (nativeQ h) x :=
  (SimilarityCoordinates.coordinateQ_smooth (by linarith) (by linarith) hT).comp x
    (contDiffAt_fst.snd.snd.prodMk contDiffAt_fst.snd.fst)

section ActualTarget

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)

theorem actualTarget_contDiffAt {p : Slow} (hT : 0 < p.2.2)
    (hX : 0 < (BaseChartJets.normalizedCoordinates F.data.h p).2.1) :
    ContDiffAt ℝ ∞ (PrimaryTargetBounds.actualTarget v) p := by
  have hc := BaseChartJets.normalizedCoordinates_smoothAt F.data.h_pos F.data.h_lt_half hT
  have hq := BaseChartJets.normalizedCoordinates_q_pos F.data.h_pos F.data.h_lt_half hT
  have he := BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half hT
  have hs := (FinalSlowBase.leadingStress_smoothAt v hX (abs_le.mp he.le)).comp p hc.snd
  have hv := MovingFrameODE.pairCLM.contDiff.contDiffAt.comp p hs
  exact (hc.fst.rpow_const_of_ne hq.ne').smul hv

end ActualTarget

section PhaseLocal

variable {ι : Type*} {U : Domain ι Slow}

theorem phaseCovariance_contDiffAt (F : Fin 2 → PhaseConstruction U)
    (pref : Fin 2 → ι → ℝ) (hpref : ∀ j, PolynomialJets U (fun i _ => pref j i))
    (i : ι) {p : Slow} (hp : p ∈ U.carrier i) (r c : Fin 2) :
    ContDiffAt ℝ ∞ (fun q => primaryCovariance pref (fun j => (F j).frame)
      (fun j => (F j).lam) (fun j => (F j).u) (fun j => (F j).L) i q r c) p :=
  ((primaryCovariance_entry_polynomial U pref (fun j => (F j).frame)
    (fun j => (F j).lam) (fun j => (F j).u) (fun j => (F j).L)
    hpref (fun j => (F j).pulse_jets) (fun j => (F j).lam_pos)
    (fun j => (F j).u_pos) (fun j => (F j).L_pos) r c).smooth i).contDiffAt ((U.isOpen i).mem_nhds
        hp)

theorem normalizedPulse_contDiffAt (F : PhaseConstruction U) (i : ι) {z : Slow × ℝ}
    (hp : z.1 ∈ U.carrier i) (ht : z.2 ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (normalizedPulse (F.frame i) (F.lam i) (F.u i) (F.L i)) z :=
  (F.pulse_jets.smooth i).contDiffAt (((U.isOpen i).prod isOpen_Ioo).mem_nhds ⟨hp, ht⟩)

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The actual Cramer square root and actual homogeneous ODE pulse are
smooth at a strict-cone point, regardless of which side of a band boundary
the neighboring points occupy. -/
theorem primaryVelocity_contDiffAt (F : Fin 2 → PhaseConstruction U)
    (pref : Fin 2 → ι → ℝ) (hpref : ∀ j, PolynomialJets U (fun i _ => pref j i))
    (χ : ι → D → Slow × ℝ) (ε : ι → ℝ)
    (T : ι → D → SmoothCovariance.Vec2) (mask : ι → D → ℝ)
    (j : Fin 2) (i : ι) {x : D}
    (hχ : ContDiffAt ℝ ∞ (χ i) x)
    (hT : ∀ k, ContDiffAt ℝ ∞ (fun y => T i y k) x)
    (hm : ContDiffAt ℝ ∞ (mask i) x)
    (hp : (χ i x).1 ∈ U.carrier i) (ht : (χ i x).2 ∈ Ioo (0 : ℝ) 1)
    (hc : SmoothCovariance.StrictCone (pulseMatrix F pref χ i x) (T i x)) :
    ContDiffAt ℝ ∞ (primaryVelocity F pref χ ε T mask j i) x := by
  have hH (r c : Fin 2) : ContDiffAt ℝ ∞ (fun y => pulseMatrix F pref χ i y r c) x := by
    have hcomp := (phaseCovariance_contDiffAt F pref hpref i hp r c).comp x hχ.fst
    exact hcomp
  have ha := cramer_amplitude_contDiffAt hH hT hc j
  have hu := (normalizedPulse_contDiffAt (F j) i hp ht).comp x hχ
  exact ((contDiffAt_const.mul ha).mul hm).smul hu

theorem phasePressure_contDiffAt (F : PhaseConstruction U)
    (χ : ι → D → Slow × ℝ) (frequency : ι → ℝ) (u : ι → D → ProblemStatement.Space)
    (i : ι) {x : D} (hχ : ContDiffAt ℝ ∞ (χ i) x)
    (hp : (χ i x).1 ∈ U.carrier i) (ht : (χ i x).2 ∈ Ioo (0 : ℝ) 1)
    (hu : ContDiffAt ℝ ∞ (u i) x) :
    ContDiffAt ℝ ∞ (phasePressure F χ frequency u i) x := by
  have hz : ContDiffAt ℝ ∞ (phasePoint F χ i) x :=
    hχ.fst.prodMk (contDiffAt_const.mul hχ.snd)
  have hm : phasePoint F χ i x ∈ (U.slot F.V F.openV).carrier i := by
    refine ⟨hp, F.interval i ⟨mul_nonneg (F.L_pos i).le ht.1.le, ?_⟩⟩
    have hb := mul_le_mul_of_nonneg_left ht.2.le (F.L_pos i).le
    simp only [mul_one] at hb
    exact hb
  have hbase := F.phase.polynomial_jets U F.V F.openV F.baseF F.baseG
    F.r_pos F.one_le_M F.constants F.epsilon_ne F.radius F.slot
  have hn := ((hbase.1.smooth i).contDiffAt (((U.slot F.V F.openV).isOpen i).mem_nhds hm)).comp x hz
  have hnd := ((hbase.2.1.smooth i).contDiffAt (((U.slot F.V F.openV).isOpen i).mem_nhds hm)).comp
      x hz
  have hs := ((hbase.2.2.smooth i).contDiffAt (((U.slot F.V F.openV).isOpen i).mem_nhds hm)).comp x
      hz
  have hF := ((F.baseF.smooth i).contDiffAt ((U.isOpen i).mem_nhds hp)).comp x hχ.fst
  have hA := PrimaryCopyBridge.baseOperatorFamily.contDiff.contDiffAt.comp x (hF.prodMk hs)
  apply projectedPressure_contDiffAt (frequency i) hn hnd hu (hA.clm_apply hu) contDiffAt_const
  exact norm_pos_iff.mp (F.b_pos.trans_le (F.normal_range.1 i _ hm))

end PhaseLocal

/-! ## The same fixed prepared family at the closed band endpoints -/

section Prepared

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)

/-- These are precisely the closed-reference zeroth-order bounds of the
already selected family. No new family or frequency threshold is selected. -/
structure ClosedMargins (vr vt : TorusInverse.Plane) where
  /-- Gap of `ClosedMargins`, of type `ℝ`. -/
  gap : ℝ
  /-- Entry of `ClosedMargins`, of type `ℝ`. -/
  entry : ℝ
  /-- Lower of `ClosedMargins`, of type `ℝ`. -/
  lower : ℝ
  gap_pos : 0 < gap
  entry_one : 1 ≤ entry
  lower_pos : 0 < lower
  covariance : ∀ (L : PrimaryGeometryAssembly.Index W a.N) (p : Slow),
    p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W) →
    p ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L →
    PrimaryCovarianceBounds.ZeroOrderBounds (Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))
      gap entry lower (PrimaryTargetBounds.movingWeight W p)
      (PrimaryTargetBounds.preparedCovariance H v a vr vt L p)
      (fun k => PrimaryTargetBounds.actualTarget v p k)

/-- Base velocity, constructed using `primaryVelocity`. -/
noncomputable def baseVelocity (hr0 : 0 < r0) (vr vt : TorusInverse.Plane) (j : Fin 2) :
    PrimaryGeometryAssembly.Index W a.N → Native → ProblemStatement.Space :=
  primaryVelocity (PrimaryGeometryAssembly.construction H v a hr0)
    (preparedPrefactor r0 vr vt) (ActualSignedGeometry.pulseCoordinates H v a)
    (fun L => ChartScales.epsilon F.data.h (BaseChartJets.cellBand L))
    (fun _ x k => PrimaryTargetBounds.actualTarget v x.1 k)
    (fun L x => PrimaryRepresentatives.nativeMask (PrimaryGeometryAssembly.label W L).1
      (PrimaryGeometryAssembly.label W L).2 x.1) j

/-- Base pressure, constructed using `phasePressure`. -/
noncomputable def basePressure (hr0 : 0 < r0) (vr vt : TorusInverse.Plane) (j : Fin 2) :
    PrimaryGeometryAssembly.Index W a.N → Native → ℂ :=
  phasePressure (PrimaryGeometryAssembly.construction H v a hr0 j)
    (ActualSignedGeometry.pulseCoordinates H v a)
    (fun L => (ChartScales.carrier F.data.h (BaseChartJets.cellBand L) : ℝ))
    (baseVelocity H v a hr0 vr vt j)

/-- Outer factor, constructed using `outerCutoff`. -/
noncomputable def outerFactor (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) : ℝ :=
  outerCutoff (ActualSignedGeometry.pulseCoordinates H v a L x).2 *
    (SquaredPartition.dyadicProfile (nativeQ F.data.h x) * PartitionedCovariance.cutoff r0 x.2.1)

/-- Band velocity, given by `outerFactor H v a L x • baseVelocity H v a hr0 vr vt j L x`. -/
noncomputable def bandVelocity (hr0 : 0 < r0) (vr vt : TorusInverse.Plane) (j : Fin 2)
    (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) : ProblemStatement.Space :=
  outerFactor H v a L x • baseVelocity H v a hr0 vr vt j L x

/-- Band pressure, given by `outerFactor H v a L x • basePressure H v a hr0 vr vt j L x`. -/
noncomputable def bandPressure (hr0 : 0 < r0) (vr vt : TorusInverse.Plane) (j : Fin 2)
    (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) : ℂ :=
  outerFactor H v a L x • basePressure H v a hr0 vr vt j L x

theorem coordinates_smooth (L : PrimaryGeometryAssembly.Index W a.N) :
    ContDiff ℝ ∞ (ActualSignedGeometry.pulseCoordinates H v a L) :=
  contDiff_fst.prodMk (contDiff_snd.snd.div_const _)

theorem outerFactor_contDiffAt (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hT : 0 < x.1.2.2) : ContDiffAt ℝ ∞ (outerFactor H v a L) x := by
  have ho := outerCutoff_smooth.contDiffAt.comp x (coordinates_smooth H v a L).contDiffAt.snd
  have hq := SquaredPartition.dyadicProfile_smooth.contDiffAt.comp x
    (nativeQ_contDiffAt F.data.h_pos F.data.h_lt_half hT)
  have ht := (SquaredPartition.gridMask_smooth r0 0).contDiffAt.comp x contDiffAt_snd.fst
  exact ho.mul (hq.mul ht)

theorem bandPressure_eq_phasePressure (hr0 : 0 < r0) (vr vt : TorusInverse.Plane) (j : Fin 2)
    (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) :
    bandPressure H v a hr0 vr vt j L x =
      phasePressure (PrimaryGeometryAssembly.construction H v a hr0 j)
        (ActualSignedGeometry.pulseCoordinates H v a)
        (fun L => (ChartScales.carrier F.data.h (BaseChartJets.cellBand L) : ℝ))
        (bandVelocity H v a hr0 vr vt j) L x :=
  (phasePressure_smul _ _ _ (outerFactor H v a) (baseVelocity H v a hr0 vr vt j) L x).symm

end Prepared

/-- Radial interior, constructed using `WaveEdgeExtension.windowDomain`. -/
noncomputable def radialInterior {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) : Set
    Native :=
  WaveEdgeExtension.windowDomain WaveEdgeExtension.nativeSlowDomain (WaveEdgeExtension.nativeRadius
      F.data.h)
    (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)

theorem radialInterior_open {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    IsOpen (radialInterior W) :=
  WaveEdgeExtension.windowDomain_open WaveEdgeExtension.nativeSlowDomain_open
    (WaveEdgeExtension.nativeRadius_smooth F.data.h_pos F.data.h_lt_half).continuousOn _ _

theorem radialInterior_spec {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {x : Native} (hx : x ∈ radialInterior W) :
    0 < x.1.2.2 ∧ 0 < x.1.1 ∧
      (BaseChartJets.normalizedCoordinates F.data.h x.1).2.1 ∈
        Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) ∧
      0 < PrimaryTargetBounds.movingWeight W x.1 := by
  have ht : 0 < x.1.2.2 := hx.1
  have ha := PrimaryTargetBounds.leftRadius_pos W
  have hr := ha.trans hx.2.1
  have hq := BaseChartJets.normalizedCoordinates_q_pos F.data.h_pos F.data.h_lt_half ht
  have hroot := Real.sqrt_pos.mpr hq
  have hR : 0 < x.1.1 := by
    have hm := mul_pos hr hroot
    simpa only [WaveEdgeExtension.nativeRadius, PrimaryTargetBounds.profileRadius,
      div_mul_cancel₀ _ hroot.ne'] using hm
  have hasq : (PrimaryTargetBounds.leftRadius W) ^ 2 / 2 = NominalConeAssembly.activeLeft W := by
    rw [PrimaryTargetBounds.leftRadius,
      Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)]
    ring
  have hbsq : (PrimaryTargetBounds.rightRadius W) ^ 2 / 2 = NominalConeAssembly.activeRight W := by
    rw [PrimaryTargetBounds.rightRadius,
      Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W).le)]
    ring
  have hsq := PrimaryTargetBounds.profileRadius_sq (F := F) ht
  have hX : (BaseChartJets.normalizedCoordinates F.data.h x.1).2.1 ∈
      Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) := by
    rw [← hsq, ← hasq, ← hbsq]
    change (PrimaryTargetBounds.leftRadius W) ^ 2 / 2 <
      (WaveEdgeExtension.nativeRadius F.data.h x) ^ 2 / 2 ∧
      (WaveEdgeExtension.nativeRadius F.data.h x) ^ 2 / 2 <
        (PrimaryTargetBounds.rightRadius W) ^ 2 / 2
    constructor
    · nlinarith [mul_pos (sub_pos.mpr hx.2.1) (add_pos hr ha)]
    · nlinarith [mul_pos (sub_pos.mpr hx.2.2) (add_pos (hr.trans hx.2.2) hr)]
  refine ⟨ht, hR, hX, ?_⟩
  exact WeightedRadialPrimitive.zeta_pos _ _ (WeightedRadialPrimitive.logPosition_mem ha hx.2)

theorem reference_of_closed_band {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {x : Native} (hx : x ∈ radialInterior W) (hq : nativeQ F.data.h x ∈ Icc (1 / 2 : ℝ) 2) :
    x.1 ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W) := by
  obtain ⟨ht, hR, hX, _⟩ := radialInterior_spec W hx
  have hs := SimilarityCoordinates.coordinateQ_spec
    (show 0 < 2 * F.data.h by linarith [F.data.h_pos])
    (show 2 * F.data.h < 1 by linarith [F.data.h_lt_half]) (p := (x.1.2.2, x.1.2.1)) ht
  refine ⟨subset_closure ?_, ht⟩
  refine ⟨hR.le, ht.le, nativeQ F.data.h x, hq, hs.2, ?_⟩
  have he := And.intro hX.1.le hX.2.le
  simp only [BaseChartJets.normalizedCoordinates_eq, SimilarityHomogeneity.chartX,
    SimilarityCoordinates.coordinateX, SimilarityHomogeneity.chartQ, div_div] at he
  exact he

section PreparedRegularity

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)
  (hr0 : 0 < r0) (vr vt : TorusInverse.Plane)
  (M : ClosedMargins H v a vr vt)

include M

theorem prepared_strictCone (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hx : x ∈ radialInterior W) (hp : x.1 ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L)
    (hq : nativeQ F.data.h x ∈ Icc (1 / 2 : ℝ) 2) :
    SmoothCovariance.StrictCone
      (pulseMatrix (PrimaryGeometryAssembly.construction H v a hr0)
        (preparedPrefactor r0 vr vt) (ActualSignedGeometry.pulseCoordinates H v a) L x)
      (fun k => PrimaryTargetBounds.actualTarget v x.1 k) := by
  have hm := M.covariance L x.1 (reference_of_closed_band W hx hq) hp
  have hc := hm.strictCone
    (Real.sqrt_pos.mpr (zero_lt_one.trans_le ((PrimaryGeometryAssembly.domain W a.N).one_le_scale
        L)))
    M.lower_pos (radialInterior_spec W hx).2.2.2
  simp only [PrimaryTargetBounds.preparedCovariance_eq_construction H v a vr vt hr0,
    pulseMatrix, ActualSignedGeometry.pulseCoordinates] at hc ⊢
  exact hc

theorem baseVelocity_contDiffAt_closed (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x :
    Native}
    (hx : x ∈ radialInterior W) (hp : x.1 ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L)
    (hq : nativeQ F.data.h x ∈ Icc (1 / 2 : ℝ) 2)
    (hslot : (ActualSignedGeometry.pulseCoordinates H v a L x).2 ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (baseVelocity H v a hr0 vr vt j L) x := by
  have hd := radialInterior_spec W hx
  have ht := (actualTarget_contDiffAt v hd.1
    ((NominalConeAssembly.activeLeft_pos W).trans hd.2.2.1.1)).comp x contDiffAt_fst
  have htk (k : Fin 2) : ContDiffAt ℝ ∞ (fun y : Native => PrimaryTargetBounds.actualTarget v y.1
      k) x := by
    let Lk : MovingFrameODE.Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) k
    have hc := Lk.contDiff.contDiffAt.comp x ht
    exact hc
  have hmask := (PrimaryRepresentatives.nativeMask_smooth (PrimaryGeometryAssembly.label W L).1
    (PrimaryGeometryAssembly.label W L).2).contDiffAt.comp x contDiffAt_fst
  exact primaryVelocity_contDiffAt (PrimaryGeometryAssembly.construction H v a hr0)
    (preparedPrefactor r0 vr vt) (fun j => preparedPrefactor_jets r0 vr vt a.N j)
    (ActualSignedGeometry.pulseCoordinates H v a)
    (fun L => ChartScales.epsilon F.data.h (BaseChartJets.cellBand L))
    (fun _ x k => PrimaryTargetBounds.actualTarget v x.1 k)
    (fun L x => PrimaryRepresentatives.nativeMask (PrimaryGeometryAssembly.label W L).1
      (PrimaryGeometryAssembly.label W L).2 x.1) j L
    (coordinates_smooth H v a L).contDiffAt htk hmask hp hslot
    (prepared_strictCone H v a hr0 vr vt M L hx hp hq)

theorem basePressure_contDiffAt_closed (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x :
    Native}
    (hx : x ∈ radialInterior W) (hp : x.1 ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L)
    (hq : nativeQ F.data.h x ∈ Icc (1 / 2 : ℝ) 2)
    (hslot : (ActualSignedGeometry.pulseCoordinates H v a L x).2 ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (basePressure H v a hr0 vr vt j L) x :=
  phasePressure_contDiffAt (PrimaryGeometryAssembly.construction H v a hr0 j)
    (ActualSignedGeometry.pulseCoordinates H v a) _ (baseVelocity H v a hr0 vr vt j) L
    (coordinates_smooth H v a L).contDiffAt hp hslot
    (baseVelocity_contDiffAt_closed H v a hr0 vr vt M j L hx hp hq hslot)

theorem band_pair_contDiffAt_closed (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x :
    Native}
    (hx : x ∈ radialInterior W) (hp : x.1 ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L)
    (hq : nativeQ F.data.h x ∈ Icc (1 / 2 : ℝ) 2)
    (hslot : (ActualSignedGeometry.pulseCoordinates H v a L x).2 ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (bandVelocity H v a hr0 vr vt j L) x ∧
      ContDiffAt ℝ ∞ (bandPressure H v a hr0 vr vt j L) x := by
  have hf := outerFactor_contDiffAt H v a L (radialInterior_spec W hx).1
  exact ⟨hf.smul (baseVelocity_contDiffAt_closed H v a hr0 vr vt M j L hx hp hq hslot),
    hf.smul (basePressure_contDiffAt_closed H v a hr0 vr vt M j L hx hp hq hslot)⟩

end PreparedRegularity

section ZeroGerms

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem zero_germ_jets {f : D → E} {x : D} (h : f =ᶠ[𝓝 x] fun _ => 0) :
    ContDiffAt ℝ ∞ f x ∧ ∀ n, iteratedFDeriv ℝ n f x = 0 := by
  refine ⟨contDiffAt_const.congr_of_eventuallyEq h, ?_⟩
  intro n
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq h n, iteratedFDeriv_fun_zero]
  rfl

omit [NormedSpace ℝ D] in
theorem scalar_zero_germ {g : D → ℝ} (f : D → E) {x : D}
    (h : g =ᶠ[𝓝 x] fun _ => 0) : (fun y => g y • f y) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [h] with y hy
  simp only [hy, zero_smul]

omit [NormedSpace ℝ D] in
theorem vector_zero_germ (g : D → ℝ) {f : D → E} {x : D}
    (h : f =ᶠ[𝓝 x] fun _ => 0) : (fun y => g y • f y) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [h] with y hy
  simp only [hy, smul_zero]

end ZeroGerms

section PreparedGerms

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)
  (hr0 : 0 < r0) (vr vt : TorusInverse.Plane)

theorem baseVelocity_zero_germ (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hT : 0 < x.1.2.2) (hp : x.1 ∉ (PrimaryGeometryAssembly.domain W a.N).carrier L) :
    baseVelocity H v a hr0 vr vt j L =ᶠ[𝓝 x] fun _ => 0 := by
  have hz := (preparedMask_zero_germ L hT hp).comp_tendsto
    (show ContinuousAt (fun y : Native => y.1) x from continuousAt_fst)
  filter_upwards [hz] with y hy
  simp only [Function.comp_apply] at hy
  simp only [baseVelocity, primaryVelocity, PartitionedCovariance.amplitude,
    hy, mul_zero, zero_smul]

theorem basePressure_zero_germ (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hT : 0 < x.1.2.2) (hp : x.1 ∉ (PrimaryGeometryAssembly.domain W a.N).carrier L) :
    basePressure H v a hr0 vr vt j L =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [baseVelocity_zero_germ H v a hr0 vr vt j L hT hp] with y hy
  simp only [basePressure, phasePressure, ParticularWaveBounds.projectedPressure,
    TangentProjection.pressureCoefficient, hy, map_zero, inner_zero_right,
    sub_self, add_zero, zero_div, Complex.ofReal_zero, mul_zero]

theorem band_pair_zero_germ_cell (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hT : 0 < x.1.2.2) (hp : x.1 ∉ (PrimaryGeometryAssembly.domain W a.N).carrier L) :
    (bandVelocity H v a hr0 vr vt j L =ᶠ[𝓝 x] fun _ => 0) ∧
      (bandPressure H v a hr0 vr vt j L =ᶠ[𝓝 x] fun _ => 0) :=
  ⟨vector_zero_germ _ (baseVelocity_zero_germ H v a hr0 vr vt j L hT hp),
    vector_zero_germ _ (basePressure_zero_germ H v a hr0 vr vt j L hT hp)⟩

theorem factor_zero_germ_slot (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hslot : (ActualSignedGeometry.pulseCoordinates H v a L x).2 ∉ Ioo (0 : ℝ) 1) :
    outerFactor H v a L =ᶠ[𝓝 x] fun _ => 0 := by
  have hn : (ActualSignedGeometry.pulseCoordinates H v a L x).2 ∉ tsupport outerCutoff := by
    intro hs
    have hb := outerCutoff_support hs
    apply hslot
    constructor <;> linarith [hb.1, hb.2]
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (coordinates_smooth H v a L).continuous.continuousAt.snd
  filter_upwards [hz] with y hy
  simp only [Function.comp_apply, Pi.zero_apply] at hy
  simp only [outerFactor, hy, zero_mul]

theorem factor_zero_germ_band (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hT : 0 < x.1.2.2) (hq : nativeQ F.data.h x ∉ Icc (1 / 2 : ℝ) 2) :
    outerFactor H v a L =ᶠ[𝓝 x] fun _ => 0 := by
  have hn : nativeQ F.data.h x ∉ tsupport SquaredPartition.dyadicProfile := by
    rwa [SquaredPartition.dyadicProfile_tsupport]
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (nativeQ_contDiffAt F.data.h_pos F.data.h_lt_half hT).continuousAt
  filter_upwards [hz] with y hy
  simp only [Function.comp_apply, Pi.zero_apply] at hy
  simp only [outerFactor, hy, zero_mul, mul_zero]

include hr0 in
theorem factor_zero_germ_transverse (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hu : x.2.1 ∉ Icc (-r0) r0) : outerFactor H v a L =ᶠ[𝓝 x] fun _ => 0 := by
  have hn : x.2.1 ∉ tsupport (PartitionedCovariance.cutoff r0) := by
    simpa only [PartitionedCovariance.cutoff, SquaredPartition.gridMask_tsupport r0 hr0,
      Int.cast_zero, mul_zero, zero_sub, zero_add] using hu
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (show ContinuousAt (fun y : Native => y.2.1) x from continuousAt_snd.fst)
  filter_upwards [hz] with y hy
  simp only [Function.comp_apply, Pi.zero_apply] at hy
  simp only [outerFactor, hy, mul_zero]

theorem band_pair_zero_germ_factor (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x :
    Native}
    (hz : outerFactor H v a L =ᶠ[𝓝 x] fun _ => 0) :
    (bandVelocity H v a hr0 vr vt j L =ᶠ[𝓝 x] fun _ => 0) ∧
      (bandPressure H v a hr0 vr vt j L =ᶠ[𝓝 x] fun _ => 0) :=
  ⟨scalar_zero_germ _ hz, scalar_zero_germ _ hz⟩

theorem outerFactor_band_jets (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hT : 0 < x.1.2.2) (he : nativeQ F.data.h x = 1 / 2 ∨ nativeQ F.data.h x = 2)
    (n : ℕ) : iteratedFDeriv ℝ n (outerFactor H v a L) x = 0 := by
  have hq := nativeQ_contDiffAt F.data.h_pos F.data.h_lt_half hT
  have ho := outerCutoff_smooth.contDiffAt.comp x (coordinates_smooth H v a L).contDiffAt.snd
  have hu := (SquaredPartition.gridMask_smooth r0 0).contDiffAt.comp x contDiffAt_snd.fst
  have hz := (dyadic_product_endpoint hq (ho.mul hu) he).2 n
  convert! hz using 1
  congr 1
  funext y
  change _ = _ * (_ * _)
  dsimp only [outerFactor, Function.comp_apply, PartitionedCovariance.cutoff]
  ring

include hr0 in
theorem outerFactor_transverse_jets (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hT : 0 < x.1.2.2) (he : x.2.1 = -r0 ∨ x.2.1 = r0)
    (n : ℕ) : iteratedFDeriv ℝ n (outerFactor H v a L) x = 0 := by
  have ho := outerCutoff_smooth.contDiffAt.comp x (coordinates_smooth H v a L).contDiffAt.snd
  have hq := SquaredPartition.dyadicProfile_smooth.contDiffAt.comp x
    (nativeQ_contDiffAt F.data.h_pos F.data.h_lt_half hT)
  have hu := (SquaredPartition.gridMask_smooth r0 0).contDiffAt.comp x contDiffAt_snd.fst
  have hflat : ∀ k, iteratedFDeriv ℝ k (fun y : Native => PartitionedCovariance.cutoff r0 y.2.1) x
      = 0 := by
    intro k
    apply flat_comp_jets (SquaredPartition.gridMask_smooth r0 0) contDiffAt_snd.fst
    intro m
    rcases he with he | he
    · rw [he]; exact (transverse_endpoint_jets hr0 m).1
    · rw [he]; exact (transverse_endpoint_jets hr0 m).2
  have hz := flat_smul_jets hu (ho.mul hq) hflat n
  convert! hz using 1
  congr 1
  funext y
  change _ = _ * (_ * _)
  dsimp only [outerFactor, Function.comp_apply, PartitionedCovariance.cutoff]
  ring

end PreparedGerms

section FullBandRegularity

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)
  (hr0 : 0 < r0) (vr vt : TorusInverse.Plane)
  (M : ClosedMargins H v a vr vt)

include M

theorem band_pair_contDiffAt (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hx : x ∈ radialInterior W) :
    ContDiffAt ℝ ∞ (bandVelocity H v a hr0 vr vt j L) x ∧
      ContDiffAt ℝ ∞ (bandPressure H v a hr0 vr vt j L) x := by
  by_cases hp : x.1 ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L
  · by_cases ht : (ActualSignedGeometry.pulseCoordinates H v a L x).2 ∈ Ioo (0 : ℝ) 1
    · by_cases hq : nativeQ F.data.h x ∈ Icc (1 / 2 : ℝ) 2
      · exact band_pair_contDiffAt_closed H v a hr0 vr vt M j L hx hp hq ht
      · have hz := band_pair_zero_germ_factor H v a hr0 vr vt j L
          (factor_zero_germ_band H v a L hx.1 hq)
        exact ⟨(zero_germ_jets hz.1).1, (zero_germ_jets hz.2).1⟩
    · have hz := band_pair_zero_germ_factor H v a hr0 vr vt j L (factor_zero_germ_slot H v a L ht)
      exact ⟨(zero_germ_jets hz.1).1, (zero_germ_jets hz.2).1⟩
  · have hz := band_pair_zero_germ_cell H v a hr0 vr vt j L hx.1 hp
    exact ⟨(zero_germ_jets hz.1).1, (zero_germ_jets hz.2).1⟩

theorem band_pair_contDiffOn (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    ContDiffOn ℝ ∞ (bandVelocity H v a hr0 vr vt j L) (radialInterior W) ∧
      ContDiffOn ℝ ∞ (bandPressure H v a hr0 vr vt j L) (radialInterior W) :=
  ⟨fun _ hx => (band_pair_contDiffAt H v a hr0 vr vt M j L hx).1.contDiffWithinAt,
    fun _ hx => (band_pair_contDiffAt H v a hr0 vr vt M j L hx).2.contDiffWithinAt⟩

theorem band_pair_edge_jets_closed (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x :
    Native}
    (hx : x ∈ radialInterior W) (hp : x.1 ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L)
    (hq : nativeQ F.data.h x ∈ Icc (1 / 2 : ℝ) 2)
    (hslot : (ActualSignedGeometry.pulseCoordinates H v a L x).2 ∈ Ioo (0 : ℝ) 1)
    (he : (nativeQ F.data.h x = 1 / 2 ∨ nativeQ F.data.h x = 2) ∨ (x.2.1 = -r0 ∨ x.2.1 = r0))
    (n : ℕ) : iteratedFDeriv ℝ n (bandVelocity H v a hr0 vr vt j L) x = 0 ∧
      iteratedFDeriv ℝ n (bandPressure H v a hr0 vr vt j L) x = 0 := by
  have hflat : ∀ m, iteratedFDeriv ℝ m (outerFactor H v a L) x = 0 := by
    rcases he with hq | hu
    · exact outerFactor_band_jets H v a L hx.1 hq
    · exact outerFactor_transverse_jets H v a hr0 L hx.1 hu
  have hf := outerFactor_contDiffAt H v a L hx.1
  exact ⟨flat_smul_jets hf (baseVelocity_contDiffAt_closed H v a hr0 vr vt M j L hx hp hq hslot)
      hflat n,
    flat_smul_jets hf (basePressure_contDiffAt_closed H v a hr0 vr vt M j L hx hp hq hslot) hflat n⟩

end FullBandRegularity

section NativeCoverage

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)
  (hr0 : 0 < r0) (vr vt : TorusInverse.Plane)

include hr0 in
theorem native_mem_of_data (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hx : x ∈ radialInterior W) (hp : x.1 ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L)
    (hq : nativeQ F.data.h x ∈ Ioo (1 / 2 : ℝ) 2) (hu : x.2.1 ∈ Ioo (-r0) r0)
    (hslot : (ActualSignedGeometry.pulseCoordinates H v a L x).2 ∈ Ioo (0 : ℝ) 1) :
    x ∈ (ActualSignedGeometry.nativeDomain H v a).carrier L := by
  have hL : 0 < ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L) :=
    div_pos (mul_pos (by norm_num) hr0) (ChartScales.timeCoefficient_pos _ _)
  have hv : x.2.2 ∈ Ioo 0 (ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L)) := by
    exact ⟨by simpa only [zero_mul] using (lt_div_iff₀ hL).mp hslot.1,
      (div_lt_one hL).mp hslot.2⟩
  refine ⟨⟨hp, ?_⟩, hu, hv⟩
  apply (BaseContextAssembly.nativeStrip_mem W _ _).mpr
  exact ⟨⟨hx.1, hq⟩, hx.2⟩

theorem native_mem_band (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hx : x ∈ (ActualSignedGeometry.nativeDomain H v a).carrier L) :
    nativeQ F.data.h x ∈ Ioo (1 / 2 : ℝ) 2 :=
  ((BaseContextAssembly.nativeStrip_mem W _ _).mp hx.1.2).1.2

theorem band_pair_zero_jets_off_native (M : ClosedMargins H v a vr vt)
    (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hx : x ∈ radialInterior W)
    (hn : x ∉ (ActualSignedGeometry.nativeDomain H v a).carrier L) (n : ℕ) :
    iteratedFDeriv ℝ n (bandVelocity H v a hr0 vr vt j L) x = 0 ∧
      iteratedFDeriv ℝ n (bandPressure H v a hr0 vr vt j L) x = 0 := by
  by_cases hp : x.1 ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L
  · by_cases ht : (ActualSignedGeometry.pulseCoordinates H v a L x).2 ∈ Ioo (0 : ℝ) 1
    · by_cases hq : nativeQ F.data.h x ∈ Icc (1 / 2 : ℝ) 2
      · by_cases hu : x.2.1 ∈ Icc (-r0) r0
        · have he : (nativeQ F.data.h x = 1 / 2 ∨ nativeQ F.data.h x = 2) ∨
              (x.2.1 = -r0 ∨ x.2.1 = r0) := by
            by_cases hqi : nativeQ F.data.h x ∈ Ioo (1 / 2 : ℝ) 2
            · right
              have hui : x.2.1 ∉ Ioo (-r0) r0 :=
                fun hui => hn (native_mem_of_data H v a hr0 L hx hp hqi hui ht)
              rcases eq_or_lt_of_le hu.1 with he | hlt
              · exact Or.inl he.symm
              · exact Or.inr (le_antisymm hu.2 (not_lt.mp (fun hr => hui ⟨hlt, hr⟩)))
            · left
              rcases eq_or_lt_of_le hq.1 with he | hlt
              · exact Or.inl he.symm
              · exact Or.inr (le_antisymm hq.2 (not_lt.mp (fun hr => hqi ⟨hlt, hr⟩)))
          exact band_pair_edge_jets_closed H v a hr0 vr vt M j L hx hp hq ht he n
        · have hz := band_pair_zero_germ_factor H v a hr0 vr vt j L
            (factor_zero_germ_transverse H v a hr0 L hu)
          exact ⟨(zero_germ_jets hz.1).2 n, (zero_germ_jets hz.2).2 n⟩
      · have hz := band_pair_zero_germ_factor H v a hr0 vr vt j L
          (factor_zero_germ_band H v a L hx.1 hq)
        exact ⟨(zero_germ_jets hz.1).2 n, (zero_germ_jets hz.2).2 n⟩
    · have hz := band_pair_zero_germ_factor H v a hr0 vr vt j L (factor_zero_germ_slot H v a L ht)
      exact ⟨(zero_germ_jets hz.1).2 n, (zero_germ_jets hz.2).2 n⟩
  · have hz := band_pair_zero_germ_cell H v a hr0 vr vt j L hx.1 hp
    exact ⟨(zero_germ_jets hz.1).2 n, (zero_germ_jets hz.2).2 n⟩

theorem band_pair_band_edge_jets (M : ClosedMargins H v a vr vt)
    (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hx : x ∈ radialInterior W) (he : nativeQ F.data.h x = 1 / 2 ∨ nativeQ F.data.h x = 2) (n : ℕ) :
    iteratedFDeriv ℝ n (bandVelocity H v a hr0 vr vt j L) x = 0 ∧
      iteratedFDeriv ℝ n (bandPressure H v a hr0 vr vt j L) x = 0 := by
  apply band_pair_zero_jets_off_native H v a hr0 vr vt M j L hx _ n
  intro hi
  have hq := native_mem_band H v a L hi
  rcases he with he | he
  · rw [he] at hq
    exact (lt_irrefl _ hq.1)
  · rw [he] at hq
    exact (lt_irrefl _ hq.2)

/-- The full open radial domain, preserving the original native growth
function exactly and adding the flat band/transverse boundary points. -/
noncomputable def radialDomain : JetDomain (PrimaryGeometryAssembly.Index W a.N) Native where
  scale := (ActualSignedGeometry.nativeDomain H v a).scale
  carrier := fun _ => radialInterior W
  isOpen := fun _ => radialInterior_open W
  one_le_scale := (ActualSignedGeometry.nativeDomain H v a).one_le_scale
  growth := (ActualSignedGeometry.nativeDomain H v a).growth
  scale_le_growth L x _ := by
    exact (le_max_right 1 (ChartScales.S (BaseChartJets.cellBand L))).trans
      ((BaseContextAssembly.nativeStrip W
        (ActualSignedGeometry.standardSlowRegion F.data.h_pos F.data.h_lt_half)).slow_le_growth _ _)

theorem radialDomain_growth (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) :
    (radialDomain H v a).growth L x = BaseContextAssembly.slowScale (BaseChartJets.cellBand L) *
      WaveEdgeExtension.edgeGrowth (WaveEdgeExtension.nativeRadius F.data.h)
        (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) x := by
  change BaseContextAssembly.slowScale (BaseChartJets.cellBand L) *
    max 1 ((BaseContextAssembly.nativeStrip W
      (ActualSignedGeometry.standardSlowRegion F.data.h_pos F.data.h_lt_half)).delta
        (BaseContextAssembly.insertSlow x.1))⁻¹ = _
  unfold WaveEdgeExtension.edgeGrowth WaveEdgeExtension.logCoordinate WaveEdgeExtension.nativeRadius
    PrimaryTargetBounds.profileRadius
  rw [BaseChartJets.normalizedCoordinates_eq]
  rfl

end NativeCoverage

section UniformExtension

variable {ι : Type*} {D : Type} {E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Flat boundary points, unlike zero germs, can be covered by their
proved local smoothness and exact zero tensors. Uniform constants are unchanged. -/
theorem NativeJets.on_flat_cover {V V' : JetDomain ι D} {w : ι → D → ℝ} {f : ι → D → E}
    (hf : NativeJets V w f)
    (hcover : ∀ i x, x ∈ V'.carrier i → x ∈ V.carrier i ∨
      (ContDiffAt ℝ ∞ (f i) x ∧ ∀ n, iteratedFDeriv ℝ n (f i) x = 0))
    (hw : ∀ i x, x ∈ V'.carrier i → 0 ≤ w i x)
    (hG : ∀ i x, x ∈ V'.carrier i → x ∈ V.carrier i → V.growth i x ≤ V'.growth i x) :
    NativeJets V' w f := by
  refine ⟨hw, ?_, ?_⟩
  · intro i x hx
    rcases hcover i x hx with hi | hz
    · exact ((hf.smooth i).contDiffAt ((V.isOpen i).mem_nhds hi)).contDiffWithinAt
    · exact hz.1.contDiffWithinAt
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bound m
    refine ⟨C, hC, p, ?_⟩
    intro i x hx j hj
    rcases hcover i x hx with hi | hz
    · exact (hb i x hi j hj).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (V.one_le_growth i hi)) (hG i x hx hi) p)
          (zero_le_one.trans hC)) (hw i x hx))
    · rw [hz.2 j, norm_zero]
      exact mul_nonneg (mul_nonneg (zero_le_one.trans hC)
        (pow_nonneg (zero_le_one.trans (V'.one_le_growth i hx)) _)) (hw i x hx)

end UniformExtension

/-! ## Uniform bounds and the final radial attachment -/

section Attachment

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)
  (hr0 : 0 < r0) (vr vt : TorusInverse.Plane)

/-- Envelope, given by `pulseEnvelope (PrimaryGeometryAssembly.construction H v a hr0)
(ActualSignedGeometry.pulseCoordinates H v a) j`. -/
noncomputable def envelope (j : Fin 2) : PrimaryGeometryAssembly.Index W a.N → Native → ℝ :=
  pulseEnvelope (PrimaryGeometryAssembly.construction H v a hr0)
    (ActualSignedGeometry.pulseCoordinates H v a) j

/-- Velocity weight, constructed using `Real.sqrt`. -/
noncomputable def velocityWeight (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) (x : Native)
    : ℝ :=
  Real.sqrt (ChartScales.epsilon F.data.h (BaseChartJets.cellBand L)) *
    Real.sqrt (PrimaryTargetBounds.movingWeight W x.1) * envelope H v a hr0 j L x

/-- Pressure weight, constructed using `ChartScales.epsilon`. -/
noncomputable def pressureWeight (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) (x : Native)
    : ℝ :=
  ChartScales.epsilon F.data.h (BaseChartJets.cellBand L) *
    Real.sqrt (PrimaryTargetBounds.movingWeight W x.1) * envelope H v a hr0 j L x

theorem velocityWeight_nonneg (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) :
    0 ≤ velocityWeight H v a hr0 j L x := by
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (referenceP_pos _ _ _ _).le

theorem pressureWeight_nonneg (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) :
    0 ≤ pressureWeight H v a hr0 j L x := by
  exact mul_nonneg (mul_nonneg (ChartScales.epsilon_pos _ _).le (Real.sqrt_nonneg _))
    (referenceP_pos _ _ _ _).le

theorem bandVelocity_radial_jets (M : ClosedMargins H v a vr vt) (j : Fin 2)
    (hu : NativeJets (ActualSignedGeometry.nativeDomain H v a) (velocityWeight H v a hr0 j)
      (bandVelocity H v a hr0 vr vt j)) :
    NativeJets (radialDomain H v a) (velocityWeight H v a hr0 j) (bandVelocity H v a hr0 vr vt j)
        := by
  apply NativeJets.on_flat_cover (V' := radialDomain H v a) hu _ (fun L x _ =>
      velocityWeight_nonneg H v a hr0 j L x)
    (fun _ _ _ _ => le_rfl)
  intro L x hx
  by_cases hi : x ∈ (ActualSignedGeometry.nativeDomain H v a).carrier L
  · exact Or.inl hi
  · exact Or.inr ⟨(band_pair_contDiffAt H v a hr0 vr vt M j L hx).1,
      fun n => (band_pair_zero_jets_off_native H v a hr0 vr vt M j L hx hi n).1⟩

theorem bandPressure_radial_jets (M : ClosedMargins H v a vr vt) (j : Fin 2)
    (hp : NativeJets (ActualSignedGeometry.nativeDomain H v a) (pressureWeight H v a hr0 j)
      (bandPressure H v a hr0 vr vt j)) :
    NativeJets (radialDomain H v a) (pressureWeight H v a hr0 j) (bandPressure H v a hr0 vr vt j)
        := by
  apply NativeJets.on_flat_cover (V' := radialDomain H v a) hp _ (fun L x _ =>
      pressureWeight_nonneg H v a hr0 j L x)
    (fun _ _ _ _ => le_rfl)
  intro L x hx
  by_cases hi : x ∈ (ActualSignedGeometry.nativeDomain H v a).carrier L
  · exact Or.inl hi
  · exact Or.inr ⟨(band_pair_contDiffAt H v a hr0 vr vt M j L hx).2,
      fun n => (band_pair_zero_jets_off_native H v a hr0 vr vt M j L hx hi n).2⟩

/-- After filling the flat band boundary, the radial attachment theorem
applies at both radial edges, including their intersections with band edges. -/
theorem band_pair_native_regular (M : ClosedMargins H v a vr vt) (j : Fin 2)
    (hu : NativeJets (ActualSignedGeometry.nativeDomain H v a) (velocityWeight H v a hr0 j)
      (bandVelocity H v a hr0 vr vt j))
    (hp : NativeJets (ActualSignedGeometry.nativeDomain H v a) (pressureWeight H v a hr0 j)
      (bandPressure H v a hr0 vr vt j)) :
    ∀ L, WaveEdgeExtension.NativeRegularity W (bandVelocity H v a hr0 vr vt j L) ∧
      WaveEdgeExtension.NativeRegularity W (bandPressure H v a hr0 vr vt j L) := by
  have henv := WaveEdgeExtension.pulseEnvelope_continuousOn
    (PrimaryGeometryAssembly.construction H v a hr0) (ActualSignedGeometry.pulseCoordinates H v a)
    (fun L => (coordinates_smooth H v a L).continuous.continuousOn.snd) j
  have henv0 : ∀ L x, x ∈ WaveEdgeExtension.nativeSlowDomain → 0 ≤ envelope H v a hr0 j L x :=
    fun _ _ _ => (referenceP_pos _ _ _ _).le
  have hG : ∀ L x, x ∈ radialInterior W → (radialDomain H v a).growth L x ≤
      BaseContextAssembly.slowScale (BaseChartJets.cellBand L) *
        WaveEdgeExtension.edgeGrowth (WaveEdgeExtension.nativeRadius F.data.h)
          (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) x ^ 1 := by
    intro L x _
    rw [pow_one, radialDomain_growth]
  have hu' := WaveEdgeExtension.NativeJets.native_zero_extension W
    (bandVelocity_radial_jets H v a hr0 vr vt M j hu)
    (fun L => Real.sqrt_nonneg (ChartScales.epsilon F.data.h (BaseChartJets.cellBand L)))
    (fun L => BaseContextAssembly.one_le_slowScale (BaseChartJets.cellBand L)) henv henv0
    (fun _ => Subset.rfl) 1 hG
  have hp' := WaveEdgeExtension.NativeJets.native_zero_extension W
    (bandPressure_radial_jets H v a hr0 vr vt M j hp)
    (fun L => (ChartScales.epsilon_pos F.data.h (BaseChartJets.cellBand L)).le)
    (fun L => BaseContextAssembly.one_le_slowScale (BaseChartJets.cellBand L)) henv henv0
    (fun _ => Subset.rfl) 1 hG
  intro L
  exact ⟨⟨(hu' L).1, (hu' L).2.1, (hu' L).2.2⟩, ⟨(hp' L).1, (hp' L).2.1, (hp' L).2.2⟩⟩

/-- Pre outer velocity, given by `(SquaredPartition.dyadicProfile (nativeQ F.data.h x) *
PartitionedCovariance.cutoff r0 x.2.1) • baseVelocity H v a hr0 vr vt j L x`. -/
noncomputable def preOuterVelocity (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    (x : Native) : ProblemStatement.Space :=
  (SquaredPartition.dyadicProfile (nativeQ F.data.h x) * PartitionedCovariance.cutoff r0 x.2.1) •
    baseVelocity H v a hr0 vr vt j L x

/-- Pre outer pressure, given by `(SquaredPartition.dyadicProfile (nativeQ F.data.h x) *
PartitionedCovariance.cutoff r0 x.2.1) • basePressure H v a hr0 vr vt j L x`. -/
noncomputable def preOuterPressure (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    (x : Native) : ℂ :=
  (SquaredPartition.dyadicProfile (nativeQ F.data.h x) * PartitionedCovariance.cutoff r0 x.2.1) •
    basePressure H v a hr0 vr vt j L x

theorem preOuterPressure_eq_phasePressure (j : Fin 2)
    (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) :
    preOuterPressure H v a hr0 vr vt j L x =
      phasePressure (PrimaryGeometryAssembly.construction H v a hr0 j)
        (ActualSignedGeometry.pulseCoordinates H v a)
        (fun L => (ChartScales.carrier F.data.h (BaseChartJets.cellBand L) : ℝ))
        (preOuterVelocity H v a hr0 vr vt j) L x :=
  (phasePressure_smul _ _ _
    (fun _ y => SquaredPartition.dyadicProfile (nativeQ F.data.h y) * PartitionedCovariance.cutoff
        r0 y.2.1)
    (baseVelocity H v a hr0 vr vt j) L x).symm

theorem bandVelocity_eq_outer (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) :
    bandVelocity H v a hr0 vr vt j L x =
      outerCutoff (ActualSignedGeometry.pulseCoordinates H v a L x).2 •
        preOuterVelocity H v a hr0 vr vt j L x := by
  simp only [bandVelocity, outerFactor, preOuterVelocity, smul_smul]

theorem bandPressure_eq_outer (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) :
    bandPressure H v a hr0 vr vt j L x =
      outerCutoff (ActualSignedGeometry.pulseCoordinates H v a L x).2 •
        preOuterPressure H v a hr0 vr vt j L x := by
  simp only [bandPressure, outerFactor, preOuterPressure, smul_smul]

/-- Applying the intended Gaussian after attachment still applies that
Gaussian exactly once: the outer slot cutoff is one on its support. -/
theorem gaussian_bandVelocity (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) :
    GaussianTailFlat.profile (ActualSignedGeometry.pulseCoordinates H v a L x).2 •
      bandVelocity H v a hr0 vr vt j L x =
    GaussianTailFlat.profile (ActualSignedGeometry.pulseCoordinates H v a L x).2 •
      preOuterVelocity H v a hr0 vr vt j L x := by
  rw [bandVelocity_eq_outer, smul_smul, profile_mul_outerCutoff]

theorem gaussian_bandPressure (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) (x : Native) :
    GaussianTailFlat.profile (ActualSignedGeometry.pulseCoordinates H v a L x).2 •
      bandPressure H v a hr0 vr vt j L x =
    GaussianTailFlat.profile (ActualSignedGeometry.pulseCoordinates H v a L x).2 •
      preOuterPressure H v a hr0 vr vt j L x := by
  rw [bandPressure_eq_outer, smul_smul, profile_mul_outerCutoff]

include hr0 in
theorem outerCutoff_native_polynomial :
    PolynomialJets (ActualSignedGeometry.nativeDomain H v a).toDomain
      (fun L x => outerCutoff (ActualSignedGeometry.pulseCoordinates H v a L x).2) := by
  let c := ActualSignedGeometry.preparedChart H v a hr0
  have hτ := c.coordinate_jets.clm (ContinuousLinearMap.snd ℝ Slow ℝ)
  apply hτ.compact_comp isOpen_univ outerCutoff_smooth.contDiffOn
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)) (subset_univ _)
  intro L x hx
  exact ⟨(c.maps L x hx).2.1.le, (c.maps L x hx).2.2.le⟩

/-- The endpoint consumed by the actual initialization: only the already
proved raw interior jet estimates and the fixed family's closed margins enter.
The outer time cutoff and all boundary regularity are derived here. -/
theorem band_pair_native_regular_of_raw_jets (M : ClosedMargins H v a vr vt) (j : Fin 2)
    (hu : NativeJets (ActualSignedGeometry.nativeDomain H v a) (velocityWeight H v a hr0 j)
      (preOuterVelocity H v a hr0 vr vt j))
    (hp : NativeJets (ActualSignedGeometry.nativeDomain H v a) (pressureWeight H v a hr0 j)
      (preOuterPressure H v a hr0 vr vt j)) :
    ∀ L, WaveEdgeExtension.NativeRegularity W (bandVelocity H v a hr0 vr vt j L) ∧
      WaveEdgeExtension.NativeRegularity W (bandPressure H v a hr0 vr vt j L) := by
  apply band_pair_native_regular H v a hr0 vr vt M j
  · exact (hu.polynomial_smul (outerCutoff_native_polynomial H v a hr0)).congr
      (fun L x _ => (bandVelocity_eq_outer H v a hr0 vr vt j L x).symm)
  · exact (hp.polynomial_smul (outerCutoff_native_polynomial H v a hr0)).congr
      (fun L x _ => (bandPressure_eq_outer H v a hr0 vr vt j L x).symm)

/-- The band boundary tensors remain zero after the radial attachment,
including the intersections of the band and radial boundaries. -/
theorem attached_pair_band_edge_jets (M : ClosedMargins H v a vr vt) (j : Fin 2)
    (hu : NativeJets (ActualSignedGeometry.nativeDomain H v a) (velocityWeight H v a hr0 j)
      (preOuterVelocity H v a hr0 vr vt j))
    (hp : NativeJets (ActualSignedGeometry.nativeDomain H v a) (pressureWeight H v a hr0 j)
      (preOuterPressure H v a hr0 vr vt j))
    (L : PrimaryGeometryAssembly.Index W a.N) {x : Native}
    (hT : 0 < x.1.2.2) (he : nativeQ F.data.h x = 1 / 2 ∨ nativeQ F.data.h x = 2) (n : ℕ) :
    iteratedFDeriv ℝ n (WaveEdgeExtension.nativeExtension W (bandVelocity H v a hr0 vr vt j L)) x =
        0 ∧
      iteratedFDeriv ℝ n (WaveEdgeExtension.nativeExtension W (bandPressure H v a hr0 vr vt j L)) x
          = 0 := by
  obtain ⟨hv, hp'⟩ := band_pair_native_regular_of_raw_jets H v a hr0 vr vt M j hu hp L
  by_cases hi : WaveEdgeExtension.nativeRadius F.data.h x ∈
      Ioo (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)
  · rw [hv.jet_inside n hT hi, hp'.jet_inside n hT hi]
    exact band_pair_band_edge_jets H v a hr0 vr vt M j L ⟨hT, hi⟩ he n
  · exact ⟨hv.jet_outside n hT hi, hp'.jet_outside n hT hi⟩

end Attachment

end NavierStokes.NativeBandExtension
