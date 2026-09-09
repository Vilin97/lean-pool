/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalRankDefect
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryResidualClass
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryMaterialDefect
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualTZ
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryTargetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseRadialJets
import LeanPool.NavierStokesAndEuler.NavierStokes.AllBandBaseJets

/-!
# The correction context of the actual slow base

The native slow order is `(T,Z)`. The explicit linear map `slowCoordinates`
converts to the `(R,(Z,T))` order used by the physical base charts. Every
field below uses one fixed final profile, coefficient family, and schedule.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.BaseContextAssembly

open Set Function Filter WeightedClasses
open scoped ContDiff Topology BigOperators EuclideanSpace

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

/-- Common index, given by `ChartScales.nativeIndex h n`. -/
noncomputable def commonIndex (h : ℝ) (n : ℕ) : ℕ := ChartScales.nativeIndex h n

/-- Slow scale, given by `max 1 (ChartScales.S n)`. -/
noncomputable def slowScale (n : ℕ) : ℝ := max 1 (ChartScales.S n)

theorem one_le_slowScale (n : ℕ) : 1 ≤ slowScale n := le_max_left _ _

/-- Reconstruction, bundling `exponent`, `inner`, `outer`, `inner_lt_outer` and the required
compatibility proofs. -/
noncomputable def reconstruction (h a b : ℝ) (hab : a < b) : CorrectionState.ReconstructionData
    where
  exponent := ChartScales.radialExponent h
  inner := a
  outer := b
  inner_lt_outer := hab
  frequency n := ChartScales.Lambda ^ commonIndex h n *
    ChartScales.Q n ^ (ChartScales.radialExponent h / 2)
  radialDirection := TorusInverse.vector .radial

/-- Operators, constructed using `CorrectionState.graphOperators`. -/
noncomputable def operators (h a b : ℝ) (hab : a < b) : MeanIncrementBounds.Operators Point :=
  CorrectionState.graphOperators (reconstruction h a b hab) (ChartScales.epsilon h)
    (fun n => ChartScales.Tg ^ commonIndex h n * ChartScales.Q n ^ (1 + h))
    ((0, 1), 0) ((1, 0), 0) (TorusInverse.vector .temporal)

@[simp] theorem operators_epsilon (h a b : ℝ) (hab : a < b) :
    (operators h a b hab).epsilon = ChartScales.epsilon h := rfl

@[simp] theorem operators_radialFrequency (h a b : ℝ) (hab : a < b) :
    (operators h a b hab).radialFrequency = ChartScales.radialCoefficient h := rfl

@[simp] theorem operators_fastCoefficient (h a b : ℝ) (hab : a < b) :
    (operators h a b hab).fastCoefficient = ChartScales.timeCoefficient h := rfl

@[simp] theorem operators_radius (h a b : ℝ) (hab : a < b) :
    (operators h a b hab).radius = Prod.fst := rfl

/-- The actual fixed `TZ -> ZT` permutation, discarding auxiliary variables. -/
noncomputable def slowCoordinates : Point →L[ℝ] Slow where
  toFun x := (x.1, (x.2.1.2, x.2.1.1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.prodMk (continuous_snd.fst.snd.prodMk continuous_snd.fst.fst)

@[simp] theorem slowCoordinates_apply (x : Point) :
    slowCoordinates x = (x.1, (x.2.1.2, x.2.1.1)) := rfl

theorem slowCoordinates_norm_le : ‖slowCoordinates‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [slowCoordinates_apply, one_mul, Prod.norm_def]
  exact max_le_max le_rfl ((max_comm _ _).le.trans (le_max_left _ _))

/-- Physical point, given by `BaseChartJets.bandPoint h (ChartScales.Q n) (slowCoordinates x)`. -/
noncomputable def physicalPoint (h : ℝ) (n : ℕ) (x : Point) : ProblemStatement.SpaceTime :=
  BaseChartJets.bandPoint h (ChartScales.Q n) (slowCoordinates x)

theorem physicalPoint_time (h : ℝ) (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    (physicalPoint h n x).1 < 1 := BaseChartJets.bandPoint_time (ChartScales.Q_pos n) hT

theorem physicalPoint_smooth (h : ℝ) (n : ℕ) : ContDiff ℝ ∞ (physicalPoint h n) := by
  change ContDiff ℝ ∞ (fun x : Point =>
    (1 - ChartScales.Q n * x.2.1.1,
      !₂[Real.sqrt (ChartScales.Q n) * x.1, 0,
        ChartScales.Q n ^ CoordinateAlgebra.D h * x.2.1.2]))
  apply ContDiff.prodMk
  · exact contDiff_const.sub (contDiff_const.mul contDiff_snd.fst.fst)
  · apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun x : Point => Real.sqrt (ChartScales.Q n) * x.1)
      exact contDiff_const.mul contDiff_fst
    · change ContDiff ℝ ∞ (fun _ : Point => (0 : ℝ))
      exact contDiff_const
    · change ContDiff ℝ ∞ (fun x : Point => ChartScales.Q n ^ CoordinateAlgebra.D h * x.2.1.2)
      exact contDiff_const.mul contDiff_snd.fst.snd

theorem operators_match_physical (h a b : ℝ) (hab : a < b) (n : ℕ) :
    PhysicalResidualTZ.MatchesAtTZ (operators h a b hab)
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (commonIndex h n)) n := by
  constructor <;> rfl

section OperatorBounds

theorem timeCoefficient_uniform (h : ℝ) (hh : 0 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n, ‖ChartScales.timeCoefficient h n‖ ≤ C := by
  let C := 1 + ∑ i ∈ Finset.range 4, ‖ChartScales.timeCoefficient h i‖
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : n < 4
  · have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range 4) =>
      norm_nonneg (ChartScales.timeCoefficient h i)) (Finset.mem_range.mpr hn)
    exact hs.trans (by dsimp [C]; linarith)
  · have hSn : 1 ≤ ChartScales.S n := by
      have hn' : (4 : ℝ) ≤ n := by exact_mod_cast (le_of_not_gt hn)
      dsimp [ChartScales.S]
      nlinarith
    have ht := (ChartScales.timeCoefficient_bounds h hh (le_of_not_gt hn)).2
    rw [Real.norm_eq_abs, abs_of_pos (ChartScales.timeCoefficient_pos h n)]
    exact ht.trans ((one_div_le_one_div_of_le zero_lt_one hSn).trans (by simpa using hC))

theorem radialCoefficient_uniform (h : ℝ) (hh : 0 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n, ‖ChartScales.radialCoefficient h n‖ ≤
      C * ChartScales.epsilon h n ^ (-ChartScales.kappa) := by
  let C := 1 + ∑ i ∈ Finset.range 4, ‖ChartScales.radialCoefficient h i‖
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hpow (n : ℕ) : 1 ≤ ChartScales.epsilon h n ^ (-ChartScales.kappa) := by
    have he := Real.rpow_le_rpow_of_exponent_ge (ChartScales.epsilon_pos h n)
      (ChartScales.epsilon_le_one h hh n) (show -ChartScales.kappa ≤ (0 : ℝ) by
        norm_num [ChartScales.kappa])
    simpa only [Real.rpow_zero] using he
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : n < 4
  · have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range 4) =>
      norm_nonneg (ChartScales.radialCoefficient h i)) (Finset.mem_range.mpr hn)
    exact (hs.trans (by dsimp [C]; linarith)).trans
      (le_mul_of_one_le_right (zero_le_one.trans hC) (hpow n))
  · have hSn : 1 ≤ ChartScales.S n := by
      have hn' : (4 : ℝ) ≤ n := by exact_mod_cast (le_of_not_gt hn)
      dsimp [ChartScales.S]
      nlinarith
    have ht : ChartScales.timeCoefficient h n ≤ 1 :=
      ((ChartScales.timeCoefficient_bounds h hh (le_of_not_gt hn)).2).trans
        (by simpa using one_div_le_one_div_of_le zero_lt_one hSn)
    rw [Real.norm_eq_abs, abs_of_pos (ChartScales.radialCoefficient_pos h n),
      ChartScales.radialCoefficient_eq]
    exact (mul_le_of_le_one_right (Real.rpow_nonneg (ChartScales.epsilon_pos h n).le _)
      (Real.rpow_le_one (ChartScales.timeCoefficient_pos h n).le ht ChartScales.rho_pos.le)).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg (ChartScales.epsilon_pos h n).le _) hC)

/-- Moving strip, constructed using `LocalSignedRequest.movingStripData`. -/
noncomputable def movingStrip {h : ℝ} (hh : 0 ≤ h) (U : LocalSignedRequest.SlowRegion (2 * h))
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR) : StripData Point :=
  LocalSignedRequest.movingStripData U a b cL cR ha hcL hcR
    (ChartScales.epsilon h) slowScale (ChartScales.epsilon_pos h)
    (ChartScales.epsilon_le_one h hh) one_le_slowScale

theorem radial_unweighted {s : StripData Point} {a b : ℝ}
    (hr : ∀ x ∈ s.domain, x.1 ∈ Icc a b) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    UnweightedClass s 0 (fun _ x => g x.1) := by
  apply unweighted_of_finiteJetBounds _ _ (hg.comp contDiff_fst).contDiffOn
  intro m
  obtain ⟨C, _, hC⟩ := WeightedRadialPrimitive.cutoff_finiteJet_bound
    (E := Plane × Plane) a b g hg m
  exact ⟨C, fun j hj x hx => hC j hj x (hr x hx)⟩

theorem positive_radial_unweighted {s : StripData Point} {a b : ℝ} (ha : 0 < a)
    (hr : ∀ x ∈ s.domain, x.1 ∈ Icc a b) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) : UnweightedClass s 0 (fun _ x => g x.1) := by
  let ext : ℝ → ℝ := g ∘ TerminalEdgeFactor.positiveExtension a
  have hext : ContDiff ℝ ∞ ext := by
    apply contDiffOn_univ.mp
    exact hg.comp (TerminalEdgeFactor.positiveExtension_contDiff a).contDiffOn
      (fun x _ => TerminalEdgeFactor.positiveExtension_pos ha x)
  apply MeanIncrementBounds.class_congr (radial_unweighted hr hext)
  intro n x hx
  dsimp [ext]
  rw [TerminalEdgeFactor.positiveExtension_eq ha (hr x hx).1]

theorem movingStrip_radial_bounds {h : ℝ} (hh : 0 ≤ h)
    (U : LocalSignedRequest.SlowRegion (2 * h))
    (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    {x : Point} (hx : x ∈ (movingStrip hh U a b cL cR ha hcL hcR).domain) :
    x.1 ∈ Icc (Real.sqrt U.qlo * a) (Real.sqrt U.qhi * b) :=
  LocalSignedRequest.moving_radial_bounds U ha hx.1 hx.2.1

theorem operators_local {h a b : ℝ} (hab : a < b) (U : Set Plane) :
    LocalRankDefect.LocalOperators U (operators h a b hab) := by
  refine ⟨rfl, ?_⟩
  intro x hx
  change ContDiffWithinAt ℝ ∞ (fun y : Point =>
    ChartScales.radialExponent h * y.1 ^ (ChartScales.radialExponent h - 1)) _ x
  exact (contDiffAt_const.mul (contDiffAt_fst.rpow_const_of_ne hx.1.ne')).contDiffWithinAt

theorem operator_bounds {h : ℝ} (hh : 0 ≤ h) (U : LocalSignedRequest.SlowRegion (2 * h))
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR) :
    MeanIncrementBounds.OperatorBounds (movingStrip hh U a b cL cR ha hcL hcR)
      (operators h a b hab) ChartScales.kappa := by
  let s := movingStrip hh U a b cL cR ha hcL hcR
  have hmin : 0 < Real.sqrt U.qlo * a := mul_pos (Real.sqrt_pos.mpr U.qlo_pos) ha
  have hr : ∀ x ∈ s.domain, x.1 ∈ Icc (Real.sqrt U.qlo * a) (Real.sqrt U.qhi * b) :=
    fun _ hx => movingStrip_radial_bounds hh U a b cL cR ha hcL hcR hx
  refine ⟨rfl, ?_, ?_, ?_, ?_, by norm_num [ChartScales.kappa], ?_⟩
  · change UnweightedClass s 0 (fun _ x => RadialPullback.radialJacobian
      (ChartScales.radialExponent h) x.1)
    apply positive_radial_unweighted hmin hr
    intro x hx
    exact (contDiffAt_const.mul (contDiffAt_id.rpow_const_of_ne hx.ne')).contDiffWithinAt
  · apply positive_radial_unweighted hmin hr
    exact contDiffOn_id.inv (fun x hx => hx.ne')
  · obtain ⟨C, hC, hb⟩ := radialCoefficient_uniform h hh
    refine ⟨C, zero_le_one.trans hC, 0, fun n => ?_⟩
    simp only [pow_zero, mul_one]
    exact hb n
  · obtain ⟨C, hC, hb⟩ := timeCoefficient_uniform h hh
    refine ⟨C, zero_le_one.trans hC, 0, fun n => ?_⟩
    simp only [Real.rpow_zero, pow_zero, mul_one]
    exact hb n
  · intro x hx
    change WeightedRadialPrimitive.zeta cL cR _ _ ≤ 1
    unfold WeightedRadialPrimitive.zeta
    exact (mul_le_mul (WeightedRadialPrimitive.edge_le_one hcL.le _)
      (WeightedRadialPrimitive.edge_le_one hcR.le _) (FlatCutoff.edge_nonneg _ _)
          zero_le_one).trans_eq (by
          simp)

end OperatorBounds

section NativeGeometry

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

/-- Native strip, constructed using `movingStrip`. -/
noncomputable def nativeStrip (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) : StripData Point
    :=
  movingStrip F.data.h_pos.le U (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius
      W)
    (FinalSlowBase.edgeExponent W / 4) 1 (PrimaryTargetBounds.leftRadius_pos W)
    (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num)) zero_lt_one

theorem nativeStrip_mem (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (x : Point) :
    x ∈ (nativeStrip W U).domain ↔ x.2.1 ∈ U.carrier ∧
      PrimaryTargetBounds.profileRadius F.data.h (slowCoordinates x) ∈
        Ioo (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) := by
  rw [nativeStrip, movingStrip, LocalSignedRequest.movingStrip_domain]
  rw [PrimaryTargetBounds.profileRadius]
  change (_ ∧ _) ↔ (_ ∧ x.1 / Real.sqrt
    (BaseChartJets.normalizedCoordinates F.data.h (PrimaryTargetBounds.meanPoint x)).1 ∈ _)
  rw [PrimaryTargetBounds.meanPoint_scalar]
  rfl

theorem nativeStrip_radius (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {x : Point} (hx : x ∈ (nativeStrip W U).domain) : 0 < x.1 := by
  have hr := movingStrip_radial_bounds F.data.h_pos.le U _ _ _ _
    (PrimaryTargetBounds.leftRadius_pos W)
    (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num)) zero_lt_one hx
  exact (mul_pos (Real.sqrt_pos.mpr U.qlo_pos) (PrimaryTargetBounds.leftRadius_pos W)).trans_le hr.1

theorem nativeStrip_time (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {x : Point} (hx : x ∈ (nativeStrip W U).domain) : 0 < x.2.1.1 :=
  U.time_pos _ ((nativeStrip_mem W U x).mp hx).1

theorem nativeStrip_active (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {x : Point} (hx : x ∈ (nativeStrip W U).domain) :
    (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2 ∈ FinalSlowBase.annulus W
        := by
  have hT := nativeStrip_time W U hx
  have hr := ((nativeStrip_mem W U x).mp hx).2
  have hpos := PrimaryTargetBounds.profileRadius_pos (F := F) (p := slowCoordinates x)
    hT (nativeStrip_radius W U hx)
  have he := PrimaryTargetBounds.profileRadius_sq (F := F) (p := slowCoordinates x) hT
  have ha : (PrimaryTargetBounds.leftRadius W)^2 = 2 * NominalConeAssembly.activeLeft W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)
  have hb : (PrimaryTargetBounds.rightRadius W)^2 = 2 * NominalConeAssembly.activeRight W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W).le)
  have hls := sq_lt_sq' (by linarith [PrimaryTargetBounds.leftRadius_pos W]) hr.1
  have hrs := sq_lt_sq' (by linarith [PrimaryTargetBounds.rightRadius_pos W]) hr.2
  have heta := BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half
    (p := slowCoordinates x) hT
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · nlinarith
  · nlinarith
  · exact ⟨(abs_lt.mp heta).1.le, (abs_lt.mp heta).2.le⟩

theorem nativeStrip_weight (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {x : Point} (hx : x ∈ (nativeStrip W U).domain) :
    (nativeStrip W U).zeta x = FinalSlowBase.weight W
      (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2 := by
  change (LocalSignedRequest.movingStripData U _ _ _ _ _ _ _ _ _ _ _ _).zeta x = _
  rw [PrimaryTargetBounds.movingStripData_zeta]
  exact PrimaryTargetBounds.movingWeight_eq W (nativeStrip_time W U hx) (nativeStrip_radius W U hx)

/-- Insert zero auxiliary variables, retaining the explicit coordinate order. -/
noncomputable def insertSlow : Slow →L[ℝ] Point where
  toFun p := (p.1, ((p.2.2, p.2.1), 0))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  cont := continuous_fst.prodMk ((continuous_snd.snd.prodMk continuous_snd.fst).prodMk
      continuous_const)

theorem slowCoordinates_insert (p : Slow) : slowCoordinates (insertSlow p) = p := rfl

/-- Slow carrier, given by `insertSlow ⁻¹' (nativeStrip W U).domain`. -/
noncomputable def slowCarrier (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) : Set Slow :=
  insertSlow ⁻¹' (nativeStrip W U).domain

theorem slowCarrier_open (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    IsOpen (slowCarrier W U) := (nativeStrip W U).isOpen_domain.preimage insertSlow.continuous

/-- Phase domain, given by `BaseChartJets.oneDomain ι (fun _ => slowCarrier W U) (fun _ =>
slowCarrier_open W U)`. -/
noncomputable def phaseDomain (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    (ι : Type*) : PhaseJetBounds.Domain ι Slow :=
  BaseChartJets.oneDomain ι (fun _ => slowCarrier W U) (fun _ => slowCarrier_open W U)

theorem slowCoordinates_maps (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    MapsTo slowCoordinates (nativeStrip W U).domain (slowCarrier W U) := by
  intro x hx
  apply (nativeStrip_mem W U _).mpr
  exact (nativeStrip_mem W U x).mp hx

/-- Geometry radius, given by `Real.sqrt U.qlo * PrimaryTargetBounds.leftRadius W`. -/
noncomputable def geometryRadius (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) : ℝ :=
  Real.sqrt U.qlo * PrimaryTargetBounds.leftRadius W

/-- Geometry upper, given by `max 1 U.qhi + 1`. -/
noncomputable def geometryUpper (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) : ℝ :=
  max 1 U.qhi + 1

/-- Geometry bound, constructed using `max`. -/
noncomputable def geometryBound (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) : ℝ :=
  max 1 (max (Real.sqrt (max 1 U.qhi) * PrimaryTargetBounds.rightRadius W)
    (max ((max 1 U.qhi) ^ CoordinateAlgebra.D F.data.h) (max 1 U.qhi)))

theorem geometryRadius_pos (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    0 < geometryRadius W U := mul_pos (Real.sqrt_pos.mpr U.qlo_pos)
        (PrimaryTargetBounds.leftRadius_pos W)

theorem geometryUpper_pos (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    0 < geometryUpper U := by dsimp [geometryUpper]; linarith [le_max_left (1 : ℝ) U.qhi]

theorem one_le_geometryBound (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    1 ≤ geometryBound W U := le_max_left _ _

theorem native_geometry (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (ι : Type*) :
    BaseChartJets.GeometryBounds (phaseDomain W U ι) F.data.h (geometryRadius W U)
      (geometryBound W U) (U.qlo / 2) (geometryUpper U)
      (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) := by
  have hT {p : Slow} (hp : p ∈ slowCarrier W U) : 0 < p.2.2 := nativeStrip_time W U hp
  have hqm {p : Slow} (hp : p ∈ slowCarrier W U) :
      (BaseChartJets.normalizedCoordinates F.data.h p).1 ∈ Icc U.qlo U.qhi := by
    rw [BaseChartJets.normalizedCoordinates_eq]
    exact U.q_mem _ ((nativeStrip_mem W U _).mp hp).1
  have hr {p : Slow} (hp : p ∈ slowCarrier W U) :
      p.1 ∈ Icc (geometryRadius W U) (Real.sqrt U.qhi * PrimaryTargetBounds.rightRadius W) :=
    movingStrip_radial_bounds F.data.h_pos.le U _ _ _ _ (PrimaryTargetBounds.leftRadius_pos W)
      (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num)) zero_lt_one hp
  refine ⟨fun _ _ hp => hT hp, fun _ _ hp => (hr hp).1, ?_, ?_, ?_⟩
  · intro i p hp
    have ht := hT hp
    have hq := hqm hp
    have hqp := U.qlo_pos.trans_le hq.1
    have hqM := hq.2.trans (le_max_right (1 : ℝ) U.qhi)
    rw [BaseChartJets.normalizedCoordinates_eq] at hqp hqM
    have hD : 0 ≤ CoordinateAlgebra.D F.data.h := by
      unfold CoordinateAlgebra.D; linarith [F.data.h_lt_half]
    have heta := BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half ht
    rw [BaseChartJets.normalizedCoordinates_eq] at heta
    change |p.2.1 / SimilarityHomogeneity.chartQ F.data.h p ^ ((1-2*F.data.h)/2)| < 1 at heta
    have hd : (1 - 2 * F.data.h) / 2 = CoordinateAlgebra.D F.data.h := by
      unfold CoordinateAlgebra.D; ring
    rw [hd, abs_div, abs_of_pos (Real.rpow_pos_of_pos hqp _), div_lt_one (Real.rpow_pos_of_pos hqp
        _)] at heta
    have hz : |p.2.1| ≤ (max 1 U.qhi) ^ CoordinateAlgebra.D F.data.h :=
      heta.le.trans (Real.rpow_le_rpow hqp.le hqM hD)
    have hspec := SimilarityCoordinates.coordinateQ_spec (show 0 < 2*F.data.h by
        linarith [F.data.h_pos])
      (show 2*F.data.h < 1 by linarith [F.data.h_lt_half]) (p := (p.2.2,p.2.1)) ht
    have htq : p.2.2 ≤ SimilarityHomogeneity.chartQ F.data.h p := by
      have hn := mul_nonneg (sq_nonneg p.2.1) (Real.rpow_nonneg hspec.1.le (2*F.data.h))
      change p.2.2 ≤ SimilarityCoordinates.coordinateQ (2*F.data.h) (p.2.2,p.2.1)
      have he := hspec.2
      dsimp [SimilarityCoordinates.forwardScalar] at he
      linarith
    have hR := (hr hp).2.trans (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (le_max_right (1 : ℝ) U.qhi)) (PrimaryTargetBounds.rightRadius_pos W).le)
    change max |p.1| (max |p.2.1| |p.2.2|) ≤ geometryBound W U
    have hpR : 0 < p.1 := nativeStrip_radius W U hp
    rw [abs_of_pos hpR, abs_of_pos ht]
    exact (max_le_max hR (max_le_max hz (htq.trans hqM))).trans (le_max_right _ _)
  · intro i p hp
    have hq := hqm hp
    exact ⟨by
        linarith [U.qlo_pos, hq.1], by
            dsimp [geometryUpper]; linarith [hq.2, le_max_right (1 : ℝ) U.qhi]⟩
  · intro i p hp
    exact (nativeStrip_active W U hp).1

end NativeGeometry

theorem unweighted_polynomial_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : StripData Point) {D : PhaseJetBounds.Domain ℕ Slow} {f : ℕ → Slow → E}
    (hf : PhaseJetBounds.PolynomialJets (BaseChartJets.unitScale D) f)
    (hmap : ∀ n, MapsTo slowCoordinates s.domain (D.carrier n)) :
    UnweightedClass s 0 (fun n x => f n (slowCoordinates x)) := by
  refine ⟨fun _ _ _ => zero_le_one, fun n => (hf.smooth n).comp slowCoordinates.contDiff.contDiffOn
      (hmap n), ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := BaseChartJets.polynomial_unit_bound hf m
  refine ⟨C, zero_le_one.trans hC, 0, fun n x hx j hj => ?_⟩
  have hjet := PhaseJetBounds.norm_jet_comp_linear (D.isOpen n) (hf.smooth n)
    slowCoordinates (hmap n hx) j
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f n) (slowCoordinates x)‖ * ‖slowCoordinates‖ ^ j := hjet
    _ ≤ C * 1 := mul_le_mul (hb n j hj _ (hmap n hx))
      (pow_le_one₀ (norm_nonneg _) slowCoordinates_norm_le) (by positivity) (zero_le_one.trans hC)
    _ = _ := by simp only [majorant, Real.rpow_zero, pow_zero, mul_one]

theorem envelope_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : StripData Point) {D : PhaseJetBounds.Domain ℕ Slow} {f : ℕ → Slow → E}
    {w : ℕ → ℝ} (hf : PrimaryPulseBounds.EnvelopeJets (BaseChartJets.unitScale D) (fun n _ => w n)
        f)
    (hmap : ∀ n, MapsTo slowCoordinates s.domain (D.carrier n)) {alpha : ℝ}
    (hw : ∀ n, w n = s.epsilon n ^ alpha) :
    UnweightedClass s alpha (fun n x => f n (slowCoordinates x)) := by
  refine ⟨fun _ _ _ => zero_le_one, fun n => (hf.smooth n).comp slowCoordinates.contDiff.contDiffOn
      (hmap n), ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := BaseChartJets.envelope_unit_bound hf m
  refine ⟨C, zero_le_one.trans hC, 0, fun n x hx j hj => ?_⟩
  have hjet := PhaseJetBounds.norm_jet_comp_linear (D.isOpen n) (hf.smooth n)
    slowCoordinates (hmap n hx) j
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f n) (slowCoordinates x)‖ * ‖slowCoordinates‖ ^ j := hjet
    _ ≤ (C * w n) * 1 := mul_le_mul (hb n _ (hmap n hx) j hj)
      (pow_le_one₀ (norm_nonneg _) slowCoordinates_norm_le) (by positivity)
      (mul_nonneg (zero_le_one.trans hC) (hf.nonneg n _ (hmap n hx)))
    _ = _ := by simp only [majorant, pow_zero, mul_one, hw]

section ActualFields

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ)

/-- Radial base, given by `ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n x) 0`. -/
noncomputable def radialBase (n : ℕ) (x : Point) : ℝ :=
  ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
    FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n x) 0

/-- Frequency base, constructed using `BaseChartJets.frequency`. -/
noncomputable def frequencyBase (n : ℕ) (x : Point) : ℝ :=
  BaseChartJets.frequency (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
    (FinalSlowBase.coefficients H v) (ChartScales.Q n) (slowCoordinates x)

/-- Axial base, constructed using `BaseChartJets.axial`. -/
noncomputable def axialBase (n : ℕ) (x : Point) : ℝ :=
  BaseChartJets.axial (FinalSlowBase.scales H v upper B) F.data.h
    (FinalSlowBase.coefficients H v) (ChartScales.Q n) (slowCoordinates x)

/-- Base, bundling `radial`, `angular`, `axial`. -/
noncomputable def base : MeanIncrementBounds.Triple Point where
  radial := radialBase H v upper B
  angular n x := x.1 * frequencyBase H v upper B n x
  axial := axialBase H v upper B

/-- Raw stress as an element of `ℝ × ℝ`. -/
noncomputable def rawStress (n : ℕ) (x : Point) : ℝ × ℝ :=
  let p := AxisymmetricFields.profilePoint (physicalPoint F.data.h n x).1
    (physicalPoint F.data.h n x).2
  ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h) •
    (SlowBorelBase.baseStressTheta (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
      (FinalSlowBase.coefficients H v) p,
     SlowBorelBase.baseStressAxial (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
      (FinalSlowBase.coefficients H v) p)

/-- The physical stress on positive radius, extended by zero to the other
half-line. Its actual inner zero region makes this extension smooth. -/
noncomputable def virtualStress (n : ℕ) (x : Point) : ℝ × ℝ :=
  if 0 < x.1 then rawStress H v upper B n x else 0

@[simp] theorem virtualStress_eq_raw (n : ℕ) {x : Point} (hR : 0 < x.1) :
    virtualStress H v upper B n x = rawStress H v upper B n x := by
  simp only [virtualStress, ite_eq_left hR]

@[simp] theorem virtualStress_eq_zero (n : ℕ) {x : Point} (hR : x.1 ≤ 0) :
    virtualStress H v upper B n x = 0 := by
  simp only [virtualStress, ite_eq_right (not_lt.mpr hR)]

/-- Context, bundling `operators`, `base`, `virtualTheta`, `virtualAxial`. -/
noncomputable def context (a b : ℝ) (hab : a < b) : CorrectionState.Context Point where
  operators := operators F.data.h a b hab
  base := base H v upper B
  virtualTheta n x := (virtualStress H v upper B n x).1
  virtualAxial n x := (virtualStress H v upper B n x).2

theorem axialBase_physical (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    axialBase H v upper B n x = ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n x) 2 :=
  BaseChartJets.axial_eq_normalized_velocity (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (ChartScales.Q_pos n) (FinalSlowBase.coefficients_smooth H v) hT

theorem angularBase_physical (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : 0 < x.1) :
    (base H v upper B).angular n x = ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n x) 1 := by
  have he := BaseChartJets.frequency_eq_normalized_velocity
    (FinalSlowBase.scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half (ChartScales.Q_pos
        n)
    (FinalSlowBase.coefficients_smooth H v) (C := W.axis.normalization) (p := slowCoordinates x) hT
        hR
  change x.1 * BaseChartJets.frequency _ _ _ _ _ _ = _
  rw [he]
  change x.1 * (_ / x.1) = _
  simp only [FinalSlowBase.velocity, physicalPoint, slowCoordinates_apply]
  field_simp

theorem physicalComponent_smoothAt (n : ℕ) (i : Fin 3) {x : Point} (hT : 0 < x.2.1.1) :
    ContDiffAt ℝ ∞ (fun y => ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n y) i) x := by
  have hu := (FinalSlowBase.velocity_smooth H v upper B).contDiffAt
    (BaseResidual.past_isOpen.mem_nhds
      (show physicalPoint F.data.h n x ∈ BaseResidual.past from
        ⟨physicalPoint_time F.data.h n hT, mem_univ _⟩))
  exact contDiffAt_const.mul ((EuclideanSpace.proj i : ProblemStatement.Space →L[ℝ]
      ℝ).contDiff.contDiffAt.comp x
    (hu.comp x (physicalPoint_smooth F.data.h n).contDiffAt))

theorem base_smooth (U : Set Plane) (hT : ∀ p ∈ U, 0 < p.1) :
    MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain U) (base H v upper B) := by
  have hs (n : ℕ) (i : Fin 3) :
      ContDiffOn ℝ ∞ (fun y => ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
        FinalSlowBase.velocity H v upper B (physicalPoint F.data.h n y) i)
        (LocalRankDefect.positiveDomain U) :=
    fun x hx => (physicalComponent_smoothAt H v upper B n i (hT x.2.1 hx.2)).contDiffWithinAt
  refine ⟨fun n => hs n 0, fun n => ?_, fun n => ?_⟩
  · exact (hs n 1).congr (fun x hx => angularBase_physical H v upper B n (hT x.2.1 hx.2) hx.1)
  · exact (hs n 2).congr (fun x hx => axialBase_physical H v upper B n (hT x.2.1 hx.2))

theorem native_estimates (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    BaseChartJets.Estimates (phaseDomain W U ℕ) ChartScales.Q (FinalSlowBase.scales H v upper B)
      F.data.h W.axis.normalization (FinalSlowBase.coefficients H v) :=
  AllBandBaseJets.final_estimates H v upper B (geometryRadius_pos W U) (one_le_geometryBound W U)
    (div_pos U.qlo_pos (by norm_num)) (geometryUpper_pos U) (NominalConeAssembly.activeLeft_pos W)
    (le_max_right _ _) (native_geometry W U ℕ) ChartScales.Q ChartScales.Q_pos ChartScales.Q_le_one

theorem frequencyBase_unweighted (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    UnweightedClass (nativeStrip W U) 0 (frequencyBase H v upper B) :=
  unweighted_polynomial_pullback (nativeStrip W U) (native_estimates H v upper B U).frequency_jets
    (fun _ => slowCoordinates_maps W U)

theorem axialBase_unweighted (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    UnweightedClass (nativeStrip W U) 0 (axialBase H v upper B) :=
  unweighted_polynomial_pullback (nativeStrip W U) (native_estimates H v upper B U).axial_jets
    (fun _ => slowCoordinates_maps W U)

theorem radialBase_unweighted (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    UnweightedClass (nativeStrip W U) 1 (radialBase H v upper B) := by
  have hr := AllBandBaseJets.final_radial_envelope H v upper B (geometryRadius_pos W U)
    (one_le_geometryBound W U) (div_pos U.qlo_pos (by norm_num)) (geometryUpper_pos U)
    (NominalConeAssembly.activeLeft_pos W) (le_max_right _ _) (native_geometry W U ℕ)
    ChartScales.Q ChartScales.Q_pos ChartScales.Q_le_one
  exact envelope_pullback (nativeStrip W U) hr (fun _ => slowCoordinates_maps W U)
    (fun n => by rw [Real.rpow_one]; rfl)

theorem base_bounds (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    MeanIncrementBounds.BaseBounds (nativeStrip W U) (base H v upper B) := by
  refine ⟨radialBase_unweighted H v upper B U, ?_, axialBase_unweighted H v upper B U⟩
  have hr : UnweightedClass (nativeStrip W U) 0 (fun _ (x : Point) => x.1) :=
    radial_unweighted (fun _ hx => movingStrip_radial_bounds F.data.h_pos.le U _ _ _ _
      (PrimaryTargetBounds.leftRadius_pos W)
      (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num)) zero_lt_one hx) contDiff_id
  have he := hr.mul (frequencyBase_unweighted H v upper B U)
  simp only [zero_add, mul_one] at he
  exact he

theorem rawStress_smooth (U : Set Plane) (hT : ∀ p ∈ U, 0 < p.1) (n : ℕ) :
    ContDiffOn ℝ ∞ (rawStress H v upper B n) (PhysicalMeanDomain.slowDomain U) := by
  let P : Point → SlowBorelBase.Chart := fun x => AxisymmetricFields.profilePoint
    (physicalPoint F.data.h n x).1 (physicalPoint F.data.h n x).2
  have hP : ContDiff ℝ ∞ P :=
    AxisymmetricFields.contDiff_profilePoint.comp (physicalPoint_smooth F.data.h n)
  intro x hx
  have ht : (P x).1 < 1 := physicalPoint_time F.data.h n (hT x.2.1 hx)
  have htheta := SlowBorelBase.physicalProfile_smoothAt (FinalSlowBase.scales_strictMono H v upper
      B)
    F.data.h_pos F.data.h_lt_half (SlowBorelBase.bundleComponent_smooth
      (FinalSlowBase.coefficients_smooth H v) W.axis.normalization 3) (-CoordinateAlgebra.A
          F.data.h - 1 / 2) ht
  have haxial := SlowBorelBase.physicalProfile_smoothAt (FinalSlowBase.scales_strictMono H v upper
      B)
    F.data.h_pos F.data.h_lt_half (SlowBorelBase.bundleComponent_smooth
      (FinalSlowBase.coefficients_smooth H v) W.axis.normalization 4) (-CoordinateAlgebra.A
          F.data.h - 1 / 2) ht
  exact ((contDiffAt_const (c := (ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h) : ℝ))).smul
      ((htheta.comp x hP.contDiffAt).prodMk
    (haxial.comp x hP.contDiffAt))).contDiffWithinAt

theorem rawStress_periodic (U : Set Plane) (n : ℕ) :
    PhysicalMeanDomain.PeriodicOn U (fun x => (rawStress H v upper B n x).1) ∧
    PhysicalMeanDomain.PeriodicOn U (fun x => (rawStress H v upper B n x).2) := by
  constructor <;> intro r s hs Y k <;> rfl

theorem rawStress_normalized (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    rawStress H v upper B n x =
      (ChartScales.epsilon F.data.h n *
        (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).1 ^
          (-CoordinateAlgebra.A F.data.h - 1 / 2)) •
      FinalSlowBase.normalizedStress H v upper B
        (SlowBorelBase.scaleMap (ChartScales.Q n)
          (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x))) := by
  have hq := BaseChartJets.normalizedCoordinates_q_pos F.data.h_pos F.data.h_lt_half
    (p := slowCoordinates x) hT
  have he := FinalSlowBase.physical_stress_eq_normalized H v upper B
    (p := AxisymmetricFields.profilePoint (physicalPoint F.data.h n x).1 (physicalPoint F.data.h n
        x).2)
    (physicalPoint_time F.data.h n hT)
  have hc := BaseChartJets.bandPoint_chart F.data.h_pos F.data.h_lt_half (ChartScales.Q_pos n)
    (p := slowCoordinates x) hT
  change SlowBorelBase.physicalChart F.data.h
    (AxisymmetricFields.profilePoint (physicalPoint F.data.h n x).1 (physicalPoint F.data.h n x).2)
        = _ at hc
  rw [hc] at he
  change ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h) • _ = _
  rw [he, smul_smul]
  congr 1
  simp only [SlowBorelBase.scaleMap_apply]
  rw [Real.mul_rpow (ChartScales.Q_pos n).le hq.le, ← mul_assoc,
    ← Real.rpow_add (ChartScales.Q_pos n)]
  have hex : 2 * CoordinateAlgebra.A F.data.h + (-CoordinateAlgebra.A F.data.h - 1 / 2) = F.data.h
      := by
    unfold CoordinateAlgebra.A
    ring
  rw [hex]
  rfl

theorem rawStress_zero_inner (n : ℕ) {x : Point} (hT : 0 < x.2.1.1)
    (hX : (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2.1 ≤
      NominalConeAssembly.activeLeft W) : rawStress H v upper B n x = 0 := by
  rw [rawStress_normalized H v upper B n hT]
  rw [show FinalSlowBase.normalizedStress H v upper B
      (SlowBorelBase.scaleMap (ChartScales.Q n)
        (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x))) = 0 from
    FinalSlowBase.normalizedStress_zero_left H v upper B _ hX, smul_zero]

theorem rawStress_zero_near_axis (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : x.1 = 0) :
    rawStress H v upper B n =ᶠ[𝓝 x] 0 := by
  have hc := (BaseChartJets.normalizedCoordinates_smoothAt F.data.h_pos F.data.h_lt_half
    (p := slowCoordinates x) hT).comp x slowCoordinates.contDiff.contDiffAt
  have hzero : (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2.1 = 0 := by
    rw [BaseChartJets.normalizedCoordinates_eq]
    simp [SimilarityHomogeneity.chartX, SimilarityCoordinates.coordinateX,
      slowCoordinates_apply, hR]
  have hx : (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2.1 <
      NominalConeAssembly.activeLeft W := by rw [hzero]; exact NominalConeAssembly.activeLeft_pos W
  filter_upwards [(isOpen_lt continuous_const continuous_snd.fst.fst).mem_nhds hT,
    hc.snd.fst.continuousAt.eventually (Iio_mem_nhds hx)] with y hy hY
  exact rawStress_zero_inner H v upper B n hy hY.le

theorem virtualStress_smooth (U : Set Plane) (hT : ∀ p ∈ U, 0 < p.1) (n : ℕ) :
    ContDiffOn ℝ ∞ (virtualStress H v upper B n) (PhysicalMeanDomain.slowDomain U) := by
  intro x hx
  by_cases hR : 0 < x.1
  · have he : virtualStress H v upper B n =ᶠ[𝓝 x] rawStress H v upper B n := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hR] with y hy
      exact virtualStress_eq_raw H v upper B n hy
    exact (rawStress_smooth H v upper B U hT n x hx).congr_of_eventuallyEq
      (he.filter_mono nhdsWithin_le_nhds) he.self_of_nhds
  · have he : virtualStress H v upper B n =ᶠ[𝓝 x] 0 := by
      rcases lt_or_eq_of_le (le_of_not_gt hR) with hneg | hzero
      · filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hneg] with y hy
        exact virtualStress_eq_zero H v upper B n hy.le
      · filter_upwards [rawStress_zero_near_axis H v upper B n (hT x.2.1 hx) hzero] with y hy
        simp only [virtualStress]
        split_ifs <;> simp_all only [Pi.zero_apply]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

theorem virtualStress_periodic (U : Set Plane) (n : ℕ) :
    PhysicalMeanDomain.PeriodicOn U (fun x => (virtualStress H v upper B n x).1) ∧
    PhysicalMeanDomain.PeriodicOn U (fun x => (virtualStress H v upper B n x).2) := by
  constructor <;> intro r s hs Y k <;> rfl

theorem virtualStress_normalized (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : 0 < x.1) :
    virtualStress H v upper B n x =
      (ChartScales.epsilon F.data.h n *
        (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).1 ^
          (-CoordinateAlgebra.A F.data.h - 1 / 2)) •
      FinalSlowBase.normalizedStress H v upper B
        (SlowBorelBase.scaleMap (ChartScales.Q n)
          (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x))) := by
  rw [virtualStress_eq_raw H v upper B n hR, rawStress_normalized H v upper B n hT]

theorem virtualStress_support (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    (n : ℕ) {x : Point} (hx : x.2.1 ∈ U.carrier) (hn : virtualStress H v upper B n x ≠ 0) :
    (LocalSignedRequest.profileMap (2 * F.data.h) x).1 ∈
      Icc (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) := by
  have hR : 0 < x.1 := by
    by_contra hh
    exact hn (virtualStress_eq_zero H v upper B n (le_of_not_gt hh))
  have hT := U.time_pos _ hx
  have hX : (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2.1 ∈
      Icc (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) := by
    by_contra hh
    apply hn
    rw [virtualStress_normalized H v upper B n hT hR]
    rw [show FinalSlowBase.normalizedStress H v upper B
        (SlowBorelBase.scaleMap (ChartScales.Q n)
          (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x))) = 0 from
      FinalSlowBase.normalizedStress_zero_outside H v upper B _ hh
        (let he := abs_lt.mp (BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half
          (p := slowCoordinates x) hT); ⟨he.1.le, he.2.le⟩), smul_zero]
  have hpos := PrimaryTargetBounds.profileRadius_pos (F := F) (p := slowCoordinates x) hT hR
  have he := PrimaryTargetBounds.profileRadius_sq (F := F) (p := slowCoordinates x) hT
  have ha : (PrimaryTargetBounds.leftRadius W)^2 = 2 * NominalConeAssembly.activeLeft W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)
  have hb : (PrimaryTargetBounds.rightRadius W)^2 = 2 * NominalConeAssembly.activeRight W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W).le)
  have hrad : PrimaryTargetBounds.profileRadius F.data.h (slowCoordinates x) ∈
      Icc (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) := by
    constructor
    · nlinarith [PrimaryTargetBounds.leftRadius_pos W, hX.1]
    · nlinarith [PrimaryTargetBounds.rightRadius_pos W, hX.2]
  change x.1 / Real.sqrt (MeanRankUpdate.chartQ (2 * F.data.h) x) ∈ _
  rw [← PrimaryTargetBounds.meanPoint_scalar (F := F) x]
  exact hrad

theorem virtualStress_movingSupport (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (n : ℕ) :
    LocalSignedRequest.MovingSupport (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.rightRadius W)
      (2 * F.data.h) U.carrier (fun x => (virtualStress H v upper B n x).1) ∧
    LocalSignedRequest.MovingSupport (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.rightRadius W)
      (2 * F.data.h) U.carrier (fun x => (virtualStress H v upper B n x).2) := by
  constructor <;> intro x hx hn <;> apply virtualStress_support H v upper B U n hx <;>
    intro he <;> simp only [he, Prod.fst_zero, Prod.snd_zero, ne_eq, not_true_eq_false] at hn

/-- Leading virtual stress, with branches according to `0 < x.1`. -/
noncomputable def leadingVirtualStress (n : ℕ) (x : Point) : ℝ × ℝ :=
  if 0 < x.1 then
    (ChartScales.epsilon F.data.h n *
      (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).1 ^
        (-CoordinateAlgebra.A F.data.h - 1/2)) •
      BaseResidual.stressPair (FinalSlowBase.coefficients H v) 0
        (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).2
  else 0

theorem leadingVirtualStress_eq (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : 0 < x.1) :
    leadingVirtualStress H v n x =
      (ChartScales.epsilon F.data.h n *
        (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates x)).1 ^
          (-CoordinateAlgebra.A F.data.h - 1/2)) •
      FinalSlowBase.leadingStress v (BaseChartJets.normalizedCoordinates F.data.h (slowCoordinates
          x)).2 := by
  rw [leadingVirtualStress, ite_eq_left hR]
  congr 1
  apply FinalSlowBase.leading_stress_eq H v
  · have hp := PrimaryTargetBounds.profileRadius_sq (F := F) (p := slowCoordinates x) hT
    rw [← hp]
    positivity
  · exact (BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half
      (p := slowCoordinates x) hT).le

/-- Wave coefficients, bundling `radius`, `radialBase`, `frequencyBase`, `axialBase` and the
required compatibility proofs. -/
noncomputable def waveCoefficients (phase : ℕ → Point × ℝ → ℝ)
    (amplitude : ℕ → Point × ℝ → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → Point × ℝ → ℂ) (frequency : ℕ → ℝ) :
    LinearWaveBounds.WaveCoefficients (Point × ℝ) where
  radius _ x := x.1.1
  radialBase n x := radialBase H v upper B n x.1
  frequencyBase n x := frequencyBase H v upper B n x.1
  axialBase n x := axialBase H v upper B n x.1
  phase := phase
  amplitude := amplitude
  pressure := pressure
  frequency := frequency

theorem waveCoefficients_match (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (phase : ℕ → Point × ℝ → ℝ)
    (amplitude : ℕ → Point × ℝ → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → Point × ℝ → ℂ) (frequency : ℕ → ℝ) :
    PrimaryResidualClass.Matches (movingStrip F.data.h_pos.le U a b cL cR ha hcL hcR)
      (context H v upper B a b hab) (waveCoefficients H v upper B phase amplitude pressure
          frequency) := by
  refine ⟨rfl, rfl, ?_⟩
  intro n
  funext x i
  fin_cases i <;> rfl

/-- Radial slow, constructed using `BaseRadialJets.radial`. -/
noncomputable def radialSlow (n : ℕ) (p : Slow) : ℝ :=
  BaseRadialJets.radial (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
    (FinalSlowBase.coefficients H v) (ChartScales.Q n) p

/-- Frequency slow, constructed using `BaseChartJets.frequency`. -/
noncomputable def frequencySlow (n : ℕ) : Slow → ℝ :=
  BaseChartJets.frequency (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
    (FinalSlowBase.coefficients H v) (ChartScales.Q n)

/-- Axial slow, given by `BaseChartJets.axial (FinalSlowBase.scales H v upper B) F.data.h
(FinalSlowBase.coefficients H v) (ChartScales.Q n)`. -/
noncomputable def axialSlow (n : ℕ) : Slow → ℝ :=
  BaseChartJets.axial (FinalSlowBase.scales H v upper B) F.data.h
    (FinalSlowBase.coefficients H v) (ChartScales.Q n)

theorem radialSlow_pullback (n : ℕ) (x : Point) :
    radialSlow H v upper B n (slowCoordinates x) = radialBase H v upper B n x := rfl

theorem radialBase_stream (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    radialBase H v upper B n x = -(ChartScales.epsilon F.data.h n * x.1 / 2) *
      PhaseCalculus.slowZ (BaseRadialJets.normalizedStream (FinalSlowBase.scales H v upper B)
        F.data.h (FinalSlowBase.coefficients H v) (ChartScales.Q n)) (slowCoordinates x) :=
  BaseRadialJets.radial_eq_stream (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (ChartScales.Q_pos n) (FinalSlowBase.coefficients_smooth H v) hT

theorem radialSlow_smoothAt (n : ℕ) {p : Slow} (hp : 0 < p.2.2) :
    ContDiffAt ℝ ∞ (radialSlow H v upper B n) p := by
  exact (physicalComponent_smoothAt H v upper B n 0 (x := insertSlow p) hp).comp p
    insertSlow.contDiff.contDiffAt

/-- The slot clock can vary with the native construction. Its slow and
angular coordinates stay literal, so no phase estimate enters the binding. -/
noncomputable def nativeCoordinates (clock : ℕ → Point → ℝ) (n : ℕ) (x : Point × ℝ) :
    PhaseCalculus.Slot :=
  (slowCoordinates x.1, (x.2, clock n x.1))

theorem primaryCoefficients_match
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {D : PhaseJetBounds.Domain ℕ Slow} (P : PrimaryPulseBounds.PhaseConstruction D)
    (hF : P.phase.F = frequencySlow H v upper B)
    (hG : P.phase.G = axialSlow H v upper B)
    (chi : ℕ → Point × ℝ → PhaseCalculus.Slot)
    (hchi : ∀ n x, (chi n x).1 = slowCoordinates x.1)
    (amplitude : ℕ → Point × ℝ → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → Point × ℝ → ℂ) (frequency : ℕ → ℝ) :
    PrimaryResidualClass.Matches (nativeStrip W U)
      (context H v upper B (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)
        (PrimaryTargetBounds.radii_ordered W))
      (PrimaryMaterialDefect.coefficients P (radialSlow H v upper B) chi amplitude pressure
          frequency) := by
  refine ⟨rfl, ?_, ?_⟩
  · funext n x
    change (chi n x).1.1 = x.1.1
    rw [hchi]
    rfl
  · intro n
    funext x i
    simp only [PrimaryMaterialDefect.coefficients, LinearWaveResidual.complexBase,
      LinearWaveResidual.base, hchi, hF, hG, HarmonicResidual.contextBase, context, base,
      radialSlow_pullback]
    fin_cases i <;> rfl

theorem nativeCoefficients_match
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {D : PhaseJetBounds.Domain ℕ Slow} (P : PrimaryPulseBounds.PhaseConstruction D)
    (hF : P.phase.F = frequencySlow H v upper B)
    (hG : P.phase.G = axialSlow H v upper B)
    (clock : ℕ → Point → ℝ)
    (amplitude : ℕ → Point × ℝ → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → Point × ℝ → ℂ) (frequency : ℕ → ℝ) :
    PrimaryResidualClass.Matches (nativeStrip W U)
      (context H v upper B (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)
        (PrimaryTargetBounds.radii_ordered W))
      (PrimaryMaterialDefect.coefficients P (radialSlow H v upper B) (nativeCoordinates clock)
        amplitude pressure frequency) :=
  primaryCoefficients_match H v upper B U P hF hG (nativeCoordinates clock) (fun _ _ => rfl)
    amplitude pressure frequency

theorem radialSlow_productClass (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    (chi : ℕ → Point × ℝ → PhaseCalculus.Slot)
    (hchi : ∀ n x, (chi n x).1 = slowCoordinates x.1) :
    UnweightedClass (HarmonicWaveInteraction.productStrip (nativeStrip W U)) 1
      (fun n x => radialSlow H v upper B n (chi n x).1) := by
  apply MeanIncrementBounds.class_congr (HarmonicWaveInteraction.class_lift
    (radialBase_unweighted H v upper B U))
  intro n x hx
  change radialSlow H v upper B n (chi n x).1 = radialBase H v upper B n x.1
  rw [hchi, radialSlow_pullback]

/-- Native context, given by `context H v upper B (PrimaryTargetBounds.leftRadius W)
(PrimaryTargetBounds.rightRadius W) (PrimaryTargetBounds.radii_ordered W)`. -/
noncomputable def nativeContext : CorrectionState.Context Point :=
  context H v upper B (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)
    (PrimaryTargetBounds.radii_ordered W)

theorem native_operator_bounds (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    MeanIncrementBounds.OperatorBounds (nativeStrip W U) (nativeContext H v upper B).operators
      ChartScales.kappa :=
  operator_bounds F.data.h_pos.le U (PrimaryTargetBounds.leftRadius_pos W)
    (PrimaryTargetBounds.radii_ordered W) (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num))
    zero_lt_one

theorem native_base_bounds (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    MeanIncrementBounds.BaseBounds (nativeStrip W U) (nativeContext H v upper B).base :=
  base_bounds H v upper B U

theorem native_operators_local (U : Set Plane) :
    LocalRankDefect.LocalOperators U (nativeContext H v upper B).operators :=
  operators_local (PrimaryTargetBounds.radii_ordered W) U

theorem native_base_smooth (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) :
    MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain U.carrier)
      (nativeContext H v upper B).base := base_smooth H v upper B U.carrier U.time_pos

theorem native_radial_isSlow (U : Set Plane) :
    LocalRankDefect.IsSlowOn U (nativeContext H v upper B).base.radial := by
  intro n R p hp Y
  rfl

theorem native_angular_isSlow (U : Set Plane) :
    LocalRankDefect.IsSlowOn U (nativeContext H v upper B).base.angular := by
  intro n R p hp Y
  rfl

theorem native_axial_isSlow (U : Set Plane) :
    LocalRankDefect.IsSlowOn U (nativeContext H v upper B).base.axial := by
  intro n R p hp Y
  rfl

theorem native_matches_physical (n : ℕ) :
    PhysicalResidualTZ.MatchesAtTZ (nativeContext H v upper B).operators
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) F.data.h (commonIndex F.data.h n)) n :=
  operators_match_physical _ _ _ _ n

theorem native_stress_properties (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun x => ((nativeContext H v upper B).virtualTheta n x,
      (nativeContext H v upper B).virtualAxial n x)) (PhysicalMeanDomain.slowDomain U.carrier) ∧
    PhysicalMeanDomain.PeriodicOn U.carrier ((nativeContext H v upper B).virtualTheta n) ∧
    PhysicalMeanDomain.PeriodicOn U.carrier ((nativeContext H v upper B).virtualAxial n) ∧
    LocalSignedRequest.MovingSupport (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.rightRadius W)
      (2 * F.data.h) U.carrier ((nativeContext H v upper B).virtualTheta n) ∧
    LocalSignedRequest.MovingSupport (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.rightRadius W)
      (2 * F.data.h) U.carrier ((nativeContext H v upper B).virtualAxial n) :=
  ⟨virtualStress_smooth H v upper B U.carrier U.time_pos n,
    (virtualStress_periodic H v upper B U.carrier n).1,
    (virtualStress_periodic H v upper B U.carrier n).2,
    (virtualStress_movingSupport H v upper B U n).1,
    (virtualStress_movingSupport H v upper B U n).2⟩

end ActualFields

/-- Constructed context, given by `nativeContext FinalSlowBase.actualProfile.certificate
FinalSlowBase.actualProfile.modulation upper B`. -/
noncomputable def constructedContext (upper : ℝ) (B : ℕ) : CorrectionState.Context Point :=
  nativeContext FinalSlowBase.actualProfile.certificate FinalSlowBase.actualProfile.modulation
      upper B

theorem constructed_context_bounds (upper : ℝ) (B : ℕ)
    (U : LocalSignedRequest.SlowRegion (2 * FinalSlowBase.actualProfile.outgoing.data.h)) :
    MeanIncrementBounds.OperatorBounds (nativeStrip FinalSlowBase.actualProfile.nominal U)
      (constructedContext upper B).operators ChartScales.kappa ∧
    MeanIncrementBounds.BaseBounds (nativeStrip FinalSlowBase.actualProfile.nominal U)
      (constructedContext upper B).base ∧
    LocalRankDefect.LocalOperators U.carrier (constructedContext upper B).operators ∧
    MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain U.carrier)
      (constructedContext upper B).base :=
  ⟨native_operator_bounds _ _ upper B U, native_base_bounds _ _ upper B U,
    native_operators_local _ _ upper B U.carrier, native_base_smooth _ _ upper B U⟩

end NavierStokes.BaseContextAssembly
