/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseContextAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseStressClasses
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualNaturality

@[expose] public section

/-!
# The actual slow base on a coarsest common integer cover

The physical base, virtual stress, dyadic band and small parameter stay fixed.
Only the integer cover used in the graph operators changes. The forward
real-lift map is the genuine integer covering matrix, with its actual norm.
-/

noncomputable section

namespace NavierStokes.CommonBaseContext

open Set Function Filter WeightedClasses
open scoped ContDiff Topology BigOperators

abbrev Plane := BaseContextAssembly.Plane
abbrev Point := BaseContextAssembly.Point
abbrev Slow := BaseContextAssembly.Slow

/-- Scalar hypotheses on the chosen common index, including every low band. -/
structure IndexBounds (h : ℝ) (index : ℕ → ℕ) (K : ℕ) : Prop where
  le_native : ∀ n, index n ≤ ChartScales.nativeIndex h n
  gap_le : ∀ n, ChartScales.nativeIndex h n - index n ≤ K

theorem IndexBounds.native_le_add {h : ℝ} {index : ℕ → ℕ} {K : ℕ}
    (H : IndexBounds h index K) (n : ℕ) : ChartScales.nativeIndex h n ≤ index n + K := by
  have hi := H.le_native n
  have hg := H.gap_le n
  omega

theorem IndexBounds.add_gap {h : ℝ} {index : ℕ → ℕ} {K : ℕ}
    (H : IndexBounds h index K) (n : ℕ) :
    index n + (ChartScales.nativeIndex h n - index n) = ChartScales.nativeIndex h n :=
  Nat.add_sub_of_le (H.le_native n)

theorem IndexBounds.commonRatio {h : ℝ} {index : ℕ → ℕ} {K : ℕ}
    (H : IndexBounds h index K) (n : ℕ) :
    0 < MeanChartCompatibility.commonRatio h n (index n) ∧
      MeanChartCompatibility.commonRatio h n (index n) ≤ ChartScales.Tg ^ K :=
  ⟨MeanChartCompatibility.commonRatio_pos h n (index n),
    MeanChartCompatibility.commonRatio_le (H.native_le_add n)⟩

noncomputable def radialFrequency (h : ℝ) (index : ℕ → ℕ) (n : ℕ) : ℝ :=
  ChartScales.Lambda ^ index n * ChartScales.Q n ^ (ChartScales.radialExponent h / 2)

noncomputable def fastCoefficient (h : ℝ) (index : ℕ → ℕ) (n : ℕ) : ℝ :=
  ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h)

theorem radialFrequency_pos (h : ℝ) (index : ℕ → ℕ) (n : ℕ) : 0 < radialFrequency h index n :=
  mul_pos (pow_pos ChartScales.Lambda_pos _) (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)

theorem fastCoefficient_pos (h : ℝ) (index : ℕ → ℕ) (n : ℕ) : 0 < fastCoefficient h index n :=
  mul_pos (pow_pos ChartScales.Tg_pos _) (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)

theorem radialFrequency_mono (h : ℝ) {i j : ℕ → ℕ} {n : ℕ} (hij : i n ≤ j n) :
    radialFrequency h i n ≤ radialFrequency h j n :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [ChartScales.Lambda_two_lt]) hij)
    (Real.rpow_nonneg (ChartScales.Q_pos n).le _)

theorem fastCoefficient_mono (h : ℝ) {i j : ℕ → ℕ} {n : ℕ} (hij : i n ≤ j n) :
    fastCoefficient h i n ≤ fastCoefficient h j n :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ChartScales.Tg_one_lt.le hij)
    (Real.rpow_nonneg (ChartScales.Q_pos n).le _)

theorem radialFrequency_add (h : ℝ) (i k : ℕ → ℕ) (n : ℕ) :
    radialFrequency h (fun m => i m + k m) n = ChartScales.Lambda ^ k n * radialFrequency h i n :=
      by
  simp only [radialFrequency, pow_add]
  ring

theorem fastCoefficient_add (h : ℝ) (i k : ℕ → ℕ) (n : ℕ) :
    fastCoefficient h (fun m => i m + k m) n = ChartScales.Tg ^ k n * fastCoefficient h i n := by
  simp only [fastCoefficient, pow_add]
  ring

theorem radialFrequency_bounds {h : ℝ} {index : ℕ → ℕ} {K : ℕ}
    (H : IndexBounds h index K) (n : ℕ) :
    ChartScales.radialCoefficient h n / ChartScales.Lambda ^ K ≤ radialFrequency h index n ∧
      radialFrequency h index n ≤ ChartScales.radialCoefficient h n := by
  refine ⟨?_, radialFrequency_mono h (H.le_native n)⟩
  apply (div_le_iff₀ (pow_pos ChartScales.Lambda_pos K)).mpr
  have hm := radialFrequency_mono h (i := ChartScales.nativeIndex h)
    (j := fun m => index m + K) (n := n) (H.native_le_add n)
  rw [radialFrequency_add] at hm
  simp only [mul_comm]
  exact hm

theorem fastCoefficient_bounds {h : ℝ} {index : ℕ → ℕ} {K : ℕ}
    (H : IndexBounds h index K) (n : ℕ) :
    ChartScales.timeCoefficient h n / ChartScales.Tg ^ K ≤ fastCoefficient h index n ∧
      fastCoefficient h index n ≤ ChartScales.timeCoefficient h n := by
  refine ⟨?_, fastCoefficient_mono h (H.le_native n)⟩
  apply (div_le_iff₀ (pow_pos ChartScales.Tg_pos K)).mpr
  have hm := fastCoefficient_mono h (i := ChartScales.nativeIndex h)
    (j := fun m => index m + K) (n := n) (H.native_le_add n)
  rw [fastCoefficient_add] at hm
  simp only [mul_comm]
  exact hm

theorem fastCoefficient_inverse_bound {h : ℝ} {index : ℕ → ℕ} {K : ℕ}
    (H : IndexBounds h index K) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    (fastCoefficient h index n)⁻¹ ≤ ChartScales.Tg ^ (K+1) * ChartScales.S n := by
  have hl := (fastCoefficient_bounds H n).1
  have hp := div_pos (ChartScales.timeCoefficient_pos h n) (pow_pos ChartScales.Tg_pos K)
  have hi := inv_anti₀ hp hl
  rw [inv_div] at hi
  calc
    _ ≤ ChartScales.Tg ^ K / ChartScales.timeCoefficient h n := hi
    _ ≤ ChartScales.Tg ^ K * (ChartScales.Tg * ChartScales.S n) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (ChartScales.timeCoefficient_inv_upper h hh hn)
        (pow_nonneg ChartScales.Tg_pos.le _)
    _ = _ := by rw [pow_succ]; ring

noncomputable def reconstruction (h : ℝ) (index : ℕ → ℕ) (a b : ℝ) (hab : a < b) :
    CorrectionState.ReconstructionData where
  exponent := ChartScales.radialExponent h
  inner := a
  outer := b
  inner_lt_outer := hab
  frequency := radialFrequency h index
  radialDirection := TorusInverse.vector .radial

noncomputable def operators (h : ℝ) (index : ℕ → ℕ) (a b : ℝ) (hab : a < b) :
    MeanIncrementBounds.Operators Point :=
  CorrectionState.graphOperators (reconstruction h index a b hab) (ChartScales.epsilon h)
    (fastCoefficient h index) ((0,1),0) ((1,0),0) (TorusInverse.vector .temporal)

theorem operators_native (h a b : ℝ) (hab : a < b) :
    operators h (ChartScales.nativeIndex h) a b hab = BaseContextAssembly.operators h a b hab := rfl

theorem operators_match_physical (h : ℝ) (index : ℕ → ℕ) (a b : ℝ) (hab : a < b) (n : ℕ) :
    PhysicalResidualTZ.MatchesAtTZ (operators h index a b hab)
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (index n)) n := by
  constructor <;> rfl

theorem operator_bounds {h : ℝ} (hh : 0 ≤ h) (U : LocalSignedRequest.SlowRegion (2*h))
    {index : ℕ → ℕ} (hi : ∀ n, index n ≤ ChartScales.nativeIndex h n)
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR) :
    MeanIncrementBounds.OperatorBounds (BaseContextAssembly.movingStrip hh U a b cL cR ha hcL hcR)
      (operators h index a b hab) ChartScales.kappa := by
  have hn := BaseContextAssembly.operator_bounds hh U ha hab hcL hcR
  refine ⟨hn.epsilon_eq, hn.radialProfile, hn.invRadius, ?_, ?_, hn.kappa_nonneg, hn.weight_le_one⟩
  · obtain ⟨C, hC, p, hp⟩ := hn.radialFrequency
    refine ⟨C, hC, p, fun n => ?_⟩
    apply le_trans _ (hp n)
    change ‖radialFrequency h index n‖ ≤ ‖ChartScales.radialCoefficient h n‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (radialFrequency_pos h index n),
      abs_of_pos (ChartScales.radialCoefficient_pos h n)]
    exact radialFrequency_mono h (hi n)
  · obtain ⟨C, hC, p, hp⟩ := hn.fastCoefficient
    refine ⟨C, hC, p, fun n => ?_⟩
    apply le_trans _ (hp n)
    change ‖fastCoefficient h index n‖ ≤ ‖ChartScales.timeCoefficient h n‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (fastCoefficient_pos h index n),
      abs_of_pos (ChartScales.timeCoefficient_pos h n)]
    exact fastCoefficient_mono h (hi n)

section Cover

/-- The forward integer covering on the full free auxiliary lift. -/
noncomputable def coverLift (k : ℕ) : Point ≃L[ℝ] Point :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    ((ContinuousLinearEquiv.refl ℝ Plane).prodCongr (CommonCoverSolve.coverPower k))

@[simp] theorem coverLift_apply (k : ℕ) (x : Point) :
    coverLift k x = (x.1, (x.2.1, CommonCoverSolve.coverPower k x.2.2)) := rfl

@[simp] theorem coverLift_slow (k : ℕ) (x : Point) :
    BaseContextAssembly.slowCoordinates (coverLift k x) = BaseContextAssembly.slowCoordinates x :=
      rfl

@[simp] theorem coverLift_eR (k : ℕ) : coverLift k (1,(0,0)) = (1,(0,0)) := by
  simp only [coverLift_apply, map_zero]

@[simp] theorem coverLift_eZ (k : ℕ) : coverLift k (0,((0,1),0)) = (0,((0,1),0)) := by
  simp only [coverLift_apply, map_zero]

@[simp] theorem coverLift_eT (k : ℕ) : coverLift k (0,((1,0),0)) = (0,((1,0),0)) := by
  simp only [coverLift_apply, map_zero]

theorem coverPower_radial (k : ℕ) :
    CommonCoverSolve.coverPower k (TorusInverse.vector .radial) =
      ChartScales.Lambda ^ k • TorusInverse.vector .radial := by
  rw [CommonCoverSolve.coverPower_apply]
  exact PhysicalGraphBounds.cover_pow_radialDirection k

theorem coverPower_temporal (k : ℕ) :
    CommonCoverSolve.coverPower k (TorusInverse.vector .temporal) =
      ChartScales.Tg ^ k • TorusInverse.vector .temporal := by
  rw [CommonCoverSolve.coverPower_apply]
  exact PhysicalGraphBounds.cover_pow_timeDirection k

theorem coverLift_vR (k : ℕ) : coverLift k (0,(0,TorusInverse.vector .radial)) =
    ChartScales.Lambda ^ k • (0,(0,TorusInverse.vector .radial)) := by
  rw [coverLift_apply, coverPower_radial]
  simp

theorem coverLift_vT (k : ℕ) : coverLift k (0,(0,TorusInverse.vector .temporal)) =
    ChartScales.Tg ^ k • (0,(0,TorusInverse.vector .temporal)) := by
  rw [coverLift_apply, coverPower_temporal]
  simp

theorem coverPower_comp (i k : ℕ) (Y : Plane) :
    CommonCoverSolve.coverPower k (CommonCoverSolve.coverPower i Y) =
      CommonCoverSolve.coverPower (i+k) Y := by
  simp only [CommonCoverSolve.coverPower_apply]
  rw [← _root_.mul_apply_eq_comp, ← pow_add, Nat.add_comm]

theorem coverLift_physicalToChart (h : ℝ) (n i k : ℕ) (x : Point) :
    coverLift k (PhysicalResidualTZ.physicalToChartTZ h n i x) =
      PhysicalResidualTZ.physicalToChartTZ h n (i+k) x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · change CommonCoverSolve.coverPower k (TemporalMeanUpdate.coverMap i x.2.2) =
        TemporalMeanUpdate.coverMap (i+k) x.2.2
      rw [MeanChartCompatibility.coverMap_eq_coverPower,
        MeanChartCompatibility.coverMap_eq_coverPower,
        coverPower_comp]

theorem IndexBounds.physicalToChart {h : ℝ} {index : ℕ → ℕ} {K : ℕ}
    (H : IndexBounds h index K) (n : ℕ) (x : Point) :
    coverLift (ChartScales.nativeIndex h n - index n)
      (PhysicalResidualTZ.physicalToChartTZ h n (index n) x) =
    PhysicalResidualTZ.physicalToChartTZ h n (ChartScales.nativeIndex h n) x := by
  rw [coverLift_physicalToChart, H.add_gap n]

noncomputable def pull {E : Type*} (gap : ℕ → ℕ) (f : ℕ → Point → E) (n : ℕ) (x : Point) : E :=
  f n (coverLift (gap n) x)

theorem pull_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gap : ℕ → ℕ) (f : ℕ → Point → E) (n : ℕ) (x v : Point) :
    fderiv ℝ (pull gap f n) x v = fderiv ℝ (f n) (coverLift (gap n) x) (coverLift (gap n) v) :=
  PhysicalResidualTZ.fderiv_reindex (coverLift (gap n)) (f n) x v

theorem pull_dr (h a b : ℝ) (hab : a < b) (index gap : ℕ → ℕ) (f : ℕ → Point → ℝ) :
    (operators h index a b hab).dr (pull gap f) =
      pull gap ((operators h (fun n => index n + gap n) a b hab).dr f) := by
  funext n x
  change fderiv ℝ (pull gap f n) x (1,(0,0)) +
      radialFrequency h index n * (RadialPullback.radialJacobian (ChartScales.radialExponent h) x.1
        *
        fderiv ℝ (pull gap f n) x (0,(0,TorusInverse.vector .radial))) =
    fderiv ℝ (f n) (coverLift (gap n) x) (1,(0,0)) +
      radialFrequency h (fun n => index n + gap n) n *
        (RadialPullback.radialJacobian (ChartScales.radialExponent h) x.1 *
          fderiv ℝ (f n) (coverLift (gap n) x) (0,(0,TorusInverse.vector .radial)))
  rw [pull_fderiv, pull_fderiv, coverLift_eR, coverLift_vR, map_smul, radialFrequency_add]
  simp only [smul_eq_mul]
  ring

theorem pull_dz (h a b : ℝ) (hab : a < b) (index gap : ℕ → ℕ) (f : ℕ → Point → ℝ) :
    (operators h index a b hab).dz (pull gap f) =
      pull gap ((operators h (fun n => index n + gap n) a b hab).dz f) := by
  funext n x
  change ChartScales.epsilon h n * fderiv ℝ (pull gap f n) x (0,((0,1),0)) =
    ChartScales.epsilon h n * fderiv ℝ (f n) (coverLift (gap n) x) (0,((0,1),0))
  rw [pull_fderiv, coverLift_eZ]

theorem pull_slowTime (h a b : ℝ) (hab : a < b) (index gap : ℕ → ℕ) (f : ℕ → Point → ℝ) :
    (operators h index a b hab).slowTime (pull gap f) =
      pull gap ((operators h (fun n => index n + gap n) a b hab).slowTime f) := by
  funext n x
  change -(ChartScales.epsilon h n * fderiv ℝ (pull gap f n) x (0,((1,0),0))) =
    -(ChartScales.epsilon h n * fderiv ℝ (f n) (coverLift (gap n) x) (0,((1,0),0)))
  rw [pull_fderiv, coverLift_eT]

theorem pull_fastTime (h a b : ℝ) (hab : a < b) (index gap : ℕ → ℕ) (f : ℕ → Point → ℝ) :
    (operators h index a b hab).fastTime (pull gap f) =
      pull gap ((operators h (fun n => index n + gap n) a b hab).fastTime f) := by
  funext n x
  change fastCoefficient h index n * fderiv ℝ (pull gap f n) x (0,(0,TorusInverse.vector
    .temporal)) =
    fastCoefficient h (fun n => index n + gap n) n *
      fderiv ℝ (f n) (coverLift (gap n) x) (0,(0,TorusInverse.vector .temporal))
  rw [pull_fderiv, coverLift_vT, map_smul, fastCoefficient_add]
  simp only [smul_eq_mul]
  ring

theorem pull_time (h a b : ℝ) (hab : a < b) (index gap : ℕ → ℕ) (f : ℕ → Point → ℝ) :
    (operators h index a b hab).time (pull gap f) =
      pull gap ((operators h (fun n => index n + gap n) a b hab).time f) := by
  rw [MeanIncrementBounds.Operators.time, pull_slowTime, pull_fastTime]
  rfl

theorem pull_native_derivatives (h a b : ℝ) (hab : a < b)
    {index : ℕ → ℕ} (hi : ∀ n, index n ≤ ChartScales.nativeIndex h n) (f : ℕ → Point → ℝ) :
    let gap := fun n => ChartScales.nativeIndex h n - index n
    (operators h index a b hab).dr (pull gap f) =
        pull gap ((BaseContextAssembly.operators h a b hab).dr f) ∧
    (operators h index a b hab).dz (pull gap f) =
        pull gap ((BaseContextAssembly.operators h a b hab).dz f) ∧
    (operators h index a b hab).slowTime (pull gap f) =
        pull gap ((BaseContextAssembly.operators h a b hab).slowTime f) ∧
    (operators h index a b hab).fastTime (pull gap f) =
        pull gap ((BaseContextAssembly.operators h a b hab).fastTime f) ∧
    (operators h index a b hab).time (pull gap f) =
        pull gap ((BaseContextAssembly.operators h a b hab).time f) := by
  dsimp only
  have he : (fun n => index n + (ChartScales.nativeIndex h n - index n)) = ChartScales.nativeIndex
    h :=
    funext (fun n => Nat.add_sub_of_le (hi n))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [he, operators_native] using pull_dr h a b hab index (fun n =>
    ChartScales.nativeIndex h n - index n) f
  · simpa only [he, operators_native] using pull_dz h a b hab index (fun n =>
    ChartScales.nativeIndex h n - index n) f
  · simpa only [he, operators_native] using pull_slowTime h a b hab index (fun n =>
    ChartScales.nativeIndex h n - index n) f
  · simpa only [he, operators_native] using pull_fastTime h a b hab index (fun n =>
    ChartScales.nativeIndex h n - index n) f
  · simpa only [he, operators_native] using pull_time h a b hab index (fun n =>
    ChartScales.nativeIndex h n - index n) f

theorem coverLift_radialField (h a b : ℝ) (hab : a < b) (index gap : ℕ → ℕ) (n : ℕ) (x : Point) :
    coverLift (gap n) ((operators h index a b hab).eR +
      ((operators h index a b hab).radialFrequency n * (operators h index a b hab).radialProfile x)
        •
        (operators h index a b hab).vR) =
    (operators h (fun m => index m + gap m) a b hab).eR +
      ((operators h (fun m => index m + gap m) a b hab).radialFrequency n *
        (operators h (fun m => index m + gap m) a b hab).radialProfile (coverLift (gap n) x)) •
        (operators h (fun m => index m + gap m) a b hab).vR := by
  change coverLift (gap n) ((1,(0,0)) + (radialFrequency h index n *
      RadialPullback.radialJacobian (ChartScales.radialExponent h) x.1) •
      (0,(0,TorusInverse.vector .radial))) =
    (1,(0,0)) + (radialFrequency h (fun m => index m + gap m) n *
      RadialPullback.radialJacobian (ChartScales.radialExponent h) x.1) •
      (0,(0,TorusInverse.vector .radial))
  rw [map_add, map_smul, coverLift_eR, coverLift_vR, smul_smul, radialFrequency_add]
  congr 2
  ring

theorem coverLift_axialField (h a b : ℝ) (hab : a < b) (index gap : ℕ → ℕ) (n : ℕ) :
    coverLift (gap n) ((operators h index a b hab).epsilon n • (operators h index a b hab).eZ) =
    (operators h (fun m => index m + gap m) a b hab).epsilon n •
      (operators h (fun m => index m + gap m) a b hab).eZ := by
  change coverLift (gap n) (ChartScales.epsilon h n • (0,((0,1),0))) =
    ChartScales.epsilon h n • (0,((0,1),0))
  rw [map_smul, coverLift_eZ]

theorem coverLift_timeField (h a b : ℝ) (hab : a < b) (index gap : ℕ → ℕ) (n : ℕ) :
    coverLift (gap n) ((operators h index a b hab).fastCoefficient n • (operators h index a b
      hab).vT -
      (operators h index a b hab).epsilon n • (operators h index a b hab).eT) =
    (operators h (fun m => index m + gap m) a b hab).fastCoefficient n •
      (operators h (fun m => index m + gap m) a b hab).vT -
    (operators h (fun m => index m + gap m) a b hab).epsilon n •
      (operators h (fun m => index m + gap m) a b hab).eT := by
  change coverLift (gap n) (fastCoefficient h index n • (0,(0,TorusInverse.vector .temporal)) -
      ChartScales.epsilon h n • (0,((1,0),0))) =
    fastCoefficient h (fun m => index m + gap m) n • (0,(0,TorusInverse.vector .temporal)) -
      ChartScales.epsilon h n • (0,((1,0),0))
  rw [map_sub, map_smul, map_smul, coverLift_vT, coverLift_eT, smul_smul, fastCoefficient_add]
  rw [mul_comm (fastCoefficient h index n)]

theorem pull_eq_coverPull (k : ℕ) (f : Point → ℝ) :
    (fun x => f (coverLift k x)) =
      MeanChartCompatibility.coverPull 1 (ContinuousLinearMap.id ℝ Plane) k 1 f := by
  funext x
  change f (x.1,(x.2.1,CommonCoverSolve.coverPower k x.2.2)) =
    1 * f (1 * x.1,(x.2.1,TemporalMeanUpdate.coverMap k x.2.2))
  rw [MeanChartCompatibility.coverMap_eq_coverPower]
  simp

theorem pull_periodic (k : ℕ) {f : Point → ℝ} (hf : PressureStream.TorusPeriodicLift f) :
    PressureStream.TorusPeriodicLift (fun x => f (coverLift k x)) := by
  rw [pull_eq_coverPull]
  exact MeanChartCompatibility.coverPull_periodic _ _ _ _ hf

theorem pull_periodicOn (k : ℕ) {U : Set Plane} {f : Point → ℝ}
    (hf : PhysicalMeanDomain.PeriodicOn U f) :
    PhysicalMeanDomain.PeriodicOn U (fun x => f (coverLift k x)) := by
  intro R p hp Y z
  change f (R,(p,CommonCoverSolve.coverPower k (Y + TorusAverages.latticePoint z))) =
    f (R,(p,CommonCoverSolve.coverPower k Y))
  rw [map_add, CommonCoverSolve.coverPower_lattice]
  exact hf R p hp (CommonCoverSolve.coverPower k Y) (CommonCoverSolve.coverIndex k z)

theorem coverLift_norm_le {k K : ℕ} (hk : k ≤ K) :
    ‖(coverLift k : Point →L[ℝ] Point)‖ ≤ 1 + CommonCoverSolve.coveringBound K := by
  have hC : 1 ≤ 1 + CommonCoverSolve.coveringBound K := by
    linarith [CommonCoverSolve.coveringBound_pos K]
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hC)
  intro x
  have hxx : ‖x‖ ≤ (1 + CommonCoverSolve.coveringBound K) * ‖x‖ :=
    le_mul_of_one_le_left (norm_nonneg _) hC
  change max ‖x.1‖ (max ‖x.2.1‖ ‖CommonCoverSolve.coverPower k x.2.2‖) ≤ _
  apply max_le ((norm_fst_le x).trans hxx)
  apply max_le (((norm_fst_le x.2).trans (norm_snd_le x)).trans hxx)
  calc
    _ ≤ ‖(CommonCoverSolve.coverPower k : Plane →L[ℝ] Plane)‖ * ‖x.2.2‖ :=
      (CommonCoverSolve.coverPower k : Plane →L[ℝ] Plane).le_opNorm _
    _ ≤ CommonCoverSolve.coveringBound K * ‖x‖ :=
      mul_le_mul (CommonCoverSolve.coveringNorm_le_bound hk) ((norm_snd_le x.2).trans (norm_snd_le
        x))
        (norm_nonneg _) (CommonCoverSolve.coveringBound_pos K).le
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end Cover

section CoverClass

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  (U : LocalSignedRequest.SlowRegion (2*F.data.h))

@[simp] theorem coverLift_mem (k : ℕ) (x : Point) :
    coverLift k x ∈ (BaseContextAssembly.nativeStrip W U).domain ↔
      x ∈ (BaseContextAssembly.nativeStrip W U).domain := Iff.rfl

@[simp] theorem coverLift_delta (k : ℕ) (x : Point) :
    (BaseContextAssembly.nativeStrip W U).delta (coverLift k x) =
      (BaseContextAssembly.nativeStrip W U).delta x := rfl

@[simp] theorem coverLift_zeta (k : ℕ) (x : Point) :
    (BaseContextAssembly.nativeStrip W U).zeta (coverLift k x) =
      (BaseContextAssembly.nativeStrip W U).zeta x := rfl

@[simp] theorem coverLift_growth (k n : ℕ) (x : Point) :
    (BaseContextAssembly.nativeStrip W U).growth n (coverLift k x) =
      (BaseContextAssembly.nativeStrip W U).growth n x := rfl

/-- True covering norms produce one finite-jet constant before the band is
chosen. No isometry property is assumed of the cover. -/
theorem class_pull {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {gap : ℕ → ℕ} {K : ℕ} (hgap : ∀ n, gap n ≤ K)
    {w : ℕ → Point → ℝ} {alpha : ℝ} {f : ℕ → Point → E}
    (hf : MemClass (BaseContextAssembly.nativeStrip W U) w alpha f)
    (hw : ∀ n x, x ∈ (BaseContextAssembly.nativeStrip W U).domain →
      w n (coverLift (gap n) x) = w n x) :
    MemClass (BaseContextAssembly.nativeStrip W U) w alpha (pull gap f) := by
  let s := BaseContextAssembly.nativeStrip W U
  have hc : 1 ≤ 1 + CommonCoverSolve.coveringBound K := by
    linarith [CommonCoverSolve.coveringBound_pos K]
  have ht := CommonCoverClass.memClass_affine_transport s s (w := w) (v := w) (α := alpha) (f := f)
    hf id
    (fun n => (coverLift (gap n) : Point →L[ℝ] Point)) (fun _ => 0)
    (fun n x hx => by simp only [zero_add]; exact (coverLift_mem W U (gap n) x).mpr hx)
    (fun n x hx => by simp only [id_eq, zero_add]; exact hw n x hx)
    (Ce := 1) (Cg := 1) (CL := 1 + CommonCoverSolve.coveringBound K)
    zero_le_one le_rfl hc 1 0
    (fun n => by simp only [id_eq, one_mul]; exact le_rfl)
    (fun n x hx => by simp only [id_eq, zero_add, pow_one, one_mul]; exact le_rfl)
    (fun n x hx => by simpa only [pow_zero, mul_one] using coverLift_norm_le (hgap n))
  simp only [id_eq, zero_add] at ht
  exact ht

theorem unweighted_pull {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {gap : ℕ → ℕ} {K : ℕ} (hgap : ∀ n, gap n ≤ K) {alpha : ℝ} {f : ℕ → Point → E}
    (hf : UnweightedClass (BaseContextAssembly.nativeStrip W U) alpha f) :
    UnweightedClass (BaseContextAssembly.nativeStrip W U) alpha (pull gap f) :=
  class_pull W U hgap hf (fun _ _ _ => rfl)

theorem mean_pull {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {gap : ℕ → ℕ} {K : ℕ} (hgap : ∀ n, gap n ≤ K) {alpha : ℝ} {f : ℕ → Point → E}
    (hf : MeanClass (BaseContextAssembly.nativeStrip W U) alpha f) :
    MeanClass (BaseContextAssembly.nativeStrip W U) alpha (pull gap f) :=
  class_pull W U hgap hf (fun _ _ _ => rfl)

theorem temporalAtIndex_class {index : ℕ → ℕ} {K : ℕ} (hi : IndexBounds F.data.h index K)
    {alpha : ℝ} {f : ℕ → Point → ℝ}
    (hf : MeanClass (BaseContextAssembly.nativeStrip W U) alpha
      (fun n => TemporalMeanUpdate.desiredIncrement F.data.h n (f n))) :
    MeanClass (BaseContextAssembly.nativeStrip W U) alpha
      (fun n => MeanChartCompatibility.temporalAtIndex F.data.h n (index n) (f n)) :=
  MeanChartCompatibility.meanClass_temporalAtIndex_of_native _ index K hi.native_le_add hf

end CoverClass

section ActualContext

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ)

/-- Same actual base and stress; only the graph's integer index changes. -/
noncomputable def context (index : ℕ → ℕ) : CorrectionState.Context Point :=
  { BaseContextAssembly.nativeContext H v upper B with
    operators := operators F.data.h index (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W)
      (PrimaryTargetBounds.radii_ordered W) }

@[simp] theorem context_base (index : ℕ → ℕ) :
    (context H v upper B index).base = (BaseContextAssembly.nativeContext H v upper B).base := rfl

@[simp] theorem context_virtualTheta (index : ℕ → ℕ) :
    (context H v upper B index).virtualTheta = (BaseContextAssembly.nativeContext H v upper
      B).virtualTheta := rfl

@[simp] theorem context_virtualAxial (index : ℕ → ℕ) :
    (context H v upper B index).virtualAxial = (BaseContextAssembly.nativeContext H v upper
      B).virtualAxial := rfl

theorem context_native : context H v upper B (ChartScales.nativeIndex F.data.h) =
    BaseContextAssembly.nativeContext H v upper B := rfl

theorem context_operator_bounds (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {index : ℕ → ℕ} (hi : ∀ n, index n ≤ ChartScales.nativeIndex F.data.h n) :
    MeanIncrementBounds.OperatorBounds (BaseContextAssembly.nativeStrip W U)
      (context H v upper B index).operators ChartScales.kappa :=
  operator_bounds F.data.h_pos.le U hi (PrimaryTargetBounds.leftRadius_pos W)
    (PrimaryTargetBounds.radii_ordered W) (div_pos (FinalSlowBase.edgeExponent_pos W) (by
      norm_num)) zero_lt_one

theorem context_base_bounds (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (index : ℕ → ℕ) :
    MeanIncrementBounds.BaseBounds (BaseContextAssembly.nativeStrip W U) (context H v upper B
      index).base :=
  BaseContextAssembly.native_base_bounds H v upper B U

theorem context_base_smooth (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (index : ℕ → ℕ) :
    MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain U.carrier) (context H v upper
      B index).base :=
  BaseContextAssembly.native_base_smooth H v upper B U

theorem context_operators_local (U : Set Plane) (index : ℕ → ℕ) :
    LocalRankDefect.LocalOperators U (context H v upper B index).operators := by
  have hn := BaseContextAssembly.native_operators_local H v upper B U
  exact ⟨hn.radius_eq, hn.radialProfile⟩

theorem context_isSlow (U : Set Plane) (index : ℕ → ℕ) :
    LocalRankDefect.IsSlowOn U (context H v upper B index).base.radial ∧
    LocalRankDefect.IsSlowOn U (context H v upper B index).base.angular ∧
    LocalRankDefect.IsSlowOn U (context H v upper B index).base.axial :=
  ⟨BaseContextAssembly.native_radial_isSlow H v upper B U,
    BaseContextAssembly.native_angular_isSlow H v upper B U,
    BaseContextAssembly.native_axial_isSlow H v upper B U⟩

theorem context_matches_physical (index : ℕ → ℕ) (n : ℕ) :
    PhysicalResidualTZ.MatchesAtTZ (context H v upper B index).operators
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) F.data.h (index n)) n :=
  operators_match_physical _ _ _ _ _ _

theorem context_radial_physical (index : ℕ → ℕ) (n : ℕ) (x : Point) :
    (context H v upper B index).base.radial n x = ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (BaseContextAssembly.physicalPoint F.data.h n x) 0 := rfl

theorem context_angular_physical (index : ℕ → ℕ) (n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1) (hR : 0 < x.1) :
    (context H v upper B index).base.angular n x = ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (BaseContextAssembly.physicalPoint F.data.h n x) 1 :=
  BaseContextAssembly.angularBase_physical H v upper B n hT hR

theorem context_axial_physical (index : ℕ → ℕ) (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    (context H v upper B index).base.axial n x = ChartScales.Q n ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (BaseContextAssembly.physicalPoint F.data.h n x) 2 :=
  BaseContextAssembly.axialBase_physical H v upper B n hT

theorem context_stress_properties (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    (index : ℕ → ℕ) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun x => ((context H v upper B index).virtualTheta n x,
      (context H v upper B index).virtualAxial n x)) (PhysicalMeanDomain.slowDomain U.carrier) ∧
    PhysicalMeanDomain.PeriodicOn U.carrier ((context H v upper B index).virtualTheta n) ∧
    PhysicalMeanDomain.PeriodicOn U.carrier ((context H v upper B index).virtualAxial n) ∧
    LocalSignedRequest.MovingSupport (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W)
      (2 * F.data.h) U.carrier ((context H v upper B index).virtualTheta n) ∧
    LocalSignedRequest.MovingSupport (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W)
      (2 * F.data.h) U.carrier ((context H v upper B index).virtualAxial n) :=
  BaseContextAssembly.native_stress_properties H v upper B U n

theorem context_base_cover (index : ℕ → ℕ) (k n : ℕ) (x : Point) :
    HarmonicResidual.contextBase (context H v upper B index) n (coverLift k x) =
      HarmonicResidual.contextBase (context H v upper B index) n x := rfl

theorem context_virtualTheta_cover (index : ℕ → ℕ) (k n : ℕ) (x : Point) :
    (context H v upper B index).virtualTheta n (coverLift k x) =
      (context H v upper B index).virtualTheta n x := rfl

theorem context_virtualAxial_cover (index : ℕ → ℕ) (k n : ℕ) (x : Point) :
    (context H v upper B index).virtualAxial n (coverLift k x) =
      (context H v upper B index).virtualAxial n x := rfl

/-- Context coherence is proved on every free auxiliary lift point. -/
theorem contextOn_add (index gap : ℕ → ℕ) (U : Set Point) (n : ℕ) :
    PhysicalResidualNaturality.ContextOn U (coverLift (gap n)) 1 1
      (context H v upper B index) (context H v upper B (fun m => index m + gap m)) n n := by
  constructor
  · constructor
    · intro x hx
      simp only [one_smul]
      exact coverLift_radialField F.data.h _ _
        (PrimaryTargetBounds.radii_ordered W) index gap n x
    · intro x hx
      simp only [one_smul]
      exact coverLift_axialField F.data.h _ _
        (PrimaryTargetBounds.radii_ordered W) index gap n
    · intro x hx
      simp only [one_mul, one_smul]
      exact coverLift_timeField F.data.h _ _
        (PrimaryTargetBounds.radii_ordered W) index gap n
    · intro x hx
      exact (one_mul x.1).symm
    · simp only [mul_one, one_mul]
      rfl
  · constructor <;> intro x hx <;> simp only [one_mul] <;> rfl
  · intro x hx
    simp only [one_mul]
    rfl
  · intro x hx
    simp only [one_mul]
    rfl

theorem contextOn_native {index : ℕ → ℕ} (hi : ∀ n, index n ≤ ChartScales.nativeIndex F.data.h n)
    (U : Set Point) (n : ℕ) :
    PhysicalResidualNaturality.ContextOn U
      (coverLift (ChartScales.nativeIndex F.data.h n - index n)) 1 1
      (context H v upper B index) (BaseContextAssembly.nativeContext H v upper B) n n := by
  have he : (fun m => index m + (ChartScales.nativeIndex F.data.h m - index m)) =
      ChartScales.nativeIndex F.data.h := funext (fun m => Nat.add_sub_of_le (hi m))
  have hc := contextOn_add H v upper B index (fun m => ChartScales.nativeIndex F.data.h m - index
    m) U n
  rwa [he, context_native] at hc

theorem context_stress_classes (hcone : LeadingStressWeights.FullTrueCone v)
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (index : ℕ → ℕ) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 1 (context H v upper B index).virtualTheta ∧
    MeanClass (BaseContextAssembly.nativeStrip W U) 1 (context H v upper B index).virtualAxial :=
  BaseStressClasses.virtualStress_components H v hcone upper B U

theorem context_higher_stress_classes (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (index : ℕ
  → ℕ) :
    MeanClass (BaseContextAssembly.nativeStrip W U) 2
      (fun n x => (context H v upper B index).virtualTheta n x -
        (BaseContextAssembly.leadingVirtualStress H v n x).1) ∧
    MeanClass (BaseContextAssembly.nativeStrip W U) 2
      (fun n x => (context H v upper B index).virtualAxial n x -
        (BaseContextAssembly.leadingVirtualStress H v n x).2) :=
  BaseStressClasses.higherStress_components H v upper B U

theorem context_primaryCoefficients_match
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (index : ℕ → ℕ)
    {D : PhaseJetBounds.Domain ℕ Slow} (P : PrimaryPulseBounds.PhaseConstruction D)
    (hF : P.phase.F = BaseContextAssembly.frequencySlow H v upper B)
    (hG : P.phase.G = BaseContextAssembly.axialSlow H v upper B)
    (chi : ℕ → Point × ℝ → PhaseCalculus.Slot)
    (hchi : ∀ n x, (chi n x).1 = BaseContextAssembly.slowCoordinates x.1)
    (amplitude : ℕ → Point × ℝ → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → Point × ℝ → ℂ) (frequency : ℕ → ℝ) :
    PrimaryResidualClass.Matches (BaseContextAssembly.nativeStrip W U) (context H v upper B index)
      (PrimaryMaterialDefect.coefficients P (BaseContextAssembly.radialSlow H v upper B)
        chi amplitude pressure frequency) := by
  have hm := BaseContextAssembly.primaryCoefficients_match H v upper B U P hF hG chi hchi
    amplitude pressure frequency
  exact ⟨hm.epsilon, hm.radius, hm.base⟩

end ActualContext

end NavierStokes.CommonBaseContext
