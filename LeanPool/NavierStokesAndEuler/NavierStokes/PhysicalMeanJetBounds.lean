/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalPhysicalCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.VariableGaugeMean
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-!
# Physical jets of coherent mean fields

The graph below is the actual common-cover cylindrical graph, with slow order
`(T,Z)`.  It is identified with `VariableGaugeMean.physicalToChartTZ`, and its
derivative estimates are derived from the actual physical graph and radius map.
The final restriction is a single coherent physical field, not a sum over bands.
-/

noncomputable section

namespace NavierStokes.PhysicalMeanJetBounds

open Set Function Filter ProblemStatement PhysicalWaveSum LocalPhysicalCopyBounds
open scoped Topology ContDiff BigOperators

abbrev Point := PressureStream.Lift PhysicalGraphBounds.Plane

/-- The unscaled physical cylindrical point with the actual auxiliary graph. -/
noncomputable def physicalPoint (h : ℝ) (w : SpaceTime) : Point :=
  (PhysicalClassBounds.cartesianRadius (PhysicalGraphBounds.radialProjection w),
    ((1 - w.1, w.2 2), PhysicalGraphBounds.radialProfile (ChartScales.radialExponent h)
      (PhysicalGraphBounds.radialProjection w) + w.1 • PhysicalGraphBounds.timeDirection))

/-- A bounded-gap common-cover graph, in the mean-field coordinate order. -/
noncomputable def graph (h : ℝ) (n d : ℕ) : SpaceTime → Point :=
  PhysicalClassBounds.cylindricalMap ∘ commonLift h n d

theorem cartesianRadius_smul {c : ℝ} (hc : 0 ≤ c) (y : PhysicalGraphBounds.Plane) :
    PhysicalClassBounds.cartesianRadius (c • y) = c * PhysicalClassBounds.cartesianRadius y := by
  unfold PhysicalClassBounds.cartesianRadius
  change Real.sqrt ((c * y.1) ^ 2 + (c * y.2) ^ 2) = c * Real.sqrt (y.1 ^ 2 + y.2 ^ 2)
  rw [show (c * y.1) ^ 2 + (c * y.2) ^ 2 = c ^ 2 * (y.1 ^ 2 + y.2 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem physicalToChartTZ_apply (h : ℝ) (n i : ℕ) (p : Point) :
    VariableGaugeMean.physicalToChartTZ h n i p =
      (MeanChartCompatibility.chartScale n * p.1,
        ((ChartScales.Q n ^ (-1 : ℝ) * p.2.1.1,
          ChartScales.Q n ^ (-CoordinateAlgebra.D h) * p.2.1.2),
          TemporalMeanUpdate.coverMap i p.2.2)) := rfl

/-- Exact identification with the variable-gauge mean chart.  The cover
index is the native index minus the actual common-cover gap. -/
theorem graph_eq_physicalToChartTZ (h : ℝ) (n d : ℕ)
    (hd : d ≤ ChartScales.nativeIndex h n) (w : SpaceTime) :
    graph h n d w = VariableGaugeMean.physicalToChartTZ h n
      (ChartScales.nativeIndex h n - d) (physicalPoint h w) := by
  have haux := congrArg Prod.snd (commonLift_formula h n d hd w)
  change (CommonCoverSolve.coverPower d).symm (PhysicalGraphBounds.nativeGraph h n w) = _ at haux
  rw [graph, Function.comp_apply, PhysicalClassBounds.cylindricalMap_commonLift,
    physicalToChartTZ_apply, physicalPoint]
  apply Prod.ext
  · change PhysicalClassBounds.cartesianRadius
      (ChartScales.Q n ^ (-(1 / 2 : ℝ)) • PhysicalGraphBounds.radialProjection w) = _
    exact cartesianRadius_smul (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).le _
  · apply Prod.ext
    · ext <;> simp only [Real.rpow_neg_one, div_eq_mul_inv]
      ring
    · rw [haux, MeanChartCompatibility.coverMap_eq_coverPower, CommonCoverSolve.coverPower_apply]

theorem graph_smoothAt {a b : ℝ} (ha : 0 < a) (h : ℝ) (n d : ℕ)
    {w : SpaceTime} (hw : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b) :
    ContDiffAt ℝ ∞ (graph h n d) w := by
  have hx := PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hw
  exact ((PhysicalClassBounds.cylindricalMap_smooth ha).contDiffAt
    ((PhysicalClassBounds.cylindricalDomain_open a b).mem_nhds hx)).comp w
      (commonLift_smoothAt h n d (PhysicalGraphBounds.scaledRadial_ne_zero
        (PhysicalGraphBounds.annulus_axisFree ha hw)))

/-! ## Selection of a comparable dyadic band -/

theorem Q_eq_half_pow (n : ℕ) : ChartScales.Q n = (1 / 2 : ℝ) ^ n := by
  change (2 : ℝ) ^ (-(n : ℝ)) = _
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp only [one_div, inv_pow]

theorem Q_add (n k : ℕ) : ChartScales.Q (n + k) = ChartScales.Q n * ChartScales.Q k := by
  simp only [Q_eq_half_pow, pow_add]

/-- Every sufficiently small positive physical scale has a comparable
band above any prescribed cutoff.  No summation over bands is introduced. -/
theorem exists_comparable_band (N : ℕ) {q : ℝ} (hq : 0 < q) (hsmall : q ≤ ChartScales.Q N) :
    ∃ n : ℕ, N ≤ n ∧ q ≤ ChartScales.Q n ∧ ChartScales.Q n < 2 * q := by
  have hQN := ChartScales.Q_pos N
  obtain ⟨k, hlo, hhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hq hQN) ((div_le_one hQN).mpr hsmall)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N + k, Nat.le_add_right _ _, ?_, ?_⟩
  · rw [Q_add, Q_eq_half_pow k]
    exact (div_le_iff₀ hQN).mp hhi |>.trans_eq (mul_comm _ _)
  · have hh := (lt_div_iff₀ hQN).mp hlo
    rw [pow_succ] at hh
    rw [Q_add, Q_eq_half_pow k]
    nlinarith

/-! ## The local, nonoscillatory graph estimate -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem common_stripped_physical_bound_local {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (g e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
        |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : LiftPoint → E, SmoothNear f (commonLift h n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (f ∘ commonLift h n d) w‖ ≤
        C * q ^ (g - (PhysicalGraphBounds.graphLoss m + 1)) := by
  obtain ⟨C, hC, hb⟩ := common_stripped_physical_bound (E := E) (b := b)
    hh hh1 ha Δ m g e A hA
  refine ⟨C, hC, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi f hf hjet
  obtain ⟨F, hF, he⟩ := hf.exists_global_germ
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha
    hann)
  have he' := he.comp_tendsto (commonLift_smoothAt h n d haxis).continuousAt
  rw [iteratedFDeriv_eq_of_eventuallyEq he' m]
  apply hb n hn d hd w hann ht q hq hlo hhi F hF
  intro i hi
  rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
  exact hjet i hi

noncomputable def bandField (h : ℝ) (n d : ℕ) (degree : ℝ) (f : Point → E) : SpaceTime → E :=
  fun w => (ChartScales.Q n ^ (-degree)) • f (graph h n d w)

noncomputable def loss (degree : ℝ) (m : ℕ) : ℝ :=
  PhysicalGraphBounds.graphLoss m + 1 + degree

/-- Actual cylindrical mean-field restriction.  Both graph stages are
differentiated using their proved jet bounds.  Raw input smoothness is local. -/
theorem bandField_jet_bound {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (gain degree e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
        |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : Point → E, SmoothNear f (graph h n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (graph h n d w)‖ ≤
        A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (bandField h n d degree f) w‖ ≤
        C * q ^ (gain - loss degree m) := by
  obtain ⟨B, hB, hBj⟩ := PhysicalClassBounds.cylindricalMap_positiveJets (b := b) ha m
  let A' : ℝ := (m.factorial : ℝ) * A * B ^ m
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  obtain ⟨C, hC, hb⟩ := common_stripped_physical_bound_local (E := E) (b := b)
    hh hh1 ha Δ m (gain - degree) e A' hA'
  refine ⟨C, hC, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi f hf hjet
  obtain ⟨F, hF, he⟩ := hf.exists_global_germ
  have hx := PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hann
  have hg : ContDiffOn ℝ ∞ (F ∘ PhysicalClassBounds.cylindricalMap)
      (PhysicalClassBounds.cylindricalDomain a b) :=
    hF.comp_contDiffOn (PhysicalClassBounds.cylindricalMap_smooth ha)
  let u : LiftPoint → E := fun x => (ChartScales.Q n ^ (-degree)) • F
    (PhysicalClassBounds.cylindricalMap x)
  have hu : SmoothNear u (commonLift h n d w) :=
    SmoothNear.of_open (PhysicalClassBounds.cylindricalDomain_open a b)
      (hg.const_smul _) hx
  have he' : bandField h n d degree f =ᶠ[𝓝 w] u ∘ commonLift h n d := by
    filter_upwards [he.comp_tendsto (graph_smoothAt ha h n d hann).continuousAt] with z hz
    exact congrArg (fun v => (ChartScales.Q n ^ (-degree)) • v) hz
  rw [iteratedFDeriv_eq_of_eventuallyEq he' m]
  have hbound := hb n hn d hd w hann ht q hq hlo hhi u hu
  have hqN := ChartScales.Q_pos n
  have hSN := ChartScales.S_pos (show 1 ≤ n by omega)
  have hab : 0 ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by positivity
  have hFjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F (graph h n d w)‖ ≤
      A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by
    intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
    exact hjet i hi
  have hcomp := PhysicalClassBounds.composition_jet_bound hF
    (PhysicalClassBounds.cylindricalDomain_open a b) (PhysicalClassBounds.cylindricalMap_smooth ha)
    hx m hab hB hFjet (hBj _ hx)
  have huc : ∀ i ≤ m, ‖iteratedFDeriv ℝ i u (commonLift h n d w)‖ ≤
      A' * ChartScales.Q n ^ (gain - degree) * ChartScales.S n ^ e := by
    intro i hi
    have hnear := hg.contDiffAt ((PhysicalClassBounds.cylindricalDomain_open a b).mem_nhds hx)
    change ‖iteratedFDeriv ℝ i (fun x => (ChartScales.Q n ^ (-degree)) •
      (F ∘ PhysicalClassBounds.cylindricalMap) x) (commonLift h n d w)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hnear.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)),
      norm_smul (ChartScales.Q n ^ (-degree))
        (iteratedFDeriv ℝ i (F ∘ PhysicalClassBounds.cylindricalMap) (commonLift h n d w)),
      Real.norm_of_nonneg (Real.rpow_pos_of_pos hqN (-degree)).le]
    calc
      _ ≤ ChartScales.Q n ^ (-degree) * ((m.factorial : ℝ) *
          (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m) :=
        mul_le_mul_of_nonneg_left (hcomp i hi) (Real.rpow_pos_of_pos hqN _).le
      _ = _ := by dsimp [A']; rw [Real.rpow_sub hqN, Real.rpow_neg hqN.le]; ring
  convert! hbound huc using 1
  congr 2
  unfold loss
  ring

/-! ## The actual normalized slow coordinate -/

theorem physicalQ_eq (h : ℝ) (w : SpaceTime) :
    physicalQ h w = SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2) := rfl

theorem graph_slow (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    (graph h n d w).2.1 =
      ((1 - w.1) / ChartScales.Q n, ChartScales.Q n ^ (-CoordinateAlgebra.D h) * w.2 2) := by
  rw [graph, Function.comp_apply, PhysicalClassBounds.cylindricalMap_commonLift]

theorem graph_slow_continuous (h : ℝ) (n d : ℕ) :
    Continuous (fun w => (graph h n d w).2.1) := by
  simp_rw [graph_slow]
  exact ((continuous_const.sub continuous_fst).div_const _).prodMk
    (continuous_const.mul ((AxisymmetricFields.projection 2).continuous.comp continuous_snd))

theorem graph_radius (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    (graph h n d w).1 = PolarCharts.radius (PhysicalGraphBounds.scaledRadial n w) := by
  rw [graph, Function.comp_apply, PhysicalClassBounds.cylindricalMap_commonLift]
  rfl

theorem graph_radius_continuous (h : ℝ) (n d : ℕ) : Continuous (fun w => (graph h n d w).1) := by
  simp_rw [graph_radius]
  exact PolarCharts.radius_continuous.comp (PhysicalGraphBounds.scaledRadial n).continuous

theorem graph_time_pos (h : ℝ) (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal) :
    0 < (graph h n d w).2.1.1 := by
  rw [graph_slow]
  exact div_pos (sub_pos.mpr hw) (ChartScales.Q_pos n)

theorem graph_q_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (n d : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal) :
    SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1 = physicalQ h w / ChartScales.Q n
      := by
  rw [graph_slow, physicalQ_eq]
  have hp : ChartScales.Q n ^ (-CoordinateAlgebra.D h) =
      (ChartScales.Q n)⁻¹ ^ CoordinateAlgebra.D h := by
    rw [Real.rpow_neg (ChartScales.Q_pos n).le, Real.inv_rpow (ChartScales.Q_pos n).le]
  have he := SimilarityHomogeneity.coordinateQ_scale_h (z := w.2 2) hh hh1
    (inv_pos.mpr (ChartScales.Q_pos n)) (sub_pos.mpr hw)
  simpa only [hp, div_eq_mul_inv, mul_comm] using he

theorem graph_slow_normalized {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hlo : physicalQ h w / 2 ≤ ChartScales.Q n) (hhi : ChartScales.Q n ≤ 2 * physicalQ h w) :
    (graph h n d w).2.1 ∈ PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 := by
  refine ⟨graph_time_pos h n d hw, ?_⟩
  rw [graph_q_eq hh hh1 n d hw]
  have hQ := ChartScales.Q_pos n
  have hq := physicalQ_pos hh hh1 hw
  constructor
  · apply (lt_div_iff₀ hQ).mpr
    nlinarith
  · apply (div_lt_iff₀ hQ).mpr
    nlinarith

theorem graph_length_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (n d : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal) :
    0 < VariableGaugeMean.qLength (2 * h) (graph h n d w).2.1 :=
  VariableGaugeMean.qLength_pos (by linarith) (by linarith) (graph_time_pos h n d hw)

theorem graph_length_continuousAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (n d : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal) :
    ContinuousAt (fun z => VariableGaugeMean.qLength (2 * h) (graph h n d z).2.1) w := by
  have he : ContDiffAt ℝ ∞ (VariableGaugeMean.qLength (2 * h)) (graph h n d w).2.1 :=
    (VariableGaugeMean.qLength_contDiffOn (by linarith : 0 < 2 * h)
    (by linarith : 2 * h < 1)).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds (graph_time_pos h n d hw))
  have ht : Tendsto (fun z : SpaceTime => (graph h n d z).2.1) (𝓝 w)
      (𝓝 (graph h n d w).2.1) := (graph_slow_continuous h n d).continuousAt
  exact he.continuousAt.tendsto.comp ht

theorem graph_length_bounds {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (n d : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal)
    (hlo : physicalQ h w / 2 ≤ ChartScales.Q n) (hhi : ChartScales.Q n ≤ 2 * physicalQ h w) :
    1 / 2 ≤ VariableGaugeMean.qLength (2 * h) (graph h n d w).2.1 ∧
      VariableGaugeMean.qLength (2 * h) (graph h n d w).2.1 ≤ 2 := by
  have hQ := ChartScales.Q_pos n
  have hq := physicalQ_pos hh hh1 hw
  have hlow : (1 / 4 : ℝ) ≤ physicalQ h w / ChartScales.Q n := by
    apply (le_div_iff₀ hQ).mpr
    nlinarith
  have hhigh : physicalQ h w / ChartScales.Q n ≤ (4 : ℝ) := by
    apply (div_le_iff₀ hQ).mpr
    nlinarith
  change 1 / 2 ≤ Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1) ∧ _
  rw [graph_q_eq hh hh1 n d hw]
  constructor
  · exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; exact hlow)
  · change Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1) ≤ 2
    rw [graph_q_eq hh hh1 n d hw]
    exact (Real.sqrt_le_left (by norm_num)).mpr (by norm_num; exact hhigh)

/-! ## One physical field represented in all valid bands -/

/-- Exact chart coherence for the same physical lifted field.  The data do
not define a sum of band fields and contain no physical derivative estimate. -/
structure CoherentFamily (h degree : ℝ) (N Δ : ℕ) (U : Set PhysicalGraphBounds.Plane)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  native : ℕ → Point → E
  physical : Point → E
  gap : ℕ → ℕ
  gap_le : ∀ n ≥ N, gap n ≤ Δ
  gap_native : ∀ n ≥ N, gap n ≤ ChartScales.nativeIndex h n
  coherent : ∀ n ≥ N, ∀ z : Point, 0 < z.2.1.1 →
    (VariableGaugeMean.physicalToChartTZ h n (ChartScales.nativeIndex h n - gap n) z).2.1 ∈ U →
    physical z = (ChartScales.Q n ^ (-degree)) •
      native n (VariableGaugeMean.physicalToChartTZ h n (ChartScales.nativeIndex h n - gap n) z)

noncomputable def CoherentFamily.field {h degree : ℝ} {N Δ : ℕ} {U : Set PhysicalGraphBounds.Plane}
    (D : CoherentFamily h degree N Δ U E) : SpaceTime → E := D.physical ∘ physicalPoint h

variable {h degree a b : ℝ} {N Δ : ℕ} {U : Set PhysicalGraphBounds.Plane}

theorem CoherentFamily.field_eq (D : CoherentFamily h degree N Δ U E)
    (n : ℕ) (hn : N ≤ n) {w : SpaceTime} (hw : w ∈ preterminal)
    (hU : (graph h n (D.gap n) w).2.1 ∈ U) :
    D.field w = bandField h n (D.gap n) degree (D.native n) w := by
  have he := D.coherent n hn (physicalPoint h w) (sub_pos.mpr hw)
    (by simpa only [← graph_eq_physicalToChartTZ h n (D.gap n) (D.gap_native n hn)] using hU)
  simpa only [CoherentFamily.field, Function.comp_apply, bandField,
    ← graph_eq_physicalToChartTZ h n (D.gap n) (D.gap_native n hn)] using he

theorem CoherentFamily.field_germ (D : CoherentFamily h degree N Δ U E)
    (hU : IsOpen U) (n : ℕ) (hn : N ≤ n) {w : SpaceTime} (hw : w ∈ preterminal)
    (hu : (graph h n (D.gap n) w).2.1 ∈ U) :
    D.field =ᶠ[𝓝 w] bandField h n (D.gap n) degree (D.native n) := by
  filter_upwards [preterminal_open.mem_nhds hw,
    (graph_slow_continuous h n (D.gap n)).continuousAt (hU.mem_nhds hu)] with y hy hys
  exact D.field_eq n hn hy hys

/-- Supported native coefficients, stated for an arbitrary normed target.
For real-valued coefficients this is the actual `SupportedGauge` condition. -/
def NativeSupport (h a b : ℝ) (N : ℕ) (U : Set PhysicalGraphBounds.Plane)
    (f : ℕ → Point → E) : Prop :=
  ∀ n ≥ N, ∀ z, z.2.1 ∈ U → f n z ≠ 0 →
    z.1 ∈ Icc (VariableGaugeMean.qLength (2 * h) z.2.1 * a)
      (VariableGaugeMean.qLength (2 * h) z.2.1 * b)

theorem CoherentFamily.native_ratio_on_tsupport (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hU : IsOpen U)
    (hs : NativeSupport h a b N U D.native) (n : ℕ) (hn : N ≤ n)
    {w : SpaceTime} (hw : w ∈ preterminal) (hu : (graph h n (D.gap n) w).2.1 ∈ U)
    (hts : w ∈ tsupport D.field) :
    (graph h n (D.gap n) w).1 /
      VariableGaugeMean.qLength (2 * h) (graph h n (D.gap n) w).2.1 ∈ Icc a b := by
  let V : Set SpaceTime := preterminal ∩ (fun y => (graph h n (D.gap n) y).2.1) ⁻¹' U
  have hV : IsOpen V := preterminal_open.inter (hU.preimage (graph_slow_continuous h n (D.gap n)))
  have hcont := (graph_radius_continuous h n (D.gap n)).continuousAt.div
    (graph_length_continuousAt hh hh1 n (D.gap n) hw) (graph_length_pos hh hh1 n (D.gap n) hw).ne'
  apply closed_property_on_tsupport hV (show w ∈ V from ⟨hw, hu⟩) hcont isClosed_Icc ?_ hts
  intro y hy hne
  have hnative : D.native n (graph h n (D.gap n) y) ≠ 0 := by
    intro he
    apply hne
    rw [D.field_eq n hn hy.1 hy.2, bandField, he, smul_zero]
  have hb := hs n hn _ hy.2 hnative
  have hell := graph_length_pos hh hh1 n (D.gap n) hy.1
  exact ⟨(le_div_iff₀ hell).mpr (by simpa only [mul_comm] using hb.1),
    (div_le_iff₀ hell).mpr (by simpa only [mul_comm] using hb.2)⟩

/-- Native moving-annulus support gives a fixed Cartesian chart annulus
at every supported physical point with a comparable band. -/
theorem CoherentFamily.annulus_on_tsupport (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hs : NativeSupport h a b N U D.native) (n : ℕ) (hn : N ≤ n)
    {w : SpaceTime} (hw : w ∈ preterminal) (hu : (graph h n (D.gap n) w).2.1 ∈ U)
    (hlo : physicalQ h w / 2 ≤ ChartScales.Q n) (hhi : ChartScales.Q n ≤ 2 * physicalQ h w)
    (hts : w ∈ tsupport D.field) :
    PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus (a / 4) (2 * b) := by
  have hratio := D.native_ratio_on_tsupport hh hh1 hU hs n hn hw hu hts
  have hell := graph_length_pos hh hh1 n (D.gap n) hw
  have hlen := graph_length_bounds hh hh1 n (D.gap n) hw hlo hhi
  have hloR := (le_div_iff₀ hell).mp hratio.1
  have hhiR := (div_le_iff₀ hell).mp hratio.2
  have haR : a / 2 ≤ (graph h n (D.gap n) w).1 := by nlinarith [hlen.1]
  have hbR : (graph h n (D.gap n) w).1 ≤ 2 * b := by nlinarith [hlen.2]
  rw [graph_radius] at haR hbR
  refine ⟨?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using
      (PolarCharts.norm_le_radius _).trans hbR
  · change a / 4 ≤ ‖PhysicalGraphBounds.scaledRadial n w‖
    linarith only [haR, PolarCharts.radius_le_two_norm (PhysicalGraphBounds.scaledRadial n w)]

/-- Band-independent native jets after absorbing the actual flat weight. -/
def NativeJets (N : ℕ) (U : Set PhysicalGraphBounds.Plane) (gain : ℝ)
    (f : ℕ → Point → E) : Prop :=
  ∀ m : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∃ e : ℕ, ∀ n ≥ N, ∀ z, z.2.1 ∈ U → ∀ j ≤ m,
    ‖iteratedFDeriv ℝ j (f n) z‖ ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ e

/-- A uniform estimate for the same coherent physical field.  A comparable
band is selected at each point and used through an exact field germ. -/
theorem CoherentFamily.field_jet_bound (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.field w‖ ≤ C * physicalQ h w ^ (gain - loss degree m) := by
  obtain ⟨A, hA, e, hjet⟩ := hj m
  obtain ⟨C, hC, hb⟩ := bandField_jet_bound (E := E) (b := 2 * b)
    hh.le hh1.le (div_pos ha (by norm_num : (0 : ℝ) < 4)) Δ m gain degree e A hA
  refine ⟨C, hC, ?_⟩
  intro w hw ht hsmall
  have hq := physicalQ_pos hh hh1 hw
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq⟩ := exists_comparable_band N hq hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
    have hu := hcover (graph_slow_normalized hh hh1 n (D.gap n) hw hlo hnq.le)
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    rw [iteratedFDeriv_eq_of_eventuallyEq (D.field_germ hU n hn hw hu) m]
    apply hb n (hN.trans hn) (D.gap n) (D.gap_le n hn) w hann ht
      (physicalQ h w) hq hlo hnq.le (D.native n)
    · exact SmoothNear.of_open (PhysicalMeanDomain.slowDomain_open hU) (hsm n hn) hu
    · intro j hjm
      simpa only [Real.rpow_natCast] using hjet n hn _ hu j hjm
  · rw [jet_zero_off_tsupport _ _ hts, norm_zero]
    positivity

theorem CoherentFamily.field_smoothAt (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {w : SpaceTime} (hw : w ∈ preterminal)
    (hsmall : physicalQ h w ≤ ChartScales.Q N) : ContDiffAt ℝ ∞ D.field w := by
  classical
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq⟩ := exists_comparable_band N (physicalQ_pos hh hh1 hw) hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
    have hu := hcover (graph_slow_normalized hh hh1 n (D.gap n) hw hlo hnq.le)
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    have hnative := (hsm n hn).contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hu)
    have hc := (hnative.comp w (graph_smoothAt (div_pos ha (by norm_num : (0 : ℝ) < 4)) h n
      (D.gap n) hann)).const_smul (ChartScales.Q n ^ (-degree))
    exact hc.congr_of_eventuallyEq (D.field_germ hU n hn hw hu)
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hts)

/-! ## The local mean-class consumer -/

theorem NativeJets.of_localBandJets {h α : ℝ} {N : ℕ} {U : Set PhysicalGraphBounds.Plane}
    {ε L : ℕ → ℝ} {f : ℕ → Point → E}
    (hj : PhysicalMeanDomain.LocalBandJets U ε L α f)
    (hε : ∀ n ≥ N, ε n = ChartScales.epsilon h n)
    (hL0 : ∀ n ≥ N, 0 ≤ L n) {C : ℝ} {p : ℕ} (hC : 1 ≤ C)
    (hL : ∀ n ≥ N, L n ≤ C * ChartScales.S n ^ p) :
    NativeJets N U (h * α) f := by
  intro m
  obtain ⟨A, hA, e, hb⟩ := hj m
  refine ⟨A * C ^ e, mul_nonneg hA (pow_nonneg (zero_le_one.trans hC) _), p * e, ?_⟩
  intro n hn x hx j hjm
  have hQ := ChartScales.Q_pos n
  have hpow : ε n ^ α = ChartScales.Q n ^ (h * α) := by
    rw [hε n hn, ChartScales.epsilon, ← Real.rpow_mul (ChartScales.Q_pos n).le]
  calc
    _ ≤ A * ε n ^ α * L n ^ e := hb n x hx j hjm
    _ ≤ A * ε n ^ α * (C * ChartScales.S n ^ p) ^ e :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hL0 n hn) (hL n hn) e)
        (mul_nonneg hA (by rw [hpow]; positivity))
    _ = _ := by rw [hpow, mul_pow, ← pow_mul]; ring

/-- Incoming local band jets of any real class exponent give physical
Cartesian jets of that same coherent field. -/
theorem CoherentFamily.field_jet_bound_of_localBandJets (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {α : ℝ} {ε L : ℕ → ℝ}
    (hj : PhysicalMeanDomain.LocalBandJets U ε L α D.native)
    (hε : ∀ n ≥ N, ε n = ChartScales.epsilon h n)
    (hL0 : ∀ n ≥ N, 0 ≤ L n) {C : ℝ} {p : ℕ} (hC : 1 ≤ C)
    (hL : ∀ n ≥ N, L n ≤ C * ChartScales.S n ^ p) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.field w‖ ≤ K * physicalQ h w ^ (h * α - loss degree m) :=
  D.field_jet_bound hh hh1 ha hab hN hU hcover hsm hs
    (NativeJets.of_localBandJets hj hε hL0 hC hL) m

/-- The open physical region on which the local native hypotheses imply
smoothness, including the zero neighborhood at the spatial axis. -/
noncomputable def physicalDomain (h : ℝ) (N : ℕ) : Set SpaceTime :=
  {w | w ∈ preterminal ∧ physicalQ h w < ChartScales.Q N}

theorem physicalDomain_open {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (N : ℕ) :
    IsOpen (physicalDomain h N) := by
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  exact inter_mem (preterminal_open.mem_nhds hw.1)
    ((physicalQ_smoothAt hh hh1 hw.1).continuousAt (isOpen_Iio.mem_nhds hw.2))

theorem CoherentFamily.field_smooth (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) :
    ContDiffOn ℝ ∞ D.field (physicalDomain h N) := by
  intro w hw
  exact (D.field_smoothAt hh hh1 ha hab hU hcover hsm hs hw.1 hw.2.le).contDiffWithinAt

@[simp] theorem loss_velocity (h : ℝ) (m : ℕ) :
    loss (CoordinateAlgebra.A h) m = PhysicalGraphBounds.graphLoss m + 1 + CoordinateAlgebra.A h :=
      rfl

@[simp] theorem loss_stream (h : ℝ) (m : ℕ) :
    loss (CoordinateAlgebra.A h - 1 / 2) m = PhysicalGraphBounds.graphLoss m + 1 + h := by
  unfold loss CoordinateAlgebra.A
  ring

@[simp] theorem loss_pressure (h : ℝ) (m : ℕ) :
    loss (2 * CoordinateAlgebra.A h) m = PhysicalGraphBounds.graphLoss m + 1 + 2 *
      CoordinateAlgebra.A h := rfl

/-! ## The actual Cartesian angular frame -/

/-- The Cartesian unit angular direction, with the usual totalized value
at the axis.  Axis regularity below comes from the supported coefficient. -/
noncomputable def angularVector (y : PhysicalGraphBounds.Plane) : Space :=
  (-y.2 / PhysicalClassBounds.cartesianRadius y) • coordinateVector 0 +
    (y.1 / PhysicalClassBounds.cartesianRadius y) • coordinateVector 1

theorem angularVector_smooth :
    ContDiffOn ℝ ∞ angularVector {y : PhysicalGraphBounds.Plane | y ≠ 0} := by
  have hr := PhysicalClassBounds.cartesianRadius_smooth
  have hn : ∀ y : PhysicalGraphBounds.Plane, y ≠ 0 →
      PhysicalClassBounds.cartesianRadius y ≠ 0 := by
    intro y hy
    exact (Real.sqrt_pos.2 (PhysicalGraphBounds.sum_sq_pos hy)).ne'
  exact (((contDiffOn_snd.neg).div hr hn).smul contDiffOn_const).add
    ((contDiffOn_fst.div hr hn).smul contDiffOn_const)

theorem angularVector_smul {c : ℝ} (hc : 0 < c) (y : PhysicalGraphBounds.Plane) :
    angularVector (c • y) = angularVector y := by
  unfold angularVector
  rw [cartesianRadius_smul hc.le]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have h0 : -(c * y.2) / (c * PhysicalClassBounds.cartesianRadius y) =
      -y.2 / PhysicalClassBounds.cartesianRadius y := by
    rw [neg_mul_eq_mul_neg, mul_div_mul_left _ _ hc.ne']
  rw [h0, mul_div_mul_left _ _ hc.ne']

/-- A local Leibniz estimate for scalar multiplication, including order
zero.  It uses actual Fréchet tensors on the supplied open set. -/
theorem smul_jet_bound {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set D} (hU : IsOpen U) {f : D → ℝ} {g : D → E}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {z : D} (hz : z ∈ U)
    {m j : ℕ} (hj : j ≤ m) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f z‖ ≤ A)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g z‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun x => f x • g x) z‖ ≤ (2 : ℝ) ^ m * A * B := by
  have hprod := norm_iteratedFDerivWithin_smul_le hf hg hU.uniqueDiffOn hz
    (n := j) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  simp only [iteratedFDerivWithin_of_isOpen _ hU hz] at hprod
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (j - i) g z‖ := hprod
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfa i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj))
          (Nat.cast_nonneg _))
        (hgb (j - i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ j * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ (2 : ℝ) ^ m * A * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB

theorem angularVector_lift_smooth {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (angularVector ∘ PhysicalGraphBounds.liftXY)
      (PhysicalClassBounds.cylindricalDomain a b) :=
  angularVector_smooth.comp PhysicalGraphBounds.liftXY.contDiff.contDiffOn
    (fun _ hx => PhysicalClassBounds.cylindricalDomain_axisFree ha hx)

/-- The angular frame has uniform jets on the fixed padded annulus.
No slow or auxiliary coordinate enters these constants. -/
theorem angularVector_lift_jet_bound {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ PhysicalClassBounds.cylindricalDomain a b, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (angularVector ∘ PhysicalGraphBounds.liftXY) x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := PhysicalGraphBounds.compact_jet_bound
    PhysicalGraphBounds.axisFree_open angularVector_smooth
    (PhysicalGraphBounds.isCompact_annulus (a / 2) (b + 1))
    (PhysicalGraphBounds.annulus_axisFree (half_pos ha)) m
  refine ⟨B, hB, ?_⟩
  intro x hx j hj
  have haxis := PhysicalClassBounds.cylindricalDomain_axisFree ha hx
  have hann : PhysicalGraphBounds.liftXY x ∈ PhysicalGraphBounds.annulus (a / 2) (b + 1) := by
    refine ⟨?_, hx.1.le⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2.le
  exact (PhysicalGraphBounds.norm_jet_comp_linear PhysicalGraphBounds.axisFree_open
    angularVector_smooth PhysicalGraphBounds.liftXY haxis j).trans
    ((mul_le_mul (hb j hj _ hann)
      (pow_le_one₀ (norm_nonneg _) PhysicalGraphBounds.norm_liftXY_le)
      (by positivity) (zero_le_one.trans hB)).trans_eq (mul_one B))

theorem angularVector_scaledRadial (n : ℕ) (w : SpaceTime) :
    angularVector (PhysicalGraphBounds.scaledRadial n w) =
      angularVector (PhysicalGraphBounds.radialProjection w) :=
  angularVector_smul (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) _

/-- This is the direct angular vector when `degree = A h`, and the
azimuthal stream potential when `degree = A h - 1/2`. -/
noncomputable def bandAngularField (h : ℝ) (n d : ℕ) (degree : ℝ)
    (f : Point → ℝ) : VelocityField :=
  fun w => bandField h n d degree f w • angularVector (PhysicalGraphBounds.radialProjection w)

/-- The actual angular direction is incorporated before estimating the
physical graph.  Thus it incurs no additional power loss. -/
theorem bandAngularField_jet_bound {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (gain degree e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
        |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : Point → ℝ, SmoothNear f (graph h n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (graph h n d w)‖ ≤
        A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (bandAngularField h n d degree f) w‖ ≤
        C * q ^ (gain - loss degree m) := by
  obtain ⟨B, hB, hBj⟩ := PhysicalClassBounds.cylindricalMap_positiveJets (b := b) ha m
  obtain ⟨V, hV, hVj⟩ := angularVector_lift_jet_bound (b := b) ha m
  let A' : ℝ := (2 : ℝ) ^ m * ((m.factorial : ℝ) * A * B ^ m) * V
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  obtain ⟨C, hC, hb⟩ := common_stripped_physical_bound_local (E := Space) (b := b)
    hh hh1 ha Δ m (gain - degree) e A' hA'
  refine ⟨C, hC, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi f hf hjet
  obtain ⟨F, hF, he⟩ := hf.exists_global_germ
  have hx := PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hann
  have hg : ContDiffOn ℝ ∞ (F ∘ PhysicalClassBounds.cylindricalMap)
      (PhysicalClassBounds.cylindricalDomain a b) :=
    hF.comp_contDiffOn (PhysicalClassBounds.cylindricalMap_smooth ha)
  let v : LiftPoint → Space := fun x => F (PhysicalClassBounds.cylindricalMap x) •
    angularVector (PhysicalGraphBounds.liftXY x)
  have hv : ContDiffOn ℝ ∞ v (PhysicalClassBounds.cylindricalDomain a b) :=
    hg.smul (angularVector_lift_smooth ha)
  let u : LiftPoint → Space := fun x => (ChartScales.Q n ^ (-degree)) • v x
  have hu : SmoothNear u (commonLift h n d w) :=
    SmoothNear.of_open (PhysicalClassBounds.cylindricalDomain_open a b)
      (hv.const_smul _) hx
  have he' : bandAngularField h n d degree f =ᶠ[𝓝 w] u ∘ commonLift h n d := by
    filter_upwards [he.comp_tendsto (graph_smoothAt ha h n d hann).continuousAt] with z hz
    change (ChartScales.Q n ^ (-degree) * f (graph h n d z)) •
      angularVector (PhysicalGraphBounds.radialProjection z) =
        ChartScales.Q n ^ (-degree) • (F (graph h n d z) •
          angularVector (PhysicalGraphBounds.liftXY (commonLift h n d z)))
    rw [PhysicalClassBounds.liftXY_commonLift, angularVector_scaledRadial]
    change f (graph h n d z) = F (graph h n d z) at hz
    simp only [hz, smul_smul]
  rw [iteratedFDeriv_eq_of_eventuallyEq he' m]
  have hbound := hb n hn d hd w hann ht q hq hlo hhi u hu
  have hqN := ChartScales.Q_pos n
  have hSN := ChartScales.S_pos (show 1 ≤ n by omega)
  have hab : 0 ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by positivity
  have hFjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F (graph h n d w)‖ ≤
      A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by
    intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
    exact hjet i hi
  have hcomp := PhysicalClassBounds.composition_jet_bound hF
    (PhysicalClassBounds.cylindricalDomain_open a b) (PhysicalClassBounds.cylindricalMap_smooth ha)
    hx m hab hB hFjet (hBj _ hx)
  have huc : ∀ i ≤ m, ‖iteratedFDeriv ℝ i u (commonLift h n d w)‖ ≤
      A' * ChartScales.Q n ^ (gain - degree) * ChartScales.S n ^ e := by
    intro i hi
    have hnear := hv.contDiffAt ((PhysicalClassBounds.cylindricalDomain_open a b).mem_nhds hx)
    change ‖iteratedFDeriv ℝ i (fun x => (ChartScales.Q n ^ (-degree)) • v x)
      (commonLift h n d w)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hnear.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)),
      norm_smul (ChartScales.Q n ^ (-degree)) (iteratedFDeriv ℝ i v (commonLift h n d w)),
      Real.norm_of_nonneg (Real.rpow_pos_of_pos hqN (-degree)).le]
    have hprod := smul_jet_bound (PhysicalClassBounds.cylindricalDomain_open a b)
      hg (angularVector_lift_smooth ha) hx hi
      (by positivity : 0 ≤ (m.factorial : ℝ) *
        (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m)
      (zero_le_one.trans hV) hcomp (hVj _ hx)
    calc
      _ ≤ ChartScales.Q n ^ (-degree) * ((2 : ℝ) ^ m * ((m.factorial : ℝ) *
          (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m) * V) :=
        mul_le_mul_of_nonneg_left hprod (Real.rpow_pos_of_pos hqN _).le
      _ = _ := by dsimp [A']; rw [Real.rpow_sub hqN, Real.rpow_neg hqN.le]; ring
  convert! hbound huc using 1
  congr 2
  unfold loss
  ring

/-- The actual Cartesian vector associated with the coherent scalar
field.  The formula applies both to angular velocity and stream potential. -/
noncomputable def CoherentFamily.angularField (D : CoherentFamily h degree N Δ U ℝ) : VelocityField
  :=
  fun w => D.field w • angularVector (PhysicalGraphBounds.radialProjection w)

theorem CoherentFamily.angularField_formula (D : CoherentFamily h degree N Δ U ℝ) (w : SpaceTime) :
    D.angularField w =
      (-w.2 1 / PhysicalClassBounds.cartesianRadius (PhysicalGraphBounds.radialProjection w) *
        D.field w) • coordinateVector 0 +
      (w.2 0 / PhysicalClassBounds.cartesianRadius (PhysicalGraphBounds.radialProjection w) *
        D.field w) • coordinateVector 1 := by
  simp only [CoherentFamily.angularField, angularVector, smul_add, smul_smul]
  change (D.field w * (-w.2 1 / _)) • _ + (D.field w * (w.2 0 / _)) • _ = _
  rw [mul_comm (D.field w), mul_comm (D.field w)]

theorem CoherentFamily.angularField_germ (D : CoherentFamily h degree N Δ U ℝ)
    (hU : IsOpen U) (n : ℕ) (hn : N ≤ n) {w : SpaceTime} (hw : w ∈ preterminal)
    (hu : (graph h n (D.gap n) w).2.1 ∈ U) :
    D.angularField =ᶠ[𝓝 w] bandAngularField h n (D.gap n) degree (D.native n) := by
  filter_upwards [D.field_germ hU n hn hw hu] with z hz
  exact congrArg (fun v => v • angularVector (PhysicalGraphBounds.radialProjection z)) hz

theorem CoherentFamily.angularField_zero_germ (D : CoherentFamily h degree N Δ U ℝ)
    {w : SpaceTime} (hw : w ∉ tsupport D.field) :
    D.angularField =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with z hz
  change D.field z = 0 at hz
  change D.field z • _ = _
  simp only [hz, zero_smul]

theorem CoherentFamily.angularField_jet_bound (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.angularField w‖ ≤ C * physicalQ h w ^ (gain - loss degree m) := by
  obtain ⟨A, hA, e, hjet⟩ := hj m
  obtain ⟨C, hC, hb⟩ := bandAngularField_jet_bound (b := 2 * b)
    hh.le hh1.le (div_pos ha (by norm_num : (0 : ℝ) < 4)) Δ m gain degree e A hA
  refine ⟨C, hC, ?_⟩
  intro w hw ht hsmall
  have hq := physicalQ_pos hh hh1 hw
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq⟩ := exists_comparable_band N hq hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
    have hu := hcover (graph_slow_normalized hh hh1 n (D.gap n) hw hlo hnq.le)
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    rw [iteratedFDeriv_eq_of_eventuallyEq (D.angularField_germ hU n hn hw hu) m]
    apply hb n (hN.trans hn) (D.gap n) (D.gap_le n hn) w hann ht
      (physicalQ h w) hq hlo hnq.le (D.native n)
    · exact SmoothNear.of_open (PhysicalMeanDomain.slowDomain_open hU) (hsm n hn) hu
    · intro j hjm
      simpa only [Real.rpow_natCast] using hjet n hn _ hu j hjm
  · rw [jet_zero_off_tsupport _ _
      (notMem_tsupport_iff_eventuallyEq.mpr (D.angularField_zero_germ hts)), norm_zero]
    positivity

theorem CoherentFamily.angularField_smoothAt (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {w : SpaceTime} (hw : w ∈ preterminal)
    (hsmall : physicalQ h w ≤ ChartScales.Q N) : ContDiffAt ℝ ∞ D.angularField w := by
  classical
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq⟩ := exists_comparable_band N (physicalQ_pos hh hh1 hw) hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
    have hu := hcover (graph_slow_normalized hh hh1 n (D.gap n) hw hlo hnq.le)
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    have haxis := PhysicalGraphBounds.scaledRadial_ne_zero
      (PhysicalGraphBounds.annulus_axisFree (div_pos ha (by norm_num : (0 : ℝ) < 4)) hann)
    exact (D.field_smoothAt hh hh1 ha hab hU hcover hsm hs hw hsmall).smul
      ((angularVector_smooth.contDiffAt (PhysicalGraphBounds.axisFree_open.mem_nhds haxis)).comp w
        PhysicalGraphBounds.radialProjection.contDiff.contDiffAt)
  · exact contDiffAt_const.congr_of_eventuallyEq (D.angularField_zero_germ hts)

theorem CoherentFamily.angularField_smooth (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) :
    ContDiffOn ℝ ∞ D.angularField (physicalDomain h N) := by
  intro w hw
  exact (D.angularField_smoothAt hh hh1 ha hab hU hcover hsm hs hw.1 hw.2.le).contDiffWithinAt

/-- The actual spatial curl of the azimuthal stream potential.  Its
fixed physical loss uses one more derivative; no derivative is postulated. -/
theorem CoherentFamily.curl_angularField_jet_bound (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SpaceTime, w ∈ physicalDomain h N → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl D.angularField) w‖ ≤
        C * physicalQ h w ^ (gain - loss degree (m + 1)) := by
  obtain ⟨C, hC, hb⟩ := D.angularField_jet_bound hh hh1 ha hab hN hU hcover hsm hs hj (m + 1)
  refine ⟨‖PhysicalClassBounds.jointCurl‖ * C,
    mul_nonneg (norm_nonneg PhysicalClassBounds.jointCurl) hC, ?_⟩
  intro w hw ht
  exact (PhysicalClassBounds.spatialCurl_jet_bound (physicalDomain_open hh hh1 N)
    (D.angularField_smooth hh hh1 ha hab hU hcover hsm hs) hw m).trans
    ((mul_le_mul_of_nonneg_left (hb w hw.1 ht hw.2.le)
      (norm_nonneg PhysicalClassBounds.jointCurl)).trans_eq (by ring))

theorem CoherentFamily.curl_angularField_smooth (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) :
    ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl D.angularField) (physicalDomain h N) := by
  intro w hw
  exact (SpatialCurl.contDiffAt_spatialCurl
    (D.angularField_smoothAt hh hh1 ha hab hU hcover hsm hs hw.1 hw.2.le)
    (by simp)).contDiffWithinAt

/-! ## Genuine moving-weight mean classes -/

/-- The existing moving two-edge mean class supplies the native input
jets.  The only extra regularity is the genuine supported extension across
the edges, on the valid slow region. -/
theorem NativeJets.of_movingMeanClass {h α a b cL cR : ℝ}
    (R : LocalSignedRequest.SlowRegion (2 * h)) (ha : 0 < a)
    (hcL : 0 < cL) (hcR : 0 < cR) (ε L : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain R.carrier))
    (hs : ∀ n, VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength (2 * h))
      R.carrier (f n))
    (hclass : WeightedClasses.MeanClass
      (LocalSignedRequest.movingStripData R a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (N : ℕ) (hεnative : ∀ n ≥ N, ε n = ChartScales.epsilon h n)
    {C : ℝ} {p : ℕ} (hC : 1 ≤ C) (hpoly : ∀ n ≥ N, L n ≤ C * ChartScales.S n ^ p) :
    NativeJets N R.carrier (h * α) f :=
  NativeJets.of_localBandJets
    (VariableGaugeMean.meanClass_moving_localBandJets R ha hcL hcR ε L hε hεone hL hf hs hclass)
    hεnative (fun n _ => zero_le_one.trans (hL n)) hC hpoly

/-! ## Coherence of the actual reconstructed pressure and stream -/

theorem meanPressure_fiberLocal (d a b M : ℝ) (hab : a < b)
    (ell : PhysicalGraphBounds.Plane → ℝ) (v : PressureStream.Plane) :
    PhysicalMeanDomain.FiberLocal (VariableGaugeMean.meanPressure d a b M hab ell v) := by
  intro f g s he r Y
  apply VariableGaugeMean.compactPrimitive_fiberLocal d a b M ell v _ _ s ?_ r Y
  intro R W
  change f (R, (s, W)) - VariableGaugeMean.density a b hab ell (R, (s, W)) *
      PressureStream.pressureMass f s =
    g (R, (s, W)) - VariableGaugeMean.density a b hab ell (R, (s, W)) *
      PressureStream.pressureMass g s
  rw [he, show PressureStream.pressureMass f s = PressureStream.pressureMass g s from
    PhysicalMeanDomain.liftedPressureMass_fiberLocal f g s he R W]

theorem streamPotential_fiberLocal (d a b M : ℝ)
    (ell : PhysicalGraphBounds.Plane → ℝ) (v : PressureStream.Plane) :
    PhysicalMeanDomain.FiberLocal (VariableGaugeMean.streamPotential d a b M ell v) := by
  intro f g s he r Y
  apply congrArg (fun x : ℝ => x / r)
  exact VariableGaugeMean.compactPrimitive_fiberLocal d a b M ell v _ _ s
    (PhysicalMeanDomain.weightedSource_fiberLocal f g s he) r Y

/-- Reconstruct the physical pressure from the coherent momentum source.
The output coherence is proved from the actual integral operator; it is not
an additional premise. -/
noncomputable def CoherentFamily.reconstructPressure
    (D : CoherentFamily h (2 * CoordinateAlgebra.A h + 1 / 2) N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    {d : ℝ} (hd : 0 < d) (M : ℝ) (hU : IsOpen U)
    (hf : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hp : ∀ n ≥ N, PhysicalMeanDomain.PeriodicOn U (D.native n))
    (hs : NativeSupport h a b N U D.native) :
    CoherentFamily h (2 * CoordinateAlgebra.A h) N Δ U ℝ where
  native n := VariableGaugeMean.meanPressure d a b
    (MeanChartCompatibility.radialFrequency h n (ChartScales.nativeIndex h n - D.gap n) d M)
    hab (VariableGaugeMean.qLength (2 * h)) (TorusInverse.vector .radial) (D.native n)
  physical := VariableGaugeMean.meanPressure d a b M hab
    (VariableGaugeMean.qLength (2 * h)) (TorusInverse.vector .radial) D.physical
  gap := D.gap
  gap_le := D.gap_le
  gap_native := D.gap_native
  coherent := by
    intro n hn z ht hu
    have he := meanPressure_fiberLocal d a b M hab (VariableGaugeMean.qLength (2 * h))
      (TorusInverse.vector .radial) D.physical
      (VariableGaugeMean.fieldOnPhysicalTZ h n (ChartScales.nativeIndex h n - D.gap n)
        (2 * CoordinateAlgebra.A h + 1 / 2) (D.native n)) z.2.1
      (fun r Y => D.coherent n hn (r, (z.2.1, Y)) ht hu) z.1 z.2.2
    exact he.trans (VariableGaugeMean.physicalMeanPressure_naturality hh hh1 ha hab hd n
      (ChartScales.nativeIndex h n - D.gap n) M hU (hf n hn) (hp n hn) (hs n hn) z ht hu)

/-- Reconstruct the azimuthal stream potential from a coherent axial
source.  Its physical degree is exactly `A h - 1/2`. -/
noncomputable def CoherentFamily.reconstructStream
    (D : CoherentFamily h (CoordinateAlgebra.A h) N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    {d : ℝ} (hd : 0 < d) (M : ℝ) (hU : IsOpen U)
    (hf : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) :
    CoherentFamily h (CoordinateAlgebra.A h - 1 / 2) N Δ U ℝ where
  native n := VariableGaugeMean.streamPotential d a b
    (MeanChartCompatibility.radialFrequency h n (ChartScales.nativeIndex h n - D.gap n) d M)
    (VariableGaugeMean.qLength (2 * h)) (TorusInverse.vector .radial) (D.native n)
  physical := VariableGaugeMean.streamPotential d a b M
    (VariableGaugeMean.qLength (2 * h)) (TorusInverse.vector .radial) D.physical
  gap := D.gap
  gap_le := D.gap_le
  gap_native := D.gap_native
  coherent := by
    intro n hn z ht hu
    have he := streamPotential_fiberLocal d a b M (VariableGaugeMean.qLength (2 * h))
      (TorusInverse.vector .radial) D.physical
      (VariableGaugeMean.fieldOnPhysicalTZ h n (ChartScales.nativeIndex h n - D.gap n)
        (CoordinateAlgebra.A h) (D.native n)) z.2.1
      (fun r Y => D.coherent n hn (r, (z.2.1, Y)) ht hu) z.1 z.2.2
    exact he.trans (VariableGaugeMean.physicalStreamPotential_naturality hh hh1 ha hab hd n
      (ChartScales.nativeIndex h n - D.gap n) M hU (hf n hn) (hs n hn) z ht hu)

end NavierStokes.PhysicalMeanJetBounds
