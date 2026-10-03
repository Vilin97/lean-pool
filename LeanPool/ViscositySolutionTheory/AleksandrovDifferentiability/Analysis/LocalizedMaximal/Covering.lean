/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LocalizedMaximal.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Localized maximal witness intervals
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- An open interval in the source domain whose measure average exceeds the threshold. -/
def SourceMaximalWitnessInterval (μ : Measure ℝ) (t : ℝ) : Type :=
  {p : ℝ × ℝ //
    p.1 < p.2 ∧
      Set.Ioo p.1 p.2 ⊆ sourceMaximalDomain ∧
        t < openIntervalMeasureAverage μ p.1 p.2}

namespace SourceMaximalWitnessInterval

variable {μ : Measure ℝ} {t : ℝ}

/-- Left endpoint of a source maximal witness interval. -/
def left (I : SourceMaximalWitnessInterval μ t) : ℝ :=
  I.1.1

/-- Right endpoint of a source maximal witness interval. -/
def right (I : SourceMaximalWitnessInterval μ t) : ℝ :=
  I.1.2

/-- Underlying open interval of a source maximal witness. -/
def interval (I : SourceMaximalWitnessInterval μ t) : Set ℝ :=
  Set.Ioo I.left I.right

/-- Center of the witness interval, for the ball formulation of the covering lemma. -/
def center (I : SourceMaximalWitnessInterval μ t) : ℝ :=
  (I.left + I.right) / 2

/-- Radius of the witness interval, for the ball formulation of the covering lemma. -/
def radius (I : SourceMaximalWitnessInterval μ t) : ℝ :=
  (I.right - I.left) / 2

theorem left_lt_right (I : SourceMaximalWitnessInterval μ t) : I.left < I.right :=
  I.2.1

theorem interval_subset_sourceMaximalDomain (I : SourceMaximalWitnessInterval μ t) :
    I.interval ⊆ sourceMaximalDomain :=
  I.2.2.1

theorem average_gt (I : SourceMaximalWitnessInterval μ t) :
    t < openIntervalMeasureAverage μ I.left I.right :=
  I.2.2.2

theorem radius_pos (I : SourceMaximalWitnessInterval μ t) : 0 < I.radius := by
  rw [radius]
  exact half_pos (sub_pos.mpr I.left_lt_right)

theorem interval_eq_ball (I : SourceMaximalWitnessInterval μ t) :
    I.interval = Metric.ball I.center I.radius := by
  rw [interval, center, radius]
  exact Real.Ioo_eq_ball I.left I.right

/-- The left endpoint of any source-admissible open interval is at least `-2`. -/
theorem left_ge_neg_two_of_Ioo_subset_sourceMaximalDomain {a b : ℝ}
    (hab : a < b) (hsub : Set.Ioo a b ⊆ sourceMaximalDomain) :
    (-2 : ℝ) ≤ a := by
  by_contra hnot
  have ha : a < -2 := lt_of_not_ge hnot
  by_cases hb : b ≤ -2
  · rcases exists_between hab with ⟨y, hay, hyb⟩
    have hy_source := hsub ⟨hay, hyb⟩
    rw [sourceMaximalDomain] at hy_source
    rcases hy_source with ⟨hy_left, _hy_right⟩
    linarith
  · have hneg2b : (-2 : ℝ) < b := lt_of_not_ge hb
    rcases exists_between ha with ⟨y, hay, hyneg2⟩
    have hy_source := hsub ⟨hay, hyneg2.trans hneg2b⟩
    rw [sourceMaximalDomain] at hy_source
    rcases hy_source with ⟨hy_left, _hy_right⟩
    linarith

/-- The right endpoint of any source-admissible open interval is at most `2`. -/
theorem right_le_two_of_Ioo_subset_sourceMaximalDomain {a b : ℝ}
    (hab : a < b) (hsub : Set.Ioo a b ⊆ sourceMaximalDomain) :
    b ≤ (2 : ℝ) := by
  by_contra hnot
  have hb : (2 : ℝ) < b := lt_of_not_ge hnot
  by_cases ha : (2 : ℝ) ≤ a
  · rcases exists_between hab with ⟨y, hay, hyb⟩
    have hy_source := hsub ⟨hay, hyb⟩
    rw [sourceMaximalDomain] at hy_source
    rcases hy_source with ⟨_hy_left, hy_right⟩
    linarith
  · have ha2 : a < (2 : ℝ) := lt_of_not_ge ha
    rcases exists_between hb with ⟨y, h2y, hyb⟩
    have hy_source := hsub ⟨ha2.trans h2y, hyb⟩
    rw [sourceMaximalDomain] at hy_source
    rcases hy_source with ⟨_hy_left, hy_right⟩
    linarith

theorem left_ge_neg_two (I : SourceMaximalWitnessInterval μ t) : (-2 : ℝ) ≤ I.left :=
  left_ge_neg_two_of_Ioo_subset_sourceMaximalDomain I.left_lt_right
    I.interval_subset_sourceMaximalDomain

theorem right_le_two (I : SourceMaximalWitnessInterval μ t) : I.right ≤ (2 : ℝ) :=
  right_le_two_of_Ioo_subset_sourceMaximalDomain I.left_lt_right
    I.interval_subset_sourceMaximalDomain

/-- Witness intervals have radius at most `2`, since they are contained in `(-2,2)`. -/
theorem radius_le_two (I : SourceMaximalWitnessInterval μ t) : I.radius ≤ 2 := by
  rw [radius]
  have hlen : I.right - I.left ≤ (2 : ℝ) - (-2 : ℝ) :=
    sub_le_sub I.right_le_two I.left_ge_neg_two
  linarith

/-- The Euclidean length of a witness interval is twice its radius. -/
theorem length_eq_two_mul_radius (I : SourceMaximalWitnessInterval μ t) :
    I.right - I.left = 2 * I.radius := by
  rw [radius]
  ring

/-- The witness average inequality, rewritten as a mass lower bound. -/
theorem t_mul_length_lt_measureReal_interval (I : SourceMaximalWitnessInterval μ t) :
    t * (I.right - I.left) < μ.real I.interval := by
  have hlen_pos : 0 < I.right - I.left := sub_pos.mpr I.left_lt_right
  have havg := I.average_gt
  rw [openIntervalMeasureAverage] at havg
  change t < μ.real I.interval / (I.right - I.left) at havg
  exact (lt_div_iff₀ hlen_pos).mp havg

/-- The witness average inequality, in radius form. -/
theorem t_mul_two_mul_radius_lt_measureReal_interval
    (I : SourceMaximalWitnessInterval μ t) :
    t * (2 * I.radius) < μ.real I.interval := by
  simpa [length_eq_two_mul_radius] using I.t_mul_length_lt_measureReal_interval

/-- Pointwise bound for the Lebesgue measure of an enlarged witness ball.

This is the quantitative step in the source Vitali argument: the average bound
`t < μ(I) / |I|` implies `|B(c, τ r)| <= (τ / t) μ(I)`. -/
theorem volume_enlargedBall_le_of_average
    (I : SourceMaximalWitnessInterval μ t) {τ : ℝ} (ht : 0 < t) (hτ : 0 ≤ τ) :
    volume (Metric.ball I.center (τ * I.radius)) ≤
      ENNReal.ofReal ((τ / t) * μ.real I.interval) := by
  rw [Real.volume_ball]
  apply ENNReal.ofReal_le_ofReal
  have hmass :
      t * (2 * I.radius) ≤ μ.real I.interval :=
    (I.t_mul_two_mul_radius_lt_measureReal_interval).le
  have hscale : 0 ≤ τ / t := div_nonneg hτ ht.le
  have hscaled := mul_le_mul_of_nonneg_left hmass hscale
  calc
    2 * (τ * I.radius) = (τ / t) * (t * (2 * I.radius)) := by
      field_simp [ne_of_gt ht]
    _ ≤ (τ / t) * μ.real I.interval := hscaled

/-- Pointwise enlarged-ball bound in the measure-valued form used for summing. -/
theorem volume_enlargedBall_le_mul_measure_interval
    (I : SourceMaximalWitnessInterval μ t) {τ : ℝ} (ht : 0 < t) (hτ : 0 ≤ τ)
    (hfinite : μ I.interval ≠ ⊤) :
    volume (Metric.ball I.center (τ * I.radius)) ≤
      ENNReal.ofReal (τ / t) * μ I.interval := by
  refine (I.volume_enlargedBall_le_of_average ht hτ).trans_eq ?_
  rw [ENNReal.ofReal_mul (div_nonneg hτ ht.le)]
  change ENNReal.ofReal (τ / t) * ENNReal.ofReal (μ I.interval).toReal =
    ENNReal.ofReal (τ / t) * μ I.interval
  rw [ENNReal.ofReal_toReal hfinite]

/-- A disjoint subfamily of nonempty witness balls is countable. -/
theorem countable_of_pairwiseDisjoint_witnessBall
    {u : Set (SourceMaximalWitnessInterval μ t)}
    (hdisj :
      u.PairwiseDisjoint
        (fun I : SourceMaximalWitnessInterval μ t => Metric.ball I.center I.radius)) :
    u.Countable :=
  hdisj.countable_of_nonempty_interior fun I _hI => by
    refine ⟨I.center, ?_⟩
    rw [Metric.isOpen_ball.interior_eq]
    exact Metric.mem_ball_self I.radius_pos

end SourceMaximalWitnessInterval

/-- The source localized maximal bad set is covered by all its witness intervals. -/
theorem sourceLocalizedMaximalBadSet_subset_iUnion_witnessInterval
    {μ : Measure ℝ} {t : ℝ} :
    sourceLocalizedMaximalBadSet μ t ⊆
      ⋃ I : SourceMaximalWitnessInterval μ t,
        SourceMaximalWitnessInterval.interval I := by
  intro s hs
  rcases hs with ⟨hs_window, hs_bad⟩
  rcases (sourceLocalizedMaximalBadPredicate_iff_exists_average_gt_of_mem_window
      (μ := μ) (s := s) (t := t) hs_window).mp hs_bad with
    ⟨a, b, hab, hsub, hs_interval, havg⟩
  refine Set.mem_iUnion.mpr ⟨⟨(a, b), hab, hsub, havg⟩, ?_⟩
  exact hs_interval

/-- Ball-form version of the witness cover, ready for the one-dimensional Vitali covering
theorem. -/
theorem sourceLocalizedMaximalBadSet_subset_iUnion_witnessBall
    {μ : Measure ℝ} {t : ℝ} :
    sourceLocalizedMaximalBadSet μ t ⊆
      ⋃ I : SourceMaximalWitnessInterval μ t,
        Metric.ball (SourceMaximalWitnessInterval.center I)
          (SourceMaximalWitnessInterval.radius I) := by
  simpa [SourceMaximalWitnessInterval.interval_eq_ball] using
    sourceLocalizedMaximalBadSet_subset_iUnion_witnessInterval (μ := μ) (t := t)

/-- Vitali's ball-covering lemma applied to source maximal witness intervals: there is a
disjoint family of witness balls whose `τ`-enlargements cover the source maximal bad set. -/
theorem exists_disjoint_witnessBall_covering_enlargement
    {μ : Measure ℝ} {t τ : ℝ} (hτ : 3 < τ) :
    ∃ u : Set (SourceMaximalWitnessInterval μ t),
      u.PairwiseDisjoint
        (fun I : SourceMaximalWitnessInterval μ t =>
          Metric.ball (SourceMaximalWitnessInterval.center I)
            (SourceMaximalWitnessInterval.radius I)) ∧
        sourceLocalizedMaximalBadSet μ t ⊆
          ⋃ I ∈ u,
            Metric.ball (SourceMaximalWitnessInterval.center I)
              (τ * SourceMaximalWitnessInterval.radius I) := by
  classical
  rcases Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (t := (Set.univ : Set (SourceMaximalWitnessInterval μ t)))
      (x := fun I : SourceMaximalWitnessInterval μ t =>
        SourceMaximalWitnessInterval.center I)
      (r := fun I : SourceMaximalWitnessInterval μ t =>
        SourceMaximalWitnessInterval.radius I)
      (R := 2) (τ := τ)
      (fun I _ => SourceMaximalWitnessInterval.radius_le_two I) hτ with
    ⟨u, _hu_subset, hdisj, hcover⟩
  refine ⟨u, hdisj, ?_⟩
  intro s hs
  have hs_ball :=
    sourceLocalizedMaximalBadSet_subset_iUnion_witnessBall (μ := μ) (t := t) hs
  rcases Set.mem_iUnion.mp hs_ball with ⟨I, hsI⟩
  rcases hcover I (Set.mem_univ I) with ⟨J, hJu, hIJ⟩
  exact Set.mem_iUnion.mpr ⟨J, Set.mem_iUnion.mpr ⟨hJu, hIJ hsI⟩⟩

/-- Countable subadditivity for the `τ`-enlargements of a selected witness family. -/
theorem volume_biUnion_enlarged_witnessBall_le_tsum
    {μ : Measure ℝ} {t τ : ℝ} {u : Set (SourceMaximalWitnessInterval μ t)}
    (hcount : u.Countable) :
    volume
        (⋃ I ∈ u,
          Metric.ball (SourceMaximalWitnessInterval.center I)
            (τ * SourceMaximalWitnessInterval.radius I)) ≤
      ∑' I : u,
        volume
          (Metric.ball (SourceMaximalWitnessInterval.center I.1)
            (τ * SourceMaximalWitnessInterval.radius I.1)) := by
  exact measure_biUnion_le volume hcount
    (fun I : SourceMaximalWitnessInterval μ t =>
      Metric.ball (SourceMaximalWitnessInterval.center I)
        (τ * SourceMaximalWitnessInterval.radius I))

/-- The source pointwise ball estimate summed over a countable selected witness family. -/
theorem volume_biUnion_enlarged_witnessBall_le_tsum_average
    {μ : Measure ℝ} {t τ : ℝ} {u : Set (SourceMaximalWitnessInterval μ t)}
    (hcount : u.Countable) (ht : 0 < t) (hτ : 0 ≤ τ) :
    volume
        (⋃ I ∈ u,
          Metric.ball (SourceMaximalWitnessInterval.center I)
            (τ * SourceMaximalWitnessInterval.radius I)) ≤
      ∑' I : u,
        ENNReal.ofReal
          ((τ / t) * μ.real (SourceMaximalWitnessInterval.interval I.1)) := by
  calc
    volume
        (⋃ I ∈ u,
          Metric.ball (SourceMaximalWitnessInterval.center I)
            (τ * SourceMaximalWitnessInterval.radius I)) ≤
        ∑' I : u,
          volume
            (Metric.ball (SourceMaximalWitnessInterval.center I.1)
              (τ * SourceMaximalWitnessInterval.radius I.1)) :=
      volume_biUnion_enlarged_witnessBall_le_tsum (μ := μ) (t := t) (τ := τ) hcount
    _ ≤
        ∑' I : u,
          ENNReal.ofReal
            ((τ / t) * μ.real (SourceMaximalWitnessInterval.interval I.1)) :=
      ENNReal.tsum_le_tsum fun I =>
        SourceMaximalWitnessInterval.volume_enlargedBall_le_of_average I.1 ht hτ

/-- The source pointwise ball estimate summed in measure-valued form over a countable selected
witness family. -/
theorem volume_biUnion_enlarged_witnessBall_le_mul_tsum_measure
    {μ : Measure ℝ} {t τ : ℝ} {u : Set (SourceMaximalWitnessInterval μ t)}
    (hcount : u.Countable) (ht : 0 < t) (hτ : 0 ≤ τ)
    (hfinite : μ sourceMaximalDomain < ⊤) :
    volume
        (⋃ I ∈ u,
          Metric.ball (SourceMaximalWitnessInterval.center I)
            (τ * SourceMaximalWitnessInterval.radius I)) ≤
      ENNReal.ofReal (τ / t) *
        ∑' I : u, μ (SourceMaximalWitnessInterval.interval I.1) := by
  calc
    volume
        (⋃ I ∈ u,
          Metric.ball (SourceMaximalWitnessInterval.center I)
            (τ * SourceMaximalWitnessInterval.radius I)) ≤
        ∑' I : u,
          volume
            (Metric.ball (SourceMaximalWitnessInterval.center I.1)
              (τ * SourceMaximalWitnessInterval.radius I.1)) :=
      volume_biUnion_enlarged_witnessBall_le_tsum (μ := μ) (t := t) (τ := τ) hcount
    _ ≤
        ∑' I : u,
          ENNReal.ofReal (τ / t) *
            μ (SourceMaximalWitnessInterval.interval I.1) := by
      refine ENNReal.tsum_le_tsum fun I => ?_
      have hfiniteI :
          μ (SourceMaximalWitnessInterval.interval I.1) ≠ ⊤ :=
        (measure_ne_top_of_subset
          (SourceMaximalWitnessInterval.interval_subset_sourceMaximalDomain I.1)
          hfinite.ne)
      exact SourceMaximalWitnessInterval.volume_enlargedBall_le_mul_measure_interval
        I.1 ht hτ hfiniteI
    _ =
        ENNReal.ofReal (τ / t) *
          ∑' I : u, μ (SourceMaximalWitnessInterval.interval I.1) := by
      rw [ENNReal.tsum_mul_left]

/-- Disjoint witness balls give disjoint witness intervals. -/
theorem pairwiseDisjoint_witnessInterval_of_pairwiseDisjoint_witnessBall
    {μ : Measure ℝ} {t : ℝ} {u : Set (SourceMaximalWitnessInterval μ t)}
    (hdisj :
      u.PairwiseDisjoint
        (fun I : SourceMaximalWitnessInterval μ t =>
          Metric.ball (SourceMaximalWitnessInterval.center I)
            (SourceMaximalWitnessInterval.radius I))) :
    u.PairwiseDisjoint fun I : SourceMaximalWitnessInterval μ t =>
      SourceMaximalWitnessInterval.interval I := by
  simpa [SourceMaximalWitnessInterval.interval_eq_ball] using hdisj

/-- The total measure of a selected disjoint witness family is bounded by the measure of the
source domain. -/
theorem tsum_measure_witnessInterval_le_sourceMaximalDomain
    {μ : Measure ℝ} {t : ℝ} {u : Set (SourceMaximalWitnessInterval μ t)}
    (hcount : u.Countable)
    (hdisj :
      u.PairwiseDisjoint
        (fun I : SourceMaximalWitnessInterval μ t =>
          Metric.ball (SourceMaximalWitnessInterval.center I)
            (SourceMaximalWitnessInterval.radius I))) :
    (∑' I : u, μ (SourceMaximalWitnessInterval.interval I.1)) ≤ μ sourceMaximalDomain := by
  have hdisjInterval :
      u.PairwiseDisjoint fun I : SourceMaximalWitnessInterval μ t =>
        SourceMaximalWitnessInterval.interval I :=
    pairwiseDisjoint_witnessInterval_of_pairwiseDisjoint_witnessBall hdisj
  have hmeasure :
      μ
          (⋃ I ∈ u, SourceMaximalWitnessInterval.interval I) =
        ∑' I : u, μ (SourceMaximalWitnessInterval.interval I.1) :=
    measure_biUnion hcount hdisjInterval fun _ _ => measurableSet_Ioo
  have hsubset :
      (⋃ I ∈ u, SourceMaximalWitnessInterval.interval I) ⊆ sourceMaximalDomain := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨I, hxI⟩
    rcases Set.mem_iUnion.mp hxI with ⟨_hIu, hx_interval⟩
    exact SourceMaximalWitnessInterval.interval_subset_sourceMaximalDomain I hx_interval
  calc
    (∑' I : u, μ (SourceMaximalWitnessInterval.interval I.1)) =
        μ (⋃ I ∈ u, SourceMaximalWitnessInterval.interval I) := hmeasure.symm
    _ ≤ μ sourceMaximalDomain := measure_mono hsubset

end AleksandrovDifferentiability
