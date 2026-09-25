/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.AttachmentMap


/-!
# The source-side metric-adjunction formula

The asymmetric adjunction in the manuscript glues a closed subset of the
source to the old target by a nonexpansive map.  Mathlib's exact metric gluing
requires two isometric maps, so it does not directly apply.  Here we formalize
the source--source distance candidate from the manuscript and prove its key
short-scale property: an excursion through the old target cannot shorten a
source pair of distance at most `r`.
-/

@[expose] public section

namespace ScottishBook155

open ENNReal WithLp

universe u v

theorem oneSum_dist_eq
    {M : Type u} [NormedAddCommGroup M] (x y : OneSum M) :
    dist x y = dist x.fst y.fst + |x.snd - y.snd| := by
  rw [WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp [Real.dist_eq]

/-- Length of the cheapest source--target--source excursion in the proposed
metric adjunction. -/
noncomputable def attachmentExcursionCost
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ : OneSum M) : ℝ :=
  ⨅ p : M ⊕ Unit, ⨅ q : M ⊕ Unit,
    dist x₀ (attachmentPoint a H p) +
      dist (attachmentMap V y p) (attachmentMap V y q) +
      dist (attachmentPoint a H q) x₁

/-- The manuscript's source--source adjunction distance formula, before the
ambient quotient space is constructed. -/
noncomputable def sourceAdjunctionDist
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ : OneSum M) : ℝ :=
  min (dist x₀ x₁) (attachmentExcursionCost V a y H x₀ x₁)

/-- Distance candidate from a source point to an old-target point. -/
noncomputable def attachmentTargetCost
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x : OneSum M) (n : N) : ℝ :=
  ⨅ p : M ⊕ Unit,
    dist x (attachmentPoint a H p) + dist (attachmentMap V y p) n

/-- The two-layer adjunction predistance on the disjoint union of the source
and old target.  The remaining construction step is to prove its triangle
inequality and take its metric separation quotient. -/
noncomputable def adjunctionPreDist
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) :
      OneSum M ⊕ N → OneSum M ⊕ N → ℝ
  | Sum.inl x₀, Sum.inl x₁ => sourceAdjunctionDist V a y H x₀ x₁
  | Sum.inr n₀, Sum.inr n₁ => dist n₀ n₁
  | Sum.inl x, Sum.inr n => attachmentTargetCost V a y H x n
  | Sum.inr n, Sum.inl x => attachmentTargetCost V a y H x n

theorem attachmentTargetCost_nonneg
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x : OneSum M) (n : N) :
    0 ≤ attachmentTargetCost V a y H x n := by
  rw [attachmentTargetCost]
  apply le_ciInf
  intro p
  positivity

theorem attachmentTargetCost_le
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x : OneSum M) (n : N)
    (p : M ⊕ Unit) :
    attachmentTargetCost V a y H x n ≤
      dist x (attachmentPoint a H p) + dist (attachmentMap V y p) n := by
  rw [attachmentTargetCost]
  apply ciInf_le
  exact ⟨0, Set.forall_mem_range.2 fun q => by positivity⟩

theorem infDist_attachmentSet_le_attachmentTargetCost
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x : OneSum M) (n : N) :
    Metric.infDist x (attachmentSet a H) ≤ attachmentTargetCost V a y H x n := by
  rw [attachmentTargetCost]
  apply le_ciInf
  intro p
  calc
    Metric.infDist x (attachmentSet a H) ≤ dist x (attachmentPoint a H p) :=
      Metric.infDist_le_dist_of_mem (attachmentPoint_mem_attachmentSet a H p)
    _ ≤ dist x (attachmentPoint a H p) + dist (attachmentMap V y p) n := by
      exact le_add_of_nonneg_right dist_nonneg

/-- Inside the protected vertical collar, the source--target adjunction cost is
exactly the vertical distance to the base plus the old-target distance from
the image of the horizontal coordinate. -/
theorem attachmentTargetCost_eq_collar
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [PseudoMetricSpace N]
    {V : M → N} {a : M} {y : N} {H r : ℝ}
    (hr : 0 < r) (hH : 2 * r + dist (V a) y < H)
    (hshort : PreservesUpTo r V) (m : M) {s : ℝ} (hs : |s| < r) (n : N) :
    attachmentTargetCost V a y H (toLp 1 (m, s)) n =
      |s| + dist (V m) n := by
  have hV := preservesUpTo_nonexpansive hr hshort
  have hHpos : 0 < H := by
    have hnonneg : 0 ≤ 2 * r + dist (V a) y := by positivity
    linarith
  have hs_le_H : s ≤ H := by
    have hsabs : s ≤ |s| := le_abs_self s
    have hgap_nonneg : 0 ≤ dist (V a) y := dist_nonneg
    linarith
  have hbase (v : M) :
      dist (toLp 1 (m, s) : OneSum M) (attachmentPoint a H (Sum.inl v)) =
        dist m v + |s| := by
    simp [attachmentPoint,
      WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  have htop :
      dist (toLp 1 (m, s) : OneSum M) (attachmentPoint a H (Sum.inr ())) =
        dist m a + (H - s) := by
    simp [attachmentPoint,
      WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs_le_H)]
  apply le_antisymm
  · calc
      attachmentTargetCost V a y H (toLp 1 (m, s)) n ≤
          dist (toLp 1 (m, s) : OneSum M) (attachmentPoint a H (Sum.inl m)) +
            dist (attachmentMap V y (Sum.inl m)) n :=
        attachmentTargetCost_le V a y H _ n (Sum.inl m)
      _ = |s| + dist (V m) n := by
        rw [hbase]
        simp [attachmentMap]
  · rw [attachmentTargetCost]
    apply le_ciInf
    intro p
    cases p with
    | inl v =>
        rw [hbase]
        change |s| + dist (V m) n ≤ dist m v + |s| + dist (V v) n
        have htri := dist_triangle (V m) (V v) n
        have hnonexp := hV m v
        linarith
    | inr star =>
        rw [htop]
        change |s| + dist (V m) n ≤ dist m a + (H - s) + dist y n
        have htri := dist_triangle4 (V m) (V a) y n
        have hnonexp := hV m a
        have hsabs : s ≤ |s| := le_abs_self s
        linarith

theorem attachmentExcursionCost_nonneg
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ : OneSum M) :
    0 ≤ attachmentExcursionCost V a y H x₀ x₁ := by
  rw [attachmentExcursionCost]
  apply le_ciInf
  intro p
  apply le_ciInf
  intro q
  positivity

theorem attachmentExcursionCost_le
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ : OneSum M)
    (p q : M ⊕ Unit) :
    attachmentExcursionCost V a y H x₀ x₁ ≤
      dist x₀ (attachmentPoint a H p) +
        dist (attachmentMap V y p) (attachmentMap V y q) +
        dist (attachmentPoint a H q) x₁ := by
  rw [attachmentExcursionCost]
  have hinner (p' : M ⊕ Unit) : BddBelow (Set.range fun q' : M ⊕ Unit =>
      dist x₀ (attachmentPoint a H p') +
        dist (attachmentMap V y p') (attachmentMap V y q') +
        dist (attachmentPoint a H q') x₁) :=
    ⟨0, Set.forall_mem_range.2 fun q' => by positivity⟩
  have houter : BddBelow (Set.range fun p' : M ⊕ Unit =>
      ⨅ q' : M ⊕ Unit,
        dist x₀ (attachmentPoint a H p') +
          dist (attachmentMap V y p') (attachmentMap V y q') +
          dist (attachmentPoint a H q') x₁) := by
    refine ⟨0, Set.forall_mem_range.2 ?_⟩
    intro p'
    apply le_ciInf
    intro q'
    positivity
  exact ciInf_le_of_le houter p (ciInf_le (hinner p) q)

theorem attachmentExcursionCost_comm
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ : OneSum M) :
    attachmentExcursionCost V a y H x₀ x₁ =
      attachmentExcursionCost V a y H x₁ x₀ := by
  apply le_antisymm
  · rw [attachmentExcursionCost]
    apply le_ciInf
    intro p
    apply le_ciInf
    intro q
    calc
      attachmentExcursionCost V a y H x₀ x₁ ≤
          dist x₀ (attachmentPoint a H q) +
            dist (attachmentMap V y q) (attachmentMap V y p) +
            dist (attachmentPoint a H p) x₁ :=
        attachmentExcursionCost_le V a y H x₀ x₁ q p
      _ = dist x₁ (attachmentPoint a H p) +
            dist (attachmentMap V y p) (attachmentMap V y q) +
            dist (attachmentPoint a H q) x₀ := by
        rw [dist_comm x₀, dist_comm (attachmentMap V y q),
          dist_comm (attachmentPoint a H p)]
        ring
  · rw [attachmentExcursionCost]
    apply le_ciInf
    intro p
    apply le_ciInf
    intro q
    calc
      attachmentExcursionCost V a y H x₁ x₀ ≤
          dist x₁ (attachmentPoint a H q) +
            dist (attachmentMap V y q) (attachmentMap V y p) +
            dist (attachmentPoint a H p) x₀ :=
        attachmentExcursionCost_le V a y H x₁ x₀ q p
      _ = dist x₀ (attachmentPoint a H p) +
            dist (attachmentMap V y p) (attachmentMap V y q) +
            dist (attachmentPoint a H q) x₁ := by
        rw [dist_comm x₁, dist_comm (attachmentMap V y q),
          dist_comm (attachmentPoint a H p)]
        ring

theorem infDist_attachmentSet_le_excursionCost_left
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ : OneSum M) :
    Metric.infDist x₀ (attachmentSet a H) ≤
      attachmentExcursionCost V a y H x₀ x₁ := by
  rw [attachmentExcursionCost]
  apply le_ciInf
  intro p
  apply le_ciInf
  intro q
  calc
    Metric.infDist x₀ (attachmentSet a H) ≤ dist x₀ (attachmentPoint a H p) :=
      Metric.infDist_le_dist_of_mem (attachmentPoint_mem_attachmentSet a H p)
    _ ≤ dist x₀ (attachmentPoint a H p) +
          dist (attachmentMap V y p) (attachmentMap V y q) +
          dist (attachmentPoint a H q) x₁ := by
      have h₁ : 0 ≤ dist (attachmentMap V y p) (attachmentMap V y q) := dist_nonneg
      have h₂ : 0 ≤ dist (attachmentPoint a H q) x₁ := dist_nonneg
      linarith

theorem infDist_attachmentSet_le_excursionCost_right
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ : OneSum M) :
    Metric.infDist x₁ (attachmentSet a H) ≤
      attachmentExcursionCost V a y H x₀ x₁ := by
  rw [attachmentExcursionCost]
  apply le_ciInf
  intro p
  apply le_ciInf
  intro q
  calc
    Metric.infDist x₁ (attachmentSet a H) ≤ dist x₁ (attachmentPoint a H q) :=
      Metric.infDist_le_dist_of_mem (attachmentPoint_mem_attachmentSet a H q)
    _ = dist (attachmentPoint a H q) x₁ := dist_comm _ _
    _ ≤ dist x₀ (attachmentPoint a H p) +
          dist (attachmentMap V y p) (attachmentMap V y q) +
          dist (attachmentPoint a H q) x₁ := by
      have h₁ : 0 ≤ dist x₀ (attachmentPoint a H p) := dist_nonneg
      have h₂ : 0 ≤ dist (attachmentMap V y p) (attachmentMap V y q) := dist_nonneg
      linarith

theorem dist_attachmentMap_le_excursionCost
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [MetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (p q : M ⊕ Unit) :
    dist (attachmentMap V y p) (attachmentMap V y q) ≤
      attachmentExcursionCost V a y H (attachmentPoint a H p) (attachmentPoint a H q) := by
  rw [attachmentExcursionCost]
  apply le_ciInf
  intro s
  apply le_ciInf
  intro t
  have hleft := hattach p s
  have hright := hattach t q
  have htarget := dist_triangle4 (attachmentMap V y p) (attachmentMap V y s)
    (attachmentMap V y t) (attachmentMap V y q)
  linarith

/-- Zero excursion cost forces equal source points when the prescribed
attachment map is injective. -/
theorem eq_of_attachmentExcursionCost_eq_zero
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [MetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hinj : Function.Injective (attachmentMap V y))
    {x₀ x₁ : OneSum M}
    (hzero : attachmentExcursionCost V a y H x₀ x₁ = 0) : x₀ = x₁ := by
  have hne : (attachmentSet a H).Nonempty :=
    ⟨attachmentPoint a H (Sum.inr ()), attachmentPoint_mem_attachmentSet a H _⟩
  have hx₀zero : Metric.infDist x₀ (attachmentSet a H) = 0 := by
    have hle := infDist_attachmentSet_le_excursionCost_left V a y H x₀ x₁
    have hnonneg : 0 ≤ Metric.infDist x₀ (attachmentSet a H) := Metric.infDist_nonneg
    linarith
  have hx₁zero : Metric.infDist x₁ (attachmentSet a H) = 0 := by
    have hle := infDist_attachmentSet_le_excursionCost_right V a y H x₀ x₁
    have hnonneg : 0 ≤ Metric.infDist x₁ (attachmentSet a H) := Metric.infDist_nonneg
    linarith
  have hx₀ : x₀ ∈ attachmentSet a H :=
    ((isClosed_attachmentSet a H).mem_iff_infDist_zero hne).2 hx₀zero
  have hx₁ : x₁ ∈ attachmentSet a H :=
    ((isClosed_attachmentSet a H).mem_iff_infDist_zero hne).2 hx₁zero
  rcases hx₀ with ⟨p, rfl⟩
  rcases hx₁ with ⟨q, rfl⟩
  have hmapzero : dist (attachmentMap V y p) (attachmentMap V y q) = 0 := by
    have hle := dist_attachmentMap_le_excursionCost V a y H hattach p q
    have hnonneg : 0 ≤ dist (attachmentMap V y p) (attachmentMap V y q) := dist_nonneg
    linarith
  exact congrArg (attachmentPoint a H) (hinj (dist_eq_zero.mp hmapzero))

theorem eq_of_sourceAdjunctionDist_eq_zero
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [MetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hinj : Function.Injective (attachmentMap V y))
    {x₀ x₁ : OneSum M} (hzero : sourceAdjunctionDist V a y H x₀ x₁ = 0) :
    x₀ = x₁ := by
  by_cases hdirect : dist x₀ x₁ ≤ attachmentExcursionCost V a y H x₀ x₁
  · apply dist_eq_zero.mp
    simpa [sourceAdjunctionDist, min_eq_left hdirect] using hzero
  · apply eq_of_attachmentExcursionCost_eq_zero V a y H hattach hinj
    simpa [sourceAdjunctionDist, min_eq_right (le_of_not_ge hdirect)] using hzero

theorem sourceAdjunctionDist_comm
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ : OneSum M) :
    sourceAdjunctionDist V a y H x₀ x₁ = sourceAdjunctionDist V a y H x₁ x₀ := by
  rw [sourceAdjunctionDist, sourceAdjunctionDist, dist_comm x₀ x₁,
    attachmentExcursionCost_comm V a y H x₀ x₁]

theorem sourceAdjunctionDist_le_excursion
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ : OneSum M)
    (p q : M ⊕ Unit) :
    sourceAdjunctionDist V a y H x₀ x₁ ≤
      dist x₀ (attachmentPoint a H p) +
        dist (attachmentMap V y p) (attachmentMap V y q) +
        dist (attachmentPoint a H q) x₁ := by
  exact (min_le_right _ _).trans (attachmentExcursionCost_le V a y H x₀ x₁ p q)

/-- One mixed triangle inequality: moving inside the old target after entering
it cannot make the source--target cost larger than the corresponding sum. -/
theorem attachmentTargetCost_triangle_target
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (x : OneSum M) (n₀ n₁ : N) :
    attachmentTargetCost V a y H x n₁ ≤
      attachmentTargetCost V a y H x n₀ + dist n₀ n₁ := by
  rw [attachmentTargetCost]
  apply le_ciInf_add
  intro p
  calc
    attachmentTargetCost V a y H x n₁ ≤
        dist x (attachmentPoint a H p) + dist (attachmentMap V y p) n₁ :=
      attachmentTargetCost_le V a y H x n₁ p
    _ ≤ (dist x (attachmentPoint a H p) + dist (attachmentMap V y p) n₀) +
          dist n₀ n₁ := by
      linarith [dist_triangle (attachmentMap V y p) n₀ n₁]

/-- A target point may serve as the middle vertex of a source--source
triangle. -/
theorem sourceAdjunctionDist_triangle_target
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (x₀ x₁ : OneSum M) (n : N) :
    sourceAdjunctionDist V a y H x₀ x₁ ≤
      attachmentTargetCost V a y H x₀ n + attachmentTargetCost V a y H x₁ n := by
  rw [attachmentTargetCost, attachmentTargetCost]
  apply le_ciInf_add_ciInf
  intro p q
  calc
    sourceAdjunctionDist V a y H x₀ x₁ ≤
        dist x₀ (attachmentPoint a H p) +
          dist (attachmentMap V y p) (attachmentMap V y q) +
          dist (attachmentPoint a H q) x₁ :=
      sourceAdjunctionDist_le_excursion V a y H x₀ x₁ p q
    _ ≤ (dist x₀ (attachmentPoint a H p) + dist (attachmentMap V y p) n) +
          (dist x₁ (attachmentPoint a H q) + dist (attachmentMap V y q) n) := by
      have ht := dist_triangle (attachmentMap V y p) n (attachmentMap V y q)
      rw [dist_comm n (attachmentMap V y q)] at ht
      linarith [dist_comm (attachmentPoint a H q) x₁]

/-- If the attachment map is nonexpansive, a source point may serve as the
middle vertex of an old-target triangle. -/
theorem dist_triangle_attachmentTargetCost
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (n₀ n₁ : N) (x : OneSum M) :
    dist n₀ n₁ ≤
      attachmentTargetCost V a y H x n₀ + attachmentTargetCost V a y H x n₁ := by
  rw [attachmentTargetCost, attachmentTargetCost]
  apply le_ciInf_add_ciInf
  intro p q
  have hsource := dist_triangle (attachmentPoint a H p) x (attachmentPoint a H q)
  have htarget := dist_triangle4 n₀ (attachmentMap V y p) (attachmentMap V y q) n₁
  have hmap := hattach p q
  rw [dist_comm (attachmentPoint a H p) x] at hsource
  rw [dist_comm n₀ (attachmentMap V y p)] at htarget
  linarith

theorem adjunctionPreDist_triangle_middle_target
    {M : Type u} [NormedAddCommGroup M]
    {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (z₀ z₁ : OneSum M ⊕ N) (n : N) :
    adjunctionPreDist V a y H z₀ z₁ ≤
      adjunctionPreDist V a y H z₀ (Sum.inr n) +
        adjunctionPreDist V a y H (Sum.inr n) z₁ := by
  cases z₀ with
  | inl x₀ =>
      cases z₁ with
      | inl x₁ => exact sourceAdjunctionDist_triangle_target V a y H x₀ x₁ n
      | inr n₁ => exact attachmentTargetCost_triangle_target V a y H x₀ n n₁
  | inr n₀ =>
      cases z₁ with
      | inl x₁ =>
          change attachmentTargetCost V a y H x₁ n₀ ≤
            dist n₀ n + attachmentTargetCost V a y H x₁ n
          have h := attachmentTargetCost_triangle_target V a y H x₁ n n₀
          rw [dist_comm n n₀] at h
          linarith
      | inr n₁ => exact dist_triangle n₀ n n₁

/-- Mixed triangle inequality with a source point in the middle.  The proof
splits according to which branch of the source--source minimum is active. -/
theorem attachmentTargetCost_triangle_source
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (x₀ x₁ : OneSum M) (n : N) :
    attachmentTargetCost V a y H x₀ n ≤
      sourceAdjunctionDist V a y H x₀ x₁ + attachmentTargetCost V a y H x₁ n := by
  by_cases hdirect : dist x₀ x₁ ≤ attachmentExcursionCost V a y H x₀ x₁
  · rw [sourceAdjunctionDist, min_eq_left hdirect, attachmentTargetCost]
    apply le_add_ciInf
    intro p
    calc
      attachmentTargetCost V a y H x₀ n ≤
          dist x₀ (attachmentPoint a H p) + dist (attachmentMap V y p) n :=
        attachmentTargetCost_le V a y H x₀ n p
      _ ≤ dist x₀ x₁ +
          (dist x₁ (attachmentPoint a H p) + dist (attachmentMap V y p) n) := by
        linarith [dist_triangle x₀ x₁ (attachmentPoint a H p)]
  · rw [sourceAdjunctionDist, min_eq_right (le_of_not_ge hdirect),
      attachmentExcursionCost, attachmentTargetCost]
    apply le_ciInf_add_ciInf
    intro p r
    apply le_ciInf_add
    intro q
    calc
      attachmentTargetCost V a y H x₀ n ≤
          dist x₀ (attachmentPoint a H p) + dist (attachmentMap V y p) n :=
        attachmentTargetCost_le V a y H x₀ n p
      _ ≤ (dist x₀ (attachmentPoint a H p) +
            dist (attachmentMap V y p) (attachmentMap V y q) +
            dist (attachmentPoint a H q) x₁) +
          (dist x₁ (attachmentPoint a H r) + dist (attachmentMap V y r) n) := by
        have hsource := dist_triangle (attachmentPoint a H q) x₁ (attachmentPoint a H r)
        have hmap := hattach q r
        have htarget := dist_triangle4 (attachmentMap V y p) (attachmentMap V y q)
          (attachmentMap V y r) n
        linarith

theorem adjunctionPreDist_triangle_target_source_target
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (n₀ n₁ : N) (x : OneSum M) :
    adjunctionPreDist V a y H (Sum.inr n₀) (Sum.inr n₁) ≤
      adjunctionPreDist V a y H (Sum.inr n₀) (Sum.inl x) +
        adjunctionPreDist V a y H (Sum.inl x) (Sum.inr n₁) :=
  dist_triangle_attachmentTargetCost V a y H hattach n₀ n₁ x

theorem adjunctionPreDist_triangle_source_source_target
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (x₀ x₁ : OneSum M) (n : N) :
    adjunctionPreDist V a y H (Sum.inl x₀) (Sum.inr n) ≤
      adjunctionPreDist V a y H (Sum.inl x₀) (Sum.inl x₁) +
        adjunctionPreDist V a y H (Sum.inl x₁) (Sum.inr n) :=
  attachmentTargetCost_triangle_source V a y H hattach x₀ x₁ n

theorem sourceAdjunctionDist_triangle_direct_left
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ x₂ : OneSum M) :
    sourceAdjunctionDist V a y H x₀ x₂ ≤
      dist x₀ x₁ + sourceAdjunctionDist V a y H x₁ x₂ := by
  by_cases hdirect : dist x₁ x₂ ≤ attachmentExcursionCost V a y H x₁ x₂
  · have hbranch : sourceAdjunctionDist V a y H x₁ x₂ = dist x₁ x₂ := by
      rw [sourceAdjunctionDist, min_eq_left hdirect]
    rw [hbranch]
    exact (min_le_left _ _).trans (dist_triangle x₀ x₁ x₂)
  · have hbranch : sourceAdjunctionDist V a y H x₁ x₂ =
        attachmentExcursionCost V a y H x₁ x₂ := by
      rw [sourceAdjunctionDist, min_eq_right (le_of_not_ge hdirect)]
    rw [hbranch, attachmentExcursionCost]
    apply le_add_ciInf
    intro p
    apply le_add_ciInf
    intro q
    calc
      sourceAdjunctionDist V a y H x₀ x₂ ≤
          dist x₀ (attachmentPoint a H p) +
            dist (attachmentMap V y p) (attachmentMap V y q) +
            dist (attachmentPoint a H q) x₂ :=
        sourceAdjunctionDist_le_excursion V a y H x₀ x₂ p q
      _ ≤ dist x₀ x₁ +
          (dist x₁ (attachmentPoint a H p) +
            dist (attachmentMap V y p) (attachmentMap V y q) +
            dist (attachmentPoint a H q) x₂) := by
        linarith [dist_triangle x₀ x₁ (attachmentPoint a H p)]

theorem sourceAdjunctionDist_triangle_direct_right
    {M : Type u} [NormedAddCommGroup M]
    {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ x₂ : OneSum M) :
    sourceAdjunctionDist V a y H x₀ x₂ ≤
      sourceAdjunctionDist V a y H x₀ x₁ + dist x₁ x₂ := by
  have h := sourceAdjunctionDist_triangle_direct_left V a y H x₂ x₁ x₀
  rw [sourceAdjunctionDist_comm V a y H x₂ x₀,
    sourceAdjunctionDist_comm V a y H x₁ x₀, dist_comm x₂ x₁] at h
  linarith

theorem sourceAdjunctionDist_triangle
    {M : Type u} [NormedAddCommGroup M]
    {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (x₀ x₁ x₂ : OneSum M) :
    sourceAdjunctionDist V a y H x₀ x₂ ≤
      sourceAdjunctionDist V a y H x₀ x₁ + sourceAdjunctionDist V a y H x₁ x₂ := by
  by_cases h₀₁ : dist x₀ x₁ ≤ attachmentExcursionCost V a y H x₀ x₁
  · have hbranch : sourceAdjunctionDist V a y H x₀ x₁ = dist x₀ x₁ := by
      rw [sourceAdjunctionDist, min_eq_left h₀₁]
    rw [hbranch]
    exact sourceAdjunctionDist_triangle_direct_left V a y H x₀ x₁ x₂
  · have hbranch₀₁ : sourceAdjunctionDist V a y H x₀ x₁ =
        attachmentExcursionCost V a y H x₀ x₁ := by
      rw [sourceAdjunctionDist, min_eq_right (le_of_not_ge h₀₁)]
    rw [hbranch₀₁]
    by_cases h₁₂ : dist x₁ x₂ ≤ attachmentExcursionCost V a y H x₁ x₂
    · have hbranch₁₂ : sourceAdjunctionDist V a y H x₁ x₂ = dist x₁ x₂ := by
        rw [sourceAdjunctionDist, min_eq_left h₁₂]
      rw [hbranch₁₂]
      have h := sourceAdjunctionDist_triangle_direct_right V a y H x₀ x₁ x₂
      rw [hbranch₀₁] at h
      exact h
    · have hbranch₁₂ : sourceAdjunctionDist V a y H x₁ x₂ =
          attachmentExcursionCost V a y H x₁ x₂ := by
        rw [sourceAdjunctionDist, min_eq_right (le_of_not_ge h₁₂)]
      rw [hbranch₁₂, attachmentExcursionCost, attachmentExcursionCost]
      apply le_ciInf_add_ciInf
      intro p s
      apply le_ciInf_add_ciInf
      intro q t
      calc
        sourceAdjunctionDist V a y H x₀ x₂ ≤
            dist x₀ (attachmentPoint a H p) +
              dist (attachmentMap V y p) (attachmentMap V y t) +
              dist (attachmentPoint a H t) x₂ :=
          sourceAdjunctionDist_le_excursion V a y H x₀ x₂ p t
        _ ≤ (dist x₀ (attachmentPoint a H p) +
              dist (attachmentMap V y p) (attachmentMap V y q) +
              dist (attachmentPoint a H q) x₁) +
            (dist x₁ (attachmentPoint a H s) +
              dist (attachmentMap V y s) (attachmentMap V y t) +
              dist (attachmentPoint a H t) x₂) := by
          have hsource := dist_triangle (attachmentPoint a H q) x₁
            (attachmentPoint a H s)
          have hmap := hattach q s
          have htarget := dist_triangle4 (attachmentMap V y p) (attachmentMap V y q)
            (attachmentMap V y s) (attachmentMap V y t)
          linarith

theorem sourceAdjunctionDist_self
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x : OneSum M) :
    sourceAdjunctionDist V a y H x x = 0 := by
  rw [sourceAdjunctionDist, dist_self, min_eq_left]
  exact attachmentExcursionCost_nonneg V a y H x x

theorem adjunctionPreDist_self
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) :
    ∀ z : OneSum M ⊕ N, adjunctionPreDist V a y H z z = 0
  | Sum.inl x => sourceAdjunctionDist_self V a y H x
  | Sum.inr n => dist_self n

theorem adjunctionPreDist_comm
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) :
    ∀ z₀ z₁ : OneSum M ⊕ N,
      adjunctionPreDist V a y H z₀ z₁ = adjunctionPreDist V a y H z₁ z₀
  | Sum.inl x₀, Sum.inl x₁ => sourceAdjunctionDist_comm V a y H x₀ x₁
  | Sum.inl _, Sum.inr _ => rfl
  | Sum.inr _, Sum.inl _ => rfl
  | Sum.inr n₀, Sum.inr n₁ => dist_comm n₀ n₁

theorem adjunctionPreDist_triangle
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) :
    ∀ z₀ z₁ z₂ : OneSum M ⊕ N,
      adjunctionPreDist V a y H z₀ z₂ ≤
        adjunctionPreDist V a y H z₀ z₁ + adjunctionPreDist V a y H z₁ z₂
  | Sum.inl x₀, Sum.inl x₁, Sum.inl x₂ =>
      sourceAdjunctionDist_triangle V a y H hattach x₀ x₁ x₂
  | Sum.inl x₀, Sum.inl x₁, Sum.inr n₂ =>
      attachmentTargetCost_triangle_source V a y H hattach x₀ x₁ n₂
  | Sum.inl x₀, Sum.inr n₁, Sum.inl x₂ =>
      sourceAdjunctionDist_triangle_target V a y H x₀ x₂ n₁
  | Sum.inl x₀, Sum.inr n₁, Sum.inr n₂ =>
      attachmentTargetCost_triangle_target V a y H x₀ n₁ n₂
  | Sum.inr n₀, Sum.inl x₁, Sum.inl x₂ => by
      change attachmentTargetCost V a y H x₂ n₀ ≤
        attachmentTargetCost V a y H x₁ n₀ + sourceAdjunctionDist V a y H x₁ x₂
      have h := attachmentTargetCost_triangle_source V a y H hattach x₂ x₁ n₀
      rw [sourceAdjunctionDist_comm V a y H x₂ x₁] at h
      linarith
  | Sum.inr n₀, Sum.inl x₁, Sum.inr n₂ =>
      dist_triangle_attachmentTargetCost V a y H hattach n₀ n₂ x₁
  | Sum.inr n₀, Sum.inr n₁, Sum.inl x₂ => by
      change attachmentTargetCost V a y H x₂ n₀ ≤
        dist n₀ n₁ + attachmentTargetCost V a y H x₂ n₁
      have h := attachmentTargetCost_triangle_target V a y H x₂ n₁ n₀
      rw [dist_comm n₁ n₀] at h
      linarith
  | Sum.inr n₀, Sum.inr n₁, Sum.inr n₂ => dist_triangle n₀ n₁ n₂

/-- The gluing pseudometric on the disjoint union of the one-sum source and target, under
the attachment distance bound. -/
@[implicit_reducible]
noncomputable def adjunctionPseudoMetricSpace
    {M : Type u} [NormedAddCommGroup M]
    {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) :
    PseudoMetricSpace (OneSum M ⊕ N) where
  dist := adjunctionPreDist V a y H
  dist_self := adjunctionPreDist_self V a y H
  dist_comm := adjunctionPreDist_comm V a y H
  dist_triangle := adjunctionPreDist_triangle V a y H hattach

theorem attachmentTargetCost_glued
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (p : M ⊕ Unit) :
    attachmentTargetCost V a y H (attachmentPoint a H p) (attachmentMap V y p) = 0 := by
  apply le_antisymm
  · rw [attachmentTargetCost]
    have hb : BddBelow (Set.range fun q : M ⊕ Unit =>
        dist (attachmentPoint a H p) (attachmentPoint a H q) +
          dist (attachmentMap V y q) (attachmentMap V y p)) := by
      refine ⟨0, Set.forall_mem_range.2 ?_⟩
      intro q
      positivity
    exact (ciInf_le hb p).trans_eq (by simp)
  · exact attachmentTargetCost_nonneg V a y H _ _

theorem adjunctionPreDist_glued
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (p : M ⊕ Unit) :
    adjunctionPreDist V a y H (Sum.inl (attachmentPoint a H p))
      (Sum.inr (attachmentMap V y p)) = 0 :=
  attachmentTargetCost_glued V a y H p

theorem adjunctionPreDist_target
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (n₀ n₁ : N) :
    adjunctionPreDist V a y H (Sum.inr n₀) (Sum.inr n₁) = dist n₀ n₁ :=
  rfl

theorem sourceAdjunctionDist_le
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ) (x₀ x₁ : OneSum M) :
    sourceAdjunctionDist V a y H x₀ x₁ ≤ dist x₀ x₁ :=
  min_le_left _ _

/-- For a short source pair, every excursion through the attachment set and
the old target has length at least the original source distance. -/
theorem dist_le_attachmentExcursionCost_of_short
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [PseudoMetricSpace N]
    {V : M → N} {a : M} {y : N} {H r : ℝ}
    (hr : 0 < r) (hH : 2 * r < H) (hshort : PreservesUpTo r V)
    {x₀ x₁ : OneSum M} (hd : dist x₀ x₁ ≤ r) :
    dist x₀ x₁ ≤ attachmentExcursionCost V a y H x₀ x₁ := by
  have hV : ∀ m n, dist (V m) (V n) ≤ dist m n :=
    preservesUpTo_nonexpansive hr hshort
  rw [attachmentExcursionCost]
  apply le_ciInf
  intro p
  apply le_ciInf
  intro q
  cases p with
  | inl u =>
      cases q with
      | inl v =>
          have hhorizontal :
              dist x₀.fst x₁.fst ≤
                dist x₀.fst u + dist (V u) (V v) + dist v x₁.fst := by
            calc
              dist x₀.fst x₁.fst = dist (V x₀.fst) (V x₁.fst) := by
                symm
                apply hshort
                rw [oneSum_dist_eq] at hd
                linarith [abs_nonneg (x₀.snd - x₁.snd)]
              _ ≤ dist (V x₀.fst) (V u) + dist (V u) (V v) +
                    dist (V v) (V x₁.fst) := dist_triangle4 _ _ _ _
              _ ≤ dist x₀.fst u + dist (V u) (V v) + dist v x₁.fst := by
                gcongr
                · exact hV x₀.fst u
                · exact hV v x₁.fst
          rw [oneSum_dist_eq, attachmentPoint, attachmentPoint,
            oneSum_dist_eq, oneSum_dist_eq]
          simp only [toLp_fst, toLp_snd, attachmentMap, sub_zero, zero_sub]
          rw [abs_neg]
          have habs : |x₀.snd - x₁.snd| ≤ |x₀.snd| + |x₁.snd| := by
            simpa [sub_eq_add_neg] using abs_add_le x₀.snd (-x₁.snd)
          linarith
      | inr star =>
          have hatt : H ≤
              dist x₀ (attachmentPoint a H (Sum.inl u)) + dist x₀ x₁ +
                dist (attachmentPoint a H (Sum.inr star)) x₁ := by
            calc
              H ≤ dist (attachmentPoint a H (Sum.inl u))
                    (attachmentPoint a H (Sum.inr star)) := by
                rw [dist_attachmentPoint_base_top]
                · exact le_add_of_nonneg_left dist_nonneg
                · linarith
              _ ≤ dist (attachmentPoint a H (Sum.inl u)) x₀ + dist x₀ x₁ +
                    dist x₁ (attachmentPoint a H (Sum.inr star)) :=
                dist_triangle4 _ _ _ _
              _ = _ := by rw [dist_comm (attachmentPoint a H (Sum.inl u)) x₀,
                dist_comm x₁ (attachmentPoint a H (Sum.inr star))]
          have htwo : 2 * dist x₀ x₁ < H := by linarith
          have htarget : 0 ≤ dist (attachmentMap V y (Sum.inl u))
              (attachmentMap V y (Sum.inr star)) := dist_nonneg
          linarith
  | inr star =>
      cases q with
      | inl v =>
          have hatt : H ≤
              dist x₀ (attachmentPoint a H (Sum.inr star)) + dist x₀ x₁ +
                dist (attachmentPoint a H (Sum.inl v)) x₁ := by
            calc
              H ≤ dist (attachmentPoint a H (Sum.inr star))
                    (attachmentPoint a H (Sum.inl v)) := by
                rw [dist_comm, dist_attachmentPoint_base_top]
                · exact le_add_of_nonneg_left dist_nonneg
                · linarith
              _ ≤ dist (attachmentPoint a H (Sum.inr star)) x₀ + dist x₀ x₁ +
                    dist x₁ (attachmentPoint a H (Sum.inl v)) :=
                dist_triangle4 _ _ _ _
              _ = _ := by rw [dist_comm (attachmentPoint a H (Sum.inr star)) x₀,
                dist_comm x₁ (attachmentPoint a H (Sum.inl v))]
          have htwo : 2 * dist x₀ x₁ < H := by linarith
          have htarget : 0 ≤ dist (attachmentMap V y (Sum.inr star))
              (attachmentMap V y (Sum.inl v)) := dist_nonneg
          linarith
      | inr other =>
          simp only [attachmentMap, dist_self, add_zero]
          exact dist_triangle _ _ _

/-- The source-side adjunction formula preserves every distance at most `r`. -/
theorem sourceAdjunctionDist_eq_of_short
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [PseudoMetricSpace N]
    {V : M → N} {a : M} {y : N} {H r : ℝ}
    (hr : 0 < r) (hH : 2 * r < H) (hshort : PreservesUpTo r V)
    {x₀ x₁ : OneSum M} (hd : dist x₀ x₁ ≤ r) :
    sourceAdjunctionDist V a y H x₀ x₁ = dist x₀ x₁ := by
  rw [sourceAdjunctionDist, min_eq_left]
  exact dist_le_attachmentExcursionCost_of_short hr hH hshort hd

theorem adjunctionPreDist_source_eq_of_short
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [PseudoMetricSpace N]
    {V : M → N} {a : M} {y : N} {H r : ℝ}
    (hr : 0 < r) (hH : 2 * r < H) (hshort : PreservesUpTo r V)
    {x₀ x₁ : OneSum M} (hd : dist x₀ x₁ ≤ r) :
    adjunctionPreDist V a y H (Sum.inl x₀) (Sum.inl x₁) = dist x₀ x₁ :=
  sourceAdjunctionDist_eq_of_short hr hH hshort hd

/-- The metric separation quotient realizing the asymmetric metric
adjunction. -/
noncomputable def AdjunctionSpace
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) : Type (max u v) :=
  @SeparationQuotient (OneSum M ⊕ N)
    (adjunctionPseudoMetricSpace V a y H hattach).toUniformSpace.toTopologicalSpace

noncomputable instance
    {M : Type u} [NormedAddCommGroup M]
    {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) :
    MetricSpace (AdjunctionSpace V a y H hattach) :=
  inferInstanceAs <| MetricSpace <| @SeparationQuotient (OneSum M ⊕ N)
    (adjunctionPseudoMetricSpace V a y H hattach).toUniformSpace.toTopologicalSpace

/-- The canonical map from the one-sum source into the metric adjunction space. -/
noncomputable def adjunctionSourceMk
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (x : OneSum M) : AdjunctionSpace V a y H hattach :=
  Quotient.mk'' (Sum.inl x)

noncomputable instance adjunctionSpaceNonempty
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) :
    Nonempty (AdjunctionSpace V a y H hattach) :=
  ⟨adjunctionSourceMk V a y H hattach 0⟩

/-- The canonical map from the target into the metric adjunction space. -/
noncomputable def adjunctionTargetMk
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (n : N) : AdjunctionSpace V a y H hattach :=
  Quotient.mk'' (Sum.inr n)

theorem dist_adjunctionTargetMk
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (n₀ n₁ : N) :
    dist (adjunctionTargetMk V a y H hattach n₀)
      (adjunctionTargetMk V a y H hattach n₁) = dist n₀ n₁ := rfl

theorem dist_adjunctionSourceMk_targetMk_eq_collar
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [PseudoMetricSpace N]
    {V : M → N} {a : M} {y : N} {H r : ℝ}
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hr : 0 < r) (hH : 2 * r + dist (V a) y < H)
    (hshort : PreservesUpTo r V) (m : M) {s : ℝ} (hs : |s| < r) (n : N) :
    dist (adjunctionSourceMk V a y H hattach (toLp 1 (m, s)))
      (adjunctionTargetMk V a y H hattach n) = |s| + dist (V m) n :=
  attachmentTargetCost_eq_collar hr hH hshort m hs n

theorem adjunctionTargetMk_isometry
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) :
    Isometry (adjunctionTargetMk V a y H hattach) :=
  Isometry.of_dist_eq (dist_adjunctionTargetMk V a y H hattach)

theorem adjunctionMk_glued
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (p : M ⊕ Unit) :
    adjunctionSourceMk V a y H hattach (attachmentPoint a H p) =
      adjunctionTargetMk V a y H hattach (attachmentMap V y p) := by
  apply dist_eq_zero.mp
  exact adjunctionPreDist_glued V a y H p

/-- Distance from a source point to the embedded old target is exactly its
distance to the source attachment set. -/
theorem infDist_adjunctionTarget_range_eq_attachmentSet
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) (x : OneSum M) :
    Metric.infDist (adjunctionSourceMk V a y H hattach x)
      (Set.range (adjunctionTargetMk V a y H hattach)) =
        Metric.infDist x (attachmentSet a H) := by
  have htarget : (Set.range (adjunctionTargetMk V a y H hattach)).Nonempty :=
    ⟨adjunctionTargetMk V a y H hattach y, ⟨y, rfl⟩⟩
  have hat : (attachmentSet a H).Nonempty :=
    ⟨attachmentPoint a H (Sum.inr ()), attachmentPoint_mem_attachmentSet a H _⟩
  apply le_antisymm
  · rw [Metric.le_infDist hat]
    intro z hz
    rcases hz with ⟨p, rfl⟩
    calc
      Metric.infDist (adjunctionSourceMk V a y H hattach x)
          (Set.range (adjunctionTargetMk V a y H hattach)) ≤
          dist (adjunctionSourceMk V a y H hattach x)
            (adjunctionTargetMk V a y H hattach (attachmentMap V y p)) :=
        Metric.infDist_le_dist_of_mem ⟨attachmentMap V y p, rfl⟩
      _ = dist (adjunctionSourceMk V a y H hattach x)
            (adjunctionSourceMk V a y H hattach (attachmentPoint a H p)) := by
        rw [adjunctionMk_glued V a y H hattach p]
      _ = sourceAdjunctionDist V a y H x (attachmentPoint a H p) := rfl
      _ ≤ dist x (attachmentPoint a H p) :=
        sourceAdjunctionDist_le V a y H x (attachmentPoint a H p)
  · rw [Metric.le_infDist htarget]
    intro z hz
    rcases hz with ⟨n, rfl⟩
    exact infDist_attachmentSet_le_attachmentTargetCost V a y H x n

theorem dist_adjunctionSourceMk_of_short
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [PseudoMetricSpace N]
    {V : M → N} {a : M} {y : N} {H r : ℝ}
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hr : 0 < r) (hH : 2 * r < H) (hshort : PreservesUpTo r V)
    {x₀ x₁ : OneSum M} (hd : dist x₀ x₁ ≤ r) :
    dist (adjunctionSourceMk V a y H hattach x₀)
      (adjunctionSourceMk V a y H hattach x₁) = dist x₀ x₁ :=
  adjunctionPreDist_source_eq_of_short hr hH hshort hd

theorem adjunctionSourceMk_injective
    {M : Type u} [NormedAddCommGroup M] {N : Type v} [MetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hinj : Function.Injective (attachmentMap V y)) :
    Function.Injective (adjunctionSourceMk V a y H hattach) := by
  intro x₀ x₁ h
  apply eq_of_sourceAdjunctionDist_eq_zero V a y H hattach hinj
  have hzero : dist (adjunctionSourceMk V a y H hattach x₀)
      (adjunctionSourceMk V a y H hattach x₁) = 0 := by
    rw [h, dist_self]
  exact hzero

end ScottishBook155
