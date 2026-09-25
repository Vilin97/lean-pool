/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.KuratowskiCoordinate


/-!
# Collapsing a closed subset to one point

This module constructs the pseudometric on the original space whose metric
separation quotient is the quotient used for the injectivity coordinate.
-/

@[expose] public section

namespace ScottishBook155

open ENNReal lp Metric

universe u

/-- The distance obtained by allowing a path to jump for free inside `S`. -/
noncomputable def collapsedDist {P : Type u} [MetricSpace P] (S : Set P) (x y : P) : ℝ :=
  min (dist x y) (infDist x S + infDist y S)

theorem collapsedDist_self {P : Type u} [MetricSpace P] (S : Set P) (x : P) :
    collapsedDist S x x = 0 := by
  simp [collapsedDist, infDist_nonneg]

theorem collapsedDist_comm {P : Type u} [MetricSpace P] (S : Set P) (x y : P) :
    collapsedDist S x y = collapsedDist S y x := by
  simp [collapsedDist, dist_comm, add_comm]

theorem collapsedDist_triangle {P : Type u} [MetricSpace P] (S : Set P) (x y z : P) :
    collapsedDist S x z ≤ collapsedDist S x y + collapsedDist S y z := by
  unfold collapsedDist
  by_cases hxy : dist x y ≤ infDist x S + infDist y S
  · rw [min_eq_left hxy]
    by_cases hyz : dist y z ≤ infDist y S + infDist z S
    · rw [min_eq_left hyz]
      exact (min_le_left _ _).trans (dist_triangle x y z)
    · rw [min_eq_right (le_of_not_ge hyz)]
      refine (min_le_right _ _).trans ?_
      have hx := infDist_le_infDist_add_dist (x := x) (y := y) (s := S)
      linarith
  · rw [min_eq_right (le_of_not_ge hxy)]
    by_cases hyz : dist y z ≤ infDist y S + infDist z S
    · rw [min_eq_left hyz]
      refine (min_le_right _ _).trans ?_
      have hz := infDist_le_infDist_add_dist (x := z) (y := y) (s := S)
      rw [dist_comm z y] at hz
      linarith
    · rw [min_eq_right (le_of_not_ge hyz)]
      refine (min_le_right _ _).trans ?_
      have hy : 0 ≤ infDist y S := infDist_nonneg
      linarith

/-- The pseudometric whose separation quotient collapses `S`. -/
@[implicit_reducible]
noncomputable def collapsedPseudoMetricSpace {P : Type u} [MetricSpace P] (S : Set P) :
    PseudoMetricSpace P where
  dist := collapsedDist S
  dist_self := collapsedDist_self S
  dist_comm := collapsedDist_comm S
  dist_triangle := collapsedDist_triangle S

/-- The metric separation quotient of the collapsed pseudometric. -/
noncomputable def CollapsedQuotient (P : Type u) [MetricSpace P] (S : Set P) : Type u :=
  letI := collapsedPseudoMetricSpace S
  SeparationQuotient P

noncomputable instance {P : Type u} [MetricSpace P] (S : Set P) :
    MetricSpace (CollapsedQuotient P S) := by
  unfold CollapsedQuotient
  letI := collapsedPseudoMetricSpace S
  infer_instance

/-- The canonical map to the collapsed quotient. -/
noncomputable def collapseMk {P : Type u} [MetricSpace P] (S : Set P) (x : P) :
    CollapsedQuotient P S := by
  unfold CollapsedQuotient
  letI := collapsedPseudoMetricSpace S
  exact SeparationQuotient.mk x

theorem dist_collapseMk {P : Type u} [MetricSpace P] (S : Set P) (x y : P) :
    dist (collapseMk S x) (collapseMk S y) = collapsedDist S x y := rfl

theorem collapseMk_dist_le {P : Type u} [MetricSpace P] (S : Set P) (x y : P) :
    dist (collapseMk S x) (collapseMk S y) ≤ dist x y := by
  rw [dist_collapseMk, collapsedDist]
  exact min_le_left _ _

theorem collapseMk_eq_of_mem {P : Type u} [MetricSpace P] {S : Set P}
    {x y : P} (hx : x ∈ S) (hy : y ∈ S) :
    collapseMk S x = collapseMk S y := by
  apply dist_eq_zero.mp
  rw [dist_collapseMk, collapsedDist]
  simp [infDist_zero_of_mem hx, infDist_zero_of_mem hy]

/-- For a nonempty closed set, the quotient map remains injective away from
the collapsed set. -/
theorem collapseMk_injOn_compl {P : Type u} [MetricSpace P] {S : Set P}
    (hne : S.Nonempty) (hclosed : IsClosed S) :
    Set.InjOn (collapseMk S) Sᶜ := by
  intro x hx y hy hxy
  have hzero : collapsedDist S x y = 0 := by
    rw [← dist_collapseMk, hxy, dist_self]
  by_cases hdirect : dist x y ≤ infDist x S + infDist y S
  · apply dist_eq_zero.mp
    simpa [collapsedDist, min_eq_left hdirect] using hzero
  · have hsum : infDist x S + infDist y S = 0 := by
      simpa [collapsedDist, min_eq_right (le_of_not_ge hdirect)] using hzero
    have hxpos : 0 < infDist x S := (hclosed.notMem_iff_infDist_pos hne).1 hx
    have hypos : 0 < infDist y S := (hclosed.notMem_iff_infDist_pos hne).1 hy
    linarith

theorem collapsedDist_eq_zero_iff {P : Type u} [MetricSpace P] {S : Set P}
    (hne : S.Nonempty) (hclosed : IsClosed S) (x y : P) :
    collapsedDist S x y = 0 ↔ x = y ∨ (x ∈ S ∧ y ∈ S) := by
  constructor
  · intro hzero
    by_cases hdirect : dist x y ≤ infDist x S + infDist y S
    · left
      apply dist_eq_zero.mp
      simpa [collapsedDist, min_eq_left hdirect] using hzero
    · right
      have hsum : infDist x S + infDist y S = 0 := by
        simpa [collapsedDist, min_eq_right (le_of_not_ge hdirect)] using hzero
      have hxzero : infDist x S = 0 := by
        have hxnonneg : 0 ≤ infDist x S := infDist_nonneg
        have hynonneg : 0 ≤ infDist y S := infDist_nonneg
        linarith
      have hyzero : infDist y S = 0 := by
        have hxnonneg : 0 ≤ infDist x S := infDist_nonneg
        have hynonneg : 0 ≤ infDist y S := infDist_nonneg
        linarith
      exact ⟨(hclosed.mem_iff_infDist_zero hne).2 hxzero,
        (hclosed.mem_iff_infDist_zero hne).2 hyzero⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · exact collapsedDist_self S x
    · simp [collapsedDist, infDist_zero_of_mem hx, infDist_zero_of_mem hy]

theorem collapseMk_eq_iff {P : Type u} [MetricSpace P] {S : Set P}
    (hne : S.Nonempty) (hclosed : IsClosed S) (x y : P) :
    collapseMk S x = collapseMk S y ↔ x = y ∨ (x ∈ S ∧ y ∈ S) := by
  rw [← collapsedDist_eq_zero_iff hne hclosed, ← dist_collapseMk, dist_eq_zero]

/-- The manuscript's injectivity coordinate, represented in unrestricted
`ℓ∞` after collapsing `S`. -/
noncomputable def quotientKuratowski {P : Type u} [MetricSpace P]
    (S : Set P) (base : P) (x : P) :
      lp (fun _ : CollapsedQuotient P S ↦ ℝ) ∞ :=
  fullKuratowski (collapseMk S base) (collapseMk S x)

theorem quotientKuratowski_of_mem {P : Type u} [MetricSpace P]
    {S : Set P} {base x : P} (hbase : base ∈ S) (hx : x ∈ S) :
    quotientKuratowski S base x = 0 := by
  rw [quotientKuratowski, collapseMk_eq_of_mem hx hbase, fullKuratowski_base]

theorem quotientKuratowski_dist_le {P : Type u} [MetricSpace P]
    (S : Set P) (base x y : P) :
    dist (quotientKuratowski S base x) (quotientKuratowski S base y) ≤ dist x y := by
  rw [quotientKuratowski, quotientKuratowski,
    (fullKuratowski_isometry (collapseMk S base)).dist_eq, dist_collapseMk]
  exact min_le_left _ _

theorem quotientKuratowski_eq_iff {P : Type u} [MetricSpace P]
    {S : Set P} (hne : S.Nonempty) (hclosed : IsClosed S) (base x y : P) :
    quotientKuratowski S base x = quotientKuratowski S base y ↔
      x = y ∨ (x ∈ S ∧ y ∈ S) := by
  rw [quotientKuratowski, quotientKuratowski,
    (fullKuratowski_isometry (collapseMk S base)).injective.eq_iff,
    collapseMk_eq_iff hne hclosed]

end ScottishBook155
