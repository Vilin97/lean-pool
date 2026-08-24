/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.TerminalCage
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Raw geometric exceptional-word closures

This file connects the local algebraic kernels to finite polygon geometry.
Realization records contain only labelled vertices, distance classes, strict
quadrilateral and half-plane facts, and pointwise arc partitions.  All degree
and cardinality bounds are conclusions of the theorems below.
-/

namespace LeanPool.Erdos132ConvexK3

/-- Translate the first center to the origin and rotate the directed center
line onto the positive horizontal axis. -/
noncomputable def normalizeAlong (a b p : Point ℝ) : Point ℝ :=
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let scale := Real.sqrt (sqDist a b)
  (((p.1 - a.1) * dx + (p.2 - a.2) * dy) / scale,
    (dx * (p.2 - a.2) - dy * (p.1 - a.1)) / scale)

private theorem normalizeAlong_scale_pos {a b : Point ℝ} (hab : a ≠ b) :
    0 < Real.sqrt (sqDist a b) :=
  Real.sqrt_pos.2 (sqDist_pos_of_ne hab)

private theorem normalizeAlong_fst_sub
    (a b p q : Point ℝ) :
    (normalizeAlong a b q).1 - (normalizeAlong a b p).1 =
      ((q.1 - p.1) * (b.1 - a.1) + (q.2 - p.2) * (b.2 - a.2)) /
        Real.sqrt (sqDist a b) := by
  simp only [normalizeAlong]
  ring

private theorem normalizeAlong_snd_sub
    (a b p q : Point ℝ) :
    (normalizeAlong a b q).2 - (normalizeAlong a b p).2 =
      ((b.1 - a.1) * (q.2 - p.2) - (b.2 - a.2) * (q.1 - p.1)) /
        Real.sqrt (sqDist a b) := by
  simp only [normalizeAlong]
  ring

/-- The hand-rolled normalization is an exact Euclidean isometry. -/
theorem normalizeAlong_sqDist
    {a b : Point ℝ} (hab : a ≠ b) (p q : Point ℝ) :
    sqDist (normalizeAlong a b p) (normalizeAlong a b q) = sqDist p q := by
  have hscale := normalizeAlong_scale_pos hab
  have hscaleSq := Real.sq_sqrt (sqDist_nonneg a b)
  change ((normalizeAlong a b q).1 - (normalizeAlong a b p).1) ^ 2 +
      ((normalizeAlong a b q).2 - (normalizeAlong a b p).2) ^ 2 = sqDist p q
  rw [normalizeAlong_fst_sub, normalizeAlong_snd_sub]
  have hid :
      (((q.1 - p.1) * (b.1 - a.1) + (q.2 - p.2) * (b.2 - a.2)) ^ 2 +
        ((b.1 - a.1) * (q.2 - p.2) - (b.2 - a.2) * (q.1 - p.1)) ^ 2) =
      sqDist a b * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by
    simp only [sqDist]
    ring
  calc
    _ = ((((q.1 - p.1) * (b.1 - a.1) + (q.2 - p.2) * (b.2 - a.2)) ^ 2 +
          ((b.1 - a.1) * (q.2 - p.2) - (b.2 - a.2) * (q.1 - p.1)) ^ 2) /
            Real.sqrt (sqDist a b) ^ 2) := by ring
    _ = (sqDist a b * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2)) /
          Real.sqrt (sqDist a b) ^ 2 := by rw [hid]
    _ = (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 := by
      rw [hscaleSq]
      field_simp [ne_of_gt (sqDist_pos_of_ne hab)]
    _ = sqDist p q := by simp only [sqDist]

private theorem normalizeAlong_injective
    {a b : Point ℝ} (hab : a ≠ b) : Function.Injective (normalizeAlong a b) := by
  intro p q hpq
  by_contra hpq'
  have hpositive := sqDist_pos_of_ne hpq'
  have hzero : sqDist (normalizeAlong a b p) (normalizeAlong a b q) = 0 := by
    rw [hpq]
    simp [sqDist]
  rw [normalizeAlong_sqDist hab] at hzero
  linarith

/-- The chosen rotation preserves signed orientation. -/
theorem normalizeAlong_turn
    {a b : Point ℝ} (hab : a ≠ b) (p q r : Point ℝ) :
    turn (normalizeAlong a b p) (normalizeAlong a b q)
      (normalizeAlong a b r) = turn p q r := by
  have hscale := normalizeAlong_scale_pos hab
  have hscaleSq := Real.sq_sqrt (sqDist_nonneg a b)
  change ((normalizeAlong a b q).1 - (normalizeAlong a b p).1) *
      ((normalizeAlong a b r).2 - (normalizeAlong a b p).2) -
      ((normalizeAlong a b q).2 - (normalizeAlong a b p).2) *
        ((normalizeAlong a b r).1 - (normalizeAlong a b p).1) = turn p q r
  rw [normalizeAlong_fst_sub, normalizeAlong_snd_sub,
    normalizeAlong_fst_sub, normalizeAlong_snd_sub]
  have hid :
      (((q.1 - p.1) * (b.1 - a.1) + (q.2 - p.2) * (b.2 - a.2)) *
          ((b.1 - a.1) * (r.2 - p.2) - (b.2 - a.2) * (r.1 - p.1)) -
        ((b.1 - a.1) * (q.2 - p.2) - (b.2 - a.2) * (q.1 - p.1)) *
          ((r.1 - p.1) * (b.1 - a.1) + (r.2 - p.2) * (b.2 - a.2))) =
      sqDist a b * ((q.1 - p.1) * (r.2 - p.2) -
        (q.2 - p.2) * (r.1 - p.1)) := by
    simp only [sqDist]
    ring
  calc
    _ = ((((q.1 - p.1) * (b.1 - a.1) + (q.2 - p.2) * (b.2 - a.2)) *
            ((b.1 - a.1) * (r.2 - p.2) - (b.2 - a.2) * (r.1 - p.1)) -
          ((b.1 - a.1) * (q.2 - p.2) - (b.2 - a.2) * (q.1 - p.1)) *
            ((r.1 - p.1) * (b.1 - a.1) + (r.2 - p.2) * (b.2 - a.2))) /
              Real.sqrt (sqDist a b) ^ 2) := by ring
    _ = (sqDist a b * ((q.1 - p.1) * (r.2 - p.2) -
          (q.2 - p.2) * (r.1 - p.1))) / Real.sqrt (sqDist a b) ^ 2 := by
      rw [hid]
    _ = (q.1 - p.1) * (r.2 - p.2) -
        (q.2 - p.2) * (r.1 - p.1) := by
      rw [hscaleSq]
      field_simp [ne_of_gt (sqDist_pos_of_ne hab)]
    _ = turn p q r := by simp only [turn]

private theorem normalizeAlong_first_center
    {a b : Point ℝ} (hab : a ≠ b) :
    normalizeAlong a b a = (0, 0) := by
  have hscale := normalizeAlong_scale_pos hab
  apply Prod.ext <;> simp [normalizeAlong]

private theorem normalizeAlong_second_center
    {a b : Point ℝ} (hab : a ≠ b) :
    normalizeAlong a b b = (Real.sqrt (sqDist a b), 0) := by
  have hscale := normalizeAlong_scale_pos hab
  have hscaleSq := Real.sq_sqrt (sqDist_nonneg a b)
  apply Prod.ext
  · simp only [normalizeAlong]
    rw [div_eq_iff (ne_of_gt hscale)]
    simp only [sqDist] at hscaleSq ⊢
    nlinarith
  · simp only [normalizeAlong]
    rw [div_eq_zero_iff]
    exact Or.inl (by ring)

private theorem normalizeAlong_second_coordinate
    {a b : Point ℝ} (_hab : a ≠ b) (p : Point ℝ) :
    (normalizeAlong a b p).2 = turn a b p / Real.sqrt (sqDist a b) := by
  simp only [normalizeAlong, turn]

/-- Normalization preserves the executable degree in the top-three graph. -/
theorem normalizeAlong_vertexDegree
    {n : ℕ} {P : Fin n → Point ℝ} {a b : Point ℝ} (hab : a ≠ b)
    (d₁ d₂ d₃ : ℝ) (i : Fin n) :
    vertexDegree (fun j ↦ normalizeAlong a b (P j)) d₁ d₂ d₃ i =
      vertexDegree P d₁ d₂ d₃ i := by
  unfold vertexDegree
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  rw [normalizeAlong_sqDist hab]

/-- The three distinguished squared-distance classes survive normalization. -/
theorem normalizeAlong_top_three_classes
    {n : ℕ} {P : Fin n → Point ℝ} {a b : Point ℝ} (hab : a ≠ b)
    {d₁ d₂ d₃ : ℝ} (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃) :
    HasTopThreeDistanceClasses (fun j ↦ normalizeAlong a b (P j)) d₁ d₂ d₃ := by
  simpa only [HasTopThreeDistanceClasses, normalizeAlong_sqDist hab] using hClasses

private theorem top_three_values_nonnegative
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃) :
    0 ≤ d₁ ∧ 0 ≤ d₂ ∧ 0 ≤ d₃ := by
  rcases hClasses with ⟨_, _, ⟨e₁, _, he₁⟩, ⟨e₂, _, he₂⟩,
    ⟨e₃, _, he₃⟩, _⟩
  exact ⟨he₁ ▸ sqDist_nonneg (P e₁.1) (P e₁.2),
    he₂ ▸ sqDist_nonneg (P e₂.1) (P e₂.2),
    he₃ ▸ sqDist_nonneg (P e₃.1) (P e₃.2)⟩

private theorem top_three_third_value_pos
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hInjective : Function.Injective P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃) : 0 < d₃ := by
  rcases hClasses with ⟨_, _, _, _, ⟨e, heList, heq⟩, _⟩
  have hindices : e.1 ≠ e.2 := ne_of_lt (mem_unorderedPairList_iff.mp heList)
  have hpoints : P e.1 ≠ P e.2 := hInjective.ne hindices
  simpa only [heq] using sqDist_pos_of_ne hpoints

private theorem top_three_first_bound_local
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (i j : Fin n) : sqDist (P i) (P j) ≤ d₁ := by
  by_cases hij : i = j
  · subst j
    simpa [sqDist] using (top_three_values_nonnegative hClasses).1
  · exact (top_three_class_bounds_of_ne hClasses hij).1

private theorem euclideanDist_nonneg_local (a b : Point ℝ) :
    0 ≤ euclideanDist a b := by
  exact dist_nonneg

private theorem euclideanDist_comm_local (a b : Point ℝ) :
    euclideanDist a b = euclideanDist b a := by
  exact dist_comm _ _

private theorem euclideanDist_eq_sqrt_sqDist (a b : Point ℝ) :
    euclideanDist a b = Real.sqrt (sqDist a b) := by
  rw [← euclideanDist_sq]
  symm
  exact Real.sqrt_sq (euclideanDist_nonneg_local a b)

private theorem euclideanDist_eq_sqrt_of_sqDist_eq
    {a b : Point ℝ} {d : ℝ} (h : sqDist a b = d) :
    euclideanDist a b = Real.sqrt d := by
  rw [euclideanDist_eq_sqrt_sqDist, h]

private theorem euclideanDist_le_sqrt_of_sqDist_le
    {a b : Point ℝ} {d : ℝ} (h : sqDist a b ≤ d) :
    euclideanDist a b ≤ Real.sqrt d := by
  rw [euclideanDist_eq_sqrt_sqDist]
  exact Real.sqrt_le_sqrt h

private theorem sqDist_lt_of_euclideanDist_lt_sqrt
    {a b : Point ℝ} {d : ℝ} (hd : 0 ≤ d)
    (h : euclideanDist a b < Real.sqrt d) : sqDist a b < d := by
  have hsqrt := Real.sq_sqrt hd
  have hdist := euclideanDist_sq a b
  have hnonneg := euclideanDist_nonneg_local a b
  have hsqrtNonneg := Real.sqrt_nonneg d
  nlinarith

private theorem sqDist_eq_of_euclideanDist_eq_sqrt
    {a b : Point ℝ} {d : ℝ} (hd : 0 ≤ d)
    (h : euclideanDist a b = Real.sqrt d) : sqDist a b = d := by
  have hsqrt := Real.sq_sqrt hd
  have hdist := euclideanDist_sq a b
  rw [h] at hdist
  nlinarith

private theorem sqrt_lt_euclideanDist_of_sqDist_lt
    {a b : Point ℝ} {d : ℝ} (hd : 0 ≤ d)
    (h : d < sqDist a b) : Real.sqrt d < euclideanDist a b := by
  apply (Real.sqrt_lt hd (euclideanDist_nonneg_local a b)).2
  simpa only [euclideanDist_sq] using h

private theorem top_three_radius_bounds_of_ne
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hij : i ≠ j) :
    let r₁ := Real.sqrt d₁
    let r₂ := Real.sqrt d₂
    let r₃ := Real.sqrt d₃
    euclideanDist (P i) (P j) ≤ r₁ ∧
      (euclideanDist (P i) (P j) < r₁ →
        euclideanDist (P i) (P j) ≤ r₂) ∧
      (euclideanDist (P i) (P j) < r₂ →
        euclideanDist (P i) (P j) ≤ r₃) := by
  dsimp only
  obtain ⟨hd₁, hd₂, hd₃⟩ := top_three_values_nonnegative hClasses
  have hbounds := top_three_class_bounds_of_ne hClasses hij
  refine ⟨euclideanDist_le_sqrt_of_sqDist_le hbounds.1, ?_, ?_⟩
  · intro hlt
    exact euclideanDist_le_sqrt_of_sqDist_le
      (hbounds.2.1 (sqDist_lt_of_euclideanDist_lt_sqrt hd₁ hlt))
  · intro hlt
    exact euclideanDist_le_sqrt_of_sqDist_le
      (hbounds.2.2 (sqDist_lt_of_euclideanDist_lt_sqrt hd₂ hlt))

private theorem top_three_radius_strict_order
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃) :
    Real.sqrt d₃ < Real.sqrt d₂ ∧ Real.sqrt d₂ < Real.sqrt d₁ := by
  obtain ⟨_, hd₂, hd₃⟩ := top_three_values_nonnegative hClasses
  exact ⟨Real.sqrt_lt_sqrt hd₃ hClasses.1,
    Real.sqrt_lt_sqrt hd₂ hClasses.2.1⟩

private theorem sqDist_eq_d₁_of_sqrt_d₂_lt
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hij : i ≠ j)
    (h : Real.sqrt d₂ < euclideanDist (P i) (P j)) :
    sqDist (P i) (P j) = d₁ := by
  have hbounds := top_three_class_bounds_of_ne hClasses hij
  by_contra hne
  have hlt : sqDist (P i) (P j) < d₁ := lt_of_le_of_ne hbounds.1 hne
  have hle := hbounds.2.1 hlt
  have hdist := euclideanDist_le_sqrt_of_sqDist_le hle
  linarith

private theorem sqDist_eq_d₁_or_d₂_of_sqrt_d₃_lt
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hij : i ≠ j)
    (h : Real.sqrt d₃ < euclideanDist (P i) (P j)) :
    sqDist (P i) (P j) = d₁ ∨ sqDist (P i) (P j) = d₂ := by
  have hbounds := top_three_class_bounds_of_ne hClasses hij
  by_cases h₁ : sqDist (P i) (P j) = d₁
  · exact Or.inl h₁
  have hlt₁ : sqDist (P i) (P j) < d₁ := lt_of_le_of_ne hbounds.1 h₁
  have hle₂ := hbounds.2.1 hlt₁
  by_cases h₂ : sqDist (P i) (P j) = d₂
  · exact Or.inr h₂
  have hlt₂ : sqDist (P i) (P j) < d₂ := lt_of_le_of_ne hle₂ h₂
  have hle₃ := hbounds.2.2 hlt₂
  have hdist := euclideanDist_le_sqrt_of_sqDist_le hle₃
  linarith

private theorem euclideanDist_not_gt_sqrt_d₁
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hij : i ≠ j) :
    ¬Real.sqrt d₁ < euclideanDist (P i) (P j) := by
  have hbounds := top_three_radius_bounds_of_ne hClasses hij
  dsimp only at hbounds
  linarith

/-- Neighbor indices restricted to a raw boundary arc. -/
private noncomputable def arcNeighbors
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (v : Fin n) (arc : Finset (Fin n)) : Finset (Fin n) :=
  arc.filter fun j ↦ j ≠ v ∧
    (sqDist (P v) (P j) = d₁ ∨ sqDist (P v) (P j) = d₂ ∨
      sqDist (P v) (P j) = d₃)

private theorem vertexDegree_le_partition_four
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {v w s : Fin n} {leftArc rightArc : Finset (Fin n)}
    (hcover : ∀ j, j ≠ v →
      j ∈ leftArc ∨ j = w ∨ j = s ∨ j ∈ rightArc) :
    vertexDegree P d₁ d₂ d₃ v ≤
      (arcNeighbors P d₁ d₂ d₃ v leftArc).card +
        (arcNeighbors P d₁ d₂ d₃ v rightArc).card + 2 := by
  classical
  let N := (Finset.univ.erase v).filter fun j ↦
    sqDist (P v) (P j) = d₁ ∨ sqDist (P v) (P j) = d₂ ∨
      sqDist (P v) (P j) = d₃
  let C : Finset (Fin n) := arcNeighbors P d₁ d₂ d₃ v leftArc ∪
    arcNeighbors P d₁ d₂ d₃ v rightArc ∪ {w, s}
  have hsubset : N ⊆ C := by
    intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjne := (Finset.mem_erase.mp hjData.1).1
    rcases hcover j hjne with hjLeft | rfl | rfl | hjRight
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hjLeft, hjne, hjData.2⟩))))
    · simp [C]
    · simp [C]
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hjRight, hjne, hjData.2⟩))))
  change N.card ≤ _
  calc
    N.card ≤ C.card := Finset.card_le_card hsubset
    _ ≤ (arcNeighbors P d₁ d₂ d₃ v leftArc).card +
          (arcNeighbors P d₁ d₂ d₃ v rightArc).card +
            ({w, s} : Finset (Fin n)).card := by
      dsimp [C]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (arcNeighbors P d₁ d₂ d₃ v leftArc).card +
          (arcNeighbors P d₁ d₂ d₃ v rightArc).card + 2 := by
      exact Nat.add_le_add_left Finset.card_le_two _

private theorem vertexDegree_le_partition_without_w
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {v w s : Fin n} {leftArc rightArc : Finset (Fin n)}
    (hcover : ∀ j, j ≠ v →
      j ∈ leftArc ∨ j = w ∨ j = s ∨ j ∈ rightArc)
    (hw : ¬(sqDist (P v) (P w) = d₁ ∨
      sqDist (P v) (P w) = d₂ ∨ sqDist (P v) (P w) = d₃)) :
    vertexDegree P d₁ d₂ d₃ v ≤
      (arcNeighbors P d₁ d₂ d₃ v leftArc).card +
        (arcNeighbors P d₁ d₂ d₃ v rightArc).card + 1 := by
  classical
  let N := (Finset.univ.erase v).filter fun j ↦
    sqDist (P v) (P j) = d₁ ∨ sqDist (P v) (P j) = d₂ ∨
      sqDist (P v) (P j) = d₃
  let C : Finset (Fin n) := arcNeighbors P d₁ d₂ d₃ v leftArc ∪
    arcNeighbors P d₁ d₂ d₃ v rightArc ∪ {s}
  have hsubset : N ⊆ C := by
    intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjne := (Finset.mem_erase.mp hjData.1).1
    rcases hcover j hjne with hjLeft | hjw | hjs | hjRight
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hjLeft, hjne, hjData.2⟩))))
    · subst j
      exact (hw hjData.2).elim
    · subst j
      simp [C]
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hjRight, hjne, hjData.2⟩))))
  change N.card ≤ _
  calc
    N.card ≤ C.card := Finset.card_le_card hsubset
    _ ≤ (arcNeighbors P d₁ d₂ d₃ v leftArc).card +
          (arcNeighbors P d₁ d₂ d₃ v rightArc).card +
            ({s} : Finset (Fin n)).card := by
      dsimp [C]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (arcNeighbors P d₁ d₂ d₃ v leftArc).card +
          (arcNeighbors P d₁ d₂ d₃ v rightArc).card + 1 := by
      simp

private noncomputable def circleSlot
    {n : ℕ} (P : Fin n → Point ℝ) (arc : Finset (Fin n))
    (firstCenter secondCenter : Fin n) (firstRadius secondRadius : ℝ) :
    Finset (Fin n) :=
  arc.filter fun j ↦
    sqDist (P firstCenter) (P j) = firstRadius ∧
      sqDist (P secondCenter) (P j) = secondRadius

private theorem circleSlot_card_le_one
    {n : ℕ} {P : Fin n → Point ℝ} (hInjective : Function.Injective P)
    {arc : Finset (Fin n)} {firstCenter secondCenter : Fin n}
    (hcenters : firstCenter ≠ secondCenter)
    (hside : ∀ j ∈ arc,
      InLeftOpenHalfPlane (P firstCenter) (P secondCenter) (P j))
    {firstRadius secondRadius : ℝ} :
    (circleSlot P arc firstCenter secondCenter firstRadius secondRadius).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  have hpData := Finset.mem_filter.mp hp
  have hqData := Finset.mem_filter.mp hq
  apply hInjective
  apply same_half_plane_two_circle_unique (hInjective.ne hcenters)
  · exact hpData.2.1.trans hqData.2.1.symm
  · exact hpData.2.2.trans hqData.2.2.symm
  · exact hside p hpData.1
  · exact hside q hqData.1

private theorem circleSlot_card_le_one_reverse
    {n : ℕ} {P : Fin n → Point ℝ} (hInjective : Function.Injective P)
    {arc : Finset (Fin n)} {firstCenter secondCenter : Fin n}
    (hcenters : firstCenter ≠ secondCenter)
    (hside : ∀ j ∈ arc,
      InLeftOpenHalfPlane (P secondCenter) (P firstCenter) (P j))
    {firstRadius secondRadius : ℝ} :
    (circleSlot P arc firstCenter secondCenter firstRadius secondRadius).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  have hpData := Finset.mem_filter.mp hp
  have hqData := Finset.mem_filter.mp hq
  apply hInjective
  apply same_half_plane_two_circle_unique (hInjective.ne hcenters.symm)
  · exact hpData.2.2.trans hqData.2.2.symm
  · exact hpData.2.1.trans hqData.2.1.symm
  · exact hside p hpData.1
  · exact hside q hqData.1

private theorem circleSlot_card_le_one_either
    {n : ℕ} {P : Fin n → Point ℝ} (hInjective : Function.Injective P)
    {arc : Finset (Fin n)} {firstCenter secondCenter : Fin n}
    (hcenters : firstCenter ≠ secondCenter)
    (hside :
      (∀ j ∈ arc, InLeftOpenHalfPlane (P firstCenter) (P secondCenter) (P j)) ∨
      (∀ j ∈ arc, InLeftOpenHalfPlane (P secondCenter) (P firstCenter) (P j)))
    {firstRadius secondRadius : ℝ} :
    (circleSlot P arc firstCenter secondCenter firstRadius secondRadius).card ≤ 1 := by
  rcases hside with hforward | hreverse
  · exact circleSlot_card_le_one hInjective hcenters hforward
  · exact circleSlot_card_le_one_reverse hInjective hcenters hreverse

private theorem arcNeighbors_card_le_of_three_slots
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {v firstCenter secondCenter : Fin n} {arc : Finset (Fin n)}
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (hcover : arcNeighbors P d₁ d₂ d₃ v arc ⊆
      circleSlot P arc firstCenter secondCenter a₁ b₁ ∪
        circleSlot P arc firstCenter secondCenter a₂ b₂ ∪
          circleSlot P arc firstCenter secondCenter a₃ b₃)
    (h₁ : (circleSlot P arc firstCenter secondCenter a₁ b₁).card ≤ 1)
    (h₂ : (circleSlot P arc firstCenter secondCenter a₂ b₂).card ≤ 1)
    (h₃ : (circleSlot P arc firstCenter secondCenter a₃ b₃).card ≤ 1) :
    (arcNeighbors P d₁ d₂ d₃ v arc).card ≤ 3 := by
  calc
    (arcNeighbors P d₁ d₂ d₃ v arc).card ≤
        (circleSlot P arc firstCenter secondCenter a₁ b₁ ∪
          circleSlot P arc firstCenter secondCenter a₂ b₂ ∪
            circleSlot P arc firstCenter secondCenter a₃ b₃).card :=
      Finset.card_le_card hcover
    _ ≤ (circleSlot P arc firstCenter secondCenter a₁ b₁).card +
          (circleSlot P arc firstCenter secondCenter a₂ b₂).card +
            (circleSlot P arc firstCenter secondCenter a₃ b₃).card := by
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ 3 := by omega

private theorem arcNeighbors_card_le_of_two_slots
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {v firstCenter secondCenter : Fin n} {arc : Finset (Fin n)}
    {a₁ b₁ a₂ b₂ : ℝ}
    (hcover : arcNeighbors P d₁ d₂ d₃ v arc ⊆
      circleSlot P arc firstCenter secondCenter a₁ b₁ ∪
        circleSlot P arc firstCenter secondCenter a₂ b₂)
    (h₁ : (circleSlot P arc firstCenter secondCenter a₁ b₁).card ≤ 1)
    (h₂ : (circleSlot P arc firstCenter secondCenter a₂ b₂).card ≤ 1) :
    (arcNeighbors P d₁ d₂ d₃ v arc).card ≤ 2 := by
  calc
    (arcNeighbors P d₁ d₂ d₃ v arc).card ≤
        (circleSlot P arc firstCenter secondCenter a₁ b₁ ∪
          circleSlot P arc firstCenter secondCenter a₂ b₂).card :=
      Finset.card_le_card hcover
    _ ≤ (circleSlot P arc firstCenter secondCenter a₁ b₁).card +
          (circleSlot P arc firstCenter secondCenter a₂ b₂).card :=
      Finset.card_union_le _ _
    _ ≤ 2 := by omega

private theorem arcNeighbors_card_le_of_one_slot
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {v firstCenter secondCenter : Fin n} {arc : Finset (Fin n)}
    {a b : ℝ}
    (hcover : arcNeighbors P d₁ d₂ d₃ v arc ⊆
      circleSlot P arc firstCenter secondCenter a b)
    (hslot : (circleSlot P arc firstCenter secondCenter a b).card ≤ 1) :
    (arcNeighbors P d₁ d₂ d₃ v arc).card ≤ 1 :=
  (Finset.card_le_card hcover).trans hslot

/-- Raw row-1 terminal `B:3→2` geometry from draft Section 6.4. -/
structure Row1B32WordRealization
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  pointsInjective : Function.Injective P
  classes : HasTopThreeDistanceClasses P d₁ d₂ d₃
  /-- First diameter center. -/
  x : Fin n
  /-- Vertex whose top-three degree is bounded. -/
  vertex : Fin n
  /-- Second diameter center. -/
  t : Fin n
  /-- Penultimate rung point. -/
  w : Fin n
  /-- Shared terminal tip. -/
  s : Fin n
  x_ne_vertex : x ≠ vertex
  t_ne_vertex : t ≠ vertex
  x_ne_t : x ≠ t
  x_ne_w : x ≠ w
  x_ne_s : x ≠ s
  t_ne_w : t ≠ w
  t_ne_s : t ≠ s
  w_ne_s : w ≠ s
  w_ne_vertex : w ≠ vertex
  s_ne_vertex : s ≠ vertex
  /-- Boundary vertices on the first-center side. -/
  leftArc : Finset (Fin n)
  /-- Boundary vertices on the second-center side. -/
  rightArc : Finset (Fin n)
  arcPartition : ∀ j, j ≠ vertex →
    j ∈ leftArc ∨ j = w ∨ j = s ∨ j ∈ rightArc
  leftHalfPlane : ∀ j ∈ leftArc,
    InLeftOpenHalfPlane (P x) (P vertex) (P j)
  left_x_ne : ∀ j ∈ leftArc, x ≠ j
  /-- The return arc lies to the left of the reversed chord `vertex ⟶ t`. -/
  rightHalfPlane : ∀ j ∈ rightArc,
    InLeftOpenHalfPlane (P vertex) (P t) (P j)
  right_t_ne : ∀ j ∈ rightArc, t ≠ j
  leftQuad : ∀ j ∈ leftArc,
    StrictConvexQuad (P vertex) (P j) (P s) (P x)
  rightQuad : ∀ j ∈ rightArc,
    StrictConvexQuad (P t) (P s) (P j) (P vertex)
  centralLeftQuad : StrictConvexQuad (P vertex) (P w) (P s) (P x)
  centralRightQuad : StrictConvexQuad (P t) (P w) (P s) (P vertex)
  terminalQuad : StrictConvexQuad (P t) (P w) (P s) (P x)
  shortLeftQuad : ∀ j ∈ leftArc,
    StrictConvexQuad (P vertex) (P j) (P w) (P x)
  xw_le : sqDist (P x) (P w) ≤ d₂
  xs : sqDist (P x) (P s) = d₂
  tw : sqDist (P t) (P w) = d₂
  ts : sqDist (P t) (P s) = d₁

private theorem row1_B32_left_card_le_three
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row1B32WordRealization P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.leftArc).card ≤ 3 := by
  apply arcNeighbors_card_le_of_three_slots
    (firstCenter := G.x) (secondCenter := G.vertex)
    (a₁ := d₁) (b₁ := d₂) (a₂ := d₁) (b₂ := d₃)
    (a₃ := d₂) (b₃ := d₃)
  · intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjArc := hjData.1
    have hED := edge_diagonal_inequality (G.leftQuad j hjArc)
    rw [euclideanDist_comm_local (P G.s) (P G.x),
      euclideanDist_eq_sqrt_of_sqDist_eq G.xs,
      euclideanDist_eq_sqrt_of_sqDist_eq hVs,
      euclideanDist_comm_local (P j) (P G.x)] at hED
    rcases hjData.2.2 with hVj | hVj | hVj
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₁ < euclideanDist (P G.x) (P j) := by linarith
      exact (euclideanDist_not_gt_sqrt_d₁ G.classes
        (G.left_x_ne j hjArc) hfar).elim
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₂ < euclideanDist (P G.x) (P j) := by linarith
      have hxj := sqDist_eq_d₁_of_sqrt_d₂_lt G.classes
        (G.left_x_ne j hjArc) hfar
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hjArc, hxj, hVj⟩))))
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₃ < euclideanDist (P G.x) (P j) := by linarith
      rcases sqDist_eq_d₁_or_d₂_of_sqrt_d₃_lt G.classes
          (G.left_x_ne j hjArc) hfar with hxj | hxj
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hjArc, hxj, hVj⟩))))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hjArc, hxj, hVj⟩))
  · exact circleSlot_card_le_one G.pointsInjective G.x_ne_vertex G.leftHalfPlane
  · exact circleSlot_card_le_one G.pointsInjective G.x_ne_vertex G.leftHalfPlane
  · exact circleSlot_card_le_one G.pointsInjective G.x_ne_vertex G.leftHalfPlane

private theorem row1_B32_right_card_le_two
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row1B32WordRealization P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.rightArc).card ≤ 2 := by
  apply arcNeighbors_card_le_of_two_slots
    (firstCenter := G.t) (secondCenter := G.vertex)
    (a₁ := d₁) (b₁ := d₃) (a₂ := d₂) (b₂ := d₃)
  · intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjArc := hjData.1
    have hED := edge_diagonal_inequality (G.rightQuad j hjArc)
    rw [euclideanDist_eq_sqrt_of_sqDist_eq G.ts,
      euclideanDist_comm_local (P j) (P G.vertex),
      euclideanDist_comm_local (P G.s) (P G.vertex),
      euclideanDist_eq_sqrt_of_sqDist_eq hVs] at hED
    rcases hjData.2.2 with hVj | hVj | hVj
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hbound := euclideanDist_not_gt_sqrt_d₁ G.classes (G.right_t_ne j hjArc)
      have horder := (top_three_radius_strict_order G.classes).2
      exfalso
      exact hbound (by linarith)
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₁ < euclideanDist (P G.t) (P j) := by linarith
      exact (euclideanDist_not_gt_sqrt_d₁ G.classes
        (G.right_t_ne j hjArc) hfar).elim
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have horder := (top_three_radius_strict_order G.classes).2
      have htjLower : Real.sqrt d₃ < euclideanDist (P G.t) (P j) := by
        linarith
      rcases sqDist_eq_d₁_or_d₂_of_sqrt_d₃_lt G.classes
          (G.right_t_ne j hjArc) htjLower with htj | htj
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨hjArc, htj, hVj⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hjArc, htj, hVj⟩))
  · exact circleSlot_card_le_one_reverse G.pointsInjective G.t_ne_vertex G.rightHalfPlane
  · exact circleSlot_card_le_one_reverse G.pointsInjective G.t_ne_vertex G.rightHalfPlane

private theorem row1_B32_low_left_card_le_two
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row1B32WordRealization P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) ≤ d₃) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.leftArc).card ≤ 2 := by
  apply arcNeighbors_card_le_of_two_slots
    (firstCenter := G.x) (secondCenter := G.vertex)
    (a₁ := d₁) (b₁ := d₂) (a₂ := d₁) (b₂ := d₃)
  · intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjArc := hjData.1
    have hVsDist := euclideanDist_le_sqrt_of_sqDist_le hVs
    have hED := edge_diagonal_inequality (G.leftQuad j hjArc)
    rw [euclideanDist_comm_local (P G.s) (P G.x),
      euclideanDist_eq_sqrt_of_sqDist_eq G.xs,
      euclideanDist_comm_local (P j) (P G.x)] at hED
    rcases hjData.2.2 with hVj | hVj | hVj
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hxUpper := top_three_radius_bounds_of_ne G.classes (G.left_x_ne j hjArc)
      dsimp only at hxUpper
      have horder := top_three_radius_strict_order G.classes
      exfalso
      linarith
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have horder := top_three_radius_strict_order G.classes
      have hfar : Real.sqrt d₂ < euclideanDist (P G.x) (P j) := by linarith
      have hxj := sqDist_eq_d₁_of_sqrt_d₂_lt G.classes
        (G.left_x_ne j hjArc) hfar
      exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hjArc, hxj, hVj⟩))
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₂ < euclideanDist (P G.x) (P j) := by linarith
      have hxj := sqDist_eq_d₁_of_sqrt_d₂_lt G.classes
        (G.left_x_ne j hjArc) hfar
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hjArc, hxj, hVj⟩))
  · exact circleSlot_card_le_one G.pointsInjective G.x_ne_vertex G.leftHalfPlane
  · exact circleSlot_card_le_one G.pointsInjective G.x_ne_vertex G.leftHalfPlane

private theorem row1_B32_low_right_card_eq_zero
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row1B32WordRealization P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) ≤ d₃) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.rightArc).card = 0 := by
  by_contra hnot
  have hpos : 0 < (arcNeighbors P d₁ d₂ d₃ G.vertex G.rightArc).card := by
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  have hjData := Finset.mem_filter.mp hj
  have hjArc := hjData.1
  have hVsDist := euclideanDist_le_sqrt_of_sqDist_le hVs
  have htjBounds := top_three_radius_bounds_of_ne G.classes (G.right_t_ne j hjArc)
  dsimp only at htjBounds
  have hED := edge_diagonal_inequality (G.rightQuad j hjArc)
  rw [euclideanDist_eq_sqrt_of_sqDist_eq G.ts,
    euclideanDist_comm_local (P j) (P G.vertex),
    euclideanDist_comm_local (P G.s) (P G.vertex)] at hED
  have horder := top_three_radius_strict_order G.classes
  rcases hjData.2.2 with hVj | hVj | hVj <;>
    rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED <;> linarith

private theorem row1_B32_long_right_card_le_one
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row1B32WordRealization P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂)
    (hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.rightArc).card ≤ 1 := by
  apply arcNeighbors_card_le_of_one_slot
    (firstCenter := G.t) (secondCenter := G.vertex) (a := d₁) (b := d₃)
  · intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjArc := hjData.1
    have hED := edge_diagonal_inequality (G.rightQuad j hjArc)
    rw [euclideanDist_eq_sqrt_of_sqDist_eq G.ts,
      euclideanDist_comm_local (P j) (P G.vertex),
      euclideanDist_comm_local (P G.s) (P G.vertex),
      euclideanDist_eq_sqrt_of_sqDist_eq hVs] at hED
    rcases hjData.2.2 with hVj | hVj | hVj
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have htjBounds := top_three_radius_bounds_of_ne G.classes (G.right_t_ne j hjArc)
      dsimp only at htjBounds
      have horder := (top_three_radius_strict_order G.classes).2
      exfalso
      linarith
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₁ < euclideanDist (P G.t) (P j) := by linarith
      exact (euclideanDist_not_gt_sqrt_d₁ G.classes
        (G.right_t_ne j hjArc) hfar).elim
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have htjBounds := top_three_radius_bounds_of_ne G.classes (G.right_t_ne j hjArc)
      dsimp only at htjBounds
      have htj := terminal_long_right_d3_partner_forces_outer_d1
        ⟨htjBounds.1, htjBounds.2.1⟩ hlong hED
      have htjSq : sqDist (P G.t) (P j) = d₁ := by
        rw [euclideanDist_eq_sqrt_sqDist] at htj
        have hd₁ := (top_three_values_nonnegative G.classes).1
        have hsq := congrArg (fun z : ℝ ↦ z ^ 2) htj
        rw [Real.sq_sqrt (sqDist_nonneg (P G.t) (P j)),
          Real.sq_sqrt hd₁] at hsq
        exact hsq
      exact Finset.mem_filter.mpr ⟨hjArc, htjSq, hVj⟩
  · exact circleSlot_card_le_one_reverse G.pointsInjective G.t_ne_vertex G.rightHalfPlane

private theorem row1_B32_short_left_card_le_two
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row1B32WordRealization P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂)
    (hxw : sqDist (P G.x) (P G.w) = d₂)
    (hVw : sqDist (P G.vertex) (P G.w) = d₃) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.leftArc).card ≤ 2 := by
  apply arcNeighbors_card_le_of_two_slots
    (firstCenter := G.x) (secondCenter := G.vertex)
    (a₁ := d₁) (b₁ := d₂) (a₂ := d₁) (b₂ := d₃)
  · intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjArc := hjData.1
    rcases hjData.2.2 with hVj | hVj | hVj
    · have hED := edge_diagonal_inequality (G.leftQuad j hjArc)
      rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj,
        euclideanDist_comm_local (P G.s) (P G.x),
        euclideanDist_eq_sqrt_of_sqDist_eq G.xs,
        euclideanDist_eq_sqrt_of_sqDist_eq hVs,
        euclideanDist_comm_local (P j) (P G.x)] at hED
      have hfar : Real.sqrt d₁ < euclideanDist (P G.x) (P j) := by linarith
      exact (euclideanDist_not_gt_sqrt_d₁ G.classes
        (G.left_x_ne j hjArc) hfar).elim
    · have hED := edge_diagonal_inequality (G.leftQuad j hjArc)
      rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj,
        euclideanDist_comm_local (P G.s) (P G.x),
        euclideanDist_eq_sqrt_of_sqDist_eq G.xs,
        euclideanDist_eq_sqrt_of_sqDist_eq hVs,
        euclideanDist_comm_local (P j) (P G.x)] at hED
      have hfar : Real.sqrt d₂ < euclideanDist (P G.x) (P j) := by linarith
      have hxj := sqDist_eq_d₁_of_sqrt_d₂_lt G.classes
        (G.left_x_ne j hjArc) hfar
      exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hjArc, hxj, hVj⟩))
    · have hED := edge_diagonal_inequality (G.shortLeftQuad j hjArc)
      rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj,
        euclideanDist_comm_local (P G.w) (P G.x),
        euclideanDist_eq_sqrt_of_sqDist_eq hxw,
        euclideanDist_eq_sqrt_of_sqDist_eq hVw,
        euclideanDist_comm_local (P j) (P G.x)] at hED
      have hfar : Real.sqrt d₂ < euclideanDist (P G.x) (P j) := by linarith
      have hxj := sqDist_eq_d₁_of_sqrt_d₂_lt G.classes
        (G.left_x_ne j hjArc) hfar
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hjArc, hxj, hVj⟩))
  · exact circleSlot_card_le_one G.pointsInjective G.x_ne_vertex G.leftHalfPlane
  · exact circleSlot_card_le_one G.pointsInjective G.x_ne_vertex G.leftHalfPlane

private theorem row1_B32_central_distances
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row1B32WordRealization P d₁ d₂ d₃) :
    euclideanDist (P G.vertex) (P G.s) ≤ Real.sqrt d₂ ∧
      euclideanDist (P G.vertex) (P G.w) <
        euclideanDist (P G.vertex) (P G.s) := by
  have hq := euclideanDist_le_sqrt_of_sqDist_le G.xw_le
  have hVsBounds := top_three_radius_bounds_of_ne G.classes G.s_ne_vertex.symm
  have hVwBounds := top_three_radius_bounds_of_ne G.classes G.w_ne_vertex.symm
  dsimp only at hVsBounds hVwBounds
  have hleftED := edge_diagonal_inequality G.centralLeftQuad
  rw [euclideanDist_comm_local (P G.s) (P G.x),
    euclideanDist_eq_sqrt_of_sqDist_eq G.xs,
    euclideanDist_comm_local (P G.w) (P G.x)] at hleftED
  have hrightED := edge_diagonal_inequality G.centralRightQuad
  rw [euclideanDist_eq_sqrt_of_sqDist_eq G.tw,
    euclideanDist_comm_local (P G.s) (P G.vertex),
    euclideanDist_eq_sqrt_of_sqDist_eq G.ts,
    euclideanDist_comm_local (P G.w) (P G.vertex)] at hrightED
  apply terminal_central_distances hq
    ⟨hVsBounds.1, hVsBounds.2.1⟩ ⟨hVwBounds.1, hVwBounds.2.1⟩
  · linarith [hleftED]
  · linarith [hrightED]

/-- The row-1 terminal `B:3→2` word forces its displayed lower vertex to
have degree at most six, derived only from its raw geometry. -/
theorem row1_B32_realization_degree_le_six
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row1B32WordRealization P d₁ d₂ d₃) :
    vertexDegree P d₁ d₂ d₃ G.vertex ≤ 6 := by
  obtain ⟨hVsLe, hVwLt⟩ := row1_B32_central_distances G
  have hVsBounds := top_three_class_bounds_of_ne G.classes G.s_ne_vertex.symm
  rcases top_three_value_split hVsBounds with hVsD₁ | hVsD₂ | hVsLow
  · have hVsRadius := euclideanDist_eq_sqrt_of_sqDist_eq hVsD₁
    have horder := (top_three_radius_strict_order G.classes).2
    exfalso
    linarith
  · have hleft := row1_B32_left_card_le_three G hVsD₂
    have hright := row1_B32_right_card_le_two G hVsD₂
    by_cases hlong :
        2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃
    · have hrightLong := row1_B32_long_right_card_le_one G hVsD₂ hlong
      have hpartition := vertexDegree_le_partition_four
        (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) G.arcPartition
      omega
    · have hshort : Real.sqrt d₁ + Real.sqrt d₃ < 2 * Real.sqrt d₂ :=
        lt_of_not_ge hlong
      have ⟨hd₁, hd₂, hd₃⟩ := top_three_values_nonnegative G.classes
      let q := euclideanDist (P G.x) (P G.w)
      have hq : q ≤ Real.sqrt d₂ := euclideanDist_le_sqrt_of_sqDist_le G.xw_le
      have hqClass : q = Real.sqrt d₂ ∨ q ≤ Real.sqrt d₃ := by
        rcases lt_or_eq_of_le G.xw_le with hxwLt | hxwEq
        · right
          have hxwBounds := top_three_class_bounds_of_ne G.classes G.x_ne_w
          exact euclideanDist_le_sqrt_of_sqDist_le (hxwBounds.2.2 hxwLt)
        · left
          exact euclideanDist_eq_sqrt_of_sqDist_eq hxwEq
      have hterminalED := edge_diagonal_inequality G.terminalQuad
      rw [euclideanDist_eq_sqrt_of_sqDist_eq G.tw,
        euclideanDist_comm_local (P G.s) (P G.x),
        euclideanDist_eq_sqrt_of_sqDist_eq G.xs,
        euclideanDist_eq_sqrt_of_sqDist_eq G.ts,
        euclideanDist_comm_local (P G.w) (P G.x)] at hterminalED
      have hqEq := terminal_short_regime_forces_q_eq_d2
        hq hqClass hshort (by dsimp [q]; linarith [hterminalED])
      have hxwD₂ : sqDist (P G.x) (P G.w) = d₂ :=
        sqDist_eq_of_euclideanDist_eq_sqrt hd₂ hqEq
      have hVsRadius := euclideanDist_eq_sqrt_of_sqDist_eq hVsD₂
      have hVwLtRadius : euclideanDist (P G.vertex) (P G.w) < Real.sqrt d₂ := by
        linarith
      have hVwLtSq : sqDist (P G.vertex) (P G.w) < d₂ :=
        sqDist_lt_of_euclideanDist_lt_sqrt hd₂ hVwLtRadius
      have hVwBounds := top_three_class_bounds_of_ne G.classes G.w_ne_vertex.symm
      have hVwLeD₃ := hVwBounds.2.2 hVwLtSq
      by_cases hVwD₃ : sqDist (P G.vertex) (P G.w) = d₃
      · have hleftShort := row1_B32_short_left_card_le_two G hVsD₂ hxwD₂ hVwD₃
        have hpartition := vertexDegree_le_partition_four
          (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) G.arcPartition
        omega
      · have hVwLtD₃ : sqDist (P G.vertex) (P G.w) < d₃ :=
          lt_of_le_of_ne hVwLeD₃ hVwD₃
        have hwNot : ¬(sqDist (P G.vertex) (P G.w) = d₁ ∨
            sqDist (P G.vertex) (P G.w) = d₂ ∨
              sqDist (P G.vertex) (P G.w) = d₃) := by
          intro hw
          rcases hw with hw | hw | hw <;> linarith [G.classes.1, G.classes.2.1]
        have hpartition := vertexDegree_le_partition_without_w
          (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) G.arcPartition hwNot
        omega
  · have hleft := row1_B32_low_left_card_le_two G hVsLow
    have hright := row1_B32_low_right_card_eq_zero G hVsLow
    have hpartition := vertexDegree_le_partition_four
      (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) G.arcPartition
    omega

private theorem vertexDegree_le_partition_three
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {v s : Fin n} {leftArc rightArc : Finset (Fin n)}
    (hcover : ∀ j, j ≠ v → j ∈ leftArc ∨ j = s ∨ j ∈ rightArc) :
    vertexDegree P d₁ d₂ d₃ v ≤
      (arcNeighbors P d₁ d₂ d₃ v leftArc).card +
        (arcNeighbors P d₁ d₂ d₃ v rightArc).card + 1 := by
  classical
  let N := (Finset.univ.erase v).filter fun j ↦
    sqDist (P v) (P j) = d₁ ∨ sqDist (P v) (P j) = d₂ ∨
      sqDist (P v) (P j) = d₃
  let C : Finset (Fin n) := arcNeighbors P d₁ d₂ d₃ v leftArc ∪
    arcNeighbors P d₁ d₂ d₃ v rightArc ∪ {s}
  have hsubset : N ⊆ C := by
    intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjne := (Finset.mem_erase.mp hjData.1).1
    rcases hcover j hjne with hjLeft | rfl | hjRight
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hjLeft, hjne, hjData.2⟩))))
    · simp [C]
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hjRight, hjne, hjData.2⟩))))
  change N.card ≤ _
  calc
    N.card ≤ C.card := Finset.card_le_card hsubset
    _ ≤ (arcNeighbors P d₁ d₂ d₃ v leftArc).card +
          (arcNeighbors P d₁ d₂ d₃ v rightArc).card +
            ({s} : Finset (Fin n)).card := by
      dsimp [C]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (arcNeighbors P d₁ d₂ d₃ v leftArc).card +
          (arcNeighbors P d₁ d₂ d₃ v rightArc).card + 1 := by simp

/-- Equal-radius shared-tip geometry normalizes to the diameter-lens kernel.
The only positional inputs are the two signed sides of the center line. -/
private theorem shared_tip_unique_farthest
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hInjective : Function.Injective P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {e t s vertex : Fin n}
    (he_ne_t : e ≠ t)
    (hes : sqDist (P e) (P s) = d₁)
    (hts : sqDist (P t) (P s) = d₁)
    (htipAbove : 0 < turn (P e) (P t) (P s))
    (hvertexBelow : turn (P e) (P t) (P vertex) < 0) :
    ∀ j, j ≠ s →
      sqDist (P vertex) (P j) < sqDist (P vertex) (P s) := by
  let N : Fin n → Point ℝ := fun j ↦ normalizeAlong (P e) (P t) (P j)
  have hcenters : P e ≠ P t := hInjective.ne he_ne_t
  let scale := Real.sqrt (sqDist (P e) (P t))
  have hscale : 0 < scale := normalizeAlong_scale_pos hcenters
  let c := scale / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hscaleEq : scale = 2 * c := by dsimp [c]; ring
  have he : N e = (0, 0) := by
    simpa only [N] using normalizeAlong_first_center hcenters
  have htScale : N t = (scale, 0) := by
    simpa only [N, scale] using normalizeAlong_second_center hcenters
  have ht : N t = (2 * c, 0) := by simpa only [hscaleEq] using htScale
  have hesN : sqDist (N e) (N s) = d₁ := by
    simpa only [N, normalizeAlong_sqDist hcenters] using hes
  have htsN : sqDist (N t) (N s) = d₁ := by
    simpa only [N, normalizeAlong_sqDist hcenters] using hts
  let H := (N s).2
  have hsFirst : (N s).1 = c := by
    rw [he] at hesN
    rw [ht] at htsN
    simp only [sqDist] at hesN htsN
    nlinarith
  have hs : N s = (c, H) := Prod.ext hsFirst rfl
  have hH : 0 < H := by
    have hsecond := normalizeAlong_second_coordinate hcenters (P s)
    change (N s).2 = _ at hsecond
    change 0 < (N s).2
    rw [hsecond]
    exact div_pos htipAbove hscale
  let X := (N vertex).1
  let Y := (N vertex).2
  have hv : N vertex = (X, Y) := rfl
  have hY : Y < 0 := by
    have hsecond := normalizeAlong_second_coordinate hcenters (P vertex)
    change (N vertex).2 = _ at hsecond
    dsimp [Y]
    rw [hsecond]
    exact div_neg_of_neg_of_pos hvertexBelow hscale
  have hd₁Radius : d₁ = c ^ 2 + H ^ 2 := by
    rw [he, hs] at hesN
    simpa [sqDist] using hesN.symm
  have hVertexTipRaw := top_three_first_bound_local hClasses vertex s
  have hVertexTipN : sqDist (N vertex) (N s) ≤ d₁ := by
    simpa only [N, normalizeAlong_sqDist hcenters] using hVertexTipRaw
  have hVertexTip : sqDist (X, Y) (c, H) ≤ c ^ 2 + H ^ 2 := by
    rw [← hv, ← hs, ← hd₁Radius]
    exact hVertexTipN
  intro j hjs
  have hleftRaw := top_three_first_bound_local hClasses e j
  have hrightRaw := top_three_first_bound_local hClasses t j
  have hleftN : sqDist (N e) (N j) ≤ d₁ := by
    simpa only [N, normalizeAlong_sqDist hcenters] using hleftRaw
  have hrightN : sqDist (N t) (N j) ≤ d₁ := by
    simpa only [N, normalizeAlong_sqDist hcenters] using hrightRaw
  have hjLens : InSharedDiameterLens c H (N j) := by
    constructor
    · rw [← he, ← hd₁Radius]
      exact hleftN
    · rw [← ht, ← hd₁Radius]
      exact hrightN
  have hpoints : P j ≠ P s := hInjective.ne hjs
  have hnormalized : N j ≠ N s :=
    (normalizeAlong_injective hcenters).ne hpoints
  have hneTip : N j ≠ (c, H) := by
    rw [← hs]
    exact hnormalized
  have hbound := diameter_lens_unique_farthest hc hH hY
    hVertexTip hjLens hneTip
  rw [← hv, ← hs] at hbound
  simpa only [N, normalizeAlong_sqDist hcenters] using hbound

/-- Raw shared-tip geometry with one surviving penultimate rung. -/
structure OnePenultimateWordGeometry
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  pointsInjective : Function.Injective P
  classes : HasTopThreeDistanceClasses P d₁ d₂ d₃
  /-- First diameter center. -/
  e : Fin n
  /-- Vertex whose top-three degree is bounded. -/
  vertex : Fin n
  /-- Second diameter center. -/
  t : Fin n
  /-- Surviving penultimate rung point. -/
  p : Fin n
  /-- Shared tip. -/
  s : Fin n
  e_ne_vertex : e ≠ vertex
  t_ne_vertex : t ≠ vertex
  p_ne_vertex : p ≠ vertex
  s_ne_vertex : s ≠ vertex
  e_ne_t : e ≠ t
  e_ne_s : e ≠ s
  t_ne_p : t ≠ p
  t_ne_s : t ≠ s
  p_ne_s : p ≠ s
  /-- Boundary vertices on the first-center side. -/
  leftArc : Finset (Fin n)
  /-- Boundary vertices on the second-center side. -/
  rightArc : Finset (Fin n)
  arcPartition : ∀ j, j ≠ vertex →
    j ∈ leftArc ∨ j = s ∨ j ∈ rightArc
  left_e_ne : ∀ j ∈ leftArc, e ≠ j
  right_t_ne : ∀ j ∈ rightArc, t ≠ j
  left_s_ne : ∀ j ∈ leftArc, j ≠ s
  right_s_ne : ∀ j ∈ rightArc, j ≠ s
  leftHalfPlane : ∀ j ∈ leftArc,
    InLeftOpenHalfPlane (P e) (P vertex) (P j)
  /-- The return arc lies to the left of the reversed chord `vertex ⟶ t`. -/
  rightHalfPlane : ∀ j ∈ rightArc,
    InLeftOpenHalfPlane (P vertex) (P t) (P j)
  leftQuad : ∀ j ∈ leftArc,
    StrictConvexQuad (P vertex) (P j) (P s) (P e)
  rightQuad : ∀ j ∈ rightArc,
    StrictConvexQuad (P t) (P s) (P j) (P vertex)
  rungQuad : StrictConvexQuad (P t) (P p) (P s) (P vertex)
  tipAbove : 0 < turn (P e) (P t) (P s)
  vertexBelow : turn (P e) (P t) (P vertex) < 0
  es : sqDist (P e) (P s) = d₁
  ts : sqDist (P t) (P s) = d₁
  tp : sqDist (P t) (P p) = d₂

private theorem one_penultimate_tip_unique_farthest
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : OnePenultimateWordGeometry P d₁ d₂ d₃) :
    ∀ j, j ≠ G.s →
      sqDist (P G.vertex) (P j) < sqDist (P G.vertex) (P G.s) :=
  shared_tip_unique_farthest G.pointsInjective G.classes G.e_ne_t
    G.es G.ts G.tipAbove G.vertexBelow

private theorem one_penultimate_arc_card_le_two_raw
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : OnePenultimateWordGeometry P d₁ d₂ d₃)
    {arc : Finset (Fin n)} {center : Fin n}
    (hcenter : center ≠ G.vertex)
    (hcenterArc : ∀ j ∈ arc, center ≠ j)
    (hsArc : ∀ j ∈ arc, j ≠ G.s)
    (hside :
      (∀ j ∈ arc, InLeftOpenHalfPlane (P center) (P G.vertex) (P j)) ∨
      (∀ j ∈ arc, InLeftOpenHalfPlane (P G.vertex) (P center) (P j)))
    (hED : ∀ j ∈ arc,
      euclideanDist (P G.vertex) (P j) + Real.sqrt d₁ <
        Real.sqrt d₂ + euclideanDist (P center) (P j))
    (hVs : sqDist (P G.vertex) (P G.s) = d₂) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex arc).card ≤ 2 := by
  apply arcNeighbors_card_le_of_two_slots
    (firstCenter := center) (secondCenter := G.vertex)
    (a₁ := d₁) (b₁ := d₃) (a₂ := d₂) (b₂ := d₃)
  · intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjArc := hjData.1
    have hfarSq := one_penultimate_tip_unique_farthest G j (hsArc j hjArc)
    rw [hVs] at hfarSq
    rcases hjData.2.2 with hVj | hVj | hVj
    · exfalso
      linarith [G.classes.2.1]
    · exfalso
      linarith
    · have hEDj := hED j hjArc
      rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hEDj
      have horder := (top_three_radius_strict_order G.classes).2
      have hcenterFar : Real.sqrt d₃ < euclideanDist (P center) (P j) := by
        linarith [hEDj]
      rcases sqDist_eq_d₁_or_d₂_of_sqrt_d₃_lt G.classes
          (hcenterArc j hjArc) hcenterFar with hcj | hcj
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨hjArc, hcj, hVj⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hjArc, hcj, hVj⟩))
  · exact circleSlot_card_le_one_either G.pointsInjective hcenter hside
  · exact circleSlot_card_le_one_either G.pointsInjective hcenter hside

private theorem one_penultimate_left_arc_card_le_two
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : OnePenultimateWordGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.leftArc).card ≤ 2 := by
  apply one_penultimate_arc_card_le_two_raw G G.e_ne_vertex G.left_e_ne
    G.left_s_ne (Or.inl G.leftHalfPlane)
  · intro j hj
    have hED := edge_diagonal_inequality (G.leftQuad j hj)
    rw [euclideanDist_comm_local (P G.s) (P G.e),
      euclideanDist_eq_sqrt_of_sqDist_eq G.es,
      euclideanDist_eq_sqrt_of_sqDist_eq hVs,
      euclideanDist_comm_local (P j) (P G.e)] at hED
    linarith
  · exact hVs

private theorem one_penultimate_right_arc_card_le_two
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : OnePenultimateWordGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.rightArc).card ≤ 2 := by
  apply one_penultimate_arc_card_le_two_raw G G.t_ne_vertex G.right_t_ne
    G.right_s_ne (Or.inr G.rightHalfPlane)
  · intro j hj
    have hED := edge_diagonal_inequality (G.rightQuad j hj)
    rw [euclideanDist_eq_sqrt_of_sqDist_eq G.ts,
      euclideanDist_comm_local (P j) (P G.vertex),
      euclideanDist_comm_local (P G.s) (P G.vertex),
      euclideanDist_eq_sqrt_of_sqDist_eq hVs] at hED
    linarith
  · exact hVs

private theorem one_penultimate_low_degree_le_one
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : OnePenultimateWordGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) ≤ d₃) :
    vertexDegree P d₁ d₂ d₃ G.vertex ≤ 1 := by
  classical
  unfold vertexDegree
  apply (Finset.card_le_card (t := {G.s}) ?_).trans
  · simp
  intro j hj
  have hjData := Finset.mem_filter.mp hj
  have hjne := (Finset.mem_erase.mp hjData.1).1
  by_cases hjs : j = G.s
  · simp [hjs]
  have hfar := one_penultimate_tip_unique_farthest G j hjs
  have hlt : sqDist (P G.vertex) (P j) < d₃ := hfar.trans_le hVs
  rcases hjData.2 with hj | hj | hj <;> linarith [G.classes.1, G.classes.2.1]

private theorem one_penultimate_tip_not_d₁
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : OnePenultimateWordGeometry P d₁ d₂ d₃) :
    sqDist (P G.vertex) (P G.s) ≠ d₁ := by
  intro hVs
  have hVpBounds := top_three_radius_bounds_of_ne G.classes G.p_ne_vertex.symm
  dsimp only at hVpBounds
  have hfarSq := one_penultimate_tip_unique_farthest G G.p G.p_ne_s
  have ⟨hd₁, _, _⟩ := top_three_values_nonnegative G.classes
  have hfar : euclideanDist (P G.vertex) (P G.p) <
      euclideanDist (P G.vertex) (P G.s) := by
    rw [euclideanDist_eq_sqrt_sqDist, euclideanDist_eq_sqrt_sqDist]
    exact Real.sqrt_lt_sqrt (sqDist_nonneg _ _) hfarSq
  have hED := edge_diagonal_inequality G.rungQuad
  rw [euclideanDist_eq_sqrt_of_sqDist_eq G.tp,
    euclideanDist_comm_local (P G.s) (P G.vertex),
    euclideanDist_eq_sqrt_of_sqDist_eq hVs,
    euclideanDist_eq_sqrt_of_sqDist_eq G.ts,
    euclideanDist_comm_local (P G.p) (P G.vertex)] at hED
  have hVsRadius := euclideanDist_eq_sqrt_of_sqDist_eq hVs
  have hnot := one_penultimate_anti_saturation
    ⟨hVpBounds.1, hVpBounds.2.1⟩ hfar (by linarith [hED, hVsRadius])
  exact hnot (euclideanDist_eq_sqrt_of_sqDist_eq hVs)

/-- Every raw one-penultimate realization has displayed degree at most five. -/
theorem one_penultimate_realization_degree_le_five
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : OnePenultimateWordGeometry P d₁ d₂ d₃) :
    vertexDegree P d₁ d₂ d₃ G.vertex ≤ 5 := by
  have hVsBounds := top_three_class_bounds_of_ne G.classes G.s_ne_vertex.symm
  rcases top_three_value_split hVsBounds with hVs | hVs | hVs
  · exact (one_penultimate_tip_not_d₁ G hVs).elim
  · have hleft := one_penultimate_left_arc_card_le_two G hVs
    have hright := one_penultimate_right_arc_card_le_two G hVs
    have hpartition := vertexDegree_le_partition_three
      (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) G.arcPartition
    omega
  · exact (one_penultimate_low_degree_le_one G hVs).trans (by omega)

/-- One raw boundary branch in the four-edge cage.  The disjunction records
the two cyclic orientations that yield the same edge--diagonal inequality. -/
structure FourEdgeBranchGeometry
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ : ℝ)
    (vertex center central : Fin n) where
  /-- Boundary arc assigned to this cage branch. -/
  arc : Finset (Fin n)
  center_ne_vertex : center ≠ vertex
  center_ne_arc : ∀ j ∈ arc, center ≠ j
  /-- One consistent side of the unoriented line through the two centers. -/
  halfPlane :
    (∀ j ∈ arc, InLeftOpenHalfPlane (P center) (P vertex) (P j)) ∨
    (∀ j ∈ arc, InLeftOpenHalfPlane (P vertex) (P center) (P j))
  quad : ∀ j ∈ arc,
    StrictConvexQuad (P vertex) (P j) (P central) (P center) ∨
      StrictConvexQuad (P center) (P central) (P j) (P vertex)
  diameterEdge : sqDist (P center) (P central) = d₁

private theorem fourEdgeBranchED
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ : ℝ}
    {vertex center central : Fin n}
    (B : FourEdgeBranchGeometry P d₁ vertex center central)
    {j : Fin n} (hj : j ∈ B.arc) :
    euclideanDist (P vertex) (P j) + Real.sqrt d₁ <
      euclideanDist (P center) (P j) + euclideanDist (P vertex) (P central) := by
  rcases B.quad j hj with hquad | hquad
  · have hED := edge_diagonal_inequality hquad
    rw [euclideanDist_comm_local (P central) (P center),
      euclideanDist_eq_sqrt_of_sqDist_eq B.diameterEdge,
      euclideanDist_comm_local (P j) (P center)] at hED
    linarith
  · have hED := edge_diagonal_inequality hquad
    rw [euclideanDist_eq_sqrt_of_sqDist_eq B.diameterEdge,
      euclideanDist_comm_local (P j) (P vertex),
      euclideanDist_comm_local (P central) (P vertex)] at hED
    linarith

private theorem fourEdgeBranch_card_le_three_of_central_d₁
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {vertex center central : Fin n}
    (hInjective : Function.Injective P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (B : FourEdgeBranchGeometry P d₁ vertex center central)
    (hCentral : sqDist (P vertex) (P central) = d₁) :
    (arcNeighbors P d₁ d₂ d₃ vertex B.arc).card ≤ 3 := by
  apply arcNeighbors_card_le_of_three_slots
    (firstCenter := center) (secondCenter := vertex)
    (a₁ := d₁) (b₁ := d₂) (a₂ := d₁) (b₂ := d₃)
    (a₃ := d₂) (b₃ := d₃)
  · intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjArc := hjData.1
    have hED := fourEdgeBranchED B hjArc
    rw [euclideanDist_eq_sqrt_of_sqDist_eq hCentral] at hED
    rcases hjData.2.2 with hVj | hVj | hVj
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₁ < euclideanDist (P center) (P j) := by linarith
      exact (euclideanDist_not_gt_sqrt_d₁ hClasses
        (B.center_ne_arc j hjArc) hfar).elim
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₂ < euclideanDist (P center) (P j) := by linarith
      have hcj := sqDist_eq_d₁_of_sqrt_d₂_lt hClasses
        (B.center_ne_arc j hjArc) hfar
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hjArc, hcj, hVj⟩))))
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₃ < euclideanDist (P center) (P j) := by linarith
      rcases sqDist_eq_d₁_or_d₂_of_sqrt_d₃_lt hClasses
          (B.center_ne_arc j hjArc) hfar with hcj | hcj
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hjArc, hcj, hVj⟩))))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hjArc, hcj, hVj⟩))
  · exact circleSlot_card_le_one_either hInjective B.center_ne_vertex B.halfPlane
  · exact circleSlot_card_le_one_either hInjective B.center_ne_vertex B.halfPlane
  · exact circleSlot_card_le_one_either hInjective B.center_ne_vertex B.halfPlane

private theorem fourEdgeBranch_card_le_two_of_central_d₂
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {vertex center central : Fin n}
    (hInjective : Function.Injective P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (B : FourEdgeBranchGeometry P d₁ vertex center central)
    (hCentral : sqDist (P vertex) (P central) = d₂) :
    (arcNeighbors P d₁ d₂ d₃ vertex B.arc).card ≤ 2 := by
  apply arcNeighbors_card_le_of_two_slots
    (firstCenter := center) (secondCenter := vertex)
    (a₁ := d₁) (b₁ := d₃) (a₂ := d₂) (b₂ := d₃)
  · intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjArc := hjData.1
    have hED := fourEdgeBranchED B hjArc
    rw [euclideanDist_eq_sqrt_of_sqDist_eq hCentral] at hED
    rcases hjData.2.2 with hVj | hVj | hVj
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hcenterBounds := top_three_radius_bounds_of_ne hClasses
        (B.center_ne_arc j hjArc)
      dsimp only at hcenterBounds
      have horder := (top_three_radius_strict_order hClasses).2
      exfalso
      linarith
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₁ < euclideanDist (P center) (P j) := by linarith
      exact (euclideanDist_not_gt_sqrt_d₁ hClasses
        (B.center_ne_arc j hjArc) hfar).elim
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have horder := (top_three_radius_strict_order hClasses).2
      have hfar : Real.sqrt d₃ < euclideanDist (P center) (P j) := by linarith
      rcases sqDist_eq_d₁_or_d₂_of_sqrt_d₃_lt hClasses
          (B.center_ne_arc j hjArc) hfar with hcj | hcj
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨hjArc, hcj, hVj⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hjArc, hcj, hVj⟩))
  · exact circleSlot_card_le_one_either hInjective B.center_ne_vertex B.halfPlane
  · exact circleSlot_card_le_one_either hInjective B.center_ne_vertex B.halfPlane

private theorem fourEdgeBranch_card_le_one_of_central_d₂_long
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {vertex center central : Fin n}
    (hInjective : Function.Injective P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (B : FourEdgeBranchGeometry P d₁ vertex center central)
    (hCentral : sqDist (P vertex) (P central) = d₂)
    (hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃) :
    (arcNeighbors P d₁ d₂ d₃ vertex B.arc).card ≤ 1 := by
  apply arcNeighbors_card_le_of_one_slot
    (firstCenter := center) (secondCenter := vertex) (a := d₁) (b := d₃)
  · intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjArc := hjData.1
    have hED := fourEdgeBranchED B hjArc
    rw [euclideanDist_eq_sqrt_of_sqDist_eq hCentral] at hED
    rcases hjData.2.2 with hVj | hVj | hVj
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hcenterBounds := top_three_radius_bounds_of_ne hClasses
        (B.center_ne_arc j hjArc)
      dsimp only at hcenterBounds
      have horder := (top_three_radius_strict_order hClasses).2
      exfalso
      linarith
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₁ < euclideanDist (P center) (P j) := by linarith
      exact (euclideanDist_not_gt_sqrt_d₁ hClasses
        (B.center_ne_arc j hjArc) hfar).elim
    · rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED
      have hfar : Real.sqrt d₂ < euclideanDist (P center) (P j) := by
        linarith
      have hcj := sqDist_eq_d₁_of_sqrt_d₂_lt hClasses
        (B.center_ne_arc j hjArc) hfar
      exact Finset.mem_filter.mpr ⟨hjArc, hcj, hVj⟩
  · exact circleSlot_card_le_one_either hInjective B.center_ne_vertex B.halfPlane

private theorem fourEdgeBranch_card_eq_zero_of_central_le_d₃
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {vertex center central : Fin n}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (B : FourEdgeBranchGeometry P d₁ vertex center central)
    (hCentral : sqDist (P vertex) (P central) ≤ d₃) :
    (arcNeighbors P d₁ d₂ d₃ vertex B.arc).card = 0 := by
  by_contra hnot
  have hpos : 0 < (arcNeighbors P d₁ d₂ d₃ vertex B.arc).card := by omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  have hjData := Finset.mem_filter.mp hj
  have hjArc := hjData.1
  have hcentralDist := euclideanDist_le_sqrt_of_sqDist_le hCentral
  have hcenterBounds := top_three_radius_bounds_of_ne hClasses (B.center_ne_arc j hjArc)
  dsimp only at hcenterBounds
  have hED := fourEdgeBranchED B hjArc
  have horder := top_three_radius_strict_order hClasses
  rcases hjData.2.2 with hVj | hVj | hVj <;>
    rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED <;> linarith

private noncomputable def singletonNeighbor
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (v j : Fin n) : Finset (Fin n) :=
  ({j} : Finset (Fin n)).filter fun k ↦ k ≠ v ∧
    (sqDist (P v) (P k) = d₁ ∨ sqDist (P v) (P k) = d₂ ∨
      sqDist (P v) (P k) = d₃)

private noncomputable def cageSideNeighbors
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (v central : Fin n) (arc : Finset (Fin n)) : Finset (Fin n) :=
  arcNeighbors P d₁ d₂ d₃ v arc ∪
    singletonNeighbor P d₁ d₂ d₃ v central

private theorem singletonNeighbor_card_le_one
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {v j : Fin n} :
    (singletonNeighbor P d₁ d₂ d₃ v j).card ≤ 1 := by
  exact (Finset.card_filter_le _ _).trans (by simp)

private theorem singletonNeighbor_card_eq_zero_of_lt_d₃
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {v j : Fin n} (h : sqDist (P v) (P j) < d₃) :
    (singletonNeighbor P d₁ d₂ d₃ v j).card = 0 := by
  by_contra hnot
  have hpos : 0 < (singletonNeighbor P d₁ d₂ d₃ v j).card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  have hkData := Finset.mem_filter.mp hk
  have hkj := Finset.mem_singleton.mp hkData.1
  subst k
  rcases hkData.2.2 with hj | hj | hj <;>
    linarith [hClasses.1, hClasses.2.1]

private theorem cageSideNeighbors_card_le
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {v central : Fin n} {arc : Finset (Fin n)} :
    (cageSideNeighbors P d₁ d₂ d₃ v central arc).card ≤
      (arcNeighbors P d₁ d₂ d₃ v arc).card +
        (singletonNeighbor P d₁ d₂ d₃ v central).card := by
  exact Finset.card_union_le _ _

/-- Raw data for the two sides counted at one central cage endpoint. -/
structure FourEdgeEndpointGeometry
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (x t w s : Fin n) where
  /-- Central cage endpoint whose degree is counted. -/
  vertex : Fin n
  w_ne_vertex : w ≠ vertex
  s_ne_vertex : s ≠ vertex
  /-- First-center boundary branch. -/
  left : FourEdgeBranchGeometry P d₁ vertex x w
  /-- Second-center boundary branch. -/
  right : FourEdgeBranchGeometry P d₁ vertex t s
  arcPartition : ∀ j, j ≠ vertex →
    j ∈ left.arc ∨ j = w ∨ j = s ∨ j ∈ right.arc

private theorem fourEdgeEndpoint_degree_le_sides
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {x t w s : Fin n}
    (E : FourEdgeEndpointGeometry P d₁ d₂ d₃ x t w s) :
    vertexDegree P d₁ d₂ d₃ E.vertex ≤
      (cageSideNeighbors P d₁ d₂ d₃ E.vertex w E.left.arc).card +
        (cageSideNeighbors P d₁ d₂ d₃ E.vertex s E.right.arc).card := by
  classical
  let N := (Finset.univ.erase E.vertex).filter fun j ↦
    sqDist (P E.vertex) (P j) = d₁ ∨ sqDist (P E.vertex) (P j) = d₂ ∨
      sqDist (P E.vertex) (P j) = d₃
  let L := cageSideNeighbors P d₁ d₂ d₃ E.vertex w E.left.arc
  let R := cageSideNeighbors P d₁ d₂ d₃ E.vertex s E.right.arc
  have hsubset : N ⊆ L ∪ R := by
    intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjne := (Finset.mem_erase.mp hjData.1).1
    rcases E.arcPartition j hjne with hjLeft | hjw | hjs | hjRight
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hjLeft, hjne, hjData.2⟩))))
    · subst j
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨by simp, E.w_ne_vertex, hjData.2⟩))))
    · subst j
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨by simp, E.s_ne_vertex, hjData.2⟩))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hjRight, hjne, hjData.2⟩))))
  change N.card ≤ _
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le L R)

private def RealizesCageBand
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (v central : Fin n) : CageDistanceBand → Prop
  | .d1 => sqDist (P v) (P central) = d₁
  | .d2 => sqDist (P v) (P central) = d₂
  | .d3 => sqDist (P v) (P central) = d₃
  | .below => sqDist (P v) (P central) < d₃

private theorem cageSide_general_bound
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {vertex center central : Fin n}
    (hInjective : Function.Injective P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (B : FourEdgeBranchGeometry P d₁ vertex center central)
    (band : CageDistanceBand)
    (hBand : RealizesCageBand P d₁ d₂ d₃ vertex central band) :
    (cageSideNeighbors P d₁ d₂ d₃ vertex central B.arc).card ≤
      fourEdgeGeneralPackage band := by
  have hside := cageSideNeighbors_card_le
    (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)
    (v := vertex) (central := central) (arc := B.arc)
  cases band with
  | d1 =>
      have harc := fourEdgeBranch_card_le_three_of_central_d₁
        hInjective hClasses B hBand
      have hcentral := singletonNeighbor_card_le_one
        (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)
        (v := vertex) (j := central)
      simp only [fourEdgeGeneralPackage]
      omega
  | d2 =>
      have harc := fourEdgeBranch_card_le_two_of_central_d₂
        hInjective hClasses B hBand
      have hcentral := singletonNeighbor_card_le_one
        (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)
        (v := vertex) (j := central)
      simp only [fourEdgeGeneralPackage]
      omega
  | d3 =>
      have harc := fourEdgeBranch_card_eq_zero_of_central_le_d₃ hClasses B hBand.le
      have hcentral := singletonNeighbor_card_le_one
        (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)
        (v := vertex) (j := central)
      simp only [fourEdgeGeneralPackage]
      omega
  | below =>
      have harc := fourEdgeBranch_card_eq_zero_of_central_le_d₃ hClasses B hBand.le
      have hcentral := singletonNeighbor_card_eq_zero_of_lt_d₃ hClasses hBand
      simp only [fourEdgeGeneralPackage]
      omega

private theorem cageSide_long_bound
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {vertex center central : Fin n}
    (hInjective : Function.Injective P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (B : FourEdgeBranchGeometry P d₁ vertex center central)
    (hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃)
    (band : CageDistanceBand)
    (hBand : RealizesCageBand P d₁ d₂ d₃ vertex central band) :
    (cageSideNeighbors P d₁ d₂ d₃ vertex central B.arc).card ≤
      fourEdgeLongPackage band := by
  cases band with
  | d1 =>
      simpa [fourEdgeLongPackage, fourEdgeGeneralPackage] using
        cageSide_general_bound hInjective hClasses B .d1 hBand
  | d2 =>
      have hside := cageSideNeighbors_card_le
        (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)
        (v := vertex) (central := central) (arc := B.arc)
      have harc := fourEdgeBranch_card_le_one_of_central_d₂_long
        hInjective hClasses B hBand hlong
      have hcentral := singletonNeighbor_card_le_one
        (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)
        (v := vertex) (j := central)
      simp only [fourEdgeLongPackage]
      omega
  | d3 =>
      simpa [fourEdgeLongPackage, fourEdgeGeneralPackage] using
        cageSide_general_bound hInjective hClasses B .d3 hBand
  | below =>
      simpa [fourEdgeLongPackage, fourEdgeGeneralPackage] using
        cageSide_general_bound hInjective hClasses B .below hBand

private theorem exists_cage_band
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {v central : Fin n} (hne : v ≠ central) :
    ∃ band, RealizesCageBand P d₁ d₂ d₃ v central band := by
  have hbounds := top_three_class_bounds_of_ne hClasses hne
  rcases top_three_value_split hbounds with h₁ | h₂ | hlow
  · exact ⟨.d1, h₁⟩
  · exact ⟨.d2, h₂⟩
  · by_cases h₃ : sqDist (P v) (P central) = d₃
    · exact ⟨.d3, h₃⟩
    · exact ⟨.below, lt_of_le_of_ne hlow h₃⟩

private structure FourEdgeEndpointPackage
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {x t w s : Fin n}
    (E : FourEdgeEndpointGeometry P d₁ d₂ d₃ x t w s) where
  leftBand : CageDistanceBand
  rightBand : CageDistanceBand
  leftSpec : RealizesCageBand P d₁ d₂ d₃ E.vertex w leftBand
  rightSpec : RealizesCageBand P d₁ d₂ d₃ E.vertex s rightBand
  generalBound : vertexDegree P d₁ d₂ d₃ E.vertex ≤
    fourEdgeGeneralPackage leftBand + fourEdgeGeneralPackage rightBand
  longBound : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃ →
    vertexDegree P d₁ d₂ d₃ E.vertex ≤
      fourEdgeLongPackage leftBand + fourEdgeLongPackage rightBand

private noncomputable def fourEdgeEndpointPackage
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {x t w s : Fin n}
    (hInjective : Function.Injective P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (E : FourEdgeEndpointGeometry P d₁ d₂ d₃ x t w s) :
    FourEdgeEndpointPackage E := by
  let leftBand := Classical.choose (exists_cage_band hClasses E.w_ne_vertex.symm)
  have leftSpec : RealizesCageBand P d₁ d₂ d₃ E.vertex w leftBand :=
    Classical.choose_spec (exists_cage_band hClasses E.w_ne_vertex.symm)
  let rightBand := Classical.choose (exists_cage_band hClasses E.s_ne_vertex.symm)
  have rightSpec : RealizesCageBand P d₁ d₂ d₃ E.vertex s rightBand :=
    Classical.choose_spec (exists_cage_band hClasses E.s_ne_vertex.symm)
  have hdegree := fourEdgeEndpoint_degree_le_sides E
  have hleftGeneral := cageSide_general_bound hInjective hClasses E.left
    leftBand leftSpec
  have hrightGeneral := cageSide_general_bound hInjective hClasses E.right
    rightBand rightSpec
  refine {
    leftBand := leftBand
    rightBand := rightBand
    leftSpec := leftSpec
    rightSpec := rightSpec
    generalBound := by omega
    longBound := ?_ }
  intro hlong
  have hleftLong := cageSide_long_bound hInjective hClasses E.left hlong
    leftBand leftSpec
  have hrightLong := cageSide_long_bound hInjective hClasses E.right hlong
    rightBand rightSpec
  omega

/-- Raw row-4 `DD` four-edge cage. -/
structure Row4DDWordRealization
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  pointsInjective : Function.Injective P
  classes : HasTopThreeDistanceClasses P d₁ d₂ d₃
  /-- First diameter center. -/
  x : Fin n
  /-- Second diameter center. -/
  t : Fin n
  /-- First central rung endpoint. -/
  w : Fin n
  /-- Second central rung endpoint. -/
  s : Fin n
  w_ne_s : w ≠ s
  x_ne_w : x ≠ w
  x_ne_s : x ≠ s
  t_ne_w : t ≠ w
  t_ne_s : t ≠ s
  /-- First central cage endpoint. -/
  first : FourEdgeEndpointGeometry P d₁ d₂ d₃ x t w s
  /-- Second central cage endpoint. -/
  second : FourEdgeEndpointGeometry P d₁ d₂ d₃ x t w s
  first_ne_second : first.vertex ≠ second.vertex
  xSide : InLeftOpenHalfPlane (P w) (P s) (P x)
  tSide : InLeftOpenHalfPlane (P w) (P s) (P t)
  firstSide : InLeftOpenHalfPlane (P w) (P s) (P first.vertex)
  secondSide : InLeftOpenHalfPlane (P w) (P s) (P second.vertex)
  xw : sqDist (P x) (P w) = d₁
  xs : sqDist (P x) (P s) = d₂
  tw : sqDist (P t) (P w) = d₂
  ts : sqDist (P t) (P s) = d₁

private theorem fourEdge_mixed_d1_d2_impossible
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row4DDWordRealization P d₁ d₂ d₃)
    (E : FourEdgeEndpointGeometry P d₁ d₂ d₃ G.x G.t G.w G.s)
    (hSide : InLeftOpenHalfPlane (P G.w) (P G.s) (P E.vertex))
    (hW : sqDist (P E.vertex) (P G.w) = d₁)
    (hS : sqDist (P E.vertex) (P G.s) = d₂) : False := by
  have heq : P E.vertex = P G.x := by
    apply same_half_plane_two_circle_unique (G.pointsInjective.ne G.w_ne_s)
    · simpa only [sqDist_comm] using hW.trans G.xw.symm
    · simpa only [sqDist_comm] using hS.trans G.xs.symm
    · exact hSide
    · exact G.xSide
  exact E.left.center_ne_vertex (G.pointsInjective heq).symm

private theorem fourEdge_mixed_d2_d1_impossible
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row4DDWordRealization P d₁ d₂ d₃)
    (E : FourEdgeEndpointGeometry P d₁ d₂ d₃ G.x G.t G.w G.s)
    (hSide : InLeftOpenHalfPlane (P G.w) (P G.s) (P E.vertex))
    (hW : sqDist (P E.vertex) (P G.w) = d₂)
    (hS : sqDist (P E.vertex) (P G.s) = d₁) : False := by
  have heq : P E.vertex = P G.t := by
    apply same_half_plane_two_circle_unique (G.pointsInjective.ne G.w_ne_s)
    · simpa only [sqDist_comm] using hW.trans G.tw.symm
    · simpa only [sqDist_comm] using hS.trans G.ts.symm
    · exact hSide
    · exact G.tSide
  exact E.right.center_ne_vertex (G.pointsInjective heq).symm

private theorem fourEdge_two_d1d1_impossible
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row4DDWordRealization P d₁ d₂ d₃)
    (hFirstW : sqDist (P G.first.vertex) (P G.w) = d₁)
    (hFirstS : sqDist (P G.first.vertex) (P G.s) = d₁)
    (hSecondW : sqDist (P G.second.vertex) (P G.w) = d₁)
    (hSecondS : sqDist (P G.second.vertex) (P G.s) = d₁) : False := by
  have heq : P G.first.vertex = P G.second.vertex := by
    apply same_half_plane_two_circle_unique (G.pointsInjective.ne G.w_ne_s)
    · simpa only [sqDist_comm] using hFirstW.trans hSecondW.symm
    · simpa only [sqDist_comm] using hFirstS.trans hSecondS.symm
    · exact G.firstSide
    · exact G.secondSide
  exact G.first_ne_second (G.pointsInjective heq)

/-- The row-4 `DD` cage closes by the exact long/short package split. -/
theorem row4_DD_realization_min_degree_le_six
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row4DDWordRealization P d₁ d₂ d₃) :
    min (vertexDegree P d₁ d₂ d₃ G.first.vertex)
      (vertexDegree P d₁ d₂ d₃ G.second.vertex) ≤ 6 := by
  let firstPackage := fourEdgeEndpointPackage G.pointsInjective G.classes G.first
  let secondPackage := fourEdgeEndpointPackage G.pointsInjective G.classes G.second
  by_cases hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃
  · apply four_edge_cage_long_min_degree_le_six
      (firstPackage.longBound hlong) (secondPackage.longBound hlong)
    intro hstates
    rcases hstates with ⟨hFirstLeft, hFirstRight, hSecondLeft, hSecondRight⟩
    apply fourEdge_two_d1d1_impossible G
    · simpa [hFirstLeft, RealizesCageBand] using firstPackage.leftSpec
    · simpa [hFirstRight, RealizesCageBand] using firstPackage.rightSpec
    · simpa [hSecondLeft, RealizesCageBand] using secondPackage.leftSpec
    · simpa [hSecondRight, RealizesCageBand] using secondPackage.rightSpec
  · apply four_edge_cage_short_min_degree_le_six
      firstPackage.generalBound secondPackage.generalBound
    · intro hstates
      exact fourEdge_mixed_d1_d2_impossible G G.first G.firstSide
        (by simpa [hstates.1, RealizesCageBand] using firstPackage.leftSpec)
        (by simpa [hstates.2, RealizesCageBand] using firstPackage.rightSpec)
    · intro hstates
      exact fourEdge_mixed_d2_d1_impossible G G.first G.firstSide
        (by simpa [hstates.1, RealizesCageBand] using firstPackage.leftSpec)
        (by simpa [hstates.2, RealizesCageBand] using firstPackage.rightSpec)
    · intro hstates
      exact fourEdge_mixed_d1_d2_impossible G G.second G.secondSide
        (by simpa [hstates.1, RealizesCageBand] using secondPackage.leftSpec)
        (by simpa [hstates.2, RealizesCageBand] using secondPackage.rightSpec)
    · intro hstates
      exact fourEdge_mixed_d2_d1_impossible G G.second G.secondSide
        (by simpa [hstates.1, RealizesCageBand] using secondPackage.leftSpec)
        (by simpa [hstates.2, RealizesCageBand] using secondPackage.rightSpec)
    · intro hstates
      rcases hstates with ⟨hFirstLeft, hFirstRight, hSecondLeft, hSecondRight⟩
      apply fourEdge_two_d1d1_impossible G
      · simpa [hFirstLeft, RealizesCageBand] using firstPackage.leftSpec
      · simpa [hFirstRight, RealizesCageBand] using firstPackage.rightSpec
      · simpa [hSecondLeft, RealizesCageBand] using secondPackage.leftSpec
      · simpa [hSecondRight, RealizesCageBand] using secondPackage.rightSpec

/-- Raw row-4 `DD` geometry supplies an actual vertex of degree at most six. -/
theorem row4_DD_realization_degree_le_six
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row4DDWordRealization P d₁ d₂ d₃) :
    ∃ v, vertexDegree P d₁ d₂ d₃ v ≤ 6 := by
  have hmin := row4_DD_realization_min_degree_le_six G
  by_cases hle : vertexDegree P d₁ d₂ d₃ G.first.vertex ≤
      vertexDegree P d₁ d₂ d₃ G.second.vertex
  · exact ⟨G.first.vertex, by simpa [min_eq_left hle] using hmin⟩
  · have hreverse : vertexDegree P d₁ d₂ d₃ G.second.vertex ≤
        vertexDegree P d₁ d₂ d₃ G.first.vertex := by omega
    exact ⟨G.second.vertex, by simpa [min_eq_right hreverse] using hmin⟩

/-- Raw full-two-rung shared-tip geometry.  The four arc pieces are the two
open half-planes for each of the two diameter-center circle systems. -/
structure FullTwoRungGeometry
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  pointsInjective : Function.Injective P
  classes : HasTopThreeDistanceClasses P d₁ d₂ d₃
  /-- First diameter center. -/
  e : Fin n
  /-- Second diameter center. -/
  t : Fin n
  /-- Shared upper tip. -/
  s : Fin n
  /-- Penultimate point on the first rung. -/
  w : Fin n
  /-- Penultimate point on the second rung. -/
  r : Fin n
  /-- Lower vertex whose degree is bounded. -/
  vertex : Fin n
  /-- Remaining explicitly separated boundary endpoint. -/
  endpoint : Fin n
  e_ne_t : e ≠ t
  e_ne_s : e ≠ s
  t_ne_s : t ≠ s
  w_ne_s : w ≠ s
  r_ne_s : r ≠ s
  vertex_ne_e : vertex ≠ e
  vertex_ne_t : vertex ≠ t
  vertex_ne_s : vertex ≠ s
  vertex_ne_w : vertex ≠ w
  vertex_ne_r : vertex ≠ r
  tipAbove : 0 < turn (P e) (P t) (P s)
  vertexBelow : turn (P e) (P t) (P vertex) < 0
  wAbove : 0 < turn (P e) (P t) (P w)
  rAbove : 0 < turn (P e) (P t) (P r)
  wBelowTip : turn (P e) (P t) (P w) < turn (P e) (P t) (P s)
  es : sqDist (P e) (P s) = d₁
  ts : sqDist (P t) (P s) = d₁
  ew : sqDist (P e) (P w) = d₁
  tw : sqDist (P t) (P w) = d₂
  er : sqDist (P e) (P r) = d₂
  tr : sqDist (P t) (P r) = d₁
  antiSaturationQuad : StrictConvexQuad (P t) (P w) (P s) (P vertex)
  /-- First-center arc in the positive half-plane. -/
  ePositiveArc : Finset (Fin n)
  /-- First-center arc in the opposite half-plane. -/
  eNegativeArc : Finset (Fin n)
  /-- Second-center arc in the positive half-plane. -/
  tPositiveArc : Finset (Fin n)
  /-- Second-center arc in the opposite half-plane. -/
  tNegativeArc : Finset (Fin n)
  arcPartition : ∀ j, j ≠ vertex →
    j ∈ ePositiveArc ∨ j ∈ eNegativeArc ∨ j ∈ tPositiveArc ∨
      j ∈ tNegativeArc ∨ j = s ∨ j = endpoint
  ePositive_ne_tip : ∀ j ∈ ePositiveArc, j ≠ s
  eNegative_ne_tip : ∀ j ∈ eNegativeArc, j ≠ s
  tPositive_ne_tip : ∀ j ∈ tPositiveArc, j ≠ s
  tNegative_ne_tip : ∀ j ∈ tNegativeArc, j ≠ s
  ePositive_center_ne : ∀ j ∈ ePositiveArc, e ≠ j
  eNegative_center_ne : ∀ j ∈ eNegativeArc, e ≠ j
  tPositive_center_ne : ∀ j ∈ tPositiveArc, t ≠ j
  tNegative_center_ne : ∀ j ∈ tNegativeArc, t ≠ j
  ePositiveHalfPlane : ∀ j ∈ ePositiveArc,
    InLeftOpenHalfPlane (P e) (P vertex) (P j)
  eNegativeHalfPlane : ∀ j ∈ eNegativeArc,
    InLeftOpenHalfPlane (P vertex) (P e) (P j)
  tPositiveHalfPlane : ∀ j ∈ tPositiveArc,
    InLeftOpenHalfPlane (P t) (P vertex) (P j)
  tNegativeHalfPlane : ∀ j ∈ tNegativeArc,
    InLeftOpenHalfPlane (P vertex) (P t) (P j)
  ePositiveQuad : ∀ j ∈ ePositiveArc,
    StrictConvexQuad (P vertex) (P j) (P s) (P e)
  eNegativeQuad : ∀ j ∈ eNegativeArc,
    StrictConvexQuad (P vertex) (P j) (P s) (P e)
  tPositiveQuad : ∀ j ∈ tPositiveArc,
    StrictConvexQuad (P t) (P s) (P j) (P vertex)
  tNegativeQuad : ∀ j ∈ tNegativeArc,
    StrictConvexQuad (P t) (P s) (P j) (P vertex)

private noncomputable def FullTwoRungGeometry.normalized
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃) : Fin n → Point ℝ :=
  fun j ↦ normalizeAlong (P G.e) (P G.t) (P j)

private structure FullTwoRungCanonicalFrame
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃) where
  scale : ℝ
  c : ℝ
  H : ℝ
  offset : ℝ
  K : ℝ
  heightDrop : ℝ
  X : ℝ
  Y : ℝ
  scale_pos : 0 < scale
  c_pos : 0 < c
  H_pos : 0 < H
  offset_pos : 0 < offset
  K_pos : 0 < K
  heightDrop_pos : 0 < heightDrop
  Y_neg : Y < 0
  scale_eq : scale = 2 * c
  e_coord : G.normalized G.e = (0, 0)
  t_coord : G.normalized G.t = (2 * c, 0)
  s_coord : G.normalized G.s = (c, H)
  w_coord : G.normalized G.w = (c + offset, K)
  r_coord : G.normalized G.r = (c - offset, K)
  vertex_coord : G.normalized G.vertex = (X, Y)
  base_le_d₁ : (2 * c) ^ 2 ≤ d₁
  d₁_radius : d₁ = c ^ 2 + H ^ 2
  classDifference : d₁ - d₂ = 4 * c * offset
  heightDrop_eq : heightDrop = H - K
  heightConstraint :
    2 * c * offset + offset ^ 2 = heightDrop * (H + (H - heightDrop))

private theorem fullTwoRungCanonicalFrame_exists
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃) :
    Nonempty (FullTwoRungCanonicalFrame G) := by
  let N := G.normalized
  have hcenters : P G.e ≠ P G.t := G.pointsInjective.ne G.e_ne_t
  let scale := Real.sqrt (sqDist (P G.e) (P G.t))
  have hscale : 0 < scale := normalizeAlong_scale_pos hcenters
  let c := scale / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hscaleEq : scale = 2 * c := by dsimp [c]; ring
  have he : N G.e = (0, 0) := by
    simpa only [N, FullTwoRungGeometry.normalized] using
      normalizeAlong_first_center hcenters
  have htScale : N G.t = (scale, 0) := by
    simpa only [N, FullTwoRungGeometry.normalized, scale] using
      normalizeAlong_second_center hcenters
  have ht : N G.t = (2 * c, 0) := by simpa only [hscaleEq] using htScale
  have hesN : sqDist (N G.e) (N G.s) = d₁ := by
    simpa only [N, FullTwoRungGeometry.normalized,
      normalizeAlong_sqDist hcenters] using G.es
  have htsN : sqDist (N G.t) (N G.s) = d₁ := by
    simpa only [N, FullTwoRungGeometry.normalized,
      normalizeAlong_sqDist hcenters] using G.ts
  let H := (N G.s).2
  have hsFirst : (N G.s).1 = c := by
    rw [he] at hesN
    rw [ht] at htsN
    simp only [sqDist] at hesN htsN
    nlinarith
  have hs : N G.s = (c, H) := Prod.ext hsFirst rfl
  have hH : 0 < H := by
    have hsecond := normalizeAlong_second_coordinate hcenters (P G.s)
    change (N G.s).2 = _ at hsecond
    change 0 < (N G.s).2
    rw [hsecond]
    exact div_pos G.tipAbove hscale
  let X := (N G.vertex).1
  let Y := (N G.vertex).2
  have hv : N G.vertex = (X, Y) := rfl
  have hY : Y < 0 := by
    have hsecond := normalizeAlong_second_coordinate hcenters (P G.vertex)
    change (N G.vertex).2 = _ at hsecond
    dsimp [Y]
    rw [hsecond]
    exact div_neg_of_neg_of_pos G.vertexBelow hscale
  let W := (N G.w).1
  let K_w := (N G.w).2
  let R := (N G.r).1
  let K_r := (N G.r).2
  have hKw : 0 < K_w := by
    have hsecond := normalizeAlong_second_coordinate hcenters (P G.w)
    change (N G.w).2 = _ at hsecond
    dsimp [K_w]
    rw [hsecond]
    exact div_pos G.wAbove hscale
  have hKr : 0 < K_r := by
    have hsecond := normalizeAlong_second_coordinate hcenters (P G.r)
    change (N G.r).2 = _ at hsecond
    dsimp [K_r]
    rw [hsecond]
    exact div_pos G.rAbove hscale
  have hewN : sqDist (N G.e) (N G.w) = d₁ := by
    simpa only [N, FullTwoRungGeometry.normalized,
      normalizeAlong_sqDist hcenters] using G.ew
  have htwN : sqDist (N G.t) (N G.w) = d₂ := by
    simpa only [N, FullTwoRungGeometry.normalized,
      normalizeAlong_sqDist hcenters] using G.tw
  have herN : sqDist (N G.e) (N G.r) = d₂ := by
    simpa only [N, FullTwoRungGeometry.normalized,
      normalizeAlong_sqDist hcenters] using G.er
  have htrN : sqDist (N G.t) (N G.r) = d₁ := by
    simpa only [N, FullTwoRungGeometry.normalized,
      normalizeAlong_sqDist hcenters] using G.tr
  have hwA : W ^ 2 + K_w ^ 2 = d₁ := by
    rw [he] at hewN
    simpa [sqDist, W, K_w] using hewN
  have hwB : (W - 2 * c) ^ 2 + K_w ^ 2 = d₂ := by
    rw [ht] at htwN
    simpa [sqDist, W, K_w] using htwN
  have hrB : R ^ 2 + K_r ^ 2 = d₂ := by
    rw [he] at herN
    simpa [sqDist, R, K_r] using herN
  have hrA : (R - 2 * c) ^ 2 + K_r ^ 2 = d₁ := by
    rw [ht] at htrN
    simpa [sqDist, R, K_r] using htrN
  obtain ⟨offset, K, hoffset, hW, hR, hKwEq, hKrEq, hclass⟩ :=
    forced_penultimate_coordinates hc G.classes.2.1 hwA hwB hrB hrA hKw hKr
  have hw : N G.w = (c + offset, K) := by
    apply Prod.ext
    · exact hW
    · exact hKwEq
  have hr : N G.r = (c - offset, K) := by
    apply Prod.ext
    · exact hR
    · exact hKrEq
  have hKltH : K < H := by
    have hsecondW := normalizeAlong_second_coordinate hcenters (P G.w)
    have hsecondS := normalizeAlong_second_coordinate hcenters (P G.s)
    change (N G.w).2 = _ at hsecondW
    change (N G.s).2 = _ at hsecondS
    have hnormalized : (N G.w).2 < (N G.s).2 := by
      rw [hsecondW, hsecondS]
      exact (div_lt_div_iff_of_pos_right hscale).2 G.wBelowTip
    rw [hw, hs] at hnormalized
    exact hnormalized
  let heightDrop := H - K
  have hheightDrop : 0 < heightDrop := sub_pos.mpr hKltH
  have hd₁Radius : d₁ = c ^ 2 + H ^ 2 := by
    rw [he, hs] at hesN
    simpa [sqDist] using hesN.symm
  have hbaseLeRaw := top_three_first_bound_local G.classes G.e G.t
  have hscaleSq := Real.sq_sqrt (sqDist_nonneg (P G.e) (P G.t))
  have hbaseLe : (2 * c) ^ 2 ≤ d₁ := by
    rw [← hscaleEq]
    dsimp [scale]
    rw [hscaleSq]
    exact hbaseLeRaw
  have hradius : (c + offset) ^ 2 + K ^ 2 = c ^ 2 + H ^ 2 := by
    rw [hw] at hewN
    rw [he] at hewN
    simp only [sqDist] at hewN
    nlinarith [hd₁Radius]
  have hconstraint :
      2 * c * offset + offset ^ 2 =
        heightDrop * (H + (H - heightDrop)) := by
    apply forced_penultimate_height_constraint_reparam
    dsimp [heightDrop]
    convert hradius using 1
    all_goals ring
  exact ⟨{
    scale := scale
    c := c
    H := H
    offset := offset
    K := K
    heightDrop := heightDrop
    X := X
    Y := Y
    scale_pos := hscale
    c_pos := hc
    H_pos := hH
    offset_pos := hoffset
    K_pos := hKwEq ▸ hKw
    heightDrop_pos := hheightDrop
    Y_neg := hY
    scale_eq := hscaleEq
    e_coord := he
    t_coord := ht
    s_coord := hs
    w_coord := hw
    r_coord := hr
    vertex_coord := hv
    base_le_d₁ := hbaseLe
    d₁_radius := hd₁Radius
    classDifference := hclass
    heightDrop_eq := rfl
    heightConstraint := hconstraint }⟩

private theorem fullTwoRung_tip_unique_farthest
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃) :
    ∀ j, j ≠ G.s →
      sqDist (P G.vertex) (P j) < sqDist (P G.vertex) (P G.s) :=
  shared_tip_unique_farthest G.pointsInjective G.classes G.e_ne_t
    G.es G.ts G.tipAbove G.vertexBelow

private theorem fullTwoRung_diameter_branch_impossible
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃) :
    sqDist (P G.vertex) (P G.s) ≠ d₁ := by
  intro hVs
  have hVwBounds := top_three_radius_bounds_of_ne G.classes G.vertex_ne_w
  dsimp only at hVwBounds
  have hfarSq := fullTwoRung_tip_unique_farthest G G.w G.w_ne_s
  have hfar : euclideanDist (P G.vertex) (P G.w) <
      euclideanDist (P G.vertex) (P G.s) := by
    rw [euclideanDist_eq_sqrt_sqDist, euclideanDist_eq_sqrt_sqDist]
    exact Real.sqrt_lt_sqrt (sqDist_nonneg _ _) hfarSq
  have hED := edge_diagonal_inequality G.antiSaturationQuad
  rw [euclideanDist_eq_sqrt_of_sqDist_eq G.tw,
    euclideanDist_comm_local (P G.s) (P G.vertex),
    euclideanDist_eq_sqrt_of_sqDist_eq hVs,
    euclideanDist_eq_sqrt_of_sqDist_eq G.ts,
    euclideanDist_comm_local (P G.w) (P G.vertex)] at hED
  have hVsRadius := euclideanDist_eq_sqrt_of_sqDist_eq hVs
  have hnot := one_penultimate_anti_saturation
    ⟨hVwBounds.1, hVwBounds.2.1⟩ hfar (by linarith [hED, hVsRadius])
  exact hnot (euclideanDist_eq_sqrt_of_sqDist_eq hVs)

private theorem fullTwoRung_low_degree_le_one
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) ≤ d₃) :
    vertexDegree P d₁ d₂ d₃ G.vertex ≤ 1 := by
  classical
  unfold vertexDegree
  apply (Finset.card_le_card (t := {G.s}) ?_).trans
  · simp
  intro j hj
  have hjData := Finset.mem_filter.mp hj
  by_cases hjs : j = G.s
  · simp [hjs]
  have hfar := fullTwoRung_tip_unique_farthest G j hjs
  have hlt : sqDist (P G.vertex) (P j) < d₃ := hfar.trans_le hVs
  rcases hjData.2 with hj | hj | hj <;> linarith [G.classes.1, G.classes.2.1]

private theorem fullTwoRung_arc_neighbor_classes
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂)
    (hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃)
    {center j : Fin n} (hcenterj : center ≠ j) (hjs : j ≠ G.s)
    (hneighbor : sqDist (P G.vertex) (P j) = d₁ ∨
      sqDist (P G.vertex) (P j) = d₂ ∨
        sqDist (P G.vertex) (P j) = d₃)
    (hED : euclideanDist (P G.vertex) (P j) + Real.sqrt d₁ <
      Real.sqrt d₂ + euclideanDist (P center) (P j)) :
    sqDist (P G.vertex) (P j) = d₃ ∧ sqDist (P center) (P j) = d₁ := by
  have hfar := fullTwoRung_tip_unique_farthest G j hjs
  have hlt₂ : sqDist (P G.vertex) (P j) < d₂ := by
    rw [hVs] at hfar
    exact hfar
  have hVj : sqDist (P G.vertex) (P j) = d₃ := by
    rcases hneighbor with h₁ | h₂ | h₃
    · linarith [G.classes.2.1]
    · linarith
    · exact h₃
  have hED' := hED
  rw [euclideanDist_eq_sqrt_of_sqDist_eq hVj] at hED'
  have hcenterFar : Real.sqrt d₂ < euclideanDist (P center) (P j) := by
    linarith
  exact ⟨hVj, sqDist_eq_d₁_of_sqrt_d₂_lt G.classes hcenterj hcenterFar⟩

private theorem fullTwoRung_arc_card_le_one
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂)
    (hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃)
    {arc : Finset (Fin n)} {center : Fin n}
    (hcenterVertex : center ≠ G.vertex)
    (hcenterArc : ∀ j ∈ arc, center ≠ j)
    (hneTip : ∀ j ∈ arc, j ≠ G.s)
    (hED : ∀ j ∈ arc,
      euclideanDist (P G.vertex) (P j) + Real.sqrt d₁ <
        Real.sqrt d₂ + euclideanDist (P center) (P j))
    (hside :
      (∀ j ∈ arc, InLeftOpenHalfPlane (P center) (P G.vertex) (P j)) ∨
      (∀ j ∈ arc, InLeftOpenHalfPlane (P G.vertex) (P center) (P j))) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex arc).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  have hpData := Finset.mem_filter.mp hp
  have hqData := Finset.mem_filter.mp hq
  have hpClasses := fullTwoRung_arc_neighbor_classes G hVs hlong
    (hcenterArc p hpData.1) (hneTip p hpData.1) hpData.2.2
    (hED p hpData.1)
  have hqClasses := fullTwoRung_arc_neighbor_classes G hVs hlong
    (hcenterArc q hqData.1) (hneTip q hqData.1) hqData.2.2
    (hED q hqData.1)
  apply G.pointsInjective
  rcases hside with hforward | hreverse
  · apply same_half_plane_two_circle_unique
      (G.pointsInjective.ne hcenterVertex)
    · exact hpClasses.2.trans hqClasses.2.symm
    · exact hpClasses.1.trans hqClasses.1.symm
    · exact hforward p hpData.1
    · exact hforward q hqData.1
  · apply same_half_plane_two_circle_unique
      (G.pointsInjective.ne hcenterVertex.symm)
    · exact hpClasses.1.trans hqClasses.1.symm
    · exact hpClasses.2.trans hqClasses.2.symm
    · exact hreverse p hpData.1
    · exact hreverse q hqData.1

private theorem fullTwoRung_ePositive_card_le_one
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂)
    (hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.ePositiveArc).card ≤ 1 := by
  apply fullTwoRung_arc_card_le_one G hVs hlong G.vertex_ne_e.symm
    G.ePositive_center_ne G.ePositive_ne_tip
  · intro j hj
    have hED := edge_diagonal_inequality (G.ePositiveQuad j hj)
    rw [euclideanDist_comm_local (P G.s) (P G.e),
      euclideanDist_eq_sqrt_of_sqDist_eq G.es,
      euclideanDist_eq_sqrt_of_sqDist_eq hVs,
      euclideanDist_comm_local (P j) (P G.e)] at hED
    linarith
  · exact Or.inl G.ePositiveHalfPlane

private theorem fullTwoRung_eNegative_card_le_one
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂)
    (hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.eNegativeArc).card ≤ 1 := by
  apply fullTwoRung_arc_card_le_one G hVs hlong G.vertex_ne_e.symm
    G.eNegative_center_ne G.eNegative_ne_tip
  · intro j hj
    have hED := edge_diagonal_inequality (G.eNegativeQuad j hj)
    rw [euclideanDist_comm_local (P G.s) (P G.e),
      euclideanDist_eq_sqrt_of_sqDist_eq G.es,
      euclideanDist_eq_sqrt_of_sqDist_eq hVs,
      euclideanDist_comm_local (P j) (P G.e)] at hED
    linarith
  · exact Or.inr G.eNegativeHalfPlane

private theorem fullTwoRung_tPositive_card_le_one
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂)
    (hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.tPositiveArc).card ≤ 1 := by
  apply fullTwoRung_arc_card_le_one G hVs hlong G.vertex_ne_t.symm
    G.tPositive_center_ne G.tPositive_ne_tip
  · intro j hj
    have hED := edge_diagonal_inequality (G.tPositiveQuad j hj)
    rw [euclideanDist_eq_sqrt_of_sqDist_eq G.ts,
      euclideanDist_comm_local (P j) (P G.vertex),
      euclideanDist_comm_local (P G.s) (P G.vertex),
      euclideanDist_eq_sqrt_of_sqDist_eq hVs] at hED
    linarith
  · exact Or.inl G.tPositiveHalfPlane

private theorem fullTwoRung_tNegative_card_le_one
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂)
    (hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃) :
    (arcNeighbors P d₁ d₂ d₃ G.vertex G.tNegativeArc).card ≤ 1 := by
  apply fullTwoRung_arc_card_le_one G hVs hlong G.vertex_ne_t.symm
    G.tNegative_center_ne G.tNegative_ne_tip
  · intro j hj
    have hED := edge_diagonal_inequality (G.tNegativeQuad j hj)
    rw [euclideanDist_eq_sqrt_of_sqDist_eq G.ts,
      euclideanDist_comm_local (P j) (P G.vertex),
      euclideanDist_comm_local (P G.s) (P G.vertex),
      euclideanDist_eq_sqrt_of_sqDist_eq hVs] at hED
    linarith
  · exact Or.inr G.tNegativeHalfPlane

private theorem fullTwoRung_degree_le_six_of_arc_bounds
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (hePositive :
      (arcNeighbors P d₁ d₂ d₃ G.vertex G.ePositiveArc).card ≤ 1)
    (heNegative :
      (arcNeighbors P d₁ d₂ d₃ G.vertex G.eNegativeArc).card ≤ 1)
    (htPositive :
      (arcNeighbors P d₁ d₂ d₃ G.vertex G.tPositiveArc).card ≤ 1)
    (htNegative :
      (arcNeighbors P d₁ d₂ d₃ G.vertex G.tNegativeArc).card ≤ 1) :
    vertexDegree P d₁ d₂ d₃ G.vertex ≤ 6 := by
  classical
  let N := (Finset.univ.erase G.vertex).filter fun j ↦
    sqDist (P G.vertex) (P j) = d₁ ∨ sqDist (P G.vertex) (P j) = d₂ ∨
      sqDist (P G.vertex) (P j) = d₃
  let A₁ := arcNeighbors P d₁ d₂ d₃ G.vertex G.ePositiveArc
  let A₂ := arcNeighbors P d₁ d₂ d₃ G.vertex G.eNegativeArc
  let A₃ := arcNeighbors P d₁ d₂ d₃ G.vertex G.tPositiveArc
  let A₄ := arcNeighbors P d₁ d₂ d₃ G.vertex G.tNegativeArc
  let C := (((A₁ ∪ A₂) ∪ A₃) ∪ A₄) ∪ {G.s, G.endpoint}
  have hsubset : N ⊆ C := by
    intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjne := (Finset.mem_erase.mp hjData.1).1
    rcases G.arcPartition j hjne with h₁ | h₂ | h₃ | h₄ | htip | hendpoint
    · simp [C, A₁, A₂, A₃, A₄, arcNeighbors, h₁, hjne, hjData.2]
    · simp [C, A₁, A₂, A₃, A₄, arcNeighbors, h₂, hjne, hjData.2]
    · simp [C, A₁, A₂, A₃, A₄, arcNeighbors, h₃, hjne, hjData.2]
    · simp [C, A₁, A₂, A₃, A₄, arcNeighbors, h₄, hjne, hjData.2]
    · simp [C, htip]
    · simp [C, hendpoint]
  have hN : N.card ≤ C.card := Finset.card_le_card hsubset
  have h12 : (A₁ ∪ A₂).card ≤ A₁.card + A₂.card := Finset.card_union_le _ _
  have h123 : ((A₁ ∪ A₂) ∪ A₃).card ≤ (A₁ ∪ A₂).card + A₃.card :=
    Finset.card_union_le _ _
  have h1234 : (((A₁ ∪ A₂) ∪ A₃) ∪ A₄).card ≤
      ((A₁ ∪ A₂) ∪ A₃).card + A₄.card := Finset.card_union_le _ _
  have hC : C.card ≤ (((A₁ ∪ A₂) ∪ A₃) ∪ A₄).card +
      ({G.s, G.endpoint} : Finset (Fin n)).card := Finset.card_union_le _ _
  have hspecial : ({G.s, G.endpoint} : Finset (Fin n)).card ≤ 2 :=
    Finset.card_le_two
  change N.card ≤ 6
  change A₁.card ≤ 1 at hePositive
  change A₂.card ≤ 1 at heNegative
  change A₃.card ≤ 1 at htPositive
  change A₄.card ≤ 1 at htNegative
  omega

private theorem fullTwoRung_second_class_long_degree_le_six
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂)
    (hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃) :
    vertexDegree P d₁ d₂ d₃ G.vertex ≤ 6 := by
  apply fullTwoRung_degree_le_six_of_arc_bounds G
  · exact fullTwoRung_ePositive_card_le_one G hVs hlong
  · exact fullTwoRung_eNegative_card_le_one G hVs hlong
  · exact fullTwoRung_tPositive_card_le_one G hVs hlong
  · exact fullTwoRung_tNegative_card_le_one G hVs hlong

private theorem fullTwoRung_metric_split
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (F : FullTwoRungCanonicalFrame G) :
    2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃ ∨
      d₁ + 2 * d₃ - 3 * d₂ <
        4 * F.heightDrop * (F.H - Real.sqrt d₂) := by
  have hd₁ : 0 < d₁ := by
    rw [← G.es]
    exact sqDist_pos_of_ne (G.pointsInjective.ne G.e_ne_s)
  have hd₃ : 0 < d₃ := top_three_third_value_pos G.pointsInjective G.classes
  have hd₂ : 0 < d₂ := hd₃.trans G.classes.1
  let D := Real.sqrt d₁
  have hD : 0 < D := Real.sqrt_pos.2 hd₁
  have hDsq : D ^ 2 = d₁ := Real.sq_sqrt hd₁.le
  let normalizedC := F.c / D
  let normalizedOffset := F.offset / D
  let beta := Real.sqrt d₂ / D
  let gamma := Real.sqrt d₃ / D
  let normalizedH := F.H / D
  let normalizedK := F.K / D
  let normalizedDrop := F.heightDrop / D
  have hC : 0 < normalizedC := div_pos F.c_pos hD
  have hbaseLength : 2 * F.c ≤ D := by
    by_contra hnot
    have hlt : D < 2 * F.c := lt_of_not_ge hnot
    have hsum : 0 < 2 * F.c + D := by linarith [F.c_pos, hD]
    have hproduct : 0 < (2 * F.c - D) * (2 * F.c + D) :=
      mul_pos (sub_pos.mpr hlt) hsum
    nlinarith [F.base_le_d₁, hDsq]
  have hChi : normalizedC ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ hD]
    linarith
  have hOffset : 0 < normalizedOffset := div_pos F.offset_pos hD
  have hBetaSq : beta ^ 2 = 1 - 4 * normalizedC * normalizedOffset := by
    have hd₂sq := Real.sq_sqrt hd₂.le
    dsimp [beta, normalizedC, normalizedOffset]
    field_simp [ne_of_gt hD]
    nlinarith [hDsq, hd₂sq, F.classDifference]
  have hGamma : 0 < gamma := div_pos (Real.sqrt_pos.2 hd₃) hD
  have hH : 0 < normalizedH := div_pos F.H_pos hD
  have hHSq : normalizedH ^ 2 = 1 - normalizedC ^ 2 := by
    dsimp [normalizedH, normalizedC]
    field_simp [ne_of_gt hD]
    nlinarith [hDsq, F.d₁_radius]
  have hK : 0 < normalizedK := div_pos F.K_pos hD
  have hKRadius : d₁ = (F.c + F.offset) ^ 2 + F.K ^ 2 := by
    have hconstraint := F.heightConstraint
    rw [F.heightDrop_eq] at hconstraint
    nlinarith [F.d₁_radius]
  have hKSq : normalizedK ^ 2 = 1 - (normalizedC + normalizedOffset) ^ 2 := by
    dsimp [normalizedK, normalizedC, normalizedOffset]
    field_simp [ne_of_gt hD]
    nlinarith [hDsq, hKRadius]
  have hDrop : 0 < normalizedDrop := div_pos F.heightDrop_pos hD
  have hDropDef : normalizedDrop = normalizedH - normalizedK := by
    dsimp [normalizedDrop, normalizedH, normalizedK]
    rw [F.heightDrop_eq]
    field_simp [ne_of_gt hD]
  rcases metric_sign_dichotomy hC hChi hOffset hBetaSq hGamma hH hHSq
      hK hKSq hDrop hDropDef with hlong | hshort
  · left
    have hscaled := mul_le_mul_of_nonneg_right hlong hD.le
    have hbetaD : beta * D = Real.sqrt d₂ := by
      dsimp [beta]
      field_simp [ne_of_gt hD]
    have hgammaD : gamma * D = Real.sqrt d₃ := by
      dsimp [gamma]
      field_simp [ne_of_gt hD]
    nlinarith
  · right
    have hcleared := (div_lt_iff₀ (by positivity : 0 < 4 * normalizedDrop)).mp hshort
    have hscaled := mul_lt_mul_of_pos_left hcleared (sq_pos_of_pos hD)
    have hbetaSqD : beta ^ 2 * D ^ 2 = d₂ := by
      have hd₂sq := Real.sq_sqrt hd₂.le
      dsimp [beta]
      field_simp [ne_of_gt hD]
      nlinarith
    have hgammaSqD : gamma ^ 2 * D ^ 2 = d₃ := by
      have hd₃sq := Real.sq_sqrt hd₃.le
      dsimp [gamma]
      field_simp [ne_of_gt hD]
      nlinarith
    have hdropD : normalizedDrop * D = F.heightDrop := by
      dsimp [normalizedDrop]
      field_simp [ne_of_gt hD]
    have hHD : normalizedH * D = F.H := by
      dsimp [normalizedH]
      field_simp [ne_of_gt hD]
    have hbetaD : beta * D = Real.sqrt d₂ := by
      dsimp [beta]
      field_simp [ne_of_gt hD]
    have hleft : D ^ 2 * (1 + 2 * gamma ^ 2 - 3 * beta ^ 2) =
        d₁ + 2 * d₃ - 3 * d₂ := by
      calc
        _ = D ^ 2 + 2 * (gamma ^ 2 * D ^ 2) -
            3 * (beta ^ 2 * D ^ 2) := by ring
        _ = _ := by rw [hgammaSqD, hbetaSqD, hDsq]
    have hheightD : (normalizedH - beta) * D = F.H - Real.sqrt d₂ := by
      calc
        _ = normalizedH * D - beta * D := by ring
        _ = _ := by rw [hHD, hbetaD]
    have hright : D ^ 2 * ((normalizedH - beta) * (4 * normalizedDrop)) =
        4 * F.heightDrop * (F.H - Real.sqrt d₂) := by
      calc
        _ = 4 * (normalizedDrop * D) * ((normalizedH - beta) * D) := by ring
        _ = _ := by rw [hdropD, hheightD]
    calc
      d₁ + 2 * d₃ - 3 * d₂ =
          D ^ 2 * (1 + 2 * gamma ^ 2 - 3 * beta ^ 2) := hleft.symm
      _ < D ^ 2 * ((normalizedH - beta) * (4 * normalizedDrop)) := hscaled
      _ = 4 * F.heightDrop * (F.H - Real.sqrt d₂) := hright

private theorem fullTwoRung_second_class_short_impossible
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (F : FullTwoRungCanonicalFrame G)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂)
    (hshort : d₁ + 2 * d₃ - 3 * d₂ <
      4 * F.heightDrop * (F.H - Real.sqrt d₂)) : False := by
  have hfarW := fullTwoRung_tip_unique_farthest G G.w G.w_ne_s
  have hfarR := fullTwoRung_tip_unique_farthest G G.r G.r_ne_s
  have hVwLt : sqDist (P G.vertex) (P G.w) < d₂ := by
    rw [hVs] at hfarW
    exact hfarW
  have hVrLt : sqDist (P G.vertex) (P G.r) < d₂ := by
    rw [hVs] at hfarR
    exact hfarR
  have hVwLe : sqDist (P G.vertex) (P G.w) ≤ d₃ :=
    (top_three_class_bounds_of_ne G.classes G.vertex_ne_w).2.2 hVwLt
  have hVrLe : sqDist (P G.vertex) (P G.r) ≤ d₃ :=
    (top_three_class_bounds_of_ne G.classes G.vertex_ne_r).2.2 hVrLt
  have hclassNeg : d₂ - d₁ = -4 * F.c * F.offset := by
    linarith [F.classDifference]
  have hsum := two_rung_sum_identity_with_classes
    (c := F.c) (d := F.offset) (H := F.H) (Δ := F.heightDrop)
    (X := F.X) (Y := F.Y) (A := d₁) (B := d₂)
    F.heightConstraint hclassNeg
  have hK : F.H - F.heightDrop = F.K := by
    rw [F.heightDrop_eq]
    ring
  rw [hK, ← F.vertex_coord, ← F.w_coord, ← F.r_coord, ← F.s_coord] at hsum
  let N := G.normalized
  have hcenters : P G.e ≠ P G.t := G.pointsInjective.ne G.e_ne_t
  have hsumRaw :
      sqDist (P G.vertex) (P G.w) + sqDist (P G.vertex) (P G.r) -
          2 * sqDist (P G.vertex) (P G.s) =
        d₂ - d₁ + 4 * F.heightDrop * F.Y := by
    simpa only [N, FullTwoRungGeometry.normalized,
      normalizeAlong_sqDist hcenters] using hsum
  have hYUpper : 4 * F.heightDrop * F.Y ≤ d₁ + 2 * d₃ - 3 * d₂ := by
    nlinarith
  have hY : F.Y < F.H - Real.sqrt d₂ := by
    nlinarith [F.heightDrop_pos]
  have hVsN : sqDist (N G.vertex) (N G.s) = d₂ := by
    simpa only [N, FullTwoRungGeometry.normalized,
      normalizeAlong_sqDist hcenters] using hVs
  dsimp only [N] at hVsN
  rw [F.vertex_coord, F.s_coord] at hVsN
  have hd₂ : 0 ≤ d₂ := (top_three_values_nonnegative G.classes).2.1
  have hsqrtSq := Real.sq_sqrt hd₂
  have hsqrtNonneg := Real.sqrt_nonneg d₂
  simp only [sqDist] at hVsN
  nlinarith [sq_nonneg (F.c - F.X)]

private theorem fullTwoRung_second_class_degree_le_six
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃)
    (hVs : sqDist (P G.vertex) (P G.s) = d₂) :
    vertexDegree P d₁ d₂ d₃ G.vertex ≤ 6 := by
  obtain ⟨F⟩ := fullTwoRungCanonicalFrame_exists G
  rcases fullTwoRung_metric_split G F with hlong | hshort
  · exact fullTwoRung_second_class_long_degree_le_six G hVs hlong
  · exact (fullTwoRung_second_class_short_impossible G F hVs hshort).elim

/-- The full two-rung insertion theorem derived from raw polygon geometry. -/
theorem fullTwoRung_realization_degree_le_six
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : FullTwoRungGeometry P d₁ d₂ d₃) :
    vertexDegree P d₁ d₂ d₃ G.vertex ≤ 6 := by
  have hVsBounds := top_three_class_bounds_of_ne G.classes G.vertex_ne_s
  rcases top_three_value_split hVsBounds with hVs | hVs | hVs
  · exact (fullTwoRung_diameter_branch_impossible G hVs).elim
  · exact fullTwoRung_second_class_degree_le_six G hVs
  · exact (fullTwoRung_low_degree_le_one G hVs).trans (by omega)

end LeanPool.Erdos132ConvexK3
