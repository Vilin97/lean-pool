/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import LeanPool.ACMax.Spectral.AlgConn
import LeanPool.ACMax.Spectral.RayleighUpper
import LeanPool.ACMax.Spectral.TestVector

/-!
# Two-vertex-cut certificate (Fiedler's `κ ≤ 2` bound)

If deleting two vertices `a ≠ b` disconnects the graph into two nonempty parts
`A` and `B` (no `A`–`B` edges), then `algConn G ≤ 2`, unconditionally.

Test vector: `x = |B|·𝟙_A − |A|·𝟙_B` (zero on `{a, b}`).  Then `∑ x = 0`,
`x ≠ 0`, and the key pointwise estimate is that every ordered adjacent pair
contributes `(x i − x j)² ≤ (x i)²·c j + c i·(x j)²` where `c` is the indicator
of the cut `{a, b}`: within `A` or within `B` the difference vanishes, `A`–`B`
edges are excluded by the separation hypothesis, and an edge into the cut
contributes exactly `|B|²` (from the `A` side) or `|A|²` (from the `B` side) —
which is precisely `(x·)²` at the non-cut endpoint.  Summing, the ordered
quadratic form is at most `2 · (∑ c) · (∑ x²) = 4 ∑ x²`, hence
`xᵀ L x ≤ 2 ∑ x²` and the universal test-vector certificate applies.
-/

namespace ACMax

open Matrix

open Classical in
/-- **Two-vertex-cut certificate**, general vertex type.  If `{a, b}` separates
the nonempty sets `A` and `B` (which together with `a, b` cover all vertices,
are disjoint, and have no edges between them), then `algConn G ≤ 2`. -/
theorem algConn_le_two_of_two_vertex_cut_general {V : Type*} [Fintype V]
    [Nonempty V] (G : SimpleGraph V) (a b : V) (hab : a ≠ b)
    (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty)
    (hdisj : Disjoint A B) (haA : a ∉ A) (haB : a ∉ B)
    (hbA : b ∉ A) (hbB : b ∉ B)
    (hcover : ∀ v : V, v ∈ A ∨ v ∈ B ∨ v = a ∨ v = b)
    (hsep : ∀ u ∈ A, ∀ v ∈ B, ¬G.Adj u v) :
    algConn G ≤ 2 := by
  classical
  set α : ℝ := (A.card : ℝ) with hαdef
  set β : ℝ := (B.card : ℝ) with hβdef
  have hβpos : 0 < β := by
    rw [hβdef]; exact_mod_cast Finset.card_pos.mpr hB
  -- The test vector.
  set x : V → ℝ := fun v => if v ∈ A then β else if v ∈ B then -α else 0
    with hxdef
  -- The indicator of the two-vertex cut `{a, b}`.
  set c : V → ℝ := fun v => if v ∈ A ∪ B then 0 else 1 with hcdef
  -- Pointwise values of `x` and `c` on the three vertex classes.
  have hxA : ∀ v ∈ A, x v = β := by
    intro v hv; simp only [hxdef]; rw [ite_eq_left hv]
  have hxB : ∀ v ∈ B, x v = -α := by
    intro v hv
    have hvA : v ∉ A := Finset.disjoint_right.mp hdisj hv
    simp only [hxdef]; rw [ite_eq_right hvA, ite_eq_left hv]
  have hxOut : ∀ v, v ∉ A ∪ B → x v = 0 := by
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    simp only [hxdef]; rw [ite_eq_right hv.1, ite_eq_right hv.2]
  have hcIn : ∀ v, v ∈ A ∪ B → c v = 0 := by
    intro v hv; simp only [hcdef]; rw [ite_eq_left hv]
  have hcOut : ∀ v, v ∉ A ∪ B → c v = 1 := by
    intro v hv; simp only [hcdef]; rw [ite_eq_right hv]
  have hcnn : ∀ v, 0 ≤ c v := by
    intro v; simp only [hcdef]; split <;> norm_num
  -- Class trichotomy (a tautology; `hcover` is only used to *count* the cut).
  have tri : ∀ v : V, v ∈ A ∨ v ∈ B ∨ v ∉ A ∪ B := by
    intro v
    by_cases h1 : v ∈ A
    · exact Or.inl h1
    by_cases h2 : v ∈ B
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (by rw [Finset.mem_union, not_or]; exact ⟨h1, h2⟩))
  -- Obligation 1: `x` sums to zero.
  have hsum0 : ∑ i, x i = 0 := by
    have hxval : ∀ v, x v =
        β * (if v ∈ A then 1 else 0) - α * (if v ∈ B then 1 else 0) := by
      intro v
      rcases tri v with hv | hv | hv
      · have hvB : v ∉ B := Finset.disjoint_left.mp hdisj hv
        rw [hxA v hv, ite_eq_left hv, ite_eq_right hvB]; ring
      · have hvA : v ∉ A := Finset.disjoint_right.mp hdisj hv
        rw [hxB v hv, ite_eq_right hvA, ite_eq_left hv]; ring
      · rw [Finset.mem_union, not_or] at hv
        rw [hxOut v (by rw [Finset.mem_union, not_or]; exact hv),
          ite_eq_right hv.1, ite_eq_right hv.2]
        ring
    simp_rw [hxval, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
      Finset.filter_univ_mem]
    rw [← hαdef, ← hβdef]
    ring
  -- Obligation 2: `x` is nonzero (any vertex of `A` witnesses this).
  have hne : ∃ i, x i ≠ 0 := by
    obtain ⟨u, hu⟩ := hA
    exact ⟨u, by rw [hxA u hu]; exact ne_of_gt hβpos⟩
  -- The cut has exactly two vertices, so the indicator sums to `2`.
  have hfilter : Finset.univ.filter (fun v => v ∉ A ∪ B) = {a, b} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hv
      rcases hcover v with h | h | h | h
      · exact absurd (Finset.mem_union_left B h) hv
      · exact absurd (Finset.mem_union_right A h) hv
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · rw [Finset.mem_union, not_or]; exact ⟨haA, haB⟩
      · rw [Finset.mem_union, not_or]; exact ⟨hbA, hbB⟩
  have hSC : ∑ v, c v = 2 := by
    have hcval : ∀ v, c v = if v ∉ A ∪ B then (1 : ℝ) else 0 := by
      intro v
      by_cases h : v ∈ A ∪ B
      · rw [hcIn v h, ite_eq_right (not_not_intro h)]
      · rw [hcOut v h, ite_eq_left h]
    simp_rw [hcval]
    rw [Finset.sum_boole, hfilter,
      Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
    norm_num
  -- Pointwise edge estimate: each ordered adjacent pair contributes at most
  -- `(x i)² c j + c i (x j)²`.
  have hpt : ∀ i j, (if G.Adj i j then (x i - x j) ^ 2 else 0) ≤
      (x i) ^ 2 * c j + c i * (x j) ^ 2 := by
    intro i j
    have hgnn : 0 ≤ (x i) ^ 2 * c j + c i * (x j) ^ 2 :=
      add_nonneg (mul_nonneg (sq_nonneg _) (hcnn j))
        (mul_nonneg (hcnn i) (sq_nonneg _))
    by_cases hadj : G.Adj i j
    · rw [ite_eq_left hadj]
      rcases tri i with hi | hi | hi <;> rcases tri j with hj | hj | hj
      · -- A–A : difference vanishes
        rw [hxA i hi, hxA j hj]
        nlinarith [mul_nonneg (sq_nonneg β) (hcnn j),
          mul_nonneg (hcnn i) (sq_nonneg β)]
      · -- A–B : excluded by separation
        exact absurd hadj (hsep i hi j hj)
      · -- A–cut : contributes exactly `β² = (x i)²`
        rw [hxA i hi, hxOut j hj, hcOut j hj, hcIn i (Finset.mem_union_left B hi)]
        ring_nf
        nlinarith [sq_nonneg β]
      · -- B–A : excluded by separation
        exact absurd hadj.symm (hsep j hj i hi)
      · -- B–B : difference vanishes
        rw [hxB i hi, hxB j hj]
        nlinarith [mul_nonneg (sq_nonneg (-α)) (hcnn j),
          mul_nonneg (hcnn i) (sq_nonneg (-α))]
      · -- B–cut : contributes exactly `α² = (x i)²`
        rw [hxB i hi, hxOut j hj, hcOut j hj, hcIn i (Finset.mem_union_right A hi)]
        ring_nf
        nlinarith [sq_nonneg α]
      · -- cut–A
        rw [hxOut i hi, hxA j hj, hcOut i hi, hcIn j (Finset.mem_union_left B hj)]
        ring_nf
        nlinarith [sq_nonneg β]
      · -- cut–B
        rw [hxOut i hi, hxB j hj, hcOut i hi, hcIn j (Finset.mem_union_right A hj)]
        ring_nf
        nlinarith [sq_nonneg α]
      · -- cut–cut : both coordinates vanish
        rw [hxOut i hi, hxOut j hj]
        nlinarith [mul_nonneg (sq_nonneg (0 : ℝ)) (hcnn j),
          mul_nonneg (hcnn i) (sq_nonneg (0 : ℝ))]
    · rw [ite_eq_right hadj]
      exact hgnn
  -- Assemble: the ordered quadratic form is at most `4 ∑ x²`.
  have hQ : (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0) ≤
      4 * ∑ i, (x i) ^ 2 := by
    have hstep : (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0) ≤
        ∑ i, ∑ j, ((x i) ^ 2 * c j + c i * (x j) ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    refine hstep.trans_eq ?_
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hSC]
    ring
  -- Conclude via the universal test-vector certificate.
  apply algConn_le_two_of_testvector G x hsum0 hne
  rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂']
  linarith [hQ]

open Classical in
/-- **Two-vertex-cut certificate** on `Fin n` (Fiedler's `κ ≤ 2` bound):
deleting the two vertices `a ≠ b` disconnects `G` into the nonempty parts
`A` and `B`, hence `algConn G ≤ 2`, unconditionally. -/
theorem algConn_le_two_of_two_vertex_cut {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (a b : Fin n) (hab : a ≠ b)
    (A B : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (hdisj : Disjoint A B) (haA : a ∉ A ∪ B) (hbB : b ∉ A ∪ B)
    (hcover : ∀ v : Fin n, v ∈ A ∨ v ∈ B ∨ v = a ∨ v = b)
    (hsep : ∀ u ∈ A, ∀ v ∈ B, ¬G.Adj u v) :
    algConn G ≤ 2 := by
  rw [Finset.mem_union, not_or] at haA hbB
  exact algConn_le_two_of_two_vertex_cut_general G a b hab A B hA hB hdisj
    haA.1 haA.2 hbB.1 hbB.2 hcover hsep

end ACMax
