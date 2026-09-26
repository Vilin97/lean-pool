/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.LengthTwoCross

/-!
# Exact torsion of two length-two midpoint marks

The exceptional high-genus all-submodular marking has torsion order two.  This
is independent of the number of other strands: each midpoint doubles to the
same endpoint pencil.
-/

@[expose] public section

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- `TorsionWitness` for an explicitly marked graph, with the structure
projections reduced away.  Rewriting with this before touching the witness
keeps every divisor typed at `CFDiv G` rather than at the defeq-but-distinct
`CFDiv (mark G u v).graph`; otherwise `simp` lemmas such as `one_zsmul` fail
to fire, because the `SMul` instance recorded in the term mentions
`(mark G u v).graph`. -/
theorem torsionWitness_mark_iff {G : CFGraph} (u v : G.V) (k : ℕ) :
    TorsionWitness (mark G u v) k ↔
      0 < k ∧ linearEquiv G ((k : ℤ) • (oneChip u - oneChip v)) 0 :=
  Iff.rfl

/-- Every combinatorial midpoint, not only the midpoint of a length-two
strand, doubles to the degree-two endpoint pencil.  This is the corrected
torsion input needed after the length-two cross-strand submodularity
exception: a length-two midpoint paired with the midpoint of an arbitrary
even-length strand still has torsion order two. -/
theorem two_smul_strand_midpoint_linearEquiv_endpoints
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (i : B.PathPosition α)
    (hi : 2 * i.val = B.length α) :
    linearEquiv B.graph ((2 : ℤ) • oneChip (strandVertex B α i))
      (oneChip (leftEndpoint B) + oneChip (rightEndpoint B)) := by
  have hmirror : strandMirror B α i = i := by
    apply Fin.ext
    simp only [strandMirror]
    omega
  have hreflection := endpoint_sum_linearEquiv_strand_reflection B α i
  rw [hmirror] at hreflection
  simpa [two_smul] using hreflection.symm

/-- Two distinct-strand midpoints have exact torsion order two.  No
length-two hypothesis is required for this torsion calculation. -/
theorem distinct_strand_midpoints_torsionOrder_two
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hαβ : α ≠ β) (hi : 2 * i.val = B.length α)
    (hj : 2 * j.val = B.length β) :
    IsTorsionOrder
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) 2 := by
  let u := strandVertex B α i
  let v := strandVertex B β j
  have hiInt : B.IsInteriorPosition α i := by
    change 0 < i.val ∧ i.val < B.length α
    have hlen := B.length_pos α
    omega
  have hjInt : B.IsInteriorPosition β j := by
    change 0 < j.val ∧ j.val < B.length β
    have hlen := B.length_pos β
    omega
  have huv : u ≠ v := by
    intro huvEq
    exact hαβ (strand_eq_of_interior_vertex_eq B α β i j
      hiInt hjInt (by simpa [u, v] using huvEq))
  have hU := two_smul_strand_midpoint_linearEquiv_endpoints B α i hi
  have hV := two_smul_strand_midpoint_linearEquiv_endpoints B β j hj
  have hUV : linearEquiv B.graph
      ((2 : ℤ) • oneChip u) ((2 : ℤ) • oneChip v) := by
    simpa [u, v] using hU.trans hV.symm
  have hDiff : linearEquiv B.graph
      ((2 : ℤ) • (oneChip u - oneChip v)) 0 := by
    unfold linearEquiv at hUV ⊢
    have heq : (0 : CFDiv B.graph) -
          (2 : ℤ) • (oneChip u - oneChip v) =
        (2 : ℤ) • oneChip v - (2 : ℤ) • oneChip u := by
      simp [smul_sub]
    rw [heq]
    exact hUV
  have hg1 : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with hg0 | hg1
    · exact absurd (Fin.ext (by
        have := α.isLt
        have := β.isLt
        omega)) hαβ
    · exact hg1
  refine ⟨⟨by omega, hDiff⟩, ?_⟩
  intro m hm
  rw [torsionWitness_mark_iff] at hm
  by_cases hm1 : m = 1
  · subst m
    have hOne := hm.2
    rw [Nat.cast_one, one_zsmul] at hOne
    exact ((marks_not_linearEquiv hg1 B (by simpa [u, v] using huv)) hOne).elim
  · have hm0 : m ≠ 0 := Nat.ne_of_gt hm.1
    omega

theorem length_two_midpoint_torsionOrder_two
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hαβ : α ≠ β) (hα : B.length α = 2) (hi : i.val = 1)
    (hβ : B.length β = 2) (hj : j.val = 1) :
    IsTorsionOrder
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) 2 := by
  let u := strandVertex B α i
  let v := strandVertex B β j
  have hU : linearEquiv B.graph
      ((2 : ℤ) • oneChip u)
      (oneChip (leftEndpoint B) + oneChip (rightEndpoint B)) := by
    dsimp [u]
    exact two_smul_midpoint_linearEquiv_endpoints B α i hα hi
  have hV : linearEquiv B.graph
      ((2 : ℤ) • oneChip v)
      (oneChip (leftEndpoint B) + oneChip (rightEndpoint B)) := by
    dsimp [v]
    exact two_smul_midpoint_linearEquiv_endpoints B β j hβ hj
  have hUV : linearEquiv B.graph
      ((2 : ℤ) • oneChip u) ((2 : ℤ) • oneChip v) :=
    hU.trans hV.symm
  have hDiff : linearEquiv B.graph
      ((2 : ℤ) • (oneChip u - oneChip v)) 0 := by
    unfold linearEquiv at hUV ⊢
    have heq : (0 : CFDiv B.graph) - (2 : ℤ) • (oneChip u - oneChip v) =
        (2 : ℤ) • oneChip v - (2 : ℤ) • oneChip u := by
      simp [smul_sub]
    rw [heq]
    exact hUV
  have huv : u ≠ v := by
    intro huv
    apply hαβ
    have huPath : u = B.pathVertex α i := by
      dsimp [u, strandVertex]
      split_ifs
      · rfl
      · congr 1
        apply Fin.ext
        simp [hα, hi]
    have hvPath : v = B.pathVertex β j := by
      dsimp [v, strandVertex]
      split_ifs
      · rfl
      · congr 1
        apply Fin.ext
        simp [hβ, hj]
    have hEq : B.pathVertex α i = B.pathVertex β j :=
      huPath.symm.trans (huv.trans hvPath)
    exact (interior_and_strand_eq_of_pathVertex_eq_interior
      B α β i j (by change 0 < j.val ∧ j.val < B.length β; omega)
      hEq).2
  have hg1 : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with hg0 | hg1
    · exact absurd (Fin.ext (by have := α.isLt; have := β.isLt; omega)) hαβ
    · exact hg1
  refine ⟨⟨by omega, hDiff⟩, ?_⟩
  intro m hm
  rw [torsionWitness_mark_iff] at hm
  by_cases hm1 : m = 1
  · subst m
    have h2 := hm.2
    rw [Nat.cast_one, one_zsmul] at h2
    exact ((marks_not_linearEquiv hg1 B (by simpa [u, v] using huv)) h2).elim
  · have hm0 : m ≠ 0 := Nat.ne_of_gt hm.1
    omega

end Bananas
