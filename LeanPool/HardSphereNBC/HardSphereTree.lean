/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
module

public import LeanPool.HardSphereNBC.HardSphereFork
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


/-! ### Elementary tree-coordinate shears -/

@[expose] public section

namespace HsVirial

open Set
open Metric
open SimpleGraph
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The graph induced by a finite set of particle edges. -/
def hardSphereTreeGraph {k : Nat}
    (T : Finset (Sym2 (Fin k))) : SimpleGraph (Fin k) :=
  SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin k)))

lemma hardSphereTreeGraph_isTree {k : Nat}
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    (hardSphereTreeGraph T).IsTree := by
  classical
  exact (Finset.mem_filter.mp hT).2

lemma hardSphereTree_parent_exists {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (i : Fin (k - 1)) :
    ∃ p : Fin k,
      p ≠ hardSphereFreeParticleIndex i ∧
      (hardSphereTreeGraph T).Adj p (hardSphereFreeParticleIndex i) ∧
    (hardSphereTreeGraph T).dist 0 p + 1 =
        (hardSphereTreeGraph T).dist 0 (hardSphereFreeParticleIndex i) := by
  classical
  let G := hardSphereTreeGraph T
  let v := hardSphereFreeParticleIndex i
  have hv : v ≠ 0 := by
    intro h
    have hv' := congrArg Fin.val h
    simp [v, hardSphereFreeParticleIndex] at hv'
  have htree : G.IsTree := hardSphereTreeGraph_isTree hT
  obtain ⟨p, hp, hplen⟩ := htree.connected.exists_path_of_dist 0 v
  have hpos : 0 < p.length := by
    rw [hplen]
    exact htree.connected.pos_dist_of_ne hv.symm
  have hpnonempty : ¬p.Nil := by
    intro hnil
    have : p.length = 0 := Walk.Nil.length_eq_zero hnil
    omega
  refine ⟨p.penultimate, ?_, p.adj_penultimate hpnonempty, ?_⟩
  · intro heq
    exact (p.adj_penultimate hpnonempty).ne heq
  have hsub : p.dropLast.IsSubwalk p := by
    exact Walk.isSubwalk_take p (p.length - 1)
  have hlast : p.dropLast.length = G.dist 0 p.penultimate := by
    exact length_eq_dist_of_subwalk hplen hsub
  have hdrop : p.dropLast.length + 1 = G.dist 0 v := by
    calc
      p.dropLast.length + 1 = p.length := p.length_dropLast_add_one hpnonempty
      _ = G.dist 0 v := hplen
  rw [hlast] at hdrop
  simpa using hdrop

/-- The parent of a free particle in the tree rooted at the anchored particle. -/
noncomputable def hardSphereTreeParent {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (i : Fin (k - 1)) : Fin k :=
  (hardSphereTree_parent_exists hT i).choose

lemma hardSphereTreeParent_ne {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (i : Fin (k - 1)) :
    hardSphereTreeParent hT i ≠ hardSphereFreeParticleIndex i := by
  exact (hardSphereTree_parent_exists hT i).choose_spec.1

lemma hardSphereTreeParent_adj {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (i : Fin (k - 1)) :
    (hardSphereTreeGraph T).Adj (hardSphereTreeParent hT i)
      (hardSphereFreeParticleIndex i) := by
  exact (hardSphereTree_parent_exists hT i).choose_spec.2.1

lemma hardSphereTreeParent_dist_succ {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (i : Fin (k - 1)) :
    (hardSphereTreeGraph T).dist 0 (hardSphereTreeParent hT i) + 1 =
      (hardSphereTreeGraph T).dist 0 (hardSphereFreeParticleIndex i) := by
  exact (hardSphereTree_parent_exists hT i).choose_spec.2.2

lemma hardSphereTreeParent_mem {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (i : Fin (k - 1)) :
    s(hardSphereTreeParent hT i, hardSphereFreeParticleIndex i) ∈ T := by
  have hadj := hardSphereTreeParent_adj hT i
  rw [hardSphereTreeGraph, SimpleGraph.fromEdgeSet_adj] at hadj
  simpa using hadj.1

lemma hardSphereFreeParticleIndex_freeIndex {k : Nat} [NeZero k]
    (v : Fin k) (hv : v ≠ 0) :
    hardSphereFreeParticleIndex (hardSphereFreeIndex v hv) = v := by
  have hvpos : 0 < v.val := by
    have hvzero : v.val ≠ 0 := by
      intro hz
      apply hv
      apply Fin.ext
      simpa using hz
    omega
  apply Fin.ext
  simp [hardSphereFreeParticleIndex, hardSphereFreeIndex]
  omega

/-- An order of free particles compatible with their rooted-tree depth. -/
@[instance_reducible]
noncomputable def hardSphereTreeIndexOrder {k : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) (_hT : T ∈ treeUniverse (V := Fin k)) :
    LinearOrder (Fin (k - 1)) :=
  LinearOrder.lift'
    (fun i => toLex ((hardSphereTreeGraph T).dist 0
      (hardSphereFreeParticleIndex i), hardSphereFreeParticleIndex i)) (by
        intro i j h
        have h' : hardSphereFreeParticleIndex i =
            hardSphereFreeParticleIndex j := by
          simpa using congrArg (fun p : Nat ×ₗ Fin k => (ofLex p).2) h
        apply Fin.ext
        have hv := congrArg Fin.val h'
        simp [hardSphereFreeParticleIndex] at hv
        omega)

lemma hardSphereTreeParent_index_lt {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (i : Fin (k - 1))
    (hp : hardSphereTreeParent hT i ≠ 0) :
    @LT.lt (Fin (k - 1)) (hardSphereTreeIndexOrder T hT).toLT
      (hardSphereFreeIndex (hardSphereTreeParent hT i) hp) i := by
  change toLex ((hardSphereTreeGraph T).dist 0
      (hardSphereFreeParticleIndex (hardSphereFreeIndex
        (hardSphereTreeParent hT i) hp)),
      hardSphereFreeParticleIndex (hardSphereFreeIndex
        (hardSphereTreeParent hT i) hp)) <
      toLex ((hardSphereTreeGraph T).dist 0 (hardSphereFreeParticleIndex i),
        hardSphereFreeParticleIndex i)
  rw [hardSphereFreeParticleIndex_freeIndex]
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl (by
    have h := hardSphereTreeParent_dist_succ hT i
    omega)

/-- The position difference along the rooted parent edge of a free particle. -/
def hardSphereTreeDifference {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (r : HardSphereConfiguration k 3) (i : Fin (k - 1)) : HSPosition 3 :=
  hardSpherePosition r (hardSphereFreeParticleIndex i) -
    hardSpherePosition r (hardSphereTreeParent hT i)

lemma hardSphereTreeDifference_eq_coordinate_sub {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (r : HardSphereConfiguration k 3) (i : Fin (k - 1)) :
    hardSphereTreeDifference hT r i =
      r i - hardSpherePosition r (hardSphereTreeParent hT i) := by
  simp [hardSphereTreeDifference]

lemma hardSphereTreeDifference_norm_lt_one {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    {r : HardSphereConfiguration k 3}
    (hr : r ∈ hardSphereTreeRegion T) (i : Fin (k - 1)) :
    ‖hardSphereTreeDifference hT r i‖ < (1 : ℝ) := by
  have hactive := hr _ (hardSphereTreeParent_mem hT i)
  rw [hardSphereActiveExact_mk] at hactive
  have hnorm : ‖hardSpherePosition r (hardSphereTreeParent hT i) -
      r i‖ < (1 : ℝ) := of_decide_eq_true hactive
  rw [norm_sub_rev] at hnorm
  simpa [hardSphereTreeDifference] using hnorm

/-- The product of unit-ball constraints for all rooted tree differences. -/
def hardSphereTreeDifferenceRegion {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    Set (HardSphereConfiguration k 3) :=
  {r | ∀ i, hardSphereTreeDifference hT r i ∈ ball 0 1}

lemma hardSphereTreeRegion_subset_differenceRegion {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    hardSphereTreeRegion T ⊆ hardSphereTreeDifferenceRegion hT := by
  intro r hr i
  rw [mem_ball_iff_norm]
  simpa only [sub_zero] using hardSphereTreeDifference_norm_lt_one hT hr i

lemma measurableSet_hardSphereTreeDifferenceRegion {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    MeasurableSet (hardSphereTreeDifferenceRegion hT) := by
  rw [show hardSphereTreeDifferenceRegion hT =
      ⋂ i : Fin (k - 1), {r : HardSphereConfiguration k 3 |
        hardSphereTreeDifference hT r i ∈ ball 0 1} by
    ext r
    simp [hardSphereTreeDifferenceRegion]]
  exact MeasurableSet.iInter (fun i => by
    change MeasurableSet ((fun r : HardSphereConfiguration k 3 =>
      hardSphereTreeDifference hT r i) ⁻¹' ball 0 1)
    apply MeasurableSet.preimage measurableSet_ball
    exact ((continuous_hardSpherePosition
      (k := k) (d := 3) (hardSphereFreeParticleIndex i)).sub
      (continuous_hardSpherePosition
        (k := k) (d := 3) (hardSphereTreeParent hT i))).measurable)



/-- Subtract the parent scalar coordinate from a child scalar coordinate. -/
def hardSphereScalarShear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (parent child : ι) (hpc : parent ≠ child) : (ι → ℝ) → (ι → ℝ) :=
  Matrix.toLin'
    (Matrix.TransvectionStruct.toMatrix
      { i := child, j := parent, hij := hpc.symm, c := (-1 : ℝ) })

lemma measurePreserving_hardSphereScalarShear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (parent child : ι) (hpc : parent ≠ child) :
    MeasurePreserving (hardSphereScalarShear parent child hpc)
      (volume : Measure (ι → ℝ)) (volume : Measure (ι → ℝ)) := by
  exact Real.volume_preserving_transvectionStruct
    { i := child, j := parent, hij := hpc.symm, c := (-1 : ℝ) }

lemma hardSphereScalarShear_apply_child
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (parent child : ι) (hpc : parent ≠ child) (x : ι → ℝ) :
    hardSphereScalarShear parent child hpc x child = x child - x parent := by
  change (Matrix.mulVec (Matrix.transvection child parent (-1)) x) child = _
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec]
  simp [sub_eq_add_neg]

lemma hardSphereScalarShear_apply_parent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (parent child : ι) (hpc : parent ≠ child) (x : ι → ℝ) :
    hardSphereScalarShear parent child hpc x parent = x parent := by
  change (Matrix.mulVec (Matrix.transvection child parent (-1)) x) parent = _
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec]
  simp [hpc]

lemma hardSphereScalarShear_apply_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (parent child q : ι) (hpc : parent ≠ child) (hqc : q ≠ child)
    (x : ι → ℝ) :
    hardSphereScalarShear parent child hpc x q = x q := by
  change (Matrix.mulVec (Matrix.transvection child parent (-1)) x) q = _
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec]
  simp [hqc]

end

end HsVirial
