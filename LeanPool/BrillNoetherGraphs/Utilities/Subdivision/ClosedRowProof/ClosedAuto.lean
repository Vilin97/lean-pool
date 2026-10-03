/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.Leaf
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedCoreSymmetry
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSubdivisionIso

/-!
# Core automorphisms on the closed row-proof orthant

`CoreOrbitReduction` transports positive subdivisions.  An RPF `AUTO` node
also acts on boundary faces, where zero slots have identified core vertices.
This file supplies that missing closed-face transport.  The proof deliberately
uses reachability, rather than the literal output of `compFold`: canonical
union-find representatives need not commute definitionally with a vertex
permutation, but their fibres do.
-/

public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open Utilities.Certificate
open Utilities.Certificate.CoreOrbitReduction
open Utilities.Certificate.ContractionForestCensusGeneral

variable {n p : ℕ} {core : ExplicitPotential.Core n p}

namespace ClosedAuto

/-! ## Fail-closed raw automorphism data

`PTree` is not indexed by a core, so an `auto` node stores lists.  The checker
decodes them only after verifying two-sided inverses and the endpoint laws.
The inverse lists are emitted mechanically from the row's permutations. -/

/-- Raw vertex and slot permutation data checked before use as a graph automorphism. -/
structure AutoData where
  /-- Proposed images of core vertices, decoded modulo the number of vertices. -/
  vertex : List ℕ
  /-- Proposed inverse images of core vertices; the checker verifies both inverse identities
  after decoding. -/
  vertexInv : List ℕ
  /-- Proposed images of slot occurrences, decoded modulo the number of slots. -/
  slot : List ℕ
  /-- Proposed inverse images of slot occurrences; the checker verifies both inverse identities
  after decoding. -/
  slotInv : List ℕ
  /-- Orientation-reversal flags indexed by source slot, with missing flags interpreted as
  false. -/
  reversed : List Bool

namespace AutoData

/-- Decode a proposed vertex image using zero for missing entries and reduction modulo the
nonzero vertex count. -/
def vertexMap (d : AutoData) (hn : 0 < n) (v : Fin n) : Fin n :=
  ⟨d.vertex.getD v.val 0 % n, Nat.mod_lt _ hn⟩

/-- Decode a proposed inverse vertex image using zero for missing entries and reduction modulo
the nonzero vertex count. -/
def vertexInvMap (d : AutoData) (hn : 0 < n) (v : Fin n) : Fin n :=
  ⟨d.vertexInv.getD v.val 0 % n, Nat.mod_lt _ hn⟩

/-- Decode a proposed slot image using zero for missing entries and reduction modulo the nonzero
slot count. -/
def slotMap (d : AutoData) (hp : 0 < p) (e : Fin p) : Fin p :=
  ⟨d.slot.getD e.val 0 % p, Nat.mod_lt _ hp⟩

/-- Decode a proposed inverse slot image using zero for missing entries and reduction modulo the
nonzero slot count. -/
def slotInvMap (d : AutoData) (hp : 0 < p) (e : Fin p) : Fin p :=
  ⟨d.slotInv.getD e.val 0 % p, Nat.mod_lt _ hp⟩

/-- Read the reversal flag of a source slot, defaulting to false when the list has no entry. -/
def reverseAt (d : AutoData) (e : Fin p) : Bool := d.reversed.getD e.val false

/-- Check nonempty vertex and slot sets, both inverse identities, and the two endpoint laws for
the decoded automorphism data. -/
def checks (d : AutoData) (core : ExplicitPotential.Core n p) : Bool :=
  if hn : 0 < n then
    if hp : 0 < p then
      decide (∀ v, d.vertexInvMap hn (d.vertexMap hn v) = v ∧
        d.vertexMap hn (d.vertexInvMap hn v) = v) &&
      decide (∀ e, d.slotInvMap hp (d.slotMap hp e) = e ∧
        d.slotMap hp (d.slotInvMap hp e) = e) &&
      decide (∀ e,
        core.tail (d.slotMap hp e) =
          if d.reverseAt e then d.vertexMap hn (core.head e)
          else d.vertexMap hn (core.tail e)) &&
      decide (∀ e,
        core.head (d.slotMap hp e) =
          if d.reverseAt e then d.vertexMap hn (core.tail e)
          else d.vertexMap hn (core.head e))
    else false
  else false

/-- Construct a core symmetry from decoded vertex and slot permutations after their inverse and
endpoint checks succeed. -/
def toSymmetry (d : AutoData) (core : ExplicitPotential.Core n p)
    (hn : 0 < n) (hp : 0 < p) (hcheck : d.checks core = true) :
    CoreSymmetry core := by
  rw [checks, dite_eq_left hn, dite_eq_left hp, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hcheck
  let vp : Equiv.Perm (Fin n) :=
    { toFun := d.vertexMap hn
      invFun := d.vertexInvMap hn
      left_inv := fun v => (of_decide_eq_true hcheck.1.1.1 v).1
      right_inv := fun v => (of_decide_eq_true hcheck.1.1.1 v).2 }
  let sp : Equiv.Perm (Fin p) :=
    { toFun := d.slotMap hp
      invFun := d.slotInvMap hp
      left_inv := fun e => (of_decide_eq_true hcheck.1.1.2 e).1
      right_inv := fun e => (of_decide_eq_true hcheck.1.1.2 e).2 }
  exact
    { vertexPerm := vp
      slotPerm := sp
      reversed := d.reverseAt
      tail_eq := of_decide_eq_true hcheck.1.2
      head_eq := of_decide_eq_true hcheck.2 }

/-- Pull a form back exactly as `rpfcheck`: the old coefficient at `e` moves
to `slotMap e`, equivalently the new coefficient at `j` is read at
`slotInvMap j`.  RPF row proofs have exactly `p` coordinates. -/
def pullbackForm (d : AutoData) (hp : 0 < p) (g : Form) : Form :=
  g.getD 0 0 :: List.ofFn (fun e : Fin p => g.getD (d.slotInvMap hp e).val.succ 0)

/-- Pull back every inequality and equality form in the context through the decoded inverse slot
map. -/
def pullbackContext (d : AutoData) (hp : 0 < p) (Γ : Context) : Context :=
  ⟨Γ.ge.map (d.pullbackForm hp), Γ.eq.map (d.pullbackForm hp)⟩

theorem eval_pullbackForm (d : AutoData) (core : ExplicitPotential.Core n p)
    (hn : 0 < n) (hp : 0 < p) (hcheck : d.checks core = true)
    (g : Form) (point : Fin p → ℤ) :
    eval (d.pullbackForm hp g)
        (List.ofFn (fun e => point ((d.toSymmetry core hn hp hcheck).slotPerm.symm e))) =
      eval g (List.ofFn point) := by
  rw [← eval_toAffineForm, ← eval_toAffineForm]
  simp only [AffineCover.AffineForm.eval, toAffineForm, pullbackForm,
    List.getD_cons_zero, List.getD_cons_succ]
  have hget (i : Fin p) :
      (List.ofFn fun e : Fin p => g.getD (d.slotInvMap hp e).val.succ 0).getD i.val 0 =
        g.getD (d.slotInvMap hp i).val.succ 0 := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  simp_rw [hget]
  have hslot (e : Fin p) :
      (d.toSymmetry core hn hp hcheck).slotPerm.symm e = d.slotInvMap hp e := rfl
  simp only [hslot]
  congr 1
  apply Fintype.sum_equiv (d.toSymmetry core hn hp hcheck).slotPerm.symm
  intro e
  rw [← hslot]

theorem pullbackContext_holds (d : AutoData) (core : ExplicitPotential.Core n p)
    (hn : 0 < n) (hp : 0 < p) (hcheck : d.checks core = true)
    {Γ : Context} {point : Fin p → ℤ} (hΓ : Γ.Holds (List.ofFn point)) :
    (d.pullbackContext hp Γ).Holds
      (List.ofFn (fun e => point ((d.toSymmetry core hn hp hcheck).slotPerm.symm e))) := by
  constructor
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    rw [d.eval_pullbackForm core hn hp hcheck]
    exact hΓ.1 f hf
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    rw [d.eval_pullbackForm core hn hp hcheck]
    exact hΓ.2 f hf

end AutoData

variable (symmetry : CoreSymmetry core) (length : Fin p → ℕ)

/-- The symmetry-reindexed length vector used to transport the zero-slot contraction and its
surviving subdivision. -/
abbrev targetLength : Fin p → ℕ := symmetry.reindexLength length
theorem adj_map {u v : Fin n} :
    AdjInList core (edgeList (zeroSet length)) u v →
      AdjInList core (edgeList (zeroSet (targetLength symmetry length)))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) := by
  exact Utilities.Certificate.ClosedCoreSymmetry.adj_map symmetry length

theorem adj_map_iff {u v : Fin n} :
    AdjInList core (edgeList (zeroSet (targetLength symmetry length)))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) ↔
      AdjInList core (edgeList (zeroSet length)) u v := by
  exact Utilities.Certificate.ClosedCoreSymmetry.adj_map_iff symmetry length

theorem reach_map_iff (u v : Fin n) :
    ReachIn core (zeroSet (targetLength symmetry length))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) ↔
      ReachIn core (zeroSet length) u v := by
  exact Utilities.Certificate.ClosedCoreSymmetry.reach_map_iff symmetry length u v

theorem rep_eq_iff (u v : Fin n) :
    compFold core (zeroSet (targetLength symmetry length)) (symmetry.vertexPerm u) =
        compFold core (zeroSet (targetLength symmetry length)) (symmetry.vertexPerm v) ↔
      compFold core (zeroSet length) u = compFold core (zeroSet length) v := by
  exact Utilities.Certificate.ClosedCoreSymmetry.rep_eq_iff symmetry length u v

theorem isForest_iff :
    IsForest core (zeroSet (targetLength symmetry length)) ↔
      IsForest core (zeroSet length) := by
  exact Utilities.Certificate.ClosedCoreSymmetry.isForest_iff symmetry length

theorem isLoopy_iff :
    IsLoopy core (zeroSet (targetLength symmetry length)) ↔
      IsLoopy core (zeroSet length) := by
  exact Utilities.Certificate.ClosedCoreSymmetry.isLoopy_iff symmetry length

theorem bnExists_iff (hn : 0 < n) (hForest : IsForest core (zeroSet length))
    (hNotLoopy : ¬ IsLoopy core (zeroSet length)) (rank degree : ℤ) :
    BNExists
        (censusSpec core hn (targetLength symmetry length)
          ((isForest_iff symmetry length).2 hForest)
          (fun h => hNotLoopy ((isLoopy_iff symmetry length).1 h))).graph rank degree ↔
      BNExists (censusSpec core hn length hForest hNotLoopy).graph rank degree := by
  exact Utilities.Certificate.ClosedCoreSymmetry.bnExists_iff symmetry length hn hForest
    hNotLoopy rank degree

end ClosedAuto

end Utilities.Subdivision.ClosedRowProof
