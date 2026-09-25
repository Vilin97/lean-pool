/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.Leaf
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreSymmetry
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

@[expose] public section

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
private theorem zero_mem_map (e : Fin p) :
    symmetry.slotPerm e ∈ zeroSet (targetLength symmetry length) ↔ e ∈ zeroSet length := by
  have hleft : symmetry.slotPerm e ∈ zeroSet (targetLength symmetry length) ↔
      targetLength symmetry length (symmetry.slotPerm e) = 0 := by
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
  have hright : e ∈ zeroSet length ↔ length e = 0 := by
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
  have hlength : targetLength symmetry length (symmetry.slotPerm e) = length e := by
    exact congrArg length (symmetry.slotPerm.symm_apply_apply e)
  exact hleft.trans ((congrArg (· = 0) hlength).to_iff.trans hright.symm)

theorem adj_map {u v : Fin n} :
    AdjInList core (edgeList (zeroSet length)) u v →
      AdjInList core (edgeList (zeroSet (targetLength symmetry length)))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) := by
  rintro ⟨e, he, huv⟩
  refine ⟨symmetry.slotPerm e, (mem_edgeList _ _).2 ?_, ?_⟩
  · exact (zero_mem_map symmetry length e).2 ((mem_edgeList _ _).1 he)
  · have ht := symmetry.tail_eq e
    have hh := symmetry.head_eq e
    by_cases hr : symmetry.reversed e
    · simp [hr] at ht hh
      rcases huv with huv | huv
      · exact Or.inr ⟨hh.trans (congrArg symmetry.vertexPerm huv.1),
          ht.trans (congrArg symmetry.vertexPerm huv.2)⟩
      · exact Or.inl ⟨ht.trans (congrArg symmetry.vertexPerm huv.1),
          hh.trans (congrArg symmetry.vertexPerm huv.2)⟩
    · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
      simp [hr'] at ht hh
      rcases huv with huv | huv
      · exact Or.inl ⟨ht.trans (congrArg symmetry.vertexPerm huv.1),
          hh.trans (congrArg symmetry.vertexPerm huv.2)⟩
      · exact Or.inr ⟨hh.trans (congrArg symmetry.vertexPerm huv.1),
          ht.trans (congrArg symmetry.vertexPerm huv.2)⟩

theorem adj_map_iff {u v : Fin n} :
    AdjInList core (edgeList (zeroSet (targetLength symmetry length)))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) ↔
      AdjInList core (edgeList (zeroSet length)) u v := by
  constructor
  · rintro ⟨f, hf, huv⟩
    let e := symmetry.slotPerm.symm f
    have hfe : symmetry.slotPerm e = f := symmetry.slotPerm.apply_symm_apply f
    have he : e ∈ zeroSet length := by
      apply (zero_mem_map symmetry length e).1
      simpa [hfe] using (mem_edgeList _ _).1 hf
    refine ⟨e, (mem_edgeList _ _).2 he, ?_⟩
    have ht := symmetry.tail_eq e
    have hh := symmetry.head_eq e
    rw [hfe] at ht hh
    by_cases hr : symmetry.reversed e
    · simp [hr] at ht hh
      rcases huv with huv | huv
      · right
        constructor
        · exact symmetry.vertexPerm.injective (huv.1.symm.trans ht) |>.symm
        · exact symmetry.vertexPerm.injective (huv.2.symm.trans hh) |>.symm
      · left
        constructor
        · exact symmetry.vertexPerm.injective (huv.1.symm.trans hh) |>.symm
        · exact symmetry.vertexPerm.injective (huv.2.symm.trans ht) |>.symm
    · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
      simp [hr'] at ht hh
      rcases huv with huv | huv
      · left
        constructor
        · exact symmetry.vertexPerm.injective (huv.1.symm.trans ht) |>.symm
        · exact symmetry.vertexPerm.injective (huv.2.symm.trans hh) |>.symm
      · right
        constructor
        · exact symmetry.vertexPerm.injective (huv.1.symm.trans hh) |>.symm
        · exact symmetry.vertexPerm.injective (huv.2.symm.trans ht) |>.symm
  · exact adj_map symmetry length

theorem reach_map_iff (u v : Fin n) :
    ReachIn core (zeroSet (targetLength symmetry length))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) ↔
      ReachIn core (zeroSet length) u v := by
  unfold ReachIn ReachInList
  constructor
  · intro h
    simpa [Function.onFun] using Relation.ReflTransGen.lift symmetry.vertexPerm.symm
      (fun a b hab => (adj_map_iff symmetry length
        (u := symmetry.vertexPerm.symm a) (v := symmetry.vertexPerm.symm b)).1
        (by simpa using hab)) (symmetry.vertexPerm u) (symmetry.vertexPerm v) h
  · exact Relation.ReflTransGen.lift symmetry.vertexPerm
      (fun _ _ h => adj_map symmetry length h) u v

theorem rep_eq_iff (u v : Fin n) :
    compFold core (zeroSet (targetLength symmetry length)) (symmetry.vertexPerm u) =
        compFold core (zeroSet (targetLength symmetry length)) (symmetry.vertexPerm v) ↔
      compFold core (zeroSet length) u = compFold core (zeroSet length) v := by
  rw [compFold_iff, compFold_iff, reach_map_iff symmetry length]

private noncomputable def classEquiv :
    {v : Fin n // compFold core (zeroSet length) v = v} ≃
      {v : Fin n // compFold core (zeroSet (targetLength symmetry length)) v = v} :=
  Equiv.ofBijective
    (fun x => ⟨compFold core (zeroSet (targetLength symmetry length))
      (symmetry.vertexPerm x.val), compFold_idem _ _ _⟩)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      have hrep := (rep_eq_iff symmetry length x.val y.val).1
        (congrArg Subtype.val hxy)
      simpa [x.property, y.property] using hrep,
     by
      intro y
      let z := symmetry.vertexPerm.symm y.val
      let x : {v : Fin n // compFold core (zeroSet length) v = v} :=
        ⟨compFold core (zeroSet length) z, compFold_idem _ _ _⟩
      refine ⟨x, Subtype.ext ?_⟩
      change compFold core (zeroSet (targetLength symmetry length))
        (symmetry.vertexPerm (compFold core (zeroSet length) z)) = y.val
      have hreach : ReachIn core (zeroSet length) (compFold core (zeroSet length) z) z :=
        (reachIn_equivalence core (zeroSet length)).symm
          (reachIn_self_compFold core (zeroSet length) z)
      have htarget := (reach_map_iff symmetry length
        (compFold core (zeroSet length) z) z).2 hreach
      have hrep := (compFold_iff core _ _ _).2 htarget
      simpa [z, y.property] using hrep⟩

private theorem card_fixed_eq_image (rep : Fin n → Fin n)
    (hidem : ∀ v, rep (rep v) = rep v) :
    Fintype.card {v : Fin n // rep v = v} =
      (Finset.image rep Finset.univ).card := by
  have himage : Finset.image rep Finset.univ =
      Finset.univ.filter (fun v : Fin n => rep v = v) := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hu, hidem u]⟩
    · intro hv
      exact Finset.mem_image.mpr
        ⟨v, Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  rw [himage, Fintype.card_subtype]

private theorem zero_card_eq :
    (zeroSet (targetLength symmetry length)).card = (zeroSet length).card := by
  refine Finset.card_bij (fun e _ => symmetry.slotPerm.symm e) ?_ ?_ ?_
  · intro e he
    have := (zero_mem_map symmetry length (symmetry.slotPerm.symm e)).1
      (by simpa using he)
    simpa using this
  · intro a _ b _ hab
    exact symmetry.slotPerm.symm.injective hab
  · intro e he
    refine ⟨symmetry.slotPerm e, (zero_mem_map symmetry length e).2 he, ?_⟩
    simp

theorem isForest_iff :
    IsForest core (zeroSet (targetLength symmetry length)) ↔
      IsForest core (zeroSet length) := by
  unfold IsForest
  have hclass := Fintype.card_congr (classEquiv symmetry length)
  rw [card_fixed_eq_image _ (compFold_idem core (zeroSet length)),
    card_fixed_eq_image _ (compFold_idem core (zeroSet (targetLength symmetry length)))]
    at hclass
  rw [zero_card_eq symmetry length, hclass]

theorem isLoopy_iff :
    IsLoopy core (zeroSet (targetLength symmetry length)) ↔
      IsLoopy core (zeroSet length) := by
  unfold IsLoopy
  constructor
  · rintro ⟨f, hf, hrep⟩
    let e := symmetry.slotPerm.symm f
    have hfe : symmetry.slotPerm e = f := symmetry.slotPerm.apply_symm_apply f
    have he : e ∉ zeroSet length := by
      intro he
      have himage := (zero_mem_map symmetry length e).2 he
      rw [hfe] at himage
      exact hf himage
    refine ⟨e, he, ?_⟩
    apply (rep_eq_iff symmetry length (core.tail e) (core.head e)).1
    have ht := symmetry.tail_eq e
    have hh := symmetry.head_eq e
    rw [hfe] at ht hh
    by_cases hr : symmetry.reversed e
    · simp [hr] at ht hh
      simpa [ht, hh] using hrep.symm
    · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
      simp [hr'] at ht hh
      simpa [ht, hh] using hrep
  · rintro ⟨e, he, hrep⟩
    refine ⟨symmetry.slotPerm e, ?_, ?_⟩
    · exact fun h => he ((zero_mem_map symmetry length e).1 h)
    · have htarget := (rep_eq_iff symmetry length (core.tail e) (core.head e)).2 hrep
      have ht := symmetry.tail_eq e
      have hh := symmetry.head_eq e
      by_cases hr : symmetry.reversed e
      · simp [hr] at ht hh
        simpa [ht, hh] using htarget.symm
      · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
        simp [hr'] at ht hh
        simpa [ht, hh] using htarget

theorem bnExists_iff (hn : 0 < n) (hForest : IsForest core (zeroSet length))
    (hNotLoopy : ¬ IsLoopy core (zeroSet length)) (rank degree : ℤ) :
    BNExists
        (censusSpec core hn (targetLength symmetry length)
          ((isForest_iff symmetry length).2 hForest)
          (fun h => hNotLoopy ((isLoopy_iff symmetry length).1 h))).graph rank degree ↔
      BNExists (censusSpec core hn length hForest hNotLoopy).graph rank degree := by
  let source := censusSpec core hn length hForest hNotLoopy
  let hForest' := (isForest_iff symmetry length).2 hForest
  let hNotLoopy' : ¬ IsLoopy core (zeroSet (targetLength symmetry length)) :=
    fun h => hNotLoopy ((isLoopy_iff symmetry length).1 h)
  let target := censusSpec core hn (targetLength symmetry length) hForest' hNotLoopy'
  let ce : source.Class ≃ target.Class := classEquiv symmetry length
  have hclass (u : Fin n) :
      ce ⟨source.rep u, source.rep_idem u⟩ =
        ⟨target.rep (symmetry.vertexPerm u), target.rep_idem _⟩ := by
    apply Subtype.ext
    exact (rep_eq_iff symmetry length (source.rep u) u).2
      (source.rep_idem u)
  let rel : source.Relabeling target :=
    { classEquiv := ce
      slotEquiv := symmetry.slotPerm
      reversed := symmetry.reversed
      length_eq := fun e => symmetry.reindexLength_compat length e
      tail_eq := fun e => by
        by_cases hr : symmetry.reversed e
        · simp only [ite_eq_left hr]
          rw [hclass]
          apply Subtype.ext
          have ht := symmetry.tail_eq e
          simp [hr] at ht
          change target.rep (symmetry.vertexPerm (core.head e)) =
            target.rep (core.tail (symmetry.slotPerm e))
          rw [ht]
        · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
          simp only [ite_eq_right hr]
          rw [hclass]
          apply Subtype.ext
          have ht := symmetry.tail_eq e
          simp [hr'] at ht
          change target.rep (symmetry.vertexPerm (core.tail e)) =
            target.rep (core.tail (symmetry.slotPerm e))
          rw [ht]
      head_eq := fun e => by
        by_cases hr : symmetry.reversed e
        · simp only [ite_eq_left hr]
          rw [hclass]
          apply Subtype.ext
          have hh := symmetry.head_eq e
          simp [hr] at hh
          change target.rep (symmetry.vertexPerm (core.tail e)) =
            target.rep (core.head (symmetry.slotPerm e))
          rw [hh]
        · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
          simp only [ite_eq_right hr]
          rw [hclass]
          apply Subtype.ext
          have hh := symmetry.head_eq e
          simp [hr'] at hh
          change target.rep (symmetry.vertexPerm (core.head e)) =
            target.rep (core.head (symmetry.slotPerm e))
          rw [hh] }
  exact Utilities.Certificate.DegenerateSpec.DegSpec.Relabeling.bnExists_iff source target rel rank degree

end ClosedAuto

end Utilities.Subdivision.ClosedRowProof
