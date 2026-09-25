/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.ClosedAuto
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichLeafAssembly
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.ClosedVertexCut

/-!
# The row-proof tree layer, deep-embedded

Step C of the proof-data source needs a way to lower a `SPLIT` node.  `NEXT.md`
proposed lowering it *shallowly*, as a generated `rcases le_or_gt`; this file
takes the deep-embedded route instead, for the same reason the corresponding closed-row proof module
deep-embeds the arithmetic:

* the whole tree becomes one piece of data and one `decide`, instead of one
  `decide` per leaf plus a generated tactic script whose size is the number of
  nodes — for `g4row099` that is 64 leaves and 63 splits;
* the accumulated context at a leaf is *computed* by `PTree.checks` rather than
  transcribed by the emitter, so the emitter cannot get it wrong;
* the `rcases le_or_gt` of the shallow plan survives verbatim, once, inside
  `PTree.sound` below, where it is proved rather than generated.

The tree layer is deliberately minimal: `SPLIT`, `LEAF`, `USE`, `AUTO`,
`ABSURD`, and the one `REDUCE` opcode whose Lean theorem exists on the closed
orthant, `REDUCE CUTVERTEX`.  Spec §4.2's other opcodes (`SPLIT3`, `MOD`,
`CITE`, and the other `REDUCE` operations) are absent on purpose — spec
§13.6's rule is that a node shape is a reject until its Lean theorem exists,
and adding a constructor here with no soundness case would break `PTree.sound`
rather than silently weaken it.

## `ABSURD`

`(absurd cert)` discharges an *empty* cell: `cert` is a Farkas derivation of
`−1 ≥ 0` from the accumulated context, so no point satisfies the context and
the row's conclusion holds there vacuously.  This is the same `Cert` and the
same `Cert.check_sound` as everywhere else — the only novelty is that the form
entailed is the constant `falseForm = −1` rather than something the leaf needs.

It is not a luxury.  Splitting a chamber finely produces empty cells as the
normal case, so a cover of any size contains them in quantity; a tree layer
without `ABSURD` can only lower covers that were pruned by hand.

`AUTO` is closed-face sound, not merely an interior-cone shortcut.  Its raw
permutations are checked against the core, its context forms are pulled back
by the slot permutation, and `ClosedAuto.bnExists_iff` transports through the
quotient classes created by zero slots.  Named-subtree soundness is therefore
kept uniform in the length vector: an auto-wrapped `use` may invoke the same
subtree at the reindexed metric and then transport the result back.

## `USE`, and the shape change it forces

`(use k cert_0 … cert_{m-1})` cites the *earlier* named subtree `k`.  A subtree
carries an **entry context** — a list of forms it may assume on top of the root
domain — and the citing node must show that the context accumulated at the
citation entails every one of them.  That is pure context weakening, and
`Cert.check_sound` is exactly the entailment half of it.

So `use` cannot be checked against a tree alone: the checker has to know what
the earlier subtrees claim.  `PTree.checksIn` therefore threads a list `E` of
entry contexts, `PProof` bundles an ordered list of subtrees with a main tree,
and `subsCheck` walks the subtrees in order, each seeing only its predecessors.
That ordering is what makes the recursion well-founded and is verbatim
`rpfcheck.c`'s "`use` must reference an earlier subtree".

`PTree.checks` is kept as the `E = []` specialisation, so a proof with no
subtrees — every row in the catalog that predates this — lowers to exactly the
same term it did before.

The payoff is that a chamber cover whose cells reuse the same local witness
stores and *checks* that witness once: on row 099 the 64 materialized leaves
become 15 subtrees plus 64 entailment citations.

## `REDUCE CUTVERTEX`

`(reduce cutvertex v c_0 … c_{p-1})` names an articulation vertex `v` and
two-colours the slots.  the proof-data source verifies that the colouring
really does split the core at `v` into two connected positive-genus factors
meeting only there, and then cites the factorwise gluing theorem.  On the Lean
side that citation is
`RowProof.bnExists_censusSpec_of_genusFourRankOneCheck`, the closed-orthant
port of `Certificate/CoreVertexCutGenusFour.lean`'s theorem, whose conclusion
is verbatim `PTree.sound`'s at `degree = 3`.

Three things make the fit exact rather than approximate.

* The Lean checker is `CoreVertexCut.Data.genusFourRankOneCheck`, which
  re-derives the cut, the two factor genera, and — on a genus-one factor — the
  two-regularity that `PointedGenusOneRigid` needs.  The colouring is *not*
  trusted: `CutData` carries raw `ℕ`s, `toCut` decodes them totally, and the
  checker validates the decoding.  A `.rpf` colouring that does not in fact
  cut the core is simply rejected by `decide`.
* The gluing theorem is **specific to `degree = 3`**, unlike the rest of
  `PTree.sound`, which is generic in `degree`.  `CutData.checks` therefore
  demands `degree = 3` outright rather than papering over the difference.
* The node's conclusion is unconditional — it holds on the whole closed
  orthant — so `CutData.checks` ignores the accumulated context `Γ`.  That is
  sound in the safe direction: the node proves more than its chamber needs.

## The context discipline

`SPLIT g` pushes `g` in the first branch and `−1 − g` in the second; over the
integers those are exhaustive, and that is the entire coverage argument (spec
§4.2).  New rows are appended at the **end** of `Γ.ge`, so a context row's
index never changes as the tree descends: at a leaf of a depth-`k` branch the
root's `p` coordinate rows still sit at indices `0 … p−1` and the branch
conditions at `p … p+k−1`.  That stability is what lets the emitter address
context rows by a fixed index in every certificate it synthesises.
-/

@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open MarkedGraphs.Certificate
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral

/-- `−1 − g`: the negation of `g ≥ 0` over the integers. -/
def negForm (g : Form) : Form := subForm [-1] g

@[simp] theorem eval_negForm (g : Form) (x : List ℤ) :
    eval (negForm g) x = -1 - eval g x := by
  rw [negForm, eval_subForm]
  simp [eval, dot]

/-- The constant form `−1`.  A context that entails it is unsatisfiable, which
is exactly what an `ABSURD` node certifies. -/
def falseForm : Form := [-1]

@[simp] theorem eval_falseForm (x : List ℤ) : eval falseForm x = -1 := by
  simp [falseForm, eval, dot]

/-- Append a form to the inequality part of a context.  Appending, rather than
prepending, is what keeps context indices stable down a branch. -/
def Context.pushGe (Γ : Context) (g : Form) : Context := ⟨Γ.ge ++ [g], Γ.eq⟩

theorem Context.pushGe_holds {Γ : Context} {g : Form} {x : List ℤ}
    (hΓ : Γ.Holds x) (hg : 0 ≤ eval g x) : (Γ.pushGe g).Holds x := by
  refine ⟨?_, hΓ.2⟩
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · exact hΓ.1 f h
  · rw [List.mem_singleton.mp h]; exact hg

/-! ## The `REDUCE CUTVERTEX` node

`PTree` is core-independent — it is one inductive type, not a family indexed by
`(n, p, core)` — so a `cutvertex` node cannot carry a `CoreVertexCut.Data core`
directly.  It carries raw `ℕ` data instead, and `toCut` / `toTree` decode it
against whatever core the checker is run at.  Decoding is **total**: out-of-range
indices are reduced `% n` or `% p` and missing list entries default to `0`,
exactly as the generated `core` itself decodes its `tail`/`head` lists.  Nothing
about the decoded data is believed; `genusFourRankOneCheck` re-derives every
condition the gluing theorem needs. -/

/-- Raw data for a `(reduce cutvertex …)` node: the articulation vertex and one
side of the cut, plus a rooted spanning tree witnessing core connectivity.

The `.rpf` carries only `glue` and the slot colouring; `left` is the colouring
converted to a vertex set, and the four tree fields are synthesised by the
emitter.  Both conversions are validated by the checker rather than trusted. -/
structure CutData where
  /-- The articulation vertex, as a raw index. -/
  glue : ℕ
  /-- The named side of the cut, as raw vertex indices; must contain `glue`. -/
  left : List ℕ
  /-- Root of the spanning tree. -/
  root : ℕ
  /-- `parent v`, indexed by raw vertex index. -/
  parent : List ℕ
  /-- A slot joining `v` to `parent v`, indexed by raw vertex index. -/
  parentEdge : List ℕ
  /-- A rank that strictly decreases along parent links. -/
  rank : List ℕ

namespace CutData

variable {n p : ℕ}

/-- Decode the articulation vertex and the named side. -/
def toCut (d : CutData) (core : ExplicitPotential.Core n p) (hn : 0 < n) :
    CoreVertexCut.Data core where
  glue := ⟨d.glue % n, Nat.mod_lt _ hn⟩
  left := (d.left.map fun v => (⟨v % n, Nat.mod_lt _ hn⟩ : Fin n)).toFinset

/-- Decode the spanning-tree certificate. -/
def toTree (d : CutData) (core : ExplicitPotential.Core n p) (hn : 0 < n)
    (hp : 0 < p) : SpanningTreeConnectivity.Certificate core where
  root := ⟨d.root % n, Nat.mod_lt _ hn⟩
  parent := fun v => ⟨d.parent.getD v.val 0 % n, Nat.mod_lt _ hn⟩
  parentEdge := fun v => ⟨d.parentEdge.getD v.val 0 % p, Nat.mod_lt _ hp⟩
  rank := fun v => d.rank.getD v.val 0

/-- The node checker: the three hypotheses of
`bnExists_censusSpec_of_genusFourRankOneCheck` that are not already in scope.

`degree = 3` is demanded because the gluing theorem is degree-three-specific.
The empty core (`n = 0`) and the edgeless core (`p = 0`) are rejected outright:
neither can carry a spanning-tree certificate, and neither is a genus-four
row. -/
def checks (d : CutData) (core : ExplicitPotential.Core n p) (degree : ℤ) :
    Bool :=
  if hn : 0 < n then
    if hp : 0 < p then
      decide (degree = 3) &&
        ExplicitPotential.allFin
            (fun e : Fin p => decide (core.tail e ≠ core.head e)) &&
        (d.toCut core hn).genusFourRankOneCheck (d.toTree core hn hp)
    else false
  else false

end CutData

/-! ## Subtrees and their entry contexts

A named subtree is checked once, under the root domain extended by its declared
entry forms; a `use` node cites it after re-deriving those forms in whatever
context the citation sits in. -/

/-- The context a subtree is checked under: the closed root domain, then the
subtree's declared entry forms.  Appending keeps the root's `p` coordinate rows
at indices `0 … p−1`, so a certificate synthesised against the root addresses
the same rows inside a subtree. -/
def subContext (p : ℕ) (entry : List Form) : Context :=
  ⟨(List.range p).map coordForm ++ entry, []⟩

/-- Positional lookup into the list of entry contexts.  Written out rather than
taken from `List.getElem?` so that `lookup_mem` — the only fact soundness needs
— is a three-line induction that cannot drift with the library. -/
def lookupEntry : List (List Form) → ℕ → Option (List Form)
  | [], _ => none
  | e :: _, 0 => some e
  | _ :: rest, k + 1 => lookupEntry rest k

theorem lookupEntry_mem :
    ∀ {E : List (List Form)} {k : ℕ} {entry : List Form},
      lookupEntry E k = some entry → entry ∈ E
  | [], _, _, h => by simp [lookupEntry] at h
  | _ :: _, 0, _, h => by
      rw [lookupEntry, Option.some.injEq] at h; exact h ▸ List.mem_cons_self ..
  | _ :: rest, k + 1, _, h => by
      rw [lookupEntry] at h
      exact List.mem_cons_of_mem _ (lookupEntry_mem (E := rest) (k := k) h)

/-- The citation's obligation: certificate `i` must entail entry form `i`.
A missing certificate is `Cert.dflt`, which fails `1 ≤ k`, so a `use` with too
few certificates is a reject rather than a gap. -/
def entryChecks (Γ : Context) : List Form → List Cert → Bool
  | [], _ => true
  | g :: gs, cs =>
      (cs.headD Cert.dflt).check Γ g && entryChecks Γ gs cs.tail

theorem entryChecks_sound {Γ : Context} {x : List ℤ} (hΓ : Γ.Holds x) :
    ∀ {entry : List Form} {certs : List Cert},
      entryChecks Γ entry certs = true → ∀ g ∈ entry, 0 ≤ eval g x
  | [], _, _, _, hg => by simp at hg
  | g :: gs, cs, h, f, hf => by
      rw [entryChecks, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hf with rfl | hf
      · exact Cert.check_sound h.1 hΓ
      · exact entryChecks_sound hΓ (entry := gs) (certs := cs.tail) h.2 f hf

/-- A row proof tree: spec §4.2 restricted to the node shapes that have a Lean
soundness theorem. -/
inductive PTree where
  /-- A leaf carrying the local witness of spec §4.3. -/
  | leaf : Witness → PTree
  /-- A full W1--W5 leaf with multiple blocks and positioned chips. -/
  | richLeaf : RichWitness → PTree
  /-- `SPLIT g`: the first child is verified under `g ≥ 0`, the second under
  `−1 − g ≥ 0`. -/
  | split : Form → PTree → PTree → PTree
  /-- `AUTO a`: verify the child after pulling its context through a checked
  core automorphism. -/
  | auto : ClosedAuto.AutoData → PTree → PTree
  /-- `REDUCE CUTVERTEX`: a leaf-like node discharged by the genus-four
  vertex-cut gluing theorem on the closed orthant. -/
  | cutvertex : CutData → PTree
  /-- `USE k cert…`: cite the earlier named subtree `k`, re-deriving each of its
  entry forms from the context accumulated here. -/
  | use : ℕ → List Cert → PTree
  /-- `ABSURD cert`: the accumulated context is contradictory — `cert` derives
  `−1 ≥ 0` from it — so this cell is empty and there is nothing to prove. -/
  | absurd : Cert → PTree

/-- The tree checker, in scope of the entry contexts `E` of the subtrees this
node may cite.  One `Bool` for the whole proof. -/
def PTree.checksIn {n p : ℕ} (m : ℕ) (core : ExplicitPotential.Core n p)
    (degree : ℤ) (E : List (List Form)) (Γ : Context) : PTree → Bool
  | .leaf w => w.leafChecks m core Γ degree
  | .richLeaf w => w.richLeafChecks m core Γ degree
  | .split g a b =>
      PTree.checksIn m core degree E (Γ.pushGe g) a &&
        PTree.checksIn m core degree E (Γ.pushGe (negForm g)) b
  | .auto d t =>
      if hp : 0 < p then
        decide (m = p) && d.checks core &&
          PTree.checksIn m core degree E (d.pullbackContext hp Γ) t
      else false
  | .cutvertex d => d.checks core degree
  | .use k certs =>
      match lookupEntry E k with
      | none => false
      | some entry => entryChecks Γ entry certs
  | .absurd w => w.check Γ falseForm

/-- The tree checker with no subtrees in scope: every `use` is then a reject.
This is the shape every row lowered before `use` existed still uses. -/
def PTree.checks {n p : ℕ} (m : ℕ) (core : ExplicitPotential.Core n p)
    (degree : ℤ) (Γ : Context) (t : PTree) : Bool :=
  PTree.checksIn m core degree [] Γ t

/-- An ordered list of named subtrees, each with its entry context, and the main
tree.  Subtree `i` is checked with `E = ` the entries of subtrees `0 … i−1`
only, which is `rpfcheck.c`'s earlier-only rule and what keeps the recursion
well-founded. -/
structure PProof where
  /-- `(entry, body)` per named subtree, in declaration order. -/
  subs : List (List Form × PTree)
  /-- The main tree, which may cite every subtree. -/
  main : PTree

/-- Check the subtrees in order, each in scope of its predecessors' entries. -/
def subsCheck {n p : ℕ} (m : ℕ) (core : ExplicitPotential.Core n p) (degree : ℤ) :
    List (List Form) → List (List Form × PTree) → Bool
  | _, [] => true
  | acc, (entry, t) :: rest =>
      PTree.checksIn m core degree acc (subContext p entry) t &&
        subsCheck m core degree (acc ++ [entry]) rest

/-- The whole-proof checker: the subtrees, then the main tree in scope of all
of them. -/
def PProof.checks {n p : ℕ} (m : ℕ) (core : ExplicitPotential.Core n p)
    (degree : ℤ) (Γ : Context) (P : PProof) : Bool :=
  subsCheck m core degree [] P.subs &&
    PTree.checksIn m core degree (P.subs.map Prod.fst) Γ P.main

section Sound

variable {n p m : ℕ} (core : ExplicitPotential.Core n p) (degree : ℤ)

/-- **A checked `cutvertex` node is sound**, by the closed-orthant port of the
genus-four vertex-cut gluing theorem.  No context is consumed: the conclusion
holds on the whole closed orthant, so a fortiori on the node's chamber. -/
theorem CutData.sound (d : CutData) (hn : 0 < n)
    (hchk : d.checks core degree = true)
    (ℓ : Fin p → ℕ) (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree := by
  rw [CutData.checks, dif_pos hn] at hchk
  by_cases hp : 0 < p
  · rw [dif_pos hp, Bool.and_eq_true, Bool.and_eq_true] at hchk
    obtain ⟨⟨hdeg, hLoop⟩, hCheck⟩ := hchk
    have hdeg' : degree = 3 := of_decide_eq_true hdeg
    subst hdeg'
    refine bnExists_censusSpec_of_genusFourRankOneCheck core hn
      (d.toCut core hn) (d.toTree core hn hp) (fun e => ?_) hCheck ℓ hForest
      hNotLoopy
    exact of_decide_eq_true ((ExplicitPotential.allFin_eq_true_iff _).mp hLoop e)
  · rw [dif_neg hp] at hchk
    exact absurd hchk (by simp)

/-- The root domain rows hold at any point whose first `p` coordinates are the
lengths — the half of a subtree's entry context that costs nothing. -/
theorem rootRows_holds (hp : p ≤ m) (point : Fin m → ℤ) (ℓ : Fin p → ℕ)
    (hlen : ∀ e : Fin p, (ℓ e : ℤ) = point (Fin.castLE hp e))
    {g : Form} (hg : g ∈ (List.range p).map coordForm) :
    0 ≤ eval g (List.ofFn point) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  have hip : i < p := List.mem_range.mp hi
  have him : i < m := lt_of_lt_of_le hip hp
  have h := eval_coordForm_ofFn point ⟨i, him⟩
  have hcast : (⟨i, him⟩ : Fin m) = Fin.castLE hp ⟨i, hip⟩ := rfl
  rw [show ((⟨i, him⟩ : Fin m)).val = i from rfl] at h
  rw [h, hcast, ← hlen ⟨i, hip⟩]
  exact Int.natCast_nonneg _

/-- A subtree's context holds at the point as soon as its declared entry forms
do: the root domain rows are free, by `rootRows_holds`. -/
theorem subContext_holds (hp : p ≤ m) (point : Fin m → ℤ) (ℓ : Fin p → ℕ)
    (hlen : ∀ e : Fin p, (ℓ e : ℤ) = point (Fin.castLE hp e))
    {entry : List Form} (hentry : ∀ g ∈ entry, 0 ≤ eval g (List.ofFn point)) :
    (subContext p entry).Holds (List.ofFn point) := by
  refine ⟨?_, by simp [subContext]⟩
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact rootRows_holds hp point ℓ hlen h
  · exact hentry g h

/-- **The tree is sound.**

Every branch of an accepted tree ends in an accepted leaf whose context holds
at the point, or in an `ABSURD` node whose context holds at no point at all.
The two `SPLIT` branches are exhaustive over `ℤ`, which is the coverage
argument of spec §4.2 and the only place it is used.

The extra hypothesis `hE` is the induction's account of `USE`: every entry
context in scope is one whose satisfaction already yields the goal.  A `use`
node consumes it by re-deriving that entry context here, which is the context
weakening spec §4.2 asks of a citation and nothing more. -/
theorem PTree.sound (hp : p ≤ m) (hn : 0 < n) (point : Fin m → ℤ)
    (ℓ : Fin p → ℕ) (hlen : ∀ e : Fin p, (ℓ e : ℤ) = point (Fin.castLE hp e))
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    ∀ (t : PTree) (E : List (List Form)) (Γ : Context),
      (∀ entry ∈ E, ∀ (ℓ' : Fin p → ℕ)
        (hForest' : IsForest core (zeroSet ℓ'))
        (hNotLoopy' : ¬ IsLoopy core (zeroSet ℓ')) (point' : Fin m → ℤ)
        (_hlen' : ∀ e : Fin p, (ℓ' e : ℤ) = point' (Fin.castLE hp e)),
        (subContext p entry).Holds (List.ofFn point') →
        BNExists (censusSpec core hn ℓ' hForest' hNotLoopy').graph 1 degree) →
      PTree.checksIn m core degree E Γ t = true → Γ.Holds (List.ofFn point) →
      BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree := by
  intro t
  induction t generalizing m point ℓ with
  | leaf w =>
      intro E Γ _ hchk hΓ
      exact leaf_sound core w Γ degree hp hn hchk point hΓ ℓ hlen hForest hNotLoopy
  | richLeaf w =>
      intro E Γ _ hchk hΓ
      exact RichWitness.richLeaf_sound core w Γ degree hp hn hchk point hΓ ℓ hlen hForest hNotLoopy
  | split g a b iha ihb =>
      intro E Γ hE hchk hΓ
      rw [PTree.checksIn, Bool.and_eq_true] at hchk
      rcases le_or_gt 0 (eval g (List.ofFn point)) with hg | hg
      · exact iha (hp := hp) (point := point) (ℓ := ℓ) (hlen := hlen)
          (hForest := hForest) (hNotLoopy := hNotLoopy) _ _ hE hchk.1
          (Context.pushGe_holds hΓ hg)
      · refine ihb (hp := hp) (point := point) (ℓ := ℓ) (hlen := hlen)
          (hForest := hForest) (hNotLoopy := hNotLoopy) _ _ hE hchk.2
          (Context.pushGe_holds hΓ ?_)
        rw [eval_negForm]
        omega
  | auto d t iht =>
      intro E Γ hE hchk hΓ
      rw [PTree.checksIn] at hchk
      by_cases hp0 : 0 < p
      · rw [dif_pos hp0, Bool.and_eq_true, Bool.and_eq_true] at hchk
        have hmp : m = p := of_decide_eq_true hchk.1.1
        subst m
        let symmetry := d.toSymmetry core hn hp0 hchk.1.2
        let ℓ' := symmetry.reindexLength ℓ
        have hForest' : IsForest core (zeroSet ℓ') :=
          (ClosedAuto.isForest_iff symmetry ℓ).2 hForest
        have hNotLoopy' : ¬ IsLoopy core (zeroSet ℓ') := fun h =>
          hNotLoopy ((ClosedAuto.isLoopy_iff symmetry ℓ).1 h)
        have hpnt : point = fun e => (ℓ e : ℤ) := by
          funext e
          exact (hlen e).symm
        subst point
        have hΓ' : (d.pullbackContext hp0 Γ).Holds
            (List.ofFn fun e => (ℓ' e : ℤ)) :=
          d.pullbackContext_holds core hn hp0 hchk.1.2 hΓ
        have htarget := iht (hp := le_rfl) (point := fun e => (ℓ' e : ℤ))
          (ℓ := ℓ') (hlen := fun _ => rfl) (hForest := hForest')
          (hNotLoopy := hNotLoopy') E (d.pullbackContext hp0 Γ) hE hchk.2 hΓ'
        exact (ClosedAuto.bnExists_iff symmetry ℓ hn hForest hNotLoopy 1 degree).mp htarget
      · rw [dif_neg hp0] at hchk
        exact _root_.absurd hchk (by simp)
  | cutvertex d =>
      intro E Γ _ hchk _
      rw [PTree.checksIn] at hchk
      exact CutData.sound core degree d hn hchk ℓ hForest hNotLoopy
  | «use» k certs =>
      intro E Γ hE hchk hΓ
      rw [PTree.checksIn] at hchk
      revert hchk
      cases hlookup : lookupEntry E k with
      | none => intro h; exact _root_.absurd h (by simp)
      | some entry =>
          intro hchk
          refine hE entry (lookupEntry_mem hlookup) ℓ hForest hNotLoopy point hlen
            (subContext_holds hp point ℓ hlen ?_)
          exact entryChecks_sound hΓ hchk
  | «absurd» w =>
      -- The context entails `−1 ≥ 0`, so no point satisfies it — least of all
      -- this one.  The goal follows from `False`.
      intro E Γ _ hchk hΓ
      rw [PTree.checksIn] at hchk
      have h : (0 : ℤ) ≤ eval falseForm (List.ofFn point) := Cert.check_sound hchk hΓ
      rw [eval_falseForm] at h
      exact _root_.absurd h (by decide)

/-- **The subtree list is sound**, processed in order.

Each subtree is checked in scope of its predecessors' entry contexts only, so
the accumulated soundness fact grows by one entry at a time and never appeals
to a subtree that has not yet been proved.  This is where `rpfcheck.c`'s
"`use` must reference an earlier subtree" is paid for. -/
theorem subsCheck_sound (hp : p ≤ m) (hn : 0 < n) :
    ∀ (subs : List (List Form × PTree)) (acc : List (List Form)),
      (∀ entry ∈ acc, ∀ (ℓ : Fin p → ℕ)
        (hForest : IsForest core (zeroSet ℓ))
        (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) (point : Fin m → ℤ)
        (_hlen : ∀ e : Fin p, (ℓ e : ℤ) = point (Fin.castLE hp e)),
        (subContext p entry).Holds (List.ofFn point) →
        BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree) →
      subsCheck m core degree acc subs = true →
      ∀ entry ∈ acc ++ subs.map Prod.fst, ∀ (ℓ : Fin p → ℕ)
        (hForest : IsForest core (zeroSet ℓ))
        (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) (point : Fin m → ℤ)
        (_hlen : ∀ e : Fin p, (ℓ e : ℤ) = point (Fin.castLE hp e)),
        (subContext p entry).Holds (List.ofFn point) →
        BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree := by
  intro subs
  induction subs with
  | nil => intro acc hacc _; simpa using hacc
  | cons st rest ih =>
      obtain ⟨entry, t⟩ := st
      intro acc hacc hchk
      rw [subsCheck, Bool.and_eq_true] at hchk
      have hentry : ∀ (ℓ : Fin p → ℕ)
          (hForest : IsForest core (zeroSet ℓ))
          (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) (point : Fin m → ℤ)
          (hlen : ∀ e : Fin p, (ℓ e : ℤ) = point (Fin.castLE hp e)),
          (subContext p entry).Holds (List.ofFn point) →
          BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree := by
        intro ℓ hForest hNotLoopy point hlen hctx
        exact PTree.sound core degree hp hn point ℓ hlen hForest hNotLoopy
          t acc _ hacc hchk.1 hctx
      have hacc' : ∀ e ∈ acc ++ [entry], ∀ (ℓ : Fin p → ℕ)
          (hForest : IsForest core (zeroSet ℓ))
          (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) (point : Fin m → ℤ)
          (_hlen : ∀ edge : Fin p, (ℓ edge : ℤ) = point (Fin.castLE hp edge)),
          (subContext p e).Holds (List.ofFn point) →
          BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree := by
        intro e he
        rcases List.mem_append.mp he with h | h
        · exact hacc e h
        · rw [List.mem_singleton.mp h]; exact hentry
      have := ih (acc ++ [entry]) hacc' hchk.2
      simpa using this

end Sound

/-- **The row obligation for a `(domain closed)` proof, verbatim.**

An accepted tree at the closed root proves the goal on every face of the closed
length orthant whose vanishing set is a non-loopy forest — that is, on every
subdivision of the core *and* every equal-genus contraction of one.  Compare
spec §3 and `AllMarksCoreCase.SolvedAllMarksClosedCensus`. -/
theorem tree_sound_closed_root {n p : ℕ} (core : ExplicitPotential.Core n p)
    (t : PTree) (degree : ℤ) (hn : 0 < n)
    (hchk : PTree.checks p core degree (rootContextClosed p) t = true)
    (ℓ : Fin p → ℕ)
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree :=
  PTree.sound core degree le_rfl hn (fun e : Fin p => (ℓ e : ℤ)) ℓ (fun _ => rfl)
    hForest hNotLoopy t [] _ (by simp) hchk (rootContextClosed_holds ℓ)

/-- **The row obligation for a `(domain closed)` proof with named subtrees.**

Same conclusion as `tree_sound_closed_root`, for a proof whose cells cite shared
subtrees by `use`.  The subtrees are discharged first, in order; the main tree
is then checked with all of them in scope. -/
theorem proof_sound_closed_root {n p : ℕ} (core : ExplicitPotential.Core n p)
    (P : PProof) (degree : ℤ) (hn : 0 < n)
    (hchk : PProof.checks p core degree (rootContextClosed p) P = true)
    (ℓ : Fin p → ℕ)
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree := by
  rw [PProof.checks, Bool.and_eq_true] at hchk
  have hE := subsCheck_sound core degree le_rfl hn P.subs [] (by simp) hchk.1
  simp only [List.nil_append] at hE
  exact PTree.sound core degree le_rfl hn (fun e : Fin p => (ℓ e : ℤ)) ℓ
    (fun _ => rfl) hForest hNotLoopy P.main _ _ hE hchk.2
    (rootContextClosed_holds ℓ)

end Utilities.Subdivision.ClosedRowProof
