/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.Arith
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSpecCensus

/-!
# `leaf_sound`: the row-proof leaf, lowered to Lean

This is step B of the proof-data source.  A `LEAF` node of a row proof carries a
local witness (spec §4.3); this file turns an accepted witness into
`BNExists … 1 d` on the degenerate subdivision determined by *any* length
vector whose vanishing set is a non-loopy forest.

## Representation discipline

Every generated form is a `List ℤ` addressed with `List.getD`, as in
the corresponding closed-row proof module.  `§1` below is the only place where a form is turned
into the `Fin`-indexed `ExplicitPotential.AffineForm` the existing certificate
layer speaks: `toAffineForm` reads the coefficients out of the list with
`getD`, so no `![…]` and no `Matrix.cons` ever appears.

## Where the soundness hazard is discharged

`RESULTS.md` §9 records that on a core carrying a loop the core vertices are
*not* rank determining, so the strong-separator step is unsound there.  In
this file that hazard is discharged in exactly one place: `censusSpec`'s
`rep_loopless` field, which is supplied by the row obligation's own
`¬ IsLoopy` census hypothesis through
`ContractionForestCensusGeneral.rep_loopless_of_not_isLoopy`.  Every
downstream separator fact (`DegSpec.strongSeparatorCertificate`) is
hypothesis-free precisely *because* a `DegSpec` cannot be built without that
field.  Dropping `hNotLoopy` from `leaf_sound` is therefore not possible: the
conclusion does not typecheck without it.

## What the checker accepts, and what it deliberately refuses

`Witness` is the spec's §4.3 record verbatim (chips, a block list per slot,
head/tail slack).  `Witness.leafChecks` is **fail-closed** on the parts of
that record whose Lean support does not exist yet:

* it requires `chips = []`, and
* it requires exactly one block per slot (`k_e = 1`),

so that no named interior point ever arises.  With `k_e = 1` there are no
interior named points, W1's slack and W4's interior residual are vacuous, and
W5 collapses to the per-core-vertex integer test `ValidClosed` already makes.

This is not a toy restriction: it is exactly the leaf the implemented
generator emits.  the proof-data source's `verify_leaf` checks precisely
`lo_e ≤ hi_e`, `lo_e·ℓ_e ≤ F(head e) − F(tail e) ≤ hi_e·ℓ_e`, and the core
residual, and all four leaves in the proof-data source (`banana3`,
`g4row002`, `g4row010`, `g4row011`) have `(chips)` empty and one `(b …)` per
slot.  The multi-block half of §4.3 is unexercised by every accepted proof in
the catalog; see the note at the end of this file for what it would cost.
-/

@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open Finset
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral

/-! ## §1  From a `List ℤ` form to an `AffineForm`

`eval g x = dot g (1 :: x)` truncates at the shorter list, which is what makes
the translation unconditional: a form longer than `m + 1` has its tail ignored
on both sides. -/

theorem dot_eq_sum_range (l r : List ℤ) :
    dot l r = ∑ i ∈ Finset.range r.length, l.getD i 0 * r.getD i 0 := by
  induction r generalizing l with
  | nil => simp
  | cons b bs ih =>
      cases l with
      | nil => simp
      | cons a as =>
          rw [List.length_cons, Finset.sum_range_succ']
          simp only [List.getD_cons_succ, List.getD_cons_zero, dot]
          rw [ih as]
          ring

/-- A `List ℤ` form, read as an `AffineForm m`: the head is the constant and
entry `i + 1` is the coefficient of coordinate `i`. -/
def toAffineForm (m : ℕ) (g : Form) : ExplicitPotential.AffineForm m where
  fixedValue := g.getD 0 0
  coefficient := fun i => g.getD (i.val + 1) 0

theorem eval_toAffineForm {m : ℕ} (g : Form) (point : Fin m → ℤ) :
    (toAffineForm m g).eval point = eval g (List.ofFn point) := by
  have hget : ∀ (i : ℕ) (hi : i < m), (List.ofFn point).getD i 0 = point ⟨i, hi⟩ := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  rw [eval, dot_eq_sum_range]
  simp only [List.length_cons, List.length_ofFn]
  rw [Finset.sum_range_succ']
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  have hsum : ∑ i ∈ Finset.range m, g.getD (i + 1) 0 * (List.ofFn point).getD i 0
      = ∑ i : Fin m, g.getD (i.val + 1) 0 * point i := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => g.getD (i + 1) 0 * (List.ofFn point).getD i 0) m]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hget i.val i.isLt]
  rw [hsum]
  simp only [AffineCover.AffineForm.eval, toAffineForm]
  ring

/-- A passive affine-cover cell supplies exactly the inequality half of a
row-proof context.  This is the generic bridge used by generated conditional
rich-plan covers; no coordinate is assumed to be a graph length here. -/
theorem contextHolds_of_formsHold_toAffineForm {m : ℕ}
    (ge : List Form) (point : Fin m → ℤ)
    (hForms : AffineCover.FormsHold (ge.map (toAffineForm m)) point) :
    (⟨ge, []⟩ : Context).Holds (List.ofFn point) := by
  constructor
  · intro form hForm
    have hAffine := hForms (toAffineForm m form)
      (List.mem_map.mpr ⟨form, hForm, rfl⟩)
    simpa only [AffineCover.AffineForm.Holds, eval_toAffineForm] using hAffine
  · simp

/-! ### The coordinate forms -/

/-- The form `x_e`, as a `List ℤ`: entry `e + 1` is `1` and the rest are `0`. -/
def coordForm (e : ℕ) : Form := List.replicate (e + 1) 0 ++ [1]

private theorem dot_replicate_append (e : ℕ) (x : List ℤ) :
    dot (List.replicate e 0 ++ [1]) x = x.getD e 0 := by
  induction e generalizing x with
  | zero =>
      cases x with
      | nil => simp
      | cons a as => simp [dot]
  | succ k ih =>
      cases x with
      | nil => simp
      | cons a as =>
          simp only [List.replicate_succ, List.cons_append, dot, ih as,
            List.getD_cons_succ]
          ring

@[simp] theorem eval_coordForm (e : ℕ) (x : List ℤ) :
    eval (coordForm e) x = x.getD e 0 := by
  simp only [eval, coordForm, List.replicate_succ, List.cons_append, dot]
  rw [dot_replicate_append]
  ring

theorem eval_coordForm_ofFn {m : ℕ} (point : Fin m → ℤ) (e : Fin m) :
    eval (coordForm e.val) (List.ofFn point) = point e := by
  rw [eval_coordForm, List.getD_eq_getElem _ _ (by simp)]
  simp

/-! ## §2  The leaf witness, spec §4.3

The record is the specification's, verbatim; the *checker* is what refuses the
half of it that has no Lean support (see the module docstring). -/

/-- One block of a slot script: over the stretch ending at `endForm` the script
rises by `rise`, its first unit slope is at least `lo` and its last at most
`hi`.  This is `rowproof`'s `(b end rise lo hi)`. -/
structure Block where
  /-- The affine form naming the right end of the stretch. -/
  endForm : Form
  /-- The affine form naming the total rise across the stretch. -/
  rise : Form
  /-- Lower bound on the first unit slope. -/
  lo : ℤ
  /-- Upper bound on the last unit slope. -/
  hi : ℤ

/-- The out-of-range block: every check on it fails. -/
def Block.dflt : Block := ⟨[], [], 1, 0⟩

/-- The firing script attached to one anchor: a potential at each core vertex,
a block list per slot, the declared endpoint slacks of W1, and the entailment
certificates for the two realizability rows of §13.1. -/
structure AnchorPlan where
  /-- One form per core vertex. -/
  potential : List Form
  /-- One nonempty block list per slot. -/
  blocks : List (List Block)
  /-- `α_e` of W1. -/
  headSlack : List ℕ
  /-- `ω_e` of W1. -/
  tailSlack : List ℕ
  /-- Per slot, a certificate of `rise_e − lo_e·σ_e ≥ 0`. -/
  loCert : List Cert
  /-- Per slot, a certificate of `hi_e·σ_e − rise_e ≥ 0`. -/
  hiCert : List Cert

/-- The out-of-range plan. -/
def AnchorPlan.dflt : AnchorPlan := ⟨[], [], [], [], [], []⟩

/-- The out-of-range certificate: `k = 0` fails `1 ≤ k`, so lookups past the
end of a certificate list are fail-closed. -/
def Cert.dflt : Cert := ⟨0, [], [], 0⟩

/-! ### Rich multi-block leaf data

`Witness` below is retained for the already-generated one-block catalog.  The
full RPF leaf has more receipts than that compact record can carry, so the
multi-block path uses a separate record rather than adding required fields to
`AnchorPlan` and invalidating every existing generated module.  `PTree` will
gain the corresponding leaf constructor once `richLeafChecks` and its
soundness theorem are assembled below.
-/

/-- The three local entailment receipts for a block: its length is
nonnegative, and its declared rise lies between the endpoint-slope bounds. -/
structure RichBlockCert where
  /-- Entailment receipt asserting that the block endpoint is no earlier than its starting
  point. -/
  monotone : Cert
  /-- Entailment receipt for the lower realizability inequality: the declared rise is at least
  the lower slope bound times the block length. -/
  lower : Cert
  /-- Entailment receipt for the upper realizability inequality: the declared rise is at most
  the upper slope bound times the block length. -/
  upper : Cert

/-- Missing rich receipts fail closed because every constituent default has
`k = 0`. -/
def RichBlockCert.dflt : RichBlockCert := ⟨Cert.dflt, Cert.dflt, Cert.dflt⟩

/-- A firing plan with all data required by RPF W1--W5.  The outer list indices
are slots and inner indices are block numbers; `separationCert e i j` is the
strict W4 receipt for the run beginning at C-index `i` and ending at `j`.
The lowerer synthesises every receipt with the existing exact Farkas engine. -/
structure RichAnchorPlan where
  /-- Affine potential values indexed by core vertex for this anchor firing plan. -/
  potential : List Form
  /-- The ordered interpolation blocks on each slot, with outer indices naming slots and inner
  indices naming blocks. -/
  blocks : List (List Block)
  /-- The per-slot W1 parameter α, bounding the initial named points allowed to coincide with
  the tail endpoint. -/
  headSlack : List ℕ
  /-- The per-slot W1 parameter ω, bounding the final named points allowed to coincide with the
  head endpoint. -/
  tailSlack : List ℕ
  /-- Per-slot, per-block receipts for nonnegative block length and the two rise bounds. -/
  blockCert : List (List RichBlockCert)
  /-- Per-slot strict-positivity receipts placing the first point beyond the allowed tail slack
  after the tail. -/
  tailSlackCert : List Cert
  /-- Per-slot strict-positivity receipts placing the last point before the allowed head slack
  before the head. -/
  headSlackCert : List Cert
  /-- Strict separation receipts indexed by slot and the first and last named-point indices of a
  W4 run. -/
  separationCert : List (List (List Cert))

/-- The empty fallback plan used when an anchor index is absent from a rich witness. -/
def RichAnchorPlan.dflt : RichAnchorPlan :=
  ⟨[], [], [], [], [], [], [], []⟩

/-- The full multi-block/chip RPF leaf.  This is deliberately distinct from
the old `Witness`, so the existing single-block generated modules remain
byte-compatible while new lowering selects the rich soundness path. -/
structure RichWitness where
  /-- The divisor coefficients at the original core vertices, indexed by vertex number. -/
  divisorCore : List ℤ
  /-- Named slot chips as triples of slot index, affine position form, and signed integer
  coefficient. -/
  chips : List (ℕ × Form × ℤ)
  /-- One rich firing plan for each core-vertex anchor. -/
  anchors : List RichAnchorPlan
  /-- Per-slot entailment receipts establishing nonnegative slot length from the ambient
  context. -/
  slotCert : List Cert

namespace RichWitness

variable (w : RichWitness)

/-- Look up the rich firing plan for an anchor, returning the empty default plan for an absent
entry. -/
def plan (a : ℕ) : RichAnchorPlan := w.anchors.getD a RichAnchorPlan.dflt
/-- Read an anchor plan’s potential at a core vertex, using the zero affine form for a missing
entry. -/
def pot (a v : ℕ) : Form := (w.plan a).potential.getD v []
/-- Read the ordered block list for an anchor and slot, using an empty list when it is absent. -/
def blockList (a e : ℕ) : List Block := (w.plan a).blocks.getD e []
/-- Read a specified interpolation block, using the default block with inconsistent slope bounds
for a missing entry. -/
def block (a e i : ℕ) : Block := (w.blockList a e).getD i Block.dflt
/-- Read an anchor’s receipts for a slot and block, falling back to the default rich block
certificate. -/
def blockReceipt (a e i : ℕ) : RichBlockCert :=
  ((w.plan a).blockCert.getD e []).getD i RichBlockCert.dflt
/-- Read the strict separation receipt for a run of named points, indexed by anchor, slot, and
run endpoints. -/
def separationReceipt (a e i j : ℕ) : Cert :=
  (((w.plan a).separationCert.getD e []).getD i []).getD j Cert.dflt

end RichWitness

/-- The local witness carried by a `LEAF` node. -/
structure Witness where
  /-- The divisor's coefficient at each core vertex. -/
  divisorCore : List ℤ
  /-- Chips in slot interiors: `(slot, position form, coefficient)`. -/
  chips : List (ℕ × Form × ℤ)
  /-- One plan per core vertex, since the anchors are the core classes. -/
  anchors : List AnchorPlan
  /-- Per slot, a certificate of `σ_e ≥ 0` from the ambient context. -/
  slotCert : List Cert

namespace Witness

variable (w : Witness)

/-- The plan of anchor `a`. -/
def plan (a : ℕ) : AnchorPlan := w.anchors.getD a AnchorPlan.dflt

/-- The potential of anchor `a` at core vertex `v`. -/
def pot (a v : ℕ) : Form := (w.plan a).potential.getD v []

/-- The block list of anchor `a` on slot `e`. -/
def blockList (a e : ℕ) : List Block := (w.plan a).blocks.getD e []

/-- The first (and, once `leafChecks` accepts, only) block of slot `e`. -/
def block (a e : ℕ) : Block := (w.blockList a e).getD 0 Block.dflt

end Witness

/-! ## §3  The certificate a witness denotes

`ExplicitPotential.Certificate` is the existing arithmetic record; a
single-block leaf is exactly one, with `α_e = lo_e` and `β_e = −hi_e`.  The
cone is *synthesised* here rather than transcribed: it holds precisely the
rows the semantics needs, and `FormsHold` for them is discharged by the
entailment layer of the corresponding closed-row proof module, not by cone membership. -/

variable {m n p : ℕ}

/-- The row `rise_e − lo_e·σ_e ≥ 0`, written so that it is *definitionally*
`(leafCertificate …).lowerForm`. -/
def leafLowerForm (m : ℕ) (core : ExplicitPotential.Core n p) (w : Witness)
    (a : Fin n) (e : Fin p) : ExplicitPotential.AffineForm m :=
  ExplicitPotential.AffineForm.sub
    (ExplicitPotential.AffineForm.sub
      (toAffineForm m (w.pot a.val (core.head e).val))
      (toAffineForm m (w.pot a.val (core.tail e).val)))
    (ExplicitPotential.AffineForm.scale (w.block a.val e.val).lo
      (toAffineForm m (coordForm e.val)))

/-- The row `hi_e·σ_e − rise_e ≥ 0`, written so that it is *definitionally*
`(leafCertificate …).upperForm`. -/
def leafUpperForm (m : ℕ) (core : ExplicitPotential.Core n p) (w : Witness)
    (a : Fin n) (e : Fin p) : ExplicitPotential.AffineForm m :=
  ExplicitPotential.AffineForm.sub
    (ExplicitPotential.AffineForm.scale (-(-(w.block a.val e.val).hi))
      (toAffineForm m (coordForm e.val)))
    (ExplicitPotential.AffineForm.sub
      (toAffineForm m (w.pot a.val (core.head e).val))
      (toAffineForm m (w.pot a.val (core.tail e).val)))

/-- The synthesised cone: the slot lengths and, per anchor and slot, the two
realizability rows. -/
def leafCone (m : ℕ) (core : ExplicitPotential.Core n p) (w : Witness) :
    List (ExplicitPotential.AffineForm m) :=
  (List.finRange p).map (fun e => toAffineForm m (coordForm e.val)) ++
    (List.finRange n).flatMap (fun a =>
      (List.finRange p).flatMap (fun e =>
        [leafLowerForm m core w a e, leafUpperForm m core w a e]))

/-- The explicit-potential certificate a single-block leaf denotes. -/
def leafCertificate (m : ℕ) (core : ExplicitPotential.Core n p) (w : Witness) :
    ExplicitPotential.Certificate m n p where
  core := core
  segment := fun e => toAffineForm m (coordForm e.val)
  divisor := fun v => w.divisorCore.getD v.val 0
  witness := fun a =>
    { alpha := fun e => (w.block a.val e.val).lo
      beta := fun e => -(w.block a.val e.val).hi
      potential := fun v => toAffineForm m (w.pot a.val v.val) }
  cone := leafCone m core w

theorem leafCertificate_lowerForm (core : ExplicitPotential.Core n p) (w : Witness)
    (a : Fin n) (e : Fin p) :
    (leafCertificate m core w).lowerForm a e = leafLowerForm m core w a e := rfl

theorem leafCertificate_upperForm (core : ExplicitPotential.Core n p) (w : Witness)
    (a : Fin n) (e : Fin p) :
    (leafCertificate m core w).upperForm a e = leafUpperForm m core w a e := rfl

/-! ## §4  The Boolean leaf checker -/

/-- **The leaf checker.**  `Γ` is the context the tree layer has accumulated at
this node; `degree` is the goal's degree.

Restrictions, both fail-closed and both deliberate: no chips, and exactly one
block per slot.  See the module docstring. -/
def Witness.leafChecks (w : Witness) (m : ℕ) (core : ExplicitPotential.Core n p)
    (Γ : Context) (degree : ℤ) : Bool :=
  -- the row itself: a loopless, connected core
  ExplicitPotential.allFin (fun e : Fin p => decide (core.tail e ≠ core.head e)) &&
  core.connectedCheck &&
  -- shape restriction
  w.chips.isEmpty &&
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
    decide ((w.blockList a.val e.val).length = 1)) &&
  -- W1: the one block ends at the head of the slot
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
    formEq (w.block a.val e.val).endForm (coordForm e.val)) &&
  -- W2 closure: the declared rise is the potential difference
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
    formEq (w.block a.val e.val).rise
      (subForm (w.pot a.val (core.head e).val) (w.pot a.val (core.tail e).val))) &&
  -- W2 realizability (§13.1), entailed from Γ: `lo_e·σ_e ≤ rise_e ≤ hi_e·σ_e`
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
    ((w.plan a.val).loCert.getD e.val Cert.dflt).check Γ
      (subForm (w.block a.val e.val).rise
        (smulForm (w.block a.val e.val).lo (coordForm e.val)))) &&
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
    ((w.plan a.val).hiCert.getD e.val Cert.dflt).check Γ
      (subForm (smulForm (w.block a.val e.val).hi (coordForm e.val))
        (w.block a.val e.val).rise)) &&
  -- the slot lengths are nonnegative on Γ (implicit rule I1 at the root)
  ExplicitPotential.allFin (fun e : Fin p =>
    (w.slotCert.getD e.val Cert.dflt).check Γ (coordForm e.val)) &&
  -- `lo_e ≤ hi_e`
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
    decide ((w.block a.val e.val).lo ≤ (w.block a.val e.val).hi)) &&
  -- W5, the core residual
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun v : Fin n =>
    decide (0 ≤ (leafCertificate m core w).targetCoefficient a v +
      (leafCertificate m core w).lowerEndpointContribution a v)) &&
  -- W7, the degree
  decide ((∑ v : Fin n, w.divisorCore.getD v.val 0) = degree)

/-! ## §5  The degenerate subdivision determined by a length vector

This is where the soundness hazard of `RESULTS.md` §9 is discharged: the
`rep_loopless` field below is supplied by `hNotLoopy` and by nothing else. -/

/-- The vanishing set of a length vector. -/
def zeroSet {p : ℕ} (ℓ : Fin p → ℕ) : Finset (Fin p) :=
  Finset.univ.filter (fun e => ℓ e = 0)

/-- **The row obligation's target object.**  The degenerate subdivision of
`core` at lengths `ℓ`, given the two census hypotheses of spec §3.

`hForest` is genus preservation and `hNotLoopy` is looplessness of the
contracted core — which is exactly what the strong-separator step needs, and
is why `DegSpec.strongSeparatorCertificate` can be hypothesis-free. -/
def censusSpec (core : ExplicitPotential.Core n p) (hn : 0 < n) (ℓ : Fin p → ℕ)
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    Utilities.Certificate.DegenerateSpec.DegSpec n p where
  core := core
  length := ℓ
  core_nonempty := hn
  rep := compFold core (zeroSet ℓ)
  rep_idem := compFold_idem core (zeroSet ℓ)
  rep_zero := fun e he =>
    compFold_tail_eq_head_of_mem core (by simp [zeroSet, he])
  rep_loopless := fun e he =>
    rep_loopless_of_not_isLoopy core hNotLoopy e (by simp [zeroSet]; omega)
  forest := forest_image_add_card_eq core hForest

/-- Two degenerate specs with the same core, lengths and representative map are
equal; the remaining fields are `Prop`s. -/
theorem DegSpec.ext'
    {d d' : Utilities.Certificate.DegenerateSpec.DegSpec n p}
    (hc : d.core = d'.core) (hl : d.length = d'.length) (hr : d.rep = d'.rep) :
    d = d' := by
  obtain ⟨c, l, _, r, _, _, _, _⟩ := d
  obtain ⟨c', l', _, r', _, _, _, _⟩ := d'
  simp only at hc hl hr
  subst hc; subst hl; subst hr
  rfl

/-! ## §6  `leaf_sound` -/

section LeafSound

variable (core : ExplicitPotential.Core n p) (w : Witness) (Γ : Context) (degree : ℤ)

/-- **The leaf is sound.**

If `leafChecks` accepts the witness against the context `Γ`, then at *every*
integral point of `Γ` the goal `BNExists … 1 degree` holds on the degenerate
subdivision determined by the induced length vector, for every length vector
whose vanishing set is a non-loopy forest.

Provenance of the hypotheses:

* `hp`, `hlen` — the format's own convention that coordinate `e` *is* the
  length of slot `e` (spec §4.1);
* `hn` — needed to state the conclusion at all (`DegSpec.core_nonempty`);
* `hchk` — the Boolean leaf checker;
* `hΓ` — the context holds at the point; supplied by the tree layer, and
  trivial at the closed root (see `leaf_sound_closed_root`);
* `hForest`, `hNotLoopy` — the two census hypotheses of spec §3, inputs to the
  row obligation.  `hNotLoopy` is the one that pays for the
  rank-determining-set step; see `censusSpec`. -/
theorem leaf_sound (hp : p ≤ m) (hn : 0 < n)
    (hchk : w.leafChecks m core Γ degree = true)
    (point : Fin m → ℤ) (hΓ : Γ.Holds (List.ofFn point))
    (ℓ : Fin p → ℕ) (hlen : ∀ e : Fin p, (ℓ e : ℤ) = point (Fin.castLE hp e))
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree := by
  classical
  simp only [Witness.leafChecks, Bool.and_eq_true, decide_eq_true_eq,
    ExplicitPotential.allFin_eq_true_iff, List.isEmpty_iff] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hLoopless, hConn⟩, _hChips⟩, _hOneBlock⟩, _hW1⟩, hW2⟩, hLoCert⟩,
    hHiCert⟩, hSlotCert⟩, hLoHi⟩, hW5⟩, hW7⟩ := hchk
  -- Abbreviations.
  have hx : ∀ e : Fin m, eval (coordForm e.val) (List.ofFn point) = point e :=
    eval_coordForm_ofFn point
  have hxp : ∀ e : Fin p,
      eval (coordForm e.val) (List.ofFn point) = point (Fin.castLE hp e) := by
    intro e
    simpa using hx (Fin.castLE hp e)
  -- The three cone facts, all from the entailment layer.
  have hslot : ∀ e : Fin p, (0 : ℤ) ≤ point (Fin.castLE hp e) := by
    intro e
    have := Cert.check_sound (hSlotCert e) hΓ
    rwa [hxp e] at this
  have hrise : ∀ (a : Fin n) (e : Fin p),
      eval (w.block a.val e.val).rise (List.ofFn point) =
        eval (w.pot a.val (core.head e).val) (List.ofFn point) -
          eval (w.pot a.val (core.tail e).val) (List.ofFn point) := by
    intro a e
    rw [eval_eq_of_formEq (hW2 a e) (List.ofFn point), eval_subForm]
  have hlow : ∀ (a : Fin n) (e : Fin p),
      (0 : ℤ) ≤ (leafLowerForm m core w a e).eval point := by
    intro a e
    have h := Cert.check_sound (hLoCert a e) hΓ
    rw [eval_subForm, eval_smulForm, hrise a e] at h
    simp only [leafLowerForm, ExplicitPotential.AffineForm.eval_sub,
      ExplicitPotential.AffineForm.eval_scale, eval_toAffineForm]
    linarith
  have hupp : ∀ (a : Fin n) (e : Fin p),
      (0 : ℤ) ≤ (leafUpperForm m core w a e).eval point := by
    intro a e
    have h := Cert.check_sound (hHiCert a e) hΓ
    rw [eval_subForm, eval_smulForm, hrise a e] at h
    simp only [leafUpperForm, ExplicitPotential.AffineForm.eval_sub,
      ExplicitPotential.AffineForm.eval_scale, eval_toAffineForm]
    linarith
  -- The cone holds at the point.
  have hCone : ExplicitPotential.FormsHold (leafCertificate m core w).cone point := by
    intro f hf
    simp only [leafCertificate, leafCone, List.mem_append, List.mem_map,
      List.mem_flatMap, List.mem_finRange, List.mem_cons, List.not_mem_nil,
      or_false, true_and] at hf
    rcases hf with ⟨e, rfl⟩ | ⟨a, e, (rfl | rfl)⟩
    · show (0 : ℤ) ≤ _
      rw [eval_toAffineForm, hxp e]
      exact hslot e
    · exact hlow a e
    · exact hupp a e
  -- The slot lengths read off the point are `ℓ`.
  have hseg : ∀ e : Fin p, (leafCertificate m core w).segmentNat point e = ℓ e := by
    intro e
    show (((toAffineForm m (coordForm e.val)) :
      ExplicitPotential.AffineForm m).eval point).toNat = ℓ e
    rw [eval_toAffineForm, hxp e, ← hlen e]
    simp
  -- `ValidClosed`, conjunct by conjunct.
  have hValid : (leafCertificate m core w).ValidClosed degree := by
    refine ⟨hLoopless, ?_, ?_, hW5, ?_, ?_⟩
    · exact hW7
    · intro a e
      have := hLoHi a e
      show (w.block a.val e.val).lo + -(w.block a.val e.val).hi ≤ 0
      omega
    · intro e
      refine Or.inr (Or.inr (Or.inr ?_))
      simp only [leafCertificate, leafCone]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨e, List.mem_finRange e, rfl⟩)
    · intro a e
      constructor
      · refine Or.inr ?_
        rw [leafCertificate_lowerForm]
        simp only [leafCertificate, leafCone]
        refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, List.mem_finRange a, ?_⟩)
        exact List.mem_flatMap.mpr ⟨e, List.mem_finRange e, by simp⟩
      · refine Or.inr ?_
        rw [leafCertificate_upperForm]
        simp only [leafCertificate, leafCone]
        refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, List.mem_finRange a, ?_⟩)
        exact List.mem_flatMap.mpr ⟨e, List.mem_finRange e, by simp⟩
  -- The census facts transport along `hseg`.
  have hzs : (leafCertificate m core w).zeroSlots point = zeroSet ℓ := by
    unfold ExplicitPotential.Certificate.zeroSlots zeroSet
    exact Finset.filter_congr fun e _ => by rw [hseg e]
  have hForest' : IsForest (leafCertificate m core w).core
      ((leafCertificate m core w).zeroSlots point) := by rw [hzs]; exact hForest
  have hNotLoopy' : ¬ IsLoopy (leafCertificate m core w).core
      ((leafCertificate m core w).zeroSlots point) := by rw [hzs]; exact hNotLoopy
  have hCoreConn : (leafCertificate m core w).core.Connected :=
    (ExplicitPotential.Core.connectedCheck_eq_true_iff core).mp hConn
  have hMain :=
    ExplicitPotential.Certificate.bnExists_on_degenerate_subdivision_of_validClosed_of_forestCensus
      (leafCertificate m core w) point hn degree hValid hCone hForest' hNotLoopy' hCoreConn
  -- Finally the two degenerate specs are the same object.
  have hEq : (leafCertificate m core w).degenerateSpec point hn
      ((leafCertificate m core w).censusRep point)
      ((leafCertificate m core w).censusRep_idem point)
      ((leafCertificate m core w).censusRep_zero point)
      ((leafCertificate m core w).censusRep_loopless point hNotLoopy')
      ((leafCertificate m core w).censusRep_forest point hForest')
      = censusSpec core hn ℓ hForest hNotLoopy := by
    refine DegSpec.ext' rfl (funext hseg) ?_
    show ExplicitPotential.Certificate.censusRep _ point = compFold core (zeroSet ℓ)
    unfold ExplicitPotential.Certificate.censusRep
    rw [hzs]
    rfl
  rwa [hEq] at hMain

end LeafSound

/-! ## §7  The root of a `(domain closed)` proof

Spec §4.1: the root context is the closed orthant `[σ_0, …, σ_{p−1}]` with no
equalities.  Specialising `leaf_sound` there removes `point`, `hΓ` and `hlen`
and leaves exactly the row obligation of §3: *for every* `ℓ : Fin p → ℕ` whose
vanishing set is a non-loopy forest, the goal holds. -/

/-- The closed-orthant root context. -/
def rootContextClosed (p : ℕ) : Context where
  ge := (List.range p).map coordForm
  eq := []

theorem rootContextClosed_holds {p : ℕ} (ℓ : Fin p → ℕ) :
    (rootContextClosed p).Holds (List.ofFn fun e : Fin p => (ℓ e : ℤ)) := by
  refine ⟨?_, by simp [rootContextClosed]⟩
  intro g hg
  simp only [rootContextClosed, List.mem_map, List.mem_range] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  rw [eval_coordForm_ofFn (fun e : Fin p => (ℓ e : ℤ)) ⟨i, hi⟩]
  exact Int.natCast_nonneg _

/-- **The row obligation, verbatim.**  An accepted single-block leaf at the
closed root proves the goal on every face of the closed length orthant whose
vanishing set is a non-loopy forest.  Compare spec §3 and
`AllMarksCoreCase.SolvedAllMarksClosedCensus`. -/
theorem leaf_sound_closed_root {n p : ℕ} (core : ExplicitPotential.Core n p)
    (w : Witness) (degree : ℤ) (hn : 0 < n)
    (hchk : w.leafChecks p core (rootContextClosed p) degree = true)
    (ℓ : Fin p → ℕ)
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree :=
  leaf_sound core w (rootContextClosed p) degree le_rfl hn hchk
    (fun e : Fin p => (ℓ e : ℤ)) (rootContextClosed_holds ℓ) ℓ (fun _ => rfl)
    hForest hNotLoopy

/-! ## §8  What the multi-block half of §4.3 would cost

Spec §5.3 calls the leaf "composition, not new mathematics" and points at
`Certificate/SlopeScript.lean` and `Certificate/AffinePositionMultiBreak.lean`
for the multi-break script.  That is only true on the **open** orthant: both
of those modules are stated for `SubdivisionGraph.Spec`, which carries
`length_pos`, whereas the leaf obligation of a `(domain closed)` proof lives
on `Utilities.Certificate.DegenerateSpec.DegSpec`, where lengths may vanish.  The closed-orthant
script layer that exists is
`Utilities.Certificate.DegenerateSpec.DegSpec.interpolatedScript` — *one* affine interpolation per
slot, i.e. exactly `k_e = 1`.

So supporting `k_e ≥ 2` needs a genuinely new construction: a piecewise-affine
script on `DegSpec` whose break positions are affine forms that may collide
with each other and with the two endpoints, plus its `prin` at interior and
core vertices, plus the `α_e`/`ω_e` slack reading of W5.  That is the
`DegSpec` port of `SlopeScript` + `AffinePositionMultiBreak`, and it is where
W4 (which is vacuous here) starts doing work.

Nothing in the catalog needs it yet: the proof-data source only ever
emits one block per slot, and §13.5 proves that a *single* whole-orthant leaf
on a two-edge-connected core with more core vertices than degree cannot exist
at all — those rows need a chamber split or an interior chip, which is the
tree layer and the chips, not more blocks. -/

end Utilities.Subdivision.ClosedRowProof
