/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.Leaf

/-!
# Executable checks for rich row-proof leaves

This is the data-level half of the multi-block leaf checker.  In particular,
the W4 and W5 quantities below are integer computations on the declared block
bounds and chips; only the certificates witnessing the length-dependent
alternatives are delegated to `Cert.check`.

The indices deliberately agree with `rpfcheck.c`: a named point has index
`s : ℕ`, is the end of block `s - 1`, and hence runs in W4 start at `1`.
-/

@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open Utilities.Certificate

namespace RichWitness

variable {m n p : ℕ}

/-- The right end of block `i - 1`; index zero is the tail of the slot. -/
def point (w : RichWitness) (a e i : ℕ) : Form :=
  if i = 0 then [] else (w.block a e (i - 1)).endForm

/-- The length of block `i`, as a form. -/
def blockLength (w : RichWitness) (a e i : ℕ) : Form :=
  subForm (w.block a e i).endForm (w.point a e i)

/-- Total chip coefficient assigned to a named point.

This intentionally follows `rpfcheck.c`'s W3 scan: a chip belongs to the
*first* matching named interior point of the slot.  The distinction matters
when zero-length blocks make two named forms equal.  In particular index zero
is the tail, not a named interior point, so it never receives a chip.  W3
separately ensures that every chip has such a matching interior point. -/
def chipAt (w : RichWitness) (a e i : ℕ) : ℤ :=
  if i == 0 then 0 else
    w.chips.foldl (fun z c =>
      if c.1 == e && formEq c.2.1 (w.point a e i) &&
          (List.range (i - 1)).all
            (fun j => !(formEq c.2.1 (w.point a e (j + 1))))
      then z + c.2.2 else z) 0

@[simp] theorem chipAt_zero (w : RichWitness) (a e : ℕ) :
    w.chipAt a e 0 = 0 := by
  simp [chipAt]

/-- Chip coefficients at named points `1, …, s`, inclusive. -/
def chipPrefix (w : RichWitness) (a e s : ℕ) : ℤ :=
  (List.range (s + 1)).foldl (fun z i => z + w.chipAt a e i) 0

/-- The W5 tail candidate when precisely the first `s` named points have
fallen into the tail. -/
def tailCandidate (w : RichWitness) (a e s : ℕ) : ℤ :=
  w.chipPrefix a e s + (w.block a e s).lo

/-- The W5 head candidate when precisely the last `s` named points have
fallen into the head. -/
def headCandidate (w : RichWitness) (a e s : ℕ) : ℤ :=
  let k := (w.blockList a e).length
  (List.range (s + 1)).foldl (fun z t =>
    if t = 0 then z else z + w.chipAt a e (k - t)) 0 -
    (w.block a e (k - 1 - s)).hi

/-- Minimum of the endpoint candidates indexed by `0, …, bound`.

This is public because the closed-face soundness proof uses the elementary
fact that it is bounded above by every candidate represented by a collapsed
endpoint prefix/suffix. -/
def minOver (f : ℕ → ℤ) (bound : ℕ) : ℤ :=
  (List.range bound).foldl (fun z i => min z (f (i + 1))) (f 0)

/-- The conservative W5 contribution of a slot at its tail. -/
def tailContribution (w : RichWitness) (a e : ℕ) : ℤ :=
  minOver (w.tailCandidate a e) ((w.plan a).headSlack.getD e 0)

/-- The conservative W5 contribution of a slot at its head. -/
def headContribution (w : RichWitness) (a e : ℕ) : ℤ :=
  minOver (w.headCandidate a e) ((w.plan a).tailSlack.getD e 0)

/-- The constant residual of the W4 run from named point `i` through `j`. -/
def w4Residual (w : RichWitness) (a e i j : ℕ) : ℤ :=
  (List.range (j + 1 - i)).foldl (fun z t => z + w.chipAt a e (i + t)) 0 +
    (w.block a e j).lo - (w.block a e (i - 1)).hi

/-- The strict-integer certificate that a form is positive. -/
def positiveCheck (c : Cert) (Γ : Context) (f : Form) : Bool :=
  c.check Γ (subForm f [1])

/-- W1: block order, final endpoint, and endpoint-slack discipline. -/
def w1Checks (w : RichWitness) (_core : ExplicitPotential.Core n p) (Γ : Context) : Bool :=
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
    let bs := w.blockList a.val e.val
    let k := bs.length
    let α := (w.plan a.val).headSlack.getD e.val 0
    let ω := (w.plan a.val).tailSlack.getD e.val 0
    decide (1 ≤ k) && decide (α + ω + 1 ≤ k) &&
    (List.range k).all (fun i =>
      (w.blockReceipt a.val e.val i).monotone.check Γ (w.blockLength a.val e.val i)) &&
    formEq (w.block a.val e.val (k - 1)).endForm (coordForm e.val) &&
    (if α + 1 ≤ k - 1 then
      positiveCheck ((w.plan a.val).tailSlackCert.getD e.val Cert.dflt)
        Γ (w.point a.val e.val (α + 1)) else true) &&
    (if k - 1 - ω ≥ 1 then
      positiveCheck ((w.plan a.val).headSlackCert.getD e.val Cert.dflt) Γ
        (subForm (coordForm e.val) (w.point a.val e.val (k - 1 - ω))) else true))

/-- W2: each block is realizable by convex interpolation and the block rises
close the potential around every slot. -/
def w2Checks (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context) : Bool :=
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
    let k := (w.blockList a.val e.val).length
    (List.range k).all (fun i =>
      let b := w.block a.val e.val i
      let r := w.blockReceipt a.val e.val i
      decide (b.lo ≤ b.hi) &&
        r.lower.check Γ (subForm b.rise (smulForm b.lo (w.blockLength a.val e.val i))) &&
        r.upper.check Γ (subForm (smulForm b.hi (w.blockLength a.val e.val i)) b.rise)) &&
    formEq ((List.range k).foldl (fun z i => addForm z (w.block a.val e.val i).rise) [])
      (subForm (w.pot a.val (core.head e).val) (w.pot a.val (core.tail e).val)))

/-- W3: each chip is on this slot's syntactically named interior point. -/
def w3Checks (w : RichWitness) (_core : ExplicitPotential.Core n p) : Bool :=
  w.chips.all (fun c => decide (c.1 < p)) &&
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
    w.chips.all (fun c =>
      if c.1 == e.val then
        (List.range ((w.blockList a.val e.val).length - 1)).any
          (fun i => formEq c.2.1 (w.point a.val e.val (i + 1)))
      else true))

/-- A named point whose form is *syntactically* the tail of its slot.  Since
W1 makes the named points weakly increasing from `0`, such a point evaluates
to `0` at every parameter value, so any collapsed run through it sits on the
tail core vertex, where W5 — not W4 — accounts for it. -/
def tailConfined (w : RichWitness) (a e i : ℕ) : Bool :=
  formEq (w.point a e i) []

/-- The head-side mirror of `tailConfined`. -/
def headConfined (w : RichWitness) (a e j : ℕ) : Bool :=
  formEq (w.point a e j) (coordForm e)

/-- W4: every possibly-collapsed interior run has nonnegative residual, or a
strict separation receipt.

The run `i … j` ranges over *all* named interior indices `1 ≤ i ≤ j ≤ k − 1`.
It is exempt only when it is pinned to an endpoint by `tailConfined` /
`headConfined`, which is the sound reading of spec §4.3's "every named
interior point and every collapsed run of them".

The earlier implementation instead skipped `i ≤ α` and `j > k − 1 − ω`, using
the *declared* endpoint slack.  That is unsound: `α` bounds how many named
points **may** slide onto the tail, not how many **do**, so a run starting at
`i ≤ α` can collapse at a strictly interior vertex whose residual then goes
unchecked.  See the accompanying analysis. -/
def w4Checks (w : RichWitness) (_core : ExplicitPotential.Core n p) (Γ : Context) : Bool :=
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
    let k := (w.blockList a.val e.val).length
    (List.range (k - 1)).all (fun q =>
      let i := q + 1
      (List.range (k - i)).all (fun r =>
        let j := i + r
        if w.tailConfined a.val e.val i || w.headConfined a.val e.val j then true
        else if 0 ≤ w.w4Residual a.val e.val i j then true
        else if i == j then false
        else positiveCheck (w.separationReceipt a.val e.val i j) Γ
          (subForm (w.point a.val e.val j) (w.point a.val e.val i)))))

/-- W5 residual at one core vertex for one plan, with `mult` chips withdrawn
at the plan's own vertex.

`mult = 1` is a rank anchor: reaching `a` witnesses `rank ≥ 1` there.
`mult = m` is a legged goal's `(comp x …)` doubled anchor, where the claim is
instead that `D − m·1_x` is winnable.  The two run through identical
machinery; this coefficient is the only difference, exactly as in
`rpfcheck.c`'s W5. -/
def w5MultResidual (w : RichWitness) (core : ExplicitPotential.Core n p)
    (mult : ℤ) (a v : ℕ) : ℤ :=
  w.divisorCore.getD v 0 - (if v == a then mult else 0) +
    (List.finRange p).foldl (fun z e => z +
      (if (core.tail e).val == v then w.tailContribution a e.val else 0) +
      (if (core.head e).val == v then w.headContribution a e.val else 0)) 0

/-- W5 residual at one core vertex for one anchor. -/
def w5Residual (w : RichWitness) (core : ExplicitPotential.Core n p) (a v : ℕ) : ℤ :=
  w.w5MultResidual core 1 a v

/-- W5 at multiplicity `mult` for the single plan at `a`: the extra row a
legged rich leaf carries beyond `richLeafChecks`. -/
def w5MultChecks (w : RichWitness) (core : ExplicitPotential.Core n p)
    (mult : ℤ) (a : ℕ) : Bool :=
  ExplicitPotential.allFin fun v : Fin n =>
    decide (0 ≤ w.w5MultResidual core mult a v.val)

@[simp] theorem w5MultChecks_eq_true_iff (w : RichWitness)
    (core : ExplicitPotential.Core n p) (mult : ℤ) (a : ℕ) :
    w.w5MultChecks core mult a = true ↔
      ∀ v : Fin n, 0 ≤ w.w5MultResidual core mult a v.val := by
  simp [w5MultChecks, ExplicitPotential.allFin_eq_true_iff]

/-- W5: all conservative core residuals are effective. -/
def w5Checks (w : RichWitness) (core : ExplicitPotential.Core n p) : Bool :=
  ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun v : Fin n =>
    decide (0 ≤ w.w5Residual core a.val v.val))

/-- The executable W1--W5 checker for a rich multi-block leaf.  Structural
row conditions and degree are included here so that this is directly usable as
the replacement leaf predicate by the tree layer. -/
def richLeafChecks (w : RichWitness) (_m : ℕ) (core : ExplicitPotential.Core n p)
    (Γ : Context) (degree : ℤ) : Bool :=
  ExplicitPotential.allFin (fun e : Fin p => decide (core.tail e ≠ core.head e)) &&
  core.connectedCheck &&
  -- The C checker requires `(div ...)` to have exactly one coefficient per
  -- core vertex.  This is also soundness-critical here: W5 reads only the
  -- first `n` entries with `getD`, so W7 must not count trailing entries that
  -- have no vertex in the decoded divisor.
  decide (w.divisorCore.length = n) &&
  w.w1Checks core Γ && w.w2Checks core Γ && w.w3Checks core &&
  w.w4Checks core Γ && w.w5Checks core &&
  ExplicitPotential.allFin (fun e : Fin p =>
    (w.slotCert.getD e.val Cert.dflt).check Γ (coordForm e.val)) &&
  decide ((w.divisorCore.foldl (· + ·) 0 +
    w.chips.foldl (fun z c => z + c.2.2) 0) = degree)

end RichWitness

end Utilities.Subdivision.ClosedRowProof
