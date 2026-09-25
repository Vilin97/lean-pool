/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.ChainOfLoops.CDPR

/-!
# Highlights of the chain-of-loops application

**A public interface, in one file.**  Every main theorem of
`Bananas/ChainOfLoops/` is restated below as an `example` whose type is written
out in full and whose proof is the real theorem.  There is not a single new
definition or theorem here.

This file plays for `Bananas/ChainOfLoops/` the role `TwiceMarkedBananas.lean`
plays for the rest of `Bananas`.  The two are deliberately separate:
`TwiceMarkedBananas.lean` is a *paper-order* index of the twice-marked banana paper, and
Cools–Draisma–Payne–Robeva is not a result of that paper — it is a downstream
consumer of its Section 6 chain theorems.  Folding these statements into the
paper index would break the one invariant that index has.

* **For a reader.**  The complete statement of Cools–Draisma–Payne–Robeva's
  main theorem, as formalized, is visible here in one screen.
* **For the build.**  Each `example` is checked by the kernel against the real
  declaration, so a change to a statement is detected in this file.

These files formalize the discrete form of **CDPR Theorem 1.1**
(arXiv:1001.2774): a generic chain of loops is Brill–Noether general.  Part (1)
is the nonexistence statement `cdpr_nonexistence`; part (2) is the sharper
once-marked form `cdpr_no_high_multiplicity`, which says no divisor of the
expected degree and rank contains `(r + ρ + 1)` copies of the chain's end
vertex.

-/

@[expose] public section

namespace ChainOfLoops.Highlights

open Utilities ChainOfLoops

/-! ## The key definitions -/

/-- A **loop** of the chain: two positive arc lengths `top` and `bot`, CDPR's
`ℓ_i` and `m_i`.  The positivity proofs are bundled into the structure so a
`List Loop` can be `List.map`ped and `List.take`/`List.drop`ed without
`List.pmap`.  (`Bananas/ChainOfLoops/CDPR.lean`) -/
alias Loop := ChainOfLoops.Loop

/-- The **torsion order** of a loop: `(ℓ + m) / gcd(ℓ, m)`, the order of the
class of `v_i - v_{i-1}` in the Jacobian of that cycle.
(`Bananas/ChainOfLoops/CDPR.lean`) -/
alias torsionOrder := ChainOfLoops.Loop.torsionOrder

/-- The chain of loops as a `CFGraph`: `g` cycles glued in a row.
(`Bananas/ChainOfLoops/CDPR.lean`) -/
alias chainGraph := ChainOfLoops.chainGraph

/-- The chain as a marked graph, whose `.left` and `.right` are CDPR's `v_0`
and `v_g`.  (`Bananas/ChainOfLoops/CDPR.lean`) -/
alias chainMarked := ChainOfLoops.chainMarked

/-- **CDPR Definition 4.1**, literally: no ratio `ℓ_i / m_i` equals the ratio
of two positive integers whose sum is at most `2g - 2`.  Cross-multiplied to
avoid a division convention.  (`Bananas/ChainOfLoops/CDPR.lean`) -/
alias CDPRGeneric := ChainOfLoops.CDPRGeneric

/-! ## The genus and the Brill–Noether number -/

/-- A chain of `g` loops has genus `g`. -/
example (P : Loop) (L : List Loop) :
    genus (chainGraph P L) = (L.length : ℤ) + 1 :=
  ChainOfLoops.genus_chainGraph P L

/-- The repository's `bnNumber` on a chain of loops is CDPR's
`ρ(g, r, d) = g - (r + 1)(g - d + r)`, written out. -/
example (P : Loop) (L : List Loop) (r d : ℤ) :
    bnNumber (chainGraph P L) r d =
      ((L.length : ℤ) + 1) - (r + 1) * (((L.length : ℤ) + 1) - d + r) :=
  ChainOfLoops.bnNumber_chainGraph P L r d

/-- CDPR genericity is exactly a lower bound on the torsion orders: writing
`d = gcd(ℓ, m)`, the least attainable coordinate sum is `(ℓ + m)/d`, which is
`torsionOrder`. -/
example (L : List Loop) :
    CDPRGeneric L ↔ ∀ P ∈ L, 2 * L.length - 2 < P.torsionOrder :=
  ChainOfLoops.cdprGeneric_iff L

/-! ## The main theorem -/

/-- **CDPR Theorem 1.1(1)**, discrete form.  On a generic chain of `g ≥ 2`
loops, no divisor realizes a Brill–Noether parameter pair with negative `ρ`. -/
example (P : Loop) (L : List Loop)
    (hg : 2 ≤ L.length + 1) (hGeneric : CDPRGeneric (P :: L))
    (r d : ℤ) (hr : 0 ≤ r) (hrho : bnNumber (chainGraph P L) r d < 0) :
    ¬ BNExists (chainGraph P L) r d :=
  ChainOfLoops.cdpr_nonexistence P L hg hGeneric r d hr hrho

/-! ## The once-marked form

The sharper statement, and the one that carries the real content: when `ρ ≥ 0`,
no divisor of degree `d` and rank at least `r` contains `(r + ρ + 1)` copies of
a marked end vertex.

The orientation is not optional.  The theorem holds at the *right* mark `v_g`
under the prefix torsion budget and at the *left* mark `v_0` under the suffix
budget; testing at `v_0` under the prefix budget is false. -/

/-- **CDPR Theorem 1.1(2)**, discrete form, at the chain's right-hand mark
`v_g`.  `hrbound` is CDPR's own standing range restriction (Notation 4.2),
kept for faithfulness. -/
example (P : Loop) (L : List Loop)
    (hg : 2 ≤ L.length + 1) (hGeneric : CDPRGeneric (P :: L))
    (D : CFDiv (chainGraph P L)) (r d : ℤ) (hr : 0 ≤ r)
    (hrbound : r < genus (chainGraph P L))
    (hdeg : deg D = d) (hrank : rank (chainGraph P L) D ≥ r)
    (hrho : 0 ≤ bnNumber (chainGraph P L) r d) :
    rank (chainGraph P L)
        (D - (r + bnNumber (chainGraph P L) r d + 1) •
          (oneChip (chainMarked P L).right : CFDiv (chainGraph P L))) < 0 :=
  ChainOfLoops.cdpr_no_high_multiplicity P L hg hGeneric D r d hr hrbound hdeg
    hrank hrho

/-- The same statement at the chain's *left* mark `v_0`, which is how CDPR
state it.  Obtained through the reversed presentation of the chain and its
isomorphism to the canonical one. -/
example (P : Loop) (L : List Loop)
    (hg : 2 ≤ L.length + 1) (hGeneric : CDPRGeneric (P :: L))
    (D : CFDiv (chainGraph P L)) (r d : ℤ) (hr : 0 ≤ r)
    (hrbound : r < genus (chainGraph P L))
    (hdeg : deg D = d) (hrank : rank (chainGraph P L) D ≥ r)
    (hrho : 0 ≤ bnNumber (chainGraph P L) r d) :
    rank (chainGraph P L)
        (D - (r + bnNumber (chainGraph P L) r d + 1) •
          (oneChip (chainMarked P L).left : CFDiv (chainGraph P L))) < 0 :=
  ChainOfLoops.cdpr_no_high_multiplicity_left P L hg hGeneric D r d hr hrbound
    hdeg hrank hrho

end ChainOfLoops.Highlights
