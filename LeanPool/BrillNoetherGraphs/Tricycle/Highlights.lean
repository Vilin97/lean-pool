/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Tricycle.Gap

/-!
# Highlights of the `Tricycle` library

**A public interface, in one file.**  Every main theorem of this library is
restated below as an `example` whose type is written out in full and whose
proof is the real theorem.  There is not a single new definition or theorem
here.

* **For a reader.**  The complete statement of the discrete/metric gonality
  counterexample, as formalized, is visible here in one screen.
* **For the build.** Each `example` is checked by the kernel against the real
  declaration, so a change to a statement is detected in this file.

The library formalizes van Dobben de Bruyn–Smit–van der Wegen, *Discrete and
metric divisorial gonality can be different*, JCTA **189** (2022) 105619
(arXiv:2106.12568): the **minimal tricycle** `T_m`, a connected loopless
multigraph on seven vertices with fifteen edges and cyclomatic genus nine,
satisfies `min_{k ≥ 1} dgon(σ_k(T_m)) = 5 < 6 = dgon(T_m)`.  Baker's
Conjecture 3.14(a) is therefore false, already at `r = 1` and `k = 2`.

Thus a proof for metric gonality alone does not imply the corresponding result
for discrete divisorial gonality.
-/

@[expose] public section

namespace Tricycle.Highlights

open Utilities Utilities.Gonality Utilities.Tricycle
open Utilities.Certificate.SubdivisionGraph

/-! ## The key definitions -/

/-- The **tricycle core**: the seven-vertex, fifteen-slot core whose
subdivisions are the tricycle graphs.  (`Tricycle/Core.lean`) -/
alias tricycleCore := Utilities.Tricycle.tricycleCore

/-- A subdivision is a **tricycle graph** when its three transition slots are
unsubdivided.  (`Tricycle/Core.lean`) -/
alias IsTricycle := Utilities.Tricycle.IsTricycle

/-- The **minimal tricycle** `T_m`: the tricycle core at all-ones lengths.
(`Tricycle/UpperBounds.lean`) -/
alias Tm := Utilities.Tricycle.Tm

/-- **Divisorial gonality**: the least degree of an effective divisor of rank
at least one.  (`Utilities/Gonality/DivisorialGonality.lean`) -/
alias divisorialGonality := Utilities.Gonality.divisorialGonality

/-- `min_{k ≥ 1} dgon(σ_k(G))`, with `σ_k` the `k`-fold regular subdivision
built on the occurrence presentation of `G`.  Deliberately *not* called
`metricGonality`: the identification with the metric invariant is the source's
Theorem 1.5, which is not formalized here.
(`Utilities/Gonality/GonalityTransport.lean`) -/
alias regularSubdivisionGonality := Utilities.Gonality.regularSubdivisionGonality

/-! ## The headline statements -/

/-- **The tricycle gap**, with both sides invariants of the bare graph:
`min_{k ≥ 1} dgon(σ_k(T_m)) = 5 < 6 = dgon(T_m)`. -/
example :
    regularSubdivisionGonality Tm.graph < divisorialGonality Tm.graph :=
  Utilities.Tricycle.tricycle_gap_graph

/-- **Baker's Conjecture 3.14(a) is false.**  Baker, *Specialization of linear
systems from curves to graphs*, Conjecture 3.14(a) asserts
`dgon_r(σ_k(G)) = dgon_r(G)` for every connected loopless multigraph `G`, every
`r ≥ 1` and every `k ≥ 1`.  It fails already at `r = 1` and `k = 2`. -/
example :
    ¬ ∀ (G : CFGraph.{0}) (k : ℕ) (hk : 0 < k), graphConnected G →
        divisorialGonality (regularSubdivision G k hk) = divisorialGonality G :=
  Utilities.Tricycle.baker_conjecture_3_14a_false

/-! ## The two sides of the gap -/

/-- `dgon(T_m) = 6`. -/
example : divisorialGonality Tm.graph = 6 :=
  Utilities.Tricycle.divisorialGonality_Tm

/-- `min_{k ≥ 1} dgon(σ_k(T_m)) = 5`, the minimum attained at `k = 2`. -/
example : regularSubdivisionGonality Tm.graph = 5 :=
  Utilities.Tricycle.regularSubdivisionGonality_Tm

/-! ## The two reusable ingredients

Both are more general than the headline, and both are stated for an arbitrary
subdivision specification rather than for one graph. -/

/-- **Corollary 3.7.**  *Every* subdivision of the tricycle core, at *every*
positive length vector, has `dgon ≥ 5`.  This is what makes the left-hand side
of the gap a genuine minimum over `k`; it has to be, because
`k ↦ dgon(σ_k(T_m))` is not monotone. -/
example (spec : Spec 7 15) (hcore : spec.core = tricycleCore)
    (hconn : graphConnected spec.graph) :
    5 ≤ divisorialGonality spec.graph :=
  Utilities.Tricycle.five_le_divisorialGonality hcore hconn

/-- **Theorem 3.9, lower half.**  Every *tricycle graph* — every subdivision of
the minimal tricycle whose three transition edges are unsubdivided — has
`dgon ≥ 6`. -/
example (spec : Spec 7 15) (hcore : spec.core = tricycleCore)
    (htri : IsTricycle spec.length) (hconn : graphConnected spec.graph) :
    6 ≤ divisorialGonality spec.graph :=
  Utilities.Tricycle.six_le_divisorialGonality hcore htri hconn

end Tricycle.Highlights
