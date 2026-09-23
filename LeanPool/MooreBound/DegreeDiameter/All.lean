/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.Results
public import LeanPool.MooreBound.DegreeDiameter.FlagSpace
public import LeanPool.MooreBound.DegreeDiameter.Proposition31
public import LeanPool.MooreBound.DegreeDiameter.Proposition31Asymptotics
public import LeanPool.MooreBound.DegreeDiameter.Proposition31Full
public import LeanPool.MooreBound.DegreeDiameter.Theorem11FromProposition31
public import LeanPool.MooreBound.DegreeDiameter.Corollary12FromProposition31

/-!
# Formalization of the fixed-diameter degree--diameter theorem

The exported results are:

* `DegreeDiameter.alternating_route` — Lemma 2.1;
* `DegreeDiameter.proposition_3_1` — the complete formal statement of
  Proposition 3.1, including equations (6)--(9), with the finite clauses
  exposed through the named fields of `DegreeDiameter.Proposition31FiniteClaims`;
* `DegreeDiameter.proposition_3_1_over_finite_field` — its finite-field
  finite-claims theorem;
* `DegreeDiameter.proposition_3_1_for_prime_power` — its all-prime-power
  instance;
* `DegreeDiameter.proposition31_degree_div_cap_tendsto_one` and
  `DegreeDiameter.proposition31_order_div_degree_pow_tendsto_one` — equation
  (9) for the actual graph family;
* `DegreeDiameter.proposition31_order_div_cap_pow_tendsto_one_from_proposition_3_1`
  — the order/cap bridge derived from the two bundled equation-(9) limits;
* `DegreeDiameter.theorem_1_1` — Theorem 1.1;
* `DegreeDiameter.corollary_1_2` — Corollary 1.2.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

@[expose] public section

namespace MooreBound

end MooreBound
