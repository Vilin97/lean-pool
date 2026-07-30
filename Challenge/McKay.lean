/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.RepresentationTheory.Character

/-!
# The McKay conjecture

Source: arxiv:2410.20392, doi:10.4007/annals.2026.203.3.5
Proposed by: Vasily Ilin
Open declarations: `Challenge.McKay.card_pPrimeCharacters_eq`
Tags: group-theory, representation-theory, character-theory, mckay-conjecture
MSC: 20C15, 20D20
Estimated size: ~1000000 lines of Lean

Informal statement:
* `Challenge.McKay.card_pPrimeCharacters_eq` — For every finite group G, every prime p, and every
  Sylow p-subgroup P of G, the set of character functions of simple finite-dimensional complex
  representations of G whose dimension p does not divide has the same cardinality as the
  corresponding set for the normalizer of P in G. Two simple representations have equal characters
  exactly when they are isomorphic, so both sets are in bijection with the sets Irr_p'(G) and
  Irr_p'(N_G(P)) that the McKay conjecture counts.
-/

open CategoryTheory

namespace Challenge.McKay

/-- The irreducible complex characters of `G` of `p'`-degree, as a set of functions: the
characters of simple finite-dimensional complex representations whose dimension is not
divisible by `p`. Two simple representations have equal characters exactly when they are
isomorphic, so this set is in canonical bijection with the set `Irr_{p'}(G)` counted by
the McKay conjecture. -/
def pPrimeCharacters (G : Type*) [Group G] (p : ℕ) : Set (G → ℂ) :=
  {χ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ ∧ ¬p ∣ Module.finrank ℂ V}

/-- The **McKay conjecture**, now the theorem of Cabanes and Späth: for every finite
group `G`, every prime `p`, and every Sylow `p`-subgroup `P` of `G`, the irreducible
complex characters of `G` of degree not divisible by `p` are equinumerous with those of
the normalizer of `P` in `G`. -/
theorem card_pPrimeCharacters_eq (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) :
    Cardinal.mk (pPrimeCharacters G p) =
      Cardinal.mk (pPrimeCharacters (Subgroup.normalizer (P : Set G)) p) := sorry

end Challenge.McKay
