/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.Module.ArchimedeanBallSplitting

/-!
# API checks for the ordered Archimedean splitting

This file checks the public interface for the splitting of a closed Archimedean ball into its
stratum and open ball. The nondegenerate check has both coordinates unequal and moving in opposite
directions: the stratum coordinate increases while the open-ball coordinate decreases. The image
must increase, distinguishing the lexicographic order from the componentwise product order.
-/

public section

namespace Tests

open FiniteArchimedeanClass

variable {K M : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable [Module K M] [IsOrderedModule K M]

open HahnEmbedding in
/-- A strict increase in the stratum dominates a strict decrease in the open-ball coordinate.

The two strict inequalities exclude equality in either coordinate, so this is not a zero or
one-coordinate smoke test. -/
theorem archimedeanSplitting_stratum_dominates_ball
    (u : ArchimedeanStrata K M) (c : FiniteArchimedeanClass M)
    (s₁ s₂ : u.stratum c) (b₁ b₂ : ball K c) (hs : s₁ < s₂) (hb : b₂ < b₁) :
    ArchimedeanStrata.stratumLexBallEquivClosedBall u c (toLex (s₁, b₁)) <
      ArchimedeanStrata.stratumLexBallEquivClosedBall u c (toLex (s₂, b₂)) := by
  have _ := hb
  rw [map_lt_map_iff, Prod.Lex.toLex_lt_toLex]
  exact Or.inl hs

open HahnEmbedding in
theorem archimedeanSplitting_addition_formula
    (u : ArchimedeanStrata K M) (c : FiniteArchimedeanClass M)
    (s : u.stratum c) (b : ball K c) :
    ArchimedeanStrata.stratumLexBallEquivClosedBall u c (toLex (s, b)) =
      (s : M) + (b : M) := by
  simp

open HahnEmbedding in
theorem archimedeanSplitting_roundtrip
    (u : ArchimedeanStrata K M) (c : FiniteArchimedeanClass M) (x : closedBall K c) :
    ArchimedeanStrata.stratumLexBallEquivClosedBall u c
      (ArchimedeanStrata.closedBallEquivStratumLexBall u c x) = x := by
  simp

end Tests
