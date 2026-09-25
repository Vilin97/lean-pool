/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


/-
General finite-order Hadamard factorization — public entry point.

Import this file for the multiplicity-aware, any-finite-order version of
Hadamard's factorization theorem (Conway XI.3.4).
-/

public import LeanPool.LiCriterion.Hadamard.General.Factorization

/-!
# Genus-1 Hadamard factorization

Aggregator for the general order-`≤ 1` factorization theorem.
-/

@[expose] public section

namespace Hadamard

export General
  ( canonicalProductZeroSetMultiplicityRank
    canonicalProductZeroSetMultiplicityRank_one
    hadamard_factorization_general )

end Hadamard
