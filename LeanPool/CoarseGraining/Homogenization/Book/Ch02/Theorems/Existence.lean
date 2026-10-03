/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Existence

/-! # Existence -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 response-maximizer existence theorem.

The proof is supplied by the internal a.e.-representative bridge, so the public
surface only mentions the note-facing `Domain` and `CoeffOn` data. -/
theorem responseExistenceTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseExistenceTheory U a :=
  Homogenization.Internal.Ch02.BookCh02.responseExistenceTheory U a

/-- Public per-loading response-maximizer existence, derived from the proved
Chapter 2 existence theorem. -/
theorem responseMaximizerExists {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) :
    ResponseMaximizerExists U a p q :=
  (responseExistenceTheory U a).exists_maximizer p q

end

end Ch02
end Book
end Homogenization
