/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.GradientUniqueness
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.Existence

/-! # Gradient Uniqueness -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 a.e. uniqueness theorem for response-maximizer gradients. -/
theorem responseGradientUniquenessTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseGradientUniquenessTheory U a :=
  Homogenization.Internal.Ch02.BookCh02.responseGradientUniquenessTheory U a

/-- Public a.e. gradient uniqueness for response maximizers with the same
loading. -/
theorem sameGradientAE_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    {p q : Vec d} {v w : Solution U a}
    (hv : IsResponseMaximizer U a p q v) (hw : IsResponseMaximizer U a p q w) :
    Solution.SameGradientAE v w :=
  sameGradientAE_of_response_maximizers
    (responseGradientUniquenessTheory U a) hv hw

/-- Any response maximizer has the same gradient a.e. as the public canonical
maximizer for the same loading.  This is the deterministic Ch2 bridge needed
when an upstream scalar-response selection is constructed by a Hilbert/Galerkin
argument. -/
theorem canonicalMaximizer_sameGradientAE_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    {p q : Vec d} {v : Solution U a}
    (hv : IsResponseMaximizer U a p q v) :
    Solution.SameGradientAE
      (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution v :=
  sameGradientAE_of_isResponseMaximizer
    (canonicalMaximizer (responseExistenceTheory U a) p q).isMaximizer hv

/-- Transporting the public canonical response maximizer across a coefficient
a.e. equality gives a solution with the same gradient as the canonical maximizer
for the transported coefficient. -/
theorem canonicalMaximizer_sameGradientAE_ofAEEq
    {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (p q : Vec d) :
    Solution.SameGradientAE
      (Solution.ofAEEq h
        (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution)
      (canonicalMaximizer (responseExistenceTheory U b) p q).toSolution := by
  have htransport :
      IsResponseMaximizer U b p q
        (Solution.ofAEEq h
          (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution) :=
    (canonicalMaximizer (responseExistenceTheory U a) p q).isMaximizer.ofAEEq h
  have hcanonical :
      IsResponseMaximizer U b p q
        (canonicalMaximizer (responseExistenceTheory U b) p q).toSolution :=
    (canonicalMaximizer (responseExistenceTheory U b) p q).isMaximizer
  exact sameGradientAE_of_isResponseMaximizer htransport hcanonical

end

end Ch02
end Book
end Homogenization
