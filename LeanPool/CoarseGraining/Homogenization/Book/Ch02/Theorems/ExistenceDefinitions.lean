/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Definitions

/-! # Existence Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- The existence statement needed to turn the note's `v(.,U,p,q;a)` into a
chosen Lean object. This is a public theorem target, not a downstream hypothesis. -/
def ResponseMaximizerExists {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) : Prop :=
  ∃ v : Solution U a,
    MeanZeroOn (U : Set (Vec d)) v.toH1.toFun ∧ IsResponseMaximizer U a p q v

namespace ResponseMaximizerExists

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {p q : Vec d}
    (hv : ResponseMaximizerExists U a p q) :
    ResponseMaximizerExists U b p q := by
  rcases hv with ⟨v, hmean, hmax⟩
  exact ⟨Solution.ofAEEq h v, by simpa using hmean, hmax.ofAEEq h⟩

theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {p q : Vec d} :
    ResponseMaximizerExists U a p q ↔ ResponseMaximizerExists U b p q :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end ResponseMaximizerExists

/-- Public theorem package for Chapter 2 response maximizer existence.

This contains only the existence package used by the chosen-object API.
The proved public theorem is `responseExistenceTheory` in `Existence.lean`.
-/
structure ResponseExistenceTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) : Prop where
  exists_maximizer : ∀ p q : Vec d, ResponseMaximizerExists U a p q

namespace ResponseExistenceTheory

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b)
    (hTheory : ResponseExistenceTheory U a) :
    ResponseExistenceTheory U b where
  exists_maximizer := fun p q =>
    (hTheory.exists_maximizer p q).ofAEEq h

theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    ResponseExistenceTheory U a ↔ ResponseExistenceTheory U b :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end ResponseExistenceTheory

/-- Chosen public maximizer, once the Chapter 2 existence theorem has been supplied. -/
noncomputable def responseMaximizer {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {p q : Vec d} (h : ResponseMaximizerExists U a p q) : Solution U a :=
  Classical.choose h

theorem responseMaximizer_meanZero {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {p q : Vec d} (h : ResponseMaximizerExists U a p q) :
    MeanZeroOn (U : Set (Vec d)) (responseMaximizer h).toH1.toFun :=
  (Classical.choose_spec h).1

theorem responseMaximizer_isMaximizer {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {p q : Vec d} (h : ResponseMaximizerExists U a p q) :
    IsResponseMaximizer U a p q (responseMaximizer h) :=
  (Classical.choose_spec h).2

theorem responseJ_eq_responseValue_responseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {p q : Vec d}
    (h : ResponseMaximizerExists U a p q) :
    responseJ U a p q = responseValue U a p q (responseMaximizer h) :=
  responseJ_eq_responseValue_of_isResponseMaximizer (responseMaximizer_isMaximizer h)

/-- The canonical maximizer supplied by the public existence interface. -/
noncomputable def canonicalMaximizer {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (hTheory : ResponseExistenceTheory U a) (p q : Vec d) :
    CanonicalMaximizer U a p q where
  toSolution := responseMaximizer (hTheory.exists_maximizer p q)
  meanZero := responseMaximizer_meanZero (hTheory.exists_maximizer p q)
  isMaximizer := responseMaximizer_isMaximizer (hTheory.exists_maximizer p q)

theorem canonicalMaximizer_meanZero {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (hTheory : ResponseExistenceTheory U a) (p q : Vec d) :
    MeanZeroOn (U : Set (Vec d)) (canonicalMaximizer hTheory p q).toSolution.toH1.toFun :=
  (canonicalMaximizer hTheory p q).meanZero

theorem canonicalMaximizer_isMaximizer {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (hTheory : ResponseExistenceTheory U a) (p q : Vec d) :
    IsResponseMaximizer U a p q (canonicalMaximizer hTheory p q).toSolution :=
  (canonicalMaximizer hTheory p q).isMaximizer

theorem responseJ_eq_responseValue_canonicalMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hTheory : ResponseExistenceTheory U a) (p q : Vec d) :
    responseJ U a p q =
      responseValue U a p q (canonicalMaximizer hTheory p q).toSolution :=
  (canonicalMaximizer hTheory p q).responseJ_eq

end

end Ch02
end Book
end Homogenization
