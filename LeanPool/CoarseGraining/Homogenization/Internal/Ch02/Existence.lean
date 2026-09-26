/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.ExistenceDefinitions
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Existence
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Adapters
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives

/-! # Existence -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-- Internal bridge from the old canonical maximizer package to the new public
Chapter 2 existence package. -/
theorem responseMaximizerExists_of_scalarCanonicalMaximizer {d : ℕ}
    (U : Domain d) (a : CoeffOn U) {p q : Vec d}
    (v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q a.toCoeffField) :
    ResponseMaximizerExists U a p q := by
  refine ⟨(v : AHarmonicFunction a.toCoeffField (U : Set (Vec d))), ?_, ?_⟩
  · exact v.meanZero
  · exact v.isResponseMaximizer

/-- Internal pointwise-coefficient bridge. This is not the final public
note-facing theorem: it is the adapter that lets the old Hilbert existence
engine feed the new public package whenever an internal representative has
already been upgraded to pointwise ellipticity. -/
theorem responseMaximizerExists_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p q : Vec d) :
    ResponseMaximizerExists U a p q := by
  rcases ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) (a := a.toCoeffField)
      (lam := a.lam) (Lam := a.Lam)
      U.nonempty U.isDomain hEll p q with
    ⟨v⟩
  exact responseMaximizerExists_of_scalarCanonicalMaximizer U a v

/-- Internal pointwise-coefficient existence theory. The public a.e. theorem is
proved below by changing representatives first. -/
theorem responseExistenceTheory_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseExistenceTheory U a where
  exists_maximizer := responseMaximizerExists_of_isEllipticFieldOn U a hEll

/-- Note-facing Chapter 2 response-maximizer existence from the public a.e.
coefficient interface. Pointwise ellipticity is used only for the private
representative `pointwiseCoeffOn U a`, and the result is transported back across
a.e. equality of coefficient representatives. -/
theorem responseExistenceTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseExistenceTheory U a := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hEll :
      IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a
  have hb : ResponseExistenceTheory U b :=
    responseExistenceTheory_of_isEllipticFieldOn U b hEll
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  exact ResponseExistenceTheory.ofAEEq hba hb

end BookCh02

end

end Ch02
end Internal
end Homogenization
