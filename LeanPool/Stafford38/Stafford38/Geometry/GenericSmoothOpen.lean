/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.FinitePresentation


/-!
# A generic smooth principal open

For a finite-type domain over a perfect field, the generic localization is a
finitely generated field extension and hence formally smooth.  Mathlib's
smooth-locus spreading theorem then supplies a nonzero principal open which
is smooth.  This file deliberately makes no Jacobian or conormal
identification.
-/

@[expose] public section

namespace Stafford38.Geometry

noncomputable section

variable {k A : Type*} {n : ℕ} [Field k] [PerfectField k] [CommRing A]
  [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [Algebra.FinitePresentation k A]

theorem exists_nonzero_smooth_away
    : ∃ f : A, f ≠ 0 ∧ Algebra.Smooth k (Localization.Away f) := by
  let : Algebra.IsSmoothAt k (⊥ : Ideal A) := by
    change Algebra.FormallySmooth k (Localization.AtPrime (⊥ : Ideal A))
    let : Field (Localization.AtPrime (⊥ : Ideal A)) :=
      IsField.toField (by
        rw [IsLocalRing.isField_iff_maximalIdeal_eq]
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        simp)
    exact Algebra.FormallySmooth.of_perfectField
      (K := k) (L := Localization.AtPrime (⊥ : Ideal A))
  obtain ⟨f, hf, hsmooth⟩ :=
    Algebra.IsSmoothAt.exists_notMem_smooth k (⊥ : Ideal A)
  exact ⟨f, by simpa using hf, hsmooth⟩

theorem exists_nonzero_smooth_away_quotient
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] :
    ∃ f : (MvPolynomial (Fin n) k ⧸ P), f ≠ 0 ∧
      Algebra.Smooth k (Localization.Away f) := by
  let A := MvPolynomial (Fin n) k ⧸ P
  let : Algebra k A := Ideal.Quotient.algebra k
  let : Algebra.FinitePresentation k A := by
    dsimp [A]
    exact Algebra.FinitePresentation.quotient P.fg_of_isNoetherianRing
  simpa [A] using (exists_nonzero_smooth_away (k := k) (A := A))


end
end Stafford38.Geometry
