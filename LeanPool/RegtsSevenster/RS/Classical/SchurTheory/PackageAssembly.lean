/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SquareGrowth
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.IdempotentBridge
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.NativeFaithful

/-!
# Assembly of the Schur package

The choice of a simple submodule realizing each Jacobi–Trudi
character, and the construction of a `SchurPackage` from the theory.
The branching field and the factorial bound enter as parameters,
discharged in `PairingPos.lean` and `Common/FactorialBound.lean`.
-/

namespace RS

open Finset

open scoped Classical in
/-- The chosen simple submodule realizing `jtChar μ`. -/
noncomputable def jtSimple (μ : YoungDiagram) :
    Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
      (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))) :=
  Classical.choose (jtChar_eq_nChar μ)

open scoped Classical in
/-- The chosen submodule is simple. -/
theorem jtSimple_simple (μ : YoungDiagram) :
    IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
      (jtSimple μ) :=
  (Classical.choose_spec (jtChar_eq_nChar μ)).1

open scoped Classical in
/-- And its character is the Jacobi–Trudi one it was chosen for. -/
theorem jtSimple_char (μ : YoungDiagram) :
    ∀ π, jtChar μ π = nChar (jtSimple μ) π :=
  (Classical.choose_spec (jtChar_eq_nChar μ)).2

/-- The chosen idempotent is the native projector. -/
theorem charIdempotent_jtSimple (μ : YoungDiagram) :
    charIdempotent (nDim (jtSimple μ)) (jtChar μ) =
      nProjector (jtSimple μ) := by
  refine charIdempotent_eq_nProjector (jtSimple μ) (jtChar μ)
    (jtSimple_char μ) (fun π => jtChar_inv μ π)

/-- **The Schur package**, given the branching fact and the
factorial bound. -/
noncomputable def schurPackageOf
    (H3 : ∀ n : ℕ, n ^ n ≤ 3 ^ n * n.factorial)
    (Hbranch : ∀ (lam mu : YoungDiagram), lam ≤ mu →
      ∀ h : lam.card ≤ mu.card,
      charIdempotent (nDim (jtSimple mu)) (jtChar mu) *
        symCast h
          (charIdempotent (nDim (jtSimple lam)) (jtChar lam)) *
        charIdempotent (nDim (jtSimple mu)) (jtChar mu) ≠ 0) :
    SchurPackage.{u} where
  dim := fun μ => nDim (jtSimple μ)
  char := fun μ => jtChar μ
  dim_pos := fun μ => by
    haveI := jtSimple_simple μ
    haveI := IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))) (jtSimple μ)
    haveI : Nontrivial (subCarrier (jtSimple μ)) :=
      inferInstanceAs (Nontrivial (jtSimple μ))
    exact Module.finrank_pos
  central := fun μ x => by
    rw [charIdempotent_jtSimple μ]
    exact nProjector_central (jtSimple μ) x
  idem := fun μ => by
    rw [charIdempotent_jtSimple μ]
    exact nProjector_idem (jtSimple μ) (jtSimple_simple μ)
  block_rank := fun μ => by
    rw [charIdempotent_jtSimple μ]
    exact nProjector_block_rank (jtSimple μ) (jtSimple_simple μ)
  block_faithful := fun μ B _ _ φ hφ x h0 => by
    rw [charIdempotent_jtSimple μ] at hφ h0 ⊢
    exact nProjector_block_faithful (jtSimple μ)
      (jtSimple_simple μ) φ hφ x h0
  branching := Hbranch
  square_dim := fun R => by
    obtain ⟨s, hs⟩ := square_growth H3 R
    exact ⟨s, hs (jtSimple (squareDiagram s))
      (jtSimple_char (squareDiagram s))⟩
  frobenius := fun μ t => jtChar_frobenius' μ t

end RS
