/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.NativeTable
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.SchurPackage

/-!
# The interface idempotent as a class element

`charIdempotent` of the interface unfolds to a `classElem` of the
projector theory; for inversion-invariant class functions the
normalizations agree, identifying `charIdempotent (nDim S) (nChar S)`
with `nProjector S` over the symmetric group.
-/

@[expose] public section

namespace RS

open Finset Equiv

variable {n : ℕ}

/-- `charIdempotent` is the class element of the normalized
inverted character. -/
theorem charIdempotent_eq_classElem (d : ℕ)
    (χ : Equiv.Perm (Fin n) → ℂ) (hinv : ∀ π, χ π⁻¹ = χ π) :
    charIdempotent d χ =
      classElem (fun π : Equiv.Perm (Fin n) =>
        ((d : ℂ) / (n.factorial : ℂ)) * χ π⁻¹) := by
  rw [charIdempotent, classElem, Finset.smul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [hinv π, smul_smul]
  rfl

/-- Over the symmetric group, `charIdempotent` of a simple
submodule's data is the native projector. -/
theorem charIdempotent_eq_nProjector
    (S : Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin n)))
      (MonoidAlgebra ℂ (Equiv.Perm (Fin n))))
    (χ : Equiv.Perm (Fin n) → ℂ)
    (hχ : ∀ π, χ π = nChar S π) (hinv : ∀ π, χ π⁻¹ = χ π) :
    charIdempotent (nDim S) χ = nProjector S := by
  rw [charIdempotent_eq_classElem (nDim S) χ hinv, nProjector]
  congr 1
  funext π
  rw [nCoeff, hχ π⁻¹]
  rw [show (Fintype.card (Equiv.Perm (Fin n)) : ℂ) =
      (n.factorial : ℂ) from by
    rw [Fintype.card_perm, Fintype.card_fin]]

end RS
