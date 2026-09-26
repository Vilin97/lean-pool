/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.HookConfinementSharp
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.SkeinTower
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.TensorNonvanishing

/-!
# The two halves of the dimension bound

The tower half is unconditional: at any side `s > 2eR` the skein
representation kills the square block idempotent
(`skeinRep_square_dead`).  The model half is parameterized -- any
linear map out of the group algebra that factors the kill and
admits a trace functional with plain or signed
constant-cycle-product character forces the constant below `s`
(`sector_bound_of_dead`, `sector_bound_of_dead_signed`), provided
the square Schur value at that constant is nonzero.

The two are composed in `Interfaces/SectorDischarge.lean`, against
the sector traces of `SectorIntertwine.lean` and the binomial
determinant of `SymFun/LGVStrict.lean`.
-/

@[expose] public section

namespace RS

open Finset

/-- The chosen block dimension is positive. -/
theorem jtSimple_dim_pos (μ : YoungDiagram) :
    0 < nDim (jtSimple μ) := by
  have := jtSimple_simple μ
  have := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))) (jtSimple μ)
  have : Nontrivial (subCarrier (jtSimple μ)) :=
    inferInstanceAs (Nontrivial (jtSimple μ))
  exact Module.finrank_pos

/-- **Square death in the skein tower**: at any side `s > 2eR` the
skein representation kills the square block idempotent. -/
theorem skeinRep_square_dead {R : ℕ} (f : EdgeRankParameter R)
    {s : ℕ} (hs : 2 * Real.exp 1 * R < s) :
    skeinRep f (squareDiagram s).card
      (charIdempotent (nDim (jtSimple (squareDiagram s)))
        (jtChar (squareDiagram s))) = 0 :=
  not_not.mp ((skeinPermTower f).not_alive_square_sharp
    (by rwa [Real.sqrt_sq (Nat.cast_nonneg R)]))

/-- **The even sector bound**: a linear map with plain
constant-cycle-product character that kills the square idempotent
forces the constant below the side, given the Schur nonvanishing. -/
theorem sector_bound_of_dead {s m : ℕ} {M : Type*} [AddCommGroup M]
    [Module ℂ M]
    (ρ : SymGroupAlgebra (squareDiagram s).card →ₗ[ℂ] M)
    (tr : M →ₗ[ℂ] ℂ)
    (htr : ∀ π, tr (ρ (MonoidAlgebra.of ℂ
        (Equiv.Perm (Fin (squareDiagram s).card)) π)) =
      cycleProd (fun _ => (m : ℂ)) π)
    (hSchur : s ≤ m →
      diagramSchur (squareDiagram s) (fun _ => (m : ℂ)) ≠ 0)
    (h0 : ρ (charIdempotent (nDim (jtSimple (squareDiagram s)))
      (jtChar (squareDiagram s))) = 0) :
    m < s := by
  by_contra h
  push Not at h
  exact charIdempotent_image_ne_zero m (squareDiagram s)
    (nDim (jtSimple (squareDiagram s)))
    (jtSimple_dim_pos (squareDiagram s)) ρ tr htr (hSchur h) h0

/-- **The odd sector bound**: the sign-twisted analogue, with the
Schur nonvanishing at the negated constant. -/
theorem sector_bound_of_dead_signed {s m : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℂ M]
    (ρ : SymGroupAlgebra (squareDiagram s).card →ₗ[ℂ] M)
    (tr : M →ₗ[ℂ] ℂ)
    (htr : ∀ π, tr (ρ (MonoidAlgebra.of ℂ
        (Equiv.Perm (Fin (squareDiagram s).card)) π)) =
      ((Equiv.Perm.sign π : ℤ) : ℂ) *
        cycleProd (fun _ => (m : ℂ)) π)
    (hSchur : s ≤ m →
      diagramSchur (squareDiagram s) (fun _ => -(m : ℂ)) ≠ 0)
    (h0 : ρ (charIdempotent (nDim (jtSimple (squareDiagram s)))
      (jtChar (squareDiagram s))) = 0) :
    m < s := by
  by_contra h
  push Not at h
  exact charIdempotent_image_ne_zero_signed m (squareDiagram s)
    (nDim (jtSimple (squareDiagram s)))
    (jtSimple_dim_pos (squareDiagram s)) ρ tr htr (hSchur h) h0

end RS
