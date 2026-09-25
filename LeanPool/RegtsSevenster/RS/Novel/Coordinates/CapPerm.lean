/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.EvForm

/-!
# The peel rotation as a permutation and a cast

The peel rotation splits as a same-arity permutation followed by
an arity cast; the permutation feeds the braiding-word transport
and the cast transports as an equality of powers.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The peel rotation as a permutation of the source arity. -/
def capPeelPerm (m : ℕ) :
    _root_.Equiv.Perm (Fin ((m + 1) + (m + 1))) :=
  (capPeelRotation m).trans (finCongr
    (by omega : (m + m) + 2 = (m + 1) + (m + 1)))

/-- The peel rotation is its permutation followed by the arity
cast. -/
theorem capPeelEquiv_split (m : ℕ) :
    capPeelRotation m = (capPeelPerm m).trans (finCongr
      (by omega : (m + 1) + (m + 1) = (m + m) + 2)) :=
  _root_.Equiv.ext (fun _ => Fin.ext rfl)

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The peel bundle map splits as permutation then cast. -/
theorem bmc_capPeel_split (m : ℕ) :
    bundleMapClass f (capPeelRotation m) =
      HomSpace.comp f ((m + 1) + (m + 1)) ((m + 1) + (m + 1))
        ((m + m) + 2)
        (bundleMapClass f ((capPeelPerm m) :
          Fin ((m + 1) + (m + 1)) ≃ Fin ((m + 1) + (m + 1))))
        (bundleMapClass f (finCongr
          (by omega : (m + 1) + (m + 1) = (m + m) + 2))) := by
  rw [bundleMapClass_comp]
  exact bundleMapClass_congr f (capPeelEquiv_split m)

variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))

/-- **The cast transport**: an arity-cast bundle map conjugates
through the model transport into the equality of powers. -/
theorem stdToOmega_bmc_cast {n₁ n₂ : ℕ} (h : n₁ = n₂) :
    letI := P.braided
    stdToOmega f P e n₁ ≫
        P.ω.map (bundleMapClass f (finCongr h)) =
      eqToHom (congrArg (superPow (stdSuperPair k ℓ)) h) ≫
        stdToOmega f P e n₂ := by
  let := P.braided
  subst h
  rw [show (finCongr (rfl : n₁ = n₁) : Fin n₁ ≃ Fin n₁) =
      _root_.Equiv.refl (Fin n₁) from
    _root_.Equiv.ext (fun x => Fin.ext rfl)]
  rw [show bundleMapClass f (_root_.Equiv.refl (Fin n₁)) =
      𝟙 (SkeinObj.mk n₁ : SkeinObj f) from
    bundleMapClass_refl f n₁]
  rw [show P.ω.map (𝟙 (SkeinObj.mk n₁ : SkeinObj f)) =
      𝟙 (P.ω.obj (SkeinObj.mk n₁)) from P.ω.map_id _]
  rw [eqToHom_refl]
  rw [Category.comp_id, Category.id_comp]

end RS
