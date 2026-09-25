/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CoordOf

/-!
# The cap value on model vectors

The cap functional pulled back to the model: the scalar the
final computation evaluates.  Its base case: the zero cap reads
off the scalar itself.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))

/-- The cap value: the cap functional on the transported model
vector. -/
noncomputable def capVal (m : ℕ)
    (v : (superPow (stdSuperPair k ℓ) (m + m)).even) : ℂ :=
  omegaFun f P (bundleCapClass f m)
    (((stdToOmega f P e (m + m)) :
      SuperVect.Hom _ _).evenMap v)

/-- **The zero cap value is the scalar itself.** -/
theorem capVal_zero (v : (superPow (stdSuperPair k ℓ) 0).even) :
    capVal f P e 0 v = v := by
  let := P.braided
  unfold capVal
  rw [omegaFun_cap_zero]
  have hcomp : (ε P.ω ≫ η P.ω : SuperVect.tensorUnit ⟶
      SuperVect.tensorUnit) = 𝟙 SuperVect.tensorUnit :=
    Functor.Monoidal.ε_η P.ω
  exact congrArg (fun z : (SuperVect.tensorUnit ⟶
      SuperVect.tensorUnit) =>
    (z : SuperVect.Hom _ _).evenMap v) hcomp

/-- The cap value is additive over finite sums. -/
theorem capVal_sum {ι : Type*} (m : ℕ) (s : Finset ι)
    (g : ι → (superPow (stdSuperPair k ℓ) (m + m)).even) :
    capVal f P e m (∑ i ∈ s, g i) =
      ∑ i ∈ s, capVal f P e m (g i) := by
  unfold capVal
  rw [map_sum, map_sum]

/-- The cap value is homogeneous. -/
theorem capVal_smul (m : ℕ) (r : ℂ)
    (v : (superPow (stdSuperPair k ℓ) (m + m)).even) :
    capVal f P e m (r • v) = r * capVal f P e m v := by
  unfold capVal
  rw [map_smul, map_smul, smul_eq_mul]

variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- **The parameter value through the cap value**: the final
scalar shape. -/
theorem parameter_capVal (W : ClosedFragment)
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _) :
    f.val W = circleVal f ^ W.circles *
      capVal f P e (edgeCount W)
        (((CategoryTheory.eqToHom (congrArg
            (superPow (stdSuperPair k ℓ))
            (degList_sum (starAssignEnum W))) :
          superPow (stdSuperPair k ℓ)
            ((degList (starAssignEnum W)).sum) ⟶
          superPow (stdSuperPair k ℓ)
            (edgeCount W + edgeCount W)) :
          SuperVect.Hom _ _).evenMap
          (((modelPermMap (sortSplitPerm W)) :
            SuperVect.Hom _ _).evenMap
            (modelStarVec f P e'
              (degList (starAssignEnum W))))) :=
  parameter_model f P e e' W hee'

end RS
