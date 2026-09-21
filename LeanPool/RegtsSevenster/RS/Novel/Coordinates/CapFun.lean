/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapPeel
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaCotensor

/-!
# The cap functional recursion

The base and successor laws of the cap functional through the
fibre functor: the zero cap is the identity class, and the
successor cap evaluates through the peel rotation and the
tensor split.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The zero cap is the identity class. -/
theorem bundleCapClass_zero :
    bundleCapClass f 0 = 𝟙 (SkeinObj.mk 0 : SkeinObj f) :=
  HomSpace.ofFragment_congr f (relabelZeroEquiv _ _)

variable (P : DelignePackage (SkeinObj f))

/-- **The cap functional successor law**: evaluate through the
peel rotation, then the split cap. -/
theorem omegaFun_cap_succ (m : ℕ)
    (v : (P.ω.obj (SkeinObj.mk ((m + 1) + (m + 1)))).even) :
    omegaFun f P (bundleCapClass f (m + 1)) v =
      omegaFun f P (HomSpace.tensor f (m + m) 0 2 0
          (bundleCapClass f m) (evClass f))
        ((P.ω.map (bundleMapClass f
          (capPeelRotation m))).evenMap v) := by
  rw [bundleCapClass_peel f m]
  exact omegaFun_comp f P
    (bundleMapClass f (capPeelRotation m))
    (HomSpace.tensor f (m + m) 0 2 0
      (bundleCapClass f m) (evClass f)) v

/-- The zero cap functional is the unit evaluation. -/
theorem omegaFun_cap_zero
    (v : (P.ω.obj (SkeinObj.mk 0)).even) :
    omegaFun f P (bundleCapClass f 0) v =
      letI := P.braided
      ((η P.ω : P.ω.obj (SkeinObj.mk 0) ⟶
        SuperVect.tensorUnit) :
        SuperVect.Hom _ _).evenMap v := by
  letI := P.braided
  rw [bundleCapClass_zero]
  show ((P.ω.map (𝟙 (SkeinObj.mk 0)) ≫ η P.ω :
      P.ω.obj (SkeinObj.mk 0) ⟶ SuperVect.tensorUnit) :
    SuperVect.Hom _ _).evenMap v = _
  rw [show P.ω.map (𝟙 (SkeinObj.mk 0 : SkeinObj f)) =
      𝟙 (P.ω.obj (SkeinObj.mk 0)) from P.ω.map_id _]
  rfl

end RS
