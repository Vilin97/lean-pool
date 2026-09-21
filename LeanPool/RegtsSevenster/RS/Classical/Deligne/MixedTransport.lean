/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.StepATransport

/-!
# Transport of local mixedness along a base change

Being a mixed sum after base change is inherited by any further
base change: the free module on an object is carried to the free
module on the same object, so a decomposition over one algebra
becomes a decomposition over any algebra under it.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **An isomorphism of free modules base-changes.** -/
noncomputable def freeModIsoBaseChange
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    {V W : D} (e : freeMod A V ≅ freeMod A W) :
    freeMod B V ≅ freeMod B W :=
  (baseChangeFreeIso A B φ V).symm.trans
    ((baseChangeMapIso A B φ e).trans (baseChangeFreeIso A B φ W))

end RS
