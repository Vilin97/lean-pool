/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistDatum
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistBiprod
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistMixLine
import LeanPool.RegtsSevenster.RS.Classical.Deligne.StateTransport

/-!
# The odd twist of a dévissage state

Twisting the object by the odd line twists the whole state: the
remainder and its dual acquire a line factor, their duality datum
is the odd twist, and the mixed free part turns each unit summand
into a line and each line summand into a unit, so the two counts
change places.  Twisting twice returns to the original object.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **The twist of the mixed free part**: twisting the free
module on a mixed sum exchanges the two counts. -/
noncomputable def freeMixTwistIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (L : OddLine D)
    (A : D) [MonObj A] (p q : ℕ) :
    tensorLeftMod A L.obj (freeMod A (L.mix p q)) ≅
      freeMod A (L.mix q p) :=
  (freeTwistIso A L.obj (L.mix p q)).symm.trans
    (freeModMapIso A (L.twistMixIso p q))

/-- **The odd twist of a dévissage state**: the counts change
places and the remainder gains a line factor. -/
noncomputable def twistState
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (L : OddLine D)
    {X : D}
    (st : DevissageState D L X) :
    DevissageState D L (L.obj ⊗ X) :=
  letI := st.monObj
  letI := st.comm
  { base := st.base
    monObj := st.monObj
    comm := st.comm
    unit_ne_zero := st.unit_ne_zero
    units := st.lines
    lines := st.units
    rest := tensorLeftMod st.base L.obj st.rest
    restDual := tensorLeftMod st.base L.obj st.restDual
    datum := twistDatum st.base L st.datum
    zigzag := twistDatum_zigzag st.base L st.datum st.zigzag
    decomp := st.decomp.elim fun e =>
      ⟨(freeTwistIso st.base L.obj X).trans
        ((tensorLeftModWhiskerIso st.base L.obj e).trans
          ((tensorLeftBiprodIso st.base L.obj
            (freeMod st.base (L.mix st.units st.lines))
            st.rest).trans
            (modBiprodMapIso st.base _ _
              (freeMixTwistIso L st.base st.units st.lines)
              (Iso.refl _))))⟩ }

/-- The twist exchanges the unit count for the line count. -/
@[simp] theorem twistState_units
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (L : OddLine D)
    {X : D}
    (st : DevissageState D L X) :
    (twistState L st).units = st.lines := rfl

/-- The twist exchanges the line count for the unit count. -/
@[simp] theorem twistState_lines
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (L : OddLine D)
    {X : D}
    (st : DevissageState D L X) :
    (twistState L st).lines = st.units := rfl

/-- **Twisting twice is trivial**: the square trivialisation
undoes the double twist. -/
noncomputable def untwistIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D)
    (X : D) :
    L.obj ⊗ (L.obj ⊗ X) ≅ X :=
  (α_ L.obj L.obj X).symm.trans
    ((whiskerRightIso L.sq X).trans (λ_ X))

end RS
