/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29State
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModShuffle

/-!
# Transport of a dévissage state along an isomorphism

The state depends on the object only through the free module it
generates, so an isomorphism of objects carries a state to a
state without disturbing any of the counts.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **Transport of a dévissage state along an isomorphism** of
the object being decomposed. -/
noncomputable def DevissageState.transportObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    {L : OddLine D} {X Y : D} (e : X ≅ Y)
    (st : DevissageState D L X) : DevissageState D L Y :=
  letI := st.monObj
  letI := st.comm
  { base := st.base
    monObj := st.monObj
    comm := st.comm
    unit_ne_zero := st.unit_ne_zero
    units := st.units
    lines := st.lines
    rest := st.rest
    restDual := st.restDual
    datum := st.datum
    zigzag := st.zigzag
    decomp := st.decomp.elim fun f =>
      ⟨(freeModMapIso st.base e.symm).trans f⟩ }

/-- Transport leaves the unit count untouched. -/
@[simp] theorem DevissageState.transportObj_units
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    {L : OddLine D} {X Y : D} (e : X ≅ Y)
    (st : DevissageState D L X) :
    (st.transportObj e).units = st.units := rfl

/-- Transport leaves the line count untouched. -/
@[simp] theorem DevissageState.transportObj_lines
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    {L : OddLine D} {X Y : D} (e : X ≅ Y)
    (st : DevissageState D L X) :
    (st.transportObj e).lines = st.lines := rfl

end RS
