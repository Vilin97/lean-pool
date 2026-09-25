/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainBInd
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.Rappel210Close

/-!
# The local splitting statement over the ind-completion

The last hop of Deligne's 2.10: over the ind-completion of a
small rigid abelian tensor category, the unit of the splitting
algebra survives — the colimit unit dies only at a finite stage
by the filtered criterion, and no stage unit of a monic point
vanishes.  The local splitting statement therefore holds for
every short exact sequence whose relevant objects carry duals.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **The unit of the splitting algebra survives over the
ind-completion**: the colimit unit dies only at a finite stage,
and the stage units are nonvanishing symmetrised point powers of
the monic dualised point. -/
theorem splitAlgebraUnit_ne_zero_ind
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (S : ShortComplex (Ind C))
    [HasRightDual (S.X₃ : Ind C)] [HasLeftDual (((S.X₃)ᘁ) : Ind C)]
    [HasRightDual (((S.X₃)ᘁ) : Ind C)]
    [HasRightDual (unitFormMid S : Ind C)]
    (hS : S.ShortExact)
    (h1 : ¬ IsZero (𝟙_ (Ind C))) :
    splitAlgebraUnit (((unitFormMid S)ᘁ) : Ind C)
      (unitFormPoint S) ≠ 0 := by
  have hmono : Mono (unitFormPoint S) :=
    mono_unitFormPoint S hS
  intro h0
  obtain ⟨n, hn⟩ := (chainColimitUnit_eq_zero_iff
    (splitStage (((unitFormMid S)ᘁ) : Ind C))
    (splitDelta (((unitFormMid S)ᘁ) : Ind C)
      (unitFormPoint S))
    (splitUnitStage (((unitFormMid S)ᘁ) : Ind C)
      (unitFormPoint S))
    (splitUnitStage_succ (((unitFormMid S)ᘁ) : Ind C)
      (unitFormPoint S))).mp h0
  exact splitUnitStage_ne_zero' (((unitFormMid S)ᘁ) : Ind C)
    (unitFormPoint S) h1 n hn

/-- **The local splitting statement over the ind-completion**
(Deligne 2.10): every short exact sequence whose quotient and
derived objects carry duals splits after base change to a nonzero
commutative algebra. -/
theorem rappel210_ind
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (S : ShortComplex (Ind C))
    [HasRightDual (S.X₃ : Ind C)] [HasLeftDual (((S.X₃)ᘁ) : Ind C)]
    [HasRightDual (((S.X₃)ᘁ) : Ind C)]
    [HasRightDual (unitFormMid S : Ind C)]
    (hS : S.ShortExact)
    (h1 : ¬ IsZero (𝟙_ (Ind C))) :
    Rappel210Statement S hS :=
  rappel210_of_unit_nonzero S hS
    (splitAlgebraUnit_ne_zero_ind S hS h1)

end RS
