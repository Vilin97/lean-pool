/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairRetract
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairUnit
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeMixRetract

/-!
# The comparison map on the free module of a mixed sum

A mixed sum of copies of the unit and of the odd line presents its
free module as a finite family of retracts of free modules on the
two generators, so the comparison map of Deligne's (2.11.1) on it is
invertible as soon as it is invertible on those two.  The unit case
is the left unitor of `RS.gammaPairComparison_unitLeft`; the odd
line is passed in as a hypothesis and discharged separately.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u}

/-- **The comparison map is an isomorphism on the free module of
the unit**, since that free module is the regular module. -/
instance isIso_gammaPairComparison_freeUnit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (N : Mod D R) :
    IsIso (gammaPairComparison L R (freeMod R (𝟙_ D)) N) :=
  gammaPairComparison_isIso_of_iso L R (freeModUnitIso R)
    (Iso.refl N) (isIso_gammaPairComparison_unitLeft L R N)

/-- **The comparison map is an isomorphism on the free module of a
mixed sum**, given that it is on the free module of the odd
line. -/
theorem isIso_gammaPairComparison_freeMix
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] [HasFiniteBiproducts D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {N : Mod D R}
    (hL : IsIso (gammaPairComparison L R (freeMod R L.obj) N))
    (p q : ℕ) :
    IsIso (gammaPairComparison L R (freeMod R (L.mix p q)) N) := by
  classical
  refine isIso_gammaPairComparison_of_retracts L R N
    (fun i => freeModMap R (biproduct.ι _ i))
    (fun i => freeModMap R (biproduct.π _ i))
    (freeModMap_biproduct_total R _) ?_
  rintro (j | j)
  · exact isIso_gammaPairComparison_freeUnit L R N
  · exact hL

/-- **The comparison map is an isomorphism on any free module that
becomes a mixed sum.** -/
theorem isIso_gammaPairComparison_free
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] [HasFiniteBiproducts D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {N : Mod D R}
    (hL : IsIso (gammaPairComparison L R (freeMod R L.obj) N))
    {X : D} {p q : ℕ} (e : freeMod R X ≅ freeMod R (L.mix p q)) :
    IsIso (gammaPairComparison L R (freeMod R X) N) :=
  gammaPairComparison_isIso_of_iso L R e (Iso.refl N)
    (isIso_gammaPairComparison_freeMix L R hL p q)

end

end RS
