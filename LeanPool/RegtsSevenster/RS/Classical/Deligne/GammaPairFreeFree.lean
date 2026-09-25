/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairFreeMix
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairRetractRight
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.OddSquareIso

/-!
# The comparison map on a pair of free modules

Putting the two retract reductions together with the odd-line
square: the comparison map of Deligne's (2.11.1) is invertible at
any pair of free modules whose objects become mixed sums after base
change.  Every case but the odd line against itself is a unitor.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u}

/-- **The comparison map at the odd line against the unit** is the
right unitor. -/
instance isIso_gammaPairComparison_freeL_freeUnit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    IsIso (gammaPairComparison L R (freeMod R L.obj)
      (freeMod R (𝟙_ D))) :=
  gammaPairComparison_isIso_of_iso L R (Iso.refl _)
    (freeModUnitIso R)
    (isIso_gammaPairComparison_unitRight L R (freeMod R L.obj))

/-- **The comparison map at the odd line against the free module of
a mixed sum.** -/
theorem isIso_gammaPairComparison_freeL_mix
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] [HasFiniteBiproducts D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (p q : ℕ) :
    IsIso (gammaPairComparison L R (freeMod R L.obj)
      (freeMod R (L.mix p q))) := by
  classical
  refine isIso_gammaPairComparison_of_retracts_right L R
    (freeMod R L.obj)
    (fun i => freeModMap R (biproduct.ι _ i))
    (fun i => freeModMap R (biproduct.π _ i))
    (freeModMap_biproduct_total R _) ?_
  rintro (j | j)
  · exact isIso_gammaPairComparison_freeL_freeUnit L R
  · exact isIso_gammaPairComparison_oddSquare L R

/-- **The comparison map at the odd line against any free module
that becomes a mixed sum.** -/
theorem isIso_gammaPairComparison_freeL_free
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] [HasFiniteBiproducts D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {Y : D} {p q : ℕ}
    (eY : freeMod R Y ≅ freeMod R (L.mix p q)) :
    IsIso (gammaPairComparison L R (freeMod R L.obj)
      (freeMod R Y)) :=
  gammaPairComparison_isIso_of_iso L R (Iso.refl _) eY
    (isIso_gammaPairComparison_freeL_mix L R p q)

/-- **The comparison map of (2.11.1) at a pair of free modules.** -/
theorem isIso_gammaPairComparison_freeFree
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] [HasFiniteBiproducts D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {X Y : D}
    {p q p' q' : ℕ}
    (eX : freeMod R X ≅ freeMod R (L.mix p q))
    (eY : freeMod R Y ≅ freeMod R (L.mix p' q')) :
    IsIso (gammaPairComparison L R (freeMod R X) (freeMod R Y)) :=
  isIso_gammaPairComparison_free L R
    (isIso_gammaPairComparison_freeL_free L R eY) eX

/-- **The monoidal comparison of the fibre functor is an
isomorphism** at any pair of objects that become mixed sums. -/
theorem isIso_fibreMu_of_mix
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] [HasFiniteBiproducts D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {X Y : D} {p q p' q' : ℕ}
    (eX : freeMod R X ≅ freeMod R (L.mix p q))
    (eY : freeMod R Y ≅ freeMod R (L.mix p' q')) :
    IsIso (fibreMu L R X Y) :=
  isIso_fibreMu L R X Y
    (isIso_gammaPairComparison_freeFree L R eX eY)

end

end RS
