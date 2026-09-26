/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PointFibre

/-!
# The fibre functor is complex-linear

The fibre functor is built by whiskering with the algebra and
composing, and both operations are complex-linear, so the functor
is.  This is the last field of `RS.DeligneFibreFunctor` that the
fibre construction does not supply on its own.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

section

variable {D : Type u}

/-- **The fibre functor is complex-linear.** -/
instance fibreFun_linear
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    (fibreFun L R).Linear ℂ where
  map_smul {V W} f c := by
    rw [fibreFun_map, fibreFun_map]
    refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
      refine LinearMap.ext fun m => ?_
    · change m ≫ (R ◁ (c • f)) = c • (m ≫ (R ◁ f))
      rw [MonoidalLinear.whiskerLeft_smul]
      exact CategoryTheory.Linear.comp_smul _ _ _ m c (R ◁ f)
    · change m ≫ (R ◁ (c • f)) = c • (m ≫ (R ◁ f))
      rw [MonoidalLinear.whiskerLeft_smul]
      exact CategoryTheory.Linear.comp_smul _ _ _ m c (R ◁ f)

end

end RS
