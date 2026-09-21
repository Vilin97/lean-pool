/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreAdditive
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreMonoidal

/-!
# The two presentations of the fibre functor agree

Base change followed by realization was built twice: once directly,
so that additivity could be proved without an additive structure on
the module objects, and once as a composite, so that the monoidal
comparison could be read off.  The two are the same functor.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u}

/-- **The direct and composite presentations of the fibre functor
agree.** -/
theorem fibreFun_eq_fibreOver
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    fibreFun L R = fibreOver L R := rfl

/-- The composite presentation is additive. -/
instance fibreOver_additive
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    (fibreOver L R).Additive :=
  fibreFun_eq_fibreOver L R ▸ fibreFun_additive L R

end

end RS
