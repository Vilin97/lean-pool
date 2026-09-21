/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixShuffleLine

/-!
# Tensoring a mixed sum with the odd line

Tensoring the mixed sum `L.mix p q` with the odd line exchanges
the two kinds of summand: each unit summand becomes a line, by
the right unitor, and each line summand becomes a unit, by the
square of the line.  Reindexing along the swap of the summand
labels therefore identifies `L.obj ⊗ L.mix p q` with the mixed
sum `L.mix q p` of `q` copies of the unit and `p` copies of the
line.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- Tensoring a summand of `L.mix p q` with the line gives the
summand of `L.mix q p` at the swapped index: a unit summand
becomes a line, a line summand becomes a unit. -/
noncomputable def OddLine.twistSummandIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D)
    (p q : ℕ) :
    ∀ j : Fin p ⊕ Fin q,
      L.mixFun q p (Equiv.sumComm (Fin p) (Fin q) j) ≅
        L.obj ⊗ L.mixFun p q j
  | Sum.inl _ => (ρ_ L.obj).symm
  | Sum.inr _ => L.sq.symm

/-- **Twisting a mixed sum by the line**: tensoring with the odd
line turns `p` units and `q` lines into `q` units and `p` lines.
-/
noncomputable def OddLine.twistMixIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) :
    L.obj ⊗ L.mix p q ≅ L.mix q p :=
  leftDistributor L.obj (L.mixFun p q) ≪≫
    biproduct.whiskerEquiv (Equiv.sumComm (Fin p) (Fin q))
      (L.twistSummandIso p q)

end RS
