/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreAdditive
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreEps
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaShift

/-!
# The fibre functor of a mixed sum

A mixed sum of `p` copies of the unit and `q` copies of the odd line
has for its fibre the free super module of rank `(p | q)`: the unit
contributes the algebra and the line contributes its parity shift,
and the fibre functor is additive.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u}

attribute [local instance] CategoryTheory.ModObj.regular

/-- **The free super module of rank `(p | q)`.** -/
noncomputable def superFree
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (p q : ℕ) : (gammaAlgebra D L R).Mod :=
  ⨁ fun i : Fin p ⊕ Fin q =>
    Sum.elim (fun _ => (gammaAlgebra D L R).unitMod)
      (fun _ => SuperCommAlgebra.Mod.shift
        (gammaAlgebra D L R).unitMod) i

/-- **The fibre of a mixed sum is free of the corresponding
rank.** -/
noncomputable def fibreMixIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] [IsCommMonObj R]
    (p q : ℕ) :
    (fibreFun L R).obj (L.mix p q) ≅ superFree L R p q :=
  fibreFunBiproduct L R
      (fun i : Fin p ⊕ Fin q =>
        Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) i) ≪≫
    biproduct.mapIso fun i =>
      match i with
      | Sum.inl _ => (fibreEpsIso L R).symm
      | Sum.inr _ => gammaShiftIso L R

end

end RS
