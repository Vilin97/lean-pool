/-
Copyright (c) 2026 Luka Opravš. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luka Opravš
-/
import Mathlib.Data.FinEnum
import LeanPool.PolyaEnumerationTheorem.Basic

/-!
# Reduction to `Fin`

If we have a bijection `X → Fin n`, then the number of distinct colorings of `X` with colors in `Y`
under the group action of `G` on `X` is equal to the number of distinct colorings of `Fin n` with
colors in `Y` under the induced group action of `G` on `Fin n`. This allows us to use `Fin n`
instead of more complex types when working with numbers of distinct colorings.
-/

universe u v w

namespace LeanPool.PolyaEnumerationTheorem

namespace ReductionToFin

open DistinctColorings

variable (X : Type u) (Y : Type v) (G : Type w) [enum : FinEnum X]

/-- Given a bijection `enum.equiv : X → Fin enum.card` and a group action of `G` on `X`, construct
    a group action of `G` on `Fin enum.card` with `g • i ↦ enum.equiv (g • (enum.equiv⁻¹ i))`. -/
instance MulActionFin [Monoid G] [MulAction G X] : MulAction G (Fin (enum.card)) where
  smul := fun g i ↦ enum.equiv.1 (g • (enum.equiv.2 i))
  one_smul := by
    intro b
    change enum.equiv ((1 : G) • (enum.equiv.symm b)) = b
    rw [one_smul, enum.equiv.apply_symm_apply]
  mul_smul := by
    intro x y b
    change enum.equiv ((x * y) • enum.equiv.symm b) =
      enum.equiv (x • enum.equiv.symm (enum.equiv (y • enum.equiv.symm b)))
    rw [enum.equiv.symm_apply_apply, mul_smul]

variable [Group G] [MulAction G X]

private lemma smul_fin_eq (g : G) (i : Fin enum.card) :
    (g • i : Fin enum.card) = enum.equiv (g • enum.equiv.symm i) := rfl

private lemma smul_inv_fin (g : G) (i : Fin enum.card) :
    enum.equiv.symm (g • i : Fin enum.card) = g • enum.equiv.symm i := by
  rw [smul_fin_eq, enum.equiv.symm_apply_apply]

/-- Forward map: a coloring of `X` to a coloring of `Fin enum.card`. -/
private def fwdColoring (f : X → Y) : Fin enum.card → Y := fun i => f (enum.equiv.symm i)

/-- Inverse map: a coloring of `Fin enum.card` to a coloring of `X`. -/
private def invColoring (f : Fin enum.card → Y) : X → Y := fun x => f (enum.equiv x)

private lemma fwd_inv (f : X → Y) : invColoring X Y (fwdColoring X Y f) = f := by
  funext x
  change f (enum.equiv.symm (enum.equiv x)) = f x
  rw [enum.equiv.symm_apply_apply]

private lemma inv_fwd (f : Fin enum.card → Y) : fwdColoring X Y (invColoring X Y f) = f := by
  funext i
  change f (enum.equiv (enum.equiv.symm i)) = f i
  rw [enum.equiv.apply_symm_apply]

private lemma fwd_smul (g : G) (f : X → Y) :
    fwdColoring X Y (g • f) = g • fwdColoring X Y f := by
  funext i
  change (g • f) (enum.equiv.symm i) = (g • fwdColoring X Y f) i
  change f (g⁻¹ • enum.equiv.symm i) = (fwdColoring X Y f) (g⁻¹ • i : Fin enum.card)
  change f (g⁻¹ • enum.equiv.symm i) = f (enum.equiv.symm ((g⁻¹ • i) : Fin enum.card))
  rw [smul_inv_fin]

private lemma inv_smul (g : G) (f : Fin enum.card → Y) :
    invColoring X Y (g • f) = g • invColoring X Y f := by
  funext x
  change (g • f) (enum.equiv x) = (g • invColoring X Y f) x
  change f (g⁻¹ • enum.equiv x : Fin enum.card) = (invColoring X Y f) (g⁻¹ • x)
  change f (g⁻¹ • enum.equiv x : Fin enum.card) = f (enum.equiv (g⁻¹ • x))
  change f (enum.equiv (g⁻¹ • enum.equiv.symm (enum.equiv x))) = f (enum.equiv (g⁻¹ • x))
  rw [enum.equiv.symm_apply_apply]

/-- A bijection between the distinct colorings of `X` with colors in `Y` under the group action
    of `G` on `X` and the distinct colorings of `Fin enum.card` with colors in `Y` under the
    induced group action of `G` on `Fin enum.card`. -/
def equiv_of_quotient_of_quotient_Fin :
    (Quotient (MulAction.orbitRel G (X → Y))) ≃
      (Quotient (MulAction.orbitRel G (Fin enum.card → Y))) where
  toFun := Quotient.map (fwdColoring X Y) (by
    rintro f₁ f₂ ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [← hg, fwd_smul])
  invFun := Quotient.map (invColoring X Y) (by
    rintro f₁ f₂ ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [← hg, inv_smul])
  left_inv := by
    intro q
    rcases Quotient.mk_surjective q with ⟨f, rfl⟩
    change ⟦invColoring X Y (fwdColoring X Y f)⟧ = ⟦f⟧
    rw [fwd_inv]
  right_inv := by
    intro q
    rcases Quotient.mk_surjective q with ⟨f, rfl⟩
    change ⟦fwdColoring X Y (invColoring X Y f)⟧ = ⟦f⟧
    rw [inv_fwd]

/-- An instance of `Fintype` for the distinct colorings of `Fin enum.card` with colors in `Y` under
    the induced group action of `G` on `Fin enum.card`. Required by
    `numDistinctColorings_eq_numDistinctColorings_of_Fin`. -/
instance [Fintype (Quotient (MulAction.orbitRel G (X → Y)))] :
    Fintype (Quotient (MulAction.orbitRel G (Fin enum.card → Y))) :=
  Fintype.ofEquiv (Quotient (MulAction.orbitRel G (X → Y)))
    (equiv_of_quotient_of_quotient_Fin X Y G)

/-- The number of distinct colorings of `X` with colors in `Y` under the group action of `G` on
    `X` is equal to the number of distinct colorings of `Fin enum.card` with colors in `Y` under
    the induced group action of `G` on `Fin enum.card`. -/
lemma numDistinctColorings_eq_numDistinctColorings_of_Fin
    [Fintype (Quotient (MulAction.orbitRel G (X → Y)))] :
    numDistinctColorings X Y G = numDistinctColorings (Fin (enum.card)) Y G :=
  Fintype.card_congr (equiv_of_quotient_of_quotient_Fin X Y G)

end ReductionToFin

end LeanPool.PolyaEnumerationTheorem
