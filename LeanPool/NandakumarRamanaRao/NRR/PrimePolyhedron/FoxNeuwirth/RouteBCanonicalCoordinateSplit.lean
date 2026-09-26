/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBSelectedVectorBlock
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Logic.Equiv.Set

/-!
# Route B: canonical split of the selected local vector block

For a `MixedFaceCase`, the `p` scalar coordinates at the selected retained
vertex are pairwise distinct movable quotient-orbit parameters.  This file
uses their range as a canonical selected index subtype and splits the complete
movable product into selected and complementary coordinates.

This construction
requires no additional coordinate-equivalence hypothesis.
-/

@[expose] public section

namespace NRR

open FoxNeuwirthOrderComplex
open MeasureTheory

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open Parameters
open RelativeGenericity

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

namespace MixedFaceCase

/-- Predicate selecting precisely the `p` movable scalar-orbit parameters of
one retained local vertex. -/
def IsSelectedVectorParameter
    (κ : MixedFaceCase hp C) (q : MovableParameter hp C) : Prop :=
  q ∈ Set.range (κ.vectorParameter hp C)

noncomputable instance isSelectedVectorParameterDecidable
    (κ : MixedFaceCase hp C) :
    DecidablePred (κ.IsSelectedVectorParameter hp C) :=
  Classical.decPred _

/-- The selected scalar-orbit index subtype. -/
abbrev SelectedVectorParameter (κ : MixedFaceCase hp C) :=
  {q : MovableParameter hp C // κ.IsSelectedVectorParameter hp C q}

/-- The complementary movable scalar-orbit index subtype. -/
abbrev RemainingMovableParameter (κ : MixedFaceCase hp C) :=
  {q : MovableParameter hp C // ¬ κ.IsSelectedVectorParameter hp C q}

/-- The coordinate map is an equivalence from `Fin p` onto the selected range. -/
noncomputable def vectorParameterEquiv
    (κ : MixedFaceCase hp C) :
    Fin p ≃ κ.SelectedVectorParameter hp C :=
  Equiv.ofInjective (κ.vectorParameter hp C) (κ.vectorParameter_injective hp C)

@[simp] theorem vectorParameterEquiv_apply_val
    (κ : MixedFaceCase hp C) (j : Fin p) :
    ((κ.vectorParameterEquiv hp C j : κ.SelectedVectorParameter hp C).1) =
      κ.vectorParameter hp C j := rfl

/-- Canonical measurable coordinate split into the selected block and its
complement. -/
noncomputable def parameterSplit
    (κ : MixedFaceCase hp C) :
    MovableParameterSpace hp C ≃ᵐ
      ((κ.SelectedVectorParameter hp C → Real) ×
       (κ.RemainingMovableParameter hp C → Real)) :=
  MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : MovableParameter hp C => Real)
    (κ.IsSelectedVectorParameter hp C)

/-- The canonical split preserves finite-product Lebesgue measure. -/
theorem parameterSplit_measurePreserving
    (κ : MixedFaceCase hp C) :
    MeasurePreserving (κ.parameterSplit hp C) volume volume := by
  simpa only [parameterSplit] using
    (MeasureTheory.volume_preserving_piEquivPiSubtypeProd
      (fun _ : MovableParameter hp C => Real)
      (κ.IsSelectedVectorParameter hp C))

@[simp] theorem parameterSplit_apply_selected
    (κ : MixedFaceCase hp C) (x : MovableParameterSpace hp C)
    (q : κ.SelectedVectorParameter hp C) :
    (κ.parameterSplit hp C x).1 q = x q.1 := rfl

@[simp] theorem parameterSplit_apply_remaining
    (κ : MixedFaceCase hp C) (x : MovableParameterSpace hp C)
    (q : κ.RemainingMovableParameter hp C) :
    (κ.parameterSplit hp C x).2 q = x q.1 := rfl

@[simp] theorem parameterSplit_symm_apply_selected
    (κ : MixedFaceCase hp C)
    (y : (κ.SelectedVectorParameter hp C → Real) ×
      (κ.RemainingMovableParameter hp C → Real))
    (q : κ.SelectedVectorParameter hp C) :
    (κ.parameterSplit hp C).symm y q.1 = y.1 q := by
  change (if h : κ.IsSelectedVectorParameter hp C q.1 then y.1 ⟨q.1, h⟩
    else y.2 ⟨q.1, h⟩) = y.1 q
  simp [q.2]

@[simp] theorem parameterSplit_symm_apply_remaining
    (κ : MixedFaceCase hp C)
    (y : (κ.SelectedVectorParameter hp C → Real) ×
      (κ.RemainingMovableParameter hp C → Real))
    (q : κ.RemainingMovableParameter hp C) :
    (κ.parameterSplit hp C).symm y q.1 = y.2 q := by
  change (if h : κ.IsSelectedVectorParameter hp C q.1 then y.1 ⟨q.1, h⟩
    else y.2 ⟨q.1, h⟩) = y.2 q
  simp [q.2]

/-- The local parameter at the selected vertex and coordinate `j` belongs to
the selected block. -/
theorem localParameter_selected
    (κ : MixedFaceCase hp C) (j : Fin p) :
    κ.IsSelectedVectorParameter hp C (κ.vectorParameter hp C j) := by
  exact ⟨j, rfl⟩

/-- A local scalar site at another vertex of the same cell cannot belong to the
selected block. -/
theorem localParameter_not_selected_of_vertex_ne
    (κ : MixedFaceCase hp C)
    (i : Fin (p + 1)) (hi : i ≠ κ.retained) (j : Fin p)
    (hmovable : ¬ IsFrozenParameter hp C (localParameter hp C κ.cell i j)) :
    ¬ κ.IsSelectedVectorParameter hp C
      (⟨localParameter hp C κ.cell i j, hmovable⟩ : MovableParameter hp C) := by
  rintro ⟨k, hk⟩
  have hval :
      localParameter hp C κ.cell κ.retained k =
        localParameter hp C κ.cell i j := by
    exact congrArg Subtype.val hk
  have hpair := localParameter_injective hp C κ.cell
    (show (fun z : Fin (p + 1) × Fin p =>
      localParameter hp C κ.cell z.1 z.2) (κ.retained, k) =
      (fun z : Fin (p + 1) × Fin p =>
        localParameter hp C κ.cell z.1 z.2) (i, j) from hval)
  exact hi (congrArg Prod.fst hpair).symm

end MixedFaceCase

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
