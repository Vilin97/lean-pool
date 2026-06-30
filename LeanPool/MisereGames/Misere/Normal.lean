/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import LeanPool.MisereGames.AugmentedForm
public import LeanPool.MisereGames.Misere.Comparison
public import LeanPool.MisereGames.Misere.Quotients
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Units.Basic

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

open Form
open Form.Misere.Outcome

public section

/-!
# Normal augmented forms

An augmented form is *normal* when every subposition is both Left and Right
end-like. Normal forms are invertible modulo any set of forms, so they form a
subgroup of the invertible subgroup of both the long augmented misère monoid
(all augmented forms) and the short one.

Note that comparing two normal forms modulo a promain set relies only on the
maintenance, since the proviso is always satisfied.
-/

/-! ### Comparison of end-like forms -/

namespace Form

variable {G : Type (u + 1)} [Form G]

/--
An end-like form wins going first against any end-like test form, so it is
strong.
-/
theorem Strong.of_isEndLike {A : G → Prop} {h : G} {p : Player} (hh : IsEndLike p h) :
    Strong A h p :=
  fun _ _ hx => winsGoingFirst_of_isEndLike (IsEndLike.add_iff.mpr ⟨hh, hx⟩)

/--
When `g` and `h` are end-like for both players, the proviso is automatic, so `g
≥m A h` follows from maintenance alone.
-/
theorem misereGE_of_maintenance_of_isEndLike {A : G → Prop} [Hereditary A] {g h : G}
    (hg : IsEndLike .left g) (hh : IsEndLike .right h)
    (hr : Maintenance A g h .right) (hl : Maintenance A g h .left) : g ≥m A h :=
  Hereditary.misereGE_of_maintenance_proviso A hr hl
    (fun _ => Strong.of_isEndLike hh) (fun _ => Strong.of_isEndLike hg)

/--
For forms that are end-like for both players, comparison modulo a promain set
`A` drops the proviso: `g ≥m A h` is just maintenance.
-/
theorem misereGE_iff_maintenance_of_isEndLike {A IsAmbient : G → Prop}
    (h_promain : Promain IsAmbient A) {g h : G}
    (hg : ∀ p, IsEndLike p g) (hh : ∀ p, IsEndLike p h)
    (hgA : IsAmbient g) (hhA : IsAmbient h) :
    g ≥m A h ↔ Maintenance A g h .right ∧ Maintenance A g h .left := by
  rw [h_promain hgA hhA]
  exact ⟨fun ⟨hr, hl, _, _⟩ => ⟨hr, hl⟩,
    fun ⟨hr, hl⟩ => ⟨hr, hl, fun _ => Strong.of_isEndLike (hh .right),
      fun _ => Strong.of_isEndLike (hg .left)⟩⟩

end Form

/-!
### Normal forms
-/

namespace AugmentedForm

/--
An augmented form is normal if every subposition is end-like for both players.
-/
@[expose] def Normal (g : AugmentedForm) : Prop :=
  IsEndLike .left g ∧ IsEndLike .right g ∧
    ∀ p, ∀ h ∈ Form.moves p g, Normal h
termination_by g
decreasing_by exact Moves.Subposition.of_mem_moves (by assumption)

namespace Normal

theorem isEndLike {g : AugmentedForm} (hg : Normal g) (p : Player) :
    IsEndLike p g := by
  rw [Normal] at hg
  cases p
  · exact hg.1
  · exact hg.2.1

theorem moves {g h : AugmentedForm} (hg : Normal g) {p : Player}
    (hh : h ∈ Form.moves p g) : Normal h := by
  rw [Normal] at hg
  exact hg.2.2 p h hh

theorem add_neg_isEndLike {g : AugmentedForm} (hg : Normal g) (p : Player) :
    IsEndLike p (g + -g) := by
  rw [IsEndLike.add_iff]
  exact ⟨Normal.isEndLike hg p, by
    simpa [IsEndLike.neg_iff_neg] using Normal.isEndLike hg (-p)⟩

theorem neg {g : AugmentedForm} (hg : Normal g) : Normal (-g) := by
  rw [Normal]
  refine ⟨?_, ?_, ?_⟩
  · simpa [IsEndLike.neg_iff_neg] using hg.isEndLike .right
  · simpa [IsEndLike.neg_iff_neg] using hg.isEndLike .left
  · intro p h hh
    have hh' : -h ∈ Form.moves (-p) g := by
      simpa [moves_neg, Set.mem_neg] using hh
    simpa using Normal.neg (hg.moves hh')
termination_by g
decreasing_by exact Moves.Subposition.of_mem_moves (by assumption)

@[simp]
theorem zero : Normal (0 : AugmentedForm) := by
  rw [Normal]
  refine ⟨isEndLike_of_isEnd isEnd_zero, isEndLike_of_isEnd isEnd_zero, fun p h hh => ?_⟩
  simp [moves_zero] at hh

theorem add {g h : AugmentedForm} (hg : Normal g) (hh : Normal h) : Normal (g + h) := by
  rw [Normal]
  refine ⟨IsEndLike.add_iff.mpr ⟨hg.isEndLike .left, hh.isEndLike .left⟩,
    IsEndLike.add_iff.mpr ⟨hg.isEndLike .right, hh.isEndLike .right⟩, fun p k hk => ?_⟩
  rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at hk
  rcases hk with ⟨g', hg', rfl⟩ | ⟨h', hh', rfl⟩
  · exact Normal.add (hg.moves hg') hh
  · exact Normal.add hg (hh.moves hh')
termination_by (g, h)
decreasing_by all_goals form_wf

theorem misereGE_iff_maintenance {g h : AugmentedForm.{u}} (hg : Normal g) (hh : Normal h) :
    g ≥m IsLong h ↔
      Maintenance IsLong g h .right ∧ Maintenance IsLong g h .left :=
  misereGE_iff_maintenance_of_isEndLike
    (Form.Promain.of_downlinking_of_hereditary (IsAmbient := IsLong) (A := IsLong))
    hg.isEndLike hh.isEndLike (isLong _) (isLong _)

theorem misereGE_iff_maintenance_isShort {g h : AugmentedForm.{u}}
    (hgs : IsShort g) (hhs : IsShort h) (hg : Normal g) (hh : Normal h) :
    g ≥m IsShort h ↔ Maintenance IsShort g h .right ∧ Maintenance IsShort g h .left :=
  misereGE_iff_maintenance_of_isEndLike
    (Form.Promain.of_downlinking_of_hereditary (IsAmbient := IsShort) (A := IsShort))
    hg.isEndLike hh.isEndLike hgs hhs

private theorem add_neg_misereGE_zero {g : AugmentedForm} (hg : Normal g) :
    MisereGE IsLong (g + -g) 0 := by
  refine misereGE_of_maintenance_of_isEndLike (hg.add_neg_isEndLike .left)
    (isEndLike_of_isEnd isEnd_zero) ?_ ?_
  · intro gr hgr
    rw [moves_add, Set.mem_union, Set.mem_image] at hgr
    rcases hgr with ⟨gr, hgr, rfl⟩ | ⟨ngr, hngr, rfl⟩
    · refine Or.inr ⟨gr + -gr, ?_, ?_⟩
      · exact add_left_mem_moves_add (z := gr) (by
          rw [moves_neg, Set.mem_neg]
          simpa using hgr)
      · exact add_neg_misereGE_zero (hg.moves hgr)
    · have hngr' : -ngr ∈ Form.moves Player.left g := by
        simpa [moves_neg, Set.mem_neg] using hngr
      refine Or.inr ⟨(-ngr) + ngr, ?_, ?_⟩
      · exact add_right_mem_moves_add hngr' ngr
      · simpa using add_neg_misereGE_zero (hg.moves hngr')
  · intro hl hhl
    simp at hhl
termination_by g
decreasing_by all_goals exact Moves.Subposition.of_mem_moves (by assumption)

private theorem zero_misereGE_add_neg {g : AugmentedForm} (hg : Normal g) :
    MisereGE IsLong 0 (g + -g) := by
  refine misereGE_of_maintenance_of_isEndLike (isEndLike_of_isEnd isEnd_zero)
    (hg.add_neg_isEndLike .right) ?_ ?_
  · intro gr hgr
    simp at hgr
  · intro hl hhl
    rw [moves_add, Set.mem_union, Set.mem_image] at hhl
    rcases hhl with ⟨gl, hgl, rfl⟩ | ⟨ngl, hngl, rfl⟩
    · refine Or.inr ⟨gl + -gl, ?_, ?_⟩
      · exact add_left_mem_moves_add (z := gl) (by
          rw [moves_neg, Set.mem_neg]
          simpa using hgl)
      · exact zero_misereGE_add_neg (hg.moves hgl)
    · have hngl' : -ngl ∈ Form.moves Player.right g := by
        simpa [moves_neg, Set.mem_neg] using hngl
      refine Or.inr ⟨(-ngl) + ngl, ?_, ?_⟩
      · exact add_right_mem_moves_add hngl' ngl
      · simpa using zero_misereGE_add_neg (hg.moves hngl')
termination_by g
decreasing_by all_goals exact Moves.Subposition.of_mem_moves (by assumption)

theorem add_neg_misereEQ_zero {g : AugmentedForm} (hg : Normal g) :
    MisereEQ IsLong (g + -g) 0 :=
  MisereEq.of_antisymm (add_neg_misereGE_zero hg) (zero_misereGE_add_neg hg)

theorem neg_add_misereEQ_zero {g : AugmentedForm} (hg : Normal g) :
    MisereEQ IsLong (-g + g) 0 := by
  simpa [add_comm] using add_neg_misereEQ_zero hg

end Normal

end AugmentedForm

/-!
### The augmented misère monoids and the 'normal' subgroup
-/

open AugmentedForm (Normal)

namespace Form

namespace MisereQuotient

namespace Augmented

/--
The long augmented misère monoid: augmented forms modulo misère equality.
-/
abbrev LongQuotient : Type (u + 1) :=
  MisereQuotient (G := AugmentedForm.{u}) IsLong

/--
The class of an augmented form in the long quotient.
-/
noncomputable def mkLong (g : AugmentedForm.{u}) : LongQuotient.{u} :=
  mk (A := IsLong) ⟨g, isLong _⟩

@[simp]
theorem mkLong_add (g h : AugmentedForm.{u}) :
    mkLong (g + h) = mkLong g + mkLong h :=
  (mk_add_mk (A := IsLong) ⟨g, isLong _⟩ ⟨h, isLong _⟩).symm

@[simp]
theorem mkLong_zero : mkLong (0 : AugmentedForm.{u}) = 0 :=
  mk_zero

theorem mkLong_add_neg {g : AugmentedForm.{u}} (hg : Normal g) :
    mkLong g + mkLong (-g) = 0 :=
  sound fun x _ => hg.add_neg_misereEQ_zero x (isLong _)

theorem mkLong_neg_add {g : AugmentedForm.{u}} (hg : Normal g) :
    mkLong (-g) + mkLong g = 0 :=
  sound fun x _ => hg.neg_add_misereEQ_zero x (isLong _)

theorem isAddUnit_mkLong_of_normal {g : AugmentedForm.{u}}
    (hg : Normal g) : IsAddUnit (mkLong g) :=
  isAddUnit_iff_exists.mpr ⟨mkLong (-g), mkLong_add_neg hg, mkLong_neg_add hg⟩

/--
The normal augmented forms form a subgroup of the invertible subgroup of the
long quotient monoid.
-/
noncomputable def normalLong : AddSubgroup (AddUnits LongQuotient.{u}) where
  carrier := {a | ∃ g : AugmentedForm.{u}, Normal g ∧ (↑a : LongQuotient.{u}) = mkLong g}
  zero_mem' := ⟨0, Normal.zero, by rw [AddUnits.val_zero, mkLong_zero]⟩
  add_mem' := by
    rintro a b ⟨g, hg, hga⟩ ⟨h, hh, hhb⟩
    exact ⟨g + h, hg.add hh, by rw [AddUnits.val_add, hga, hhb, mkLong_add]⟩
  neg_mem' := by
    rintro a ⟨g, hg, hga⟩
    refine ⟨-g, hg.neg, ?_⟩
    rw [← zero_add (mkLong (-g)), ← AddUnits.neg_add a, add_assoc, hga,
      mkLong_add_neg hg, add_zero]

/--
The short augmented misère monoid: short augmented forms modulo misère
equality.
-/
abbrev ShortQuotient : Type (u + 1) :=
  MisereQuotient (G := AugmentedForm.{u}) IsShort

/--
The class of a short augmented form in the short quotient.
-/
noncomputable def mkShort (g : AugmentedForm.{u}) (hg : IsShort g) : ShortQuotient.{u} :=
  mk ⟨g, hg⟩

@[simp]
theorem mkShort_add (g h : AugmentedForm.{u}) (hg : IsShort g) (hh : IsShort h) :
    mkShort (g + h) (Short.add hg hh) = mkShort g hg + mkShort h hh :=
  (mk_add_mk ⟨g, hg⟩ ⟨h, hh⟩).symm

@[simp]
theorem mkShort_zero : mkShort (0 : AugmentedForm.{u}) Short.zero = 0 :=
  mk_zero

theorem mkShort_add_neg {g : AugmentedForm.{u}} (hgs : IsShort g)
    (hg : Normal g) : mkShort g hgs + mkShort (-g) (Short.neg hgs) = 0 :=
  sound fun x _ => hg.add_neg_misereEQ_zero x (isLong _)

theorem mkShort_neg_add {g : AugmentedForm.{u}} (hgs : IsShort g)
    (hg : Normal g) : mkShort (-g) (Short.neg hgs) + mkShort g hgs = 0 :=
  sound fun x _ => hg.neg_add_misereEQ_zero x (isLong _)

theorem isAddUnit_mkShort_of_normal {g : AugmentedForm.{u}} (hgs : IsShort g)
    (hg : Normal g) : IsAddUnit (mkShort g hgs) :=
  isAddUnit_iff_exists.mpr
    ⟨mkShort (-g) (Short.neg hgs), mkShort_add_neg hgs hg, mkShort_neg_add hgs hg⟩

/--
The short normal augmented forms form a subgroup of the invertible subgroup of
the short quotient monoid.
-/
noncomputable def normalShort : AddSubgroup (AddUnits ShortQuotient.{u}) where
  carrier := {a | ∃ (g : AugmentedForm.{u}) (hgs : IsShort g),
    Normal g ∧ (↑a : ShortQuotient.{u}) = mkShort g hgs}
  zero_mem' :=
    ⟨0, Short.zero, Normal.zero, by rw [AddUnits.val_zero, mkShort_zero]⟩
  add_mem' := by
    rintro a b ⟨g, hgs, hg, hga⟩ ⟨h, hhs, hh, hhb⟩
    exact ⟨g + h, Short.add hgs hhs, hg.add hh, by
      rw [AddUnits.val_add, hga, hhb, mkShort_add]⟩
  neg_mem' := by
    rintro a ⟨g, hgs, hg, hga⟩
    refine ⟨-g, Short.neg hgs, hg.neg, ?_⟩
    rw [← zero_add (mkShort (-g) (Short.neg hgs)), ← AddUnits.neg_add a, add_assoc, hga,
      mkShort_add_neg hgs hg, add_zero]

end Augmented

end MisereQuotient

end Form

end

end MisereGames
