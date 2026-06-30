/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.AugmentedForm
public import LeanPool.MisereGames.Form.Short

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

open Form

public section

/--
A concrete encoding of the data of a short augmented form: a finite list of
Left options, a finite list of Right options, and two tombstone bits. As an
inductive type in `Type 0`, it is `Small.{u}` for every `u`.
-/
inductive ShortTree : Type
  | mk (L R : List ShortTree) (tL tR : Bool) : ShortTree

namespace ShortTree

/--
Interpret a `ShortTree` as an augmented form.
-/
noncomputable def toForm : ShortTree → AugmentedForm.{u}
  | .mk L R tL tR =>
      AugmentedForm.ofSetsWithTombs
        (fun p => Set.range (fun i : Fin (p.cases L R).length =>
            ShortTree.toForm ((p.cases L R).get i)))
        (fun p => p.cases tL tR)
  decreasing_by
    cases p
    all_goals
      simp only [Player.cases, ShortTree.mk.sizeOf_spec]
      have h := List.sizeOf_get _ i
      simp only [Player.cases] at h
      omega

@[simp]
theorem moves_toForm (p : Player) (L R : List ShortTree) (tL tR : Bool) :
    moves p (toForm (.mk L R tL tR)) = toForm '' {y | y ∈ p.cases L R} := by
  rw [toForm, AugmentedForm.moves_ofSetsWithTombs]
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, List.get_mem _ _, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hy
    exact ⟨i, rfl⟩

@[simp]
theorem hasTombstone_toForm (p : Player) (L R : List ShortTree) (tL tR : Bool) :
    (toForm (.mk L R tL tR)).hasTombstone p = p.cases tL tR := by
  rw [toForm, AugmentedForm.hasTombstone_ofSetsWithTombs]

/--
Any finite set of augmented forms, each of which is in the range of `toForm`,
is the image under `toForm` of (the set of members of) some list.
-/
theorem exists_list_image (S : Set AugmentedForm.{u}) (hfin : S.Finite)
    (h_ext : ∀ y ∈ S, ∃ t : ShortTree, toForm t = y) :
    ∃ L : List ShortTree, toForm '' {y | y ∈ L} = S := by
  choose f hf using h_ext
  refine ⟨hfin.toFinset.attach.toList.map (fun y => f y.val (hfin.mem_toFinset.mp y.prop)), ?_⟩
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map, Finset.mem_toList,
    Finset.mem_attach, true_and, Subtype.exists, hfin.mem_toFinset]
  constructor
  · rintro ⟨t, ⟨z, hz, rfl⟩, rfl⟩; rw [hf z hz]
    exact hz
  · intro hy
    exact ⟨f y hy, ⟨y, hy, rfl⟩, hf y hy⟩

/--
Every short augmented form is in the range of `toForm`.
-/
theorem isShort_mem_range_toForm {x : AugmentedForm.{u}} (h_isShort : IsShort x) :
    ∃ t : ShortTree, toForm t = x := by
  induction x using AugmentedForm.moveRecOn with
  | mk x ih =>
    classical
    obtain ⟨L, hL⟩ := exists_list_image (moves .left x) (Short.finite_moves .left h_isShort)
      (fun y hy => ih .left y hy (Short.of_mem_moves h_isShort hy))
    obtain ⟨R, hR⟩ := exists_list_image (moves .right x) (Short.finite_moves .right h_isShort)
      (fun y hy => ih .right y hy (Short.of_mem_moves h_isShort hy))
    refine ⟨.mk L R (decide (x.hasTombstone .left)) (decide (x.hasTombstone .right)), ?_⟩
    refine AugmentedForm.ext (fun p => ?_) (fun p => ?_)
    · rw [moves_toForm]
      cases p <;> assumption
    · rw [hasTombstone_toForm]
      cases p <;> simp only [Player.cases, decide_eq_true_eq]

end ShortTree

-- TODO: There MUST be a simpler way to get this instance

/--
The set of all short augmented forms definable in `u` is `u`-small.
-/
instance smallSetOfIsShort : Small.{u} {x : AugmentedForm.{u} | IsShort x} := by
  apply small_subset (s := Set.range ShortTree.toForm)
  intro x hx
  obtain ⟨t, ht⟩ := ShortTree.isShort_mem_range_toForm hx
  exact ⟨t, ht⟩

end

end MisereGames
