/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.AugmentedForm
public import LeanPool.MisereGames.Form.Misere.Outcome
public import LeanPool.MisereGames.Form.Misere.Adjoint

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

open Form
open Form.Misere.Outcome

namespace AugmentedForm

public section

/-- Lift an augmented form to the next universe level. -/
noncomputable def liftSucc (g : AugmentedForm.{u}) : AugmentedForm.{u + 1} :=
  ofSetsWithTombs
    (fun p => Set.range (fun y : moves p g => liftSucc y.val))
    (fun p => g.hasTombstone p)
  termination_by g
  decreasing_by form_wf

@[simp]
theorem moves_liftSucc (p : Player) (g : AugmentedForm.{u}) :
    moves p (liftSucc g) = liftSucc '' moves p g := by
  rw [liftSucc, moves_ofSetsWithTombs]
  ext x
  simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_image]

@[simp]
theorem hasTombstone_liftSucc (p : Player) (g : AugmentedForm.{u}) :
    (liftSucc g).hasTombstone p ↔ g.hasTombstone p := by
  rw [liftSucc, hasTombstone_ofSetsWithTombs]

theorem liftSucc_injective : Function.Injective liftSucc := by
  intro a b hab
  induction a using AugmentedForm.moveRecOn generalizing b with
  | mk a ha =>
    induction b using AugmentedForm.moveRecOn with
    | mk b hb =>
      ext p x
      · replace hab := congr_arg (fun g => moves p g) hab
        simp at hab
        constructor <;> intro hx
        · obtain ⟨y, hy, hy'⟩ := hab.subset ⟨x, hx, rfl⟩
          exact Set.mem_of_eq_of_mem (ha p x hx (Eq.symm hy')) hy
        · obtain ⟨y, hy, hy'⟩ := hab.symm.subset ⟨x, hx, rfl⟩
          exact Set.mem_of_eq_of_mem (Eq.symm (ha p y hy hy')) hy
      · replace hab := congr_arg (fun g => hasTombstone p g) hab
        simpa only [hasTombstone_liftSucc, eq_iff_iff] using hab

@[simp]
theorem isEnd_liftSucc (p : Player) (g : AugmentedForm.{u}) :
    IsEnd p (liftSucc g) ↔ IsEnd p g := by
  rw [isEnd_def, isEnd_def, moves_liftSucc, Set.image_eq_empty]

@[simp]
theorem isEndLike_liftSucc (p : Player) (g : AugmentedForm.{u}) :
    IsEndLike p (liftSucc g) ↔ IsEndLike p g := by
  rw [IsEndLike_iff, IsEndLike_iff, hasTombstone_liftSucc, isEnd_liftSucc]

@[simp]
theorem liftSucc_add (a b : AugmentedForm.{u}) :
    liftSucc (a + b) = liftSucc a + liftSucc b := by
  induction a using AugmentedForm.moveRecOn generalizing b with
  | mk a ha =>
    induction b using AugmentedForm.moveRecOn with
    | mk b hb =>
      ext p
      · simp only [moves_liftSucc, moves_add, Set.image_union, Set.image_image, Set.mem_union,
                   Set.mem_image]
        grind only
      · simp [hasTombstone_add, hasTombstone_liftSucc, isEndLike_liftSucc]

@[simp]
theorem winsGoingFirst_liftSucc (p : Player) (g : AugmentedForm.{u}) :
    WinsGoingFirst p (liftSucc g) ↔ WinsGoingFirst p g := by
  induction g using AugmentedForm.moveRecOn generalizing p with
  | mk g hg =>
    rw [winsGoingFirst_iff, winsGoingFirst_iff]
    simp only [isEndLike_liftSucc, moves_liftSucc, Set.mem_image, exists_exists_and_eq_and]
    grind only

@[simp]
theorem misereOutcome_liftSucc (g : AugmentedForm.{u}) :
    MisereOutcome (liftSucc g) = MisereOutcome g := by
  unfold MisereOutcome MiserePlayerOutcome
  rw [winsGoingFirst_liftSucc, winsGoingFirst_liftSucc]

@[simp]
theorem liftSucc_zero : liftSucc (0 : AugmentedForm.{u}) = 0 := by
  ext p x
  · simp only [moves_liftSucc, moves_zero, Set.image_empty, Set.mem_empty_iff_false]
  · rw [<-AugmentedForm.hasTombstone_liftSucc p 0, <-AugmentedForm.ofGameForm_zero]
    simp only [hasTombstone_liftSucc, not_hasTombstone_ofGameForm, false_iff]
    exact not_hasTombstone_zero' p

@[simp]
theorem not_hasTombstone_adjoint {p : Player} {g : AugmentedForm.{u}} : ¬hasTombstone p (g°) := by
  rw [adjoint_def]
  split_ifs <;> simp

@[simp]
theorem liftSucc_adjoint (g : AugmentedForm.{u}) : liftSucc (g°) = (liftSucc g)° := by
  induction g using moveRecOn with
  | mk g ih =>
  apply AugmentedForm.ext
  · intro p
    rw [moves_liftSucc, Adjoint.moves p g, Adjoint.moves, isEnd_liftSucc, moves_liftSucc]
    by_cases h : IsEnd (-p) g
    · simp only [h, if_true, Set.image_singleton, liftSucc_zero]
    · rw [if_neg h, if_neg h, ← Set.image_comp, ← Set.image_comp]
      apply Set.image_congr
      intro y hy
      simpa only [Function.comp_apply] using ih (-p) y hy
  · simp only [hasTombstone_liftSucc, not_hasTombstone_adjoint, implies_true]

end

end AugmentedForm

end MisereGames
