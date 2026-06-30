/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

import LeanPool.MisereGames.AugmentedForm.Short
public import LeanPool.MisereGames.AugmentedForm.Lift
public import LeanPool.MisereGames.Misere.Comparison
import LeanPool.MisereGames.Misere.LiftIncomparable -- for docs

/-!
Misere combinatorial games.
-/

namespace MisereGames

/-!

# Short Sets and Comparison

This is a mirror of `CombinatorialGames.Misere.LiftIncomparable` module with
the difference that if we are in a short universe then we do not need to
increase the universe level.

The main results are
- `g_misereEQ_h_short`
- `g_misereEQ_h_shortUniverse`
- `g_h_incomparable`
- `g_h_incomparable_longUniverse`
-/

universe u

open Form
open Form.Misere.Outcome
open Form.Misere.Adjoint

namespace AugmentedForm.Short

public section

/--
The set of all adjoints $J^\circ$ (lifted to $u + 1$) for all short $J$ in
universe $u$.
-/
noncomputable def adjointsOfShort : Set AugmentedForm.{u} :=
  Set.range (fun J : {x : AugmentedForm.{u} | IsShort x} => (J : AugmentedForm.{u})°)

instance smallShortAdjoints : Small.{u} (adjointsOfShort.{u}) := by
  unfold adjointsOfShort
  exact small_range _

/--
$G = \{ J^\circ \mid J^\circ \}$ for all short $J$ in universe $u$.
-/
noncomputable def g : AugmentedForm.{u} := !{adjointsOfShort | adjointsOfShort}

instance smallInsertG : Small.{u} (insert g adjointsOfShort : Set AugmentedForm.{u}) := by
  infer_instance

/--
$H = \{ G, J^\circ \mid G, J^\circ \}$ for all short $J$ in universe $u$.
-/
noncomputable def h : AugmentedForm.{u} :=
  !{insert g adjointsOfShort | insert g adjointsOfShort}

theorem adjoint_mem_adjointsOfShort {X : AugmentedForm.{u}} (hX : IsShort X) :
    X° ∈ adjointsOfShort :=
  ⟨⟨X, hX⟩, rfl⟩

@[simp]
theorem moves_g (p : Player) : moves p g = adjointsOfShort := by
  cases p <;> simp [g]

@[simp]
theorem moves_h (p : Player) :
    moves p h = insert g adjointsOfShort := by
  cases p <;> simp [h]

theorem bigG_not_isEndLike (p : Player) : ¬ IsEndLike p g := by
  rw [AugmentedForm.IsEndLike_iff]
  cases p <;> simp +decide only [isEnd_def, moves_g, not_or]
  · exact ⟨by unfold g; simp +decide [hasTombstone_ofSets],
      Set.Nonempty.ne_empty ⟨_, adjoint_mem_adjointsOfShort Short.zero⟩⟩
  · refine ⟨?_, Set.Nonempty.ne_empty ⟨_, adjoint_mem_adjointsOfShort Short.zero⟩⟩
    unfold g; simp +decide [AugmentedForm.hasTombstone_ofSets]

theorem bigH_not_isEndLike (p : Player) : ¬ IsEndLike p h := by
  rw [AugmentedForm.IsEndLike_iff]
  cases p <;> simp +decide only [isEnd_def, moves_h, not_or]
  all_goals exact ⟨by unfold h; simp +decide [hasTombstone_ofSets],
    Set.Nonempty.ne_empty ⟨_, Set.mem_insert _ _⟩⟩

theorem misereOutcome_g_add_short {x : AugmentedForm.{u}} (h_isShort : IsShort x) :
    MisereOutcome (g + x) = Outcome.N := by
  rw [misereOutcome_N_iff_winsGoingFirst, add_comm]
  constructor <;> apply winsGoingFirst_of_moves
  · use x + x°
    constructor
    · apply add_left_mem_moves_add
      exact moves_g Player.left ▸ adjoint_mem_adjointsOfShort h_isShort
    · exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P x)
  · use x + x°
    constructor
    · apply add_left_mem_moves_add
      exact moves_g Player.right ▸ adjoint_mem_adjointsOfShort h_isShort
    · exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P x)

theorem misereOutcome_h_add_short {x : AugmentedForm.{u}} (h_isShort : IsShort x) :
    MisereOutcome (h + x) = Outcome.N := by
  rw [misereOutcome_N_iff_winsGoingFirst, add_comm]
  constructor <;> apply winsGoingFirst_of_moves
  · use x + x°
    constructor
    · apply add_left_mem_moves_add
      exact moves_h Player.left ▸ Set.mem_insert_of_mem _ (adjoint_mem_adjointsOfShort h_isShort)
    · exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P x)
  · use x + x°
    constructor
    · apply add_left_mem_moves_add
      exact moves_h Player.right ▸ Set.mem_insert_of_mem _ (adjoint_mem_adjointsOfShort h_isShort)
    · exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P x)

theorem g_not_isEndLike (p : Player) : ¬ IsEndLike p g := by
  rw [AugmentedForm.IsEndLike_iff, not_or]
  constructor
  · simp only [g, hasTombstone_ofSets, not_false_eq_true]
  · cases p <;> simp only [g, adjointsOfShort, Set.coe_setOf, Set.mem_setOf_eq,
                           isEnd_def, leftMoves_ofSets, rightMoves_ofSets, Set.range_eq_empty_iff,
                           nonempty_subtype, not_isEmpty_of_nonempty, not_false_eq_true,
                           Exists.intro 0 Short.zero, ]

private theorem not_winsGoingFirst_g_add_g {p : Player} :
    ¬WinsGoingFirst p (g + g) := by
  rw [not_winsGoingFirst_iff]
  · constructor
    · simp [g_not_isEndLike]
    · intro g' h_g'_mem
      simp only [moves_add, moves_g, Set.mem_union, Set.mem_image] at h_g'_mem
      obtain (⟨x, ⟨⟨y, h_y_isShort⟩, rfl⟩, rfl⟩ | ⟨x, ⟨⟨y, h_y_isShort⟩, rfl⟩, rfl⟩) := h_g'_mem
      · apply winsGoingFirst_of_moves
        use (y°) + ((y°)°)
        constructor
        · apply add_left_mem_moves_add
          exact moves_g _ ▸ adjoint_mem_adjointsOfShort (Adjoint.short_adjoint h_y_isShort)
        · apply not_winsGoingFirst_of_misereOutcome_P
          exact misereOutcome_add_adjoint_eq_P (y°)
      · rw [add_comm]
        apply winsGoingFirst_of_moves
        use (y°) + ((y°)°)
        constructor
        · apply add_left_mem_moves_add
          exact moves_g _ ▸ adjoint_mem_adjointsOfShort (Adjoint.short_adjoint h_y_isShort)
        · apply not_winsGoingFirst_of_misereOutcome_P
          exact misereOutcome_add_adjoint_eq_P (y°)

theorem misereOutcome_g_add_g : MisereOutcome (g + g) = Outcome.P := by
  simp [misereOutcome_P_iff_winsGoingFirst, not_winsGoingFirst_g_add_g]

theorem misereOutcome_h_add_g : MisereOutcome (h + g) = Outcome.N := by
  rw [misereOutcome_N_iff_winsGoingFirst]
  constructor <;> apply winsGoingFirst_of_moves
  · use g + g
    constructor
    · apply add_right_mem_moves_add
      exact moves_h Player.left ▸ Set.mem_insert _ _
    · exact not_winsGoingFirst_of_misereOutcome_P misereOutcome_g_add_g
  · use g + g
    constructor
    · apply add_right_mem_moves_add
      exact moves_h Player.right ▸ Set.mem_insert _ _
    · exact not_winsGoingFirst_of_misereOutcome_P misereOutcome_g_add_g

theorem g_misereEQ_h_short (A : AugmentedForm.{u} → Prop) (h_short : ∀ x, A x → IsShort x) :
    g =m A h := by
  intro x hx
  rw [misereOutcome_g_add_short (h_short x hx), misereOutcome_h_add_short (h_short x hx)]

theorem g_misereEQ_h_shortUniverse (U : AugmentedForm.{u} → Prop) [ShortUniverse U] :
    MisereEQ U g h :=
  g_misereEQ_h_short U (fun _ hx => Universe.isAmbient_of_mem hx)

theorem g_h_incomparable {A : AugmentedForm.{u} → Prop} (h_Ag : A g) :
    ¬(g ≥m A h) ∧ ¬ (h ≥m A g) := by
  constructor
  all_goals
  · intro h
    have := h _ h_Ag
    simp +decide only [misereOutcome_g_add_g, misereOutcome_h_add_g, ge_iff_le] at this

/--
$G$ is in any universe $\mathcal{U}$ in $u$.
-/
theorem g_mem_longUniverse (U : AugmentedForm.{u} → Prop) [LongUniverse U] :
     U g := by
  have h_ambient : Ambient (IsLong : AugmentedForm.{u} → Prop) := inferInstance
  have h_mem : ∀ b ∈ adjointsOfShort.{u}, U b := by
    rintro b ⟨⟨J, h_j⟩, rfl⟩
    exact Form.rootedAdjoint_mem_of_isAmbient (r := 0)
      (Universe.zero_mem IsLong) (fun _ _ => isLong _) (isLong _)
  have h_notempty : (adjointsOfShort.{u}).Nonempty := ⟨_,  adjoint_mem_adjointsOfShort Short.zero⟩
  exact ClosedUnderDicotic.closed_dicotic (IsAmbient := IsLong)
    adjointsOfShort adjointsOfShort h_mem h_mem h_notempty h_notempty (isLong _)

theorem g_h_incomparable_longUniverse (U : AugmentedForm.{u} → Prop) [LongUniverse U] :
    ¬(g ≥m U h) ∧ ¬ (h ≥m U g) :=
  g_h_incomparable (g_mem_longUniverse U)

end

end AugmentedForm.Short

end MisereGames
