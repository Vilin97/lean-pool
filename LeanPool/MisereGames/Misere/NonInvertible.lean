/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Form.Misere.Outcome
public import LeanPool.MisereGames.Form.Misere.Adjoint
import Mathlib.Data.Set.Finite.Range

/-!
Misere combinatorial games.
-/

namespace MisereGames

open GameForm
open Form
open Form.Misere.Outcome
open Misere.Adjoint

public section

/--
Definition of $T$ from [Siegel, "Combinatorial Game Theory" (Theorem 6.6 on p.
270)][siegel:CombinatorialGameTheory:2013]:
$$
T = \left\{ \left( H^R \right)^{\circ} \mid \left\{ \cdot \mid \left( G^L
\right)^{\circ} \right\} \right\}.
$$
-/
noncomputable def leftEndNotLeftEndNotGeAuxT (g h : GameForm) : GameForm :=
  !{ Set.range fun hr : moves .right h => (hr : GameForm)°
   | { !{∅ | Set.range fun gl : moves .left g => (gl : GameForm)°} } }

/--
$T$ is short if $G$ and $H$ are short.
-/
theorem short_auxT {g h : GameForm} (h_g : IsShort g) (h_h : IsShort h)
    : IsShort (leftEndNotLeftEndNotGeAuxT g h) := by
  unfold leftEndNotLeftEndNotGeAuxT
  rw [short_def]
  intro p
  change (moves p _).Finite ∧ ∀ y ∈ moves p _, IsShort y
  constructor
  · cases p
    · simp only [moves_ofSets, Player.cases]
      have : Finite (moves .right h) := Short.finite_moves .right h_h
      exact Set.finite_range (fun hr : moves .right h => (hr : GameForm)°)
    · simp only [moves_ofSets, Player.cases, Set.finite_singleton]
  · intro gp h3
    cases p <;>
      simp only [moves_ofSets, Player.cases, Set.mem_singleton_iff, Set.mem_range,
        Subtype.exists, exists_prop] at h3
    · obtain ⟨gp', h3, h4⟩ := h3
      rw [<-h4]
      have h_gp' : IsShort gp' := Short.of_mem_moves h_h h3
      exact Adjoint.short_adjoint h_gp'
    · rw [h3, short_def]
      intro p
      change (moves p _).Finite ∧ ∀ y ∈ moves p _, IsShort y
      constructor <;> cases p
      · simp only [moves_ofSets, Player.cases, Set.finite_empty]
      · simp only [moves_ofSets, Player.cases]
        have : Finite (moves .left g) := Short.finite_moves .left h_g
        exact Set.finite_range (fun gl : moves .left g => (gl : GameForm)°)
      · simp only [moves_ofSets, Player.cases, Set.mem_empty_iff_false,
                   IsEmpty.forall_iff, implies_true]
      · simp only [moves_ofSets, Player.cases, Set.mem_range, Subtype.exists,
                   exists_prop, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        intro gl h4
        have h_gl : IsShort gl := Short.of_mem_moves h_g h4
        exact Adjoint.short_adjoint h_gl

/--
Generalisaton of [Siegel, "Combinatorial Game Theory" (Theorem 6.6 on p.
270)][siegel:CombinatorialGameTheory:2013].
-/
theorem not_misereGE_of_isEnd_left_not_isEnd_left {A : GameForm → Prop} {g h : GameForm}
    (h0 : A (leftEndNotLeftEndNotGeAuxT g h)) (h1 : IsEnd .left h)
    (h2 : ¬(IsEnd .left g)) : ¬(g ≥m A h) := by
  let t := !{ Set.range fun hr : moves .right h => (hr : GameForm)°
            | { !{∅ | Set.range fun gl : moves .left g => (gl : GameForm)°} } }
  -- First consider H + T
  have h3 : MisereOutcome (h + t) ≥ Outcome.P := by
    apply misereOutcome_ge_P_of_not_winsGoingFirst_right
    rw [winsGoingFirst_iff]
    simp only [moves_add, Set.mem_union, Set.mem_image, not_or, not_and, IsEnd.add_iff,
      isEndLike_iff_isEnd]
    apply And.intro (fun h3 => by
      simp [t, Set.singleton_ne_empty, not_false_eq_true, isEnd_def])
    simp only [Player.neg_right, not_exists, not_and, not_not]
    intro x h3
    apply Or.elim h3 <;> clear h3 <;> intro ⟨hr, h3, h4⟩ <;> rw [<-h4]
    · -- If Right moves to H^R + T, then Left has a winning response to H^R +
      -- (H^R)°
      refine winsGoingFirst_left_of_move_misereOutcome_P ?_ (misereOutcome_add_adjoint_eq_P hr)
      refine add_left_mem_moves_add ?_ hr
      simp only [t, leftMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop]
      exists hr
    · -- If instead Right moves to H + { | (G^L)°}, then Left wins outright,
      -- since (by the assumption on H) both components are Left ends
      apply winsGoingFirst_add_of_isEnd h1
      simp only [t, rightMoves_ofSets, Set.mem_singleton_iff] at h3
      simp only [h3, leftMoves_ofSets, isEnd_def]
  -- Next consider G + T
  have h4 : MisereOutcome (g + t) ≤ Outcome.N := by
    apply misereOutcome_le_N_of_winsGoingFirst_right
    apply winsGoingFirst_of_moves
    -- Right has a move to G + { | (G^L)° }
    use (g + !{∅ | Set.range fun gl : moves .left g => (gl : GameForm)°})
    constructor
    · refine add_left_mem_moves_add ?_ g
      simp only [t, rightMoves_ofSets, Set.mem_singleton_iff]
    · rw [not_winsGoingFirst_iff]
      simp only [isEnd_def, isEndLike_iff_isEnd, Player.neg_right, moves_add, moves_ofSets,
                 Player.cases, Set.image_empty, Set.union_empty, Set.image_eq_empty, Set.mem_image,
                 Player.neg_left, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      rw [isEnd_def] at h2
      apply And.intro h2
      intro gl h4
      -- from which Left's only options have the form G^L + { | (G^L)° }
      apply winsGoingFirst_of_moves
      -- There must be at least one such option, by the assumption on G; and
      -- each such option has a mirror-image response by Right, to G^L + (G^L)°
      use (gl + gl°)
      simp only [Player.neg_right, moves_add, moves_ofSets, Player.cases,
                 Set.mem_union, Set.mem_image, Set.mem_range, Subtype.exists, exists_prop,
                 exists_exists_and_eq_and]
      constructor
      · apply Or.inr
        use gl
      · exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P gl)
  intro h5
  have h6 : MisereOutcome (g + t) ≥ Outcome.P :=
    Preorder.le_trans
      Outcome.P
      (MisereOutcome (h + t))
      (MisereOutcome (g + t)) h3 (h5 t h0)
  cases h7 : MisereOutcome (g + t)
  all_goals simp only [t, h7, LE.le, LT.lt, and_false, and_self, and_true, ge_iff_le,
                       ne_eq, not_false_eq_true, not_true_eq_false, or_false, or_self, or_true,
                       reduceCtorEq] at h4 h6

theorem ClosedUnderNeg.not_misereGE_of_isEnd_right_not_isEnd_right {A :
    GameForm → Prop} [ClosedUnderNeg A]
    {g h : GameForm} (h0 : A (leftEndNotLeftEndNotGeAuxT (-g) (-h)))
    (h1 : IsEnd .right h) (h2 : ¬(IsEnd .right g)) : ¬(h ≥m A g) := by
  have h3 : IsEnd .left (-h) := IsEnd.neg_iff_neg.mpr h1
  have h4 : ¬(IsEnd .left (-g)) := IsEnd.neg_iff_neg.not.mpr h2
  have h5 : ¬((-g) ≥m A (-h)) := not_misereGE_of_isEnd_left_not_isEnd_left h0 h3 h4
  exact (ClosedUnderNeg.neg_ge_neg_iff h g).not.mp h5

/-- Predicates where equivalence to zero is identical equality to zero. -/
class EqZeroIdentical (A : GameForm → Prop) extends (ClosedUnderNeg A) where
  has_T_g_zero {g : GameForm} (h1 : A g) : A (leftEndNotLeftEndNotGeAuxT g 0)

instance : EqZeroIdentical IsLong where
  has_T_g_zero _ := isLong _

instance : EqZeroIdentical IsShort where
  has_T_g_zero h_g := short_auxT h_g Short.zero

theorem EqZeroIdentical.not_misereEQ_zero_of_ne_zero {A : GameForm → Prop} [EqZeroIdentical A]
    {g : GameForm} (h0 : A g) (h1 : g ≠ 0) : ¬(g =m A 0) := by
  obtain ⟨p, h2⟩ := GameForm.ne_zero_not_end h1
  cases p
  · have h3 := not_misereGE_of_isEnd_left_not_isEnd_left (has_T_g_zero h0) isEnd_zero h2
    exact not_misereEQ_of_not_misereGE h3
  · intro h3
    have h4 : A (-g) := ClosedUnderNeg.neg_iff.mpr h0
    have h5 : A (leftEndNotLeftEndNotGeAuxT (-g) (-0)) := by
      rw [neg_zero]
      exact has_T_g_zero h4
    exact not_misereEQ_of_not_misereGE
            (ClosedUnderNeg.not_misereGE_of_isEnd_right_not_isEnd_right h5 isEnd_zero h2)
            (MisereEQ.symm h3)

/--
Generalisaton of [Siegel, "Combinatorial Game Theory" (Proposition 6.7 on p.
270)][siegel:CombinatorialGameTheory:2013].
-/
theorem EqZeroIdentical.misereEQ_zero_iff_eq_zero {A : GameForm → Prop} [EqZeroIdentical A]
    {g : GameForm} (h0 : A g) : (g =m A 0 ↔ g = 0) := by
  constructor <;> intro h2
  · by_contra h3
    exact not_misereEQ_zero_of_ne_zero h0 h3 h2
  · rw [h2]
    intro _
    exact congrFun rfl

/--
[Siegel, "Combinatorial Game Theory" (Proposition 6.7 on p.
270)][siegel:CombinatorialGameTheory:2013].
-/
theorem Short.misereEQ_zero_iff_eq_zero {g : GameForm} (h_g : IsShort g) :
    (g =m IsShort 0 ↔ g = 0) := EqZeroIdentical.misereEQ_zero_iff_eq_zero h_g

/--
Transfinite generalisaton of [Siegel, "Combinatorial Game Theory" (Proposition
6.7 on p. 270)][siegel:CombinatorialGameTheory:2013].
-/
theorem Long.misereeq_zero_iff_eq_zero {g : GameForm} :
    (g =m IsLong 0 ↔ g = 0) := EqZeroIdentical.misereEQ_zero_iff_eq_zero (isLong _)

end

end MisereGames
