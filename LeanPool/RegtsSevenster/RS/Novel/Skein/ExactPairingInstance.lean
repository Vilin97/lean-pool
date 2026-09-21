/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.BraidedInstance
import LeanPool.RegtsSevenster.RS.Novel.Skein.SnakeClasses

/-!
# The exact pairing on the strand object

`ExactPairing ⟨1⟩ ⟨1⟩` in the skein category: coevaluation and
evaluation are the strand classes, and the zig-zag laws are the
snake identities — every structural cast in the categorical
formulation lives at equal numeral arities and collapses to the
identity class.
-/

namespace RS

open CategoryTheory MonoidalCategory

variable {R : ℕ} (f : EdgeRankParameter R)

/-- Bundle maps of self-casts are the identity class. -/
theorem bmc_finCongr_refl {n : ℕ} (h : n = n) :
    bundleMapClass f (finCongr h) =
      HomSpace.ofFragment f.val (strandBundle n) := by
  rw [show finCongr h = _root_.Equiv.refl (Fin n) from
    _root_.Equiv.ext (fun x => Fin.ext rfl)]
  exact bundleMapClass_refl f n

private instance : IsEmpty (bundleMap
    (transposeEquiv 1 1)).Vertex :=
  inferInstanceAs (IsEmpty Empty)

private instance : IsEmpty (permFragment
    (_root_.Equiv.swap (0 : Fin 2) 1)).Vertex :=
  inferInstanceAs (IsEmpty Empty)

private instance : DecidableEq (bundleMap
    (transposeEquiv 1 1)).Vertex :=
  fun a _ => isEmptyElim a

private instance : DecidableEq (permFragment
    (_root_.Equiv.swap (0 : Fin 2) 1)).Vertex :=
  fun a _ => isEmptyElim a

/-- The braiding class at one strand is the permutation-fragment
braid class. -/
theorem braidClass_eq_bmc :
    braidClass f = bundleMapClass f (transposeEquiv 1 1) := by
  refine HomSpace.ofFragment_congr f ?_
  refine
    { flagEquiv := _root_.Equiv.refl _
      vertexEquiv := _root_.Equiv.refl _
      attach_comm := fun g => ?_
      pairing_comm := fun g => ?_
      circles_eq := rfl }
  · obtain ⟨i, b⟩ := g
    have hi : i = (⟨0, Nat.zero_lt_two⟩ : Fin 2) ∨
        i = (⟨1, Nat.one_lt_two⟩ : Fin 2) := by
      have h2 : i.val < 2 := i.isLt
      rcases Nat.lt_or_ge i.val 1 with h | h
      · exact Or.inl (Fin.ext (show i.val = 0 by omega))
      · exact Or.inr (Fin.ext (show i.val = 1 by omega))
    rcases hi with rfl | rfl <;> cases b <;> decide
  · obtain ⟨i, b⟩ := g
    have hi : i = (⟨0, Nat.zero_lt_two⟩ : Fin 2) ∨
        i = (⟨1, Nat.one_lt_two⟩ : Fin 2) := by
      have h2 : i.val < 2 := i.isLt
      rcases Nat.lt_or_ge i.val 1 with h | h
      · exact Or.inl (Fin.ext (show i.val = 0 by omega))
      · exact Or.inr (Fin.ext (show i.val = 1 by omega))
    rcases hi with rfl | rfl <;> cases b <;> decide

/-- **The exact pairing on the strand object.** -/
noncomputable instance strandExactPairing :
    ExactPairing (SkeinObj.mk 1 : SkeinObj f) (SkeinObj.mk 1) where
  coevaluation' := coevClass f
  evaluation' := evClass f
  coevaluation_evaluation' := by
    show HomSpace.comp f 1 3 1
        (HomSpace.tensor f 1 1 0 2 (idClass f) (coevClass f))
        (HomSpace.comp f 3 3 1
          (bundleMapClass f (finCongr _))
          (HomSpace.tensor f 2 0 1 1 (evClass f) (idClass f))) =
      HomSpace.comp f 1 1 1
        (bundleMapClass f (finCongr _))
        (bundleMapClass f (finCongr _))
    rw [bmc_finCongr_refl, bmc_finCongr_refl,
      HomSpace.comp_id_left, HomSpace.comp_id_left]
    exact snake_right f
  evaluation_coevaluation' := by
    show HomSpace.comp f 1 3 1
        (HomSpace.tensor f 0 2 1 1 (coevClass f) (idClass f))
        (HomSpace.comp f 3 3 1
          (bundleMapClass f (finCongr _))
          (HomSpace.tensor f 1 1 2 0 (idClass f) (evClass f))) =
      HomSpace.comp f 1 1 1
        (bundleMapClass f (finCongr _))
        (bundleMapClass f (finCongr _))
    rw [bmc_finCongr_refl, bmc_finCongr_refl,
      HomSpace.comp_id_left, HomSpace.comp_id_left]
    exact snake_left f

/-- **Supersymmetry of the evaluation, categorical form.** -/
theorem strand_ev_symmetry :
    (β_ (SkeinObj.mk 1 : SkeinObj f) (SkeinObj.mk 1)).hom ≫
        ε_ (SkeinObj.mk 1) (SkeinObj.mk 1) =
      ε_ (SkeinObj.mk 1) (SkeinObj.mk 1) := by
  show HomSpace.comp f 2 2 0
      (bundleMapClass f (transposeEquiv 1 1)) (evClass f) =
    evClass f
  rw [← braidClass_eq_bmc]
  exact braid_comp_evClass f

end RS
