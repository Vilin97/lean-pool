/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Order.Module.Archimedean
public import Mathlib.Algebra.Order.Module.HahnEmbedding
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Ordered splitting along an Archimedean class

Let `M` be an ordered vector space over an Archimedean ordered division ring `K`. A choice of
`HahnEmbedding.ArchimedeanStrata K M` complements each open Archimedean ball inside its closed
ball. This file upgrades that algebraic complement to an ordered additive equivalence: the closed
ball is the lexicographic product of the chosen stratum, as the dominant coordinate, and the open
ball, as the infinitesimal coordinate.

This is the ordered splitting in LM24, Fact 2.4.2(2). Mathlib supplies the complement and proves
that every nonzero element of a stratum has the corresponding Archimedean class. The strict-order
argument here records the convention that Mathlib orders Archimedean classes oppositely to LM24:
a larger Mathlib class consists of smaller elements.
-/

public section

namespace HahnEmbedding.ArchimedeanStrata

open FiniteArchimedeanClass

variable {K M : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable [Module K M] [IsOrderedModule K M]

private theorem abs_lt_abs_of_mk_lt_mk {s b : M}
    (h : ArchimedeanClass.mk s < ArchimedeanClass.mk b) : |b| < |s| := by
  simpa using ArchimedeanClass.mk_lt_mk.mp h 1

private theorem pos_add_of_abs_lt_abs {s b : M} (hs : 0 < s) (h : |b| < |s|) :
    0 < s + b := by
  rw [abs_of_pos hs] at h
  have hsb : -b < s := lt_of_le_of_lt (neg_le_abs b) h
  have := add_lt_add_right hsb b
  rwa [add_neg_cancel, add_comm] at this

variable (u : HahnEmbedding.ArchimedeanStrata K M) (c : FiniteArchimedeanClass M)

private theorem stratum_le_closedBall : u.stratum c ≤ closedBall K c := by
  rw [← u.ball_sup_stratum_eq c]
  exact le_sup_right

private theorem ball_le_closedBall : ball K c ≤ closedBall K c :=
  (FiniteArchimedeanClass.ball_lt_closedBall (K := K)).le

private theorem abs_lt_abs_of_mem {s b : M} (hs : s ∈ u.stratum c) (hs0 : s ≠ 0)
    (hb : b ∈ ball K c) (hb0 : b ≠ 0) : |b| < |s| := by
  refine abs_lt_abs_of_mk_lt_mk ?_
  have hsc : FiniteArchimedeanClass.mk s hs0 = c :=
    Subtype.ext (u.archimedeanClassMk_of_mem_stratum hs hs0)
  have hcb : c < FiniteArchimedeanClass.mk b hb0 :=
    (FiniteArchimedeanClass.mem_ball_iff K).mp hb hb0
  rw [← hsc] at hcb
  exact (FiniteArchimedeanClass.mk_lt_mk hs0 hb0).mp hcb

private theorem pos_add_of_mem {s b : M} (hs : s ∈ u.stratum c) (hspos : 0 < s)
    (hb : b ∈ ball K c) : 0 < s + b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simpa using hspos
  · exact pos_add_of_abs_lt_abs hspos (abs_lt_abs_of_mem u c hs hspos.ne' hb hb0)

private def strataAdd : ((u.stratum c) ×ₗ (ball K c)) →+ (closedBall K c) where
  toFun p :=
    ⟨((ofLex p).1 : M) + ((ofLex p).2 : M),
      add_mem (stratum_le_closedBall u c (ofLex p).1.2)
        (ball_le_closedBall c (ofLex p).2.2)⟩
  map_zero' := by ext; simp
  map_add' p q := by
    apply Subtype.ext
    change ((ofLex p).1 : M) + (ofLex q).1 + (((ofLex p).2 : M) + (ofLex q).2) =
      (((ofLex p).1 : M) + (ofLex p).2) + (((ofLex q).1 : M) + (ofLex q).2)
    ac_rfl

private theorem strataAdd_injective : Function.Injective (strataAdd u c) := by
  intro p q hpq
  have hdiff : ((ofLex p).1 : M) - (ofLex q).1 = (ofLex q).2 - (ofLex p).2 := by
    have h := congrArg Subtype.val hpq
    dsimp [strataAdd] at h
    rw [sub_eq_sub_iff_add_eq_add]
    simpa [add_comm] using h
  have hzero : ((ofLex p).1 : M) - (ofLex q).1 = 0 := by
    apply Submodule.disjoint_def.mp (u.disjoint_ball_stratum c)
    · rw [hdiff]
      exact sub_mem (ofLex q).2.2 (ofLex p).2.2
    · exact sub_mem (ofLex p).1.2 (ofLex q).1.2
  apply ofLex.injective
  apply Prod.ext
  · apply Subtype.ext
    exact sub_eq_zero.mp hzero
  · apply Subtype.ext
    have h := congrArg Subtype.val hpq
    dsimp [strataAdd] at h
    rw [sub_eq_zero.mp hzero] at h
    exact add_left_cancel h

private theorem strataAdd_surjective : Function.Surjective (strataAdd u c) := by
  intro x
  have hx : (x : M) ∈ ball K c ⊔ u.stratum c := by
    rw [u.ball_sup_stratum_eq c]
    exact x.2
  obtain ⟨b, hb, s, hs, hbs⟩ := Submodule.mem_sup.mp hx
  refine ⟨toLex (⟨s, hs⟩, ⟨b, hb⟩), ?_⟩
  apply Subtype.ext
  dsimp [strataAdd]
  simpa [add_comm] using hbs

private theorem strataAdd_strictMono : StrictMono (strataAdd u c) := by
  intro p q hpq
  rcases Prod.Lex.lt_iff.mp hpq with hs | ⟨hs, hb⟩
  · rw [← sub_pos]
    change 0 < (((ofLex q).1 : M) + (ofLex q).2) -
      (((ofLex p).1 : M) + (ofLex p).2)
    rw [show (((ofLex q).1 : M) + (ofLex q).2) -
        (((ofLex p).1 : M) + (ofLex p).2) =
        ((ofLex q).1 - (ofLex p).1 : M) + ((ofLex q).2 - (ofLex p).2) by abel]
    apply pos_add_of_mem u c
    · exact sub_mem (ofLex q).1.2 (ofLex p).1.2
    · exact sub_pos.mpr hs
    · exact sub_mem (ofLex q).2.2 (ofLex p).2.2
  · change ((ofLex p).1 : M) + (ofLex p).2 < (ofLex q).1 + (ofLex q).2
    rw [hs]
    have hb' : ((ofLex p).2 : M) < (ofLex q).2 := hb
    simpa [add_comm] using add_lt_add_left hb' ((ofLex q).1 : M)

/-- The lexicographic product of a chosen Archimedean stratum and its open ball is the
corresponding closed ball. The stratum is the dominant coordinate. -/
noncomputable def stratumLexBallEquivClosedBall :
    ((u.stratum c) ×ₗ (ball K c)) ≃+o (closedBall K c) :=
  { AddEquiv.ofBijective (strataAdd u c) ⟨strataAdd_injective u c, strataAdd_surjective u c⟩ with
    map_le_map_iff' := (strataAdd_strictMono u c).le_iff_le }

@[simp]
theorem stratumLexBallEquivClosedBall_apply (p : (u.stratum c) ×ₗ (ball K c)) :
    stratumLexBallEquivClosedBall u c p = ((ofLex p).1 : M) + (ofLex p).2 := (rfl)

/-- The closed Archimedean ball, split into its dominant stratum coordinate and infinitesimal
open-ball coordinate. -/
noncomputable def closedBallEquivStratumLexBall :
    (closedBall K c) ≃+o ((u.stratum c) ×ₗ (ball K c)) :=
  (stratumLexBallEquivClosedBall u c).symm

@[simp]
theorem stratumLexBallEquivClosedBall_closedBallEquivStratumLexBall (x : closedBall K c) :
    stratumLexBallEquivClosedBall u c (closedBallEquivStratumLexBall u c x) = x :=
  (stratumLexBallEquivClosedBall u c).apply_symm_apply x

@[simp]
theorem closedBallEquivStratumLexBall_stratumLexBallEquivClosedBall
    (p : (u.stratum c) ×ₗ (ball K c)) :
    closedBallEquivStratumLexBall u c (stratumLexBallEquivClosedBall u c p) = p :=
  (stratumLexBallEquivClosedBall u c).symm_apply_apply p

end HahnEmbedding.ArchimedeanStrata
