/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.ConvexQuotient
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Order.Archimedean.Class

/-!
# Archimedean classes in subgroups and limit quotients

A positively coinitial subgroup of an ordered abelian group inherits the absence of a largest
finite Archimedean class from the ambient group. The ambient hypothesis is essential: positive
coinitiality alone does not create new Archimedean classes.

There is a separate construction suited to a limit family of classes. For a set `T` of finite
Archimedean classes, `FiniteArchimedeanClass.tailKernel T` is the intersection of their closed
Archimedean balls. If every member of `T` has a strictly later member, the quotient by this convex
subgroup has no largest finite Archimedean class. This is the quotient used at a limit of support
support classes.
-/

open Set

universe u

public noncomputable section

namespace AddSubgroup

variable {C : Type u} [AddCommGroup C] [LinearOrder C] [IsOrderedAddMonoid C]

/-- An additive subgroup of an ordered abelian group inherits the ordered-additive structure. -/
instance instIsOrderedAddMonoid (S : AddSubgroup C) : IsOrderedAddMonoid S where
  add_le_add_left a b h z :=
    show (a : C) + (z : C) ≤ (b : C) + (z : C) from by
      simpa [add_comm] using
        add_le_add_left (show (a : C) ≤ (b : C) from h) (z : C)

/-- A positively coinitial subgroup inherits the absence of a largest finite Archimedean class
from its ambient ordered group. -/
theorem finiteArchimedeanClass_noMax_of_pos_coinitial
    [NoMaxOrder (FiniteArchimedeanClass C)] (S : AddSubgroup C)
    (hS : ∀ y : C, 0 < y → ∃ x : S, 0 < (x : C) ∧ (x : C) ≤ y) :
    NoMaxOrder (FiniteArchimedeanClass S) := by
  constructor
  intro c
  induction c using FiniteArchimedeanClass.ind with
  | mk x hx =>
    obtain ⟨d, hxd⟩ := exists_gt
      (FiniteArchimedeanClass.mk (x : C) (Subtype.coe_ne_coe.mpr hx))
    induction d using FiniteArchimedeanClass.ind with
    | mk y hy =>
      obtain ⟨z, hzpos, hzy⟩ := hS |y| (abs_pos.mpr hy)
      have hz0 : z ≠ 0 := fun hz ↦ hzpos.ne' (Subtype.ext_iff.mp hz)
      refine ⟨FiniteArchimedeanClass.mk z hz0, ?_⟩
      let e : S →+o C :=
        { toFun := fun z ↦ (z : C)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          monotone' := fun _ _ h ↦ h }
      change ArchimedeanClass.mk (e x) < ArchimedeanClass.mk (e z)
      rw [← ArchimedeanClass.orderHom_mk e x, ← ArchimedeanClass.orderHom_mk e z]
      apply ((ArchimedeanClass.orderHom e).monotone.strictMono_of_injective
        (ArchimedeanClass.orderHom_injective Subtype.val_injective)).lt_iff_lt.mpr
      change ArchimedeanClass.mk (x : C) < ArchimedeanClass.mk (z : C)
      change ArchimedeanClass.mk (x : C) < ArchimedeanClass.mk y at hxd
      refine hxd.trans_le ?_
      apply ArchimedeanClass.mk_le_mk_of_abs
      simpa [abs_of_pos hzpos] using hzy

end AddSubgroup

namespace FiniteArchimedeanClass

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- The elements lying in the closed ball of every class in `T`. -/
def tailKernel (T : Set (FiniteArchimedeanClass G)) : AddSubgroup G :=
  ⨅ c : T, ArchimedeanClass.closedBallAddSubgroup c.1.1

/-- Membership in the tail kernel means having class at least every class in `T`. -/
theorem mem_tailKernel_iff {T : Set (FiniteArchimedeanClass G)} {x : G} :
    x ∈ tailKernel T ↔ ∀ c : T, c.1.1 ≤ ArchimedeanClass.mk x := by
  rw [tailKernel, AddSubgroup.mem_iInf]
  exact forall_congr' fun c ↦ ArchimedeanClass.mem_closedBallAddSubgroup_iff

/-- The common tail kernel of a family of Archimedean classes is convex. -/
instance tailKernel_isConvex (T : Set (FiniteArchimedeanClass G)) :
    (tailKernel T).IsConvex where
  ordConnected := by
    constructor
    intro a ha b hb x hx
    apply mem_tailKernel_iff.mpr
    intro c
    exact (le_min (mem_tailKernel_iff.mp ha c) (mem_tailKernel_iff.mp hb c)).trans
      (ArchimedeanClass.min_le_mk_of_le_of_le hx.1 hx.2)

/-- Absolute value commutes with projection to a convex tail quotient. -/
theorem quotient_abs (T : Set (FiniteArchimedeanClass G)) (x : G) :
    |(x : G ⧸ tailKernel T)| = ((|x| : G) : G ⧸ tailKernel T) := by
  rcases le_total 0 x with hx | hx
  · have hxq : (0 : G ⧸ tailKernel T) ≤ (x : G ⧸ tailKernel T) := by
      rw [← QuotientAddGroup.mk_zero]
      exact ConvexQuotient.mk_le_mk hx
    rw [abs_of_nonneg hx, abs_of_nonneg hxq]
  · have hxq : (x : G ⧸ tailKernel T) ≤ (0 : G ⧸ tailKernel T) := by
      rw [← QuotientAddGroup.mk_zero]
      exact ConvexQuotient.mk_le_mk hx
    rw [abs_of_nonpos hx, abs_of_nonpos hxq, ← QuotientAddGroup.mk_neg]

/-- A strict comparison of Archimedean classes in a common-tail quotient reflects to any chosen
representatives. -/
theorem archimedeanClass_mk_lt_of_quotient_mk_lt
    (T : Set (FiniteArchimedeanClass G)) {x y : G}
    (h : ArchimedeanClass.mk (x : G ⧸ tailKernel T) <
      ArchimedeanClass.mk (y : G ⧸ tailKernel T)) :
    ArchimedeanClass.mk x < ArchimedeanClass.mk y := by
  rw [ArchimedeanClass.mk_lt_mk] at h ⊢
  intro n
  have hn := h n
  have hn' : ((n • |y| : G) : G ⧸ tailKernel T) <
      ((|x| : G) : G ⧸ tailKernel T) := by
    simpa only [quotient_abs, QuotientAddGroup.mk_nsmul] using hn
  exact ConvexQuotient.lt_of_mk_lt_mk hn'

/-- A nonzero natural multiple of an absolute value stays in the same Archimedean class. -/
theorem mk_nsmul_abs {x : G} {n : ℕ} (hn : n ≠ 0) :
    ArchimedeanClass.mk (n • |x|) = ArchimedeanClass.mk x := by
  apply ArchimedeanClass.mk_eq_mk.mpr
  constructor
  · refine ⟨1, ?_⟩
    rw [one_nsmul, abs_nsmul, abs_abs]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simpa [succ_nsmul] using
      (le_add_of_nonneg_left (nsmul_nonneg (abs_nonneg x) k) :
        |x| ≤ k • |x| + |x|)
  · refine ⟨n, ?_⟩
    rw [abs_nsmul, abs_abs]

/-- If `T` has no least member in the magnitude order, its common tail quotient has no least
nonzero Archimedean class in the magnitude order. -/
theorem quotient_noMax_of_forall_exists_gt (T : Set (FiniteArchimedeanClass G))
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) :
    NoMaxOrder (FiniteArchimedeanClass (G ⧸ tailKernel T)) := by
  constructor
  intro c
  induction c using FiniteArchimedeanClass.ind with
  | mk x hx =>
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      have hxH : x ∉ tailKernel T := by
        simpa using (show (x : G ⧸ tailKernel T) ≠ 0 from hx)
      rw [mem_tailKernel_iff] at hxH
      push Not at hxH
      obtain ⟨d, hxd⟩ := hxH
      obtain ⟨e, heT, hde⟩ := hT d.1 d.2
      obtain ⟨f, hfT, hef⟩ := hT e heT
      let y : G := e.1.out
      have hyclass : ArchimedeanClass.mk y = e.1 := ArchimedeanClass.mk_out e.1
      have hy0 : y ≠ 0 := ArchimedeanClass.mk_eq_top_iff.not.mp
        (hyclass.trans_ne e.2)
      have hyH : y ∉ tailKernel T := by
        intro hy
        have hf_le_y : f.1 ≤ ArchimedeanClass.mk y :=
          mem_tailKernel_iff.mp hy ⟨f, hfT⟩
        rw [hyclass] at hf_le_y
        exact (not_le_of_gt hef) hf_le_y
      refine ⟨FiniteArchimedeanClass.mk (y : G ⧸ tailKernel T) (by simpa using hyH), ?_⟩
      change ArchimedeanClass.mk (x : G ⧸ tailKernel T) <
        ArchimedeanClass.mk (y : G ⧸ tailKernel T)
      rw [ArchimedeanClass.mk_lt_mk]
      intro n
      have hclass : ArchimedeanClass.mk x < ArchimedeanClass.mk y := by
        rw [hyclass]
        exact hxd.trans hde
      have hxy : n • |y| < |x| := ArchimedeanClass.mk_lt_mk.mp hclass n
      have hquot : ((n • |y| : G) : G ⧸ tailKernel T) <
          ((|x| : G) : G ⧸ tailKernel T) := by
        apply ConvexQuotient.mk_lt_mk_iff.mpr
        refine ⟨hxy, ?_⟩
        intro hmem
        have hdiff : d.1 ≤ ArchimedeanClass.mk (|x| - n • |y|) :=
          mem_tailKernel_iff.mp hmem d
        have hdiffclass : ArchimedeanClass.mk (|x| - n • |y|) =
            ArchimedeanClass.mk x := by
          by_cases hn : n = 0
          · simp [hn]
          rw [ArchimedeanClass.mk_sub_eq_mk_left]
          · exact ArchimedeanClass.mk_abs x
          · simpa only [ArchimedeanClass.mk_abs, mk_nsmul_abs hn] using hclass
        rw [hdiffclass] at hdiff
        exact (not_le_of_gt hxd) hdiff
      simpa only [quotient_abs, QuotientAddGroup.mk_nsmul] using hquot

/-- The no-largest-class theorem for a quotient by any additive subgroup whose carrier is the
tail kernel. -/
theorem quotient_noMax_of_eq_tailKernel (T : Set (FiniteArchimedeanClass G))
    (H : AddSubgroup G) [H.IsConvex] (hH : H = tailKernel T)
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) :
    NoMaxOrder (FiniteArchimedeanClass (G ⧸ H)) := by
  subst H
  exact quotient_noMax_of_forall_exists_gt T hT

/-- A canonical positive representative of a finite Archimedean class. -/
def positiveRepresentative (c : FiniteArchimedeanClass G) : G :=
  |c.1.out|

/-- The canonical representative of a finite class is positive. -/
theorem positiveRepresentative_pos (c : FiniteArchimedeanClass G) :
    0 < positiveRepresentative c := by
  rw [positiveRepresentative, abs_pos]
  intro h
  have := congrArg ArchimedeanClass.mk h
  rw [ArchimedeanClass.mk_out, ArchimedeanClass.mk_zero] at this
  exact c.2 this

/-- The canonical positive representative represents the requested class. -/
theorem mk_positiveRepresentative (c : FiniteArchimedeanClass G) :
    ArchimedeanClass.mk (positiveRepresentative c) = c.1 := by
  rw [positiveRepresentative, ArchimedeanClass.mk_abs, ArchimedeanClass.mk_out]

/-- At a limit family, each canonical representative survives the common tail quotient. -/
theorem positiveRepresentative_not_mem_tailKernel {T : Set (FiniteArchimedeanClass G)}
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) (c : T) :
    positiveRepresentative c.1 ∉ tailKernel T := by
  obtain ⟨d, hdT, hcd⟩ := hT c.1 c.2
  intro hmem
  have := mem_tailKernel_iff.mp hmem ⟨d, hdT⟩
  rw [mk_positiveRepresentative] at this
  exact (not_le_of_gt hcd) this

/-- The image of a canonical representative in its limit quotient is positive. -/
theorem quotient_positiveRepresentative_pos {T : Set (FiniteArchimedeanClass G)}
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) (c : T) :
    0 < ((positiveRepresentative c.1 : G) : G ⧸ tailKernel T) := by
  rw [← QuotientAddGroup.mk_zero]
  exact ConvexQuotient.mk_lt_mk_iff.mpr ⟨positiveRepresentative_pos c.1,
    by simpa using positiveRepresentative_not_mem_tailKernel hT c⟩

/-- The canonical representatives of a limit family are coinitial among the positive elements of
the common tail quotient. -/
theorem exists_quotient_positiveRepresentative_le {T : Set (FiniteArchimedeanClass G)}
    {x : G ⧸ tailKernel T} (hx : 0 < x) :
    ∃ c : T, ((positiveRepresentative c.1 : G) : G ⧸ tailKernel T) ≤ x := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    have hxq : ((0 : G) : G ⧸ tailKernel T) < (x : G ⧸ tailKernel T) := by
      simpa using hx
    have hx0 : 0 < x := ConvexQuotient.lt_of_mk_lt_mk hxq
    have hxH : x ∉ tailKernel T := by
      simpa using (ConvexQuotient.mk_lt_mk_iff.mp hxq).2
    rw [mem_tailKernel_iff] at hxH
    push Not at hxH
    obtain ⟨c, hxc⟩ := hxH
    refine ⟨c, ConvexQuotient.mk_le_mk ?_⟩
    apply (ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg ?_ hx0.le).le
    rwa [mk_positiveRepresentative]

end FiniteArchimedeanClass
