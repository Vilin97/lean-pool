/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Order.Cofinal
public import Mathlib.Topology.Order.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# A well-founded base of open Archimedean balls

In an ordered abelian group whose nonzero Archimedean classes have no smallest magnitude, the
open Archimedean balls form a neighborhood base at zero.  Mathlib orders Archimedean classes in
the reverse of magnitude, so the hypothesis is that `FiniteArchimedeanClass G` has no maximum.

The full class order need not be well-founded.  To obtain a well-founded nested base, fix an
arbitrary well-order of the finite classes and retain its record elements: a class belongs to
`CofinalIndex G` when it is larger in the ambient class order than every earlier class in the
well-order.  Record elements are cofinal, while their ambient order is a subrelation of the fixed
well-order.  Their open balls therefore give the required base without any countability
assumption or separately chosen cofinal chain.
-/

open Set

universe u

public noncomputable section

namespace ArchimedeanClass

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- The record finite Archimedean classes for an arbitrary fixed well-order.  Their inherited
Archimedean-class order is well-founded and their values are cofinal among finite classes. -/
def CofinalIndex (G : Type u) [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] :=
  {c : FiniteArchimedeanClass G // ∀ d, WellOrderingRel d c → d < c}

namespace CofinalIndex

noncomputable instance : LinearOrder (CofinalIndex G) := inferInstanceAs (LinearOrder
  {c : FiniteArchimedeanClass G // ∀ d, WellOrderingRel d c → d < c})

/-- The finite Archimedean class represented by an index in the cofinal family. -/
def archimedeanClass (i : CofinalIndex G) : FiniteArchimedeanClass G := i.1

/-- A representative of the Archimedean class indexed by `i`. -/
def representative (i : CofinalIndex G) : G :=
  ArchimedeanClass.out (archimedeanClass i).1

/-- The representative of a cofinal index is nonzero. -/
theorem representative_ne_zero (i : CofinalIndex G) : representative i ≠ 0 := by
  change ArchimedeanClass.out (archimedeanClass i).1 ≠ 0
  intro h
  have hout := ArchimedeanClass.mk_out (archimedeanClass i).1
  rw [h, ArchimedeanClass.mk_eq_top_iff.mpr rfl] at hout
  exact (archimedeanClass i).2 hout.symm

/-- The class of the chosen representative is the indexed Archimedean class. -/
theorem mk_representative (i : CofinalIndex G) :
    ArchimedeanClass.mk (representative i) = (archimedeanClass i).1 :=
  ArchimedeanClass.mk_out (archimedeanClass i).1

/-- The map from the cofinal index set to finite Archimedean classes is strictly monotone. -/
theorem archimedeanClass_lt_of_lt {i j : CofinalIndex G} (hij : i < j) :
    archimedeanClass i < archimedeanClass j :=
  hij

/-- The index order is the order induced from finite Archimedean classes. -/
theorem lt_iff_archimedeanClass_lt {i j : CofinalIndex G} :
    i < j ↔ archimedeanClass i < archimedeanClass j :=
  Iff.rfl

/-- Increasing cofinal indices give increasing underlying Archimedean classes. -/
theorem underlyingClass_lt_of_lt {i j : CofinalIndex G} (hij : i < j) :
    (archimedeanClass i).1 < (archimedeanClass j).1 :=
  hij

private theorem wellOrderingRel_of_lt {a b : CofinalIndex G} (hab : a < b) :
    WellOrderingRel a.1 b.1 := by
  rcases trichotomous_of WellOrderingRel a.1 b.1 with h | h | h
  · exact h
  · exact False.elim (hab.ne (Subtype.ext h))
  · exact False.elim ((a.property b.1 h).asymm hab)

noncomputable instance : WellFoundedLT (CofinalIndex G) :=
  (InvImage.wf (fun c : CofinalIndex G ↦ c.1) WellOrderingRel.isWellOrder.wf).mono
    (fun _ _ h ↦ wellOrderingRel_of_lt h)

/-- The indexed Archimedean classes are cofinal in the finite class order. -/
theorem isCofinal_range_archimedeanClass : IsCofinal
    (Set.range (archimedeanClass (G := G))) := by
  change IsCofinal (Set.range (fun c :
    {c : FiniteArchimedeanClass G // ∀ d, WellOrderingRel d c → d < c} => c.1))
  simpa using
    (isCofinal_setOfPred_imp_lt
      (WellOrderingRel : FiniteArchimedeanClass G → FiniteArchimedeanClass G → Prop))

end CofinalIndex

/-- Every open Archimedean ball is order-convex. -/
theorem ballAddSubgroup_ordConnected (c : ArchimedeanClass G) :
    ((ballAddSubgroup c : AddSubgroup G) : Set G).OrdConnected := by
  by_cases hc : c = ⊤
  · rw [hc, ballAddSubgroup_top]
    exact ordConnected_singleton
  constructor
  intro a ha b hb x hx
  apply (mem_ballAddSubgroup_iff hc).mpr
  have ha' := (mem_ballAddSubgroup_iff hc).mp ha
  have hb' := (mem_ballAddSubgroup_iff hc).mp hb
  exact (lt_min ha' hb').trans_le (min_le_mk_of_le_of_le hx.1 hx.2)

variable [TopologicalSpace G] [OrderTopology G] [IsTopologicalAddGroup G]

/-- An Archimedean ball is open when there is a strictly smaller nonzero magnitude. -/
theorem ballAddSubgroup_isOpen_of_exists_gt
    {c : ArchimedeanClass G} (hc : ∃ d ≠ ⊤, c < d) :
    IsOpen ((ballAddSubgroup c : AddSubgroup G) : Set G) := by
  obtain ⟨d, hdtop, hcd⟩ := hc
  induction d using ArchimedeanClass.ind with
  | mk a =>
    have ha0 : a ≠ 0 := mk_eq_top_iff.not.mp hdtop
    have habs : 0 < |a| := abs_pos.mpr ha0
    apply AddSubgroup.isOpen_of_mem_nhds
    apply Filter.mem_of_superset (Ioo_mem_nhds (neg_lt_zero.mpr habs) habs)
    intro x hx
    apply (mem_ballAddSubgroup_iff hcd.ne_top).mpr
    exact hcd.trans_le ((mk_le_mk).mpr ⟨1, by simpa using (abs_lt.mpr hx).le⟩)

/-- The canonical open Archimedean ball at a record class. -/
def cofinalBallBase (i : CofinalIndex G) : AddSubgroup G :=
  ballAddSubgroup (CofinalIndex.archimedeanClass i).1

omit [TopologicalSpace G] [OrderTopology G] [IsTopologicalAddGroup G] in
/-- Membership in a canonical Archimedean ball. -/
theorem mem_cofinalBallBase_iff (i : CofinalIndex G) (x : G) :
    x ∈ cofinalBallBase i ↔
      (CofinalIndex.archimedeanClass i).1 < ArchimedeanClass.mk x :=
  mem_ballAddSubgroup_iff (CofinalIndex.archimedeanClass i).2

omit [TopologicalSpace G] [OrderTopology G] [IsTopologicalAddGroup G] in
/-- The canonical Archimedean balls decrease along their index order. -/
theorem cofinalBallBase_antitone : Antitone (cofinalBallBase (G := G)) := by
  intro i j hij
  exact ballAddSubgroup_antitone (show i.1.1 ≤ j.1.1 from hij)

/-- If finite Archimedean classes have no maximum, every canonical ball is open. -/
theorem cofinalBallBase_isOpen [NoMaxOrder (FiniteArchimedeanClass G)] (i : CofinalIndex G) :
    IsOpen ((cofinalBallBase i : AddSubgroup G) : Set G) := by
  obtain ⟨d, hid⟩ := exists_gt (CofinalIndex.archimedeanClass i)
  exact ballAddSubgroup_isOpen_of_exists_gt ⟨d.1, d.2, hid⟩

omit [TopologicalSpace G] [OrderTopology G] [IsTopologicalAddGroup G] in
/-- Every canonical Archimedean ball is order-convex. -/
theorem cofinalBallBase_ordConnected (i : CofinalIndex G) :
    ((cofinalBallBase i : AddSubgroup G) : Set G).OrdConnected :=
  ballAddSubgroup_ordConnected (CofinalIndex.archimedeanClass i).1

omit [TopologicalSpace G] [OrderTopology G] [IsTopologicalAddGroup G] in
/-- The canonical Archimedean balls are coinitial among symmetric neighborhoods of zero. -/
theorem exists_cofinalBallBase_subset_Ioo (ε : G) (hε : 0 < ε) :
    ∃ i : CofinalIndex G, ((cofinalBallBase i : AddSubgroup G) : Set G) ⊆ Ioo (-ε) ε := by
  obtain ⟨d, ⟨i, rfl⟩, hi⟩ :=
    CofinalIndex.isCofinal_range_archimedeanClass (G := G)
      ⟨ArchimedeanClass.mk ε, ArchimedeanClass.mk_eq_top_iff.not.mpr hε.ne'⟩
  refine ⟨i, fun x hx ↦ ?_⟩
  have hix : (CofinalIndex.archimedeanClass i).1 < mk x :=
    (mem_cofinalBallBase_iff i x).mp hx
  have hi' : mk ε ≤ (CofinalIndex.archimedeanClass i).1 := hi
  have hxabs : |x| < ε := by
    simpa [abs_of_pos hε] using (mk_lt_mk.mp (hi'.trans_lt hix) 1)
  exact abs_lt.mp hxabs

/-- Open Archimedean balls admit a well-founded decreasing neighbourhood basis when the nonzero
Archimedean classes have no smallest magnitude. -/
@[blueprint "lem:well-founded-archimedean-ball-basis"
  (phase := "Algebraic independence in graded rings")
  (title := "Well-founded Archimedean-ball bases")
  (statement := /--
    Let $G$ be an ordered topological abelian group.  Suppose that the nonzero
    Archimedean classes of $G$ have no least element in the magnitude order.
    Then there are a well-founded linear order $I$ and a decreasing family
    $(U_i)_{i\in I}$ of open order-convex additive subgroups of $G$ such that
    every symmetric open interval about $0$ contains some $U_i$.
  -/)
  (proof := /--
    Well-order the finite Archimedean classes arbitrarily and retain each
    class that is larger in the Archimedean-class order than every earlier
    class.  These record classes are cofinal, while their inherited order is
    a subrelation of the chosen well-order and is therefore well-founded.
    Associate to each record class its Archimedean ball.  The balls decrease
    with the record classes and are order-convex.  The absence of a least
    nonzero magnitude makes every ball open, and cofinality of the record
    classes puts one inside every symmetric interval about $0$.
  -/)]
theorem exists_wellFounded_archimedeanBall_basis
    [NoMaxOrder (FiniteArchimedeanClass G)] :
    ∃ (ι : Type u) (_ : LinearOrder ι) (_ : WellFoundedLT ι)
      (U : ι → AddSubgroup G),
      Antitone U ∧
      (∀ i, IsOpen ((U i : AddSubgroup G) : Set G)) ∧
      (∀ i, ((U i : AddSubgroup G) : Set G).OrdConnected) ∧
      ∀ ε : G, 0 < ε → ∃ i, ((U i : AddSubgroup G) : Set G) ⊆ Ioo (-ε) ε := by
  exact ⟨CofinalIndex G, inferInstance, inferInstance, cofinalBallBase,
    cofinalBallBase_antitone, cofinalBallBase_isOpen, cofinalBallBase_ordConnected,
    exists_cofinalBallBase_subset_Ioo⟩

end ArchimedeanClass

end
