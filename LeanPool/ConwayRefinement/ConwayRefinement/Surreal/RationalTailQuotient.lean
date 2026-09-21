/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.Module.ConvexQuotientSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.CutFilling
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.RealModule
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SupportArchimedeanClasses
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.OrderedAddGroup
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Order.Module.Rat
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Rational tail quotients of the surreals

For a family of finite Archimedean classes, its common tail is a rational subspace of the
surreals. Quotienting by that subspace gives the usual ordered tail quotient together with its
native rational-vector-space structure. At a nonempty limit family, the quotient is Cauchy
complete for its additive uniformity: the canonical representatives of the family are a small
positive coinitial family, and surreal simplicity fills every cut indexed by that family.

This presentation is used when a small closed rational subspace of the tail quotient must be
formed. Its additive subgroup is exactly the tail kernel used by the older additive presentation.
-/

open Set

universe u

public noncomputable section

namespace Surreal

/-- The quotient by the rational subspace underlying a family of Archimedean tails. -/
abbrev RationalTailQuotient (T : Set (FiniteArchimedeanClass Surreal.{u})) :=
  Surreal.{u} ⧸ FiniteArchimedeanClass.tailSubmodule ℚ T

noncomputable instance rationalTailQuotientLinearOrder
    (T : Set (FiniteArchimedeanClass Surreal.{u})) : LinearOrder (RationalTailQuotient T) :=
  ConvexQuotient.instLinearOrder (H :=
    (FiniteArchimedeanClass.tailSubmodule ℚ T).toAddSubgroup)

instance rationalTailQuotientIsOrderedAddMonoid
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    IsOrderedAddMonoid (RationalTailQuotient T) :=
  ConvexQuotient.instIsOrderedAddMonoid (H :=
    (FiniteArchimedeanClass.tailSubmodule ℚ T).toAddSubgroup)

instance rationalTailQuotientPosSMulMono
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    PosSMulMono ℚ (RationalTailQuotient T) where
  smul_le_smul_of_nonneg_left q hq x y hxy := by
    change ∃ a b : Surreal.{u}, Submodule.Quotient.mk a = x ∧
      Submodule.Quotient.mk b = y ∧ a ≤ b at hxy
    obtain ⟨a, b, ha, hb, hab⟩ := hxy
    change ∃ a b : Surreal.{u}, Submodule.Quotient.mk a = q • x ∧
      Submodule.Quotient.mk b = q • y ∧ a ≤ b
    refine ⟨q • a, q • b, ?_, ?_, smul_le_smul_of_nonneg_left hab hq⟩
    · simpa only [Submodule.Quotient.mk_smul] using congrArg (q • ·) ha
    · simpa only [Submodule.Quotient.mk_smul] using congrArg (q • ·) hb

instance rationalTailQuotientPosSMulStrictMono
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    PosSMulStrictMono ℚ (RationalTailQuotient T) :=
  PosSMulMono.toPosSMulStrictMono

/-- Absolute value commutes with projection to a rational tail quotient. -/
theorem rationalTailQuotient_abs
    (T : Set (FiniteArchimedeanClass Surreal.{u})) (x : Surreal.{u}) :
    |(Submodule.Quotient.mk x : RationalTailQuotient T)| = Submodule.Quotient.mk |x| := by
  rcases le_total 0 x with hx | hx
  · have hxq : (0 : RationalTailQuotient T) ≤ Submodule.Quotient.mk x := by
      rw [← Submodule.Quotient.mk_zero]
      exact ConvexQuotient.mk_le_mk hx
    rw [abs_of_nonneg hx, abs_of_nonneg hxq]
  · have hxq : (Submodule.Quotient.mk x : RationalTailQuotient T) ≤ 0 := by
      rw [← Submodule.Quotient.mk_zero]
      exact ConvexQuotient.mk_le_mk hx
    rw [abs_of_nonpos hx, abs_of_nonpos hxq, ← Submodule.Quotient.mk_neg]

/-- A strict comparison of quotient Archimedean classes reflects to the chosen surreal
representatives. -/
theorem archimedeanClass_mk_lt_of_rationalTailQuotient_mk_lt
    (T : Set (FiniteArchimedeanClass Surreal.{u})) {x y : Surreal.{u}}
    (h : ArchimedeanClass.mk (Submodule.Quotient.mk x : RationalTailQuotient T) <
      ArchimedeanClass.mk (Submodule.Quotient.mk y : RationalTailQuotient T)) :
    ArchimedeanClass.mk x < ArchimedeanClass.mk y := by
  rw [ArchimedeanClass.mk_lt_mk] at h ⊢
  intro n
  have hn := h n
  have hn' : (Submodule.Quotient.mk (n • |y|) : RationalTailQuotient T) <
      Submodule.Quotient.mk |x| := by
    have heq : (Submodule.Quotient.mk (n • |y|) : RationalTailQuotient T) =
        n • Submodule.Quotient.mk |y| := by
      change QuotientAddGroup.mk' _ (n • |y|) = n • QuotientAddGroup.mk' _ |y|
      exact map_nsmul (QuotientAddGroup.mk' _) n |y|
    rw [heq]
    simpa only [rationalTailQuotient_abs] using hn
  exact ConvexQuotient.lt_of_mk_lt_mk hn'

/-- Suppose a chosen quotient class is met by `S`, and every nonzero member of `W` lies outside
its quotient closed ball while retaining a class met by `S`. Then the nonzero support classes of
`W` form a strict initial segment of the support classes of `S`. -/
theorem exists_nonzeroSupportClass_bound
    (T : Set (FiniteArchimedeanClass Surreal.{u}))
    (q : FiniteArchimedeanClass (RationalTailQuotient T))
    (S W : Set Surreal.{u})
    (hqocc : q.1 ∈ ArchimedeanClass.mk ''
      (Submodule.Quotient.mk (p := FiniteArchimedeanClass.tailSubmodule ℚ T) '' S))
    (hW : ∀ g ∈ W, g ≠ 0 →
      Submodule.Quotient.mk g ∉ FiniteArchimedeanClass.closedBallAddSubgroup q)
    (hWocc : ∀ g ∈ W, g ≠ 0 → ArchimedeanClass.mk g ∈ ArchimedeanClass.mk '' S) :
    ∃ c ∈ ArchimedeanClass.mk '' (S \ {0}),
      ArchimedeanClass.mk '' (W \ {0}) ⊆
        (ArchimedeanClass.mk '' (S \ {0})) ∩ Set.Iio c := by
  obtain ⟨yq, ⟨y, hyS, rfl⟩, hyq⟩ := hqocc
  have hy0 : y ≠ 0 := by
    intro hy
    subst y
    have hqtop : q.1 = ⊤ := by
      rw [← hyq]
      exact ArchimedeanClass.mk_eq_top_iff.mpr (Submodule.Quotient.mk_zero _)
    exact q.2 hqtop
  refine ⟨ArchimedeanClass.mk y, ⟨y, ⟨hyS, by simpa using hy0⟩, rfl⟩, ?_⟩
  rintro c ⟨g, ⟨hgW, hg0⟩, rfl⟩
  rw [Set.mem_singleton_iff] at hg0
  obtain ⟨z, hzS, hzg⟩ := hWocc g hgW hg0
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    rw [ArchimedeanClass.mk_zero] at hzg
    have hgtop : ArchimedeanClass.mk g = ⊤ := hzg.symm
    exact hg0 (ArchimedeanClass.mk_eq_top_iff.mp hgtop)
  refine ⟨⟨z, ⟨hzS, by simpa using hz0⟩, hzg⟩, ?_⟩
  have hgq : ArchimedeanClass.mk (Submodule.Quotient.mk g : RationalTailQuotient T) <
      ArchimedeanClass.mk (Submodule.Quotient.mk y : RationalTailQuotient T) := by
    apply ArchimedeanClass.mk_lt_of_not_mem_closedBallAddSubgroup
    intro hmem
    apply hW g hgW hg0
    apply FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff.mpr
    intro hgq0
    change q.1 ≤ ArchimedeanClass.mk (Submodule.Quotient.mk g : RationalTailQuotient T)
    rw [← hyq]
    exact ArchimedeanClass.mem_closedBallAddSubgroup_iff.mp hmem
  exact archimedeanClass_mk_lt_of_rationalTailQuotient_mk_lt T hgq

noncomputable instance rationalTailQuotientTopologicalSpace
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    TopologicalSpace (RationalTailQuotient T) :=
  Preorder.topology (RationalTailQuotient T)

instance rationalTailQuotientOrderTopology
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    OrderTopology (RationalTailQuotient T) :=
  ⟨rfl⟩

instance rationalTailQuotientDenselyOrdered
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    DenselyOrdered (RationalTailQuotient T) := by
  constructor
  intro a b hab
  refine ⟨(2 : ℚ)⁻¹ • (a + b), ?_, ?_⟩
  · calc
      a = (2 : ℚ)⁻¹ • (a + a) := by rw [smul_add, ← add_smul]; norm_num
      _ < (2 : ℚ)⁻¹ • (a + b) :=
        smul_lt_smul_of_pos_left
          (add_lt_add_left hab a |>.trans_eq (add_comm _ _)) (by norm_num)
  · calc
      (2 : ℚ)⁻¹ • (a + b) < (2 : ℚ)⁻¹ • (b + b) :=
        smul_lt_smul_of_pos_left
          (by simpa [add_comm] using (add_lt_add_left hab b)) (by norm_num)
      _ = b := by rw [smul_add, ← add_smul]; norm_num

instance rationalTailQuotientIsTopologicalAddGroup
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    IsTopologicalAddGroup (RationalTailQuotient T) where
  toContinuousAdd := continuousAdd_of_orderTopology (RationalTailQuotient T)
  toContinuousNeg := continuousNeg_of_orderTopology (RationalTailQuotient T)

noncomputable instance rationalTailQuotientUniformSpace
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    UniformSpace (RationalTailQuotient T) :=
  IsTopologicalAddGroup.rightUniformSpace (RationalTailQuotient T)

instance rationalTailQuotientIsUniformAddGroup
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    IsUniformAddGroup (RationalTailQuotient T) :=
  isUniformAddGroup_of_addCommGroup

/-- Canonical positive scales in a rational tail quotient, indexed by a small copy of the
class family. -/
def rationalTailQuotientScale
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    (i : Shrink.{u} T) :
    RationalTailQuotient T :=
  Submodule.Quotient.mk
    (FiniteArchimedeanClass.positiveRepresentative ((equivShrink T).symm i).1)

/-- The canonical quotient scale is represented by the positive representative of its class. -/
@[simp]
theorem rationalTailQuotientScale_apply
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    (i : Shrink.{u} T) :
    rationalTailQuotientScale T i = Submodule.Quotient.mk
      (FiniteArchimedeanClass.positiveRepresentative ((equivShrink T).symm i).1) :=
  (rfl)

/-- At a limit family, every canonical tail-quotient scale is positive. -/
theorem rationalTailQuotientScale_pos
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) (i : Shrink.{u} T) :
    0 < rationalTailQuotientScale T i := by
  rw [← Submodule.Quotient.mk_zero]
  apply ConvexQuotient.mk_lt_mk_iff.mpr
  constructor
  · exact FiniteArchimedeanClass.positiveRepresentative_pos _
  · intro hmem
    have htail : FiniteArchimedeanClass.positiveRepresentative ((equivShrink T).symm i).1 ∈
        FiniteArchimedeanClass.tailKernel T := by
      rw [← FiniteArchimedeanClass.tailSubmodule_toAddSubgroup ℚ T]
      simpa using hmem
    exact FiniteArchimedeanClass.positiveRepresentative_not_mem_tailKernel hT _ htail

/-- The canonical scales are coinitial among the positive elements of the tail quotient. -/
theorem exists_rationalTailQuotientScale_le
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    {x : RationalTailQuotient T} (hx : 0 < x) :
    ∃ i : Shrink.{u} T, rationalTailQuotientScale T i ≤ x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    have hxq : (Submodule.Quotient.mk (0 : Surreal.{u}) : RationalTailQuotient T) <
        (Submodule.Quotient.mk x : RationalTailQuotient T) := by
      simpa using hx
    have hx0 : 0 < x := ConvexQuotient.lt_of_mk_lt_mk hxq
    have hxH : x ∉ FiniteArchimedeanClass.tailKernel T := by
      intro hmem
      apply (ConvexQuotient.mk_lt_mk_iff.mp hxq).2
      have : x ∈ (FiniteArchimedeanClass.tailSubmodule ℚ T).toAddSubgroup := by
        simpa only [FiniteArchimedeanClass.tailSubmodule_toAddSubgroup ℚ T] using hmem
      simpa using this
    rw [FiniteArchimedeanClass.mem_tailKernel_iff] at hxH
    push Not at hxH
    obtain ⟨c, hxc⟩ := hxH
    refine ⟨equivShrink T c, ConvexQuotient.mk_le_mk ?_⟩
    apply (ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg ?_ hx0.le).le
    rw [FiniteArchimedeanClass.mk_positiveRepresentative]
    simpa using hxc

/-- The positive representatives of a limit family give a small coinitial family in its rational
tail quotient. -/
@[blueprint "lem:surreal-common-tail-quotient-coinitial-scales"
  (phase := "Surreal numbers and omnific integers")
  (title := "A coinitial family of positive elements in surreal common-tail quotients")
  (statement := /--
    Let $T$ be a $u$-small family of nonzero Archimedean classes of
    $\mathbf{No}_u$ with no least member in the magnitude order.  Index $T$ by
    a $u$-small type $I$, and let $\varepsilon_i$ be the image in
    $\mathbf{No}_u/H_T$ of the positive representative of the class indexed
    by $i$.  Then every $\varepsilon_i$ is positive, and for every $x>0$ in
    the quotient there is $i\in I$ such that $\varepsilon_i\le x$.
  -/)
  (proof := /--
    A positive representative cannot lie in $H_T$: a later class in $T$
    excludes it from the common tail.  Conversely, lift $x>0$ to a positive
    surreal representative.  Since that representative is not in $H_T$, its
    Archimedean class lies above some member of $T$; the corresponding positive
    representative therefore maps below $x$ in the quotient.
  -/)]
theorem rationalTailQuotientScale_pos_and_coinitial
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) :
    (∀ i : Shrink.{u} T, 0 < rationalTailQuotientScale T i) ∧
      ∀ x : RationalTailQuotient T, 0 < x →
        ∃ i : Shrink.{u} T, rationalTailQuotientScale T i ≤ x :=
  ⟨rationalTailQuotientScale_pos T hT, fun _ hx ↦ exists_rationalTailQuotientScale_le T hx⟩

/-- A rational tail quotient at a nonempty limit family is Cauchy complete for its additive
uniformity. -/
@[blueprint "lem:surreal-common-tail-quotient-complete"
  (phase := "Surreal numbers and omnific integers")
  (title := "Cauchy completeness of surreal common-tail quotients")
  (statement := /--
    Let $T$ be a $u$-small nonempty family of nonzero Archimedean classes of
    $\mathbf{No}_u$ with no least member in the magnitude order.  The ordered
    rational vector space obtained by quotienting $\mathbf{No}_u$ by the
    common tail below $T$ is Cauchy complete in its additive uniformity.
  -/)
  (proof := /--
    By \ref{lem:surreal-common-tail-quotient-coinitial-scales}, a small copy
    of $T$ indexes positive scales coinitial in the quotient, and rational
    halving supplies the doubled-scale hypothesis of
    \ref{lem:complete-of-coinitial-scales-and-cut-filling}.  To fill a cut in
    the quotient, \ref{lem:cut-filling-order-reflecting-surjection} lifts its
    two small indexed families to surreal representatives.  Strict order in a
    convex quotient reflects to those representatives, so
    \ref{thm:surreal-simplicity-small-cuts} fills the lifted cut inside
    $\mathbf{No}_u$; the monotone quotient map sends the filler back between
    the original families.  The Cauchy-completeness criterion now applies.
  -/)]
theorem completeSpace_rationalTailQuotient
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T] [Nonempty T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) : CompleteSpace (RationalTailQuotient T) := by
  letI : Nonempty (Shrink.{u} T) := ⟨equivShrink T (Classical.arbitrary T)⟩
  obtain ⟨hpos, hcoinitial⟩ := rationalTailQuotientScale_pos_and_coinitial T hT
  apply completeSpace_of_coinitial_of_exists_half (rationalTailQuotientScale T)
  · exact hpos
  · exact hcoinitial
  · intro x hx
    exact ⟨(2 : ℚ)⁻¹ • x, smul_pos (by norm_num) hx, by
      rw [← add_smul]
      norm_num⟩
  · exact FillsCuts.of_surjective (Submodule.Quotient.mk_surjective _)
      (fun _ _ h ↦ ConvexQuotient.mk_le_mk h)
      (fun _ _ h ↦ ConvexQuotient.lt_of_mk_lt_mk h) Surreal.fillsCuts

end Surreal
