/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.LimitTailQuotient
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.CardinalGermRefinement
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.ConvexQuotientSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.FiniteGermError

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Cauchy-complete common-tail quotients

A family of finite Archimedean classes determines a common convex tail and an ordered rational
quotient. This file gives that quotient its order topology and proves refinement when the quotient
is Cauchy complete for its additive uniformity. The resulting refinement is exact after
restriction at a coinitial family of quotient Archimedean classes in the magnitude order.
-/

open Cardinal Set

universe u

public noncomputable section



namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type*}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Module ℚ G] [PosSMulMono ℚ G]
  [Field K] [CharZero K]

/-- Cauchy completeness of a common-tail quotient gives cardinal-bounded local refinement. -/
@[blueprint "thm:complete-tail-quotient-refinement"
  (phase := "Refinement over Archimedean classes")
  (title := "Exact refinement over a Cauchy-complete common-tail quotient")
  (statement := /--
    Let $T$ be a nonempty set of nonzero Archimedean classes with no least
    member in the magnitude order, and let $C$ be the quotient of the exponent
    group by the common tail below $T$.  Assume that $C$ is Cauchy complete for
    its additive uniformity and that $T$ has cardinality less than $\kappa$.
    For every equation $ab=cd$ among four $\kappa$-bounded series in
    $K((C^{\le0}))$ and every set $U$ of nonzero Archimedean classes of $C$
    coinitial in the magnitude order, there is $q\in U$ and a $\kappa$-bounded
    four-factor refinement whose four equations hold exactly after restriction
    to the closed ball of $q$.
  -/)
  (proof := /--
    Positive representatives of the classes in $T$ give a positive coinitial
    subset of $C$ of cardinality less than $\kappa$.  Apply
    \ref{thm:cardinal-bounded-germ-refinement}; each of its four equations has
    an error supported strictly below zero.  Coinitiality of $U$ in the
    magnitude order supplies a class $q$ smaller in magnitude than all four
    errors, so closed-ball restriction makes the four equations exact
    simultaneously.
  -/)]
theorem exists_closed_class_refinement_of_complete_tail_quotient
    {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
    (T : Set (FiniteArchimedeanClass G)) [Nonempty T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d)
    [CompleteSpace (FiniteArchimedeanClass.TailQuotient T)]
    (hTcard : #T < κ)
    (a b c d : Nonpositive (FiniteArchimedeanClass.TailQuotient T) K)
    (ha : (a : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ)
    (hb : (b : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ)
    (hc : (c : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ)
    (hd : (d : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ)
    (habcd : a * b = c * d)
    {U : Set (FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T))}
    (hU : IsCofinal U) :
    ∃ q ∈ U, ∃ e f g h : Nonpositive (FiniteArchimedeanClass.TailQuotient T) K,
      closedClassRestrict q a = closedClassRestrict q e * closedClassRestrict q f ∧
      closedClassRestrict q b = closedClassRestrict q g * closedClassRestrict q h ∧
      closedClassRestrict q c = closedClassRestrict q e * closedClassRestrict q g ∧
      closedClassRestrict q d = closedClassRestrict q f * closedClassRestrict q h ∧
      (e : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ ∧
      (f : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ ∧
      (g : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ ∧
      (h : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ := by
  let C := FiniteArchimedeanClass.TailQuotient T
  let scale : T → C := fun c ↦
    Submodule.Quotient.mk (FiniteArchimedeanClass.positiveRepresentative c.1)
  have hscalePos (c : T) : 0 < scale c := by
    rw [← Submodule.Quotient.mk_zero]
    apply ConvexQuotient.mk_lt_mk_iff.mpr
    refine ⟨FiniteArchimedeanClass.positiveRepresentative_pos c.1, ?_⟩
    intro hmem
    have htail : FiniteArchimedeanClass.positiveRepresentative c.1 ∈
        FiniteArchimedeanClass.tailKernel T := by
      rw [← FiniteArchimedeanClass.tailSubmodule_toAddSubgroup ℚ T]
      simpa using hmem
    exact FiniteArchimedeanClass.positiveRepresentative_not_mem_tailKernel hT c htail
  letI : Nontrivial C := by
    let c : T := Classical.arbitrary T
    exact ⟨⟨0, scale c, (hscalePos c).ne⟩⟩
  letI : NoMaxOrder (FiniteArchimedeanClass C) :=
    FiniteArchimedeanClass.quotient_noMax_of_eq_tailKernel T
      (FiniteArchimedeanClass.tailSubmodule ℚ T).toAddSubgroup
      (FiniteArchimedeanClass.tailSubmodule_toAddSubgroup ℚ T) hT
  have hEcard : #(Set.range scale) < κ := Cardinal.mk_range_le.trans_lt hTcard
  have hEcoinitial : ∀ y : C, 0 < y →
      ∃ x ∈ Set.range scale, 0 < x ∧ x ≤ y := by
    intro y hy
    obtain ⟨c, hcy⟩ :=
      FiniteArchimedeanClass.exists_tailQuotient_positiveRepresentative_le (T := T) hy
    exact ⟨scale c, Set.mem_range_self c, hscalePos c, hcy⟩
  obtain ⟨e, f, g, h, hea, heb, hec, hed, hecard, hfcard, hgcard, hhcard⟩ :=
    exists_cardinal_germ_refinement
      (Set.range scale) hEcard hEcoinitial a b c d ha hb hc hd habcd
  obtain ⟨q, hqU, hqa, hqb, hqc, hqd⟩ := exists_closedClassRestrict_fourFactor_eq
    (cantorBendixson_germ_eq_iff a (e * f) |>.mpr hea)
    (cantorBendixson_germ_eq_iff b (g * h) |>.mpr heb)
    (cantorBendixson_germ_eq_iff c (e * g) |>.mpr hec)
    (cantorBendixson_germ_eq_iff d (f * h) |>.mpr hed) hU
  refine ⟨q, hqU, e, f, g, h, ?_, ?_, ?_, ?_, hecard, hfcard, hgcard, hhcard⟩
  · rwa [closedClassRestrict_mul] at hqa
  · rwa [closedClassRestrict_mul] at hqb
  · rwa [closedClassRestrict_mul] at hqc
  · rwa [closedClassRestrict_mul] at hqd

end HahnSeries.Nonpositive

namespace HahnSeries

variable {G : Type u} {R : Type*}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Module ℚ G] [PosSMulMono ℚ G]
  [Semiring R]

/-- A quotient class met by the support bounds a strict initial segment of the original support
classes. -/
@[blueprint "lem:tail-quotient-class-bounds-support-classes"
  (phase := "Refinement over Archimedean classes")
  (title := "Support classes beyond a quotient Archimedean ball")
  (statement := /--
    Let $T$ be a family of nonzero Archimedean classes of an ordered rational
    vector space $G$, and let $q$ be a nonzero Archimedean class of the quotient
    by the common tail below $T$.  Suppose $q$ is met by the image of a set
    $S\subseteq G$.  If every nonzero element of $W\subseteq G$ maps outside
    the closed ball of $q$ and has an Archimedean class met by $S$, then there
    is a nonzero class $c$ met by $S$ such that every class met by $W$ is
    strictly below $c$ and is met by $S$.
  -/)
  (proof := /--
    Choose $y\in S$ whose image has class $q$.  For $g\in W\setminus\{0\}$,
    being outside the closed ball of $q$ says that the quotient class of $g$ is
    strictly larger in magnitude than that of $y$.  The common-tail quotient
    reflects this strict comparison to the original Archimedean-class order,
    so the class of $g$ lies strictly below the class of $y$.
  -/)]
theorem exists_nonzeroSupportClass_bound_tailQuotient
    (T : Set (FiniteArchimedeanClass G))
    (q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T))
    (S W : Set G)
    (hqocc : q.1 ∈ ArchimedeanClass.mk ''
      (Submodule.Quotient.mk (p := FiniteArchimedeanClass.tailSubmodule ℚ T) '' S))
    (hW : ∀ g ∈ W, g ≠ 0 →
      Submodule.Quotient.mk g ∉ FiniteArchimedeanClass.closedBallAddSubgroup q)
    (hWocc : ∀ g ∈ W, g ≠ 0 →
      ArchimedeanClass.mk g ∈ ArchimedeanClass.mk '' S) :
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
  rintro _ ⟨g, ⟨hgW, hg0⟩, rfl⟩
  rw [Set.mem_singleton_iff] at hg0
  obtain ⟨z, hzS, hzg⟩ := hWocc g hgW hg0
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    rw [ArchimedeanClass.mk_zero] at hzg
    exact hg0 (ArchimedeanClass.mk_eq_top_iff.mp hzg.symm)
  refine ⟨⟨z, ⟨hzS, by simpa using hz0⟩, hzg⟩, ?_⟩
  have hgq : ArchimedeanClass.mk
      (Submodule.Quotient.mk g : FiniteArchimedeanClass.TailQuotient T) <
      ArchimedeanClass.mk
        (Submodule.Quotient.mk y : FiniteArchimedeanClass.TailQuotient T) := by
    apply ArchimedeanClass.mk_lt_of_not_mem_closedBallAddSubgroup
    intro hmem
    apply hW g hgW hg0
    apply FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff.mpr
    intro hgq0
    change q.1 ≤ ArchimedeanClass.mk
      (Submodule.Quotient.mk g : FiniteArchimedeanClass.TailQuotient T)
    rw [← hyq]
    exact ArchimedeanClass.mem_closedBallAddSubgroup_iff.mp hmem
  exact FiniteArchimedeanClass.archimedeanClass_mk_lt_of_tailQuotient_mk_lt T hgq

/-- If the support meets every class of a limit block, its nonzero outer classes after tail
regrouping are cofinal in the tail quotient. -/
theorem isCofinal_supportArchimedeanClasses_convexQuotientSplit
    (T₀ T₁ : Set (ArchimedeanClass G))
    (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b)
    (x : HahnSeries G R)
    (hxclasses : ArchimedeanClass.mk '' x.support = T₀ ∪ T₁) :
    let T : Set (FiniteArchimedeanClass G) := {c | c.1 ∈ T₀}
    let P := FiniteArchimedeanClass.tailSubmodule ℚ T
    let y := convexQuotientSplitRingEquiv P x
    IsCofinal {q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T) |
      q.1 ∈ ArchimedeanClass.mk '' y.support} := by
  dsimp only
  intro q
  induction q using FiniteArchimedeanClass.ind with
  | mk z hz =>
    obtain ⟨c, hcz⟩ := FiniteArchimedeanClass.exists_tailQuotient_positiveRepresentative_le
      (T := {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) (abs_pos.mpr hz)
    obtain ⟨d, hdT₀, hcd⟩ := hT₀gt c.1 c.2
    obtain ⟨e, heT₀, hde⟩ := hT₀gt d hdT₀
    obtain ⟨f, _hfT₀, hef⟩ := hT₀gt e heT₀
    have hdOcc : d ∈ ArchimedeanClass.mk '' x.support := by
      rw [hxclasses]
      exact Or.inl hdT₀
    obtain ⟨g, hg, hgd⟩ := hdOcc
    let P := FiniteArchimedeanClass.tailSubmodule ℚ
      {c : FiniteArchimedeanClass G | c.1 ∈ T₀}
    let qp : (FiniteArchimedeanClass.TailQuotient
        {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) × P :=
      ofLex ((Submodule.quotientLexEquiv P).symm g)
    let zq : FiniteArchimedeanClass.TailQuotient
        {c : FiniteArchimedeanClass G | c.1 ∈ T₀} := qp.1
    let p : P := qp.2
    have hzqmk : Submodule.Quotient.mk g = zq := by
      have hrepr : Submodule.quotientLexEquiv P (toLex qp) = g := by
        change Submodule.quotientLexEquiv P
          ((Submodule.quotientLexEquiv P).symm g) = g
        exact (Submodule.quotientLexEquiv P).apply_symm_apply g
      rw [← hrepr, Submodule.quotientLexEquiv_apply,
        Submodule.mk_quotientProdLinearEquiv]
      rfl
    have hzq0 : zq ≠ 0 := by
      intro hzq
      have hgP : g ∈ P := by
        rw [← Submodule.Quotient.mk_eq_zero P, hzqmk, hzq]
      have heleg : e ≤ ArchimedeanClass.mk g :=
        FiniteArchimedeanClass.mem_tailKernel_iff.mp
          ((FiniteArchimedeanClass.mem_tailSubmodule_iff (K := ℚ)).mp hgP)
          ⟨⟨e, ne_top_of_lt hef⟩, heT₀⟩
      rw [hgd] at heleg
      exact (not_le_of_gt hde) heleg
    have hzqsupp : zq ∈ (convexQuotientSplitRingEquiv P x).support := by
      rw [mem_support]
      intro hzero
      have hcoeff := congrArg (fun s : R⟦P⟧ ↦ s.coeff p) hzero
      rw [convexQuotientSplitRingEquiv_coeff] at hcoeff
      have hlex : Submodule.quotientLexEquiv P (toLex (zq, p)) = g := by
        change Submodule.quotientLexEquiv P (toLex qp) = g
        exact (Submodule.quotientLexEquiv P).apply_symm_apply g
      rw [hlex] at hcoeff
      exact (mem_support _ _).mp hg hcoeff
    refine ⟨FiniteArchimedeanClass.mk zq hzq0, ?_, ?_⟩
    · exact ⟨zq, hzqsupp, rfl⟩
    · change ArchimedeanClass.mk z ≤ ArchimedeanClass.mk zq
      rw [ArchimedeanClass.mk_le_mk]
      have habs : |zq| ≤ |z| := calc
        |zq| = (Submodule.Quotient.mk |g| : FiniteArchimedeanClass.TailQuotient
            {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) := by
          rw [← hzqmk]
          exact FiniteArchimedeanClass.tailQuotient_abs
            {c : FiniteArchimedeanClass G | c.1 ∈ T₀} g
        _ ≤ (Submodule.Quotient.mk (FiniteArchimedeanClass.positiveRepresentative c.1) :
            FiniteArchimedeanClass.TailQuotient
              {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) := by
          apply ConvexQuotient.mk_le_mk
          have hcg : c.1 < ArchimedeanClass.mk g := hcd.trans_eq hgd.symm
          have hdom := ArchimedeanClass.mk_lt_mk.mp
            (FiniteArchimedeanClass.mk_positiveRepresentative c.1 ▸ hcg) 1
          simpa only [one_nsmul,
            abs_of_pos (FiniteArchimedeanClass.positiveRepresentative_pos c.1)] using hdom.le
        _ ≤ |z| := hcz
      exact ⟨1, by simpa only [one_nsmul] using habs⟩

end HahnSeries
