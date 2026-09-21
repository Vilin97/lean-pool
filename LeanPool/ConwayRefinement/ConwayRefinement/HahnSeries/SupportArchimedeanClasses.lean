/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Order.WellFounded
public import Mathlib.RingTheory.HahnSeries.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.FinitePWOUnion
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Archimedean classes met by a nonpositive Hahn support

The Archimedean-class order puts elements of smaller magnitude in higher classes. Consequently,
on nonpositive exponents the class map is monotone: moving an exponent toward zero moves its class
up. The Archimedean classes met by a well-founded nonpositive support are therefore well ordered
in the ascending class order.

This orientation is the one needed by the Conway induction. Restriction to the closed class ball at
`c` keeps classes at least `c`; its complement consists of classes strictly below `c`, a proper
initial segment when the support meets `c`.
-/

universe u

open Set

namespace ArchimedeanClass

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

public section

/-- On nonpositive elements, the Archimedean-class map is monotone. -/
theorem mk_le_mk_of_le_of_nonpos {a b : G} (hab : a ≤ b) (hb : b ≤ 0) :
    ArchimedeanClass.mk a ≤ ArchimedeanClass.mk b := by
  refine ArchimedeanClass.mk_le_mk_of_abs ?_
  rw [abs_of_nonpos hb, abs_of_nonpos (hab.trans hb)]
  exact neg_le_neg hab

/-- An element outside the closed class ball at `c` has class strictly below `c`. -/
theorem mk_lt_of_not_mem_closedBallAddSubgroup {c : ArchimedeanClass G} {g : G}
    (hg : g ∉ closedBallAddSubgroup c) : ArchimedeanClass.mk g < c := by
  rw [mem_closedBallAddSubgroup_iff] at hg
  exact lt_of_not_ge hg

end

end ArchimedeanClass

namespace HahnSeries

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

public section

/-- The Archimedean classes of the nonzero exponents in a nonpositive Hahn series. Exponent zero
is excluded because the complementary factor has constant coefficient one; including its class
would prevent the induction rank from decreasing. -/
def Nonpositive.nonzeroSupportArchimedeanClasses
    {R : Type*} [Ring R] (x : Nonpositive G R) : Set (ArchimedeanClass G) :=
  ArchimedeanClass.mk '' ((x : R⟦G⟧).support \ {0})

/-- Membership among the Archimedean classes of the nonzero support. -/
theorem Nonpositive.mem_nonzeroSupportArchimedeanClasses_iff
    {R : Type*} [Ring R] {x : Nonpositive G R} {c : ArchimedeanClass G} :
    c ∈ x.nonzeroSupportArchimedeanClasses ↔
      ∃ g ∈ (x : R⟦G⟧).support, g ≠ 0 ∧ ArchimedeanClass.mk g = c := by
  rw [nonzeroSupportArchimedeanClasses]
  constructor
  · rintro ⟨g, ⟨hg, hg0⟩, hgc⟩
    exact ⟨g, hg, by simpa only [Set.mem_singleton_iff] using hg0, hgc⟩
  · rintro ⟨g, hg, hg0, hgc⟩
    exact ⟨g, ⟨hg, by simpa only [Set.mem_singleton_iff] using hg0⟩, hgc⟩

/-- The Archimedean classes met by a well-founded nonpositive set are well ordered ascending. -/
theorem exists_min_mem_image_mk_of_isWF {S : Set G} (hS : S.IsWF) (hS0 : S ⊆ Set.Iic 0)
    {T : Set (ArchimedeanClass G)} (hT : T ⊆ ArchimedeanClass.mk '' S) (hne : T.Nonempty) :
    ∃ c ∈ T, ∀ d ∈ T, c ≤ d := by
  classical
  let P : Set G := {g ∈ S | ArchimedeanClass.mk g ∈ T}
  have hPS : P ⊆ S := fun _ hg ↦ hg.1
  have hPne : P.Nonempty := by
    obtain ⟨c, hc⟩ := hne
    obtain ⟨g, hgS, hgc⟩ := hT hc
    exact ⟨g, hgS, by rw [hgc]; exact hc⟩
  have hPwf : P.IsWF := hS.subset hPS
  refine ⟨ArchimedeanClass.mk (hPwf.min hPne), (hPwf.min_mem hPne).2, fun d hd ↦ ?_⟩
  obtain ⟨g, hgS, rfl⟩ := hT hd
  exact ArchimedeanClass.mk_le_mk_of_le_of_nonpos
    (hPwf.min_le hPne ⟨hgS, hd⟩) (hS0 hgS)

/-- The Archimedean classes met by a nonpositive Hahn support are well ordered ascending. -/
theorem exists_min_mem_image_mk_support {R : Type*} [Zero R] (x : R⟦G⟧)
    (hx : x.support ⊆ Set.Iic 0) {T : Set (ArchimedeanClass G)}
    (hT : T ⊆ ArchimedeanClass.mk '' x.support) (hne : T.Nonempty) :
    ∃ c ∈ T, ∀ d ∈ T, c ≤ d :=
  exists_min_mem_image_mk_of_isWF x.isWF_support hx hT hne

/-- The classes met by a nonpositive Hahn support have well-founded strict order. -/
theorem wellFounded_supportArchimedeanClasses {R : Type*} [Zero R] (x : R⟦G⟧)
    (hx : x.support ⊆ Set.Iic 0) :
    WellFounded ((· < ·) :
      {c : ArchimedeanClass G // c ∈ ArchimedeanClass.mk '' x.support} →
        {c : ArchimedeanClass G // c ∈ ArchimedeanClass.mk '' x.support} → Prop) := by
  rw [WellFounded.wellFounded_iff_has_min]
  intro U hU
  let V : Set (ArchimedeanClass G) := Subtype.val '' U
  have hVne : V.Nonempty := by
    obtain ⟨c, hc⟩ := hU
    exact ⟨c, c, hc, rfl⟩
  have hVsub : V ⊆ ArchimedeanClass.mk '' x.support := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  obtain ⟨c, hcV, hcmin⟩ := exists_min_mem_image_mk_support x hx hVsub hVne
  obtain ⟨c', hc'U, hc'c⟩ := hcV
  refine ⟨c', hc'U, ?_⟩
  intro d hdU hdc
  exact (not_lt_of_ge (hcmin d ⟨d, hdU, rfl⟩)) (hc'c ▸ hdc)

/-- The Archimedean classes met by a nonpositive Hahn series are partially well ordered. -/
theorem Nonpositive.isPWO_supportArchimedeanClasses
    {R : Type*} [Ring R] (x : Nonpositive G R) :
    (ArchimedeanClass.mk '' (x : R⟦G⟧).support).IsPWO := by
  apply (x : R⟦G⟧).isPWO_support.image_of_monotoneOn
  intro a ha b hb hab
  exact ArchimedeanClass.mk_le_mk_of_abs (by
    rw [abs_of_nonpos (Nonpositive.support_subset x hb),
      abs_of_nonpos (Nonpositive.support_subset x ha)]
    exact neg_le_neg hab)

/-- The Archimedean classes of the nonzero support are partially well ordered. -/
theorem Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
    {R : Type*} [Ring R] (x : Nonpositive G R) :
    x.nonzeroSupportArchimedeanClasses.IsPWO := by
  apply x.isPWO_supportArchimedeanClasses.mono
  exact Set.image_mono Set.sdiff_subset

/-- If the nonzero support classes of one series lie strictly below a support class of another,
their order type is strictly smaller. -/
@[blueprint "lem:support-class-order-type-strict-decrease"
  (phase := "Refinement over Archimedean classes")
  (title := "Strict decrease of support-class order type")
  (statement := /--
    Let $x,y\in K((G^{\le0}))$.  If $c$ is a nonzero Archimedean class met by
    $\operatorname{supp}(x)$ and every nonzero class met by
    $\operatorname{supp}(y)$ is a class met by $\operatorname{supp}(x)$ and is
    strictly below $c$, then the order type of the nonzero support classes of
    $y$ is strictly
    smaller than that of $x$.
  -/)
  (proof := /--
    The classes met by either nonpositive support are partially well ordered.
    Monotonicity of order type embeds the classes of $y$ into the initial
    segment of the classes of $x$ below $c$, and a proper initial segment of a
    well-order has strictly smaller order type.
  -/)]
theorem Nonpositive.orderType_nonzeroSupportArchimedeanClasses_lt
    {R : Type*} [Ring R] (x y : Nonpositive G R)
    {c : ArchimedeanClass G} (hc : c ∈ x.nonzeroSupportArchimedeanClasses)
    (hsub : y.nonzeroSupportArchimedeanClasses ⊆
      x.nonzeroSupportArchimedeanClasses ∩ Set.Iio c) :
    y.isPWO_nonzeroSupportArchimedeanClasses.orderType <
      x.isPWO_nonzeroSupportArchimedeanClasses.orderType := by
  let hxbelow := x.isPWO_nonzeroSupportArchimedeanClasses.mono
    (s := x.nonzeroSupportArchimedeanClasses ∩ Set.Iio c) Set.inter_subset_left
  exact (y.isPWO_nonzeroSupportArchimedeanClasses.orderType_mono hxbelow hsub).trans_lt
    (x.isPWO_nonzeroSupportArchimedeanClasses.orderType_inter_Iio_lt hc)

/-- For a finite family of nonpositive Hahn series, the classes met by their supports are either
finite or split into an initial block of nonzero limit order type and a finite final block. -/
theorem Nonpositive.finite_or_exists_limit_initial_finite_final_supportArchimedeanClasses
    {R : Type*} [Ring R] {ι : Type*} [Finite ι] (x : ι → Nonpositive G R) :
    let s := ⋃ i, ArchimedeanClass.mk '' (x i : R⟦G⟧).support
    s.Finite ∨
      ∃ (s₀ s₁ : Set (ArchimedeanClass G)) (hs₀ : s₀.IsPWO) (_ : s₁.IsPWO),
        s₀ ⊆ s ∧
          s₁ ⊆ s ∧
          (∀ a ∈ s₀, ∀ b ∈ s₁, a < b) ∧
          Order.IsSuccLimit hs₀.orderType ∧
          s₁.Finite ∧
          s = s₀ ∪ s₁ := by
  dsimp only
  apply Set.IsPWO.finite_or_exists_limit_initial_finite_final
  exact Set.IsPWO.iUnion_of_finite _ fun i ↦
    Nonpositive.isPWO_supportArchimedeanClasses (x i)

end

end HahnSeries
