/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.RealModule
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.SmallDiscrete
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.Module.ConvexQuotientSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Assumptions
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Leading
public import Mathlib.Algebra.Order.Module.Rat
public import Mathlib.SetTheory.Cardinal.Regular

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# LM24 assumptions `(A1)_σ` and `(A2)_σ` for surreal Archimedean strata

Every real-linear complement of one open Archimedean ball in the corresponding closed surreal
ball is order-additively isomorphic to `ℝ`. To construct the isomorphism, choose a positive
element `a` of the stratum and send `x` to the standard part of `x / a`. Elements of the stratum
have the same Archimedean class as `a`, so the quotient is finite; disjointness from the open ball
makes the map injective, while real scalar multiples of `a` make it surjective.

This proves LM24, Proposition 2.4.3 in the exact form needed for assumption `(A1)_σ` in Theorem
9.0.1. The zero class remains a separate disjunct, following Mathlib's convention that it is `⊤`.

For `(A2)_σ`, every small family in the open ball has a strict upper bound still in the ball.
The bound is the surreal cut above the family and below every `a / n`, where `a` is a positive
representative of `σ`. Consequently the ball has cofinality at least the universe cardinal that
bounds surreal Hahn supports. This is the universe-bounded form of LM24, Proposition 2.4.4.
-/

public noncomputable section

open ArchimedeanClass FiniteArchimedeanClass

namespace Surreal

variable (u : HahnEmbedding.ArchimedeanStrata ℝ Surreal)
variable (c : FiniteArchimedeanClass Surreal)

private noncomputable def stratumNonzeroElement : u.stratum c :=
  Classical.choose (exists_ne (0 : u.stratum c))

private theorem stratumNonzeroElement_ne_zero : stratumNonzeroElement u c ≠ 0 :=
  Classical.choose_spec (exists_ne (0 : u.stratum c))

private noncomputable def stratumPositiveElement : u.stratum c :=
  |stratumNonzeroElement u c|

private theorem stratumPositiveElement_pos : 0 < stratumPositiveElement u c := by
  rw [stratumPositiveElement, abs_pos]
  exact stratumNonzeroElement_ne_zero u c

private theorem stratumPositiveElement_ne_zero : stratumPositiveElement u c ≠ 0 :=
  (stratumPositiveElement_pos u c).ne'

private theorem stratum_mk_div_positiveElement_eq_zero
    (x : u.stratum c) (hx : x ≠ 0) :
    ArchimedeanClass.mk ((x : Surreal) / stratumPositiveElement u c) = 0 := by
  rw [ArchimedeanClass.mk_div,
    u.archimedeanClassMk_of_mem_stratum x.property (by simpa using hx),
    u.archimedeanClassMk_of_mem_stratum (stratumPositiveElement u c).property
      (by simpa using stratumPositiveElement_ne_zero u c)]
  exact LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top c.property

private theorem stratum_mk_div_positiveElement_nonneg (x : u.stratum c) :
    0 ≤ ArchimedeanClass.mk ((x : Surreal) / stratumPositiveElement u c) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [stratum_mk_div_positiveElement_eq_zero u c x hx]

private noncomputable def stratumStdPartHom : u.stratum c →+ ℝ where
  toFun x := ArchimedeanClass.stdPart ((x : Surreal) / stratumPositiveElement u c)
  map_zero' := by simp
  map_add' x y := by
    change ArchimedeanClass.stdPart
      (((x : Surreal) + (y : Surreal)) / stratumPositiveElement u c) = _
    rw [add_div, ArchimedeanClass.stdPart_add
      (stratum_mk_div_positiveElement_nonneg u c x)
      (stratum_mk_div_positiveElement_nonneg u c y)]

private theorem stratumStdPartHom_pos {x : u.stratum c} (hx : 0 < x) :
    0 < stratumStdPartHom u c x := by
  have hquotient : 0 < (x : Surreal) / stratumPositiveElement u c :=
    div_pos (by exact hx) (by exact stratumPositiveElement_pos u c)
  have hnonneg : 0 ≤ stratumStdPartHom u c x :=
    ArchimedeanClass.stdPart_nonneg hquotient.le
  refine lt_of_le_of_ne hnonneg ?_
  intro heq
  have hzero : stratumStdPartHom u c x = 0 := heq.symm
  have hmkne := ArchimedeanClass.stdPart_eq_zero.mp hzero
  exact hmkne (stratum_mk_div_positiveElement_eq_zero u c x hx.ne')

private theorem stratumStdPartHom_strictMono : StrictMono (stratumStdPartHom u c) := by
  intro x y hxy
  rw [← sub_pos, ← map_sub]
  exact stratumStdPartHom_pos u c (sub_pos.mpr hxy)

private theorem stratumStdPartHom_surjective :
    Function.Surjective (stratumStdPartHom u c) := by
  intro r
  refine ⟨r • stratumPositiveElement u c, ?_⟩
  change ArchimedeanClass.stdPart
    (((r : ℝ) : Surreal) * (stratumPositiveElement u c : Surreal) /
      (stratumPositiveElement u c : Surreal)) = r
  rw [mul_div_cancel_right₀ _ (by simpa using stratumPositiveElement_ne_zero u c)]
  exact ArchimedeanClass.stdPart_map_real Real.toSurrealRingHom r

/-- A nonzero surreal Archimedean stratum is noncanonically isomorphic to `ℝ` as an ordered
additive group. This is LM24, Proposition 2.4.3. -/
@[blueprint "fact:surreal-archimedean-strata"
  (phase := "Surreal numbers and omnific integers")
  (title := "Real structure of surreal Archimedean strata")
  (statement := /--
    Every nonzero Archimedean stratum of the surreal numbers is noncanonically
    isomorphic to $(\mathbb R,+,<)$ as an ordered additive group
    \cite[Proposition~2.4.3]{LM24}.
  -/)
  (proof := /--
    Choose a positive element $a$ of the stratum and send $x$ to the standard
    part of $x/a$.  Division by $a$ makes the quotient finite; the chosen
    complement to the lower Archimedean ball makes the map injective, and the
    real multiples of $a$ make it surjective.
  -/)]
noncomputable def stratumOrderAddMonoidIsoReal : u.stratum c ≃+o ℝ :=
  { AddEquiv.ofBijective (stratumStdPartHom u c)
      ⟨(stratumStdPartHom_strictMono u c).injective,
        stratumStdPartHom_surjective u c⟩ with
    map_le_map_iff' := (stratumStdPartHom_strictMono u c).le_iff_le }

/-- Every nonzero surreal Archimedean class satisfies LM24 assumption `(A1)_σ`. -/
theorem assumptionA1AtFiniteClass : LM24.AssumptionA1AtFiniteClass u c := by
  rw [LM24.assumptionA1AtFiniteClass_iff]
  exact ⟨stratumOrderAddMonoidIsoReal u c⟩

/-- Every surreal Archimedean class, including the zero class, satisfies LM24 assumption
`(A1)_σ`. -/
theorem assumptionA1 (σ : ArchimedeanClass Surreal) : LM24.AssumptionA1 u σ := by
  rw [LM24.assumptionA1_iff]
  by_cases hσ : σ = ⊤
  · exact Or.inl hσ
  · exact Or.inr ⟨⟨σ, hσ⟩, by simp, ⟨stratumOrderAddMonoidIsoReal u ⟨σ, hσ⟩⟩⟩

/-- A fixed noncanonical family of real-linear complements to the surreal Archimedean balls. -/
noncomputable def archimedeanStrata : HahnEmbedding.ArchimedeanStrata ℝ Surreal :=
  Classical.choice inferInstance

/-- The fixed surreal strata satisfy LM24 assumption `(A1)_σ` at every class. -/
theorem archimedeanStrata_assumptionA1 (σ : ArchimedeanClass Surreal) :
    LM24.AssumptionA1 archimedeanStrata σ :=
  assumptionA1 archimedeanStrata σ

/-! ### Assumption `(A2)_σ` -/

universe u v

/-- The inaccessible universe cardinal that bounds supports of `SurrealHahnSeries.{u}`. -/
def smallSupportCardinal : Cardinal.{u + 1} :=
  Cardinal.univ.{u, u + 1}

/-- The surreal small-support cardinal is the universe cardinal. -/
theorem smallSupportCardinal_eq_univ :
    smallSupportCardinal.{u} = Cardinal.univ.{u, u + 1} :=
  (rfl)

/-- The surreal small-support cardinal is uncountable. -/
theorem aleph0_lt_smallSupportCardinal :
    Cardinal.aleph0 < smallSupportCardinal.{u} :=
  Cardinal.aleph0_lt_univ

/-- The small-support cardinal carries the uncountability instance used by bounded Hahn fields. -/
instance smallSupportCardinal_aleph0Fact :
    Fact (Cardinal.aleph0 < smallSupportCardinal.{u}) :=
  ⟨aleph0_lt_smallSupportCardinal⟩

/-- The surreal small-support cardinal is regular. -/
theorem smallSupportCardinal_isRegular :
    smallSupportCardinal.{u}.IsRegular :=
  Cardinal.IsInaccessible.univ.isRegular

/-- The small-support cardinal carries the regularity instance used by bounded splitting. -/
instance smallSupportCardinal_isRegularFact :
    Fact smallSupportCardinal.{u}.IsRegular :=
  ⟨smallSupportCardinal_isRegular⟩

private theorem ball_not_isCofinal_of_small
    {a : Surreal.{u}} (ha : 0 < a)
    (s : Set ↥(ball ℝ (FiniteArchimedeanClass.mk a ha.ne')))
    [Small.{u} s] : ¬ IsCofinal s := by
  let L : Set Surreal.{u} :=
    {0} ∪ (fun z : ↥(ball ℝ (FiniteArchimedeanClass.mk a ha.ne')) ↦ (z : Surreal)) '' s
  let R : Set Surreal.{u} := Set.range fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹) • a
  have hLR : ∀ x ∈ L, ∀ y ∈ R, x < y := by
    intro x hx y hy
    obtain rfl | ⟨z, hz, rfl⟩ := hx
    · obtain ⟨n, rfl⟩ := hy
      change 0 < ((n + 1 : ℝ)⁻¹) • a
      rw [real_smul_def]
      exact mul_pos (Real.toSurreal_pos_iff.mpr (inv_pos.mpr (by positivity))) ha
    · obtain ⟨n, rfl⟩ := hy
      change (z : Surreal) < ((n + 1 : ℝ)⁻¹) • a
      by_cases hz0 : (z : Surreal) = 0
      · rw [hz0, real_smul_def]
        exact mul_pos (Real.toSurreal_pos_iff.mpr (inv_pos.mpr (by positivity))) ha
      have hzclass :
          (FiniteArchimedeanClass.mk a ha.ne').val < ArchimedeanClass.mk (z : Surreal) :=
        (FiniteArchimedeanClass.mem_ball_iff ℝ).mp z.property hz0
      apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg
      · rw [ArchimedeanClass.mk_smul _ (inv_ne_zero (by positivity))]
        exact hzclass
      · exact smul_nonneg (inv_nonneg.mpr (by positivity)) ha.le
  let y : Surreal.{u} := !{L | R}' hLR
  have hypos : 0 < y :=
    Surreal.lt_ofSets_of_mem_left (show 0 ∈ L by simp [L])
  have hyright (n : ℕ) : y < ((n + 1 : ℝ)⁻¹) • a :=
    Surreal.ofSets_lt_of_mem_right
      (show ((n + 1 : ℝ)⁻¹) • a ∈ R by exact Set.mem_range_self n)
  have hyball : y ∈ ball ℝ (FiniteArchimedeanClass.mk a ha.ne') := by
    rw [FiniteArchimedeanClass.mem_ball_iff]
    intro hy0
    rw [FiniteArchimedeanClass.mk_lt_mk ha.ne' hy0, ArchimedeanClass.mk_lt_mk]
    intro n
    rw [abs_of_pos hypos, abs_of_pos ha]
    obtain rfl | hn := n.eq_zero_or_pos
    · simpa using ha
    · have hbound := hyright (n - 1)
      have hcast : (((n - 1 : ℕ) : ℝ) + 1) = n := by
        exact_mod_cast Nat.sub_add_cancel hn
      rw [hcast, real_smul_def] at hbound
      have hnSurreal : (0 : Surreal) < n := by exact_mod_cast hn
      have hmul := mul_lt_mul_of_pos_left hbound hnSurreal
      simpa [mul_assoc, hn.ne'] using hmul
  rw [not_isCofinal_iff]
  exact ⟨⟨y, hyball⟩, fun z hz ↦ by
    apply Surreal.lt_ofSets_of_mem_left
    exact Set.mem_union_right _ (Set.mem_image_of_mem _ hz)⟩

/-- Every nonzero surreal Archimedean ball has cofinality at least the small-support cardinal.
This is the universe-bounded form of LM24, Proposition 2.4.4. -/
@[blueprint "fact:surreal-archimedean-ball-cofinality"
  (phase := "Surreal numbers and omnific integers")
  (title := "Cofinality of surreal Archimedean balls")
  (statement := /--
    Fix a universe $u$, let $\kappa_u$ be its universe cardinal, and let $c$ be
    a nonzero Archimedean class of $\mathbf{No}_u$.  The strict Archimedean ball
    below $c$ has cofinality at least $\kappa_u$
    \cite[Proposition~2.4.4]{LM24}.
  -/)
  (proof := /--
    A cofinal subset of cardinality below $\kappa_u$ is $u$-small.  Conway's
    cut construction gives a surreal number above that subset but still below
    every positive rational multiple of a representative of $c$, contradicting
    cofinality.
  -/)]
theorem smallSupportCardinal_le_ball_cof (c : FiniteArchimedeanClass Surreal.{u}) :
    smallSupportCardinal.{u} ≤ Order.cof ↥(ball ℝ c) := by
  induction c using FiniteArchimedeanClass.ind with
  | mk a ha =>
      have hc : FiniteArchimedeanClass.mk |a| (abs_ne_zero.mpr ha) =
          FiniteArchimedeanClass.mk a ha := by
        apply Subtype.ext
        exact ArchimedeanClass.mk_abs a
      rw [← hc, Order.le_cof_iff]
      intro s hs
      by_contra hcard
      have hsSmall : Small.{u} s := by
        rw [Cardinal.small_iff_lift_mk_lt_univ]
        simpa [smallSupportCardinal] using (not_le.mp hcard)
      letI : Small.{u} s := hsSmall
      exact ball_not_isCofinal_of_small (a := |a|) (abs_pos.mpr ha) s hs

/-- The common tail of a small limit family of surreal Archimedean classes has cofinality at
least the surreal support cardinal. -/
@[blueprint "lem:surreal-common-tail-cofinality"
  (phase := "Surreal numbers and omnific integers")
  (title := "Cofinality of common surreal Archimedean tails")
  (statement := /--
    Fix a universe $u$, let $\kappa_u$ be its universe cardinal, and let $T$ be
    a $u$-small family of nonzero Archimedean classes with no least member in
    the magnitude order.  The common tail below $T$ has cofinality at least
    $\kappa_u$.
  -/)
  (proof := /--
    If a $u$-small subset were cofinal in the common tail, form a Conway cut
    above it and below the positive rational fractions of representatives of
    the classes in $T$.  The resulting surreal belongs to the common tail but
    is above the proposed cofinal subset.
  -/)]
theorem smallSupportCardinal_le_tailSubmodule_cof
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) :
    smallSupportCardinal.{u} ≤ Order.cof ↥(FiniteArchimedeanClass.tailSubmodule ℚ T) := by
  rw [Order.le_cof_iff]
  intro s hs
  by_contra hcard
  have hsSmall : Small.{u} s := by
    rw [Cardinal.small_iff_lift_mk_lt_univ]
    simpa [smallSupportCardinal] using (not_le.mp hcard)
  letI : Small.{u} s := hsSmall
  let L : Set Surreal.{u} := {0} ∪
    ((↑) : ↥(FiniteArchimedeanClass.tailSubmodule ℚ T) → Surreal.{u}) '' s
  let R : Set Surreal.{u} := Set.range fun p : T × ℕ ↦
    ((p.2 + 1 : ℝ)⁻¹) • FiniteArchimedeanClass.positiveRepresentative p.1.1
  have hLR : ∀ x ∈ L, ∀ y ∈ R, x < y := by
    intro x hx y hy
    obtain rfl | ⟨z, hz, rfl⟩ := hx
    · obtain ⟨⟨c, n⟩, rfl⟩ := hy
      dsimp only
      rw [real_smul_def]
      exact mul_pos (Real.toSurreal_pos_iff.mpr (inv_pos.mpr (by positivity)))
        (FiniteArchimedeanClass.positiveRepresentative_pos c.1)
    · obtain ⟨⟨c, n⟩, rfl⟩ := hy
      by_cases hz0 : (z : Surreal) = 0
      · rw [hz0]
        dsimp only
        rw [real_smul_def]
        exact mul_pos (Real.toSurreal_pos_iff.mpr (inv_pos.mpr (by positivity)))
          (FiniteArchimedeanClass.positiveRepresentative_pos c.1)
      obtain ⟨d, hdT, hcd⟩ := hT c.1 c.2
      have hzTail : (z : Surreal) ∈ FiniteArchimedeanClass.tailKernel T := by
        exact (FiniteArchimedeanClass.mem_tailSubmodule_iff (K := ℚ)).mp z.2
      have hdz : d.1 ≤ ArchimedeanClass.mk (z : Surreal) :=
        FiniteArchimedeanClass.mem_tailKernel_iff.mp hzTail ⟨d, hdT⟩
      have hcz : c.1.1 < ArchimedeanClass.mk (z : Surreal) :=
        (show c.1.1 < d.1 from hcd).trans_le hdz
      rcases le_total (z : Surreal) 0 with hzneg | hznonneg
      · dsimp only
        rw [real_smul_def]
        exact hzneg.trans_lt (mul_pos
          (Real.toSurreal_pos_iff.mpr (inv_pos.mpr (by positivity)))
          (FiniteArchimedeanClass.positiveRepresentative_pos c.1))
      · apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg
        · dsimp only
          rw [ArchimedeanClass.mk_smul _ (inv_ne_zero (by positivity)),
            FiniteArchimedeanClass.mk_positiveRepresentative]
          exact hcz
        · exact smul_nonneg (inv_nonneg.mpr (by positivity))
            (FiniteArchimedeanClass.positiveRepresentative_pos c.1).le
  let y : Surreal.{u} := !{L | R}' hLR
  have hypos : 0 < y := Surreal.lt_ofSets_of_mem_left (show 0 ∈ L by simp [L])
  have hyright (c : T) (n : ℕ) :
      y < ((n + 1 : ℝ)⁻¹) • FiniteArchimedeanClass.positiveRepresentative c.1 :=
    Surreal.ofSets_lt_of_mem_right
      (show ((n + 1 : ℝ)⁻¹) • FiniteArchimedeanClass.positiveRepresentative c.1 ∈ R by
        exact Set.mem_range_self (c, n))
  have hyTail : y ∈ FiniteArchimedeanClass.tailSubmodule ℚ T := by
    rw [FiniteArchimedeanClass.mem_tailSubmodule_iff,
      FiniteArchimedeanClass.mem_tailKernel_iff]
    intro c
    obtain ⟨d, hdT, hcd⟩ := hT c.1 c.2
    apply (show c.1.1 < d.1 from hcd).le.trans
    rw [← FiniteArchimedeanClass.mk_positiveRepresentative d]
    rw [ArchimedeanClass.mk_le_mk]
    refine ⟨1, ?_⟩
    rw [abs_of_pos (FiniteArchimedeanClass.positiveRepresentative_pos d), abs_of_pos hypos]
    simpa using (hyright ⟨d, hdT⟩ 0).le
  exact (not_isCofinal_iff.mpr ⟨⟨y, hyTail⟩, fun z hz ↦ by
    apply Surreal.lt_ofSets_of_mem_left
    exact Set.mem_union_right _ (Set.mem_image_of_mem _ hz)⟩) hs

/-- The bounded integer part on a surreal common tail generates its whole bounded Hahn field. -/
@[blueprint "thm:surreal-common-tail-integer-part-fraction-field"
  (phase := "Surreal numbers and omnific integers")
  (title := "Fraction fields of surreal common-tail integer parts")
  (statement := /--
    Let $T$ be a $u$-small family of nonzero Archimedean classes of
    $\mathbf{No}_u$ with no least member in the magnitude order, and let $H_T$
    be the common tail below $T$.  For every field $R$ and subring
    $Z\subseteq R$, the bounded Hahn field $R((H_T))_{\kappa_u}$ is the
    fraction field of $Z+R((H_T^{<0}))_{\kappa_u}$.
  -/)
  (proof := /--
    By \ref{lem:surreal-common-tail-cofinality},
    $\kappa_u\leq\operatorname{cof}(H_T)$. Therefore
    \ref{thm:bounded-hahn-integer-part-fraction-field} applies to $H_T$.
  -/)]
theorem fracSubring_cardSuppLTTruncationIntegerPart_tailSubmodule_eq_top
    {R : Type v} [Field R] (Z : Subring R)
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) :
    Subring.fracSubring (HahnSeries.cardSuppLTTruncationIntegerPart
      (G := FiniteArchimedeanClass.tailSubmodule ℚ T) (R := R)
      (κ := smallSupportCardinal.{u}) Z) = ⊤ :=
  HahnSeries.fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_le_cof Z
    (smallSupportCardinal_le_tailSubmodule_cof T hT)

/-- Every nonzero surreal Archimedean class satisfies LM24 assumption `(A2)_σ` at the cardinal
that bounds surreal Hahn supports. -/
theorem assumptionA2AtFiniteClass
    {R : Type v} [Field R] (Z : Subring R)
    (c : FiniteArchimedeanClass Surreal.{u}) :
    LM24.AssumptionA2AtFiniteClass (K := ℝ) smallSupportCardinal.{u} Z c := by
  rw [LM24.assumptionA2AtFiniteClass_iff]
  exact Or.inl (smallSupportCardinal_le_ball_cof c)

/-- Every surreal Archimedean class, including the zero class, satisfies LM24 assumption
`(A2)_σ` at the cardinal that bounds surreal Hahn supports. -/
theorem assumptionA2
    {R : Type v} [Field R] (Z : Subring R) (σ : ArchimedeanClass Surreal.{u}) :
    LM24.AssumptionA2 smallSupportCardinal.{u} Z σ := by
  rw [LM24.assumptionA2_iff]
  by_cases hσ : σ = ⊤
  · exact Or.inr (Or.inr hσ)
  · let c : FiniteArchimedeanClass Surreal := ⟨σ, hσ⟩
    have hball : (ball ℝ c : Set Surreal) = σ.ballAddSubgroup := by
      change ((ball ℝ c).toAddSubgroup : Set Surreal) = σ.ballAddSubgroup
      rw [FiniteArchimedeanClass.toAddSubgroup_ball]
      ext x
      rw [SetLike.mem_coe, SetLike.mem_coe,
        FiniteArchimedeanClass.mem_ballAddSubgroup_iff,
        ArchimedeanClass.mem_ballAddSubgroup_iff hσ]
      by_cases hx : x = 0
      · subst x
        constructor
        · intro _
          exact lt_top_iff_ne_top.mpr hσ
        · intro _ hzero
          exact (hzero rfl).elim
      · exact ⟨fun h ↦ h hx, fun h _ ↦ h⟩
    let e : ↥(ball ℝ c) ≃o ↥σ.ballAddSubgroup :=
      OrderIso.setCongr _ _ hball
    exact Or.inl (by
      rw [← e.cof_congr]
      exact smallSupportCardinal_le_ball_cof c)

end Surreal
