/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Graded
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueValuation
public import Mathlib.Topology.Instances.Real.Lemmas

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Additive
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.ClosedPWO
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval

/-!
# A topological formula for Berarducci's ordinal value

For a nonpositive real generalised power series, Berarducci's ordinal value is `omega` raised to
the Cantor–Bendixson rank of exponent zero in the closed support. A sufficiently short negative
support tail has order type equal to the ordinal value, and its strict supremum zero has the
corresponding point rank. The zero and one values are the bounded and constant germs.
-/

open Set
open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

private theorem cantorBendixsonValue_eq_zero_of_mem_negativeMonomialIdeal
    {b : Series K} (hb : b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    (b : K⟦ℝ⟧).cantorBendixsonValue = 0 := by
  rw [(b : K⟦ℝ⟧).cantorBendixsonValue_eq_zero_iff_support_bounded_lt
    (HahnSeries.Nonpositive.support_subset b)]
  have hsup :=
    HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero.mp hb
  by_cases hb0 : b = 0
  · subst b
    exact ⟨-1, by norm_num, by simp⟩
  · rw [HahnSeries.Nonpositive.supportSup_of_ne hb0] at hsup
    refine ⟨sSup (b : K⟦ℝ⟧).support, WithBot.coe_lt_coe.mp hsup, fun x hx ↦ ?_⟩
    exact le_csSup (HahnSeries.Nonpositive.bddAbove_support b) hx

private theorem cantorBendixsonValue_eq_one_of_ordinalValue_eq_one
    {b : Series K} (hb : ordinalValue b = 1) :
    (b : K⟦ℝ⟧).cantorBendixsonValue = 1 := by
  rw [HahnSeries.cantorBendixsonValue_eq_one_iff]
  obtain ⟨hbNear, hbJ⟩ := ordinalValue_eq_one_iff.mp hb
  have hcoeff : HahnSeries.Nonpositive.constantCoeff b ≠ 0 := by
    intro hzero
    apply hbJ
    have h := mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hbNear
    simpa [hzero] using h
  refine ⟨by simpa [HahnSeries.Nonpositive.constantCoeff_apply] using hcoeff, ?_⟩
  have hJ := mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hbNear
  have hcb := cantorBendixsonValue_eq_zero_of_mem_negativeMonomialIdeal hJ
  have heq :
      ((b - HahnSeries.Nonpositive.C (HahnSeries.Nonpositive.constantCoeff b) : Series K) :
          K⟦ℝ⟧) = (b : K⟦ℝ⟧) - HahnSeries.single 0 ((b : K⟦ℝ⟧).coeff 0) := by
    ext x
    simp [HahnSeries.Nonpositive.coe_C, HahnSeries.Nonpositive.constantCoeff_apply]
  rwa [heq] at hcb

/-- Berarducci's ordinal value is zero off the closed support at zero and otherwise equals
`omega` raised to the Cantor–Bendixson rank there. -/
@[blueprint "lem:ordinal-value-cantor-bendixson"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Cantor--Bendixson formula for the ordinal value")
  (statement := /--
    Let $b\in K((\mathbb R^{\le 0}))$.  If zero does not belong to the closed
    support of $b$, then $v_J(b)=0$; otherwise
    \[
      v_J(b)=
        \omega^{\operatorname{rk}_{\mathrm{CB},\mathrm{cl}(\operatorname{supp}(b))}(0)}.
    \]
  -/)
  (proof := /--
  By \ref{def:cantor-bendixson-value}, the right-hand side is zero off the
  closed support at $0$ and otherwise records its Cantor--Bendixson rank.
  For $v_J(b)=0$ or $1$ the assertion is the definition of $J$ and of the
  congruence class modulo $J+K$. If $v_J(b)=\omega^\alpha>1$, then
  \ref{fact:ordinal-value-support-tail} gives $\eta<0$ for which
  $\operatorname{supp}(b)\cap(\eta,0)$ has order type $\omega^\alpha$. Zero
  is its strict supremum, so
  \ref{lem:cantor-bendixson-rank-of-strict-supremum} gives rank $\alpha$ at
  zero in the closure of this tail. The closed support of $b$ agrees with that
  closure on a neighbourhood of zero. Cantor--Bendixson rank is local with
  respect to closed sets, so it has the same value in the closed support.
  -/)]
theorem ordinalValue_eq_cantorBendixsonValue (b : Series K) :
    (ordinalValue b).val = (b : K⟦ℝ⟧).cantorBendixsonValue := by
  rcases lt_trichotomy (ordinalValue b) 1 with hzero | hone | hlarge
  · have hvalue : ordinalValue b = 0 := Order.lt_one_iff.mp hzero
    have hbJ := ordinalValue_eq_zero_iff.mp hvalue
    rw [hvalue, cantorBendixsonValue_eq_zero_of_mem_negativeMonomialIdeal hbJ]
    simp
  · rw [hone, cantorBendixsonValue_eq_one_of_ordinalValue_eq_one hone]
    simp
  · rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal b with hzero | hprincipal
    · exact absurd hzero (ne_of_gt (zero_lt_one.trans hlarge))
    obtain ⟨a, ha⟩ := Ordinal.isAdditivelyPrincipal_iff.mp hprincipal
    let α : NatOrdinal := NatOrdinal.of a
    have hvalue : ordinalValue b = ω^ α := by
      apply NatOrdinal.val.injective
      simpa only [α, NatOrdinal.val_wpow, NatOrdinal.val_of] using ha
    obtain ⟨η, hη, htype⟩ :=
      exists_negativeSupportTail_orderType_eq_ordinalValue b hlarge
    let T : Set ℝ := negativeSupportTail b η
    let hT : T.IsPWO :=
      (b : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support b η)
    have hTLUB : IsLUB T 0 :=
      isLUB_negativeSupportTail_zero_of_one_lt_ordinalValue b hlarge hη
    have hT0 : (0 : ℝ) ∉ T := fun h ↦ (mem_negativeSupportTail_iff.mp h).2.2.false
    have hα0 : α.val ≠ 0 := by
      intro hα
      have hone' : ordinalValue b = 1 := by
        rw [hvalue]
        apply NatOrdinal.val.injective
        simp [hα]
      exact hlarge.ne' hone'
    have hrankT :
        TopologicalSpace.Closeds.cantorBendixsonRank
          (⟨closure T, isClosed_closure⟩ : TopologicalSpace.Closeds ℝ)
          hT.closure 0 = α.val := by
      apply Set.IsPWO.cantorBendixsonRank_closure_eq_of_orderType_eq_opow
        hT hTLUB hT0 hα0
      simpa only [T, hT, hvalue, NatOrdinal.val_wpow] using htype
    have hlocal :
        ((b : K⟦ℝ⟧).closedSupport : Set ℝ) ∩ Set.Ioi η =
          closure T ∩ Set.Ioi η := by
      apply Set.Subset.antisymm
      · intro x hx
        refine ⟨?_, hx.2⟩
        have hx' : x ∈ closure (b : K⟦ℝ⟧).support ∩ Set.Ioi η := by
          simpa only [HahnSeries.coe_closedSupport] using hx
        have hx'' := isOpen_Ioi.closure_inter hx'
        apply closure_minimal (s := (b : K⟦ℝ⟧).support ∩ Set.Ioi η)
          (t := closure T) ?_ isClosed_closure hx''
        rintro y ⟨hy, hηy⟩
        have hy0 : y ≤ 0 := HahnSeries.Nonpositive.support_subset b hy
        rcases eq_or_lt_of_le hy0 with rfl | hyneg
        · obtain ⟨z, hz, -, -⟩ := hTLUB.exists_between hη
          exact hTLUB.mem_closure ⟨z, hz⟩
        · apply subset_closure
          exact mem_negativeSupportTail_iff.mpr ⟨hy, hηy, hyneg⟩
      · intro x hx
        refine ⟨?_, hx.2⟩
        exact (HahnSeries.mem_closedSupport _ _).mpr
          (closure_mono (negativeSupportTail_subset_support b η) hx.1)
    have hrank : (b : K⟦ℝ⟧).cantorBendixsonRank 0 = α.val := by
      rw [HahnSeries.cantorBendixsonRank_eq]
      exact ((b : K⟦ℝ⟧).closedSupport.cantorBendixsonRank_congr_on_open
        ⟨closure T, isClosed_closure⟩ (b : K⟦ℝ⟧).closedSupport_isPWO hT.closure
        isOpen_Ioi hlocal (by simpa using hη)).trans hrankT
    have hbne : b ≠ 0 := by
      intro hb0
      subst b
      simp at hlarge
    have hmem : 0 ∈ closure (b : K⟦ℝ⟧).support :=
      (isLUB_support_zero_of_ordinalValue_ne_zero (b := b)
        (ne_of_gt (zero_lt_one.trans hlarge))).mem_closure
        (HahnSeries.support_nonempty_iff.mpr fun hcoe ↦ hbne (Subtype.ext hcoe))
    rw [(b : K⟦ℝ⟧).cantorBendixsonValue_of_mem hmem, hrank, hvalue]
    simp

variable [CharZero K]

/-- The Cantor degree of Berarducci's ordinal value is the Cantor–Bendixson rank at zero. -/
@[blueprint "lem:ordinal-value-degree-is-cantor-bendixson-rank"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Cantor--Bendixson formula for $\\deg_J$")
  (statement := /--
    Let $b\in K((\mathbb R^{\le0}))$, and let $\deg_J(b)$ be the Cantor degree
    of $v_J(b)$, with value $-\infty$ when $v_J(b)=0$. Then
    \[
      \deg_J(b)=
      \begin{cases}
        -\infty, & 0\notin\mathrm{cl}(\operatorname{supp}(b)),\\
        \operatorname{rk}_{\mathrm{CB},\mathrm{cl}(\operatorname{supp}(b))}(0),
          & 0\in\mathrm{cl}(\operatorname{supp}(b)).
      \end{cases}
    \]
  -/)
  (proof := /--
  By \ref{thm:cantor-bendixson-value-multiplicative}, taking Cantor degree of
  $V_{\mathrm{CB}}$ gives the multiplicative degree on the right.  Apply
  Cantor degree to \ref{lem:ordinal-value-cantor-bendixson}. The Cantor degree
  of $0$ is $-\infty$, and the Cantor degree of $\omega^\alpha$ is $\alpha$.
  -/)]
theorem ordinalValueDegree_eq_cantorBendixsonDegree (b : Series K) :
    ordinalValueDegree b =
      HahnSeries.Nonpositive.cantorBendixsonDegreeValuation (G := ℝ) (R := K) b := by
  rw [ordinalValueDegree_eq_cantorDegree,
    HahnSeries.Nonpositive.cantorBendixsonDegreeValuation_apply,
    HahnSeries.Nonpositive.cantorBendixsonValuation_apply,
    NatOrdinal.cantorDegree_eq_ordinalCantorDegree,
    NatOrdinal.cantorDegree_eq_ordinalCantorDegree]
  exact congrArg Ordinal.cantorDegree (by
    simpa only [NatOrdinal.val_of] using ordinalValue_eq_cantorBendixsonValue b)

/-- The two max-additive degrees on nonpositive real generalised power series are equal. -/
theorem ordinalValueDegreeValuation_eq_cantorBendixsonDegreeValuation :
    ordinalValueDegreeValuation K =
      HahnSeries.Nonpositive.cantorBendixsonDegreeValuation (G := ℝ) (R := K) := by
  apply MaxAddDegree.ext
  intro b
  rw [ordinalValueDegreeValuation_apply]
  exact ordinalValueDegree_eq_cantorBendixsonDegree (K := K) b

end Berarducci
