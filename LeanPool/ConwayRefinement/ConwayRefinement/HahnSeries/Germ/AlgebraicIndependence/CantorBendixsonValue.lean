/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonRank
public import Mathlib.RingTheory.HahnSeries.Basic
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.Topology.Order.LeftRightNhds

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Cantor–Bendixson ranks of closed Hahn supports

The closed support is taken in the exponent type's given order topology. Its point ranks use
transfinite derived sets in that same topology, without passing to an order completion.

At exponent zero the associated ordinal value is zero if zero is outside the closed support,
and is `omega` to the point rank otherwise. In particular, a finite support has value one exactly
when its zero coefficient is nonzero, and value zero otherwise. These definitions impose no
multiplicativity assertion.
-/

public noncomputable section

open Set Topology TopologicalSpace

universe u v

namespace HahnSeries

variable {Γ : Type u} {R : Type v} [LinearOrder Γ] [TopologicalSpace Γ]
  [OrderTopology Γ] [Zero R]

/-- The closure of the Hahn support in the given topology on the exponent type. -/
def closedSupport (b : HahnSeries Γ R) : Closeds Γ := ⟨closure b.support, isClosed_closure⟩

omit [OrderTopology Γ] in
@[simp]
theorem coe_closedSupport (b : HahnSeries Γ R) :
    (b.closedSupport : Set Γ) = closure b.support := (rfl)

omit [OrderTopology Γ] in
@[simp]
theorem mem_closedSupport (b : HahnSeries Γ R) (x : Γ) :
    x ∈ b.closedSupport ↔ x ∈ closure b.support := (Iff.rfl)

/-- The ambient closed support remains well ordered. -/
theorem closedSupport_isPWO (b : HahnSeries Γ R) : (b.closedSupport : Set Γ).IsPWO := by
  rw [coe_closedSupport]
  exact b.isPWO_support.closure

/-- An abbreviation for the Cantor–Bendixson point rank of the closed support, zero outside it. -/
def cantorBendixsonRank (b : HahnSeries Γ R) (x : Γ) : Ordinal.{u} :=
  b.closedSupport.cantorBendixsonRank b.closedSupport_isPWO x

theorem cantorBendixsonRank_eq (b : HahnSeries Γ R) (x : Γ) :
    b.cantorBendixsonRank x = b.closedSupport.cantorBendixsonRank b.closedSupport_isPWO x := (rfl)

/-- Derivative membership characterizes the Cantor–Bendixson rank at each exponent. -/
theorem mem_support_derivative_iff (b : HahnSeries Γ R) (x : Γ) (o : Ordinal.{u}) :
    x ∈ (b.closedSupport.cantorBendixson o : Set Γ) ↔
      x ∈ closure b.support ∧ o ≤ b.cantorBendixsonRank x := by
  rw [cantorBendixsonRank_eq, ← coe_closedSupport]
  exact b.closedSupport.mem_cantorBendixson_iff b.closedSupport_isPWO x o

variable [Zero Γ]

/-- Zero off the closed support, and `omega` to its Cantor–Bendixson rank at zero otherwise. -/
@[blueprint "def:cantor-bendixson-value"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "The Cantor--Bendixson value at exponent zero")
  (statement := /--
    Let $G$ be a linearly ordered set with zero and its order topology, let
    $R$ be a set with zero, and let $b\in R((G))$ be a generalised power
    series.  Write $C=\operatorname{cl}(\operatorname{supp}(b))$.  If
    $\operatorname{rk}_C(0)$ denotes the Cantor--Bendixson rank of $0$ in
    $C$, define
    \[
      V_{\mathrm{CB}}(b)=
      \begin{cases}
        \omega^{\operatorname{rk}_C(0)},&0\in C,\\
        0,&0\notin C.
      \end{cases}
    \]
  -/)
  (proof := /--
    The closure of a well-ordered support is again well ordered, so its
    Cantor--Bendixson point rank is defined.  The displayed alternatives are
    the two branches of the definition.
  -/)]
def cantorBendixsonValue (b : HahnSeries Γ R) : Ordinal.{u} := by
  classical
  exact if 0 ∈ b.closedSupport then Ordinal.omega0 ^ b.cantorBendixsonRank 0 else 0

/-- At a closed-support point, the value is the corresponding power of `omega`. -/
theorem cantorBendixsonValue_of_mem (b : HahnSeries Γ R) (h : 0 ∈ closure b.support) :
    b.cantorBendixsonValue = Ordinal.omega0 ^ b.cantorBendixsonRank 0 := by
  simp only [cantorBendixsonValue, mem_closedSupport, h, ite_true]

/-- A support avoiding a neighborhood of zero has value zero. -/
theorem cantorBendixsonValue_of_notMem (b : HahnSeries Γ R) (h : 0 ∉ closure b.support) :
    b.cantorBendixsonValue = 0 := by
  simp only [cantorBendixsonValue, mem_closedSupport, h, ite_false]

/-- The value vanishes exactly when zero is outside the ambient closed support. -/
theorem cantorBendixsonValue_eq_zero_iff (b : HahnSeries Γ R) :
    b.cantorBendixsonValue = 0 ↔ 0 ∉ closure b.support := by
  constructor
  · intro hv hm
    rw [b.cantorBendixsonValue_of_mem hm] at hv
    exact (Ordinal.opow_pos _ Ordinal.omega0_pos).ne' hv
  · exact b.cantorBendixsonValue_of_notMem

@[simp]
theorem cantorBendixsonValue_zero : (0 : HahnSeries Γ R).cantorBendixsonValue = 0 := by
  apply cantorBendixsonValue_of_notMem
  simp

omit [Zero Γ] in
/-- Finite Hahn supports have point rank zero everywhere. -/
theorem cantorBendixsonRank_of_finite (b : HahnSeries Γ R) (hfin : b.support.Finite) (x : Γ) :
    b.cantorBendixsonRank x = 0 := by
  rw [cantorBendixsonRank_eq]
  apply b.closedSupport.cantorBendixsonRank_of_finite b.closedSupport_isPWO
  simpa only [coe_closedSupport, hfin.isClosed.closure_eq] using hfin

/-- A finite support with nonzero ordinary coefficient has value one. -/
theorem cantorBendixsonValue_of_finite_of_coeff_ne_zero (b : HahnSeries Γ R)
    (hfin : b.support.Finite) (h : b.coeff 0 ≠ 0) : b.cantorBendixsonValue = 1 := by
  rw [b.cantorBendixsonValue_of_mem (subset_closure h), b.cantorBendixsonRank_of_finite hfin]
  exact Ordinal.opow_zero _

/-- A finite support with zero ordinary coefficient has value zero. -/
theorem cantorBendixsonValue_of_finite_of_coeff_eq_zero (b : HahnSeries Γ R)
    (hfin : b.support.Finite) (h : b.coeff 0 = 0) : b.cantorBendixsonValue = 0 := by
  apply b.cantorBendixsonValue_of_notMem
  rw [hfin.isClosed.closure_eq]
  simpa using h

/-- For nonpositive supports, value zero is equivalent to a strictly negative support bound. -/
theorem cantorBendixsonValue_eq_zero_iff_support_bounded_lt [NoMinOrder Γ]
    (b : HahnSeries Γ R) (hb : b.support ⊆ Iic 0) :
    b.cantorBendixsonValue = 0 ↔ ∃ c < (0 : Γ), b.support ⊆ Iic c := by
  rw [cantorBendixsonValue_eq_zero_iff]
  constructor
  · intro hn
    have hnh : (closure b.support)ᶜ ∈ 𝓝[≤] (0 : Γ) :=
      nhdsWithin_le_nhds (isClosed_closure.isOpen_compl.mem_nhds hn)
    obtain ⟨c, hc, hcut⟩ := mem_nhdsLE_iff_exists_Ioc_subset.mp hnh
    refine ⟨c, hc, fun x hx ↦ ?_⟩
    apply le_of_not_gt
    intro hcx
    exact hcut ⟨hcx, hb hx⟩ (subset_closure hx)
  · rintro ⟨c, hc, hbound⟩ hmem
    exact (not_le_of_gt hc) (closure_minimal hbound isClosed_Iic hmem)

/-- Equal supports give equal Cantor–Bendixson values. -/
theorem cantorBendixsonValue_congr_support {b d : HahnSeries Γ R} (h : b.support = d.support) :
    b.cantorBendixsonValue = d.cantorBendixsonValue := by
  have he : b.closedSupport = d.closedSupport := by
    apply Closeds.ext
    simp only [coe_closedSupport, h]
  have hr : b.cantorBendixsonRank 0 = d.cantorBendixsonRank 0 := by
    simp only [cantorBendixsonRank_eq, he]
  by_cases hm : 0 ∈ closure b.support
  · rw [b.cantorBendixsonValue_of_mem hm, d.cantorBendixsonValue_of_mem (h ▸ hm), hr]
  · rw [b.cantorBendixsonValue_of_notMem hm, d.cantorBendixsonValue_of_notMem (h ▸ hm)]

end HahnSeries
