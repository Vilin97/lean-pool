/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.CantorBendixsonValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.ClosedPWO

/-!
# Cantor–Bendixson rank of a principal real Hahn series

For a principal series of Hahn degree `α`, the endpoint zero of its closed support has
Cantor–Bendixson rank `α`. Thus its Cantor–Bendixson value is the same `ω ^ α` that occurs in
the support-order definition of degree.
-/

open Set
open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

open HahnSeries

variable {K : Type v} [Field K]

/-- A principal real Hahn series of degree `α` has Cantor–Bendixson rank `α` at zero. -/
theorem IsPrincipal.cantorBendixsonRank_zero_eq_of_degree_eq
    {p : Nonpositive ℝ K} (hp : IsPrincipal p) {a : NatOrdinal}
    (hdegree : (p : K⟦ℝ⟧).degree = (a : WithBot NatOrdinal)) :
    (p : K⟦ℝ⟧).cantorBendixsonRank 0 = a.val := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hpconst := hp.eq_C_constantCoeff_of_degree_zero hdegree
    apply (p : K⟦ℝ⟧).cantorBendixsonRank_of_finite
    rw [hpconst, coe_C]
    exact (finite_singleton 0).subset HahnSeries.support_single_subset
  · have hapos : 0 < a := pos_iff_ne_zero.mpr ha
    have hcoeff := hp.constantCoeff_eq_zero_of_degree_pos hdegree hapos
    have hzero : 0 ∉ (p : K⟦ℝ⟧).support := by
      intro hmem
      rw [constantCoeff_apply] at hcoeff
      exact (HahnSeries.mem_support _ _).mp hmem hcoeff
    have hlub : IsLUB (p : K⟦ℝ⟧).support 0 :=
      (supportSup_eq_coe_iff.mp hp.supportSup_eq_zero).2
    have htype := hp.supportOrderType_eq_wpow_of_degree_eq hdegree
    let S : TopologicalSpace.Closeds ℝ :=
      ⟨closure (p : K⟦ℝ⟧).support, isClosed_closure⟩
    let hS : (S : Set ℝ).IsPWO := (p : K⟦ℝ⟧).isPWO_support.closure
    have hsets : ((p : K⟦ℝ⟧).closedSupport : Set ℝ) = (S : Set ℝ) :=
      (p : K⟦ℝ⟧).coe_closedSupport
    rw [cantorBendixsonRank_eq]
    calc
      (p : K⟦ℝ⟧).closedSupport.cantorBendixsonRank
          (p : K⟦ℝ⟧).closedSupport_isPWO 0 =
          S.cantorBendixsonRank hS 0 :=
        (p : K⟦ℝ⟧).closedSupport.cantorBendixsonRank_congr_on_open S
          (p : K⟦ℝ⟧).closedSupport_isPWO hS isOpen_univ
          (by simpa only [inter_univ] using hsets) (mem_univ 0)
      _ = a.val := by
        apply Set.IsPWO.cantorBendixsonRank_closure_eq_of_orderType_eq_opow
          (p : K⟦ℝ⟧).isPWO_support hlub hzero
        · exact NatOrdinal.val.injective.ne ha
        · simpa only [HahnSeries.supportOrderType_eq_setOrderType,
            NatOrdinal.val_wpow] using htype

/-- A principal real Hahn series of degree `α` has Cantor–Bendixson value `ω ^ α`. -/
theorem IsPrincipal.cantorBendixsonValue_eq_wpow_of_degree_eq
    {p : Nonpositive ℝ K} (hp : IsPrincipal p) {a : NatOrdinal}
    (hdegree : (p : K⟦ℝ⟧).degree = (a : WithBot NatOrdinal)) :
    (p : K⟦ℝ⟧).cantorBendixsonValue = (Ordinal.omega0 ^ a.val) := by
  have hmem : 0 ∈ closure (p : K⟦ℝ⟧).support := by
    have hlub : IsLUB (p : K⟦ℝ⟧).support 0 :=
      (supportSup_eq_coe_iff.mp hp.supportSup_eq_zero).2
    exact hlub.mem_closure (HahnSeries.support_nonempty_iff.mpr (by simpa using hp.ne_zero))
  rw [(p : K⟦ℝ⟧).cantorBendixsonValue_of_mem hmem,
    hp.cantorBendixsonRank_zero_eq_of_degree_eq hdegree]

end HahnSeries.Nonpositive
