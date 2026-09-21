/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.CantorBendixsonValue

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Translation
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonReconstruction
public import Mathlib.Topology.Algebra.Group.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood

/-!
# Cantor–Bendixson ranks under translated truncation

A weak lower truncation preserves the closed support locally at its cutoff, since a well-ordered
support has a gap immediately to the right. Translation preserves point ranks. Consequently,
the value of the translated weak truncation at `c` reads the original point rank at `c`,
with value zero exactly when `c` is outside the original closed support.

The reconstruction statement lifts local lower bounds on exact-rank points to a lower bound
at the target point. Truncation uses `i ≤ c`, retaining the cutoff coefficient, and translation
by `-c` sends that exponent to zero. No multiplication identity is assumed.
-/

public noncomputable section

open Set Filter Topology TopologicalSpace

universe u v

namespace HahnSeries

variable {G : Type u} {R : Type v} [LinearOrder G] [TopologicalSpace G]
  [OrderTopology G]

section Zero

variable [Zero R]

/-- Weak lower truncation preserves the closed support in a neighborhood of its cutoff. -/
theorem closedSupport_truncLE_locally_eq (b : HahnSeries G R) (c : G) :
    ∃ U : Set G, IsOpen U ∧ c ∈ U ∧
      ((truncLE c b).closedSupport : Set G) ∩ U = (b.closedSupport : Set G) ∩ U := by
  obtain ⟨U, hU, hUo, hcU⟩ := mem_nhds_iff.mp (b.isPWO_support.eventually_le c)
  refine ⟨U, hUo, hcU, ?_⟩
  rw [coe_closedSupport, coe_closedSupport]
  apply hUo.closure_congr
  rw [support_truncLE]
  ext y
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hU h.2 h.1⟩, h.2⟩⟩

/-- Weak lower truncation preserves the Cantor–Bendixson rank at its cutoff. -/
theorem cantorBendixsonRank_truncLE (b : HahnSeries G R) (c : G) :
    (truncLE c b).cantorBendixsonRank c = b.cantorBendixsonRank c := by
  obtain ⟨U, hU, hc, he⟩ := b.closedSupport_truncLE_locally_eq c
  rw [cantorBendixsonRank_eq, cantorBendixsonRank_eq]
  exact (truncLE c b).closedSupport.cantorBendixsonRank_congr_on_open b.closedSupport
    (truncLE c b).closedSupport_isPWO b.closedSupport_isPWO hU he hc

/-- A strict upper truncation preserves the closed support locally at every point strictly above
its cutoff. -/
theorem closedSupport_truncGT_locally_eq_of_lt (b : HahnSeries G R) {c x : G}
    (hcx : c < x) :
    ∃ U : Set G, IsOpen U ∧ x ∈ U ∧
      ((truncGT c b).closedSupport : Set G) ∩ U = (b.closedSupport : Set G) ∩ U := by
  refine ⟨Ioi c, isOpen_Ioi, hcx, ?_⟩
  rw [coe_closedSupport, coe_closedSupport]
  apply isOpen_Ioi.closure_congr
  rw [support_truncGT]
  ext y
  simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi]
  tauto

/-- A strict upper truncation preserves Cantor–Bendixson rank strictly above its cutoff. -/
theorem cantorBendixsonRank_truncGT_of_lt (b : HahnSeries G R) {c x : G} (hcx : c < x) :
    (truncGT c b).cantorBendixsonRank x = b.cantorBendixsonRank x := by
  obtain ⟨U, hU, hx, he⟩ := b.closedSupport_truncGT_locally_eq_of_lt hcx
  rw [cantorBendixsonRank_eq, cantorBendixsonRank_eq]
  exact (truncGT c b).closedSupport.cantorBendixsonRank_congr_on_open b.closedSupport
    (truncGT c b).closedSupport_isPWO b.closedSupport_isPWO hU he hx

/-- The strict cutoff itself is outside the closed support of a strict upper truncation. -/
theorem notMem_closedSupport_truncGT (b : HahnSeries G R) (c : G) :
    c ∉ (truncGT c b).closedSupport := by
  rw [mem_closedSupport]
  intro hc
  obtain ⟨U, hU, hUopen, hcU⟩ := mem_nhds_iff.mp (b.isPWO_support.eventually_le c)
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff.mp hc U hUopen hcU
  rw [support_truncGT] at hy
  exact (not_le_of_gt hy.2) (hU hyU hy.1)

/-- The cutoff belongs to the truncated closed support exactly when it belongs to the original. -/
theorem mem_closedSupport_truncLE (b : HahnSeries G R) (c : G) :
    c ∈ (truncLE c b).closedSupport ↔ c ∈ b.closedSupport := by
  obtain ⟨U, _, hc, he⟩ := b.closedSupport_truncLE_locally_eq c
  exact ⟨fun h ↦ ((Set.ext_iff.mp he c).mp ⟨h, hc⟩).1,
    fun h ↦ ((Set.ext_iff.mp he c).mpr ⟨h, hc⟩).1⟩

/-- Local bounds at points of exact rank reconstruct a Cantor–Bendixson rank bound at the target. -/
theorem cantorBendixsonRank_reconstruction (b d : HahnSeries G R)
    {U : Set G} (hU : IsOpen U) {x : G} (hxU : x ∈ U)
    (a c r : Ordinal.{u}) (hx : x ∈ closure b.support) (hr : a + r ≤ b.cantorBendixsonRank x)
    (hlevel : ∀ y ∈ U, y ∈ closure b.support → b.cantorBendixsonRank y = a →
      y ∈ closure d.support ∧ c ≤ d.cantorBendixsonRank y) :
    x ∈ closure d.support ∧ c + r ≤ d.cantorBendixsonRank x := by
  apply (d.mem_support_derivative_iff x (c + r)).mp
  apply b.closedSupport.cantorBendixson_reconstruction d.closedSupport
    b.closedSupport_isPWO hU a c r _ ⟨(b.mem_support_derivative_iff x _).mpr ⟨hx, hr⟩, hxU⟩
  intro y hyU hys hy
  apply (d.mem_support_derivative_iff y c).mpr
  exact hlevel y hyU ((b.mem_closedSupport y).mp hys) ((b.cantorBendixsonRank_eq y).trans hy)

end Zero

section Translation

variable [AddCommGroup G] [IsOrderedAddMonoid G] [IsTopologicalAddGroup G] [AddMonoid R]

omit [TopologicalSpace G] [OrderTopology G] [IsTopologicalAddGroup G] in
/-- A translated weak lower truncation always has nonpositive support. -/
theorem support_translated_truncLE (b : HahnSeries G R) (c : G) :
    (translate (-c) (truncLE c b)).support ⊆ Iic 0 := by
  rw [support_translate]
  rintro x ⟨y, hy, rfl⟩
  rw [support_truncLE] at hy
  simpa only [mem_Iic, neg_add_cancel] using add_le_add_right hy.2 (-c)

/-- Translating the exponents and the target point together preserves Cantor–Bendixson rank. -/
theorem cantorBendixsonRank_translate (b : HahnSeries G R) (a x : G) :
    (translate a b).cantorBendixsonRank (a + x) = b.cantorBendixsonRank x := by
  rw [cantorBendixsonRank_eq, cantorBendixsonRank_eq]
  apply (Homeomorph.addLeft a).cantorBendixsonRank_eq b.closedSupport (translate a b).closedSupport
    b.closedSupport_isPWO (translate a b).closedSupport_isPWO
  rw [coe_closedSupport, coe_closedSupport, support_translate]
  exact (Homeomorph.addLeft a).image_closure _

omit [OrderTopology G] in
/-- Translation transports membership in the closed support. -/
theorem mem_closedSupport_translate (b : HahnSeries G R) (a x : G) :
    a + x ∈ (translate a b).closedSupport ↔ x ∈ b.closedSupport := by
  rw [mem_closedSupport, mem_closedSupport, support_translate]
  have he : (a + ·) '' closure b.support = closure ((a + ·) '' b.support) :=
    (Homeomorph.addLeft a).image_closure b.support
  rw [← he]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (add_left_cancel he : y = x) ▸ hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

/-- The rank at zero after translated weak truncation is the original rank at the cutoff. -/
theorem cantorBendixsonRank_translated_truncLE (b : HahnSeries G R) (c : G) :
    (translate (-c) (truncLE c b)).cantorBendixsonRank 0 = b.cantorBendixsonRank c := by
  simpa only [neg_add_cancel] using
    ((truncLE c b).cantorBendixsonRank_translate (-c) c).trans (b.cantorBendixsonRank_truncLE c)

open Classical in
/-- The translated weak truncation value reads the Cantor–Bendixson rank at the cutoff. -/
theorem cantorBendixsonValue_translated_truncLE (b : HahnSeries G R) (c : G) :
    (translate (-c) (truncLE c b)).cantorBendixsonValue =
      if c ∈ b.closedSupport then Ordinal.omega0 ^ b.cantorBendixsonRank c else 0 := by
  have hm : (0 : G) ∈ (translate (-c) (truncLE c b)).closedSupport ↔ c ∈ b.closedSupport := by
    simpa only [neg_add_cancel] using
      ((truncLE c b).mem_closedSupport_translate (-c) c).trans (b.mem_closedSupport_truncLE c)
  by_cases hc : c ∈ b.closedSupport
  · rw [ite_eq_left hc, cantorBendixsonValue_of_mem _ ((mem_closedSupport _ _).mp (hm.mpr hc)),
      cantorBendixsonRank_translated_truncLE]
  · rw [ite_eq_right hc]
    apply cantorBendixsonValue_of_notMem
    intro hh
    exact hc (hm.mp ((mem_closedSupport _ _).mpr hh))

/-- Nearby proper translated truncations have strictly smaller value when the value is nonzero. -/
theorem eventually_value_translated_truncLE_lt (b : HahnSeries G R)
    (hb : b.cantorBendixsonValue ≠ 0) :
    ∀ᶠ c in 𝓝 (0 : G), c ≠ 0 →
      (translate (-c) (truncLE c b)).cantorBendixsonValue < b.cantorBendixsonValue := by
  classical
  have hb0 : 0 ∈ closure b.support :=
    not_not.mp (mt (b.cantorBendixsonValue_eq_zero_iff).mpr hb)
  filter_upwards [b.closedSupport.cantorBendixsonRank_locally_lt b.closedSupport_isPWO 0]
    with c hc hne
  rw [b.cantorBendixsonValue_translated_truncLE, b.cantorBendixsonValue_of_mem hb0]
  by_cases hmem : c ∈ b.closedSupport
  · rw [ite_eq_left hmem]
    apply (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    simpa only [cantorBendixsonRank_eq] using hc hmem hne
  · rw [ite_eq_right hmem]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos

variable [Nontrivial G]

/-- Bounds at translated cutoffs of an exact lower rank reconstruct the ordinary rank sum at zero.
Only an eventual left-neighborhood bound is required; no product formula is assumed. -/
@[blueprint "lem:cantor-bendixson-rank-reconstruction"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Reconstruction from translated truncations of fixed rank")
  (statement := /--
    Let $R$ be an additive monoid, let $G$ be a nontrivial ordered
    topological abelian group with its order topology, and let
    $b,d\in R((G))$.  Suppose
    $\operatorname{supp}(b)\subseteq G^{\le0}$.
    Let $a,c,r$ be ordinals with $r>0$ and
    \[
      V_{\mathrm{CB}}(b)=\omega^{a+r}.
    \]
    Suppose that, for every $\gamma<0$ sufficiently close to $0$,
    \[
      V_{\mathrm{CB}}(b^{\vert\gamma})=\omega^a
      \quad\Longrightarrow\quad
      V_{\mathrm{CB}}(d^{\vert\gamma})\ge\omega^c.
    \]
    Then
    \[
      V_{\mathrm{CB}}(d)\ge\omega^{c+r}.
    \]
  -/)
  (proof := /--
    By \ref{def:cantor-bendixson-value}, the hypothesis on $b$ says that $0$
    has Cantor--Bendixson rank $a+r$ in its closed support.  At every nearby
    point of exact rank $a$, the translated-truncation hypothesis places that
    point in the $c$-th derivative of the closed support of $d$.
    Cantor--Bendixson
    reconstruction therefore places $0$ in its $(c+r)$-th derivative, which
    is the stated value bound.
  -/)]
theorem cantorBendixsonValue_reconstruction (b d : HahnSeries G R) (hb : b.support ⊆ Iic 0)
    (a c r : Ordinal.{u}) (hr : 0 < r)
    (hbv : b.cantorBendixsonValue = Ordinal.omega0 ^ (a + r))
    (hlevel : ∀ᶠ γ in 𝓝[<] (0 : G),
      (translate (-γ) (truncLE γ b)).cantorBendixsonValue = Ordinal.omega0 ^ a →
        Ordinal.omega0 ^ c ≤ (translate (-γ) (truncLE γ d)).cantorBendixsonValue) :
    Ordinal.omega0 ^ (c + r) ≤ d.cantorBendixsonValue := by
  classical
  have hb0 : 0 ∈ closure b.support := by
    by_contra h
    rw [b.cantorBendixsonValue_of_notMem h] at hbv
    exact (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero) hbv.symm
  have hbr : b.cantorBendixsonRank 0 = a + r := by
    rw [b.cantorBendixsonValue_of_mem hb0] at hbv
    exact (Ordinal.opow_right_inj Ordinal.one_lt_omega0).mp hbv
  obtain ⟨l, hl, hlevel⟩ := eventually_nhdsLT_iff_exists.mp hlevel
  obtain ⟨hd0, hdr⟩ := b.cantorBendixsonRank_reconstruction d isOpen_Ioi hl a c r hb0
    (le_of_eq hbr.symm) (by
      intro y hy hys hyr
      have hy0 : y ≤ 0 := closure_minimal hb isClosed_Iic hys
      have hyne : y ≠ 0 := by
        intro he
        subst y
        rw [hbr] at hyr
        exact (ne_of_gt (lt_add_of_pos_right _ hr)) hyr
      have hylt : y < 0 := lt_of_le_of_ne hy0 hyne
      have hval : (translate (-y) (truncLE y b)).cantorBendixsonValue =
          Ordinal.omega0 ^ a := by
        rw [b.cantorBendixsonValue_translated_truncLE, ite_eq_left ((b.mem_closedSupport y).mpr hys),
          hyr]
      have h := hlevel y hy hylt hval
      rw [d.cantorBendixsonValue_translated_truncLE] at h
      by_cases hym : y ∈ d.closedSupport
      · rw [ite_eq_left hym] at h
        exact ⟨(d.mem_closedSupport y).mp hym,
          (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).mp h⟩
      · rw [ite_eq_right hym] at h
        exact ((Ordinal.opow_pos _ Ordinal.omega0_pos).not_ge h).elim)
  rw [d.cantorBendixsonValue_of_mem hd0]
  exact Ordinal.opow_le_opow_right Ordinal.omega0_pos hdr

end Translation

end HahnSeries
