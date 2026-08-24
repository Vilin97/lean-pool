/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.ResidualBounds
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-!
# Terminal d2-cage

Kernelization of draft (6.9)--(6.14) and attempt 12, Section 2.  Distances
are unsquared here because the edge--diagonal inequalities are additive.
The finite branch counts are kept explicit, so the equality and `q=d₃`
boundaries cannot disappear inside prose.
-/

namespace LeanPool.Erdos132ConvexK3

/-- The first inequality in (6.10), together with `q≤d₂`, gives `Vw<Vs`. -/
theorem terminal_central_distance_order
    {d₂ q Vw Vs : ℝ}
    (hq : q ≤ d₂) (hleftED : Vw + d₂ < q + Vs) :
    Vw < Vs := by
  linarith

/-- Draft (6.11): the two central ED inequalities and the top-two gap force
`Vs≤d₂` as well as `Vw<Vs`. -/
theorem terminal_central_distances
    {d₁ d₂ q Vw Vs : ℝ}
    (hq : q ≤ d₂)
    (hVsClasses : Vs ≤ d₁ ∧ (Vs < d₁ → Vs ≤ d₂))
    (hVwClasses : Vw ≤ d₁ ∧ (Vw < d₁ → Vw ≤ d₂))
    (hleftED : Vw + d₂ < q + Vs)
    (hrightED : Vs + d₂ < Vw + d₁) :
    Vs ≤ d₂ ∧ Vw < Vs := by
  have horder := terminal_central_distance_order hq hleftED
  refine ⟨?_, horder⟩
  by_contra hnot
  have hd₂Vs : d₂ < Vs := lt_of_not_ge hnot
  have hVsEq : Vs = d₁ := by
    by_contra hne
    have hVsLt : Vs < d₁ := lt_of_le_of_ne hVsClasses.1 hne
    exact (not_lt_of_ge (hVsClasses.2 hVsLt) hd₂Vs)
  have hVwLt : Vw < d₁ := by linarith
  have hVwLe : Vw ≤ d₂ := hVwClasses.2 hVwLt
  linarith

/-- Left branch (6.12), `Vs=d₂`: a `d₂` partner must lie on the `d₁`
circle about the opposite center. -/
theorem terminal_left_d2_partner_forces_outer_d1
    {d₁ d₂ xR : ℝ}
    (hxRClasses : xR ≤ d₁ ∧ (xR < d₁ → xR ≤ d₂))
    (hED : d₂ + d₂ < xR + d₂) :
    xR = d₁ := by
  by_contra hne
  have hxRLt : xR < d₁ := lt_of_le_of_ne hxRClasses.1 hne
  have hxRLe : xR ≤ d₂ := hxRClasses.2 hxRLt
  linarith

/-- Left branch (6.12), `Vs=d₂`: a `d₃` partner uses one of exactly the
`d₁` and `d₂` second-center radii. -/
theorem terminal_left_d3_partner_outer_band
    {d₁ d₂ d₃ xR : ℝ}
    (hxRClasses : xR ≤ d₁ ∧ (xR < d₁ → xR ≤ d₂) ∧
      (xR < d₂ → xR ≤ d₃))
    (hED : d₂ + d₃ < xR + d₂) :
    xR = d₁ ∨ xR = d₂ := by
  by_cases h1 : xR = d₁
  · exact Or.inl h1
  · right
    have hxRLt : xR < d₁ := lt_of_le_of_ne hxRClasses.1 h1
    have hxRLe : xR ≤ d₂ := hxRClasses.2.1 hxRLt
    by_contra h2
    have hxRLt₂ : xR < d₂ := lt_of_le_of_ne hxRLe h2
    have hxRLe₃ : xR ≤ d₃ := hxRClasses.2.2 hxRLt₂
    linarith

/-- Right branch (6.13), `Vs=d₂`: a `d₃` partner has second-center radius
`d₁` or `d₂` before the metric split. -/
theorem terminal_right_d3_partner_outer_band
    {d₁ d₂ d₃ tR : ℝ}
    (hd₂d₁ : d₂ < d₁)
    (htRClasses : tR ≤ d₁ ∧ (tR < d₁ → tR ≤ d₂) ∧
      (tR < d₂ → tR ≤ d₃))
    (hED : d₁ + d₃ < tR + d₂) :
    tR = d₁ ∨ tR = d₂ := by
  by_cases h1 : tR = d₁
  · exact Or.inl h1
  · right
    have htRLt : tR < d₁ := lt_of_le_of_ne htRClasses.1 h1
    have htRLe : tR ≤ d₂ := htRClasses.2.1 htRLt
    apply le_antisymm htRLe
    by_contra hnot
    have htRLt₂ : tR < d₂ := lt_of_not_ge hnot
    have htRLe₃ : tR ≤ d₃ := htRClasses.2.2 htRLt₂
    linarith

/-- Long regime, including equality: (6.13) collapses the two right `d₃`
circle slots to the single `d₁` radius. -/
theorem terminal_long_right_d3_partner_forces_outer_d1
    {d₁ d₂ d₃ tR : ℝ}
    (htRClasses : tR ≤ d₁ ∧ (tR < d₁ → tR ≤ d₂))
    (hlong : 2 * d₂ ≤ d₁ + d₃)
    (hED : d₁ + d₃ < tR + d₂) :
    tR = d₁ := by
  by_contra hne
  have htRLt : tR < d₁ := lt_of_le_of_ne htRClasses.1 hne
  have htRLe : tR ≤ d₂ := htRClasses.2 htRLt
  linarith

/-- The literal `q=d₃` boundary is impossible in the short regime. -/
theorem terminal_short_q_eq_d3_impossible
    {d₁ d₂ d₃ q : ℝ}
    (hshort : d₁ + d₃ < 2 * d₂)
    (hq : q = d₃)
    (hterminalED : 2 * d₂ < q + d₁) :
    False := by
  linarith

/-- Draft (2.15)/(6.14): in the short regime, terminal ED and the top-three
gap force `q=d₂`; the entire `q≤d₃` branch, including equality, is excluded. -/
theorem terminal_short_regime_forces_q_eq_d2
    {d₁ d₂ d₃ q : ℝ}
    (hq : q ≤ d₂)
    (hqClass : q = d₂ ∨ q ≤ d₃)
    (hshort : d₁ + d₃ < 2 * d₂)
    (hterminalED : 2 * d₂ < q + d₁) :
    q = d₂ := by
  apply le_antisymm hq
  rcases hqClass with hqEq | hqLow
  · linarith
  · exfalso
    linarith

/-- Once `q=d₂`, ED with `w` collapses the two left `d₃` circle slots to
the single `d₁` second-center radius. -/
theorem terminal_short_left_d3_partner_forces_outer_d1
    {d₁ d₂ d₃ xR : ℝ}
    (hxRClasses : xR ≤ d₁ ∧ (xR < d₁ → xR ≤ d₂))
    (hED : d₂ + d₃ < xR + d₃) :
    xR = d₁ := by
  by_contra hne
  have hxRLt : xR < d₁ := lt_of_le_of_ne hxRClasses.1 hne
  have hxRLe : xR ≤ d₂ := hxRClasses.2 hxRLt
  linarith

/-- Crude package (6.14): `3+2+1+1=7`. -/
theorem terminal_crude_seven_slot_bound
    {degree leftArc rightArc wSlot : ℕ}
    (hdegree : degree ≤ leftArc + rightArc + wSlot + 1)
    (hleft : leftArc ≤ 3) (hright : rightArc ≤ 2) (hw : wSlot ≤ 1) :
    degree ≤ 7 := by
  omega

/-- Low-tip branch: two left slots, no right branch, no `w` slot, and `s`. -/
theorem terminal_low_tip_degree_le_three
    {degree leftArc rightArc wSlot : ℕ}
    (hdegree : degree ≤ leftArc + rightArc + wSlot + 1)
    (hleft : leftArc ≤ 2) (hright : rightArc = 0) (hw : wSlot = 0) :
    degree ≤ 3 := by
  omega

/-- Regime 1 package: the right branch loses one slot, so the crude seven
becomes `3+1+1+1=6`. -/
theorem terminal_long_regime_degree_le_six
    {degree leftArc rightArc wSlot : ℕ}
    (hdegree : degree ≤ leftArc + rightArc + wSlot + 1)
    (hleft : leftArc ≤ 3) (hright : rightArc ≤ 1) (hw : wSlot ≤ 1) :
    degree ≤ 6 := by
  omega

/-- Regime 2, `w` not a partner: `3+2+0+1=6`. -/
theorem terminal_short_no_w_degree_le_six
    {degree leftArc rightArc wSlot : ℕ}
    (hdegree : degree ≤ leftArc + rightArc + wSlot + 1)
    (hleft : leftArc ≤ 3) (hright : rightArc ≤ 2) (hw : wSlot = 0) :
    degree ≤ 6 := by
  omega

/-- Regime 2, `Vw=d₃`: the left package loses one slot, giving
`2+2+1+1=6`. -/
theorem terminal_short_left_collapse_degree_le_six
    {degree leftArc rightArc wSlot : ℕ}
    (hdegree : degree ≤ leftArc + rightArc + wSlot + 1)
    (hleft : leftArc ≤ 2) (hright : rightArc ≤ 2) (hw : wSlot ≤ 1) :
    degree ≤ 6 := by
  omega

/-- Complete metric split of the terminal `d₂` cage.  Equality is included
in the first branch by `≤`; strict failure invokes the `q=d₂`/left-collapse
package. -/
theorem terminal_d2_cage_metric_split_degree_le_six
    {degree leftArc rightArc wSlot : ℕ} {d₁ d₂ d₃ : ℝ}
    (hdegree : degree ≤ leftArc + rightArc + wSlot + 1)
    (hleft : leftArc ≤ 3) (hright : rightArc ≤ 2) (hw : wSlot ≤ 1)
    (hlongCollapse : 2 * d₂ ≤ d₁ + d₃ → rightArc ≤ 1)
    (hshortCollapse : d₁ + d₃ < 2 * d₂ → wSlot = 0 ∨ leftArc ≤ 2) :
    degree ≤ 6 := by
  by_cases heq : d₁ + d₃ = 2 * d₂
  · exact terminal_long_regime_degree_le_six hdegree hleft
      (hlongCollapse (metric_equality_routes_long heq)) hw
  · by_cases hlong : 2 * d₂ ≤ d₁ + d₃
    · exact terminal_long_regime_degree_le_six hdegree hleft
        (hlongCollapse hlong) hw
    · have hshort : d₁ + d₃ < 2 * d₂ := lt_of_not_ge hlong
      rcases hshortCollapse hshort with hNoW | hLeftCollapse
      · exact terminal_short_no_w_degree_le_six hdegree hleft hright hNoW
      · exact terminal_short_left_collapse_degree_le_six hdegree hLeftCollapse hright hw

end LeanPool.Erdos132ConvexK3
