/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.DerivAt
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubring
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.LeibnizRemainder

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Convolution
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSubmultiplicative
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The Leibniz rule on the spaces `P_α`

Let `u ∈ J_{ω^(α+1)}` and `v ∈ J_{ω^(β+1)}` with `α` a successor, and put `δ = α + β`, so that
`δ⁻ = α⁻ + β`. Berarducci's convolution formula writes `(uv)^{|γ}` modulo `J` as the finite sum
of the products `u^{|ξ} v^{|ζ}` over `ξ + ζ = γ`. The pairs `(γ, 0)` and `(0, γ)` contribute
`u^{|γ} v` and `u v^{|γ}`; every other pair has `ξ, ζ ∈ (γ, 0)`, and for `γ` close to zero the
truncation drop gives `v_J(u^{|ξ}) ≤ ω^{α⁻}` and `v_J(v^{|ζ}) < ω^β`, so by submultiplicativity
the product has ordinal value below `ω^{α⁻ + β} = ω^{δ⁻}`. Hence

`(uv)^{|γ} ≡ u^{|γ} v + u v^{|γ}  (mod J_{ω^{δ⁻}})`

for all `γ < 0` close to zero, and in the component `P_{δ⁻}` indexed by the predecessor of `δ`
this reads
`π_{δ⁻}((uv)^{|γ}) = π_{α⁻}(u^{|γ}) π_β(v) + π_α(u) π_{β⁻}(v^{|γ})`, the last term being zero
when `β` is not a successor because its ordinal value then already lies below `ω^{δ⁻}`.
-/

open Filter Topology
open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace Berarducci

open Berarducci HahnSeries

variable {K : Type v} [Field K]

/-! ### The identity in the homogeneous component `P_{δ⁻}` -/

/-- If `v_J(a - b - c) < ω^δ`, then `π_δ(a) = π_δ(b) + π_δ(c)`. -/
theorem principalComponentMk_eq_add_of_sub_sub_lt (delta : NatOrdinal) {a b c : Series K}
    (ha : ordinalValue a < ω^ (delta + 1)) (hb : ordinalValue b < ω^ (delta + 1))
    (hc : ordinalValue c < ω^ (delta + 1)) (h : ordinalValue (a - b - c) < ω^ delta) :
    principalComponentMk delta a ha =
      principalComponentMk delta b hb + principalComponentMk delta c hc := by
  have hbc : ordinalValue (b + c) < ω^ (delta + 1) :=
    (ordinalValue_add_le_max b c).trans_lt (max_lt hb hc)
  rw [← principalComponentMk_add delta b c hb hc hbc, principalComponentMk_eq_iff]
  rwa [sub_add_eq_sub_sub]

/-- Homogeneous inclusions of the same representative in equal grades agree. -/
theorem of_principalComponentMk_congr_of_eq
    {alpha beta : NatOrdinal} (h : alpha = beta) (b : Series K)
    (hb : ordinalValue b < ω^ (beta + 1)) :
    DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta b hb) =
      DirectSum.of (PrincipalComponent K) alpha
        (principalComponentMk alpha b (by rw [h]; exact hb)) := by
  subst h
  rfl

/-- Multiplication of homogeneous inclusions is homogeneous multiplication. -/
theorem of_principalComponentMul {alpha beta : NatOrdinal}
    (x : PrincipalComponent K alpha) (y : PrincipalComponent K beta) :
    DirectSum.of (PrincipalComponent K) (alpha + beta) (principalComponentMul x y) =
      DirectSum.of (PrincipalComponent K) alpha x * DirectSum.of (PrincipalComponent K) beta y := by
  rw [principalComponentMul_eq_componentMul, DirectSum.of_mul_of]
  rfl

/-- If `β` is not a successor and `β' < β`, then `α + β' < (α + β)⁻`. -/
private theorem add_lt_removeOne_add_of_constantCoeff_eq_zero
    {alpha beta beta' : NatOrdinal} (halpha : 0 < alpha.constantCoeff)
    (hbeta : beta.constantCoeff = 0) (hlt : beta' < beta) :
    alpha + beta' < (alpha + beta).removeNat 1 := by
  have hpos : 0 < (alpha + beta).constantCoeff := by
    rw [NatOrdinal.constantCoeff_add]; omega
  have hsucc : (alpha + beta).removeNat 1 + 1 = alpha + beta := by
    simpa using NatOrdinal.removeNat_add_natCast hpos
  have hle : alpha + beta' ≤ (alpha + beta).removeNat 1 := by
    rw [← Order.lt_add_one_iff, hsucc]
    exact add_lt_add_right hlt alpha
  refine lt_of_le_of_ne hle fun heq ↦ ?_
  have hc := congrArg NatOrdinal.constantCoeff heq
  rw [NatOrdinal.constantCoeff_add, NatOrdinal.constantCoeff_removeNat,
    NatOrdinal.constantCoeff_add, hbeta] at hc
  omega

/-- For `β` not a successor, the term `u v^{|γ}` vanishes in `P_{(α+β)⁻}` near zero. -/
theorem eventually_ordinalValue_mul_translatedTruncation_lt_of_constantCoeff_eq_zero
    {alpha beta : NatOrdinal} (halpha : 0 < alpha.constantCoeff)
    (hbeta : beta.constantCoeff = 0) (u v : Series K)
    (hu : ordinalValue u < ω^ (alpha + 1)) (hv : ordinalValue v < ω^ (beta + 1)) :
    ∀ᶠ γ in 𝓝[<] (0 : ℝ),
      ordinalValue (u * translatedTruncation (v : K⟦ℝ⟧) γ) < ω^ ((alpha + beta).removeNat 1) := by
  filter_upwards
      [eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one
    beta v hv] with γ hγ
  have hu' : ordinalValue u ≤ ω^ alpha := by
    rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal u with hzero | hprin
    · rw [hzero]; exact bot_le
    · have hxi := Ordinal.natOrdinal_of_eq_wpow_log hprin
      rw [NatOrdinal.of_val] at hxi
      rw [hxi] at hu ⊢
      exact NatOrdinal.wpow_le_wpow.mpr (Order.lt_add_one_iff.mp (NatOrdinal.wpow_lt_wpow.mp hu))
  rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal (translatedTruncation (v : K⟦ℝ⟧) γ) with
    hzero | hprin
  · calc ordinalValue (u * translatedTruncation (v : K⟦ℝ⟧) γ) ≤
          ordinalValue u * ordinalValue (translatedTruncation (v : K⟦ℝ⟧) γ) :=
              ordinalValue_mul_le_naturalMul _ _
      _ = 0 := by rw [hzero, mul_zero]
      _ < _ := NatOrdinal.wpow_pos _
  · have hxi := Ordinal.natOrdinal_of_eq_wpow_log hprin
    rw [NatOrdinal.of_val] at hxi
    set beta' :=
      NatOrdinal.of (Ordinal.log Ordinal.omega0 (ordinalValue (translatedTruncation (v : K⟦ℝ⟧)
          γ)).val)
    rw [hxi] at hγ
    have hlt : beta' < beta := NatOrdinal.wpow_lt_wpow.mp hγ
    calc ordinalValue (u * translatedTruncation (v : K⟦ℝ⟧) γ) ≤
          ordinalValue u * ordinalValue (translatedTruncation (v : K⟦ℝ⟧) γ) :=
              ordinalValue_mul_le_naturalMul _ _
      _ ≤ ω^ alpha * ω^ beta' := by rw [hxi]; exact mul_le_mul_left hu' _
      _ = ω^ (alpha + beta') := (NatOrdinal.wpow_add alpha beta').symm
      _ < ω^ ((alpha + beta).removeNat 1) :=
        NatOrdinal.wpow_lt_wpow.mpr
          (add_lt_removeOne_add_of_constantCoeff_eq_zero halpha hbeta hlt)

/-- **Leibniz identity on representatives, both grades successors.** In `P̂`, near zero,
`π_{δ⁻}((uv)^{|γ}) = π_{α⁻}(u^{|γ}) π_β(v) + π_α(u) π_{β⁻}(v^{|γ})` with `δ = α + β`. -/
theorem eventually_of_derivAt_mul_of_pos {alpha beta : NatOrdinal}
    (halpha : 0 < alpha.constantCoeff) (hbeta : 0 < beta.constantCoeff)
    (u v : Series K) (hu : ordinalValue u < ω^ (alpha + 1)) (hv : ordinalValue v < ω^ (beta + 1)) :
    ∀ᶠ γ in 𝓝[<] (0 : ℝ),
      DirectSum.of (PrincipalComponent K) ((alpha + beta).removeNat 1)
          (derivAt (alpha + beta) (u * v) γ) =
        DirectSum.of (PrincipalComponent K) (alpha.removeNat 1) (derivAt alpha u γ) *
            DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta v hv) +
          DirectSum.of (PrincipalComponent K) alpha (principalComponentMk alpha u hu) *
            DirectSum.of (PrincipalComponent K) (beta.removeNat 1)
              (derivAt beta v γ) := by
  have hsum : 0 < (alpha + beta).constantCoeff := by
    rw [NatOrdinal.constantCoeff_add]; omega
  have huv : ordinalValue (u * v) < ω^ (alpha + beta + 1) := ordinalValue_mul_lt_wpow_add_one hu hv
  filter_upwards [eventually_derivAt_eq_principalComponentMk alpha halpha u hu,
    eventually_derivAt_eq_principalComponentMk beta hbeta v hv,
    eventually_derivAt_eq_principalComponentMk (alpha + beta) hsum (u * v) huv,
    eventually_ordinalValue_leibnizRemainder_lt halpha u v hu hv] with γ ⟨hγu, hcu⟩ ⟨hγv, hcv⟩
      ⟨hγuv, hcuv⟩ hrem
  have h1 : (alpha + beta).removeNat 1 = alpha.removeNat 1 + beta :=
    NatOrdinal.removeOne_add_right alpha beta halpha
  have h2 : (alpha + beta).removeNat 1 = alpha + beta.removeNat 1 := by
    rw [add_comm, NatOrdinal.removeOne_add_right beta alpha hbeta, add_comm]
  rw [hcu, hcv, hcuv, ← of_principalComponentMul, ← of_principalComponentMul,
    principalComponentMul_mk, principalComponentMul_mk, of_principalComponentMk_congr_of_eq h1,
    of_principalComponentMk_congr_of_eq h2, ← map_add]
  congr 1
  apply principalComponentMk_eq_add_of_sub_sub_lt
  rw [h1]
  exact hrem

/-- **Leibniz identity on representatives, `β` not a successor.** In `P̂`, near zero,
`π_{δ⁻}((uv)^{|γ}) = π_{α⁻}(u^{|γ}) π_β(v)` with `δ = α + β`; the term `u v^{|γ}` vanishes in
`P_{δ⁻}`. -/
theorem eventually_of_derivAt_mul_of_eq_zero {alpha beta : NatOrdinal}
    (halpha : 0 < alpha.constantCoeff) (hbeta : beta.constantCoeff = 0)
    (u v : Series K) (hu : ordinalValue u < ω^ (alpha + 1)) (hv : ordinalValue v < ω^ (beta + 1)) :
    ∀ᶠ γ in 𝓝[<] (0 : ℝ),
      DirectSum.of (PrincipalComponent K) ((alpha + beta).removeNat 1)
          (derivAt (alpha + beta) (u * v) γ) =
        DirectSum.of (PrincipalComponent K) (alpha.removeNat 1) (derivAt alpha u γ) *
          DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta v hv) := by
  have hsum : 0 < (alpha + beta).constantCoeff := by
    rw [NatOrdinal.constantCoeff_add]; omega
  have huv : ordinalValue (u * v) < ω^ (alpha + beta + 1) := ordinalValue_mul_lt_wpow_add_one hu hv
  filter_upwards [eventually_derivAt_eq_principalComponentMk alpha halpha u hu,
    eventually_derivAt_eq_principalComponentMk (alpha + beta) hsum (u * v) huv,
    eventually_ordinalValue_leibnizRemainder_lt halpha u v hu hv,
    eventually_ordinalValue_mul_translatedTruncation_lt_of_constantCoeff_eq_zero halpha hbeta u v
        hu hv]
    with γ ⟨hγu, hcu⟩ ⟨hγuv, hcuv⟩ hrem hlimit
  have h1 : (alpha + beta).removeNat 1 = alpha.removeNat 1 + beta :=
    NatOrdinal.removeOne_add_right alpha beta halpha
  rw [hcu, hcuv, ← of_principalComponentMul, principalComponentMul_mk,
    of_principalComponentMk_congr_of_eq h1]
  congr 1
  rw [principalComponentMk_eq_iff]
  have hsplit : translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ - translatedTruncation (u :
      K⟦ℝ⟧) γ * v =
      (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ - translatedTruncation (u : K⟦ℝ⟧) γ * v -
        u * translatedTruncation (v : K⟦ℝ⟧) γ) + u * translatedTruncation (v : K⟦ℝ⟧) γ := by
    abel
  rw [hsplit]
  exact (ordinalValue_add_le_max _ _).trans_lt (max_lt (h1 ▸ hrem) hlimit)

end Berarducci
