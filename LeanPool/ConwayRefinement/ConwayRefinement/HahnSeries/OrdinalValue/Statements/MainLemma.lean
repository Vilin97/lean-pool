/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPoint
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ConvolutionRemainder
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.MainLemma
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ResidualPoint
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.GermValueCut
import Mathlib.Topology.Instances.Real.Lemmas
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSubmultiplicative
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPrincipal

/-!
# Berarducci's main lemma

Berarducci, Lemma 8.2. Assuming `v_J^p(b) ≤ v_J^p(c)` and that, for residual points of `b` close
to zero, the value of `b^{|γ} b^m c^2` is the expected Hessenberg product, the value of
`b^{m+1} c` is the expected Hessenberg product too.

The argument multiplies the product-rule estimate by `c`. Assuming for contradiction that
`v_J(b^{m+1} c)` falls short, continuity of ordinal multiplication at the principal value bounds
it by a proper multiple of the remainder bound, which makes the term `b^{m+1} c c^{|γ}` small as
well. What survives is the term supplied by the hypothesis, whose value is exactly the remainder
bound times `v_J(c)`; its natural-number coefficient is invertible because the coefficient field
has characteristic zero. Submultiplicativity then divides by `c`, and Lemma 6.9 turns the
resulting bound along the residual points into the missing lower bound on `v_J(b^{m+1} c)`.

The statement is placed with the residual-point statements because its proof uses Lemma 6.9.
-/

universe v

public noncomputable section

open HahnSeries Ordinal Filter Topology

namespace Berarducci

variable {K : Type v} [Field K]

/-- The germ identity of Berarducci, Lemma 8.2 (6): multiply the product-rule estimate by `c`. -/
private theorem germ_mul_powerRemainder
    (b c : SeriesWithOrdinalValueAboveOne K) (m : ℕ) (γ : ℝ) :
    toGerm c.1 * germAt ((b.1 ^ (m + 1) * c.1 : Series K) : K⟦ℝ⟧) γ
      = (m + 1) • (germAt (b.1 : K⟦ℝ⟧) γ * toGerm (b.1 ^ m * c.1 ^ 2))
        + toGerm (b.1 ^ (m + 1) * c.1) * germAt (c.1 : K⟦ℝ⟧) γ
        + toGerm c.1 * powerRemainder b c m γ := by
  rw [germAt_powerProduct_decomp b c m γ]
  have h1 : toGerm c.1 * toGerm (b.1 ^ m * c.1) = toGerm (b.1 ^ m * c.1 ^ 2) := by
    rw [← map_mul]
    congr 1
    ring
  have h2 : toGerm c.1 * toGerm (b.1 ^ (m + 1)) = toGerm (b.1 ^ (m + 1) * c.1) := by
    rw [← map_mul]
    congr 1
    ring
  rw [mul_add, mul_add, mul_smul_comm, ← mul_assoc, mul_comm (toGerm c.1) (germAt _ γ),
    mul_assoc, h1, ← mul_assoc, h2]

/-- Berarducci, Lemma 8.2. -/
theorem ordinalValue_pow_mul_eq_of_eventually [CharZero K]
    (b c : SeriesWithOrdinalValueAboveOne K) (hp : b.principalValue ≤ c.principalValue) (m : ℕ)
    (hyp : ∀ᶠ γ in nhdsWithin (0 : ℝ) (Set.Iio 0), γ ∈ residualPointSet b →
      ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ * b.1 ^ m * c.1 ^ 2)
        = ordinalValue b.1 ^ m * ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ)
            * ordinalValue c.1 * ordinalValue c.1) :
    ordinalValue (b.1 ^ (m + 1) * c.1) = ordinalValue b.1 ^ (m + 1) * ordinalValue c.1 := by
  classical
  set X := powerRemainderBound b c m with hXdef
  set W := ordinalValue c.1 with hWdef
  have hZ : X * b.principalValue = ordinalValue b.1 ^ (m + 1) * W := by
    rw [hXdef, powerRemainderBound_eq, ← b.residualValue_mul_principalValue]
    ring
  refine le_antisymm (ordinalValue_pow_mul_le b.1 c.1 (m + 1)) ?_
  by_contra hcon
  rw [not_le] at hcon
  rw [← hZ] at hcon
  obtain ⟨α₁, hα₁, hα₁le⟩ := exists_le_mul_of_lt_powerRemainderBound_mul b c hp m hcon
  have hWpos : (0 : NatOrdinal) < W := lt_trans zero_lt_one c.2
  have hXpos : (0 : NatOrdinal) < X := by
    rw [hXdef, powerRemainderBound_eq]
    exact mul_pos (mul_pos (pow_pos (lt_trans zero_lt_one b.2) m)
      (pos_iff_ne_zero.mpr b.residualValue_ne_zero)) hWpos
  have hσpos : (0 : NatOrdinal) < c.residualValue :=
    pos_iff_ne_zero.mpr c.residualValue_ne_zero
  -- the eventual statement feeding Lemma 6.9
  have hkey : ∀ᶠ γ in nhdsWithin (0 : ℝ) (Set.Iio 0), γ ∈ residualPointSet b →
      NatOrdinal.of X.val ≤
        ordinalValue (translatedTruncation ((b.1 ^ (m + 1) * c.1 : Series K) : K⟦ℝ⟧) γ) := by
    obtain ⟨ηR, hηR, hR⟩ := exists_powerRemainder_lt b c hp m
    obtain ⟨ηc, hηc, hcutc⟩ := exists_ordinalValue_translatedTruncation_le c
    rw [eventually_nhdsLT_iff_exists] at hyp ⊢
    obtain ⟨ηh, hηh, hhyp⟩ := hyp
    refine ⟨max ηR (max ηc ηh), max_lt hηR (max_lt hηc hηh),
      fun γ hlow hhigh hγX ↦ ?_⟩
    have hγR : ηR < γ := (le_max_left _ _).trans_lt hlow
    have hγc : ηc < γ := ((le_max_left ηc ηh).trans (le_max_right ηR _)).trans_lt hlow
    have hγh : ηh < γ := ((le_max_right ηc ηh).trans (le_max_right ηR _)).trans_lt hlow
    obtain ⟨α₂, hα₂, hα₂le⟩ := hcutc γ hγc hhigh
    set g := germAt ((b.1 ^ (m + 1) * c.1 : Series K) : K⟦ℝ⟧) γ with hgdef
    set main :=
      (m + 1) • (germAt (b.1 : K⟦ℝ⟧) γ * toGerm (b.1 ^ m * c.1 ^ 2)) with hmaindef
    set s1 := toGerm (b.1 ^ (m + 1) * c.1) * germAt (c.1 : K⟦ℝ⟧) γ with hs1def
    set s2 := toGerm c.1 * powerRemainder b c m γ with hs2def
    have hid : toGerm c.1 * g = main + s1 + s2 := germ_mul_powerRemainder b c m γ
    have hcast : ((m + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have hmainval : germOrdinalValue main = X * W := by
      rw [hmaindef, germOrdinalValue_nsmul hcast, germAt_apply, ← map_mul, toGerm_apply,
        germOrdinalValue_mk, ← mul_assoc, hhyp γ hγh hhigh hγX,
        (mem_residualPointSet_iff.mp hγX).2, hXdef, powerRemainderBound_eq]
    have hs1 : germOrdinalValue s1 < X * W := by
      have hle : germOrdinalValue s1 ≤
          NatOrdinal.of (X.val * α₁) * NatOrdinal.of (c.residualValue.val * α₂) := by
        refine (germOrdinalValue_mul_le_naturalMul _ _).trans (mul_le_mul' ?_ ?_)
        · rw [germOrdinalValue_toGerm]
          simpa using NatOrdinal.of.le_iff_le.mpr hα₁le
        · rw [germAt_apply, toGerm_apply, germOrdinalValue_mk]
          simpa using NatOrdinal.of.le_iff_le.mpr hα₂le
      refine hle.trans_lt ?_
      have hlt := NatOrdinal.naturalMul_mul_lt_of_lt
        (ρ₁ := X) (ρ₂ := c.residualValue)
        (π₁ := b.principalValue) (π₂ := c.principalValue)
        (α₁ := NatOrdinal.of α₁) (α₂ := NatOrdinal.of α₂)
        c.principalValue_isMultiplicativelyPrincipal hp
        (by rw [← NatOrdinal.of_val b.principalValue]; exact NatOrdinal.of.lt_iff_lt.mpr hα₁)
        (by rw [← NatOrdinal.of_val c.principalValue]; exact NatOrdinal.of.lt_iff_lt.mpr hα₂)
        (mul_pos hXpos hσpos)
      rw [NatOrdinal.val_of, NatOrdinal.val_of, mul_assoc,
        c.residualValue_mul_principalValue] at hlt
      exact hlt
    have hs2 : germOrdinalValue s2 < X * W := by
      have hle : germOrdinalValue s2 ≤ W * germOrdinalValue (powerRemainder b c m γ) :=
        (germOrdinalValue_mul_le_naturalMul _ _).trans
          (mul_le_mul_left (le_of_eq (germOrdinalValue_toGerm c.1)) _)
      refine hle.trans_lt ?_
      rw [mul_comm X W]
      exact mul_lt_mul_of_pos_left (hR γ hγR hhigh) hWpos
    have hge : X * W ≤ germOrdinalValue (toGerm c.1 * g) := by
      by_contra hlt
      rw [not_le] at hlt
      have hmain_eq : main = toGerm c.1 * g + -s1 + -s2 := by rw [hid]; abel
      have hbound : germOrdinalValue main ≤
          max (max (germOrdinalValue (toGerm c.1 * g)) (germOrdinalValue s1)) (germOrdinalValue s2)
              := by
        rw [hmain_eq]
        refine (germOrdinalValue_add_le_max _ _).trans (max_le ?_ ?_)
        · refine (germOrdinalValue_add_le_max _ _).trans (max_le ?_ ?_)
          · exact (le_max_left _ _).trans (le_max_left _ _)
          · rw [germOrdinalValue_neg]
            exact (le_max_right _ _).trans (le_max_left _ _)
        · rw [germOrdinalValue_neg]
          exact le_max_right _ _
      rw [hmainval] at hbound
      exact absurd hbound (not_le.mpr (max_lt (max_lt hlt hs1) hs2))
    have hdiv : X ≤ germOrdinalValue g := by
      have hstep : germOrdinalValue (toGerm c.1 * g) ≤ W * germOrdinalValue g :=
        (germOrdinalValue_mul_le_naturalMul _ _).trans
          (mul_le_mul_left (le_of_eq (germOrdinalValue_toGerm c.1)) _)
      have hmul : W * X ≤ W * germOrdinalValue g := by
        rw [mul_comm W X]
        exact hge.trans hstep
      exact le_of_mul_le_mul_left hmul hWpos
    rw [NatOrdinal.of_val]
    rw [hgdef, germAt_apply, toGerm_apply, germOrdinalValue_mk] at hdiv
    exact hdiv
  have hXprincipal : Ordinal.IsPrincipal (fun a b ↦ a + b) X.val :=
    (isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp
      (isAdditivelyPrincipal_powerRemainderBound b c hp m)).2
  have h69 := ordinalValue_ge_of_eventually_ordinalValue_translatedTruncation_ge b
    (b.1 ^ (m + 1) * c.1) hXprincipal hkey
  rw [← powerRemainderBound_mul_principalValue_val b c hp m, NatOrdinal.of_val] at h69
  exact absurd h69 (not_le.mpr hcon)

/-- Berarducci, Lemma 8.2 for a pure power, the case `c = 1` of the source. The comparison of
principal values disappears with the term it controlled, and so does the division by `v_J(c)`. -/
theorem ordinalValue_pow_eq_of_eventually [CharZero K]
    (b : SeriesWithOrdinalValueAboveOne K) (m : ℕ)
    (hyp : ∀ᶠ γ in nhdsWithin (0 : ℝ) (Set.Iio 0), γ ∈ residualPointSet b →
      ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ * b.1 ^ m)
        = ordinalValue b.1 ^ m * ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ)) :
    ordinalValue (b.1 ^ (m + 1)) = ordinalValue b.1 ^ (m + 1) := by
  classical
  set X := powerRemainderBoundOne b m with hXdef
  have hZ : X * b.principalValue = ordinalValue b.1 ^ (m + 1) := by
    rw [hXdef, powerRemainderBoundOne_eq, mul_assoc, b.residualValue_mul_principalValue, pow_succ]
  refine le_antisymm (ordinalValue_pow_le b.1 (m + 1)) ?_
  by_contra hcon
  rw [not_le, ← hZ] at hcon
  have hkey : ∀ᶠ γ in nhdsWithin (0 : ℝ) (Set.Iio 0), γ ∈ residualPointSet b →
      NatOrdinal.of X.val ≤
        ordinalValue (translatedTruncation ((b.1 ^ (m + 1) : Series K) : K⟦ℝ⟧) γ) := by
    obtain ⟨ηR, hηR, hR⟩ := exists_powerRemainderOne_lt b m
    rw [eventually_nhdsLT_iff_exists] at hyp ⊢
    obtain ⟨ηh, hηh, hhyp⟩ := hyp
    refine ⟨max ηR ηh, max_lt hηR hηh, fun γ hlow hhigh hγX ↦ ?_⟩
    have hγR : ηR < γ := (le_max_left _ _).trans_lt hlow
    have hγh : ηh < γ := (le_max_right _ _).trans_lt hlow
    set g := germAt ((b.1 ^ (m + 1) : Series K) : K⟦ℝ⟧) γ with hgdef
    set main := (m + 1) • (germAt (b.1 : K⟦ℝ⟧) γ * toGerm (b.1 ^ m)) with hmaindef
    set s := powerRemainderOne b m γ with hsdef
    have hid : g = main + s := germAt_purePower_decomp b m γ
    have hcast : ((m + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have hmainval : germOrdinalValue main = X := by
      rw [hmaindef, germOrdinalValue_nsmul hcast, germAt_apply, ← map_mul, toGerm_apply,
        germOrdinalValue_mk, hhyp γ hγh hhigh hγX, (mem_residualPointSet_iff.mp hγX).2, hXdef,
        powerRemainderBoundOne_eq]
    have hs : germOrdinalValue s < X := hR γ hγR hhigh
    have hge : X ≤ germOrdinalValue g := by
      by_contra hlt
      rw [not_le] at hlt
      have hmain_eq : main = g + -s := by rw [hid]; abel
      have hbound : germOrdinalValue main ≤ max (germOrdinalValue g) (germOrdinalValue s) := by
        rw [hmain_eq]
        refine (germOrdinalValue_add_le_max _ _).trans (max_le (le_max_left _ _) ?_)
        rw [germOrdinalValue_neg]
        exact le_max_right _ _
      rw [hmainval] at hbound
      exact absurd hbound (not_le.mpr (max_lt hlt hs))
    rw [NatOrdinal.of_val]
    rw [hgdef, germAt_apply, toGerm_apply, germOrdinalValue_mk] at hge
    exact hge
  have hXprincipal : Ordinal.IsPrincipal (fun a b ↦ a + b) X.val :=
    (isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp
      (isAdditivelyPrincipal_powerRemainderBoundOne b m)).2
  have h69 := ordinalValue_ge_of_eventually_ordinalValue_translatedTruncation_ge b
    (b.1 ^ (m + 1)) hXprincipal hkey
  rw [← powerRemainderBoundOne_mul_principalValue_val b m, NatOrdinal.of_val] at h69
  exact absurd h69 (not_le.mpr hcon)

end Berarducci
