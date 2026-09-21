/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Convolution
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.GermValueCut
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointWellOrdered
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
import Mathlib.Topology.Instances.Real.Lemmas
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSubmultiplicative
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPrincipal

/-!
# The convolution remainder estimate

Berarducci, Lemma 7.7: when `v_J^p(b) ≤ v_J^p(c)`, the germ of `b * c` at a sufficiently high
negative cutoff differs from `b^{|γ} c + b c^{|γ}` by a germ of ordinal value strictly below
`v_J^r(b) ⊙ v_J(c)`.

The convolution formula expands the germ of the product as a finite sum over the index set. Two
of its terms are the displayed ones: the index `γ` contributes `b^{|γ} c` and the index `0`
contributes `b c^{|γ}`, and when either index is absent from the set the corresponding term is
already zero because a germ at a point outside the closed support vanishes. Every remaining index
`β` satisfies `γ < β < 0` and `γ < γ - β < 0`, so the eventual value cut bounds both factor
values by proper multiples of the two residual values, submultiplicativity bounds the product, and
Berarducci, Fact 3.7 for the natural product collapses the two multipliers strictly below
`v_J^p(c)`.

The bound uses Hessenberg multiplication throughout; the multipliers supplied by the value cut are
ordinary ordinal products, and the comparison between the two is where `NatOrdinal.omul_le_mul'`
enters.
-/

universe u v

public noncomputable section

open HahnSeries Filter Topology

namespace Berarducci

variable {K : Type v} [Field K]

@[simp]
theorem germOrdinalValue_zero : germOrdinalValue (0 : Germ K) = 0 :=
  germOrdinalValue_eq_zero_iff.mpr rfl

theorem germOrdinalValue_add_le_max (q p : Germ K) :
    germOrdinalValue (q + p) ≤ max (germOrdinalValue q) (germOrdinalValue p) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective p
  rw [← map_add, germOrdinalValue_mk, germOrdinalValue_mk, germOrdinalValue_mk]
  exact ordinalValue_add_le_max b c

theorem germOrdinalValue_sum_lt {ι : Type u} {s : Finset ι} {f : ι → Germ K}
    {X : NatOrdinal} (hX : 0 < X) (h : ∀ i ∈ s, germOrdinalValue (f i) < X) :
    germOrdinalValue (∑ i ∈ s, f i) < X := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hX
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (germOrdinalValue_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · exact h a (Finset.mem_insert_self a s)
    · exact ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)


theorem exists_germOrdinalValue_convolution_remainder_lt
    (b c : SeriesWithOrdinalValueAboveOne K)
    (hp : b.principalValue ≤ c.principalValue) :
    ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      germOrdinalValue (germAt ((b.1 * c.1 : Series K) : K⟦ℝ⟧) γ
          - germAt (b.1 : K⟦ℝ⟧) γ * toGerm c.1
          - toGerm b.1 * germAt (c.1 : K⟦ℝ⟧) γ)
        < b.residualValue * ordinalValue c.1 := by
  classical
  obtain ⟨ηb, hηb, hcutb⟩ := exists_ordinalValue_translatedTruncation_le b
  obtain ⟨ηc, hηc, hcutc⟩ := exists_ordinalValue_translatedTruncation_le c
  refine ⟨max ηb ηc, max_lt hηb hηc, fun γ hγlow hγ ↦ ?_⟩
  have hηbγ : ηb < γ := (le_max_left ηb ηc).trans_lt hγlow
  have hηcγ : ηc < γ := (le_max_right ηb ηc).trans_lt hγlow
  have hclosb : closure (b.1 : K⟦ℝ⟧).support ⊆ Set.Iic 0 :=
    closure_minimal (HahnSeries.Nonpositive.support_subset b.1) isClosed_Iic
  have hclosc : closure (c.1 : K⟦ℝ⟧).support ⊆ Set.Iic 0 :=
    closure_minimal (HahnSeries.Nonpositive.support_subset c.1) isClosed_Iic
  set X : NatOrdinal := b.residualValue * ordinalValue c.1 with hXdef
  have hρb : (0 : NatOrdinal) < b.residualValue :=
    pos_iff_ne_zero.mpr b.residualValue_ne_zero
  have hρc : (0 : NatOrdinal) < c.residualValue :=
    pos_iff_ne_zero.mpr c.residualValue_ne_zero
  have hvc : (0 : NatOrdinal) < ordinalValue c.1 := lt_trans zero_lt_one c.2
  have hXpos : 0 < X := mul_pos hρb hvc
  set f : ℝ → Germ K :=
    fun β ↦ germAt (b.1 : K⟦ℝ⟧) β * germAt (c.1 : K⟦ℝ⟧) (γ - β) with hfdef
  set T := convolutionIndex (b.1 : K⟦ℝ⟧) (c.1 : K⟦ℝ⟧) γ with hTdef
  have hfγ : f γ = germAt (b.1 : K⟦ℝ⟧) γ * toGerm c.1 := by
    simp only [hfdef, sub_self, germAt_apply, translatedTruncation_zero]
  have hf0 : f 0 = toGerm b.1 * germAt (c.1 : K⟦ℝ⟧) γ := by
    simp only [hfdef, sub_zero, germAt_apply, translatedTruncation_zero]
  have hfγzero : γ ∉ T → f γ = 0 := by
    intro hmem
    rw [hTdef, mem_convolutionIndex] at hmem
    push Not at hmem
    simp only [sub_self] at hmem
    simp only [hfdef, sub_self]
    by_cases hb : γ ∈ closure (b.1 : K⟦ℝ⟧).support
    · rw [germAt_eq_zero_of_not_mem_closure_support (hmem hb), mul_zero]
    · rw [germAt_eq_zero_of_not_mem_closure_support hb, zero_mul]
  have hf0zero : (0 : ℝ) ∉ T → f 0 = 0 := by
    intro hmem
    rw [hTdef, mem_convolutionIndex] at hmem
    push Not at hmem
    simp only [sub_zero] at hmem
    simp only [hfdef, sub_zero]
    by_cases hb : (0 : ℝ) ∈ closure (b.1 : K⟦ℝ⟧).support
    · rw [germAt_eq_zero_of_not_mem_closure_support (hmem hb), mul_zero]
    · rw [germAt_eq_zero_of_not_mem_closure_support hb, zero_mul]
  have hstep1 : ∑ β ∈ T, f β = f γ + ∑ β ∈ T.erase γ, f β := by
    by_cases hmem : γ ∈ T
    · exact (Finset.add_sum_erase T f hmem).symm
    · rw [Finset.erase_eq_of_notMem hmem, hfγzero hmem, zero_add]
  have hmem0 : (0 : ℝ) ∈ T.erase γ ↔ (0 : ℝ) ∈ T := by
    rw [Finset.mem_erase]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨(ne_of_lt hγ).symm, h⟩⟩
  have hstep2 : ∑ β ∈ T.erase γ, f β = f 0 + ∑ β ∈ (T.erase γ).erase 0, f β := by
    by_cases hmem : (0 : ℝ) ∈ T.erase γ
    · exact (Finset.add_sum_erase _ f hmem).symm
    · rw [Finset.erase_eq_of_notMem hmem, hf0zero (fun h ↦ hmem (hmem0.mpr h)), zero_add]
  have hcoe : ((b.1 * c.1 : Series K) : K⟦ℝ⟧) = (b.1 : K⟦ℝ⟧) * (c.1 : K⟦ℝ⟧) := rfl
  have hrewrite : germAt ((b.1 * c.1 : Series K) : K⟦ℝ⟧) γ
      - germAt (b.1 : K⟦ℝ⟧) γ * toGerm c.1
      - toGerm b.1 * germAt (c.1 : K⟦ℝ⟧) γ
      = ∑ β ∈ (T.erase γ).erase 0, f β := by
    rw [hcoe, germAt_mul, ← hTdef, ← hfdef, hstep1, hstep2, ← hfγ, ← hf0]
    abel
  rw [hrewrite]
  refine germOrdinalValue_sum_lt hXpos fun β hβ ↦ ?_
  obtain ⟨hβ0, hβrest⟩ := Finset.mem_erase.mp hβ
  obtain ⟨hβγ, hβT⟩ := Finset.mem_erase.mp hβrest
  rw [hTdef, mem_convolutionIndex] at hβT
  have hβle : β ≤ 0 := hclosb hβT.1
  have hβneg : β < 0 := lt_of_le_of_ne hβle hβ0
  have hγβle : γ - β ≤ 0 := hclosc hβT.2
  have hγβ : γ < β := by
    rcases lt_or_eq_of_le (by linarith : γ ≤ β) with h | h
    · exact h
    · exact absurd h.symm hβγ
  obtain ⟨α₁, hα₁, hα₁le⟩ := hcutb β (hηbγ.trans hγβ) hβneg
  obtain ⟨α₂, hα₂, hα₂le⟩ :=
    hcutc (γ - β) (by linarith) (by linarith)
  have hgerm : germOrdinalValue (f β) ≤
      ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) β) *
        ordinalValue (translatedTruncation (c.1 : K⟦ℝ⟧) (γ - β)) := by
    simpa only [hfdef, germAt_apply, toGerm_apply, germOrdinalValue_mk] using
      germOrdinalValue_mul_le_naturalMul (germAt (b.1 : K⟦ℝ⟧) β)
        (germAt (c.1 : K⟦ℝ⟧) (γ - β))
  have hb₁ : ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) β) ≤
      NatOrdinal.of (b.residualValue.val * α₁) := by
    simpa using NatOrdinal.of.le_iff_le.mpr hα₁le
  have hc₁ : ordinalValue (translatedTruncation (c.1 : K⟦ℝ⟧) (γ - β)) ≤
      NatOrdinal.of (c.residualValue.val * α₂) := by
    simpa using NatOrdinal.of.le_iff_le.mpr hα₂le
  have hfinal : NatOrdinal.of (b.residualValue.val * α₁) *
      NatOrdinal.of (c.residualValue.val * α₂) < X := by
    have hlt := NatOrdinal.naturalMul_mul_lt_of_lt
      (ρ₁ := b.residualValue) (ρ₂ := c.residualValue)
      (π₁ := b.principalValue) (π₂ := c.principalValue)
      (α₁ := NatOrdinal.of α₁) (α₂ := NatOrdinal.of α₂)
      c.principalValue_isMultiplicativelyPrincipal hp
      (by simpa using NatOrdinal.of.lt_iff_lt.mpr hα₁)
      (by simpa using NatOrdinal.of.lt_iff_lt.mpr hα₂)
      (mul_pos hρb hρc)
    simpa only [NatOrdinal.val_of, hXdef, mul_assoc,
      c.residualValue_mul_principalValue] using hlt
  exact ((hgerm.trans (mul_le_mul' hb₁ hc₁)).trans_lt hfinal)

/-- The convolution-remainder estimate for the actual translated truncation series, with one
left neighbourhood working uniformly for every cutoff in it. -/
theorem exists_ordinalValue_convolution_remainder_lt
    (b c : SeriesWithOrdinalValueAboveOne K)
    (hp : b.principalValue ≤ c.principalValue) :
    ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      ordinalValue
          (translatedTruncation (((b.1 * c.1 : Series K) : K⟦ℝ⟧)) γ
            - translatedTruncation (b.1 : K⟦ℝ⟧) γ * c.1
            - b.1 * translatedTruncation (c.1 : K⟦ℝ⟧) γ) <
        b.residualValue * ordinalValue c.1 := by
  obtain ⟨η, hη, hrem⟩ := exists_germOrdinalValue_convolution_remainder_lt b c hp
  refine ⟨η, hη, fun γ hηγ hγ ↦ ?_⟩
  have hrem' := hrem γ hηγ hγ
  simp only [germAt_apply, toGerm_apply] at hrem'
  rw [← map_mul, ← map_mul, ← map_sub, ← map_sub, germOrdinalValue_mk] at hrem'
  exact hrem'


end Berarducci
