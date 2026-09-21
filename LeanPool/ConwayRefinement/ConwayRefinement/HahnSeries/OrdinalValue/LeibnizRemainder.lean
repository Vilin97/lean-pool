/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.TruncationDrop
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Convolution
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSubmultiplicative
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The Leibniz remainder of a product near zero

Berarducci, Lemma 7.7 (Fornasiero, Lavi, L'Innocente and Mantova, Proposition 2.10): for
`u ∈ J_{ω^(α+1)}` and `v ∈ J_{ω^(β+1)}` with `α` a successor, Berarducci's convolution formula
writes `(uv)^{|γ}` modulo `J` as the finite sum of the products `u^{|ξ} v^{|ζ}` over `ξ + ζ = γ`.
The pairs `(γ, 0)` and `(0, γ)` contribute `u^{|γ} v` and `u v^{|γ}`; every other pair has
`ξ, ζ ∈ (γ, 0)`, and for `γ` close to zero the truncation drop gives `v_J(u^{|ξ}) ≤ ω^{α⁻}` and
`v_J(v^{|ζ}) < ω^β`, so by submultiplicativity the product has ordinal value below
`ω^{α⁻ + β}`. Hence

`(uv)^{|γ} ≡ u^{|γ} v + u v^{|γ}  (mod J_{ω^{α⁻ + β}})`

for all `γ < 0` close to zero. Here `α⁻ + β` is `deg_J^r(u) ⊕ deg_J(v)` when `u` and `v` have
ordinal values `ω^α` and `ω^β`, which is the bound printed in the source.
-/

open Filter Topology
open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

/-- A finite sum of series of ordinal value below `ρ > 0` has ordinal value below `ρ`. -/
private theorem ordinalValue_finset_sum_lt {ι : Type*} (s : Finset ι) (f : ι → Series K)
    {ρ : NatOrdinal} (hρ : 0 < ρ) (h : ∀ i ∈ s, ordinalValue (f i) < ρ) :
    ordinalValue (∑ i ∈ s, f i) < ρ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hρ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (ordinalValue_add_le_max _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

/-- `ω^a ⊙ y < ω^(a + b)` whenever `y < ω^b`. -/
private theorem wpow_mul_lt_wpow_add_of_lt {a b y : NatOrdinal} (hy : y < ω^ b) :
    ω^ a * y < ω^ (a + b) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have hb : b ≠ 0 := by
    rintro rfl
    rw [NatOrdinal.wpow_zero] at hy
    exact hy0 (le_antisymm (Order.lt_one_iff.mp hy).le bot_le)
  obtain ⟨z, hz, n, hn⟩ := (NatOrdinal.lt_wpow_iff hb).mp hy
  calc ω^ a * y ≤ ω^ a * (ω^ z * n) := mul_le_mul_right hn.le _
    _ = ω^ (a + z) * n := by rw [← mul_assoc, ← NatOrdinal.wpow_add]
    _ < ω^ (a + b) := NatOrdinal.wpow_mul_natCast_lt (add_lt_add_right hz a) n

/-- **Convolution remainder.** For `u ∈ J_{ω^(α+1)}`, `v ∈ J_{ω^(β+1)}` and `α` a successor,
`(uv)^{|γ} - u^{|γ} v - u v^{|γ}` has ordinal value below `ω^{α⁻ + β}` for all `γ < 0` close to
zero. -/
theorem eventually_ordinalValue_leibnizRemainder_lt
    {alpha beta : NatOrdinal} (halpha : 0 < alpha.constantCoeff)
    (u v : Series K) (hu : ordinalValue u < ω^ (alpha + 1)) (hv : ordinalValue v < ω^ (beta + 1)) :
    ∀ᶠ γ in 𝓝[<] (0 : ℝ),
      ordinalValue (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ -
          translatedTruncation (u : K⟦ℝ⟧) γ * v - u * translatedTruncation (v : K⟦ℝ⟧) γ) <
        ω^ (alpha.removeNat 1 + beta) := by
  classical
  obtain ⟨ηu, hηu, hu'⟩ := eventually_nhdsLT_iff_exists.mp
    (eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one alpha u
        hu)
  obtain ⟨ηv, hηv, hv'⟩ := eventually_nhdsLT_iff_exists.mp
    (eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one beta v hv)
  rw [eventually_nhdsLT_iff_exists]
  refine ⟨max ηu ηv, max_lt hηu hηv, fun γ hηγ hγ ↦ ?_⟩
  have hαpred : alpha.removeNat 1 + 1 = alpha := by
    simpa using NatOrdinal.removeNat_add_natCast halpha
  -- The terms of the convolution sum with `ξ ∈ (γ, 0)` have small ordinal value.
  have hterm : ∀ ξ : ℝ, γ < ξ → ξ < 0 →
      ordinalValue (translatedTruncation (u : K⟦ℝ⟧) ξ * translatedTruncation (v : K⟦ℝ⟧) (γ - ξ)) <
        ω^ (alpha.removeNat 1 + beta) := by
    intro ξ hγξ hξ
    have hξu : ordinalValue (translatedTruncation (u : K⟦ℝ⟧) ξ) < ω^ alpha :=
      hu' ξ ((le_max_left _ _).trans_lt (hηγ.trans hγξ)) hξ
    have hξv : ordinalValue (translatedTruncation (v : K⟦ℝ⟧) (γ - ξ)) < ω^ beta :=
      hv' (γ - ξ) (by linarith [le_max_right ηu ηv]) (by linarith)
    have hξu' : ordinalValue (translatedTruncation (u : K⟦ℝ⟧) ξ) ≤ ω^ (alpha.removeNat 1) := by
      rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal (translatedTruncation (u : K⟦ℝ⟧) ξ) with
        hzero | hprin
      · rw [hzero]; exact bot_le
      · have hxi := Ordinal.natOrdinal_of_eq_wpow_log hprin
        rw [NatOrdinal.of_val] at hxi
        rw [hxi] at hξu ⊢
        rw [← hαpred] at hξu
        exact NatOrdinal.wpow_le_wpow.mpr (Order.lt_add_one_iff.mp (NatOrdinal.wpow_lt_wpow.mp hξu))
    calc ordinalValue (translatedTruncation (u : K⟦ℝ⟧) ξ * translatedTruncation (v : K⟦ℝ⟧) (γ - ξ))
        ≤
          ordinalValue (translatedTruncation (u : K⟦ℝ⟧) ξ) * ordinalValue (translatedTruncation (v
              : K⟦ℝ⟧) (γ - ξ)) :=
        ordinalValue_mul_le_naturalMul _ _
      _ ≤ ω^ (alpha.removeNat 1) * ordinalValue (translatedTruncation (v : K⟦ℝ⟧) (γ - ξ)) :=
        mul_le_mul_left hξu' _
      _ < ω^ (alpha.removeNat 1 + beta) := wpow_mul_lt_wpow_add_of_lt hξv
  -- Berarducci's convolution formula, with the endpoint pairs added to the index set.
  set I : Finset ℝ := convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ with hIdef
  set I' : Finset ℝ := insert γ (insert 0 I) with hI'def
  set F : ℝ → Series K := fun ξ ↦ translatedTruncation (u : K⟦ℝ⟧) ξ * translatedTruncation (v :
      K⟦ℝ⟧) (γ - ξ)
    with hFdef
  have hJ : ∀ ξ, ξ ∉ I → F ξ ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    intro ξ hξ
    rw [hIdef, mem_convolutionIndex, not_and_or] at hξ
    rcases hξ with hξ | hξ
    · exact Ideal.mul_mem_right _ _
        (translatedTruncation_mem_negativeMonomialIdeal_of_not_mem_closure_support hξ)
    · exact Ideal.mul_mem_left _ _
        (translatedTruncation_mem_negativeMonomialIdeal_of_not_mem_closure_support hξ)
  have hsumI : ∑ ξ ∈ I', F ξ - ∑ ξ ∈ I, F ξ ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    have hsub : I ⊆ I' := fun ξ hξ ↦ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hξ)
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
    exact Submodule.sum_mem _ fun ξ hξ ↦ hJ ξ (Finset.mem_sdiff.mp hξ).2
  have hconv : translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ - ∑ ξ ∈ I', F ξ ∈
      HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    have hformula := germAt_mul (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ
    simp only [germAt_apply, ← map_mul, ← map_sum] at hformula
    have hI : translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ - ∑ ξ ∈ I, F ξ ∈
        HahnSeries.Nonpositive.negativeMonomialIdeal K := by
      rw [← toGerm_eq_toGerm_iff, Subring.coe_mul]
      exact hformula
    have := Ideal.sub_mem _ hI hsumI
    rwa [sub_sub_sub_cancel_right] at this
  -- Split off the endpoint pairs `ξ = γ` and `ξ = 0`.
  set R : Finset ℝ := (I'.erase γ).erase 0 with hRdef
  have hγI' : γ ∈ I' := Finset.mem_insert_self γ _
  have h0I' : (0 : ℝ) ∈ I'.erase γ :=
    Finset.mem_erase.mpr ⟨hγ.ne', Finset.mem_insert_of_mem (Finset.mem_insert_self 0 I)⟩
  have hsplit : ∑ ξ ∈ I', F ξ = F γ + (F 0 + ∑ ξ ∈ R, F ξ) := by
    rw [Finset.add_sum_erase _ _ h0I', Finset.add_sum_erase _ _ hγI']
  have hFγ : F γ = translatedTruncation (u : K⟦ℝ⟧) γ * v := by
    simp only [hFdef, sub_self, translatedTruncation_zero]
  have hF0 : F 0 = u * translatedTruncation (v : K⟦ℝ⟧) γ := by
    simp only [hFdef, sub_zero, translatedTruncation_zero]
  -- The remainder is congruent modulo `J` to the sum over `R`.
  have hrem : translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ - translatedTruncation (u : K⟦ℝ⟧)
      γ * v -
      u * translatedTruncation (v : K⟦ℝ⟧) γ - ∑ ξ ∈ R, F ξ ∈
        HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    have : translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ - translatedTruncation (u : K⟦ℝ⟧) γ *
        v -
        u * translatedTruncation (v : K⟦ℝ⟧) γ - ∑ ξ ∈ R, F ξ =
          translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ - ∑ ξ ∈ I', F ξ := by
      rw [hsplit, hFγ, hF0]
      abel
    rw [this]
    exact hconv
  rw [ordinalValue_eq_of_sub_mem_negativeMonomialIdeal hrem]
  apply ordinalValue_finset_sum_lt _ _ (NatOrdinal.wpow_pos _)
  intro ξ hξ
  have hξ0 : ξ ≠ 0 := (Finset.mem_erase.mp hξ).1
  have hξγ : ξ ≠ γ := (Finset.mem_erase.mp (Finset.mem_erase.mp hξ).2).1
  have hξI : ξ ∈ I := by
    have hmem := (Finset.mem_erase.mp (Finset.mem_erase.mp hξ).2).2
    rw [hI'def, Finset.mem_insert, Finset.mem_insert] at hmem
    rcases hmem with h | h | h
    · exact absurd h hξγ
    · exact absurd h hξ0
    · exact h
  rw [hIdef, mem_convolutionIndex] at hξI
  have hclosure : ∀ b : Series K, closure (b : K⟦ℝ⟧).support ⊆ Set.Iic 0 := fun b ↦
    closure_minimal (HahnSeries.Nonpositive.support_subset b) isClosed_Iic
  have hξle : ξ ≤ 0 := hclosure u hξI.1
  have hγξle : γ - ξ ≤ 0 := hclosure v hξI.2
  exact hterm ξ (lt_of_le_of_ne (by linarith) (Ne.symm hξγ)) (lt_of_le_of_ne hξle hξ0)

end Berarducci

end
