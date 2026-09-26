/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Convolution
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ConvolutionRemainder
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.GermValueCut
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointWellOrdered
import Mathlib.Topology.Instances.Real.Lemmas
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPrincipal
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSubmultiplicative

/-!
# The product-rule form of the convolution remainder estimate

The form of Berarducci, Lemma 7.7 used in the proof of Lemma 8.2: when `v_J^p(b) ≤ v_J^p(c)`, the
germ of `b ^ (m + 1) * c` at a sufficiently high negative cutoff differs from

`(m + 1) * b^{|γ} b^m c + b^{m+1} c^{|γ}`

by a germ of ordinal value strictly below `v_J(b) ^ m ⊙ v_J^r(b) ⊙ v_J(c)`.

The source proves this by "reasoning as in Lemma 7.7". Applying Lemma 7.7 to the pair
`(b, b^m c)` is not available, because its hypothesis compares principal values and the principal
value of a product is exactly what multiplicativity has yet to supply. The induction here avoids
that by carrying a value cut for the partial products alongside the formula: from the formula at
stage `m`, submultiplicativity bounds `v_J((b^{m+1} c)^{|ξ})` by a maximum of three terms, each of
which is small enough after multiplication by a truncation value of `b`. The three resulting
estimates are two instances of `NatOrdinal.naturalMul_mul_lt_of_lt` and the comparison
`v_J^r(b) * α < v_J(b)` for `α < v_J^p(b)`.

The integer coefficient is a natural-number scalar on germs, so the identity holds in every
characteristic. Berarducci's characteristic-zero hypothesis is needed only where that coefficient
must be shown not to annihilate its term, which happens in Lemma 8.2.
-/

universe v

public noncomputable section

open HahnSeries

namespace Berarducci

variable {K : Type v} [Field K]

/-- The remainder in the product-rule form of Berarducci, Lemma 7.7, for `b ^ (m + 1) * c`. -/
def powerRemainder (b c : SeriesWithOrdinalValueAboveOne K) (m : ℕ) (γ : ℝ) : Germ K :=
  germAt ((b.1 ^ (m + 1) * c.1 : Series K) : K⟦ℝ⟧) γ
    - (m + 1) • (germAt (b.1 : K⟦ℝ⟧) γ * toGerm (b.1 ^ m * c.1))
    - toGerm (b.1 ^ (m + 1)) * germAt (c.1 : K⟦ℝ⟧) γ

/-- The remainder, unfolded. -/
theorem powerRemainder_eq (b c : SeriesWithOrdinalValueAboveOne K) (m : ℕ) (γ : ℝ) :
    powerRemainder b c m γ = germAt ((b.1 ^ (m + 1) * c.1 : Series K) : K⟦ℝ⟧) γ
      - (m + 1) • (germAt (b.1 : K⟦ℝ⟧) γ * toGerm (b.1 ^ m * c.1))
      - toGerm (b.1 ^ (m + 1)) * germAt (c.1 : K⟦ℝ⟧) γ := (rfl)

/-- The bound on that remainder. -/
def powerRemainderBound (b c : SeriesWithOrdinalValueAboveOne K) (m : ℕ) : NatOrdinal :=
  ordinalValue b.1 ^ m * b.residualValue * ordinalValue c.1

/-- The remainder bound, unfolded. -/
theorem powerRemainderBound_eq (b c : SeriesWithOrdinalValueAboveOne K) (m : ℕ) :
    powerRemainderBound b c m = ordinalValue b.1 ^ m * b.residualValue * ordinalValue c.1 :=
  (rfl)

private theorem powerRemainder_zero (b c : SeriesWithOrdinalValueAboveOne K) (γ : ℝ) :
    powerRemainder b c 0 γ =
      germAt ((b.1 * c.1 : Series K) : K⟦ℝ⟧) γ
        - germAt (b.1 : K⟦ℝ⟧) γ * toGerm c.1
        - toGerm b.1 * germAt (c.1 : K⟦ℝ⟧) γ := by
  simp only [powerRemainder, pow_one, pow_zero, one_mul, zero_add, one_smul]

private theorem powerRemainderBound_zero (b c : SeriesWithOrdinalValueAboveOne K) :
    powerRemainderBound b c 0 = b.residualValue * ordinalValue c.1 := by
  simp [powerRemainderBound]

theorem exists_powerRemainder_lt_zero
    (b c : SeriesWithOrdinalValueAboveOne K) (hp : b.principalValue ≤ c.principalValue) :
    ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      germOrdinalValue (powerRemainder b c 0 γ) < powerRemainderBound b c 0 := by
  obtain ⟨η, hη, h⟩ := exists_germOrdinalValue_convolution_remainder_lt b c hp
  refine ⟨η, hη, fun γ hlow hhigh ↦ ?_⟩
  rw [powerRemainder_zero, powerRemainderBound_zero]
  exact h γ hlow hhigh

theorem germOrdinalValue_nsmul_le (n : ℕ) (q : Germ K) :
    germOrdinalValue (n • q) ≤ germOrdinalValue q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    exact (germOrdinalValue_add_le_max _ _).trans (max_le ih le_rfl)

theorem ordinalValue_pow_le (b : Series K) (m : ℕ) :
    ordinalValue (b ^ m) ≤ ordinalValue b ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact (ordinalValue_mul_le_naturalMul _ _).trans (mul_le_mul_left ih _)

theorem ordinalValue_pow_mul_le (b c : Series K) (m : ℕ) :
    ordinalValue (b ^ m * c) ≤ ordinalValue b ^ m * ordinalValue c :=
  (ordinalValue_mul_le_naturalMul _ _).trans (mul_le_mul_left (ordinalValue_pow_le b m) _)

/-- The defining decomposition of the remainder, read as an expansion of the germ. -/
theorem germAt_powerProduct_decomp
    (b c : SeriesWithOrdinalValueAboveOne K) (m : ℕ) (ξ : ℝ) :
    germAt ((b.1 ^ (m + 1) * c.1 : Series K) : K⟦ℝ⟧) ξ =
      (m + 1) • (germAt (b.1 : K⟦ℝ⟧) ξ * toGerm (b.1 ^ m * c.1))
        + toGerm (b.1 ^ (m + 1)) * germAt (c.1 : K⟦ℝ⟧) ξ
        + powerRemainder b c m ξ := by
  rw [powerRemainder]
  abel

/-- The germ ordinal value of a class is the ordinal value of any representative. -/
theorem germOrdinalValue_toGerm (x : Series K) :
    germOrdinalValue (toGerm x) = ordinalValue x := by
  rw [toGerm_apply, germOrdinalValue_mk]

private theorem exists_mul_germOrdinalValue_powerProduct_lt
    (b c : SeriesWithOrdinalValueAboveOne K) (hp : b.principalValue ≤ c.principalValue) (m : ℕ)
    (hP : ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      germOrdinalValue (powerRemainder b c m γ) < powerRemainderBound b c m) :
    ∃ η < (0 : ℝ), ∀ ξ : ℝ, η < ξ → ξ < 0 →
      ∀ α : Ordinal, α < b.principalValue.val → NatOrdinal.of (b.residualValue.val * α) *
          germOrdinalValue (germAt ((b.1 ^ (m + 1) * c.1 : Series K) : K⟦ℝ⟧) ξ)
        < powerRemainderBound b c (m + 1) := by
  obtain ⟨ηP, hηP, hP'⟩ := hP
  obtain ⟨ηb, hηb, hcutb⟩ := exists_ordinalValue_translatedTruncation_le b
  obtain ⟨ηc, hηc, hcutc⟩ := exists_ordinalValue_translatedTruncation_le c
  refine ⟨max ηP (max ηb ηc), max_lt hηP (max_lt hηb hηc),
    fun ξ hlow hhigh α hα ↦ ?_⟩
  have hξP : ηP < ξ := (le_max_left _ _).trans_lt hlow
  have hξb : ηb < ξ := ((le_max_left ηb ηc).trans (le_max_right ηP _)).trans_lt hlow
  have hξc : ηc < ξ := ((le_max_right ηb ηc).trans (le_max_right ηP _)).trans_lt hlow
  obtain ⟨α₁, hα₁, hα₁le⟩ := hcutb ξ hξb hhigh
  obtain ⟨α₂, hα₂, hα₂le⟩ := hcutc ξ hξc hhigh
  set t : NatOrdinal := NatOrdinal.of (b.residualValue.val * α) with htdef
  set V := ordinalValue b.1 with hV
  set W := ordinalValue c.1 with hW
  have hmono : Monotone fun x : NatOrdinal ↦ t * x := fun _ _ h ↦ mul_le_mul_right h t
  have hgermb : germOrdinalValue (germAt (b.1 : K⟦ℝ⟧) ξ) ≤
      NatOrdinal.of (b.residualValue.val * α₁) := by
    rw [germAt_apply, toGerm_apply, germOrdinalValue_mk]
    simpa using NatOrdinal.of.le_iff_le.mpr hα₁le
  have hgermc : germOrdinalValue (germAt (c.1 : K⟦ℝ⟧) ξ) ≤
      NatOrdinal.of (c.residualValue.val * α₂) := by
    rw [germAt_apply, toGerm_apply, germOrdinalValue_mk]
    simpa using NatOrdinal.of.le_iff_le.mpr hα₂le
  have hA : germOrdinalValue ((m + 1) • (germAt (b.1 : K⟦ℝ⟧) ξ * toGerm (b.1 ^ m * c.1))) ≤
      NatOrdinal.of (b.residualValue.val * α₁) * (V ^ m * W) := by
    refine (germOrdinalValue_nsmul_le _ _).trans ?_
    refine (germOrdinalValue_mul_le_naturalMul _ _).trans (mul_le_mul' hgermb ?_)
    rw [germOrdinalValue_toGerm]
    exact ordinalValue_pow_mul_le b.1 c.1 m
  have hB : germOrdinalValue (toGerm (b.1 ^ (m + 1)) * germAt (c.1 : K⟦ℝ⟧) ξ) ≤
      V ^ (m + 1) * NatOrdinal.of (c.residualValue.val * α₂) := by
    refine (germOrdinalValue_mul_le_naturalMul _ _).trans (mul_le_mul' ?_ hgermc)
    rw [germOrdinalValue_toGerm]
    exact ordinalValue_pow_le b.1 (m + 1)
  have hC : germOrdinalValue (powerRemainder b c m ξ) < V ^ m * b.residualValue * W :=
    hP' ξ hξP hhigh
  have hval : germOrdinalValue (germAt ((b.1 ^ (m + 1) * c.1 : Series K) : K⟦ℝ⟧) ξ) ≤
      max (max (NatOrdinal.of (b.residualValue.val * α₁) * (V ^ m * W))
        (V ^ (m + 1) * NatOrdinal.of (c.residualValue.val * α₂)))
        (V ^ m * b.residualValue * W) := by
    rw [germAt_powerProduct_decomp b c m ξ]
    refine (germOrdinalValue_add_le_max _ _).trans (max_le ?_ ?_)
    · exact ((germOrdinalValue_add_le_max _ _).trans (max_le (hA.trans (le_max_left _ _))
        (hB.trans (le_max_right _ _)))).trans (le_max_left _ _)
    · exact hC.le.trans (le_max_right _ _)
  have hVpos : (0 : NatOrdinal) < V := lt_trans zero_lt_one b.2
  have hWpos : (0 : NatOrdinal) < W := lt_trans zero_lt_one c.2
  have hρpos : (0 : NatOrdinal) < b.residualValue :=
    pos_iff_ne_zero.mpr b.residualValue_ne_zero
  have hσpos : (0 : NatOrdinal) < c.residualValue :=
    pos_iff_ne_zero.mpr c.residualValue_ne_zero
  have hVmW : (0 : NatOrdinal) < V ^ m * W := mul_pos (pow_pos hVpos m) hWpos
  have hVm1 : (0 : NatOrdinal) < V ^ (m + 1) := pow_pos hVpos (m + 1)
  have hXpos : (0 : NatOrdinal) < V ^ m * b.residualValue * W :=
    mul_pos (mul_pos (pow_pos hVpos m) hρpos) hWpos
  have h1 : t * (NatOrdinal.of (b.residualValue.val * α₁) * (V ^ m * W)) <
      powerRemainderBound b c (m + 1) := by
    have key : t * NatOrdinal.of (b.residualValue.val * α₁) <
        b.residualValue * b.residualValue * b.principalValue :=
      NatOrdinal.naturalMul_mul_lt_of_lt
        b.principalValue_isMultiplicativelyPrincipal le_rfl
        (by rw [← NatOrdinal.of_val b.principalValue]; exact NatOrdinal.of.lt_iff_lt.mpr hα)
        (by rw [← NatOrdinal.of_val b.principalValue]; exact NatOrdinal.of.lt_iff_lt.mpr hα₁)
        (mul_pos hρpos hρpos)
    calc t * (NatOrdinal.of (b.residualValue.val * α₁) * (V ^ m * W))
        = t * NatOrdinal.of (b.residualValue.val * α₁) * (V ^ m * W) := by ring
      _ < b.residualValue * b.residualValue * b.principalValue * (V ^ m * W) :=
          mul_lt_mul_of_pos_right key hVmW
      _ = powerRemainderBound b c (m + 1) := by
          rw [powerRemainderBound, mul_assoc b.residualValue b.residualValue,
            b.residualValue_mul_principalValue]
          ring
  have h2 : t * (V ^ (m + 1) * NatOrdinal.of (c.residualValue.val * α₂)) <
      powerRemainderBound b c (m + 1) := by
    have key : t * NatOrdinal.of (c.residualValue.val * α₂) <
        b.residualValue * c.residualValue * c.principalValue :=
      NatOrdinal.naturalMul_mul_lt_of_lt
        c.principalValue_isMultiplicativelyPrincipal hp
        (by rw [← NatOrdinal.of_val b.principalValue]; exact NatOrdinal.of.lt_iff_lt.mpr hα)
        (by rw [← NatOrdinal.of_val c.principalValue]; exact NatOrdinal.of.lt_iff_lt.mpr hα₂)
        (mul_pos hρpos hσpos)
    calc t * (V ^ (m + 1) * NatOrdinal.of (c.residualValue.val * α₂))
        = V ^ (m + 1) * (t * NatOrdinal.of (c.residualValue.val * α₂)) := by ring
      _ < V ^ (m + 1) * (b.residualValue * c.residualValue * c.principalValue) :=
          mul_lt_mul_of_pos_left key hVm1
      _ = powerRemainderBound b c (m + 1) := by
          rw [powerRemainderBound, mul_assoc b.residualValue c.residualValue,
            c.residualValue_mul_principalValue]
          ring
  have h3 : t * (V ^ m * b.residualValue * W) < powerRemainderBound b c (m + 1) := by
    have htV : t < V := by
      have hle : t ≤ b.residualValue * NatOrdinal.of α := by
        simpa [htdef] using NatOrdinal.of.le_iff_le.mpr
          (NatOrdinal.omul_le_mul' b.residualValue.val α)
      refine hle.trans_lt ?_
      have hVeq : b.residualValue * b.principalValue = V :=
        b.residualValue_mul_principalValue
      rw [← hVeq]
      refine mul_lt_mul_of_pos_left ?_ hρpos
      rw [← NatOrdinal.of_val b.principalValue]
      exact NatOrdinal.of.lt_iff_lt.mpr hα
    calc t * (V ^ m * b.residualValue * W) < V * (V ^ m * b.residualValue * W) :=
          mul_lt_mul_of_pos_right htV hXpos
      _ = powerRemainderBound b c (m + 1) := by
          rw [powerRemainderBound]
          ring
  calc t * germOrdinalValue (germAt ((b.1 ^ (m + 1) * c.1 : Series K) : K⟦ℝ⟧) ξ)
      ≤ t * (max (max (NatOrdinal.of (b.residualValue.val * α₁) * (V ^ m * W))
          (V ^ (m + 1) * NatOrdinal.of (c.residualValue.val * α₂)))
          (V ^ m * b.residualValue * W)) := mul_le_mul_right hval t
    _ = max (max (t * (NatOrdinal.of (b.residualValue.val * α₁) * (V ^ m * W)))
          (t * (V ^ (m + 1) * NatOrdinal.of (c.residualValue.val * α₂))))
          (t * (V ^ m * b.residualValue * W)) := by
        rw [hmono.map_max, hmono.map_max]
    _ < powerRemainderBound b c (m + 1) := max_lt (max_lt h1 h2) h3

private theorem powerRemainder_step
    (b c : SeriesWithOrdinalValueAboveOne K) (hp : b.principalValue ≤ c.principalValue) (m : ℕ)
    (hP : ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      germOrdinalValue (powerRemainder b c m γ) < powerRemainderBound b c m) :
    ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      germOrdinalValue (powerRemainder b c (m + 1) γ) < powerRemainderBound b c (m + 1) := by
  classical
  obtain ⟨ηQ, hηQ, hQ⟩ := exists_mul_germOrdinalValue_powerProduct_lt b c hp m hP
  obtain ⟨ηP, hηP, hP'⟩ := hP
  obtain ⟨ηb, hηb, hcutb⟩ := exists_ordinalValue_translatedTruncation_le b
  refine ⟨max ηQ (max ηP ηb), max_lt hηQ (max_lt hηP hηb), fun γ hlow hhigh ↦ ?_⟩
  have hγQ : ηQ < γ := (le_max_left _ _).trans_lt hlow
  have hγP : ηP < γ := ((le_max_left ηP ηb).trans (le_max_right ηQ _)).trans_lt hlow
  have hγb : ηb < γ := ((le_max_right ηP ηb).trans (le_max_right ηQ _)).trans_lt hlow
  set d : Series K := b.1 ^ (m + 1) * c.1 with hddef
  set T := convolutionIndex (b.1 : K⟦ℝ⟧) ((d : Series K) : K⟦ℝ⟧) γ with hTdef
  set f : ℝ → Germ K :=
    fun β ↦
      germAt (b.1 : K⟦ℝ⟧) β * germAt ((d : Series K) : K⟦ℝ⟧) (γ - β) with hfdef
  have hclosb : closure (b.1 : K⟦ℝ⟧).support ⊆ Set.Iic 0 :=
    closure_minimal (HahnSeries.Nonpositive.support_subset b.1) isClosed_Iic
  have hclosd : closure ((d : Series K) : K⟦ℝ⟧).support ⊆ Set.Iic 0 :=
    closure_minimal (HahnSeries.Nonpositive.support_subset d) isClosed_Iic
  have hfγ : f γ = germAt (b.1 : K⟦ℝ⟧) γ * toGerm d := by
    simp only [hfdef, sub_self, germAt_apply, translatedTruncation_zero]
  have hf0 : f 0 = toGerm b.1 * germAt ((d : Series K) : K⟦ℝ⟧) γ := by
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
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨(ne_of_lt hhigh).symm, h⟩⟩
  have hstep2 : ∑ β ∈ T.erase γ, f β = f 0 + ∑ β ∈ (T.erase γ).erase 0, f β := by
    by_cases hmem : (0 : ℝ) ∈ T.erase γ
    · exact (Finset.add_sum_erase _ f hmem).symm
    · rw [Finset.erase_eq_of_notMem hmem, hf0zero (fun h ↦ hmem (hmem0.mpr h)), zero_add]
  have hSeries : (b.1 ^ (m + 1 + 1) * c.1 : Series K) = b.1 * d := by
    rw [hddef]; ring
  have hcoe : ((b.1 ^ (m + 1 + 1) * c.1 : Series K) : K⟦ℝ⟧)
      = (b.1 : K⟦ℝ⟧) * ((d : Series K) : K⟦ℝ⟧) := by rw [hSeries]; rfl
  have hsum : germAt ((b.1 ^ (m + 1 + 1) * c.1 : Series K) : K⟦ℝ⟧) γ
      = f γ + f 0 + ∑ β ∈ (T.erase γ).erase 0, f β := by
    rw [hcoe, germAt_mul, ← hTdef, ← hfdef, hstep1, hstep2]
    abel
  have hg1 : toGerm (b.1 ^ m * c.1) = toGerm b.1 ^ m * toGerm c.1 := by
    rw [map_mul, map_pow]
  have hg2 : toGerm d = toGerm b.1 ^ (m + 1) * toGerm c.1 := by
    rw [hddef, map_mul, map_pow]
  have hg3 : toGerm (b.1 ^ (m + 1)) = toGerm b.1 ^ (m + 1) := map_pow _ _ _
  have hg4 : toGerm (b.1 ^ (m + 1 + 1)) = toGerm b.1 ^ (m + 1 + 1) := map_pow _ _ _
  have hrewrite : powerRemainder b c (m + 1) γ
      = toGerm b.1 * powerRemainder b c m γ + ∑ β ∈ (T.erase γ).erase 0, f β := by
    rw [powerRemainder, hsum, hfγ, hf0, germAt_powerProduct_decomp b c m γ,
      powerRemainder, hg1, hg2, hg3, hg4]
    ring
  have hVpos : (0 : NatOrdinal) < ordinalValue b.1 := lt_trans zero_lt_one b.2
  have hWpos : (0 : NatOrdinal) < ordinalValue c.1 := lt_trans zero_lt_one c.2
  have hρpos : (0 : NatOrdinal) < b.residualValue :=
    pos_iff_ne_zero.mpr b.residualValue_ne_zero
  have hboundpos : (0 : NatOrdinal) < powerRemainderBound b c (m + 1) := by
    rw [powerRemainderBound]
    exact mul_pos (mul_pos (pow_pos hVpos (m + 1)) hρpos) hWpos
  rw [hrewrite]
  refine (germOrdinalValue_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · calc germOrdinalValue (toGerm b.1 * powerRemainder b c m γ)
        ≤ ordinalValue b.1 * germOrdinalValue (powerRemainder b c m γ) := by
          refine (germOrdinalValue_mul_le_naturalMul _ _).trans ?_
          rw [germOrdinalValue_toGerm]
      _ < ordinalValue b.1 * powerRemainderBound b c m :=
          mul_lt_mul_of_pos_left (hP' γ hγP hhigh) hVpos
      _ = powerRemainderBound b c (m + 1) := by
          rw [powerRemainderBound, powerRemainderBound]; ring
  · refine germOrdinalValue_sum_lt hboundpos fun β hβ ↦ ?_
    obtain ⟨hβ0, hβrest⟩ := Finset.mem_erase.mp hβ
    obtain ⟨hβγ, hβT⟩ := Finset.mem_erase.mp hβrest
    rw [hTdef, mem_convolutionIndex] at hβT
    have hβle : β ≤ 0 := hclosb hβT.1
    have hβneg : β < 0 := lt_of_le_of_ne hβle hβ0
    have hγβle : γ - β ≤ 0 := hclosd hβT.2
    have hγβ : γ < β := by
      rcases lt_or_eq_of_le (by linarith : γ ≤ β) with h | h
      · exact h
      · exact absurd h.symm hβγ
    obtain ⟨α, hα, hαle⟩ := hcutb β (hγb.trans hγβ) hβneg
    have hb₁ : germOrdinalValue (germAt (b.1 : K⟦ℝ⟧) β) ≤
        NatOrdinal.of (b.residualValue.val * α) := by
      rw [germAt_apply, toGerm_apply, germOrdinalValue_mk]
      simpa using NatOrdinal.of.le_iff_le.mpr hαle
    refine lt_of_le_of_lt ((germOrdinalValue_mul_le_naturalMul _ _).trans
      (mul_le_mul_left hb₁ _)) ?_
    exact hQ (γ - β) (by linarith) (by linarith) α hα

/-- Berarducci, Lemma 7.7 in the product-rule form used by Lemma 8.2: the germ of `b ^ (m + 1) * c`
at a sufficiently high negative cutoff differs from `(m + 1) * b^{|γ} b^m c + b^{m+1} c^{|γ}` by a
germ of ordinal value strictly below `v_J(b) ^ m ⊙ v_J^r(b) ⊙ v_J(c)`. -/
theorem exists_powerRemainder_lt
    (b c : SeriesWithOrdinalValueAboveOne K) (hp : b.principalValue ≤ c.principalValue) (m : ℕ) :
    ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      germOrdinalValue (powerRemainder b c m γ) < powerRemainderBound b c m := by
  induction m with
  | zero => exact exists_powerRemainder_lt_zero b c hp
  | succ m ih => exact powerRemainder_step b c hp m ih

end Berarducci
