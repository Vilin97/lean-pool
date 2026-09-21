/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.BohrUnion

/-!
# Integer translates of dyadic Bohr unions

This file formalizes the measure estimate for the paper's set `E_N`.
The general result permits any finite set of integer translates and any
logarithmic starting window depending on the translate. The specialization
to `3N/5 ≤ k ≤ 7N/10` is given using an exact finite index set.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson

/-- The translate `k + E`, written as a preimage under subtraction. -/
def integerTranslate (k : ℤ) (E : Set ℝ) : Set ℝ :=
  (fun x : ℝ => x - k) ⁻¹' E

theorem mem_integerTranslate_iff {k : ℤ} {E : Set ℝ} {x : ℝ} :
    x ∈ integerTranslate k E ↔ ∃ y ∈ E, x = (k : ℝ) + y := by
  constructor
  · intro hx
    exact ⟨x - k, hx, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [integerTranslate] using hy

theorem measurableSet_integerTranslate {k : ℤ} {E : Set ℝ}
    (hE : MeasurableSet E) : MeasurableSet (integerTranslate k E) :=
  hE.preimage (measurable_id.sub measurable_const)

@[simp]
theorem volume_integerTranslate (k : ℤ) (E : Set ℝ) :
    volume (integerTranslate k E) = volume E := by
  simp [integerTranslate, sub_eq_add_neg]

@[simp]
theorem volume_real_integerTranslate (k : ℤ) (E : Set ℝ) :
    volume.real (integerTranslate k E) = volume.real E := by
  simp [measureReal_def]

/-- Integer translates of sets supported in `[1/4,1/2)` do not overlap. -/
theorem integerTranslate_disjoint {k l : ℤ} {E F : Set ℝ}
    (hkl : k ≠ l) (hE : E ⊆ Ico (1 / 4 : ℝ) (1 / 2 : ℝ))
    (hF : F ⊆ Ico (1 / 4 : ℝ) (1 / 2 : ℝ)) :
    Disjoint (integerTranslate k E) (integerTranslate l F) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := hE hx
  have hy' := hF hy
  rcases lt_or_gt_of_ne hkl with hkl | hlk
  · have hkl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
    linarith [hx'.2, hy'.1]
  · have hlk' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hlk
    linarith [hy'.2, hx'.1]

/-- The translated pieces appearing in the definition of `E_N`. -/
def translatedDyadicBohrUnion (I : Finset ℤ) (M : ℤ → ℝ) (B c : ℝ) : Set ℝ :=
  ⋃ k ∈ I, integerTranslate k (dyadicBohrLogUnion (M k) B c)

theorem measurableSet_translatedDyadicBohrUnion
    (I : Finset ℤ) (M : ℤ → ℝ) (B c : ℝ) :
    MeasurableSet (translatedDyadicBohrUnion I M B c) :=
  Finset.measurableSet_biUnion _ fun _ _ =>
    measurableSet_integerTranslate (measurableSet_dyadicBohrLogUnion _ _ _)

/-- The measure of a finite union of these translates is exactly the sum
of the unshifted measures. -/
theorem translatedDyadicBohrUnion_volume_real_eq_sum
    (I : Finset ℤ) (M : ℤ → ℝ) (B c : ℝ) :
    volume.real (translatedDyadicBohrUnion I M B c) =
      ∑ k ∈ I, volume.real (dyadicBohrLogUnion (M k) B c) := by
  have hdisj : PairwiseDisjoint (↑I : Set ℤ)
      (fun k => integerTranslate k (dyadicBohrLogUnion (M k) B c)) := by
    intro k _ l _ hkl
    exact integerTranslate_disjoint hkl
      (dyadicBohrLogUnion_subset_Ico _ _ _) (dyadicBohrLogUnion_subset_Ico _ _ _)
  have hm : ∀ k ∈ I, MeasurableSet (integerTranslate k (dyadicBohrLogUnion (M k) B c)) :=
    fun _ _ => measurableSet_integerTranslate (measurableSet_dyadicBohrLogUnion _ _ _)
  have hf : ∀ k ∈ I, volume (integerTranslate k (dyadicBohrLogUnion (M k) B c)) ≠ ∞ := by
    intro k hk
    rw [volume_integerTranslate]
    exact measure_ne_top_of_subset (dyadicBohrLogUnion_subset_Ico _ _ _) (by simp)
  calc
    volume.real (translatedDyadicBohrUnion I M B c) =
        ∑ k ∈ I, volume.real (integerTranslate k (dyadicBohrLogUnion (M k) B c)) :=
      measureReal_biUnion_finset hdisj hm hf
    _ = ∑ k ∈ I, volume.real (dyadicBohrLogUnion (M k) B c) := by
      simp only [volume_real_integerTranslate]

/-- Quantitative measure lower bound, linear in the number of integer
indices, whenever each logarithmic window starts at least at exponent two. -/
theorem translatedDyadicBohrUnion_volume_real_ge
    (I : Finset ℤ) (M : ℤ → ℝ) {B c a : ℝ}
    (hM : ∀ k ∈ I, 2 ≤ M k) (hB : 1 ≤ B) (ha : 0 < a)
    (hac : a ≤ B * c) (hc : c < 1 / 10) :
    (I.card : ℝ) * (a / (1536 * (a + 1))) ≤
      volume.real (translatedDyadicBohrUnion I M B c) := by
  rw [translatedDyadicBohrUnion_volume_real_eq_sum]
  calc
    (I.card : ℝ) * (a / (1536 * (a + 1))) =
        ∑ _k ∈ I, a / (1536 * (a + 1)) := by simp
    _ ≤ ∑ k ∈ I, volume.real (dyadicBohrLogUnion (M k) B c) := by
      apply Finset.sum_le_sum
      intro k hk
      exact dyadicBohrLogUnion_volume_real_ge_uniform (hM k hk) hB ha hac hc

/-- The paper's index interval `[3N/5,7N/10]`, represented exactly using
integer ceiling and floor. For `N ≥ 20`, all these integers are positive. -/
noncomputable def paperBohrIndices (N : ℕ) : Finset ℤ :=
  Finset.Icc ⌈3 * (N : ℝ) / 5⌉ ⌊7 * (N : ℝ) / 10⌋

theorem mem_paperBohrIndices {N : ℕ} {k : ℤ} :
    k ∈ paperBohrIndices N ↔ 3 * (N : ℝ) / 5 ≤ k ∧ (k : ℝ) ≤ 7 * (N : ℝ) / 10 := by
  simp only [paperBohrIndices, Finset.mem_Icc, Int.ceil_le, Int.le_floor]

theorem paperBohrIndices_pos {N : ℕ} {k : ℤ} (hN : 20 ≤ N)
    (hk : k ∈ paperBohrIndices N) : 0 < k := by
  have hN' : (20 : ℝ) ≤ N := by exact_mod_cast hN
  have hk' := (mem_paperBohrIndices.mp hk).1
  have hk0 : (0 : ℝ) < k := by linarith
  exact_mod_cast hk0

/-- A concrete index count sufficient for the paper's `|E_N| ≳ N` estimate. -/
theorem paperBohrIndices_card_ge {N : ℕ} (hN : 20 ≤ N) :
    (N : ℝ) / 20 ≤ (paperBohrIndices N).card := by
  have hN' : (20 : ℝ) ≤ N := by exact_mod_cast hN
  have hl := Int.ceil_lt_add_one (3 * (N : ℝ) / 5)
  have hu := Int.lt_floor_add_one (7 * (N : ℝ) / 10)
  have hlu : ⌈3 * (N : ℝ) / 5⌉ ≤ ⌊7 * (N : ℝ) / 10⌋ + 1 := by
    have hlu' : (⌈3 * (N : ℝ) / 5⌉ : ℝ) ≤ (⌊7 * (N : ℝ) / 10⌋ : ℝ) + 1 := by
      linarith
    exact_mod_cast hlu'
  have hcard := Int.card_Icc_of_le (a := ⌈3 * (N : ℝ) / 5⌉)
    (b := ⌊7 * (N : ℝ) / 10⌋) hlu
  have hcard' := congrArg (fun z : ℤ => (z : ℝ)) hcard
  push_cast at hcard'
  change (N : ℝ) / 20 ≤ ((Finset.Icc ⌈3 * (N : ℝ) / 5⌉ ⌊7 * (N : ℝ) / 10⌋).card : ℝ)
  linarith

/-- The specialized linear estimate on the paper's index interval, still
allowing arbitrary logarithmic windows and any fixed lower bound on `Bc`. -/
theorem translatedDyadicBohrUnion_paperIndices_volume_real_ge
    {N : ℕ} (M : ℤ → ℝ) {B c a : ℝ}
    (hN : 20 ≤ N) (hM : ∀ k ∈ paperBohrIndices N, 2 ≤ M k)
    (hB : 1 ≤ B) (ha : 0 < a) (hac : a ≤ B * c) (hc : c < 1 / 10) :
    ((N : ℝ) / 20) * (a / (1536 * (a + 1))) ≤
      volume.real (translatedDyadicBohrUnion (paperBohrIndices N) M B c) := by
  calc
    ((N : ℝ) / 20) * (a / (1536 * (a + 1))) ≤
        ((paperBohrIndices N).card : ℝ) * (a / (1536 * (a + 1))) :=
      mul_le_mul_of_nonneg_right (paperBohrIndices_card_ge hN) (by positivity)
    _ ≤ volume.real (translatedDyadicBohrUnion (paperBohrIndices N) M B c) :=
      translatedDyadicBohrUnion_volume_real_ge _ M hM hB ha hac hc

/-- The paper's `E_N`, with `L` standing for its logarithm of `A`.
Keeping `L` explicit separates the measure argument from the later choice of `A`. -/
def paperTranslatedBohrSet (N : ℕ) (L : ℝ) : Set ℝ :=
  translatedDyadicBohrUnion (paperBohrIndices N)
    (fun k => (N : ℝ) * k + L) N (1 / ((2 : ℝ) ^ 100 * N))

/-- The explicit form of `|E_N| ≳ N` used in the negative endpoint proof.
The hypothesis on `L` says that even the first logarithmic window starts
at exponent two; it is enough to check this at the left endpoint `3N/5`. -/
theorem paperTranslatedBohrSet_volume_real_ge {N : ℕ} {L : ℝ}
    (hN : 20 ≤ N) (hL : 2 ≤ 3 * (N : ℝ) ^ 2 / 5 + L) :
    (N : ℝ) / (30720 * ((2 : ℝ) ^ 100 + 1)) ≤ volume.real (paperTranslatedBohrSet N L) := by
  have hN' : (20 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hM : ∀ k ∈ paperBohrIndices N, 2 ≤ (N : ℝ) * k + L := by
    intro k hk
    have hk' := (mem_paperBohrIndices.mp hk).1
    nlinarith [mul_le_mul_of_nonneg_left hk' hN0.le]
  have hc : (1 : ℝ) / ((2 : ℝ) ^ 100 * N) < 1 / 10 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hpow : (10 : ℝ) < 2 ^ 100 := by norm_num
    nlinarith
  have hac : (1 : ℝ) / 2 ^ 100 ≤ (N : ℝ) * (1 / ((2 : ℝ) ^ 100 * N)) := by
    apply le_of_eq
    field_simp
  have h := translatedDyadicBohrUnion_paperIndices_volume_real_ge
    (fun k => (N : ℝ) * k + L) hN hM (by linarith : (1 : ℝ) ≤ N)
    (by positivity : (0 : ℝ) < 1 / 2 ^ 100) hac hc
  change ((N : ℝ) / 20) * ((1 / (2 : ℝ) ^ 100) / (1536 * (1 / (2 : ℝ) ^ 100 + 1))) ≤
    volume.real (paperTranslatedBohrSet N L) at h
  calc
    (N : ℝ) / (30720 * ((2 : ℝ) ^ 100 + 1)) =
        ((N : ℝ) / 20) * ((1 / (2 : ℝ) ^ 100) / (1536 * (1 / (2 : ℝ) ^ 100 + 1))) := by
      field_simp
      ring
    _ ≤ volume.real (paperTranslatedBohrSet N L) := h

end QuadraticCarleson
