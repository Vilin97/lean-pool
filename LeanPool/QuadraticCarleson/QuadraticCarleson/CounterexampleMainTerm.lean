/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleBohrPhase

/-!
# A finite dyadic main-term level set for the negative endpoint

The parameter `L` is the paper's base-two logarithm of `A`. We keep exactly
the half-open exponent windows `N * k + L ≤ n < N * k + L + N`, with `k` in
`paperBohrIndices N`. Natural ceilings implement those windows without any
rounding enlargement. The supremum is taken over the actual complex sums
`harmonicPhaseSum`, not over Bohr membership or an assumed operator estimate.

The full level set has an extended-real Lebesgue-measure lower bound. We
also give the real-valued measure bound after localization to `[0, N + 1]`,
which already contains the entire translated Bohr set. No finiteness of an
unlocalized level set is tacitly assumed. These are main-term estimates;
passing to the singular integral requires the separate analytic error bounds.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson


/-- The finite set of translate/exponent pairs in the exact dyadic windows. -/
noncomputable def paperMainTermIndices (N : ℕ) (L : ℝ) : Finset (ℤ × ℕ) :=
  (paperBohrIndices N).biUnion fun k =>
    ({k} : Finset ℤ) ×ˢ
      Finset.Ico ⌈(N : ℝ) * k + L⌉₊ ⌈(N : ℝ) * k + L + N⌉₊

@[simp] theorem mem_paperMainTermIndices {N : ℕ} {L : ℝ} {k : ℤ} {n : ℕ} :
    (k, n) ∈ paperMainTermIndices N L ↔
      k ∈ paperBohrIndices N ∧
      (N : ℝ) * k + L ≤ (n : ℝ) ∧
      (n : ℝ) < (N : ℝ) * k + L + N := by
  simp [paperMainTermIndices, Nat.ceil_le, Nat.lt_ceil]

/-- Distinct translate indices have disjoint exponent windows. Thus the
pair-indexed supremum does not introduce two truncations for one exponent. -/
theorem paperMainTermIndices_unique_translate {N n : ℕ} {L : ℝ} {k l : ℤ}
    (hN : 0 < N) (hk : (k, n) ∈ paperMainTermIndices N L)
    (hl : (l, n) ∈ paperMainTermIndices N L) : k = l := by
  obtain ⟨_, hklo, hkhi⟩ := mem_paperMainTermIndices.mp hk
  obtain ⟨_, hllo, hlhi⟩ := mem_paperMainTermIndices.mp hl
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · have hstep : (k : ℝ) + 1 ≤ l := by exact_mod_cast Int.add_one_le_iff.mpr hkl
    nlinarith
  · exact hkl
  · have hstep : (l : ℝ) + 1 ≤ k := by exact_mod_cast Int.add_one_le_iff.mpr hlk
    nlinarith

/-- The exact window recovers the truncation index by a floor. In particular,
the lower summation index `k + 1` is strictly above `(n - L) / N`, including
when that quotient is itself an integer. -/
theorem paperMainTermIndices_floor_eq {N n : ℕ} {L : ℝ} {k : ℤ}
    (hN : 0 < N) (hk : (k, n) ∈ paperMainTermIndices N L) :
    ⌊((n : ℝ) - L) / N⌋ = k := by
  obtain ⟨_, hnlo, hnhi⟩ := mem_paperMainTermIndices.mp hk
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hNr).mpr
    nlinarith
  · apply (div_lt_iff₀ hNr).mpr
    nlinarith

/-- Under the window-start assumption the exponents are at least two, hence
in particular positive as required by the paper's convention for `ℕ`. -/
theorem paperMainTermIndices_exponent_ge_two {N n : ℕ} {L : ℝ} {k : ℤ}
    (hL : 2 ≤ 3 * (N : ℝ) ^ 2 / 5 + L)
    (hk : (k, n) ∈ paperMainTermIndices N L) : 2 ≤ n := by
  obtain ⟨hk, hn, _⟩ := mem_paperMainTermIndices.mp hk
  have hklo := (mem_paperBohrIndices.mp hk).1
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hnreal : (2 : ℝ) ≤ n := by nlinarith
  exact_mod_cast hnreal

/-- The finite supremum of the nonnegative norms, with value zero for an
empty index set. Using `ℝ≥0` internally supplies this canonical empty value. -/
noncomputable def paperMainTermSup (N : ℕ) (L x : ℝ) : ℝ :=
  ↑((paperMainTermIndices N L).sup fun p =>
    ‖harmonicPhaseSum N p.1.toNat ((2 ^ p.2 : ℕ) : ℤ) (x - p.1)‖₊)

theorem paperMainTermSup_nonneg (N : ℕ) (L x : ℝ) : 0 ≤ paperMainTermSup N L x :=
  NNReal.coe_nonneg _

theorem norm_harmonicPhaseSum_le_paperMainTermSup {N n : ℕ} {L x : ℝ} {k : ℤ}
    (hk : (k, n) ∈ paperMainTermIndices N L) :
    ‖harmonicPhaseSum N k.toNat ((2 ^ n : ℕ) : ℤ) (x - k)‖ ≤
      paperMainTermSup N L x := by
  exact_mod_cast (Finset.le_sup (f := fun p : ℤ × ℕ =>
    ‖harmonicPhaseSum N p.1.toNat ((2 ^ p.2 : ℕ) : ℤ) (x - p.1)‖₊) hk)

/-- At an admissible translate the sum is literally evaluated at the ambient
point `x`: its denominator is `x - j` and its phase is `phase (2 * 2^n * j * x)`. -/
theorem harmonicPhaseSum_paperMainTerm_eq {N n : ℕ} {L x : ℝ} {k : ℤ}
    (hN : 100 ≤ N) (hk : (k, n) ∈ paperMainTermIndices N L) :
    harmonicPhaseSum N k.toNat ((2 ^ n : ℕ) : ℤ) (x - k) =
      (1 / (N : ℂ)) * ∑ j ∈ Finset.Icc (k.toNat + 1) N,
        phase (2 * (2 ^ n : ℝ) * j * x) / ((x - j : ℝ) : ℂ) := by
  have hkpos := paperBohrIndices_pos (by omega) (mem_paperMainTermIndices.mp hk).1
  have hkcastZ : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hkpos.le
  have hkcastR : (k.toNat : ℝ) = k := by exact_mod_cast hkcastZ
  simp [harmonicPhaseSum, hkcastR]

theorem measurable_paperMainTermSup (N : ℕ) (L : ℝ) :
    Measurable (paperMainTermSup N L) := by
  have hsum (p : ℤ × ℕ) : Measurable fun x : ℝ =>
      ‖harmonicPhaseSum N p.1.toNat ((2 ^ p.2 : ℕ) : ℤ) (x - p.1)‖₊ := by
    unfold harmonicPhaseSum phase
    fun_prop
  have hsup (s : Finset (ℤ × ℕ)) : Measurable fun x : ℝ =>
      s.sup fun p =>
        ‖harmonicPhaseSum N p.1.toNat ((2 ^ p.2 : ℕ) : ℤ) (x - p.1)‖₊ := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sup_empty] using
        (measurable_const : Measurable fun _ : ℝ => (⊥ : ℝ≥0))
    | @insert p s hp ih =>
      simp only [Finset.sup_insert]
      exact (hsum p).sup ih
  exact NNReal.continuous_coe.measurable.comp (hsup _)

/-- The genuine main-term level set: it has no Bohr condition. -/
def paperMainTermLevelSet (N : ℕ) (L a : ℝ) : Set ℝ :=
  {x | a ≤ paperMainTermSup N L x}

theorem measurableSet_paperMainTermLevelSet (N : ℕ) (L a : ℝ) :
    MeasurableSet (paperMainTermLevelSet N L a) :=
  measurableSet_le measurable_const (measurable_paperMainTermSup N L)

/-- A positive level is reached exactly when one of the finitely many actual
dyadic sums reaches it. -/
theorem mem_paperMainTermLevelSet_iff {N : ℕ} {L a x : ℝ} (ha : 0 < a) :
    x ∈ paperMainTermLevelSet N L a ↔
      ∃ (k : ℤ) (n : ℕ), (k, n) ∈ paperMainTermIndices N L ∧
        a ≤ ‖harmonicPhaseSum N k.toNat ((2 ^ n : ℕ) : ℤ) (x - k)‖ := by
  have hbot : (⊥ : ℝ≥0) < ⟨a, ha.le⟩ := ha
  change (⟨a, ha.le⟩ : ℝ≥0) ≤ (paperMainTermIndices N L).sup
    (fun p : ℤ × ℕ =>
      ‖harmonicPhaseSum N p.1.toNat ((2 ^ p.2 : ℕ) : ℤ) (x - p.1)‖₊) ↔ _
  have heq := @Finset.le_sup_iff (ℝ≥0) (ℤ × ℕ) _ _
    (paperMainTermIndices N L)
    (fun p : ℤ × ℕ =>
      ‖harmonicPhaseSum N p.1.toNat ((2 ^ p.2 : ℕ) : ℤ) (x - p.1)‖₊)
    ⟨a, ha.le⟩ hbot
  refine heq.trans ?_
  constructor
  · rintro ⟨⟨k, n⟩, hkn, hval⟩
    exact ⟨k, n, hkn, hval⟩
  · rintro ⟨k, n, hkn, hval⟩
    exact ⟨(k, n), hkn, hval⟩

theorem paperTranslatedBohrSet_subset_mainTermLevelSet {N : ℕ} {L : ℝ}
    (hN : 100 ≤ N) :
    paperTranslatedBohrSet N L ⊆
      paperMainTermLevelSet N L (Real.log N / (4 * N)) := by
  intro x hx
  obtain ⟨k, n, hk, hnlo, hnhi, _, hphase⟩ :=
    paperTranslatedBohrSet_phase_witness hN hx
  exact hphase.trans (norm_harmonicPhaseSum_le_paperMainTermSup
    (mem_paperMainTermIndices.mpr ⟨hk, hnlo, hnhi⟩))

/-- The translated Bohr set lies inside the bounded spatial interval used
below; no further restriction is imposed on the full supremum. -/
theorem paperTranslatedBohrSet_subset_Icc {N : ℕ} {L : ℝ} (hN : 100 ≤ N) :
    paperTranslatedBohrSet N L ⊆ Icc (0 : ℝ) ((N : ℝ) + 1) := by
  intro x hx
  obtain ⟨k, n, hk, _, _, hbohr, _⟩ := paperTranslatedBohrSet_phase_witness hN hx
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast paperBohrIndices_pos (by omega) hk
  have hkupper := (mem_paperBohrIndices.mp hk).2
  exact ⟨by linarith [hbohr.1.1], by linarith [hbohr.1.2]⟩

/-- The paper's explicit linear lower bound for the full main-term level set,
stated in extended-real Lebesgue measure so that no finiteness is assumed. -/
theorem paperMainTermLevelSet_volume_ge {N : ℕ} {L : ℝ}
    (hN : 100 ≤ N) (hL : 2 ≤ 3 * (N : ℝ) ^ 2 / 5 + L) :
    ENNReal.ofReal ((N : ℝ) / (30720 * ((2 : ℝ) ^ 100 + 1))) ≤
      volume (paperMainTermLevelSet N L (Real.log N / (4 * N))) := by
  have hfinite : volume (paperTranslatedBohrSet N L) ≠ ∞ :=
    measure_ne_top_of_subset (paperTranslatedBohrSet_subset_Icc hN) (by simp)
  calc
    _ ≤ ENNReal.ofReal (volume.real (paperTranslatedBohrSet N L)) :=
      ENNReal.ofReal_le_ofReal (paperTranslatedBohrSet_volume_real_ge (by omega) hL)
    _ = volume (paperTranslatedBohrSet N L) := ofReal_measureReal hfinite
    _ ≤ _ := measure_mono (paperTranslatedBohrSet_subset_mainTermLevelSet hN)

/-- The same linear bound in real-valued measure, already attained inside
`[0, N + 1]`. Its coefficient is `δ = 1 / (30720 * (2^100 + 1)) > 0`. -/
theorem paperMainTermLevelSet_local_volume_real_ge {N : ℕ} {L : ℝ}
    (hN : 100 ≤ N) (hL : 2 ≤ 3 * (N : ℝ) ^ 2 / 5 + L) :
    (N : ℝ) / (30720 * ((2 : ℝ) ^ 100 + 1)) ≤
      volume.real (Icc (0 : ℝ) ((N : ℝ) + 1) ∩
        paperMainTermLevelSet N L (Real.log N / (4 * N))) := by
  have hsub : paperTranslatedBohrSet N L ⊆
      Icc (0 : ℝ) ((N : ℝ) + 1) ∩
        paperMainTermLevelSet N L (Real.log N / (4 * N)) :=
    subset_inter (paperTranslatedBohrSet_subset_Icc hN)
      (paperTranslatedBohrSet_subset_mainTermLevelSet hN)
  have hfinite : volume (Icc (0 : ℝ) ((N : ℝ) + 1) ∩
      paperMainTermLevelSet N L (Real.log N / (4 * N))) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_left (by simp)
  exact (paperTranslatedBohrSet_volume_real_ge (by omega) hL).trans
    (measureReal_mono hsub hfinite)

end QuadraticCarleson
