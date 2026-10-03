/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.ScaleTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Finite HDot⁻¹ assembly for the nine named Section 5 terms and `R46`.
The exact residual identity is an explicit upstream input. Time measurability
of prefix norms is also kept explicit, while spatial L² closure is proved. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The ten source terms in the order used by `nineTerms`, followed by `R46`.
Out-of-range indices return zero for convenient finite-prefix notation. -/
def section5Term (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (i : ℕ) :
    ℝ → Vec 2 → ℝ :=
  match i with
  | 0 => fun t => cutoff1 I hΦ m κm T t
  | 1 => fun t => twistie1 I hΦ m κm T t
  | 2 => fun t => twistie3 I hΦ m κm T t
  | 3 => fun t => twistie4 I hΦ m κm T t
  | 4 => fun t => twistie5 I hΦ m κm T t
  | 5 => fun t => normie1 I hΦ m κm T t
  | 6 => fun t => normie2 I hΦ m κm T t
  | 7 => fun t => tiny I hΦ m κm d e t
  | 8 => fun t => normie3 I hΦ m κm T t
  | 9 => fun t => R46 I hΦ m κm T t
  | _ => fun _ _ => 0

/-- The pointwise sum of the first `n` named terms. -/
def section5Prefix (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (n : ℕ) :
    ℝ → Vec 2 → ℝ :=
  fun t x => ∑ i ∈ Finset.range n,
    section5Term I hΦ m κm T d e i t x

theorem section5Prefix_succ (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (n : ℕ) :
    section5Prefix I hΦ m κm T d e (n + 1) =
      fun t x => section5Prefix I hΦ m κm T d e n t x +
        section5Term I hΦ m κm T d e n t x := by
  funext t x
  simp [section5Prefix, Finset.sum_range_succ]

/-- Every finite prefix is spatially L² when its component terms are. -/
theorem section5Prefix_memL2 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2)
    (htermL2 : ∀ i, i < 10 → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      MemL2On unitCube (section5Term I hΦ m κm T d e i t))
    (n : ℕ) (hn : n ≤ 10) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    MemL2On unitCube (section5Prefix I hΦ m κm T d e n t) := by
  induction n generalizing t ht with
  | zero =>
      change MemLp (fun _ : Vec 2 => (0 : ℝ)) 2
        (volume.restrict unitCube)
      exact MemLp.zero
  | succ n ih =>
      have hn' : n ≤ 10 := by omega
      have hi : n < 10 := by omega
      rw [section5Prefix_succ I hΦ m κm T d e n]
      exact (ih hn' t ht).add (htermL2 n hi t ht)

/-- The ten-term prefix is exactly the residual sum `nineTerms + R46`. -/
theorem section5Prefix_ten_eq_terms (hΦ : IsStreamSeq I Φ) (m : ℕ)
    (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) :
    section5Prefix I hΦ m κm T d e 10 =
      fun t x => nineTerms I hΦ m κm T d e t x + R46 I hΦ m κm T t x := by
  funext t x
  simp [section5Prefix, section5Term, nineTerms, Finset.sum_range_succ]

/-- Triangle inequality for the first `n` terms in the exact BigBound time
norm. Inputs are component L² regularity and time measurability of the terms
and partial-prefix negative norms. -/
theorem timeHMinusOneNorm_section5Prefix_le_sum (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2)
    (htermL2 : ∀ i, i < 10 → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      MemL2On unitCube (section5Term I hΦ m κm T d e i t))
    (htermMeas : ∀ i, i < 10 →
      AEMeasurable
        (fun t => hMinusOneNorm (section5Term I hΦ m κm T d e i t))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (hprefixMeas : ∀ n, 1 ≤ n → n < 10 →
      AEMeasurable
        (fun t => hMinusOneNorm (section5Prefix I hΦ m κm T d e n t))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (n : ℕ) (hnpos : 1 ≤ n) (hn : n ≤ 10) :
    timeHMinusOneNorm (section5Prefix I hΦ m κm T d e n) ≤
      ∑ i ∈ Finset.range n,
        timeHMinusOneNorm (section5Term I hΦ m κm T d e i) := by
  revert hnpos hn
  induction n with
  | zero =>
      intro hnpos hn
      omega
  | succ n ih =>
      intro hnpos hn
      by_cases hn0 : n = 0
      · subst n
        have hprefix1 : section5Prefix I hΦ m κm T d e 1 =
            section5Term I hΦ m κm T d e 0 := by
          funext t x
          simp [section5Prefix, section5Term]
        rw [hprefix1]
        simp
      · have hnpos' : 1 ≤ n := by omega
        have hnlt : n < 10 := by omega
        have hprev := ih hnpos' (by omega)
        rw [section5Prefix_succ I hΦ m κm T d e n]
        calc
          timeHMinusOneNorm
              (fun t x => section5Prefix I hΦ m κm T d e n t x +
                section5Term I hΦ m κm T d e n t x)
              ≤ timeHMinusOneNorm (section5Prefix I hΦ m κm T d e n) +
                  timeHMinusOneNorm (section5Term I hΦ m κm T d e n) :=
                timeHMinusOneNorm_add_le
                  (fun t ht => section5Prefix_memL2 I hΦ m κm T d e
                    htermL2 n (by omega) t ht)
                  (htermL2 n hnlt)
                  (hprefixMeas n hnpos' hnlt)
                  (htermMeas n hnlt)
          _ ≤ _ := by
                simpa only [Finset.sum_range_succ] using add_le_add hprev le_rfl

end AVenhance.Infra.Section5
end
