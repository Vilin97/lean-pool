/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.BlockLocalization

/-! # DegreeBookkeeping -/


open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Hermite1DimdLEAN

/-!
# DegreeBookkeeping

Finite degree intervals and support-width bounds on a fixed annulus.
Scaffolding notes: `ScaffoldingNotes/Blocks/degree_bookkeeping.md`.
-/

/-- Local degree support lies in an explicit interval. -/
theorem localDegreeInterval
    {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    (∀ n ∈ localDegreeSet j M G, degreeIntervalLower j M ≤ n ∧ n ≤ degreeIntervalUpper j M) ∧
      (localDegreeSet j M G).card ≤ degreeWidth j M := by
  /-
  Scaffolding guidance:
  keep the degree interval explicit and finite; later files need the support
  cardinality as a literal bound on Fourier support length.
  -/
  classical
  have hcoord_bounds :
      ∀ α ∈ localCoeffSet j M G, ∀ q : Fin d,
        (max (j q) M - M) ^ 2 ≤ α q ∧ α q ≤ (j q + M + 1) ^ 2 - 1 := by
    intro α hα q
    have hdist : blockDistance j (blockIndexMulti α) ≤ M := (Finset.mem_filter.mp hα).2
    have hqdist : Nat.dist (j q) (blockIndexMulti α q) ≤ M := by
      have hle : Nat.dist (j q) (blockIndexMulti α q) ≤ blockDistance j (blockIndexMulti α) := by
        dsimp [blockDistance]
        exact Finset.le_sup (s := Finset.univ)
          (f := fun q : Fin d => Nat.dist (j q) (blockIndexMulti α q)) (by simp)
      exact le_trans hle hdist
    have hidx_upper : blockIndexMulti α q ≤ j q + M := by
      have htri : blockIndexMulti α q ≤ j q + Nat.dist (blockIndexMulti α q) (j q) :=
        Nat.dist_tri_right' (blockIndexMulti α q) (j q)
      have hdist' : Nat.dist (blockIndexMulti α q) (j q) ≤ M := by
        simpa [Nat.dist_comm] using hqdist
      exact le_trans htri (Nat.add_le_add_left hdist' _)
    have hidx_lower : j q ≤ blockIndexMulti α q + M := by
      have htri : j q ≤ blockIndexMulti α q + Nat.dist (j q) (blockIndexMulti α q) :=
        Nat.dist_tri_right' (j q) (blockIndexMulti α q)
      exact le_trans htri (Nat.add_le_add_left hqdist _)
    constructor
    · by_cases hjm : j q ≤ M
      · simp [hjm]
      · have hjgt : M < j q := lt_of_not_ge hjm
        have hidx : j q - M ≤ blockIndexMulti α q := by
          omega
        have hsq : (j q - M) ^ 2 ≤ (blockIndexMulti α q) ^ 2 := by
          exact Nat.pow_le_pow_left hidx 2
        have hsqrt : (blockIndexMulti α q) ^ 2 ≤ α q := by
          simpa [blockIndexMulti, HermiteLEAN.blockIndex, pow_two] using Nat.sqrt_le' (α q)
        have hle : (j q - M) ^ 2 ≤ α q := hsq.trans hsqrt
        simpa [max_eq_left (le_of_lt hjgt)] using hle
    · have hlt : α q < (blockIndexMulti α q + 1) ^ 2 := by
        simpa [blockIndexMulti, HermiteLEAN.blockIndex, pow_two] using Nat.lt_succ_sqrt' (α q)
      have hmono : (blockIndexMulti α q + 1) ^ 2 ≤ (j q + M + 1) ^ 2 := by
        exact Nat.pow_le_pow_left (Nat.succ_le_succ hidx_upper) 2
      omega
  have hsubset :
      localDegreeSet j M G ⊆
        Finset.Icc (degreeIntervalLower j M) (degreeIntervalUpper j M) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨α, hα, rfl⟩
    have hsum_lower : degreeIntervalLower j M ≤ totalDegree α := by
      dsimp [degreeIntervalLower, totalDegree]
      exact Finset.sum_le_sum fun q _ => (hcoord_bounds α hα q).1
    have hsum_upper :
        totalDegree α ≤ ∑ q : Fin d, ((j q + M + 1) ^ 2 - 1) := by
      dsimp [totalDegree]
      exact Finset.sum_le_sum fun q _ => (hcoord_bounds α hα q).2
    have hsum_upper' : totalDegree α ≤ degreeIntervalUpper j M := by
      simpa [degreeIntervalUpper] using hsum_upper
    exact Finset.mem_Icc.mpr ⟨hsum_lower, hsum_upper'⟩
  have hcard :
      (localDegreeSet j M G).card ≤
        (Finset.Icc (degreeIntervalLower j M) (degreeIntervalUpper j M)).card :=
    Finset.card_le_card hsubset
  constructor
  · intro n hn
    exact Finset.mem_Icc.mp (hsubset hn)
  · have hIcc :
      (Finset.Icc (degreeIntervalLower j M) (degreeIntervalUpper j M)).card ≤ degreeWidth j M := by
      dsimp [degreeWidth]
      rw [Nat.card_Icc]
      omega
    exact le_trans hcard hIcc

/-- Crude bounds on the degree interval in terms of the annulus radius. -/
theorem degreeIntervalOrder
    {d : ℕ} (j : MultiIndex d) (M : ℕ) :
    degreeIntervalLower j M ≤ degreeIntervalUpper j M := by
  let R := annulusRadius j
  have hR : ∀ q : Fin d, j q ≤ R := by
    intro q
    dsimp [R, annulusRadius]
    exact Finset.le_sup (s := Finset.univ) (f := fun q : Fin d => j q) (by simp)
  have hcoord_order :
      ∀ q : Fin d, (max (j q) M - M) ^ 2 ≤ ((j q + M + 1) ^ 2 - 1) := by
    intro q
    have hmax : max (j q) M - M ≤ j q := by
      by_cases hjM : j q ≤ M
      · simp [max_eq_right hjM]
      · have hMj : M ≤ j q := le_of_lt (lt_of_not_ge hjM)
        simp [max_eq_left hMj]
    have hsquare : (max (j q) M - M) ^ 2 ≤ (j q) ^ 2 :=
      Nat.pow_le_pow_left hmax 2
    have hupper : (j q) ^ 2 ≤ ((j q + M + 1) ^ 2 - 1) := by
      have hstep : (j q) ^ 2 + 1 ≤ (j q + 1) ^ 2 := by
        ring_nf
        omega
      have hmono : (j q + 1) ^ 2 ≤ (j q + M + 1) ^ 2 := by
        exact Nat.pow_le_pow_left (by omega) 2
      omega
    exact hsquare.trans hupper
  have hinterval :
      degreeIntervalLower j M ≤ degreeIntervalUpper j M := by
    dsimp [degreeIntervalLower, degreeIntervalUpper]
    exact Finset.sum_le_sum fun q _ => hcoord_order q
  have hcoord_upper :
      ∀ q : Fin d, ((j q + M + 1) ^ 2 - 1) ≤ ((R + M + 1) ^ 2 - 1) := by
    intro q
    have hmono : j q + M + 1 ≤ R + M + 1 := by
      exact Nat.add_le_add_right (Nat.add_le_add_right (hR q) M) 1
    have hsquare : (j q + M + 1) ^ 2 ≤ (R + M + 1) ^ 2 :=
      Nat.pow_le_pow_left hmono 2
    omega
  have hupper_sum :
      degreeIntervalUpper j M ≤ d * (((R + M + 1) ^ 2) - 1) := by
    dsimp [degreeIntervalUpper]
    calc
      ∑ q : Fin d, ((j q + M + 1) ^ 2 - 1)
          ≤ ∑ q : Fin d, (((R + M + 1) ^ 2) - 1) := by
              exact Finset.sum_le_sum fun q _ => hcoord_upper q
      _ = d * (((R + M + 1) ^ 2) - 1) := by simp
  have hwidth_le_upper :
      degreeWidth j M ≤ degreeIntervalUpper j M + 1 := by
    dsimp [degreeWidth]
    omega
  have hwidth :
      degreeWidth j M ≤ d * ((R + M + 1) ^ 2 - 1) + 1 := by
    exact le_trans hwidth_le_upper (Nat.add_le_add_right hupper_sum 1)
  have hfinal :
      degreeWidth j M ≤ d * (R + M + 1) ^ 2 + 1 := by
    have hmul :
        d * ((R + M + 1) ^ 2 - 1) ≤ d * (R + M + 1) ^ 2 := by
      exact Nat.mul_le_mul_left d (Nat.sub_le _ _)
    exact le_trans hwidth (Nat.add_le_add_right hmul 1)
  exact hinterval

private theorem degreeWidth_le_upper_succ
    {d : ℕ} (j : MultiIndex d) (M : ℕ) :
    degreeWidth j M ≤ degreeIntervalUpper j M + 1 := by
  dsimp [degreeWidth]
  omega

/-- Low-annulus crude width bound in terms of the annulus radius. -/
theorem lowAnnulusDegreeWidthBound
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : annulusRadius j < M + 1) :
    degreeWidth j M ≤ d * (annulusRadius j + M + 1) ^ 2 := by
  let R := annulusRadius j
  have _ : annulusRadius j < M + 1 := hj
  have hcoord_upper :
      ∀ q : Fin d, ((j q + M + 1) ^ 2 - 1) ≤ ((R + M + 1) ^ 2 - 1) := by
    intro q
    have hqR : j q ≤ R := by
      dsimp [R, annulusRadius]
      exact Finset.le_sup (s := Finset.univ) (f := fun q : Fin d => j q) (by simp)
    have hmono : j q + M + 1 ≤ R + M + 1 := by
      omega
    have hsquare : (j q + M + 1) ^ 2 ≤ (R + M + 1) ^ 2 := Nat.pow_le_pow_left hmono 2
    omega
  have hupper_sum : degreeIntervalUpper j M ≤ d * (((R + M + 1) ^ 2) - 1) := by
    dsimp [degreeIntervalUpper]
    calc
      ∑ q : Fin d, ((j q + M + 1) ^ 2 - 1)
          ≤ ∑ q : Fin d, (((R + M + 1) ^ 2) - 1) := by
              exact Finset.sum_le_sum fun q _ => hcoord_upper q
      _ = d * (((R + M + 1) ^ 2) - 1) := by simp
  have hmain : degreeWidth j M ≤ d * (((R + M + 1) ^ 2) - 1) + 1 := by
    calc
      degreeWidth j M ≤ degreeIntervalUpper j M + 1 := degreeWidth_le_upper_succ j M
      _ ≤ d * (((R + M + 1) ^ 2) - 1) + 1 := Nat.add_le_add_right hupper_sum 1
  have hA : 1 ≤ (R + M + 1) ^ 2 := by
    have hbase : 0 < R + M + 1 := by
      omega
    exact Nat.succ_le_of_lt (Nat.pow_pos hbase)
  have hfinal : d * (((R + M + 1) ^ 2) - 1) + 1 ≤ d * (R + M + 1) ^ 2 := by
    calc
      d * (((R + M + 1) ^ 2) - 1) + 1 ≤ d * (((R + M + 1) ^ 2) - 1) + d := Nat.add_le_add_left hd _
      _ = d * (((R + M + 1) ^ 2) - 1) + d * 1 := by rw [Nat.mul_one]
      _ = d * ((((R + M + 1) ^ 2) - 1) + 1) := by rw [← Nat.mul_add]
      _ = d * (R + M + 1) ^ 2 := by rw [Nat.sub_add_cancel hA]
  exact le_trans hmain hfinal

/-- Uniform low-annulus width bound at the frozen threshold `J(d,M)`. -/
theorem uniformLowAnnulusWidthBound
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : annulusRadius j < degreeThreshold d M) :
    degreeWidth j M ≤ d * (degreeThreshold d M + M) ^ 2 := by
  let T := degreeThreshold d M
  have hcoord_upper :
      ∀ q : Fin d, ((j q + M + 1) ^ 2 - 1) ≤ ((T + M) ^ 2 - 1) := by
    intro q
    have hqR : j q ≤ annulusRadius j := by
      dsimp [annulusRadius]
      exact Finset.le_sup (s := Finset.univ) (f := fun q : Fin d => j q) (by simp)
    have hqT : j q + 1 ≤ T := by
      have : j q < T := lt_of_le_of_lt hqR (by simpa [T] using hj)
      exact Nat.succ_le_of_lt this
    have hmono : j q + M + 1 ≤ T + M := by
      omega
    have hsquare : (j q + M + 1) ^ 2 ≤ (T + M) ^ 2 := Nat.pow_le_pow_left hmono 2
    omega
  have hupper_sum : degreeIntervalUpper j M ≤ d * (((T + M) ^ 2) - 1) := by
    dsimp [degreeIntervalUpper]
    calc
      ∑ q : Fin d, ((j q + M + 1) ^ 2 - 1)
          ≤ ∑ q : Fin d, (((T + M) ^ 2) - 1) := by
              exact Finset.sum_le_sum fun q _ => hcoord_upper q
      _ = d * (((T + M) ^ 2) - 1) := by simp
  have hmain : degreeWidth j M ≤ d * (((T + M) ^ 2) - 1) + 1 := by
    calc
      degreeWidth j M ≤ degreeIntervalUpper j M + 1 := degreeWidth_le_upper_succ j M
      _ ≤ d * (((T + M) ^ 2) - 1) + 1 := Nat.add_le_add_right hupper_sum 1
  have hTpos : 0 < T := by
    unfold T degreeThreshold
    have hdpos : 0 < d := by omega
    have hodd : 0 < 2 * M + 1 := by omega
    have hprod : 0 < 120 * d * (2 * M + 1) := by
      exact Nat.mul_pos (Nat.mul_pos (by decide : 0 < 120) hdpos) hodd
    omega
  have hA : 1 ≤ (T + M) ^ 2 := by
    have hbase : 0 < T + M := by
      omega
    exact Nat.succ_le_of_lt (Nat.pow_pos hbase)
  have hfinal : d * (((T + M) ^ 2) - 1) + 1 ≤ d * (T + M) ^ 2 := by
    calc
      d * (((T + M) ^ 2) - 1) + 1 ≤ d * (((T + M) ^ 2) - 1) + d := Nat.add_le_add_left hd _
      _ = d * (((T + M) ^ 2) - 1) + d * 1 := by rw [Nat.mul_one]
      _ = d * ((((T + M) ^ 2) - 1) + 1) := by rw [← Nat.mul_add]
      _ = d * (T + M) ^ 2 := by rw [Nat.sub_add_cancel hA]
  exact le_trans hmain hfinal

private theorem annulusRadius_exists_coord
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) :
    ∃ q : Fin d, j q = annulusRadius j := by
  let q1 : Fin d := ⟨0, hd⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨q1, by simp⟩
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup
      (s := (Finset.univ : Finset (Fin d))) hne (f := fun q : Fin d => j q)
  exact ⟨q, hq.symm⟩

private theorem highAnnulusDegreeLowerBound
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : M + 1 ≤ annulusRadius j) :
    (annulusRadius j - M) ^ 2 ≤ degreeIntervalLower j M := by
  rcases annulusRadius_exists_coord (hd := hd) (j := j) with ⟨q0, hq0⟩
  have hsq : (max (annulusRadius j) M - M) ^ 2 = (annulusRadius j - M) ^ 2 := by
    rw [max_eq_left (by omega : M ≤ annulusRadius j)]
  dsimp [degreeIntervalLower]
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun q : Fin d => (max (j q) M - M) ^ 2) (by simp : q0 ∈ Finset.univ)]
  rw [hq0, hsq]
  omega

private theorem coordGapEqInt
    (n M : ℕ) (hMn : M ≤ n) :
    (((((n + M + 1) ^ 2 - 1) - (n - M) ^ 2 + 1 : ℕ) : ℤ)) =
      (2 * M + 1) * (2 * n + 1) := by
  have h1 : 1 ≤ (n + M + 1) ^ 2 := by
    exact Nat.succ_le_of_lt (Nat.pow_pos (by omega))
  have h2 : (n - M) ^ 2 ≤ (n + M + 1) ^ 2 - 1 := by
    have hklt : n - M < n + M + 1 := by
      omega
    have hsq : (n - M) ^ 2 < (n + M + 1) ^ 2 := by
      exact Nat.pow_lt_pow_left hklt (by decide : 2 ≠ 0)
    omega
  rw [Nat.cast_add, Int.ofNat_sub h2, Int.ofNat_sub h1]
  push_cast
  rw [Int.ofNat_sub hMn]
  ring_nf

private theorem coordGapMainLe
    (n M R : ℕ) (hMn : M ≤ n) (hnR : n ≤ R) :
    ((n + M + 1) ^ 2 - 1) - (n - M) ^ 2 + 1 ≤ (2 * M + 1) * (2 * R + 1) := by
  have hz :
      (((((n + M + 1) ^ 2 - 1) - (n - M) ^ 2 + 1 : ℕ) : ℤ)) ≤
        (2 * M + 1) * (2 * R + 1) := by
    rw [coordGapEqInt n M hMn]
    exact_mod_cast Nat.mul_le_mul_left (2 * M + 1) (by omega : 2 * n + 1 ≤ 2 * R + 1)
  exact_mod_cast hz

private theorem coordGapLe
    (n M R : ℕ) (hnR : n ≤ R) (hMR : M + 1 ≤ R) :
    ((n + M + 1) ^ 2 - 1) - (max n M - M) ^ 2 ≤ (2 * M + 1) * (2 * R + 1) := by
  by_cases h : n ≤ M
  · simp only [max_eq_right h, tsub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, tsub_zero, tsub_le_iff_right]
    have hsq : (n + M + 1) ^ 2 ≤ (2 * M + 1) ^ 2 := by
      refine Nat.pow_le_pow_left ?_ 2
      omega
    have hmul : (2 * M + 1) ^ 2 ≤ (2 * M + 1) * (2 * R + 1) := by
      simpa [pow_two] using
        Nat.mul_le_mul_left (2 * M + 1) (by omega : 2 * M + 1 ≤ 2 * R + 1)
    omega
  · have hMn : M ≤ n := by
      omega
    rw [max_eq_left hMn]
    have hmain := coordGapMainLe n M R hMn hnR
    exact le_trans (by omega) hmain

private theorem degreeWidth_eq_gap_sum
    {d : ℕ} (j : MultiIndex d) (M : ℕ) :
    degreeWidth j M =
      (∑ q : Fin d, (((j q + M + 1) ^ 2 - 1) - (max (j q) M - M) ^ 2)) + 1 := by
  dsimp [degreeWidth, degreeIntervalUpper, degreeIntervalLower]
  have hfg :
      ∀ x ∈ (Finset.univ : Finset (Fin d)),
        (max (j x) M - M) ^ 2 ≤ ((j x + M + 1) ^ 2 - 1) := by
    intro x hx
    by_cases h : j x ≤ M
    · simp [max_eq_right h]
    · have hMx : M ≤ j x := by
        omega
      rw [max_eq_left hMx]
      have hklt : j x - M < j x + M + 1 := by
        omega
      have hsq : (j x - M) ^ 2 < (j x + M + 1) ^ 2 := by
        exact Nat.pow_lt_pow_left hklt (by decide : 2 ≠ 0)
      omega
  have hdistrib :
      (∑ q : Fin d, (((j q + M + 1) ^ 2 - 1) - (max (j q) M - M) ^ 2)) =
        (∑ q : Fin d, ((j q + M + 1) ^ 2 - 1)) -
          (∑ q : Fin d, (max (j q) M - M) ^ 2) := by
    simpa using
      (Finset.sum_tsub_distrib (s := Finset.univ)
        (f := fun q : Fin d => ((j q + M + 1) ^ 2 - 1))
        (g := fun q : Fin d => (max (j q) M - M) ^ 2) hfg)
  rw [hdistrib]

/-- High-annulus crude degree lower/width upper bounds in terms of the annulus radius. -/
theorem highAnnulusDegreeBounds
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : M + 1 ≤ annulusRadius j) :
    (annulusRadius j - M) ^ 2 ≤ degreeIntervalLower j M ∧
      degreeWidth j M ≤ d * (2 * M + 1) * (2 * annulusRadius j + 1) := by
  let R := annulusRadius j
  let C := (2 * M + 1) * (2 * R + 1)
  have hMR : M + 1 ≤ R := by
    simpa [R] using hj
  have hlower : (annulusRadius j - M) ^ 2 ≤ degreeIntervalLower j M := by
    exact highAnnulusDegreeLowerBound (hd := hd) (j := j) (M := M) hj
  rcases annulusRadius_exists_coord (hd := hd) (j := j) with ⟨q0, hq0⟩
  have hR : ∀ q : Fin d, j q ≤ R := by
    intro q
    dsimp [R, annulusRadius]
    exact Finset.le_sup (s := Finset.univ) (f := fun q : Fin d => j q) (by simp)
  let gap : Fin d → ℕ := fun q =>
    (((j q + M + 1) ^ 2 - 1) - (max (j q) M - M) ^ 2)
  let gap' : Fin d → ℕ := fun q => if q = q0 then gap q + 1 else gap q
  have hgap'_eq : (∑ q : Fin d, gap' q) = (∑ q : Fin d, gap q) + 1 := by
    classical
    calc
      (∑ q : Fin d, gap' q)
          = ∑ q : Fin d, (gap q + if q = q0 then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              by_cases h : q = q0 <;> simp [gap', h]
      _ = (∑ q : Fin d, gap q) + ∑ q : Fin d, (if q = q0 then 1 else 0) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ q : Fin d, gap q) + 1 := by
            rw [Finset.sum_ite_eq' (s := Finset.univ) (a := q0) (b := fun _ => (1 : ℕ))]
            simp
  have hpointwise : ∀ q : Fin d, gap' q ≤ C := by
    intro q
    by_cases hqq : q = q0
    · subst hqq
      dsimp [gap', gap]
      rw [if_pos rfl, hq0, max_eq_left (by omega : M ≤ R)]
      exact coordGapMainLe R M R (by omega) le_rfl
    · dsimp [gap', gap]
      rw [if_neg hqq]
      exact coordGapLe (j q) M R (hR q) hMR
  have hwidth : degreeWidth j M ≤ d * C := by
    rw [degreeWidth_eq_gap_sum, ← hgap'_eq]
    calc
      (∑ q : Fin d, gap' q) ≤ ∑ q : Fin d, C := by
        exact Finset.sum_le_sum fun q _ => hpointwise q
      _ = d * C := by simp
  exact ⟨hlower, by simpa [C, R, Nat.mul_assoc] using hwidth⟩

/-- High-frequency threshold needed for the imported band estimate. -/
theorem highFrequencyThreshold
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : degreeThreshold d M ≤ annulusRadius j) :
    1343 * (degreeWidth j M) ^ 2 ≤ (degreeIntervalLower j M) ^ 2 := by
  /-
  Scaffolding guidance:
  prove this numerically once the crude growth estimates are frozen.
  The imported high-frequency theorem uses the exact constant `1343`.
  -/
  let R := annulusRadius j
  let x := R - M
  have hM1 : M + 1 ≤ degreeThreshold d M := by
    unfold degreeThreshold
    have hdpos : 0 < d := by
      omega
    have hodd : 0 < 2 * M + 1 := by
      omega
    have hprod : 0 < 120 * d * (2 * M + 1) := by
      exact Nat.mul_pos (Nat.mul_pos (by decide) hdpos) hodd
    omega
  have hhigh' : M + 1 ≤ annulusRadius j := le_trans hM1 hj
  have hhigh : M + 1 ≤ R := by
    simpa [R] using hhigh'
  rcases highAnnulusDegreeBounds (hd := hd) (j := j) (M := M) hhigh with ⟨hlower, hwidth⟩
  have hx_ge : 120 * d * (2 * M + 1) ≤ x := by
    dsimp [x, R]
    unfold degreeThreshold at hj
    omega
  have hM_bound : 2 * M + 1 ≤ x := by
    have h1 : 2 * M + 1 ≤ 120 * d * (2 * M + 1) := by
      nlinarith
    exact le_trans h1 hx_ge
  have hR_bound : 2 * R + 1 ≤ 3 * x := by
    dsimp [x]
    omega
  have h40base : 40 * d * (2 * M + 1) * (2 * R + 1) ≤ x * x := by
    have hstep1 :
        40 * d * (2 * M + 1) * (2 * R + 1) ≤ 40 * d * (2 * M + 1) * (3 * x) := by
      gcongr
    have hstep2 : 40 * d * (2 * M + 1) * (3 * x) = (120 * d * (2 * M + 1)) * x := by
      ring
    have hstep3 : (120 * d * (2 * M + 1)) * x ≤ x * x := by
      exact Nat.mul_le_mul_right x hx_ge
    calc
      40 * d * (2 * M + 1) * (2 * R + 1) ≤ 40 * d * (2 * M + 1) * (3 * x) := hstep1
      _ = (120 * d * (2 * M + 1)) * x := hstep2
      _ ≤ x * x := hstep3
  have h40 : 40 * degreeWidth j M ≤ x * x := by
    have hmul : 40 * degreeWidth j M ≤ 40 * (d * (2 * M + 1) * (2 * R + 1)) := by
      exact Nat.mul_le_mul_left 40 (by simpa [R] using hwidth)
    exact le_trans hmul (by simpa [mul_assoc] using h40base)
  have h1600 : 1600 * (degreeWidth j M) ^ 2 ≤ x ^ 4 := by
    have hsq := Nat.mul_self_le_mul_self h40
    simpa [pow_two, pow_succ, x, mul_assoc, mul_left_comm, mul_comm] using hsq
  have h1343 : 1343 * (degreeWidth j M) ^ 2 ≤ x ^ 4 := by
    exact le_trans (Nat.mul_le_mul_right ((degreeWidth j M) ^ 2) (by decide : 1343 ≤ 1600)) h1600
  have hlower_sq : x ^ 4 ≤ (degreeIntervalLower j M) ^ 2 := by
    have hsq := Nat.mul_self_le_mul_self (by simpa [x, R] using hlower)
    simpa [pow_two, pow_succ, x, mul_assoc, mul_left_comm, mul_comm] using hsq
  exact le_trans h1343 hlower_sq

/-- Zero-padding turns arbitrary finite support inside a band into a full band. -/
theorem zeroPaddingBand
    (N L : ℕ) (E : Finset ℕ) (b : ℕ → ℂ)
    (hE : ∀ n ∈ E, N ≤ n ∧ n < N + L) :
    ∃ c : Fin L → ℂ,
      positiveFrequencyPolynomial E b =
        bandLimitedPolynomial N L c := by
  /-
  Scaffolding guidance:
  this is the bridge from the finite degree set `S_j(G)` to the imported
  band-limited circle estimate.
  -/
  classical
  by_cases hL : L = 0
  · refine ⟨fun m => False.elim (by simpa [hL] using m.2), ?_⟩
    have hEempty : E = ∅ := by
      by_contra hne
      have hnonempty : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      rcases hnonempty with ⟨n, hn⟩
      obtain ⟨_, hlt⟩ := hE n hn
      omega
    subst hEempty
    subst hL
    ext t
    simp [positiveFrequencyPolynomial, bandLimitedPolynomial]
  · let c : Fin L → ℂ := fun m => if N + m.1 ∈ E then b (N + m.1) else 0
    refine ⟨c, ?_⟩
    ext t
    have hfilter :
        (∑ m : Fin L, (if N + m.1 ∈ E then b (N + m.1) else 0) *
          fourier ((N + m.1 : ℕ) : ℤ) t) =
        Finset.sum (Finset.univ.filter fun m : Fin L => N + m.1 ∈ E)
          (fun m => b (N + m.1) * fourier ((N + m.1 : ℕ) : ℤ) t) := by
      simp_rw [ite_mul, zero_mul]
      rw [← Finset.sum_filter]
    rw [positiveFrequencyPolynomial, bandLimitedPolynomial, hfilter]
    symm
    refine Finset.sum_bij (fun m hm => N + m.1) ?_ ?_ ?_ ?_
    · intro m hm
      simpa using (Finset.mem_filter.mp hm).2
    · intro m₁ hm₁ m₂ hm₂ hEq
      exact Fin.ext (Nat.add_left_cancel hEq)
    · intro n hn
      obtain ⟨hlo, hhi⟩ := hE n hn
      refine ⟨⟨n - N, by omega⟩, ?_, ?_⟩
      · simp [hlo, hn]
      · change N + (n - N) = n
        omega
    · intro a ha
      rfl

/-- Orthogonality to `ν_κ` removes zero from every local degree window. -/
theorem zeroFrequencyAbsent
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d)
    (horth : hermiteInnerNu κ G = 0) :
    0 ∉ localDegreeSet j M G := by
  /-
  Scaffolding guidance:
  this standalone lemma is what licenses the positive-frequency circle estimate
  on low annuli.
  -/
  classical
  have hcoeff0 : G.coeff 0 = 0 := (orthogonalToNu_iff_coeff_zero κ G).mp horth
  have hzero_support : (0 : MultiIndex d) ∉ G.support := by
    simpa [FiniteHermiteSum.support, Finsupp.mem_support_iff] using hcoeff0
  intro h0
  rcases Finset.mem_image.mp h0 with ⟨α, hαloc, hαdeg⟩
  have hcoord0 : ∀ q : Fin d, α q = 0 := by
    intro q
    have hle : α q ≤ totalDegree α := by
      dsimp [totalDegree]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
    omega
  have hαzero : α = 0 := by
    funext q
    exact hcoord0 q
  have hαsupp : α ∈ G.support := (Finset.mem_filter.mp hαloc).1
  exact hzero_support (hαzero ▸ hαsupp)

end Hermite1DimdLEAN
