/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwo.Identity

/-!
The below-two dual phase terminal gradient bound from the residual identity.
-/

open scoped BigOperators

namespace V7.Stage3BelowTwo

private lemma weightedSum_eq_sum_smul (m : ℕ) (a : ScalarSeq)
    (X : VectorSeq d) :
    weightedSum m a X = ∑ i ∈ Finset.range m, a i • X i := by
  ext j
  simp [weightedSum]

private lemma terminal_row (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
    (G r : VectorSeq d)
    (hr0 : r 0 = -(b n n) • G 0)
    (hr : ∀ k < n,
      r (k + 1) = r k -
        weightedSum (k + 2) (fun i => b (n - i) (n - 1 - k)) G) :
    r n = G n := by
  let T : ℕ → Point d := fun s =>
    weightedSum (s + 1) (fun i => b (n - i) (n - s)) G
  have hunroll : ∀ k ≤ n,
      r k = -(∑ s ∈ Finset.range (k + 1), T s) := by
    intro k hk
    induction k with
    | zero =>
      rw [hr0]
      have hzero : weightedSum 1 (fun i => b (n - i) n) G =
          b n n • G 0 := by
        ext j
        simp [weightedSum]
      have hsum0 : (∑ s ∈ Finset.range (0 + 1), T s) = T 0 := by simp
      rw [hsum0]
      dsimp [T]
      rw [hzero]
      rw [neg_smul]
    | succ k ih =>
      have hkn : k < n := by omega
      rw [hr k hkn, ih (by omega)]
      have hidx : n - 1 - k = n - (k + 1) := by omega
      rw [hidx]
      change -(∑ s ∈ Finset.range (k + 1), T s) - T (k + 1) =
        -(∑ s ∈ Finset.range (k + 2), T s)
      rw [Finset.sum_range_succ T (k + 1)]
      abel
  have hT : (∑ s ∈ Finset.range (n + 1), T s) = -(G n) := by
    calc
      (∑ s ∈ Finset.range (n + 1), T s) =
          ∑ s ∈ Finset.range (n + 1),
            ∑ i ∈ Finset.range (s + 1), b (n - i) (n - s) • G i := by
        apply Finset.sum_congr rfl
        intro s hs
        exact weightedSum_eq_sum_smul _ _ _
      _ = ∑ j ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (n - j + 1),
            b (j + l) j • G (n - (j + l)) := by
        rw [← Finset.sum_range_reflect
          (fun s => ∑ i ∈ Finset.range (s + 1),
            b (n - i) (n - s) • G i) (n + 1)]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < n + 1 := Finset.mem_range.mp hj
        have hjn : j ≤ n := by omega
        have hout : n + 1 - 1 - j = n - j := by omega
        rw [hout]
        have hcol : n - (n - j) = j := by omega
        rw [hcol]
        have href := Finset.sum_range_reflect
          (fun i => b (n - i) j • G i) (n - j + 1)
        rw [← href]
        apply Finset.sum_congr rfl
        intro l hl
        have hllt : l < n - j + 1 := Finset.mem_range.mp hl
        have hbidx : n - (n - j + 1 - 1 - l) = j + l := by omega
        have hGidx : n - j + 1 - 1 - l = n - (j + l) := by omega
        rw [hbidx, hGidx]
      _ = ∑ row ∈ Finset.range (n + 1),
          ∑ j ∈ Finset.range (row + 1), b row j • G (n - row) := by
        exact triangle_sum (fun row j => b row j • G (n - row)) n
      _ = -(G n) := by
        rw [Finset.sum_eq_single 0]
        · simp [hcoeff.2.2.2.2.1]
        · intro row hrow hrow0
          have hrowlt : row < n + 1 := Finset.mem_range.mp hrow
          have hrowpos : 0 < row := Nat.pos_of_ne_zero hrow0
          have hrs := hcoeff.2.2.2.2.2.2.2.2.2 (row - 1) (by omega)
          have hrowsize : row - 1 + 2 = row + 1 := by omega
          rw [hrowsize] at hrs
          have hroweq : row - 1 + 1 = row := by omega
          rw [hroweq] at hrs
          rw [← Finset.sum_smul]
          rw [hrs, zero_smul]
        · simp
  rw [hunroll n le_rfl, hT]
  simp

private lemma coefficient_u_pos (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b) :
    ∀ i ≤ n, 0 < u i := by
  intro i hi
  by_cases hin : i < n
  · rw [(hcoeff.2.2.2.2.2.1 i hin).1]
    positivity
  · have hieq : i = n := by omega
    rw [hieq, hcoeff.2.1, (hcoeff.2.2.2.2.2.1 (n - 1) (by omega)).1]
    positivity

private lemma coefficient_dw_and_det (n : ℕ)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b) :
    ∀ k < n,
      dw k = ((2 : ℝ) * k + 1) / 4 ∧
      u k - (dw k) ^ (2 : ℕ) = ((4 : ℝ) * k + 3) / 16 := by
  intro k hk
  have hkrow := hcoeff.2.2.2.2.2.1 k hk
  by_cases hk0 : k = 0
  · subst k
    have hd0 := hkrow.2.1
    simp only [] at hd0
    rw [hd0, hkrow.1]
    norm_num
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hpred : k - 1 < n := by omega
    have hkpred := hcoeff.2.2.2.2.2.1 (k - 1) hpred
    have hd := hkrow.2.1
    simp only [ite_eq_right hk0] at hd
    rw [hd, hkrow.1, hkpred.1]
    have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    rw [hkcast]
    constructor <;> ring

private lemma coefficient_X_representation (n : ℕ) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
    (B X : VectorSeq d) (hX : BelowXRecurrence n b B X) :
    ∀ k ≤ n, X k = weightedSum (k + 1) (c k) B := by
  intro k hk
  induction k with
  | zero =>
    rw [hX.1]
    ext j
    simp [weightedSum, hcoeff.2.2.2.1]
  | succ k ih =>
    have hkn : k < n := by omega
    rw [hX.2 k hkn, ih (by omega)]
    ext j
    simp only [weightedSum, Pi.sub_apply]
    have hsupport := hcoeff.2.2.2.2.2.2.2.2.1 k (by omega) (k + 1) (by omega)
    have hold : (∑ i ∈ Finset.range (k + 1), c k i * B i j) =
        ∑ i ∈ Finset.range (k + 2), c k i * B i j := by
      rw [Finset.sum_range_succ (fun i => c k i * B i j) (k + 1),
        hsupport, zero_mul, add_zero]
    rw [hold]
    apply Eq.symm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hb := (hcoeff.2.2.2.2.2.2.1 k hkn i).2
    rw [hb]
    ring

private lemma coefficient_X_weighted_step (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
    (B X : VectorSeq d) (hX : BelowXRecurrence n b B X) :
    ∀ k < n,
      u (k + 1) • X (k + 1) - u k • X k =
        dw (k + 1) • B (k + 1) + dw k • (B (k + 1) - B k) := by
  have hu_pos := coefficient_u_pos n hn u dw alpha c b hcoeff
  have hrep := coefficient_X_representation n u dw alpha c b hcoeff B X hX
  intro k hk
  rw [hrep k (by omega), hrep (k + 1) (by omega)]
  have hu : u (k + 1) ≠ 0 := ne_of_gt (hu_pos (k + 1) (by omega))
  ext j
  simp only [weightedSum, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsupport := hcoeff.2.2.2.2.2.2.2.2.1 k (by omega) (k + 1) (by omega)
  have hold : (∑ i ∈ Finset.range (k + 1), c k i * B i j) =
      ∑ i ∈ Finset.range (k + 2), c k i * B i j := by
    rw [Finset.sum_range_succ (fun i => c k i * B i j) (k + 1),
      hsupport, zero_mul, add_zero]
  rw [hold]
  have hc := hcoeff.2.2.2.2.2.2.1 k hk
  have hpoint : ∀ i ∈ Finset.range (k + 2),
      u (k + 1) * (c (k + 1) i * B i j) -
        u k * (c k i * B i j) =
      ((dw (k + 1) + dw k) * (if i = k + 1 then B i j else 0) -
        dw k * (if i = k then B i j else 0)) := by
    intro i hi
    have hci := (hc i).1
    field_simp [hu] at hci
    by_cases hi1 : i = k + 1 <;> by_cases hi0 : i = k
    · omega
    · subst i
      simp [] at hci ⊢
      linear_combination (B (k + 1) j) * hci
    · subst i
      simp [] at hci ⊢
      linear_combination (B k j) * hci
    · simp [hi1, hi0] at hci ⊢
      linear_combination (B i j) * hci
  have hsum := Finset.sum_congr rfl hpoint
  rw [Finset.sum_sub_distrib] at hsum
  have hrhs :
      (∑ i ∈ Finset.range (k + 2),
        ((dw (k + 1) + dw k) * (if i = k + 1 then B i j else 0) -
          dw k * (if i = k then B i j else 0))) =
      (dw (k + 1) + dw k) * B (k + 1) j - dw k * B k j := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_eq_single (k + 1)]
      · simp
      · intro i hi hne
        simp [hne]
      · simp
    · rw [Finset.sum_eq_single k]
      · simp
      · intro i hi hne
        simp [hne]
      · simp
  rw [hrhs] at hsum
  have hsize : k + 1 + 1 = k + 2 := by omega
  rw [hsize]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [hsum]
  ring

private lemma pairing_add_right (x y z : Point d) :
    O3.pairing x (y + z) = O3.pairing x y + O3.pairing x z := by
  simp [O3.pairing, Finset.sum_add_distrib, mul_add]

private lemma pairing_add_left (x y z : Point d) :
    O3.pairing (x + y) z = O3.pairing x z + O3.pairing y z := by
  simp [O3.pairing, Finset.sum_add_distrib, add_mul]

private lemma pairing_sub_left (x y z : Point d) :
    O3.pairing (x - y) z = O3.pairing x z - O3.pairing y z := by
  simp [O3.pairing, Finset.sum_sub_distrib, sub_mul]

private lemma pairing_sub_right (x y z : Point d) :
    O3.pairing x (y - z) = O3.pairing x y - O3.pairing x z := by
  simp [O3.pairing, Finset.sum_sub_distrib, mul_sub]

private lemma pairing_smul_left (r : ℝ) (x y : Point d) :
    O3.pairing (r • x) y = r * O3.pairing x y :=
  O3.Stage2RouteD.pairing_smul_left r x y

private lemma pairing_smul_right (r : ℝ) (x y : Point d) :
    O3.pairing x (r • y) = r * O3.pairing x y :=
  O3.Stage2RouteD.pairing_smul_right r x y

private lemma pairing_weightedSum_left (m : ℕ) (a : ScalarSeq)
    (X : VectorSeq d) (y : Point d) :
    O3.pairing (weightedSum m a X) y =
      ∑ i ∈ Finset.range m, a i * O3.pairing (X i) y := by
  induction m with
  | zero => simp [weightedSum, O3.pairing]
  | succ m ih =>
    have hsum : weightedSum (m + 1) a X =
        weightedSum m a X + a m • X m := by
      ext j
      simp [weightedSum, Finset.sum_range_succ]
    rw [hsum, pairing_add_left, ih, pairing_smul_left,
      Finset.sum_range_succ]

private lemma sum_pairing_by_parts (n : ℕ) (u : ScalarSeq)
    (A X : VectorSeq d) :
    (∑ k ∈ Finset.range (n + 1),
        u k * O3.pairing (A k - A (k + 1)) (X k)) =
      u 0 * O3.pairing (A 0) (X 0) +
        (∑ k ∈ Finset.range n,
          O3.pairing (A (k + 1))
            (u (k + 1) • X (k + 1) - u k • X k)) -
        u n * O3.pairing (A (n + 1)) (X n) := by
  induction n with
  | zero =>
    simp [pairing_sub_left]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    rw [pairing_sub_left, pairing_sub_right, pairing_smul_right,
      pairing_smul_right]
    ring

private lemma shifted_dw_pairing (n : ℕ) (dw : ScalarSeq)
    (A B : VectorSeq d) (hdwn : dw n = 0) :
    (∑ k ∈ Finset.range n,
      dw (k + 1) * O3.pairing (A (k + 1)) (B (k + 1))) =
    (∑ k ∈ Finset.range n, dw k * O3.pairing (A k) (B k)) -
      dw 0 * O3.pairing (A 0) (B 0) := by
  let f : ℕ → ℝ := fun k => dw k * O3.pairing (A k) (B k)
  have hshift := Finset.sum_range_succ' f n
  have hend : f n = 0 := by simp [f, hdwn]
  rw [Finset.sum_range_succ, hend, add_zero] at hshift
  dsimp [f] at hshift ⊢
  linarith

private lemma free_bilinear_reduction (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
    (A B X : VectorSeq d) (hAn : A (n + 1) = 0)
    (hX : BelowXRecurrence n b B X) :
    (∑ k ∈ Finset.range n,
        O3.pairing (weightedSum (k + 1) (alpha (k + 1)) A) (B (k + 1))) -
      (∑ k ∈ Finset.range (n + 1),
        u k * O3.pairing (A k - A (k + 1)) (X k)) =
    ∑ k ∈ Finset.range n,
      dw k * O3.pairing (A k - A (k + 1)) (B (k + 1) - B k) := by
  have hxstep := coefficient_X_weighted_step
    n hn u dw alpha c b hcoeff B X hX
  have hparts := sum_pairing_by_parts n u A X
  have hlast : u n * O3.pairing (A (n + 1)) (X n) = 0 := by
    rw [hAn]
    simp [O3.pairing]
  rw [hlast, sub_zero] at hparts
  have hu0 : u 0 = dw 0 := by
    have hd0 := (hcoeff.2.2.2.2.2.1 0 (by omega)).2.1
    simpa using hd0.symm
  have halpha :
      (∑ k ∈ Finset.range n,
        O3.pairing (weightedSum (k + 1) (alpha (k + 1)) A) (B (k + 1))) =
      ∑ k ∈ Finset.range n,
        dw k * O3.pairing (A k) (B (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn := Finset.mem_range.mp hk
    rw [alpha_weighted_primal n u dw alpha c b hcoeff A k hkn,
      pairing_smul_left]
  have hstep_sum :
      (∑ k ∈ Finset.range n,
        O3.pairing (A (k + 1))
          (u (k + 1) • X (k + 1) - u k • X k)) =
      (∑ k ∈ Finset.range n,
        dw (k + 1) * O3.pairing (A (k + 1)) (B (k + 1))) +
      ∑ k ∈ Finset.range n,
        dw k * (O3.pairing (A (k + 1)) (B (k + 1)) -
          O3.pairing (A (k + 1)) (B k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn := Finset.mem_range.mp hk
    rw [hxstep k hkn, pairing_add_right, pairing_smul_right,
      pairing_smul_right, pairing_sub_right]
  have hshift := shifted_dw_pairing n dw A B hcoeff.2.2.1
  rw [halpha, hparts, hstep_sum, hshift, hu0]
  rw [hX.1]
  have hrhs :
      (∑ k ∈ Finset.range n,
        dw k * O3.pairing (A k - A (k + 1)) (B (k + 1) - B k)) =
      ((∑ k ∈ Finset.range n,
          dw k * O3.pairing (A k) (B (k + 1))) -
        (∑ k ∈ Finset.range n,
          dw k * O3.pairing (A k) (B k))) -
        (∑ k ∈ Finset.range n,
          dw k * (O3.pairing (A (k + 1)) (B (k + 1)) -
            O3.pairing (A (k + 1)) (B k))) := by
    simp_rw [pairing_sub_left, pairing_sub_right]
    repeat' rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hrhs]
  ring

private lemma free_primal_residual_nonneg (p : ℝ) (hp : 1 < p)
    (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
    (A B X : VectorSeq d) (hAn : A (n + 1) = 0)
    (hX : BelowXRecurrence n b B X) :
    0 ≤ BelowPrimalResidual p n u dw alpha A B X
      (fun y => (1 / 2) * (lpNorm p y) ^ (2 : ℕ)) := by
  have hbil := free_bilinear_reduction
    n hn u dw alpha c b hcoeff A B X hAn hX
  unfold BelowPrimalResidual
  change 0 ≤ ((
    (∑ k ∈ Finset.range n,
      (u k / 2) * (lpNorm (conjugateExponent p) (A k - A (k + 1))) ^ (2 : ℕ)) +
    (∑ k ∈ Finset.range n,
      (1 / 2) * (lpNorm p (B k - B (k + 1))) ^ (2 : ℕ)) +
    (∑ k ∈ Finset.range n,
      O3.pairing (weightedSum (k + 1) (alpha (k + 1)) A) (B (k + 1)))) -
    (∑ k ∈ Finset.range (n + 1),
      u k * O3.pairing (A k - A (k + 1)) (X k)))
  rw [show ∀ a b c e : ℝ, (a + b + c) - e = a + b + (c - e) by
    intro a b c e; ring]
  rw [hbil]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro k hk
  have hkn := Finset.mem_range.mp hk
  let GX := lpNorm (conjugateExponent p) (A k - A (k + 1))
  let BY := lpNorm p (B (k + 1) - B k)
  have hGX : 0 ≤ GX := O3.lpNorm_nonneg _ _
  have hBY : 0 ≤ BY := O3.lpNorm_nonneg _ _
  have hdform := (coefficient_dw_and_det n u dw alpha c b hcoeff k hkn)
  have hd : 0 ≤ dw k := by rw [hdform.1]; positivity
  have hdet : 0 ≤ u k - (dw k) ^ (2 : ℕ) := by rw [hdform.2]; positivity
  have hholder := O3.abs_pairing_le_lpNorm_mul
    (O3.holderConjugate_conjugateExponent hp).symm
    (A k - A (k + 1)) (B (k + 1) - B k)
  have hpair : -GX * BY ≤
      O3.pairing (A k - A (k + 1)) (B (k + 1) - B k) := by
    have hraw := neg_le_of_abs_le hholder
    dsimp [GX, BY] at ⊢
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hpair hd
  have hpsd : 0 ≤ u k * GX ^ (2 : ℕ) + BY ^ (2 : ℕ) -
      2 * dw k * GX * BY := by
    nlinarith [sq_nonneg (dw k * GX - BY),
      mul_nonneg hdet (sq_nonneg GX)]
  have hnormsym : lpNorm p (B k - B (k + 1)) = BY := by
    dsimp [BY]
    rw [show B k - B (k + 1) = -(B (k + 1) - B k) by abel]
    change O3.lpNorm p (-(B (k + 1) - B k)) =
      O3.lpNorm p (B (k + 1) - B k)
    exact O3.lpNorm_neg p _
  change 0 ≤ u k / 2 * GX ^ (2 : ℕ) +
    1 / 2 * (lpNorm p (B k - B (k + 1))) ^ (2 : ℕ) +
    dw k * O3.pairing (A k - A (k + 1)) (B (k + 1) - B k)
  rw [hnormsym]
  nlinarith

private noncomputable def freeX (b : ScalarMatrix) (B : VectorSeq d) : VectorSeq d :=
  fun k => Nat.rec (B 0)
    (fun j previous => previous - weightedSum (j + 2) (b (j + 1)) B) k

private lemma freeX_recurrence (n : ℕ) (b : ScalarMatrix) (B : VectorSeq d) :
    BelowXRecurrence n b B (freeX b B) := by
  constructor
  · rfl
  · intro k hk
    rfl

private lemma dual_residual_nonneg (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
    (C D : VectorSeq d) :
    0 ≤ BelowDualResidual p n u alpha b C D
      (fun y => (1 / 2) * (lpNorm p y) ^ (2 : ℕ)) := by
  have hid := belowPointwiseResidualIdentity p hp hp2 d n hn
    u dw alpha c b (fun y => (1 / 2) * (lpNorm p y) ^ (2 : ℕ))
    hcoeff (by
      intro x
      dsimp
      change (1 / 2) * (O3.lpNorm p (-x)) ^ (2 : ℕ) =
        (1 / 2) * (O3.lpNorm p x) ^ (2 : ℕ)
      rw [O3.lpNorm_neg])
  obtain ⟨A, B, hmap⟩ := hid.2.1 C D
  let A' : VectorSeq d := fun i => if i ≤ n then A i else 0
  have hmap' : BelowResidualMap n u A' B C D := by
    refine ⟨?_, ?_, hmap.2.2⟩
    · dsimp [A']
      rw [ite_eq_left le_rfl]
      exact hmap.1
    · intro i hi
      dsimp [A']
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      exact hmap.2.1 i hi
  have hAn : A' (n + 1) = 0 := by simp [A']
  have hX := freeX_recurrence n b B
  have heq := hid.2.2.2.2 A' B C D (freeX b B) hAn hX hmap'
  rw [← heq]
  exact free_primal_residual_nonneg p hp n hn u dw alpha c b hcoeff
    A' B (freeX b B) hAn hX

private lemma sum_succ_sub {E : Type*} [AddCommGroup E] (n : ℕ) (f : ℕ → E) :
    (∑ k ∈ Finset.range n, (f (k + 1) - f k)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    abel

private lemma shifted_pairing_telescope (q : VectorSeq d) (g : Point d)
    (j m : ℕ) :
    (∑ l ∈ Finset.range m,
      O3.pairing g (q (j + l) - q (j + l + 1))) =
      O3.pairing g (q j - q (j + m)) := by
  induction m with
  | zero => simp [O3.pairing]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [pairing_sub_right]
    have hidx : j + (m + 1) = j + m + 1 := by omega
    rw [hidx]
    ring

private lemma dualP_pairing_path (n : ℕ) (hn : 1 ≤ n)
    (u : ScalarSeq) (G q : VectorSeq d) :
    (∑ k ∈ Finset.range n,
      O3.pairing (dualP n u G k) (q k - q (k + 1))) =
    (∑ k ∈ Finset.range n,
      (1 / u (n - (k + 1))) *
        O3.pairing (G (k + 1)) (q k - q (k + 1))) -
    ∑ j ∈ Finset.range n,
      (1 / u (n - (j + 1)) - 1 / u (n - j)) *
        O3.pairing (G j) (q j - q n) := by
  let delta : ScalarSeq := fun j =>
    1 / u (n - (j + 1)) - 1 / u (n - j)
  have hexpand :
      (∑ k ∈ Finset.range n,
        O3.pairing (dualP n u G k) (q k - q (k + 1))) =
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1))) *
          O3.pairing (G (k + 1)) (q k - q (k + 1))) -
      ∑ k ∈ Finset.range n,
        ∑ j ∈ Finset.range (k + 1),
          delta j * O3.pairing (G j) (q k - q (k + 1)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [dualP, pairing_sub_left, pairing_smul_left,
      pairing_weightedSum_left]
  rw [hexpand]
  congr 1
  have htri := triangle_sum
    (fun k j => delta j * O3.pairing (G j) (q k - q (k + 1))) (n - 1)
  have hnsize : n - 1 + 1 = n := by omega
  rw [hnsize] at htri
  rw [← htri]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  rw [← Finset.mul_sum]
  have ht := shifted_pairing_telescope q (G j) j (n - j)
  have hend : j + (n - j) = n := by omega
  rw [hend] at ht
  have hsize : n - 1 - j + 1 = n - j := by omega
  rw [hsize]
  rw [ht]

private lemma function_value_cancel (n : ℕ) (w F : ScalarSeq) :
    w 0 * (F 0 - F n) -
      (∑ k ∈ Finset.range n, (w (k + 1) - w k) * (F n - F k)) -
      (∑ k ∈ Finset.range n, w (k + 1) * (F k - F (k + 1))) = 0 := by
  have hdelta := sum_succ_sub n w
  have hshift :
      (∑ k ∈ Finset.range n, w (k + 1) * F (k + 1)) =
      (∑ k ∈ Finset.range n, w k * F k) - w 0 * F 0 + w n * F n := by
    let f : ℕ → ℝ := fun k => w k * F k
    have h := Finset.sum_range_succ' f n
    have h' := Finset.sum_range_succ f n
    dsimp [f] at h h' ⊢
    linarith
  have hdeltaF :
      (∑ k ∈ Finset.range n, (w (k + 1) - w k) * F k) =
      (∑ k ∈ Finset.range n, w (k + 1) * F k) -
        ∑ k ∈ Finset.range n, w k * F k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hlast :
      (∑ k ∈ Finset.range n, w (k + 1) * (F k - F (k + 1))) =
      (∑ k ∈ Finset.range n, w (k + 1) * F k) -
        ∑ k ∈ Finset.range n, w (k + 1) * F (k + 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hmid :
      (∑ k ∈ Finset.range n, (w (k + 1) - w k) * (F n - F k)) =
      F n * (w n - w 0) -
        ((∑ k ∈ Finset.range n, w (k + 1) * F k) -
          ∑ k ∈ Finset.range n, w k * F k) := by
    rw [← hdelta, ← hdeltaF]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hmid, hlast, hshift]
  ring

private lemma function_block_identity (n : ℕ) (hn : 1 ≤ n)
    (u : ScalarSeq) (alpha : ScalarMatrix)
    (oracle : PairOracle d) (G q Z : VectorSeq d)
    (hG : ∀ k ≤ n, G k = oracle.gradient (q k))
    (hq : ∀ k < n,
      q (k + 1) = q k -
        weightedSum (k + 1) (fun i => alpha (n - i) (n - 1 - k)) Z) :
    (∑ k ∈ Finset.range n,
      O3.pairing (dualP n u G k)
        (weightedSum (k + 1) (fun i => alpha (n - i) (n - 1 - k)) Z)) =
    (1 / u n) * (oracle.value (q 0) - oracle.value (q n)) -
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1)) - 1 / u (n - k)) *
          FunctionBregman oracle.value oracle.gradient (q n) (q k)) -
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1))) *
          FunctionBregman oracle.value oracle.gradient (q k) (q (k + 1))) := by
  have hQ : ∀ k < n,
      weightedSum (k + 1) (fun i => alpha (n - i) (n - 1 - k)) Z =
        q k - q (k + 1) := by
    intro k hk
    rw [hq k hk]
    abel
  have hpath := dualP_pairing_path n hn u G q
  have hleft :
      (∑ k ∈ Finset.range n,
        O3.pairing (dualP n u G k)
          (weightedSum (k + 1) (fun i => alpha (n - i) (n - 1 - k)) Z)) =
      ∑ k ∈ Finset.range n,
        O3.pairing (dualP n u G k) (q k - q (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hQ k (Finset.mem_range.mp hk)]
  rw [hleft, hpath]
  let w : ScalarSeq := fun k => 1 / u (n - k)
  let F : ScalarSeq := fun k => oracle.value (q k)
  have hcancel := function_value_cancel n w F
  dsimp [w, F] at hcancel
  have hrem1 :
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1)) - 1 / u (n - k)) *
          (oracle.value (q n) - oracle.value (q k) -
            pairing (oracle.gradient (q k)) (q n - q k))) =
      ∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1)) - 1 / u (n - k)) *
          (oracle.value (q n) - oracle.value (q k) -
            pairing (G k) (q n - q k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    rw [hG k (by omega)]
  have hrem2 :
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1))) *
          (oracle.value (q k) - oracle.value (q (k + 1)) -
            pairing (oracle.gradient (q (k + 1))) (q k - q (k + 1)))) =
      ∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1))) *
          (oracle.value (q k) - oracle.value (q (k + 1)) -
            pairing (G (k + 1)) (q k - q (k + 1))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    rw [hG (k + 1) (by omega)]
  have hflip :
      (∑ j ∈ Finset.range n,
        (1 / u (n - (j + 1)) - 1 / u (n - j)) *
          O3.pairing (G j) (q j - q n)) =
      -(∑ j ∈ Finset.range n,
        (1 / u (n - (j + 1)) - 1 / u (n - j)) *
          O3.pairing (G j) (q n - q j)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [pairing_sub_right]
    ring
  have hdec1 :
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1)) - 1 / u (n - k)) *
          (oracle.value (q n) - oracle.value (q k) -
            pairing (G k) (q n - q k))) =
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1)) - 1 / u (n - k)) *
          (oracle.value (q n) - oracle.value (q k))) -
      ∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1)) - 1 / u (n - k)) *
          pairing (G k) (q n - q k) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hdec2 :
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1))) *
          (oracle.value (q k) - oracle.value (q (k + 1)) -
            pairing (G (k + 1)) (q k - q (k + 1)))) =
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1))) *
          (oracle.value (q k) - oracle.value (q (k + 1)))) -
      ∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1))) *
          pairing (G (k + 1)) (q k - q (k + 1)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  unfold FunctionBregman
  rw [hrem1, hrem2, hflip, hdec1, hdec2]
  linarith

private lemma belowHstar_zero (p : ℝ) (hp : 1 < p) (d : ℕ) :
    belowHstar p (0 : Point d) = 0 := by
  rw [belowHstar, show lpNorm (conjugateExponent p) (0 : Point d) = 0 by
    change O3.lpNorm (O3.conjugateExponent p) 0 = 0
    exact O3.lpNorm_zero (lt_trans zero_lt_one (O3.one_lt_conjugateExponent hp))]
  ring

private lemma mirror_block_identity (p : ℝ) (hp : 1 < p) (n : ℕ)
     (b : ScalarMatrix) (G r : VectorSeq d)
    (hr0 : r 0 = -(b n n) • G 0)
    (hr : ∀ k < n,
      r (k + 1) = r k -
        weightedSum (k + 2) (fun i => b (n - i) (n - 1 - k)) G) :
    let Z : VectorSeq d := fun i => belowMirrorMap p (r i)
    (∑ k ∈ Finset.range (n + 1),
      O3.pairing
        (weightedSum (k + 1) (fun i => b (n - i) (n - k)) G) (Z k)) =
      -(∑ k ∈ Finset.range n,
        FunctionBregman (belowHstar p) (belowMirrorMap p) (r k) (r (k + 1))) -
      belowHstar p (r n) -
      FunctionBregman (belowHstar p) (belowMirrorMap p) 0 (r 0) := by
  dsimp
  let Z : VectorSeq d := fun i => belowMirrorMap p (r i)
  have hrow0 : weightedSum 1 (fun i => b (n - i) (n - 0)) G = -(r 0) := by
    rw [hr0]
    ext j
    simp [weightedSum]
  have hrow : ∀ k, 0 < k → k ≤ n →
      weightedSum (k + 1) (fun i => b (n - i) (n - k)) G =
        r (k - 1) - r k := by
    intro k hk0 hkn
    have hu := hr (k - 1) (by omega)
    have hidx₁ : k - 1 + 1 = k := by omega
    have hidx₂ : k - 1 + 2 = k + 1 := by omega
    have hidx₃ : n - 1 - (k - 1) = n - k := by omega
    rw [hidx₁, hidx₂, hidx₃] at hu
    rw [hu]
    abel
  have hrowsum :
      (∑ k ∈ Finset.range (n + 1),
        O3.pairing
          (weightedSum (k + 1) (fun i => b (n - i) (n - k)) G) (Z k)) =
      -O3.pairing (r 0) (Z 0) +
        ∑ k ∈ Finset.range n,
          O3.pairing (r k - r (k + 1)) (Z (k + 1)) := by
    rw [Finset.sum_range_succ']
    rw [hrow0]
    have hneg : O3.pairing (-(r 0)) (Z 0) = -O3.pairing (r 0) (Z 0) := by
      simp [O3.pairing, Finset.sum_neg_distrib]
    rw [hneg]
    have hsums :
        (∑ k ∈ Finset.range n,
          O3.pairing
            (weightedSum (k + 1 + 1) (fun i => b (n - i) (n - (k + 1))) G)
            (Z (k + 1))) =
        ∑ k ∈ Finset.range n,
          O3.pairing (r k - r (k + 1)) (Z (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      rw [hrow (k + 1) (by omega) (by omega)]
      simp only [Nat.succ_sub_one]
    rw [hsums]
    abel
  rw [hrowsum]
  unfold FunctionBregman
  have htel := sum_succ_sub n (fun k => belowHstar p (r k))
  have hpair :
      (∑ k ∈ Finset.range n,
        O3.pairing (belowMirrorMap p (r (k + 1))) (r k - r (k + 1))) =
      ∑ k ∈ Finset.range n,
        O3.pairing (r k - r (k + 1)) (Z (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [O3.pairing_comm]
  dsimp [Z] at hpair ⊢
  rw [← hpair, belowHstar_zero p hp]
  rw [Finset.sum_sub_distrib]
  have hfun :
      (∑ k ∈ Finset.range n,
        (belowHstar p (r k) - belowHstar p (r (k + 1)))) =
      belowHstar p (r 0) - belowHstar p (r n) := by
    have hneg := congrArg Neg.neg htel
    rw [← Finset.sum_neg_distrib] at hneg
    simpa only [neg_sub] using hneg
  rw [hfun]
  have hbasepair : pairing (belowMirrorMap p (r 0)) (-r 0) =
      -O3.pairing (r 0) (belowMirrorMap p (r 0)) := by
    rw [O3.pairing_comm]
    simp [O3.pairing]
  simp only [zero_sub]
  rw [hbasepair]
  ring

private lemma coefficient_u_mono (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b) :
    ∀ i < n, u i ≤ u (i + 1) := by
  intro i hi
  by_cases hisucc : i + 1 < n
  · rw [(hcoeff.2.2.2.2.2.1 i hi).1,
      (hcoeff.2.2.2.2.2.1 (i + 1) hisucc).1]
    push_cast
    have hi0 : (0 : ℝ) ≤ i := by positivity
    nlinarith
  · have hieq : i + 1 = n := by omega
    rw [hieq, hcoeff.2.1]
    have hipred : n - 1 = i := by omega
    rw [hipred]

end V7.Stage3BelowTwo

namespace V7

theorem belowTerminalGradient : BelowTerminalGradientStatement := by
  intro p hp hp2 d n data hass
  rcases hass with
    ⟨hdyn, hconv, hcoord, hbdd, hcoeff, htrace, hlen, hqueried,
      hG, hr0, hupdates, hguards⟩
  rcases hdyn with ⟨hn, hcoeffDyn, hr0Dyn, hupdatesDyn⟩
  have hu_pos := Stage3BelowTwo.coefficient_u_pos
    n hn data.u data.dw data.alpha data.c data.b hcoeff
  have hu_mono := Stage3BelowTwo.coefficient_u_mono
    n hn data.u data.dw data.alpha data.c data.b hcoeff
  have hterminal := Stage3BelowTwo.terminal_row
    n hn data.u data.dw data.alpha data.c data.b hcoeff data.G data.r hr0
      (fun k hk => (hupdates k hk).2)
  refine ⟨hterminal, ?_⟩
  let Z : VectorSeq d := fun i => belowMirrorMap p (data.r i)
  let Omega : Point d → ℝ := fun y => (1 / 2) * (lpNorm p y) ^ (2 : ℕ)
  have hres := Stage3BelowTwo.dual_residual_nonneg
    p hp hp2 n hn data.u data.dw data.alpha data.c data.b hcoeff data.G Z
  have hfunc := Stage3BelowTwo.function_block_identity
    n hn data.u data.alpha data.oracle data.G data.q Z hG
    (fun k hk => (hupdates k hk).1)
  have hmirror := Stage3BelowTwo.mirror_block_identity
    p hp n data.b data.G data.r hr0 (fun k hk => (hupdates k hk).2)
  have hfirst := O3.Stage3Anchor.firstOrderConvex_of_coordinateGradient hconv hcoord
  have hbreg : ∀ x y : Point d,
      0 ≤ FunctionBregman data.oracle.value data.oracle.gradient x y := by
    intro x y
    unfold FunctionBregman
    have h := hfirst y x
    linarith
  have hwpos : ∀ k ≤ n, 0 < 1 / data.u (n - k) := by
    intro k hk
    exact one_div_pos.mpr (hu_pos (n - k) (by omega))
  have hdelta : ∀ k < n,
      0 ≤ 1 / data.u (n - (k + 1)) - 1 / data.u (n - k) := by
    intro k hk
    have hi : n - k - 1 < n := by omega
    have hmono := hu_mono (n - k - 1) hi
    have hidx₁ : n - k - 1 + 1 = n - k := by omega
    rw [hidx₁] at hmono
    have hpos₁ := hu_pos (n - k - 1) (by omega)
    have hpos₂ := hu_pos (n - k) (by omega)
    have hinv := one_div_le_one_div_of_le hpos₁ hmono
    have hden : n - (k + 1) = n - k - 1 := by omega
    rw [hden]
    linarith
  let gradBlock : ℝ :=
    ∑ k ∈ Finset.range n,
      ((1 / data.u (n - (k + 1))) / 2) *
        (lpNorm (conjugateExponent p) (data.G k - data.G (k + 1))) ^ (2 : ℕ)
  let mirrorNormBlock : ℝ :=
    ∑ k ∈ Finset.range n, Omega (Z k - Z (k + 1))
  let bBlock : ℝ :=
    ∑ k ∈ Finset.range (n + 1),
      pairing
        (weightedSum (k + 1) (fun i => data.b (n - i) (n - k)) data.G) (Z k)
  let alphaBlock : ℝ :=
    ∑ k ∈ Finset.range n,
      pairing (Stage3BelowTwo.dualP n data.u data.G k)
        (weightedSum (k + 1)
          (fun i => data.alpha (n - i) (n - 1 - k)) Z)
  have hres_blocks : 0 ≤ gradBlock + mirrorNormBlock + bBlock + alphaBlock := by
    simpa [BelowDualResidual, gradBlock, mirrorNormBlock, bBlock, alphaBlock,
      Omega, Z, Stage3BelowTwo.dualP] using hres
  have hdelta_sum : 0 ≤
      ∑ k ∈ Finset.range n,
        (1 / data.u (n - (k + 1)) - 1 / data.u (n - k)) *
          FunctionBregman data.oracle.value data.oracle.gradient
            (data.q n) (data.q k) := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (hdelta k (Finset.mem_range.mp hk)) (hbreg _ _)
  have hguard_sum : 0 ≤
      ∑ k ∈ Finset.range n,
        (1 / data.u (n - (k + 1))) *
          (FunctionBregman data.oracle.value data.oracle.gradient
              (data.q k) (data.q (k + 1)) -
            (1 / 2) *
              (lpNorm (conjugateExponent p)
                (data.G k - data.G (k + 1))) ^ (2 : ℕ)) := by
    apply Finset.sum_nonneg
    intro k hk
    have hkn := Finset.mem_range.mp hk
    have hgk := hG k (by omega)
    have hgk1 := hG (k + 1) (by omega)
    have hg := hguards k hkn
    rw [← hgk, ← hgk1] at hg
    exact mul_nonneg (le_of_lt (hwpos (k + 1) (by omega))) (sub_nonneg.mpr hg)
  have hfunction_bound :
      gradBlock + alphaBlock ≤
        (1 / data.u n) *
          (data.oracle.value (data.q 0) - data.oracle.value (data.q n)) := by
    have hf := hfunc
    change alphaBlock = _ at hf
    have hgrad_rewrite : gradBlock =
        ∑ k ∈ Finset.range n,
          (1 / data.u (n - (k + 1))) *
            ((1 / 2) *
              (lpNorm (conjugateExponent p)
                (data.G k - data.G (k + 1))) ^ (2 : ℕ)) := by
      dsimp [gradBlock]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hguard_split : 0 ≤
        (∑ k ∈ Finset.range n,
          (1 / data.u (n - (k + 1))) *
            FunctionBregman data.oracle.value data.oracle.gradient
              (data.q k) (data.q (k + 1))) - gradBlock := by
      rw [hgrad_rewrite, ← Finset.sum_sub_distrib]
      have heq :
          (∑ k ∈ Finset.range n,
            ((1 / data.u (n - (k + 1))) *
                FunctionBregman data.oracle.value data.oracle.gradient
                  (data.q k) (data.q (k + 1)) -
              (1 / data.u (n - (k + 1))) *
                (1 / 2 * (lpNorm (conjugateExponent p)
                  (data.G k - data.G (k + 1))) ^ (2 : ℕ)))) =
          ∑ k ∈ Finset.range n,
            (1 / data.u (n - (k + 1))) *
              (FunctionBregman data.oracle.value data.oracle.gradient
                  (data.q k) (data.q (k + 1)) -
                1 / 2 * (lpNorm (conjugateExponent p)
                  (data.G k - data.G (k + 1))) ^ (2 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [heq]
      exact hguard_sum
    linarith
  have hgeom := belowGeometry p hp hp2 d
  have hmirror_gap : 0 ≤
      ∑ k ∈ Finset.range n,
        (FunctionBregman (belowHstar p) (belowMirrorMap p)
            (data.r k) (data.r (k + 1)) -
          Omega (Z k - Z (k + 1))) := by
    apply Finset.sum_nonneg
    intro k hk
    have hb := (hgeom.2.2.2.2 (data.r k) (data.r (k + 1))).2
    have hnorm : lpNorm p (Z k - Z (k + 1)) =
        lpNorm p (Z (k + 1) - Z k) := by
      dsimp [Z]
      rw [show belowMirrorMap p (data.r k) - belowMirrorMap p (data.r (k + 1)) =
        -(belowMirrorMap p (data.r (k + 1)) - belowMirrorMap p (data.r k)) by abel]
      change O3.lpNorm p (-_) = O3.lpNorm p _
      rw [O3.lpNorm_neg]
    dsimp [Omega]
    rw [hnorm]
    exact sub_nonneg.mpr hb
  have hmirror0 : 0 ≤
      FunctionBregman (belowHstar p) (belowMirrorMap p) 0 (data.r 0) := by
    have hb := (hgeom.2.2.2.2 (0 : Point d) (data.r 0)).2
    exact le_trans (by positivity) hb
  have hmirror_bound :
      mirrorNormBlock + bBlock ≤ -belowHstar p (data.r n) := by
    have hm := hmirror
    change bBlock =
      -(∑ k ∈ Finset.range n,
        FunctionBregman (belowHstar p) (belowMirrorMap p)
          (data.r k) (data.r (k + 1))) -
      belowHstar p (data.r n) -
      FunctionBregman (belowHstar p) (belowMirrorMap p) 0 (data.r 0) at hm
    have hnormdef : mirrorNormBlock =
        ∑ k ∈ Finset.range n, Omega (Z k - Z (k + 1)) := rfl
    have hgap_split : 0 ≤
        (∑ k ∈ Finset.range n,
          FunctionBregman (belowHstar p) (belowMirrorMap p)
            (data.r k) (data.r (k + 1))) - mirrorNormBlock := by
      rw [hnormdef, ← Finset.sum_sub_distrib]
      exact hmirror_gap
    linarith
  have hcore : belowHstar p (data.r n) ≤
      (1 / data.u n) *
        (data.oracle.value (data.q 0) - data.oracle.value (data.q n)) := by
    linarith
  have hsinf : sInf (Set.range data.oracle.value) ≤ data.oracle.value (data.q n) :=
    csInf_le hbdd ⟨data.q n, rfl⟩
  have hscale : 0 ≤ 1 / data.u n := le_of_lt (one_div_pos.mpr (hu_pos n le_rfl))
  have hgapscale := mul_le_mul_of_nonneg_left
    (show data.oracle.value (data.q 0) - data.oracle.value (data.q n) ≤
      data.oracle.value (data.q 0) - sInf (Set.range data.oracle.value) by linarith) hscale
  calc
    belowHstar p (data.oracle.gradient (data.q n)) = belowHstar p (data.r n) := by
      rw [← hG n le_rfl, hterminal]
    _ ≤ (1 / data.u n) *
        (data.oracle.value (data.q 0) - data.oracle.value (data.q n)) := hcore
    _ ≤ (data.oracle.value (data.q 0) - sInf (Set.range data.oracle.value)) /
        data.u n := by
      simpa [div_eq_mul_inv, one_div, mul_comm] using hgapscale

end V7
