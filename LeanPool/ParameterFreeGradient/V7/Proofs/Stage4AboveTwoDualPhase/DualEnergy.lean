/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoPrimalRepair.Closure
import LeanPool.ParameterFreeGradient.O3.Stage3Descent

/-!
The above-two dual trajectory satisfies the terminal row, query, and energy identities.
-/

open scoped BigOperators

namespace V7.Stage4AboveTwoDualPhase

private lemma weightedSum_eq_sum_smul (m : ℕ) (a : ScalarSeq)
    (X : VectorSeq d) :
    weightedSum m a X = ∑ i ∈ Finset.range m, a i • X i := by
  ext j
  simp [weightedSum]

theorem terminal_row (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (G r : VectorSeq d)
    (hr0 : r 0 = -(b n n) • G 0)
    (hr : ∀ k < n,
      r (k + 1) = r k -
        weightedSum (k + 2) (fun i ↦ b (n - i) (n - 1 - k)) G) :
    r n = G n := by
  rcases hcoeff with
    ⟨hu0, hun, hdwn, hc00, hb00, hweights, hcstep, hrows, hsupp, hbrows⟩
  let T : ℕ → Point d := fun s ↦
    weightedSum (s + 1) (fun i ↦ b (n - i) (n - s)) G
  have hunroll : ∀ k ≤ n,
      r k = -(∑ s ∈ Finset.range (k + 1), T s) := by
    intro k hk
    induction k with
    | zero =>
      rw [hr0]
      have hzero : weightedSum 1 (fun i ↦ b (n - i) n) G =
          b n n • G 0 := by
        ext j
        simp [weightedSum]
      have hsum0 : (∑ s ∈ Finset.range (0 + 1), T s) = T 0 := by simp
      rw [hsum0]
      dsimp [T]
      rw [hzero, neg_smul]
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
          (fun s ↦ ∑ i ∈ Finset.range (s + 1),
            b (n - i) (n - s) • G i) (n + 1)]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
        have hout : n + 1 - 1 - j = n - j := by omega
        rw [hout]
        have hcol : n - (n - j) = j := by omega
        rw [hcol]
        have href := Finset.sum_range_reflect
          (fun i ↦ b (n - i) j • G i) (n - j + 1)
        rw [← href]
        apply Finset.sum_congr rfl
        intro l hl
        have hln : l < n - j + 1 := Finset.mem_range.mp hl
        have hbidx : n - (n - j + 1 - 1 - l) = j + l := by omega
        have hGidx : n - j + 1 - 1 - l = n - (j + l) := by omega
        rw [hbidx, hGidx]
      _ = ∑ row ∈ Finset.range (n + 1),
          ∑ j ∈ Finset.range (row + 1), b row j • G (n - row) := by
        exact Stage4AboveTwoIdentity.triangle_sum
          (fun row j ↦ b row j • G (n - row)) n
      _ = -(G n) := by
        rw [Finset.sum_eq_single 0]
        · simp [hb00]
        · intro row hrow hrow0
          have hrowlt : row < n + 1 := Finset.mem_range.mp hrow
          have hrs := hbrows (row - 1) (by omega)
          have hrowsize : row - 1 + 2 = row + 1 := by omega
          rw [hrowsize] at hrs
          have hroweq : row - 1 + 1 = row := by omega
          rw [hroweq] at hrs
          rw [← Finset.sum_smul, hrs, zero_smul]
        · simp
  rw [hunroll n le_rfl, hT]
  simp

private lemma coefficient_u_pos (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b) :
    ∀ i ≤ n, 0 < u i := by
  rcases hcoeff with
    ⟨hu0, hun, hdwn, hc00, hb00, hweights, hcstep, hrows, hsupp, hbrows⟩
  intro i hi
  by_cases hi0 : i = 0
  · simpa [hi0] using hu0
  by_cases hin : i < n
  · exact (hweights i hin).1
  · have hieq : i = n := by omega
    rw [hieq, hun]
    exact (hweights (n - 1) (by omega)).1

private lemma coefficient_u_mono (n : ℕ)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b) :
    ∀ i < n, u i ≤ u (i + 1) := by
  rcases hcoeff with
    ⟨hu0, hun, hdwn, hc00, hb00, hweights, hcstep, hrows, hsupp, hbrows⟩
  intro i hi
  exact (hweights i hi).2.1

private lemma coefficient_dw_nonneg (n : ℕ)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b) :
    ∀ k < n, 0 ≤ dw k := by
  rcases hcoeff with
    ⟨hu0, hun, hdwn, hc00, hb00, hweights, hcstep, hrows, hsupp, hbrows⟩
  intro k hk
  rw [(hweights k hk).2.2.1]
  by_cases hk0 : k = 0
  · simp [hk0, hu0.le]
  · simp only [hk0, ↓reduceIte]
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hmono := (hweights (k - 1) (by omega)).2.1
    simpa [Nat.sub_add_cancel hk1] using sub_nonneg.mpr hmono

private lemma coefficient_X_representation (n : ℕ) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (B X : VectorSeq d) (hX : BelowXRecurrence n b B X) :
    ∀ k ≤ n, X k = weightedSum (k + 1) (c k) B := by
  rcases hcoeff with
    ⟨hu0, hun, hdwn, hc00, hb00, hweights, hcstep, hrows, hsupp, hbrows⟩
  intro k hk
  induction k with
  | zero =>
    rw [hX.1]
    ext j
    simp [weightedSum, hc00]
  | succ k ih =>
    have hkn : k < n := by omega
    rw [hX.2 k hkn, ih (by omega)]
    ext j
    simp only [weightedSum, Pi.sub_apply]
    have hsupport := hsupp k (by omega) (k + 1) (by omega)
    have hold : (∑ i ∈ Finset.range (k + 1), c k i * B i j) =
        ∑ i ∈ Finset.range (k + 2), c k i * B i j := by
      rw [Finset.sum_range_succ (fun i ↦ c k i * B i j) (k + 1),
        hsupport, zero_mul, add_zero]
    rw [hold]
    apply Eq.symm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hb := (hcstep k hkn i).2
    rw [hb]
    ring

private lemma coefficient_X_weighted_step (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (B X : VectorSeq d) (hX : BelowXRecurrence n b B X) :
    ∀ k < n,
      u (k + 1) • X (k + 1) - u k • X k =
        dw (k + 1) • B (k + 1) + dw k • (B (k + 1) - B k) := by
  rcases hcoeff with
    ⟨hu0, hun, hdwn, hc00, hb00, hweights, hcstep, hrows, hsupp, hbrows⟩
  have hu_pos := coefficient_u_pos n hn u dw alpha c b
    ⟨hu0, hun, hdwn, hc00, hb00, hweights, hcstep, hrows, hsupp, hbrows⟩
  have hrep := coefficient_X_representation n u dw alpha c b
    ⟨hu0, hun, hdwn, hc00, hb00, hweights, hcstep, hrows, hsupp, hbrows⟩ B X hX
  intro k hk
  rw [hrep k (by omega), hrep (k + 1) (by omega)]
  have hu : u (k + 1) ≠ 0 := ne_of_gt (hu_pos (k + 1) (by omega))
  ext j
  simp only [weightedSum, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsupport := hsupp k (by omega) (k + 1) (by omega)
  have hold : (∑ i ∈ Finset.range (k + 1), c k i * B i j) =
      ∑ i ∈ Finset.range (k + 2), c k i * B i j := by
    rw [Finset.sum_range_succ (fun i ↦ c k i * B i j) (k + 1),
      hsupport, zero_mul, add_zero]
  rw [hold]
  have hc := hcstep k hk
  have hpoint : ∀ i ∈ Finset.range (k + 2),
      u (k + 1) * (c (k + 1) i * B i j) - u k * (c k i * B i j) =
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
      · intro i hi hne; simp [hne]
      · simp
    · rw [Finset.sum_eq_single k]
      · simp
      · intro i hi hne; simp [hne]
      · simp
  rw [hrhs] at hsum
  have hsize : k + 1 + 1 = k + 2 := by omega
  rw [hsize, Finset.mul_sum, Finset.mul_sum, hsum]
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
  | zero => simp [pairing_sub_left]; ring
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
  let f : ℕ → ℝ := fun k ↦ dw k * O3.pairing (A k) (B k)
  have hshift := Finset.sum_range_succ' f n
  have hend : f n = 0 := by simp [f, hdwn]
  rw [Finset.sum_range_succ, hend, add_zero] at hshift
  dsimp [f] at hshift ⊢
  linarith

private lemma free_bilinear_reduction (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (A B X : VectorSeq d) (hAn : A (n + 1) = 0)
    (hX : BelowXRecurrence n b B X) :
    (∑ k ∈ Finset.range n,
        O3.pairing (weightedSum (k + 1) (alpha (k + 1)) A) (B (k + 1))) -
      (∑ k ∈ Finset.range (n + 1),
        u k * O3.pairing (A k - A (k + 1)) (X k)) =
    ∑ k ∈ Finset.range n,
      dw k * O3.pairing (A k - A (k + 1)) (B (k + 1) - B k) := by
  rcases hcoeff with
    ⟨hu0, hun, hdwn, hc00, hb00, hweights, hcstep, hrows, hsupp, hbrows⟩
  let hcoeff' : AboveCoefficientAssumptions n u dw alpha c b :=
    ⟨hu0, hun, hdwn, hc00, hb00, hweights, hcstep, hrows, hsupp, hbrows⟩
  have hxstep := coefficient_X_weighted_step n hn u dw alpha c b hcoeff' B X hX
  have hparts := sum_pairing_by_parts n u A X
  have hlast : u n * O3.pairing (A (n + 1)) (X n) = 0 := by
    rw [hAn]
    simp [O3.pairing]
  rw [hlast, sub_zero] at hparts
  have hu0dw : u 0 = dw 0 := by
    have hd0 := (hweights 0 (by omega)).2.2.1
    simpa using hd0.symm
  have halpha :
      (∑ k ∈ Finset.range n,
        O3.pairing (weightedSum (k + 1) (alpha (k + 1)) A) (B (k + 1))) =
      ∑ k ∈ Finset.range n,
        dw k * O3.pairing (A k) (B (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn := Finset.mem_range.mp hk
    rw [Stage4AboveTwoIdentity.alpha_weighted_primal
      n u dw alpha c b hcoeff' A k hkn, pairing_smul_left]
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
  have hshift := shifted_dw_pairing n dw A B hdwn
  rw [halpha, hparts, hstep_sum, hshift, hu0dw, hX.1]
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

private noncomputable def freeX (b : ScalarMatrix)
    (B : VectorSeq d) : VectorSeq d :=
  fun k ↦ Nat.rec (B 0)
    (fun j previous ↦ previous - weightedSum (j + 2) (b (j + 1)) B) k

private lemma freeX_recurrence (n : ℕ) (b : ScalarMatrix) (B : VectorSeq d) :
    BelowXRecurrence n b B (freeX b B) := by
  constructor
  · rfl
  · intro k hk
    rfl

private lemma omega_even (p : ℝ) (x : Point d) :
    aboveUniformConstant p * lpNorm p (-x) ^ p =
      aboveUniformConstant p * lpNorm p x ^ p := by
  rw [show lpNorm p (-x) = lpNorm p x by
    change O3.lpNorm p (-x) = O3.lpNorm p x
    exact O3.lpNorm_neg p x]

private lemma primal_residual_eq_mixed (p : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (A B X : VectorSeq d) (hAn : A (n + 1) = 0)
    (hX : BelowXRecurrence n b B X) :
    AbovePrimalResidual p n u alpha A B X
        (fun y ↦ aboveUniformConstant p * lpNorm p y ^ p) =
      Stage4AboveTwo.aboveMixedResidual p n u dw A (fun k ↦ -B k) := by
  have hbil := free_bilinear_reduction n hn u dw alpha c b hcoeff A B X hAn hX
  unfold AbovePrimalResidual BelowPrimalResidual Stage4AboveTwo.aboveMixedResidual
  rw [show ∀ a b c e : ℝ, (a + b + c) - e = a + b + (c - e) by
    intro a b c e; ring]
  rw [hbil]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hneg : -B k - -B (k + 1) = B (k + 1) - B k := by abel
  rw [hneg]
  have hnorm : lpNorm p (B k - B (k + 1)) =
      lpNorm p (B (k + 1) - B k) := by
    rw [show B k - B (k + 1) = -(B (k + 1) - B k) by abel]
    change O3.lpNorm p (-_) = O3.lpNorm p _
    rw [O3.lpNorm_neg]
  change
    u k / 2 * lpNorm (conjugateExponent p) (A k - A (k + 1)) ^ (2 : ℕ) +
        aboveUniformConstant p * lpNorm p (B k - B (k + 1)) ^ p +
        dw k * pairing (A k - A (k + 1)) (B (k + 1) - B k) = _
  rw [hnorm]

theorem dualResidual_lower (p : ℝ) (hp : 2 < p)
    (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (C D : VectorSeq d) :
    AboveDualResidual p n u alpha b C D
        (fun y ↦ aboveUniformConstant p * lpNorm p y ^ p) ≥
      -aboveErrorSum p n u dw := by
  have hid := V7.abovePointwiseResidualIdentity p hp d n hn
    u dw alpha c b (fun y ↦ aboveUniformConstant p * lpNorm p y ^ p)
    hcoeff (omega_even p)
  obtain ⟨A, B, hmap⟩ := hid.2.1 C D
  let A' : VectorSeq d := fun i ↦ if i ≤ n then A i else 0
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
  have hprimal := primal_residual_eq_mixed
    p n hn u dw alpha c b hcoeff A' B (freeX b B) hAn hX
  have hmix := Stage4AboveTwo.aboveMixedResidual_lower p hp n u dw
    A' (fun k ↦ -B k)
    (fun k hk ↦ coefficient_u_pos n hn u dw alpha c b hcoeff k (by omega))
    (coefficient_dw_nonneg n u dw alpha c b hcoeff)
  rw [← heq, hprimal]
  exact hmix

private lemma sum_succ_sub {E : Type*} [AddCommGroup E]
    (n : ℕ) (f : ℕ → E) :
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
      O3.pairing (Stage4AboveTwoIdentity.dualP n u G k)
        (q k - q (k + 1))) =
    (∑ k ∈ Finset.range n,
      (1 / u (n - (k + 1))) *
        O3.pairing (G (k + 1)) (q k - q (k + 1))) -
    ∑ j ∈ Finset.range n,
      (1 / u (n - (j + 1)) - 1 / u (n - j)) *
        O3.pairing (G j) (q j - q n) := by
  let delta : ScalarSeq := fun j ↦
    1 / u (n - (j + 1)) - 1 / u (n - j)
  have hexpand :
      (∑ k ∈ Finset.range n,
        O3.pairing (Stage4AboveTwoIdentity.dualP n u G k)
          (q k - q (k + 1))) =
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1))) *
          O3.pairing (G (k + 1)) (q k - q (k + 1))) -
      ∑ k ∈ Finset.range n,
        ∑ j ∈ Finset.range (k + 1),
          delta j * O3.pairing (G j) (q k - q (k + 1)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Stage4AboveTwoIdentity.dualP, pairing_sub_left, pairing_smul_left]
    change _ - O3.pairing
      (weightedSum (k + 1) (fun j ↦ delta j) G) (q k - q (k + 1)) = _
    rw [pairing_weightedSum_left]
  rw [hexpand]
  congr 1
  have htri := Stage4AboveTwoIdentity.triangle_sum
    (fun k j ↦ delta j * O3.pairing (G j) (q k - q (k + 1))) (n - 1)
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
  rw [hsize, ht]

private lemma function_value_cancel (n : ℕ) (w F : ScalarSeq) :
    w 0 * (F 0 - F n) -
      (∑ k ∈ Finset.range n, (w (k + 1) - w k) * (F n - F k)) -
      (∑ k ∈ Finset.range n, w (k + 1) * (F k - F (k + 1))) = 0 := by
  have hdelta := sum_succ_sub n w
  have hshift :
      (∑ k ∈ Finset.range n, w (k + 1) * F (k + 1)) =
      (∑ k ∈ Finset.range n, w k * F k) - w 0 * F 0 + w n * F n := by
    let f : ℕ → ℝ := fun k ↦ w k * F k
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
        weightedSum (k + 1) (fun i ↦ alpha (n - i) (n - 1 - k)) Z) :
    (∑ k ∈ Finset.range n,
      O3.pairing (Stage4AboveTwoIdentity.dualP n u G k)
        (weightedSum (k + 1) (fun i ↦ alpha (n - i) (n - 1 - k)) Z)) =
    (1 / u n) * (oracle.value (q 0) - oracle.value (q n)) -
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1)) - 1 / u (n - k)) *
          FunctionBregman oracle.value oracle.gradient (q n) (q k)) -
      (∑ k ∈ Finset.range n,
        (1 / u (n - (k + 1))) *
          FunctionBregman oracle.value oracle.gradient (q k) (q (k + 1))) := by
  have hQ : ∀ k < n,
      weightedSum (k + 1) (fun i ↦ alpha (n - i) (n - 1 - k)) Z =
        q k - q (k + 1) := by
    intro k hk
    rw [hq k hk]
    abel
  have hpath := dualP_pairing_path n hn u G q
  have hleft :
      (∑ k ∈ Finset.range n,
        O3.pairing (Stage4AboveTwoIdentity.dualP n u G k)
          (weightedSum (k + 1) (fun i ↦ alpha (n - i) (n - 1 - k)) Z)) =
      ∑ k ∈ Finset.range n,
        O3.pairing (Stage4AboveTwoIdentity.dualP n u G k)
          (q k - q (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hQ k (Finset.mem_range.mp hk)]
  rw [hleft, hpath]
  let w : ScalarSeq := fun k ↦ 1 / u (n - k)
  let F : ScalarSeq := fun k ↦ oracle.value (q k)
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
    rw [hG k (by have := Finset.mem_range.mp hk; omega)]
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
    rw [hG (k + 1) (by have := Finset.mem_range.mp hk; omega)]
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

private lemma aboveHstar_zero (p : ℝ) (hp : 2 < p) (d : ℕ) :
    aboveHstar p (0 : Point d) = 0 := by
  rw [aboveHstar]
  have hq : 0 < conjugateExponent p := Stage4AboveTwo.conjugate_pos hp
  change 1 / O3.conjugateExponent p *
    O3.lpNorm (O3.conjugateExponent p) 0 ^ O3.conjugateExponent p = 0
  rw [O3.lpNorm_zero hq, Real.zero_rpow hq.ne']
  ring

private lemma mirror_block_identity (p : ℝ) (hp : 2 < p) (n : ℕ)
    (b : ScalarMatrix) (G r : VectorSeq d)
    (hr0 : r 0 = -(b n n) • G 0)
    (hr : ∀ k < n,
      r (k + 1) = r k -
        weightedSum (k + 2) (fun i ↦ b (n - i) (n - 1 - k)) G) :
    let Z : VectorSeq d := fun i ↦ aboveMirrorMap p (r i)
    (∑ k ∈ Finset.range (n + 1),
      O3.pairing
        (weightedSum (k + 1) (fun i ↦ b (n - i) (n - k)) G) (Z k)) =
      -(∑ k ∈ Finset.range n,
        FunctionBregman (aboveHstar p) (aboveMirrorMap p) (r k) (r (k + 1))) -
      aboveHstar p (r n) -
      FunctionBregman (aboveHstar p) (aboveMirrorMap p) 0 (r 0) := by
  dsimp
  let Z : VectorSeq d := fun i ↦ aboveMirrorMap p (r i)
  have hrow0 : weightedSum 1 (fun i ↦ b (n - i) (n - 0)) G = -(r 0) := by
    rw [hr0]
    ext j
    simp [weightedSum]
  have hrow : ∀ k, 0 < k → k ≤ n →
      weightedSum (k + 1) (fun i ↦ b (n - i) (n - k)) G =
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
          (weightedSum (k + 1) (fun i ↦ b (n - i) (n - k)) G) (Z k)) =
      -O3.pairing (r 0) (Z 0) +
        ∑ k ∈ Finset.range n,
          O3.pairing (r k - r (k + 1)) (Z (k + 1)) := by
    rw [Finset.sum_range_succ']
    rw [hrow0]
    have hneg : O3.pairing (-(r 0)) (Z 0) =
        -O3.pairing (r 0) (Z 0) := by
      simp [O3.pairing, Finset.sum_neg_distrib]
    rw [hneg]
    have hsums :
        (∑ k ∈ Finset.range n,
          O3.pairing
            (weightedSum (k + 1 + 1) (fun i ↦ b (n - i) (n - (k + 1))) G)
            (Z (k + 1))) =
        ∑ k ∈ Finset.range n,
          O3.pairing (r k - r (k + 1)) (Z (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hrow (k + 1) (by omega)
        (by have := Finset.mem_range.mp hk; omega)]
      simp only [Nat.succ_sub_one]
    rw [hsums]
    abel
  rw [hrowsum]
  unfold FunctionBregman
  have htel := sum_succ_sub n (fun k ↦ aboveHstar p (r k))
  have hpair :
      (∑ k ∈ Finset.range n,
        O3.pairing (aboveMirrorMap p (r (k + 1))) (r k - r (k + 1))) =
      ∑ k ∈ Finset.range n,
        O3.pairing (r k - r (k + 1)) (Z (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [O3.pairing_comm]
  dsimp [Z] at hpair ⊢
  rw [← hpair, aboveHstar_zero p hp]
  rw [Finset.sum_sub_distrib]
  have hfun :
      (∑ k ∈ Finset.range n,
        (aboveHstar p (r k) - aboveHstar p (r (k + 1)))) =
      aboveHstar p (r 0) - aboveHstar p (r n) := by
    have hneg := congrArg Neg.neg htel
    rw [← Finset.sum_neg_distrib] at hneg
    simpa only [neg_sub] using hneg
  rw [hfun]
  have hbasepair : pairing (aboveMirrorMap p (r 0)) (-r 0) =
      -O3.pairing (r 0) (aboveMirrorMap p (r 0)) := by
    rw [O3.pairing_comm]
    simp [O3.pairing]
  simp only [zero_sub]
  rw [hbasepair]
  ring

theorem terminalRowAndQuery (p : ℝ) (n : ℕ)
    (data : AboveDualPhaseData p d n)
    (hass : AboveDualPhaseAssumptions data) :
    data.r n = data.G n ∧
      QueriedAt data.trace n (data.q n) ∧
      data.G n = data.oracle.gradient (data.q n) := by
  rcases hass with
    ⟨hdyn, hconv, hcoord, hbdd, htrace, hlen, hqueried, hr0, hupdates⟩
  rcases hdyn with ⟨hn, hcoeff, hr0Dyn, hupdatesDyn⟩
  exact ⟨terminal_row n hn data.u data.dw data.alpha data.c data.b hcoeff
    data.G data.r hr0 (fun k hk ↦ (hupdates k hk).2.1),
    (hqueried n le_rfl).1, (hqueried n le_rfl).2⟩

/-- Uniform convexity bounds the sum of dual mirror gaps along an arbitrary sequence. -/
private lemma mirror_gap_nonnegative (p : ℝ) (hp : 2 < p) (n : ℕ) (r : VectorSeq d) :
    0 ≤ ∑ k ∈ Finset.range n,
      (FunctionBregman (aboveHstar p) (aboveMirrorMap p) (r k) (r (k + 1)) -
        aboveUniformConstant p *
          lpNorm p (aboveMirrorMap p (r k) - aboveMirrorMap p (r (k + 1))) ^ p) := by
  let Z : VectorSeq d := fun i ↦ aboveMirrorMap p (r i)
  let Omega : Point d → ℝ := fun y ↦ aboveUniformConstant p * lpNorm p y ^ p
  change 0 ≤ ∑ k ∈ Finset.range n,
    (FunctionBregman (aboveHstar p) (aboveMirrorMap p) (r k) (r (k + 1)) -
      Omega (Z k - Z (k + 1)))
  apply Finset.sum_nonneg
  intro k hk
  have hconj := (V7.aboveGeometry p hp d).2.2.2
    (r k) (r (k + 1))
  have huni := (V7.aboveGeometry p hp d).2.2.1
    (aboveMirrorMap p (r (k + 1)))
    (aboveMirrorMap p (r k))
  have hnorm : lpNorm p (Z k - Z (k + 1)) =
      lpNorm p (Z (k + 1) - Z k) := by
    dsimp [Z]
    rw [show aboveMirrorMap p (r k) - aboveMirrorMap p (r (k + 1)) =
      -(aboveMirrorMap p (r (k + 1)) - aboveMirrorMap p (r k)) by
        abel]
    change O3.lpNorm p (-_) = O3.lpNorm p _
    rw [O3.lpNorm_neg]
  rw [hconj]
  dsimp [Omega]
  rw [hnorm]
  exact sub_nonneg.mpr (by simpa [aboveUniformConstant] using huni)

theorem dualTerminalEnergy (p : ℝ) (hp : 2 < p) (n : ℕ)
    (data : AboveDualPhaseData p d n)
    (hass : AboveDualPhaseAssumptions data) :
    aboveHstar p (data.oracle.gradient (data.q n)) ≤
      (data.oracle.value (data.q 0) -
        sInf (Set.range data.oracle.value)) / data.u n +
      aboveErrorSum p n data.u data.dw := by
  rcases hass with
    ⟨hdyn, hconv, hcoord, hbdd, htrace, hlen, hqueried, hr0, hupdates⟩
  rcases hdyn with ⟨hn, hcoeff, hr0Dyn, hupdatesDyn⟩
  have hG : ∀ k ≤ n, data.G k = data.oracle.gradient (data.q k) :=
    fun k hk ↦ (hqueried k hk).2
  have hu_pos := coefficient_u_pos
    n hn data.u data.dw data.alpha data.c data.b hcoeff
  have hu_mono := coefficient_u_mono
    n data.u data.dw data.alpha data.c data.b hcoeff
  have hterminal := terminal_row
    n hn data.u data.dw data.alpha data.c data.b hcoeff data.G data.r hr0
      (fun k hk ↦ (hupdates k hk).2.1)
  let Z : VectorSeq d := fun i ↦ aboveMirrorMap p (data.r i)
  let Omega : Point d → ℝ := fun y ↦
    aboveUniformConstant p * lpNorm p y ^ p
  have hres := dualResidual_lower p hp n hn data.u data.dw data.alpha
    data.c data.b hcoeff data.G Z
  have hfunc := function_block_identity n hn data.u data.alpha data.oracle
    data.G data.q Z hG (fun k hk ↦ (hupdates k hk).1)
  have hmirror := mirror_block_identity p hp n data.b data.G data.r hr0
    (fun k hk ↦ (hupdates k hk).2.1)
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
    have hinv := one_div_le_one_div_of_le hpos₁ hmono
    have hden : n - (k + 1) = n - k - 1 := by omega
    rw [hden]
    linarith
  let gradBlock : ℝ :=
    ∑ k ∈ Finset.range n,
      ((1 / data.u (n - (k + 1))) / 2) *
        (lpNorm (conjugateExponent p)
          (data.G k - data.G (k + 1))) ^ (2 : ℕ)
  let mirrorNormBlock : ℝ :=
    ∑ k ∈ Finset.range n, Omega (Z k - Z (k + 1))
  let bBlock : ℝ :=
    ∑ k ∈ Finset.range (n + 1),
      pairing
        (weightedSum (k + 1)
          (fun i ↦ data.b (n - i) (n - k)) data.G) (Z k)
  let alphaBlock : ℝ :=
    ∑ k ∈ Finset.range n,
      pairing (Stage4AboveTwoIdentity.dualP n data.u data.G k)
        (weightedSum (k + 1)
          (fun i ↦ data.alpha (n - i) (n - 1 - k)) Z)
  have hres_blocks :
      -aboveErrorSum p n data.u data.dw ≤
        gradBlock + mirrorNormBlock + bBlock + alphaBlock := by
    simpa [AboveDualResidual, BelowDualResidual, gradBlock, mirrorNormBlock,
      bBlock, alphaBlock, Omega, Z, Stage4AboveTwoIdentity.dualP] using hres
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
    exact mul_nonneg (le_of_lt (hwpos (k + 1) (by omega)))
      (sub_nonneg.mpr (hupdates k hkn).2.2)
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
  have hmirror_gap := mirror_gap_nonnegative p hp n data.r
  have hmirror0 : 0 ≤
      FunctionBregman (aboveHstar p) (aboveMirrorMap p) 0 (data.r 0) := by
    have hconj := (V7.aboveGeometry p hp d).2.2.2
      (0 : Point d) (data.r 0)
    have huni := (V7.aboveGeometry p hp d).2.2.1
      (aboveMirrorMap p (data.r 0)) (aboveMirrorMap p 0)
    rw [hconj]
    have hnonneg : 0 ≤ aboveUniformConstant p *
        lpNorm p (aboveMirrorMap p (data.r 0) - aboveMirrorMap p 0) ^ p :=
      mul_nonneg (Stage4AboveTwo.uniformConstant_pos hp).le
        (Real.rpow_nonneg (O3.lpNorm_nonneg _ _) _)
    exact le_trans hnonneg (by simpa [aboveUniformConstant] using huni)
  have hmirror_bound :
      mirrorNormBlock + bBlock ≤ -aboveHstar p (data.r n) := by
    have hm := hmirror
    change bBlock =
      -(∑ k ∈ Finset.range n,
        FunctionBregman (aboveHstar p) (aboveMirrorMap p)
          (data.r k) (data.r (k + 1))) -
      aboveHstar p (data.r n) -
      FunctionBregman (aboveHstar p) (aboveMirrorMap p) 0 (data.r 0) at hm
    have hnormdef : mirrorNormBlock =
        ∑ k ∈ Finset.range n, Omega (Z k - Z (k + 1)) := rfl
    have hgap_split : 0 ≤
        (∑ k ∈ Finset.range n,
          FunctionBregman (aboveHstar p) (aboveMirrorMap p)
            (data.r k) (data.r (k + 1))) - mirrorNormBlock := by
      rw [hnormdef, ← Finset.sum_sub_distrib]
      exact hmirror_gap
    linarith
  have hcore : aboveHstar p (data.r n) ≤
      (1 / data.u n) *
        (data.oracle.value (data.q 0) - data.oracle.value (data.q n)) +
      aboveErrorSum p n data.u data.dw := by
    linarith
  have hsinf : sInf (Set.range data.oracle.value) ≤
      data.oracle.value (data.q n) :=
    csInf_le hbdd ⟨data.q n, rfl⟩
  have hscale : 0 ≤ 1 / data.u n :=
    le_of_lt (one_div_pos.mpr (hu_pos n le_rfl))
  have hgapscale := mul_le_mul_of_nonneg_left
    (show data.oracle.value (data.q 0) - data.oracle.value (data.q n) ≤
      data.oracle.value (data.q 0) - sInf (Set.range data.oracle.value) by
        linarith) hscale
  calc
    aboveHstar p (data.oracle.gradient (data.q n)) =
        aboveHstar p (data.r n) := by
      rw [← hG n le_rfl, hterminal]
    _ ≤ (1 / data.u n) *
        (data.oracle.value (data.q 0) - data.oracle.value (data.q n)) +
      aboveErrorSum p n data.u data.dw := hcore
    _ ≤ (data.oracle.value (data.q 0) -
          sInf (Set.range data.oracle.value)) / data.u n +
        aboveErrorSum p n data.u data.dw := by
      have := add_le_add_right hgapscale (aboveErrorSum p n data.u data.dw)
      simpa [div_eq_mul_inv, one_div, mul_comm] using this

end V7.Stage4AboveTwoDualPhase

namespace V7

theorem aboveDualTerminalRowAndQuery (p : ℝ) (n : ℕ)
    (data : AboveDualPhaseData p d n)
    (hass : AboveDualPhaseAssumptions data) :
    data.r n = data.G n ∧
      QueriedAt data.trace n (data.q n) ∧
      data.G n = data.oracle.gradient (data.q n) :=
  Stage4AboveTwoDualPhase.terminalRowAndQuery p n data hass

theorem aboveDualTerminalEnergy (p : ℝ) (hp : 2 < p) (n : ℕ)
    (data : AboveDualPhaseData p d n)
    (hass : AboveDualPhaseAssumptions data) :
    aboveHstar p (data.oracle.gradient (data.q n)) ≤
      (data.oracle.value (data.q 0) -
        sInf (Set.range data.oracle.value)) / data.u n +
      aboveErrorSum p n data.u data.dw :=
  Stage4AboveTwoDualPhase.dualTerminalEnergy p hp n data hass

end V7
