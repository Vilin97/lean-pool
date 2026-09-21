/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwo.WeightBalance
import LeanPool.ParameterFreeGradient.O3.Stage2RouteC
import LeanPool.ParameterFreeGradient.O3.Stage2RouteD

/-!
The pointwise primal-dual residual identity for the above-two coefficient recurrences.
-/

open scoped BigOperators

namespace V7.Stage4AboveTwoIdentity

private noncomputable def forwardC (n : ℕ) (u : ScalarSeq)
    (A : VectorSeq d) : VectorSeq d :=
  fun k => Nat.rec (u n • A n)
    (fun j previous =>
      if j < n then
        previous + u (n - j - 1) • (A (n - j - 1) - A (n - j))
      else previous) k

private lemma forwardC_zero (n : ℕ) (u : ScalarSeq) (A : VectorSeq d) :
    forwardC n u A 0 = u n • A n := by
  rfl

private lemma forwardC_succ (n : ℕ) (u : ScalarSeq) (A : VectorSeq d)
    (k : ℕ) (hk : k < n) :
    forwardC n u A (k + 1) = forwardC n u A k +
      u (n - k - 1) • (A (n - k - 1) - A (n - k)) := by
  simp [forwardC, hk]

private lemma forward_map (n : ℕ) (u : ScalarSeq) (A B : VectorSeq d) :
    BelowResidualMap n u A B (forwardC n u A) (fun i => B (n - i)) := by
  refine ⟨forwardC_zero n u A, ?_, ?_⟩
  · intro i hi
    have hpos : 0 < n - i := by omega
    have hk : n - i - 1 < n := by omega
    rw [show n - i = (n - i - 1) + 1 by omega]
    rw [forwardC_succ n u A (n - i - 1) hk]
    have hindex₁ : n - (n - i - 1) - 1 = i := by omega
    have hindex₂ : n - (n - i - 1) = i + 1 := by omega
    rw [hindex₁, hindex₂]
    simp only [Nat.succ_sub_one]
    exact add_sub_cancel_left
      (forwardC n u A (n - i - 1))
      (u i • (A i - A (i + 1)))
  · intro i hi
    rfl

private lemma coefficient_u_pos (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b) :
    ∀ i ≤ n, 0 < u i := by
  intro i hi
  rcases hcoeff with ⟨hu0, hun, hdwn, hc00, hb00, htable, hc, hrowsc, hsupport, hrowsb⟩
  by_cases hin : i < n
  · exact (htable i hin).1
  · have hin_eq : i = n := by omega
    rw [hin_eq, hun]
    have hpred : n - 1 < n := by omega
    exact (htable (n - 1) hpred).1

private noncomputable def inverseRev (n : ℕ) (u : ScalarSeq)
    (C : VectorSeq d) : VectorSeq d :=
  fun k => Nat.rec ((1 / u n) • C 0)
    (fun j previous =>
      if j < n then
        previous + (1 / u (n - j - 1)) • (C (j + 1) - C j)
      else previous) k

private lemma inverseRev_zero (n : ℕ) (u : ScalarSeq) (C : VectorSeq d) :
    inverseRev n u C 0 = (1 / u n) • C 0 := by
  rfl

private lemma inverseRev_succ (n : ℕ) (u : ScalarSeq) (C : VectorSeq d)
    (k : ℕ) (hk : k < n) :
    inverseRev n u C (k + 1) = inverseRev n u C k +
      (1 / u (n - k - 1)) • (C (k + 1) - C k) := by
  simp [inverseRev, hk]

private noncomputable def inverseA (n : ℕ) (u : ScalarSeq)
    (C : VectorSeq d) : VectorSeq d :=
  fun i => inverseRev n u C (n - i)

private lemma inverse_map (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (C D : VectorSeq d) :
    BelowResidualMap n u (inverseA n u C) (fun i => D (n - i)) C D := by
  have hu_pos := coefficient_u_pos n hn u dw alpha c b hcoeff
  refine ⟨?_, ?_, ?_⟩
  · rw [inverseA, Nat.sub_self, inverseRev_zero]
    have hun : u n ≠ 0 := ne_of_gt (hu_pos n le_rfl)
    simp [smul_smul, hun]
  · intro i hi
    have hk : n - i - 1 < n := by omega
    have hgap : n - i = (n - i - 1) + 1 := by omega
    rw [inverseA, inverseA, show n - (i + 1) = n - i - 1 by omega, hgap,
      inverseRev_succ n u C (n - i - 1) hk]
    have hindex : n - (n - i - 1) - 1 = i := by omega
    rw [hindex]
    have hui : u i ≠ 0 := ne_of_gt (hu_pos i (by omega))
    simp [sub_eq_add_neg, smul_add, smul_smul, hui]
  · intro i hi
    change D i = D (n - (n - i))
    rw [show n - (n - i) = i by omega]

private lemma map_determined_forward (n : ℕ) (u : ScalarSeq)
    (A B C D : VectorSeq d) (hmap : BelowResidualMap n u A B C D) :
    SameOnHorizon n C (forwardC n u A) ∧
      SameOnHorizon n D (fun i => B (n - i)) := by
  constructor
  · intro k hk
    induction k with
    | zero => exact hmap.1.trans (forwardC_zero n u A).symm
    | succ k ih =>
      have hkn : k < n := by omega
      have hi : n - k - 1 < n := by omega
      have hnk : n - (n - k - 1) = k + 1 := by omega
      have hpred : n - (n - k - 1) - 1 = k := by omega
      have hm := hmap.2.1 (n - k - 1) hi
      simp only [hnk, Nat.succ_sub_one,
        show n - k - 1 + 1 = n - k by omega] at hm
      rw [forwardC_succ n u A k hkn, ← ih (by omega)]
      exact eq_add_of_sub_eq' hm
  · intro k hk
    exact hmap.2.2 k hk

private lemma map_determined_inverse (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (A B C D : VectorSeq d) (hmap : BelowResidualMap n u A B C D) :
    SameOnHorizon n A (inverseA n u C) ∧
      SameOnHorizon n B (fun i => D (n - i)) := by
  have hu_pos := coefficient_u_pos n hn u dw alpha c b hcoeff
  constructor
  · intro i hi
    let R := inverseRev n u C
    have hrev : ∀ k ≤ n, A (n - k) = R k := by
      intro k hk
      induction k with
      | zero =>
        dsimp [R]
        rw [inverseRev_zero, hmap.1]
        have hun : u n ≠ 0 := ne_of_gt (hu_pos n le_rfl)
        simp [smul_smul, hun]
      | succ k ih =>
        have hkn : k < n := by omega
        have hm := hmap.2.1 (n - k - 1) (by omega)
        have hleft : n - (n - k - 1) = k + 1 := by omega
        have hright : n - (n - k - 1) - 1 = k := by omega
        have hAi : n - k - 1 + 1 = n - k := by omega
        simp only [hleft, Nat.succ_sub_one, hAi] at hm
        have htarget : n - (k + 1) = n - k - 1 := by omega
        rw [htarget]
        dsimp [R]
        rw [inverseRev_succ n u C k hkn]
        have ih' := ih (by omega)
        change A (n - k) = inverseRev n u C k at ih'
        rw [← ih']
        have hui : u (n - k - 1) ≠ 0 :=
          ne_of_gt (hu_pos (n - k - 1) (by omega))
        rw [hm]
        simp [smul_smul, hui]
    change A i = inverseRev n u C (n - i)
    have hr := hrev (n - i) (by omega)
    change A (n - (n - i)) = inverseRev n u C (n - i) at hr
    rw [← hr, show n - (n - i) = i by omega]
  · intro i hi
    change B i = D (n - i)
    rw [hmap.2.2 (n - i) (by omega), show n - (n - i) = i by omega]

private lemma pairing_smul_left (r : ℝ) (x y : Point d) :
    O3.pairing (r • x) y = r * O3.pairing x y :=
  O3.Stage2RouteD.pairing_smul_left r x y

private lemma pairing_smul_right (r : ℝ) (x y : Point d) :
    O3.pairing x (r • y) = r * O3.pairing x y :=
  O3.Stage2RouteD.pairing_smul_right r x y

private lemma pairing_add_left (x y z : Point d) :
    O3.pairing (x + y) z = O3.pairing x z + O3.pairing y z := by
  simp [O3.pairing, Finset.sum_add_distrib, add_mul]

private lemma pairing_sub_left (x y z : Point d) :
    O3.pairing (x - y) z = O3.pairing x z - O3.pairing y z := by
  simp [O3.pairing, Finset.sum_sub_distrib, sub_mul]

private lemma pairing_sub_right (x y z : Point d) :
    O3.pairing x (y - z) = O3.pairing x y - O3.pairing x z := by
  simp [O3.pairing, Finset.sum_sub_distrib, mul_sub]

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

private lemma pairing_weightedSum_right (m : ℕ) (a : ScalarSeq)
    (X : VectorSeq d) (y : Point d) :
    O3.pairing y (weightedSum m a X) =
      ∑ i ∈ Finset.range m, a i * O3.pairing y (X i) := by
  rw [O3.pairing_comm, pairing_weightedSum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [O3.pairing_comm]

private lemma pairing_abel (n : ℕ) (Y X : VectorSeq d) :
    (∑ k ∈ Finset.range (n + 1), O3.pairing (Y k - Y (k + 1)) (X k)) =
      O3.pairing (Y 0) (X 0) +
        (∑ k ∈ Finset.range n,
          O3.pairing (Y (k + 1)) (X (k + 1) - X k)) -
        O3.pairing (Y (n + 1)) (X n) := by
  induction n with
  | zero =>
    simp [pairing_sub_left]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [pairing_sub_left, pairing_sub_right]
    ring

lemma triangle_sum {E : Type*} [AddCommMonoid E]
    (f : ℕ → ℕ → E) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      ∑ l ∈ Finset.range (n - j + 1), f (j + l) j) =
    ∑ r ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.range (r + 1), f r j := by
  induction n with
  | zero => simp
  | succ n ih =>
    change
      (∑ j ∈ Finset.range (n + 2),
        ∑ l ∈ Finset.range (n + 1 - j + 1), f (j + l) j) =
      ∑ r ∈ Finset.range (n + 2),
        ∑ j ∈ Finset.range (r + 1), f r j
    rw [Finset.sum_range_succ _ (n + 1),
      Finset.sum_range_succ _ (n + 1)]
    have hlast :
        (∑ l ∈ Finset.range (n + 1 - (n + 1) + 1), f (n + 1 + l) (n + 1)) =
          f (n + 1) (n + 1) := by simp
    rw [hlast]
    have hsplit :
        (∑ j ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (n + 1 - j + 1), f (j + l) j) =
        (∑ j ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (n - j + 1), f (j + l) j) +
        ∑ j ∈ Finset.range (n + 1), f (n + 1) j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < n + 1 := Finset.mem_range.mp hj
      have hjn : j ≤ n := by omega
      have hsize : n + 1 - j + 1 = (n - j + 1) + 1 := by omega
      rw [hsize, Finset.sum_range_succ]
      rw [show j + (n - j + 1) = n + 1 by omega]
    rw [hsplit, ih]
    rw [Finset.sum_range_succ (fun j => f (n + 1) j) (n + 1)]
    ac_rfl

lemma alpha_weighted_primal (n : ℕ) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (A : VectorSeq d) (k : ℕ) (hk : k < n) :
    weightedSum (k + 1) (alpha (k + 1)) A = dw k • A k := by
  have halpha := (hcoeff.2.2.2.2.2.1 k hk).2.2.2
  ext j
  simp only [weightedSum, Pi.smul_apply]
  rw [Finset.sum_eq_single k]
  · rw [halpha k]
    simp
  · intro i hi hik
    rw [halpha i]
    simp [hik]
  · simp

private lemma alpha_weighted_dual (n : ℕ) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (D : VectorSeq d) (k : ℕ) (hk : k < n) :
    weightedSum (k + 1) (fun i => alpha (n - i) (n - 1 - k)) D =
      dw (n - k - 1) • D k := by
  have hi : n - k - 1 < n := by omega
  have halpha := (hcoeff.2.2.2.2.2.1 (n - k - 1) hi).2.2.2
  ext j
  simp only [weightedSum, Pi.smul_apply]
  rw [Finset.sum_eq_single k]
  · have hrow : n - k = n - k - 1 + 1 := by omega
    rw [hrow, halpha (n - 1 - k)]
    have hcol : n - 1 - k = n - k - 1 := by omega
    simp [hcol]
  · intro i hii hik
    have hil : i < k + 1 := Finset.mem_range.mp hii
    have hrow : n - i = (n - i - 1) + 1 := by omega
    have hri : n - i - 1 < n := by omega
    have ha := (hcoeff.2.2.2.2.2.1 (n - i - 1) hri).2.2.2 (n - 1 - k)
    rw [hrow, ha]
    have hne : n - 1 - k ≠ n - i - 1 := by omega
    simp [hne]
  · simp

/-- The reciprocal-weight combination of reversed dual gradients used in the above-two identity. -/
noncomputable def dualP (n : ℕ) (u : ScalarSeq)
    (C : VectorSeq d) (k : ℕ) : Point d :=
  (1 / u (n - (k + 1))) • C (k + 1) -
    weightedSum (k + 1)
      (fun j => 1 / u (n - (j + 1)) - 1 / u (n - j)) C

private lemma dualP_succ (n : ℕ) (u : ScalarSeq) (C : VectorSeq d)
    (k : ℕ) :
    dualP n u C (k + 1) = dualP n u C k +
      (1 / u (n - (k + 2))) • (C (k + 2) - C (k + 1)) := by
  ext j
  simp [dualP, weightedSum, Finset.sum_range_succ]
  ring

private lemma dualP_map (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (A B C D : VectorSeq d) (hmap : BelowResidualMap n u A B C D) :
    ∀ k < n, dualP n u C k = A (n - k - 1) := by
  have hu_pos := coefficient_u_pos n hn u dw alpha c b hcoeff
  intro k hk
  induction k with
  | zero =>
    have hm := hmap.2.1 (n - 1) (by omega)
    have hnleft : n - (n - 1) = 1 := by omega
    have hnright : n - (n - 1) - 1 = 0 := by omega
    have hnA : n - 1 + 1 = n := by omega
    simp only [hnleft, hnA] at hm
    have hnsub : n - (0 + 1) = n - 1 := by omega
    rw [dualP, hnsub]
    ext j
    simp only [weightedSum, Pi.sub_apply, Pi.smul_apply]
    rw [Finset.sum_range_one]
    simp only [Nat.zero_add, Nat.sub_zero]
    have hun : u n ≠ 0 := ne_of_gt (hu_pos n le_rfl)
    have hui : u (n - 1) ≠ 0 := ne_of_gt (hu_pos (n - 1) (by omega))
    have hmj := congrFun hm j
    have hcj := congrFun hmap.1 j
    simp only [Pi.sub_apply, Pi.smul_apply] at hmj hcj ⊢
    simp only [Nat.succ_sub_one, smul_eq_mul] at hmj hcj ⊢
    have hplateau := hcoeff.2.1
    rw [hplateau] at hcj ⊢
    field_simp
    ring_nf at hmj hcj ⊢
    nlinarith
  | succ k ih =>
    have hk' : k < n := by omega
    have hgap : n - (k + 1) - 1 < n := by omega
    have hm := hmap.2.1 (n - (k + 1) - 1) hgap
    have hleft : n - (n - (k + 1) - 1) = k + 2 := by omega
    have hA : n - (k + 1) - 1 + 1 = n - k - 1 := by omega
    simp only [hleft, Nat.succ_sub_one, hA] at hm
    rw [dualP_succ, ih hk']
    have hui : u (n - (k + 1) - 1) ≠ 0 :=
      ne_of_gt (hu_pos (n - (k + 1) - 1) (by omega))
    have hden : n - (k + 2) = n - (k + 1) - 1 := by omega
    rw [hden, hm]
    simp [smul_smul, hui]

private lemma omega_block (n : ℕ) (Omega : Point d → ℝ)
    (heven : EvenIncrement Omega) (B D : VectorSeq d)
    (hD : ∀ i ≤ n, D i = B (n - i)) :
    (∑ k ∈ Finset.range n, Omega (B k - B (k + 1))) =
      ∑ k ∈ Finset.range n, Omega (D k - D (k + 1)) := by
  rw [← Finset.sum_range_reflect
    (fun k => Omega (B k - B (k + 1))) n]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  rw [hD k (by omega), hD (k + 1) (by omega)]
  have h₁ : n - k = n - 1 - k + 1 := by omega
  have h₂ : n - (k + 1) = n - 1 - k := by omega
  rw [h₁, h₂]
  rw [show B (n - 1 - k + 1) - B (n - 1 - k) =
      -(B (n - 1 - k) - B (n - 1 - k + 1)) by abel]
  exact (heven _).symm

private lemma norm_block (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (A B C D : VectorSeq d) (hmap : BelowResidualMap n u A B C D) :
    (∑ k ∈ Finset.range n,
      (u k / 2) * (lpNorm (conjugateExponent p) (A k - A (k + 1))) ^ (2 : ℕ)) =
    ∑ k ∈ Finset.range n,
      ((1 / u (n - (k + 1))) / 2) *
        (lpNorm (conjugateExponent p) (C k - C (k + 1))) ^ (2 : ℕ) := by
  have hu_pos := coefficient_u_pos n hn u dw alpha c b hcoeff
  rw [← Finset.sum_range_reflect
    (fun k => (u k / 2) *
      (lpNorm (conjugateExponent p) (A k - A (k + 1))) ^ (2 : ℕ)) n]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  let i := n - 1 - k
  have hi : i < n := by dsimp [i]; omega
  have hm := hmap.2.1 i hi
  have hleft : n - i = k + 1 := by dsimp [i]; omega
  rw [hleft] at hm
  simp only [Nat.succ_sub_one] at hm
  have hC : C k - C (k + 1) = -(u i • (A i - A (i + 1))) := by
    rw [← hm]
    abel
  have hui0 : 0 < u i := hu_pos i (by omega)
  have hq : 1 ≤ conjugateExponent p := (O3.one_lt_conjugateExponent hp).le
  have hnorm : lpNorm (conjugateExponent p) (C k - C (k + 1)) =
      u i * lpNorm (conjugateExponent p) (A i - A (i + 1)) := by
    change O3.lpNorm (conjugateExponent p) (C k - C (k + 1)) =
      u i * O3.lpNorm (conjugateExponent p) (A i - A (i + 1))
    rw [hC, O3.lpNorm_neg (conjugateExponent p),
      O3.Stage2RouteC.lpNorm_smul hq,
      abs_of_pos hui0]
  have hindex : n - 1 - k = i := rfl
  have hden : n - (k + 1) = i := by dsimp [i]; omega
  rw [hindex, hden, hnorm]
  field_simp

private lemma alpha_block (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : AboveCoefficientAssumptions n u dw alpha c b)
    (A B C D : VectorSeq d) (hmap : BelowResidualMap n u A B C D) :
    (∑ k ∈ Finset.range n,
      O3.pairing (weightedSum (k + 1) (alpha (k + 1)) A) (B (k + 1))) =
    ∑ k ∈ Finset.range n,
      O3.pairing (dualP n u C k)
        (weightedSum (k + 1) (fun i => alpha (n - i) (n - 1 - k)) D) := by
  have hP := dualP_map n hn u dw alpha c b hcoeff A B C D hmap
  have hD := hmap.2.2
  calc
    (∑ k ∈ Finset.range n,
      O3.pairing (weightedSum (k + 1) (alpha (k + 1)) A) (B (k + 1))) =
        ∑ k ∈ Finset.range n,
          dw k * O3.pairing (A k) (B (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn := Finset.mem_range.mp hk
      rw [alpha_weighted_primal n u dw alpha c b hcoeff A k hkn,
        pairing_smul_left]
    _ = ∑ k ∈ Finset.range n,
        dw (n - 1 - k) *
          O3.pairing (A (n - 1 - k)) (B (n - 1 - k + 1)) := by
      exact (Finset.sum_range_reflect
        (fun k => dw k * O3.pairing (A k) (B (k + 1))) n).symm
    _ = ∑ k ∈ Finset.range n,
      O3.pairing (dualP n u C k)
        (weightedSum (k + 1) (fun i => alpha (n - i) (n - 1 - k)) D) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn := Finset.mem_range.mp hk
      have hidx : n - 1 - k = n - k - 1 := by omega
      have hBidx : n - k = n - 1 - k + 1 := by omega
      rw [hP k hkn,
        alpha_weighted_dual n u dw alpha c b hcoeff D k hkn,
        pairing_smul_right, hD k (by omega)]
      rw [hidx, hBidx]
      simp only [Nat.succ_sub_one]

private lemma b_block (n : ℕ) (u : ScalarSeq)
    (b : ScalarMatrix) (A B C D X : VectorSeq d)
    (hb00 : b 0 0 = -1) (hAn : A (n + 1) = 0)
    (hX : BelowXRecurrence n b B X)
    (hmap : BelowResidualMap n u A B C D) :
    -(∑ k ∈ Finset.range (n + 1),
        u k * O3.pairing (A k - A (k + 1)) (X k)) =
      ∑ k ∈ Finset.range (n + 1),
        O3.pairing
          (weightedSum (k + 1) (fun i => b (n - i) (n - k)) C)
          (D k) := by
  let Y : VectorSeq d := fun k => if k ≤ n then C (n - k) else 0
  have hY : ∀ k ≤ n,
      u k • (A k - A (k + 1)) = Y k - Y (k + 1) := by
    intro k hk
    by_cases hkn : k < n
    · have hm := hmap.2.1 k hkn
      have hsub : n - (k + 1) = n - k - 1 := by omega
      dsimp [Y]
      rw [ite_eq_left hk, ite_eq_left (by omega), hsub]
      exact hm.symm
    · have hkeq : k = n := by omega
      subst k
      dsimp [Y]
      simp only [le_refl, ↓reduceIte, Nat.sub_self,
        sub_zero, hAn]
      simpa using hmap.1.symm
  have hYlast : Y (n + 1) = 0 := by simp [Y]
  have hYzero : Y 0 = C n := by simp [Y]
  have hprimal :
      -(∑ k ∈ Finset.range (n + 1),
          u k * O3.pairing (A k - A (k + 1)) (X k)) =
        -O3.pairing (Y 0) (X 0) +
          ∑ k ∈ Finset.range n,
            O3.pairing (Y (k + 1)) (X k - X (k + 1)) := by
    have hab := pairing_abel n Y X
    rw [hYlast] at hab
    have hzero : O3.pairing (0 : Point d) (X n) = 0 := by
      simp [O3.pairing]
    rw [hzero, sub_zero] at hab
    have hsum :
        (∑ k ∈ Finset.range (n + 1),
          u k * O3.pairing (A k - A (k + 1)) (X k)) =
        ∑ k ∈ Finset.range (n + 1),
          O3.pairing (Y k - Y (k + 1)) (X k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < n + 1 := Finset.mem_range.mp hk
      have hkle : k ≤ n := by omega
      rw [← pairing_smul_left, hY k hkle]
    have hneg :
        (∑ k ∈ Finset.range n,
          O3.pairing (Y (k + 1)) (X (k + 1) - X k)) =
        -(∑ k ∈ Finset.range n,
          O3.pairing (Y (k + 1)) (X k - X (k + 1))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [pairing_sub_right]
      ring
    rw [hsum, hab, hneg]
    ring
  have hrow :
      -O3.pairing (Y 0) (X 0) +
          (∑ k ∈ Finset.range n,
            O3.pairing (Y (k + 1)) (X k - X (k + 1))) =
        ∑ r ∈ Finset.range (n + 1),
          O3.pairing (Y r) (weightedSum (r + 1) (b r) B) := by
    rw [Finset.sum_range_succ']
    have hbase : weightedSum 1 (b 0) B = -(B 0) := by
      ext j
      simp [weightedSum, hb00]
    rw [hbase, hX.1]
    have hpairneg : O3.pairing (Y 0) (-(B 0)) =
        -O3.pairing (Y 0) (B 0) := by
      simp [O3.pairing, Finset.sum_neg_distrib]
    rw [hpairneg]
    have hsums :
        (∑ k ∈ Finset.range n,
          O3.pairing (Y (k + 1)) (X k - X (k + 1))) =
        ∑ k ∈ Finset.range n,
          O3.pairing (Y (k + 1))
            (weightedSum (k + 2) (b (k + 1)) B) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn := Finset.mem_range.mp hk
      have hxk := hX.2 k hkn
      rw [hxk]
      congr 1
      abel
    rw [hsums]
    abel
  have hrow_triangle :
      (∑ r ∈ Finset.range (n + 1),
          O3.pairing (Y r) (weightedSum (r + 1) (b r) B)) =
        ∑ j ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (n - j + 1),
            b (j + l) j * O3.pairing (C (n - (j + l))) (B j) := by
    calc
      (∑ r ∈ Finset.range (n + 1),
          O3.pairing (Y r) (weightedSum (r + 1) (b r) B)) =
        ∑ r ∈ Finset.range (n + 1),
          ∑ j ∈ Finset.range (r + 1),
            b r j * O3.pairing (C (n - r)) (B j) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrlt : r < n + 1 := Finset.mem_range.mp hr
          have hrn : r ≤ n := by omega
          rw [pairing_weightedSum_right]
          dsimp [Y]
          rw [ite_eq_left hrn]
      _ = ∑ j ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (n - j + 1),
            b (j + l) j * O3.pairing (C (n - (j + l))) (B j) := by
          exact (triangle_sum
            (fun r j => b r j * O3.pairing (C (n - r)) (B j)) n).symm
  have hdual_triangle :
      (∑ k ∈ Finset.range (n + 1),
        O3.pairing
          (weightedSum (k + 1) (fun i => b (n - i) (n - k)) C)
          (D k)) =
        ∑ j ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (n - j + 1),
            b (j + l) j * O3.pairing (C (n - (j + l))) (B j) := by
    rw [← Finset.sum_range_reflect
      (fun k => O3.pairing
        (weightedSum (k + 1) (fun i => b (n - i) (n - k)) C) (D k))
      (n + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < n + 1 := Finset.mem_range.mp hj
    have hjn : j ≤ n := by omega
    have hout : n + 1 - 1 - j = n - j := by omega
    rw [hout, hmap.2.2 (n - j) (by omega), show n - (n - j) = j by omega]
    rw [pairing_weightedSum_left]
    have href := Finset.sum_range_reflect
      (fun i => b (n - i) j * O3.pairing (C i) (B j)) (n - j + 1)
    rw [← href]
    apply Finset.sum_congr rfl
    intro l hl
    have hln : l < n - j + 1 := Finset.mem_range.mp hl
    have hidx : n - (n - j + 1 - 1 - l) = j + l := by omega
    have hcidx : n - j + 1 - 1 - l = n - (j + l) := by omega
    rw [hidx, hcidx]
  rw [hprimal, hrow, hrow_triangle, hdual_triangle]

end V7.Stage4AboveTwoIdentity

namespace V7

theorem abovePointwiseResidualIdentity : AbovePointwiseResidualIdentityStatement := by
  intro p hp d n hn u dw alpha c b Omega hcoeff heven
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A B
    exact ⟨Stage4AboveTwoIdentity.forwardC n u A, (fun i => B (n - i)),
      Stage4AboveTwoIdentity.forward_map n u A B⟩
  · intro C D
    exact ⟨Stage4AboveTwoIdentity.inverseA n u C, (fun i => D (n - i)),
      Stage4AboveTwoIdentity.inverse_map n hn u dw alpha c b hcoeff C D⟩
  · intro A B C₁ D₁ C₂ D₂ hmap₁ hmap₂
    have h₁ := Stage4AboveTwoIdentity.map_determined_forward n u A B C₁ D₁ hmap₁
    have h₂ := Stage4AboveTwoIdentity.map_determined_forward n u A B C₂ D₂ hmap₂
    constructor
    · intro k hk
      exact (h₁.1 k hk).trans (h₂.1 k hk).symm
    · intro k hk
      exact (h₁.2 k hk).trans (h₂.2 k hk).symm
  · intro A₁ B₁ A₂ B₂ C D hmap₁ hmap₂
    have h₁ := Stage4AboveTwoIdentity.map_determined_inverse
      n hn u dw alpha c b hcoeff A₁ B₁ C D hmap₁
    have h₂ := Stage4AboveTwoIdentity.map_determined_inverse
      n hn u dw alpha c b hcoeff A₂ B₂ C D hmap₂
    constructor
    · intro k hk
      exact (h₁.1 k hk).trans (h₂.1 k hk).symm
    · intro k hk
      exact (h₁.2 k hk).trans (h₂.2 k hk).symm
  · intro A B C D X hAn hX hmap
    have hnorm := Stage4AboveTwoIdentity.norm_block
      p (by linarith) n hn u dw alpha c b hcoeff A B C D hmap
    have homega := Stage4AboveTwoIdentity.omega_block n Omega heven B D hmap.2.2
    have halpha := Stage4AboveTwoIdentity.alpha_block
      n hn u dw alpha c b hcoeff A B C D hmap
    have hb := Stage4AboveTwoIdentity.b_block
      n u b A B C D X hcoeff.2.2.2.2.1 hAn hX hmap
    unfold AbovePrimalResidual AboveDualResidual BelowPrimalResidual BelowDualResidual
    change
      (∑ k ∈ Finset.range n,
          (u k / 2) *
            lpNorm (conjugateExponent p) (A k - A (k + 1)) ^ (2 : ℕ)) +
        (∑ k ∈ Finset.range n, Omega (B k - B (k + 1))) +
        (∑ k ∈ Finset.range n,
          pairing (weightedSum (k + 1) (alpha (k + 1)) A) (B (k + 1))) -
        (∑ k ∈ Finset.range (n + 1),
          u k * pairing (A k - A (k + 1)) (X k)) =
      (∑ k ∈ Finset.range n,
          ((1 / u (n - (k + 1))) / 2) *
            lpNorm (conjugateExponent p) (C k - C (k + 1)) ^ (2 : ℕ)) +
        (∑ k ∈ Finset.range n, Omega (D k - D (k + 1))) +
        (∑ k ∈ Finset.range (n + 1),
          pairing
            (weightedSum (k + 1) (fun i => b (n - i) (n - k)) C) (D k)) +
        (∑ k ∈ Finset.range n,
          pairing (Stage4AboveTwoIdentity.dualP n u C k)
            (weightedSum (k + 1)
              (fun i => alpha (n - i) (n - 1 - k)) D))
    rw [hnorm, homega, halpha, sub_eq_add_neg, hb]
    ring

end V7
