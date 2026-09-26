/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.ResidualAlgebra
public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwo.Primal

/-!
The pointwise primal-dual residual identity for the below-two coefficient recurrences.
-/

@[expose] public section

open scoped BigOperators

namespace V7.Stage3BelowTwo

export ResidualAlgebra (triangle_sum dualP)

open ResidualAlgebra

private lemma coefficient_u_pos (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b) :
    ∀ i ≤ n, 0 < u i := by
  intro i hi
  rcases hcoeff with ⟨hu0, hun, hdwn, hc00, hb00, htable, hc, hrowsc, hsupport, hrowsb⟩
  by_cases hin : i < n
  · rw [(htable i hin).1]
    positivity
  · have hin_eq : i = n := by omega
    rw [hin_eq, hun]
    have hpred : n - 1 < n := by omega
    rw [(htable (n - 1) hpred).1]
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity

private lemma inverse_map (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
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

private lemma map_determined_inverse (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
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

lemma alpha_weighted_primal (n : ℕ) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
    (A : VectorSeq d) (k : ℕ) (hk : k < n) :
    weightedSum (k + 1) (alpha (k + 1)) A = dw k • A k := by
  have halpha := (hcoeff.2.2.2.2.2.1 k hk).2.2
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
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
    (D : VectorSeq d) (k : ℕ) (hk : k < n) :
    weightedSum (k + 1) (fun i => alpha (n - i) (n - 1 - k)) D =
      dw (n - k - 1) • D k := by
  have hi : n - k - 1 < n := by omega
  have halpha := (hcoeff.2.2.2.2.2.1 (n - k - 1) hi).2.2
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
    have ha := (hcoeff.2.2.2.2.2.1 (n - i - 1) hri).2.2 (n - 1 - k)
    rw [hrow, ha]
    have hne : n - 1 - k ≠ n - i - 1 := by omega
    simp [hne]
  · simp

private lemma dualP_map (n : ℕ) (hn : 1 ≤ n) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
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

private lemma norm_block (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n)
    (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
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
    (hcoeff : BelowCoefficientAssumptions n u dw alpha c b)
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

end V7.Stage3BelowTwo

namespace V7

theorem belowPointwiseResidualIdentity : BelowPointwiseResidualIdentityStatement := by
  intro p hp hp2 d n hn u dw alpha c b Omega hcoeff heven
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A B
    exact ⟨ResidualAlgebra.forwardC n u A, (fun i => B (n - i)),
      ResidualAlgebra.forward_map n u A B⟩
  · intro C D
    exact ⟨ResidualAlgebra.inverseA n u C, (fun i => D (n - i)),
      Stage3BelowTwo.inverse_map n hn u dw alpha c b hcoeff C D⟩
  · intro A B C₁ D₁ C₂ D₂ hmap₁ hmap₂
    have h₁ := ResidualAlgebra.map_determined_forward n u A B C₁ D₁ hmap₁
    have h₂ := ResidualAlgebra.map_determined_forward n u A B C₂ D₂ hmap₂
    constructor
    · intro k hk
      exact (h₁.1 k hk).trans (h₂.1 k hk).symm
    · intro k hk
      exact (h₁.2 k hk).trans (h₂.2 k hk).symm
  · intro A₁ B₁ A₂ B₂ C D hmap₁ hmap₂
    have h₁ := Stage3BelowTwo.map_determined_inverse
      n hn u dw alpha c b hcoeff A₁ B₁ C D hmap₁
    have h₂ := Stage3BelowTwo.map_determined_inverse
      n hn u dw alpha c b hcoeff A₂ B₂ C D hmap₂
    constructor
    · intro k hk
      exact (h₁.1 k hk).trans (h₂.1 k hk).symm
    · intro k hk
      exact (h₁.2 k hk).trans (h₂.2 k hk).symm
  · intro A B C D X hAn hX hmap
    have hnorm := Stage3BelowTwo.norm_block
      p hp n hn u dw alpha c b hcoeff A B C D hmap
    have homega := ResidualAlgebra.omega_block n Omega heven B D hmap.2.2
    have halpha := Stage3BelowTwo.alpha_block
      n hn u dw alpha c b hcoeff A B C D hmap
    have hb := ResidualAlgebra.b_block
      n u b A B C D X hcoeff.2.2.2.2.1 hAn hX hmap
    unfold BelowPrimalResidual BelowDualResidual
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
          pairing (Stage3BelowTwo.dualP n u C k)
            (weightedSum (k + 1)
              (fun i => alpha (n - i) (n - 1 - k)) D))
    rw [hnorm, homega, halpha, sub_eq_add_neg, hb]
    ring

end V7
