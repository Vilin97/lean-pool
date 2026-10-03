/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.V0Table
public import LeanPool.Zeta32.PrimeEdge.EntryBounds
public import Mathlib.Tactic.NormNum.Prime

/-! **S3**: the `X`-free block-diagonal reference matrix of the proof notes, §6 and
its determinant `p^{Σπ} · (unit)`. Blocks: `Ref_{⟨b,i⟩,⟨b,k⟩} = p^{c_b+i+k} w_b V⁰(u^{i+k}
r_type)`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

/-- The exceptional primes of Proposition 6. -/
def exceptional : Finset ℕ := {11, 67, 193, 283, 367, 110731}

/-- The reference matrix for unit weights `w`. -/
noncomputable def Ref (p : ℕ) (w : ℕ → ℚ) : Matrix (Idx p) (Idx p) ℚ[X] :=
  Matrix.of fun a c => if a.1 = c.1 then
    C ((p : ℚ) ^ (colBase p a.1.val + a.2.val + c.2.val) * w a.1.val *
      blockMoment p a.1.val (a.2.val + c.2.val)) else 0

/-- The Hankel determinant of the fixed block of class `b`. -/
noncomputable def hankelDet (p : ℕ) (b : Fin p) : ℚ :=
  (Matrix.of fun i k : Fin (mult p b.val) => blockMoment p b.val (i.val + k.val)).det

/-- The unit of the reference determinant. -/
noncomputable def refUnit (p : ℕ) (w : ℕ → ℚ) : ℚ :=
  ∏ b : Fin p, (w b.val ^ mult p b.val * hankelDet p b)

/-- `Σ π` as an integer. -/
def levelSum (p : ℕ) : ℤ := ∑ a : Idx p, level p a

/-- **S3a (block diagonal determinant).** Scaling rows by `p^{c_b+i}` and columns by `p^k`
inside each class block (`det_mul_row`, `det_mul_column`, `BlockTriangular.det` or
`det_blockDiagonal'`-type reindexing). -/
theorem Ref_det [Fact p.Prime] (w : ℕ → ℚ) :
    (Ref p w).det = C ((p : ℚ) ^ levelSum p * refUnit p w) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- the unscaled block-diagonal core
  let N : Matrix (Idx p) (Idx p) ℚ := Matrix.blockDiagonal' fun b : Fin p =>
    Matrix.of fun i k : Fin (mult p b.val) => w b.val * blockMoment p b.val (i.val + k.val)
  have hRef : Ref p w = (C : ℚ →+* ℚ[X]).mapMatrix
      (Matrix.of fun a c : Idx p => (p : ℚ) ^ (colBase p a.1.val + a.2.val) *
        ((p : ℚ) ^ (c.2.val : ℤ) * N a c)) := by
    refine Matrix.ext fun a c => ?_
    obtain ⟨b, i⟩ := a
    obtain ⟨b', k⟩ := c
    simp only [Ref, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, N,
      Matrix.blockDiagonal'_apply']
    by_cases h : b = b'
    · subst h
      simp only [dite_true, ite_true, cast_eq]
      congr 1
      rw [zpow_add₀ hp0 (colBase p b.val + (i.val : ℤ))]
      ring
    · simp [h]
  -- determinant of a block-diagonal matrix indexed by `Fin p`
  have hblock : ∀ d : ∀ b : Fin p, Matrix (Fin (mult p b.val)) (Fin (mult p b.val)) ℚ,
      (Matrix.blockDiagonal' d).det = ∏ b, (d b).det := by
    intro d
    rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [← Matrix.det_submatrix_equiv_self (Equiv.sigmaSubtype b).symm]
    congr 1
    ext i k
    simp only [Matrix.submatrix_apply, Matrix.toSquareBlock_def]
    change Matrix.blockDiagonal' d ⟨b, i⟩ ⟨b, k⟩ = d b i k
    simp
  have hNdet : N.det = refUnit p w := by
    rw [hblock]
    unfold refUnit hankelDet
    refine Finset.prod_congr rfl fun b _ => ?_
    have hsm : (Matrix.of fun i k : Fin (mult p b.val) =>
        w b.val * blockMoment p b.val (i.val + k.val)) =
        w b.val • Matrix.of fun i k : Fin (mult p b.val) => blockMoment p b.val (i.val + k.val)
          := by
      ext i k; simp
    rw [hsm, Matrix.det_smul, Fintype.card_fin]
  have h1 := Matrix.det_mul_column (fun a : Idx p => (p : ℚ) ^ (colBase p a.1.val + a.2.val))
    (Matrix.of fun a c : Idx p => (p : ℚ) ^ (c.2.val : ℤ) * N a c)
  have h2 := Matrix.det_mul_row (fun c : Idx p => (p : ℚ) ^ (c.2.val : ℤ)) N
  simp only [Matrix.of_apply] at h1
  rw [hRef, ← RingHom.map_det, h1, h2, hNdet, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 2
  have hprod : ∀ (s : Finset (Idx p)) (f : Idx p → ℤ),
      ∏ a ∈ s, (p : ℚ) ^ f a = (p : ℚ) ^ ∑ a ∈ s, f a := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hp0]
  simp_rw [← zpow_add₀ hp0]
  rw [hprod]
  congr 1
  unfold levelSum level
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **S3b (the three fixed determinants).** `hankelDet` is `det M₀`, `det lowBlockMatrix` or `det
highBlockMatrix`. -/
theorem hankelDet_eq (b : Fin p) :
    hankelDet p b =
      if b.val = 0 then Matrix.det M₀ else if b.val + 5 ≤ p then Matrix.det lowBlockMatrix
      else Matrix.det highBlockMatrix := by
  have hcast : ∀ {m N : ℕ} (h : m = N) (F : ℕ → ℚ),
      (Matrix.of fun i k : Fin m => F (i.val + k.val)).det =
        (Matrix.of fun i k : Fin N => F (i.val + k.val)).det := by
    intro m N h F; subst h; rfl
  unfold hankelDet
  split_ifs with h0 hL
  · rw [hcast (show mult p b.val = 4 by simp [mult, h0]) (blockMoment p b.val)]
    congr 1; ext i k
    simp only [Matrix.of_apply, M₀, h0]
    exact blockMoment_zero p ⟨i.val + k.val, by omega⟩
  · rw [hcast (show mult p b.val = 3 by simp [mult, h0, hL]) (blockMoment p b.val)]
    congr 1; ext i k
    simp only [Matrix.of_apply, lowBlockMatrix]
    exact blockMoment_low h0 hL ⟨i.val + k.val, by omega⟩
  · rw [hcast (show mult p b.val = 2 by simp [mult, h0, hL]) (blockMoment p b.val)]
    congr 1; ext i k
    simp only [Matrix.of_apply, highBlockMatrix]
    exact blockMoment_high h0 hL ⟨i.val + k.val, by omega⟩

lemma padicValRat_eq_zero_of_not_dvd [hp : Fact p.Prime] {z d : ℕ} (hz : z ≠ 0) (hd : d ≠ 0)
    (hpz : ¬ p ∣ z) (hpd : ¬ p ∣ d) : padicValRat p ((z : ℚ) / d) = 0 := by
  rw [padicValRat.div (by exact_mod_cast hz) (by exact_mod_cast hd), padicValRat.of_nat,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpz, padicValNat.eq_zero_of_not_dvd hpd]
  simp

lemma not_dvd_of_prime_factor [hp : Fact p.Prime] {q : ℕ} (hq : q.Prime) (hpq : p ≠ q) :
    ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp h)

lemma not_dvd_two_three_pow [hp : Fact p.Prime] (hp7 : 7 ≤ p) (a b : ℕ) : ¬ p ∣ 2 ^ a * 3 ^ b := by
  intro h
  rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp (hp.out.dvd_of_dvd_pow h)
    omega

lemma VG_of_mul_int [hp : Fact p.Prime] (hp7 : 7 ≤ p) {q : ℚ} (z : ℤ) (hq : q * 1296 = z) :
    VG p q 0 := by
  have h0 : ((2 ^ 4 * 3 ^ 4 : ℕ) : ℚ) ≠ 0 := by norm_num
  have hv : padicValRat p ((2 ^ 4 * 3 ^ 4 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (not_dvd_two_three_pow hp7 4 4)]
    simp
  have hinv := VG.inv (p := p) (r := 0)  (by rw [hv]; simp)
  have hmul := (VG.intCast (p := p) z).mul hinv
  have he : q = (z : ℚ) * ((2 ^ 4 * 3 ^ 4 : ℕ) : ℚ)⁻¹ := by
    rw [← hq]; push_cast; ring
  rw [he]
  simpa using hmul

lemma zeroMoment_int (i : Fin 7) : ∃ z : ℤ, zeroMoment i * 1296 = z := by
  fin_cases i
  · exact ⟨1, by simp [zeroMoment]⟩
  · exact ⟨14, by simp [zeroMoment]; norm_num⟩
  · exact ⟨3130, by simp [zeroMoment]; norm_num⟩
  · exact ⟨-31150, by simp [zeroMoment]; norm_num⟩
  · exact ⟨202522, by simp [zeroMoment]; norm_num⟩
  · exact ⟨-1090510, by simp [zeroMoment]; norm_num⟩
  · exact ⟨5299858, by simp [zeroMoment]; norm_num⟩

lemma lowMoment_int (i : Fin 5) : ∃ z : ℤ, lowMoment i * 1296 = z := by
  fin_cases i
  · exact ⟨3130, by simp [lowMoment]; norm_num⟩
  · exact ⟨-31150, by simp [lowMoment]; norm_num⟩
  · exact ⟨202522, by simp [lowMoment]; norm_num⟩
  · exact ⟨-1090510, by simp [lowMoment]; norm_num⟩
  · exact ⟨5299858, by simp [lowMoment]; norm_num⟩

lemma highMoment_int (i : Fin 3) : ∃ z : ℤ, highMoment i * 1296 = z := by
  fin_cases i
  · exact ⟨-18630, by simp [highMoment]; norm_num⟩
  · exact ⟨77922, by simp [highMoment]; norm_num⟩
  · exact ⟨-280422, by simp [highMoment]; norm_num⟩

/-- **S2b-4'.** The fixed moments in the range used by one class block are `p`-integral for
`p ≥ 7` (denominators divide `2⁴3⁴`). -/
theorem blockMoment_VG [Fact p.Prime] (hp7 : 7 ≤ p) (b e : ℕ) (he : e + 1 < 2 * mult p b) :
    VG p (blockMoment p b e) 0 := by
  by_cases h0 : b = 0
  · subst h0
    have he' : e < 7 := by simp [mult] at he; omega
    obtain ⟨z, hz⟩ := zeroMoment_int ⟨e, he'⟩
    rw [show e = (⟨e, he'⟩ : Fin 7).val from rfl, blockMoment_zero]
    exact VG_of_mul_int hp7 z hz
  · by_cases hL : b + 5 ≤ p
    · have he' : e < 5 := by simp [mult, h0, hL] at he; omega
      obtain ⟨z, hz⟩ := lowMoment_int ⟨e, he'⟩
      rw [show e = (⟨e, he'⟩ : Fin 5).val from rfl, blockMoment_low h0 hL]
      exact VG_of_mul_int hp7 z hz
    · have he' : e < 3 := by simp [mult, h0, hL] at he; omega
      obtain ⟨z, hz⟩ := highMoment_int ⟨e, he'⟩
      rw [show e = (⟨e, he'⟩ : Fin 3).val from rfl, blockMoment_high h0 hL]
      exact VG_of_mul_int hp7 z hz

lemma unit_of_ratio [hp : Fact p.Prime] {q : ℚ} {z1 z2 d : ℕ} (hq : q = -((z1 * z2 : ℕ) : ℚ) / d)
    (h1 : z1.Prime) (h2 : z2.Prime) (hp1 : p ≠ z1) (hp2 : p ≠ z2) (hd : d ≠ 0) (hpd : ¬ p ∣ d) :
    q ≠ 0 ∧ padicValRat p q = 0 := by
  have hz : z1 * z2 ≠ 0 := Nat.mul_ne_zero h1.ne_zero h2.ne_zero
  have hpz : ¬ p ∣ z1 * z2 := fun h => by
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · exact not_dvd_of_prime_factor h1 hp1 h
    · exact not_dvd_of_prime_factor h2 hp2 h
  subst hq
  refine ⟨?_, ?_⟩
  · have h1 : ((z1 * z2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hz
    have h2 : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    exact div_ne_zero (neg_ne_zero.mpr h1) h2
  · rw [neg_div, padicValRat.neg]
    exact padicValRat_eq_zero_of_not_dvd hz hd hpz hpd

/-- **S3c.** The three fixed determinants are `p`-adic units for `p ≥ 7`, `p ∉ exceptional`. -/
theorem hankelDet_unit [Fact p.Prime] (hp7 : 7 ≤ p) (hE : p ∉ exceptional) (b : Fin p) :
    hankelDet p b ≠ 0 ∧ padicValRat p (hankelDet p b) = 0 := by
  have hE' : p ≠ 11 ∧ p ≠ 67 ∧ p ≠ 193 ∧ p ≠ 283 ∧ p ≠ 367 ∧ p ≠ 110731 := by
    simp only [exceptional, Finset.mem_insert, Finset.mem_singleton, not_or] at hE
    exact hE
  obtain ⟨h11, h67, h193, h283, h367, h110731⟩ := hE'
  rw [hankelDet_eq b]
  split_ifs
  · refine unit_of_ratio (z1 := 67) (z2 := 193) (d := 2 ^ 2 * 3 ^ 4) ?_ (by norm_num)
      (by norm_num) h67 h193 (by norm_num) (not_dvd_two_three_pow hp7 2 4)
    rw [det_M₀]; norm_num
  · refine unit_of_ratio (z1 := 283) (z2 := 110731) (d := 2 ^ 4 * 3 ^ 4) ?_ (by norm_num)
      (by norm_num) h283 h110731 (by norm_num) (not_dvd_two_three_pow hp7 4 4)
    rw [det_M_L]; norm_num
  · refine unit_of_ratio (z1 := 11) (z2 := 367) (d := 2 ^ 3 * 3 ^ 0) ?_ (by norm_num)
      (by norm_num) h11 h367 (by norm_num) (not_dvd_two_three_pow hp7 3 0)
    rw [det_M_H]; norm_num

/-- **S3.** The reference unit is a `p`-adic unit when all `w_b` are. -/
theorem refUnit_unit [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hE : p ∉ exceptional) (w : ℕ → ℚ)
    (hw : ∀ b < p, w b ≠ 0 ∧ padicValRat p (w b) = 0) :
    refUnit p w ≠ 0 ∧ padicValRat p (refUnit p w) = 0 := by
  have hf : ∀ b : Fin p, w b.val ^ mult p b.val * hankelDet p b ≠ 0 ∧
      padicValRat p (w b.val ^ mult p b.val * hankelDet p b) = 0 := fun b => by
    obtain ⟨hw0, hwv⟩ := hw b.val b.isLt
    obtain ⟨hh0, hhv⟩ := hankelDet_unit hp7 hE b
    refine ⟨mul_ne_zero (pow_ne_zero _ hw0) hh0, ?_⟩
    rw [padicValRat.mul (pow_ne_zero _ hw0) hh0, padicValRat.pow (w b.val), hwv, hhv]
    simp
  refine ⟨Finset.prod_ne_zero_iff.mpr fun b _ => (hf b).1, ?_⟩
  unfold refUnit
  rw [padicValRat_finset_prod _ _ fun b _ => (hf b).1]
  exact Finset.sum_eq_zero fun b _ => (hf b).2

end Zeta32.PrimeEdge

end
