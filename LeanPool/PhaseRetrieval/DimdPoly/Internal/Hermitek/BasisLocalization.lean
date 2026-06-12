/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # BasisLocalization.lean
  Statement-only scaffold for annulus localization of the true-level basis.

  Scaffolding notes:
  - `Localization/basis_localization.md`
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.ModulusRigidity
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.MissingMathlib
import Mathlib.Analysis.SpecialFunctions.Pochhammer
import LeanPool.PhaseRetrieval.Constant.Internal.LaplaceFactorial

/-! # BasisLocalization -/


open Complex MeasureTheory Real Finset

noncomputable section

namespace HermitekLEAN

private theorem hermiteSeries_single (k n : ℕ) :
    hermiteSeries k (fun m : ℕ => if m = n then (1 : ℂ) else 0) = Phi k n := by
  funext z
  unfold hermiteSeries
  rw [tsum_eq_single n]
  · simp
  · intro b hb
    simp [hb]

private theorem circleSeries_l2_single (k n : ℕ) (r : ℝ) (hr : 0 < r) :
    circleL2Sq (circleSeries k (fun m : ℕ => if m = n then (1 : ℂ) else 0) r) =
      |qkn k n r| ^ 2 := by
  have hPhi : Phi k n ∈ Hk k := Phi_mem_Hk k n
  have hseries : Phi k n = hermiteSeries k (fun m : ℕ => if m = n then (1 : ℂ) else 0) :=
    (hermiteSeries_single k n).symm
  have hsummable :
      Summable (fun m : ℕ => ‖if m = n then (1 : ℂ) else 0‖ ^ 2) := by
    classical
    apply summable_of_hasFiniteSupport
    refine Set.Finite.subset (Set.finite_singleton n) ?_
    intro m hm
    by_contra hmn
    have hmne : ‖if m = n then (1 : ℂ) else 0‖ ^ 2 ≠ 0 := by
      simpa [Function.mem_support] using hm
    have hEq : m = n := by
      by_contra hneq
      apply hmne
      simp [hneq]
    exact hmn (by simp [hEq])
  have h :=
    circleSeries_l2_identity
      (G := Phi k n)
      (g := fun m : ℕ => if m = n then (1 : ℂ) else 0)
      hPhi hseries hsummable r hr
  rw [tsum_eq_single n] at h
  · simpa using h
  · intro b hb
    simp [hb]

private theorem qkn_zero (k : ℕ) {r : ℝ} (hr : 0 < r) : qkn k 0 r = 1 := by
  rw [qkn_explicit hr]
  simp

private theorem qkn_descFactorial_form
    (k n : ℕ) {r : ℝ}
    (hr : 0 < r)
    (hkn : k ≤ n) :
    qkn k n r =
      (1 / Real.sqrt (Nat.factorial n : ℝ)) *
        Finset.sum (Finset.range (k + 1)) (fun j =>
          ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
            (Nat.descFactorial n j : ℝ) * r ^ ((n : ℤ) - 2 * (j : ℤ))) := by
  rw [qkn_explicit hr, Nat.min_eq_left hkn]
  refine congrArg (fun x => (1 / Real.sqrt (Nat.factorial n : ℝ)) * x) ?_
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjk : j ≤ k := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjn : j ≤ n := le_trans hjk hkn
  have hmul : (Nat.factorial (n - j) : ℝ) * (Nat.descFactorial n j : ℝ) = Nat.factorial n := by
    exact_mod_cast (Nat.factorial_mul_descFactorial (n := n) (k := j) hjn)
  have hmul' :
    (Nat.factorial n : ℝ) = (Nat.descFactorial n j : ℝ) * (Nat.factorial (n - j) : ℝ) := by
    simpa [mul_comm] using hmul.symm
  have hden : (Nat.factorial (n - j) : ℝ) ≠ 0 := by positivity
  have hcoeff :
      (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) = (Nat.descFactorial n j : ℝ) := by
    exact (div_eq_iff hden).2 hmul'
  rw [hcoeff]

private def qknPoly (k n : ℕ) (u : ℝ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) (fun j =>
    ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) * (Nat.descFactorial n j : ℝ) * u ^ (k - j))

-- Nat-level coefficient identity for the Charlier recurrence (s = s'+2 case).
private theorem charlier_coeff_nat (k n s' : ℕ) :
    (k + 2).choose (s' + 2) * n.descFactorial (s' + 2) +
    (k + 1) * n * (k.choose s' * (n - 1).descFactorial s') =
    (k + 1).choose (s' + 2) * n.descFactorial (s' + 2) +
    n * ((k + 1).choose (s' + 1) * n.descFactorial (s' + 1)) := by
  have hpascal : (k + 2).choose (s' + 2) =
      (k + 1).choose (s' + 1) + (k + 1).choose (s' + 2) := by
    rw [show k + 2 = (k + 1) + 1 from by omega,
        show s' + 2 = (s' + 1) + 1 from by omega]
    exact Nat.choose_succ_succ (k + 1) (s' + 1)
  have hsuff : (k + 1).choose (s' + 1) * n.descFactorial (s' + 2) +
      (k + 1) * n * (k.choose s' * (n - 1).descFactorial s') =
      n * ((k + 1).choose (s' + 1) * n.descFactorial (s' + 1)) := by
    have hdf : n.descFactorial (s' + 2) = (n - (s' + 1)) * n.descFactorial (s' + 1) :=
      Nat.descFactorial_succ n (s' + 1)
    have hdf2 : n.descFactorial (s' + 1) = n * (n - 1).descFactorial s' := by
      cases n with
      | zero => simp
      | succ n => exact Nat.succ_descFactorial_succ n s'
    have habsorb : (s' + 1) * (k + 1).choose (s' + 1) = (k + 1) * k.choose s' := by
      rw [Nat.mul_comm (s' + 1), Nat.add_one_mul_choose_eq k s', Nat.mul_comm]
    rw [hdf, hdf2]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · by_cases hns : s' < n
      · have hkey : (k + 1).choose (s' + 1) * (n - (s' + 1)) +
            (k + 1) * k.choose s' = n * (k + 1).choose (s' + 1) := by
          rw [← habsorb,
              Nat.mul_comm ((k + 1).choose (s' + 1)) (n - (s' + 1)),
              Nat.mul_comm n, ← Nat.add_mul, Nat.sub_add_cancel hns,
              Nat.mul_comm]
        have h1 : (k + 1).choose (s' + 1) *
            ((n - (s' + 1)) * (n * (n - 1).descFactorial s')) =
            (k + 1).choose (s' + 1) * (n - (s' + 1)) *
              (n * (n - 1).descFactorial s') :=
          (Nat.mul_assoc _ _ _).symm
        have h2 : (k + 1) * n * (k.choose s' * (n - 1).descFactorial s') =
            (k + 1) * k.choose s' * (n * (n - 1).descFactorial s') := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        rw [h1, h2, ← Nat.add_mul, hkey, Nat.mul_assoc]
      · have hD : (n - 1).descFactorial s' = 0 := by
          rw [Nat.descFactorial_eq_zero_iff_lt]; omega
        simp [hD]
  calc (k + 2).choose (s' + 2) * n.descFactorial (s' + 2) +
      (k + 1) * n * (k.choose s' * (n - 1).descFactorial s')
      = ((k + 1).choose (s' + 1) + (k + 1).choose (s' + 2)) *
          n.descFactorial (s' + 2) +
        (k + 1) * n * (k.choose s' * (n - 1).descFactorial s') := by
          rw [hpascal]
    _ = (k + 1).choose (s' + 1) * n.descFactorial (s' + 2) +
        (k + 1).choose (s' + 2) * n.descFactorial (s' + 2) +
        (k + 1) * n * (k.choose s' * (n - 1).descFactorial s') := by
          rw [Nat.add_mul]
    _ = (k + 1).choose (s' + 2) * n.descFactorial (s' + 2) +
        ((k + 1).choose (s' + 1) * n.descFactorial (s' + 2) +
         (k + 1) * n * (k.choose s' * (n - 1).descFactorial s')) := by
          omega
    _ = (k + 1).choose (s' + 2) * n.descFactorial (s' + 2) +
        n * ((k + 1).choose (s' + 1) * n.descFactorial (s' + 1)) := by
          rw [hsuff]

private theorem qknPoly_succ_succ
    (k n : ℕ) (u : ℝ) :
    qknPoly (k + 2) n u =
      (u - n) * qknPoly (k + 1) n u - ((k + 1 : ℕ) : ℝ) * (n : ℝ) * qknPoly k (n - 1) u := by
  -- Reduce to polynomial equality via evaluation.
  let Pk : ℕ → ℕ → Polynomial ℝ := fun k n =>
    ∑ j ∈ Finset.range (k + 1),
      (Polynomial.C ((-1 : ℝ) ^ j * ↑(k.choose j) * ↑(n.descFactorial j)) *
        Polynomial.X ^ (k - j))
  have heval : ∀ K N : ℕ, (Pk K N).eval u = qknPoly K N u := by
    intro K N
    simp only [Pk, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    simp only [qknPoly, mul_comm, mul_left_comm]
  suffices hpoly :
      Pk (k + 2) n =
        (Polynomial.X - Polynomial.C (↑n : ℝ)) * Pk (k + 1) n -
          Polynomial.C ((↑(k + 1) : ℝ) * (↑n : ℝ)) * Pk k (n - 1) by
    have h1 := congr_arg (Polynomial.eval u) hpoly
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C] at h1
    rw [heval, heval, heval] at h1
    linarith
  have hcs : ∀ (K N m : ℕ),
      (Pk K N).coeff m =
        if m ≤ K then
          (-1 : ℝ) ^ (K - m) * ↑(K.choose (K - m)) * ↑(N.descFactorial (K - m))
        else 0 := by
    intro K N m
    simp only [Pk, Polynomial.finsetSum_coeff]
    by_cases hmK : m ≤ K
    · rw [if_pos hmK, Finset.sum_eq_single (K - m)]
      · have : K - (K - m) = m := Nat.sub_sub_self hmK
        rw [this, Polynomial.coeff_C_mul_X_pow]
        simp
      · intro j hj hjne
        rw [Polynomial.coeff_C_mul_X_pow]
        simp only [show m ≠ K - j from by
          intro h; have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          exact hjne (by omega), ite_false]
      · intro hnotmem; exfalso; apply hnotmem
        exact Finset.mem_range.mpr (by omega)
    · push Not at hmK
      rw [if_neg (by omega), Finset.sum_eq_zero]
      intro j hj
      rw [Polynomial.coeff_C_mul_X_pow]
      simp only [show m ≠ K - j from by
        have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj); omega, ite_false]
  ext m
  rw [hcs, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hcs]
  cases m with
  | zero =>
    have h0 : ((Polynomial.X - Polynomial.C (↑n : ℝ)) * Pk (k + 1) n).coeff 0 =
        -(↑n : ℝ) * (Pk (k + 1) n).coeff 0 := by
      simp [Polynomial.coeff_mul]
    rw [h0, hcs]
    simp only [Nat.zero_le, ite_true, Nat.sub_zero, show (0 : ℕ) ≤ k from Nat.zero_le k]
    have h := charlier_coeff_nat k n k
    have hR : (↑((k + 2).choose (k + 2) * n.descFactorial (k + 2) +
        (k + 1) * n * (k.choose k * (n - 1).descFactorial k)) : ℝ) =
      (↑((k + 1).choose (k + 2) * n.descFactorial (k + 2) +
        n * ((k + 1).choose (k + 1) * n.descFactorial (k + 1))) : ℝ) := by
      exact_mod_cast h
    simp only [Nat.choose_self,
      Nat.choose_eq_zero_of_lt (show k + 1 < k + 2 by omega),
      Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_zero] at hR
    simp only [Nat.choose_self]
    push_cast
    have hpow : (-1 : ℝ) ^ (k + 2) = (-1) ^ k := by ring
    have hpow1 : (-1 : ℝ) ^ (k + 1) = -(-1) ^ k := by ring
    rw [hpow, hpow1]
    have hR' : (↑(n.descFactorial (k + 2)) : ℝ) =
        ↑n * ↑(n.descFactorial (k + 1)) - (↑k + 1) * ↑n * ↑((n - 1).descFactorial k) := by
      linarith
    calc (-1 : ℝ) ^ k * (↑1) * ↑(n.descFactorial (k + 2))
        = (-1) ^ k * (↑n * ↑(n.descFactorial (k + 1)) -
            (↑k + 1) * ↑n * ↑((n - 1).descFactorial k)) := by rw [mul_one, hR']
      _ = -↑n * (-(-1) ^ k * (↑1) * ↑(n.descFactorial (k + 1))) -
            (↑k + 1) * ↑n * ((-1) ^ k * (↑1) * ↑((n - 1).descFactorial k)) := by ring
  | succ a =>
    rw [Polynomial.coeff_X_sub_C_mul, hcs, hcs]
    by_cases ha1 : k + 2 < a + 1
    · simp only [show ¬(a + 1 ≤ k + 2) from by omega, ite_false,
                  show ¬(a ≤ k + 1) from by omega, ite_false,
                  show ¬(a + 1 ≤ k + 1) from by omega, ite_false,
                  show ¬(a + 1 ≤ k) from by omega, ite_false]
      ring
    · push Not at ha1
      by_cases ha2 : a + 1 ≤ k
      · simp only [show a + 1 ≤ k + 2 from by omega, ite_true,
                    show a ≤ k + 1 from by omega, ite_true,
                    show a + 1 ≤ k + 1 from by omega, ite_true,
                    show a + 1 ≤ k from ha2, ite_true]
        have hnat := charlier_coeff_nat k n (k - 1 - a)
        have hs2 : k - 1 - a + 2 = k + 1 - a := by omega
        have hs1 : k - 1 - a + 1 = k - a := by omega
        have hk2a : k + 2 - (a + 1) = k + 1 - a := by omega
        have hk1a : k + 1 - (a + 1) = k - a := by omega
        have hka : k - (a + 1) = k - 1 - a := by omega
        rw [hs2, hs1] at hnat
        rw [hk2a, hk1a, hka]
        have hR :
            (↑((k + 2).choose (k + 1 - a) * n.descFactorial (k + 1 - a) +
            (k + 1) * n * (k.choose (k - 1 - a) *
              (n - 1).descFactorial (k - 1 - a))) : ℝ) =
          (↑((k + 1).choose (k + 1 - a) * n.descFactorial (k + 1 - a) +
            n * ((k + 1).choose (k - a) * n.descFactorial (k - a))) : ℝ) := by
          exact_mod_cast hnat
        push_cast at hR ⊢
        have hpow2 : ((-1 : ℝ) ^ (k + 1 - a)) = (-1) ^ (k - 1 - a) := by
          have : k + 1 - a = (k - 1 - a) + 2 := by omega
          rw [this]; ring
        have hpow1 : ((-1 : ℝ) ^ (k - a)) = -((-1) ^ (k - 1 - a)) := by
          have : k - a = (k - 1 - a) + 1 := by omega
          rw [this]; ring
        rw [hpow2, hpow1]
        set s := (-1 : ℝ) ^ (k - 1 - a)
        have : s * (↑((k + 2).choose (k + 1 - a)) *
            ↑(n.descFactorial (k + 1 - a))) =
          s * (↑((k + 1).choose (k + 1 - a)) *
              ↑(n.descFactorial (k + 1 - a)) +
            ↑n * (↑((k + 1).choose (k - a)) * ↑(n.descFactorial (k - a))) -
            (↑k + 1) * ↑n * (↑(k.choose (k - 1 - a)) *
              ↑((n - 1).descFactorial (k - 1 - a)))) := by
          congr 1; linarith
        linarith [mul_comm s (↑((k + 2).choose (k + 1 - a)) *
          ↑(n.descFactorial (k + 1 - a)))]
      · push Not at ha2
        have hak : a = k ∨ a = k + 1 := by omega
        rcases hak with ha_eq | ha_eq
        · -- a = k case: m = k+1
          subst ha_eq
          simp only [show a + 1 ≤ a + 2 from by omega, ite_true,
            show a ≤ a + 1 from by omega, ite_true,
            show a + 1 ≤ a + 1 from le_refl _, ite_true,
            show ¬(a + 1 ≤ a) from by omega, ite_false]
          have h1 : a + 2 - (a + 1) = 1 := by omega
          have h2 : a + 1 - a = 1 := by omega
          have h3 : a + 1 - (a + 1) = 0 := by omega
          rw [h1, h2, h3]
          simp only [pow_one, pow_zero,
            Nat.choose_one_right, Nat.descFactorial_one,
            Nat.choose_zero_right, Nat.descFactorial_zero, mul_zero, sub_zero]
          push_cast; ring
        · -- a = k+1 case: m = k+2 (leading coefficient)
          subst ha_eq
          simp only [show k + 1 ≤ k + 1 from le_refl _, ite_true,
            show k + 1 + 1 ≤ k + 2 from by omega, ite_true,
            show ¬(k + 1 + 1 ≤ k + 1) from by omega, ite_false,
            show ¬(k + 1 + 1 ≤ k) from by omega, ite_false]
          norm_num [Nat.choose_zero_right, Nat.descFactorial_zero]

/-- The multiplier recurrence holds for the POLYNOMIAL variable u = r².
The original `qknMultiplier_succ_succ` claimed a recurrence in r directly,
which is false due to a power-parity mismatch. Use `qknPoly_succ_succ`
(already proved) for the correct polynomial recurrence instead. -/
private noncomputable def Pkn (k n : ℕ) : Polynomial ℝ :=
  Finset.sum (Finset.range (k + 1)) (fun j =>
    Polynomial.C (((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) * (Nat.descFactorial n j : ℝ)) *
      Polynomial.X ^ (k - j))

private theorem Pkn_eval (k n : ℕ) (x : ℝ) :
    (Pkn k n).eval x =
      Finset.sum (Finset.range (k + 1)) (fun j =>
        ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) * (Nat.descFactorial n j : ℝ) * x ^ (k - j)) := by
  unfold Pkn
  change (Polynomial.evalRingHom x)
      (Finset.sum (Finset.range (k + 1)) (fun j =>
        Polynomial.C (((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) * (Nat.descFactorial n j : ℝ)) *
          Polynomial.X ^ (k - j))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp [mul_assoc, mul_left_comm, mul_comm]

private theorem Pkn_eval_natShift (k n : ℕ) (x : ℝ) :
    (Pkn k n).eval (x + n) =
      Finset.sum (Finset.range (k + 1)) (fun j =>
        ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
        (Nat.descFactorial n j : ℝ) * (x + n) ^ (k - j)) := by
  simpa using Pkn_eval k n (x + n)

private theorem Pkn_coeff (k n m : ℕ) :
    (Pkn k n).coeff m =
      Finset.sum (Finset.range (k + 1)) (fun j =>
        if m = k - j
          then ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) * (Nat.descFactorial n j : ℝ)
          else 0) := by
  unfold Pkn
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (Polynomial.coeff_C_mul_X_pow
      (((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) * (Nat.descFactorial n j : ℝ))
      (k - j) m)

private theorem Pkn_coeff_single (k n m : ℕ) :
    (Pkn k n).coeff m =
      if m ≤ k then
        ((-1 : ℝ) ^ (k - m)) * (Nat.choose k (k - m) : ℝ) *
          (Nat.descFactorial n (k - m) : ℝ)
      else 0 := by
  by_cases hmk : m ≤ k
  · rw [Pkn_coeff, Finset.sum_eq_single (k - m)]
    · simp [hmk, Nat.sub_sub_self hmk]
    · intro j hj hjne
      by_cases hmj : m = k - j
      · exfalso
        have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hjeq : j = k - m := by omega
        exact hjne hjeq
      · simp [hmj]
    · intro hnotmem
      exfalso
      apply hnotmem
      exact Finset.mem_range.mpr (by omega)
  · rw [Pkn_coeff]
    have hmgt : k < m := Nat.lt_of_not_ge hmk
    rw [Finset.sum_eq_zero]
    · simp [hmk]
    · intro j hj
      by_cases hmj : m = k - j
      · exfalso
        omega
      · simp [hmj]

private theorem Pkn_succ_succ
    (k n : ℕ) :
    Pkn (k + 2) n =
      (Polynomial.X - Polynomial.C (n : ℝ)) * Pkn (k + 1) n -
        Polynomial.C (((k + 1 : ℕ) : ℝ) * (n : ℝ)) * Pkn k (n - 1) := by
  ext m
  rw [Pkn_coeff_single, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Pkn_coeff_single]
  cases m with
  | zero =>
    -- m = 0 case
    have h0 : ((Polynomial.X - Polynomial.C (↑n : ℝ)) * Pkn (k + 1) n).coeff 0 =
        -(↑n : ℝ) * (Pkn (k + 1) n).coeff 0 := by
      simp [Polynomial.coeff_mul]
    rw [h0, Pkn_coeff_single]
    simp only [Nat.zero_le, ite_true, Nat.sub_zero, show (0 : ℕ) ≤ k from Nat.zero_le k]
    -- Goal: (-1)^{k+2}*C(k+2,k+2)*(n)_{k+2} =
    --   -n * ((-1)^{k+1}*C(k+1,k+1)*(n)_{k+1}) - (k+1)*n*((-1)^k*C(k,k)*(n-1)_k)
    have h := charlier_coeff_nat k n k
    -- Cast h to ℝ and use it
    have hR : (↑((k + 2).choose (k + 2) * n.descFactorial (k + 2) +
        (k + 1) * n * (k.choose k * (n - 1).descFactorial k)) : ℝ) =
      (↑((k + 1).choose (k + 2) * n.descFactorial (k + 2) +
        n * ((k + 1).choose (k + 1) * n.descFactorial (k + 1))) : ℝ) := by
      exact_mod_cast h
    simp only [Nat.choose_self, Nat.choose_eq_zero_of_lt (show k + 1 < k + 2 by omega),
               Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_zero] at hR
    simp only [Nat.choose_self]
    have hpow : (-1 : ℝ) ^ (k + 2) = (-1) ^ k := by ring
    have hpow1 : (-1 : ℝ) ^ (k + 1) = -(-1) ^ k := by ring
    rw [hpow, hpow1]
    -- Goal: (-1)^k * 1 * d(n,k+2) = -n*(-(-1)^k*1*d(n,k+1)) - (k+1)*n*((-1)^k*1*d(n-1,k))
    -- = (-1)^k * n * d(n,k+1) - (-1)^k * (k+1)*n*d(n-1,k)
    -- = (-1)^k * [n*d(n,k+1) - (k+1)*n*d(n-1,k)]
    -- From hR: d(n,k+2) + (k+1)*n*d(n-1,k) = n*d(n,k+1)
    -- So d(n,k+2) = n*d(n,k+1) - (k+1)*n*d(n-1,k)
    -- After factoring (-1)^k, both sides match.
    have hR' : (↑(n.descFactorial (k + 2)) : ℝ) =
        ↑n * ↑(n.descFactorial (k + 1)) - (↑k + 1) * ↑n * ↑((n - 1).descFactorial k) := by
      linarith
    -- Factor out (-1)^k: both sides equal (-1)^k * hR'
    -- Just use ring after substituting hR'
    push_cast
    calc (-1 : ℝ) ^ k * 1 * ↑(n.descFactorial (k + 2))
        = (-1) ^ k * (↑n * ↑(n.descFactorial (k + 1)) -
            (↑k + 1) * ↑n * ↑((n - 1).descFactorial k)) := by rw [mul_one, hR']
      _ = -↑n * (-(-1) ^ k * 1 * ↑(n.descFactorial (k + 1))) -
            (↑k + 1) * ↑n * ((-1) ^ k * 1 * ↑((n - 1).descFactorial k)) := by ring
  | succ a =>
    -- m = a + 1 case: use Polynomial.coeff_X_sub_C_mul
    rw [Polynomial.coeff_X_sub_C_mul, Pkn_coeff_single, Pkn_coeff_single]
    -- Need three sub-cases: a+1 > k+2, a+1 ∈ {k+1, k+2}, a+1 ≤ k
    by_cases ha1 : k + 2 < a + 1
    · -- a+1 > k+2: LHS = 0, all RHS ifs are false
      simp only [show ¬(a + 1 ≤ k + 2) from by omega, ite_false,
                  show ¬(a ≤ k + 1) from by omega, ite_false,
                  show ¬(a + 1 ≤ k + 1) from by omega, ite_false,
                  show ¬(a + 1 ≤ k) from by omega, ite_false]
      ring
    · push Not at ha1
      by_cases ha2 : a + 1 ≤ k
      · -- a+1 ≤ k: all conditions are true
        simp only [show a + 1 ≤ k + 2 from by omega, ite_true,
                    show a ≤ k + 1 from by omega, ite_true,
                    show a + 1 ≤ k + 1 from by omega, ite_true,
                    show a + 1 ≤ k from ha2, ite_true]
        -- This is the generic case. Use charlier_coeff_nat with s' = k - a.
        -- s = k+2-(a+1) = k+1-a. Set s' = k-1-a so s = s'+2 when a+1 ≤ k-1.
        -- Actually s' = k - a - 1 and s = s' + 2 iff k - a ≥ 2 iff a ≤ k-2.
        -- For a+1 ≤ k, a ≤ k-1. If a ≤ k-2, use charlier_coeff_nat.
        -- If a = k-1 (so s=2), also use charlier_coeff_nat with s'=0.
        -- If a = k (so s=1)... but a+1 ≤ k means a ≤ k-1, so a ≤ k-1 and s ≥ 2.
        -- So s = k+1-a ≥ 2 always in this branch. Good.
        have hnat := charlier_coeff_nat k n (k - 1 - a)
        -- Simplify indices: k-1-a+2 = k+1-a, k-1-a+1 = k-a, k-1-a stays
        have hs2 : k - 1 - a + 2 = k + 1 - a := by omega
        have hs1 : k - 1 - a + 1 = k - a := by omega
        have hk2a : k + 2 - (a + 1) = k + 1 - a := by omega
        have hk1a : k + 1 - (a + 1) = k - a := by omega
        have hka : k - (a + 1) = k - 1 - a := by omega
        rw [hs2, hs1] at hnat
        rw [hk2a, hk1a, hka]
        -- Cast hnat to ℝ
        have hR : (↑((k + 2).choose (k + 1 - a) * n.descFactorial (k + 1 - a) +
            (k + 1) * n * (k.choose (k - 1 - a) * (n - 1).descFactorial (k - 1 - a))) : ℝ) =
          (↑((k + 1).choose (k + 1 - a) * n.descFactorial (k + 1 - a) +
            n * ((k + 1).choose (k - a) * n.descFactorial (k - a))) : ℝ) := by
          exact_mod_cast hnat
        push_cast at hR ⊢
        have hpow2 : ((-1 : ℝ) ^ (k + 1 - a)) = (-1) ^ (k - 1 - a) := by
          have : k + 1 - a = (k - 1 - a) + 2 := by omega
          rw [this]; ring
        have hpow1 : ((-1 : ℝ) ^ (k - a)) = -((-1) ^ (k - 1 - a)) := by
          have : k - a = (k - 1 - a) + 1 := by omega
          rw [this]; ring
        rw [hpow2, hpow1]
        -- Factor out (-1)^{k-1-a} from both sides
        set s := (-1 : ℝ) ^ (k - 1 - a)
        -- Goal: s * A = s * B - n * (-s * C) - (k+1)*n*(s*D)
        --     = s * B + n*s*C - (k+1)*n*s*D
        --     = s * (B + n*C - (k+1)*n*D)
        -- LHS = s * A
        -- This follows from A + (k+1)*n*D = B + n*C which is hR
        have hs : s ≠ 0 := by positivity
        have : s * (↑((k + 2).choose (k + 1 - a)) * ↑(n.descFactorial (k + 1 - a))) =
          s * (↑((k + 1).choose (k + 1 - a)) * ↑(n.descFactorial (k + 1 - a)) +
            ↑n * (↑((k + 1).choose (k - a)) * ↑(n.descFactorial (k - a))) -
            (↑k + 1) * ↑n * (↑(k.choose (k - 1 - a)) * ↑((n - 1).descFactorial (k - 1 - a)))) := by
          congr 1; linarith
        linarith [mul_comm s (↑((k + 2).choose (k + 1 - a)) * ↑(n.descFactorial (k + 1 - a)))]
      · push Not at ha2
        -- k < a+1 and a+1 ≤ k+2, so a+1 ∈ {k+1, k+2}, i.e., a ∈ {k, k+1}
        -- a ∈ {k, k+1}
        have hak : a = k ∨ a = k + 1 := by omega
        rcases hak with ha_eq | ha_eq
        · subst ha_eq
          simp_all
          ring_nf
        · subst ha_eq
          simp_all

private theorem qkn_power_split
    {r : ℝ}
    (hr : 0 < r)
    (n k j : ℕ)
    (hjk : j ≤ k) :
    r ^ ((n : ℤ) - 2 * (j : ℤ)) =
      r ^ ((n : ℤ) - 2 * (k : ℤ)) * (r ^ 2) ^ (k - j) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hexp :
      (n : ℤ) - 2 * (j : ℤ) = ((n : ℤ) - 2 * (k : ℤ)) + 2 * ((k - j : ℕ) : ℤ) := by
    omega
  rw [hexp, zpow_add₀ hr0]
  have hcast : (2 * ((k - j : ℕ) : ℤ)) = (((2 * (k - j) : ℕ)) : ℤ) := by
    norm_num
  rw [hcast, zpow_natCast]
  rw [show r ^ (2 * (k - j)) = (r ^ 2) ^ (k - j) by rw [pow_mul]]

private theorem qkn_eq_Pkn
    (k n : ℕ) {r : ℝ}
    (hr : 0 < r)
    (hkn : k ≤ n) :
    qkn k n r =
      (1 / Real.sqrt (Nat.factorial n : ℝ)) *
        r ^ ((n : ℤ) - 2 * (k : ℤ)) * (Pkn k n).eval (r ^ 2) := by
  rw [qkn_descFactorial_form k n hr hkn]
  have hsum :
      Finset.sum (Finset.range (k + 1)) (fun j =>
          ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) * (Nat.descFactorial n j : ℝ) *
            r ^ ((n : ℤ) - 2 * (j : ℤ))) =
        r ^ ((n : ℤ) - 2 * (k : ℤ)) *
          Finset.sum (Finset.range (k + 1)) (fun j =>
            ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) * (Nat.descFactorial n j : ℝ) *
              (r ^ 2) ^ (k - j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [qkn_power_split hr n k j hjk]
    ring
  rw [hsum, Pkn_eval]
  ring

private lemma fourier_mk_eq_exp
    (n : ℤ)
    (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : Circle) : ℂ) =
      Complex.exp (Complex.I * (n : ℂ) * θ) := by
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * θ / (HermiteLEAN.T : ℂ) =
        Complex.I * (n : ℂ) * θ := by
    simp [HermiteLEAN.T, mul_assoc]
    field_simp [Real.pi_ne_zero]
  rw [harg]

private lemma circlePoint_mk_eq_polarCoord_symm
    (r θ : ℝ) :
    circlePoint r (QuotientAddGroup.mk θ : Circle) = Complex.polarCoord.symm (r, θ) := by
  change ((r : ℂ) * (fourier (1 : ℤ) (QuotientAddGroup.mk θ : Circle) : ℂ)) = _
  rw [fourier_mk_eq_exp]
  have hexp :
      Complex.exp (Complex.I * (((1 : ℤ) : ℂ)) * (θ : ℂ)) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
    congr 1
    ring
  rw [hexp, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  simp [mul_comm]

private lemma fourier_mk_norm
    (n : ℤ)
    (θ : ℝ) :
    ‖(fourier n (QuotientAddGroup.mk θ : Circle) : ℂ)‖ = 1 := by
  rw [fourier_mk_eq_exp, Complex.norm_exp]
  simp

private lemma norm_sq_circleLeadingFactor
    (k : ℕ)
    (r : ℝ) :
    ‖circleLeadingFactor k r‖ ^ 2 =
      (((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) := by
  rw [circleLeadingFactor, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma integral_addCircle_volume_eq_smul_haar
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (f : Circle → E) :
    ∫ t : Circle, f t = T • ∫ t : Circle, f t ∂AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  rw [integral_smul_measure]
  have hT_nonneg : 0 ≤ T := by
    simpa [T, HermiteLEAN.T] using (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
  simp [ENNReal.toReal_ofReal hT_nonneg]

private lemma integral_Ioo_eq_addCircle
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (f : Circle → E) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, f (QuotientAddGroup.mk θ) =
      ∫ t : Circle, f t := by
  rw [← integral_Ioc_eq_integral_Ioo]
  have h : -Real.pi + T = Real.pi := by
    simp [T, HermiteLEAN.T]
    ring
  rw [show Set.Ioc (-Real.pi) Real.pi = Set.Ioc (-Real.pi) (-Real.pi + T) by rw [h]]
  exact AddCircle.integral_preimage T (-Real.pi) f

private lemma integral_Ioo_eq_T_smul_haar
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (f : Circle → E) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, f (QuotientAddGroup.mk θ) =
      T • ∫ t : Circle, f t ∂AddCircle.haarAddCircle := by
  rw [integral_Ioo_eq_addCircle, integral_addCircle_volume_eq_smul_haar]

private lemma continuous_mk_addCircle :
    Continuous (fun θ : ℝ => (QuotientAddGroup.mk θ : Circle)) :=
  continuous_quotient_mk'

private lemma continuous_circlePoint_mk :
    Continuous (fun p : ℝ × ℝ => circlePoint p.1 ((QuotientAddGroup.mk p.2 : Circle))) := by
  dsimp [circlePoint]
  exact
    (Complex.continuous_ofReal.comp continuous_fst).mul
      ((fourier (1 : ℤ)).continuous.comp (continuous_mk_addCircle.comp continuous_snd))

private lemma continuous_finiteHermiteSumCircle_comp
    (k : ℕ)
    {D : ℕ}
    (a : Fin D → ℂ) :
    Continuous
      (fun p : ℝ × ℝ =>
        finiteHermiteSum k a (circlePoint p.1 ((QuotientAddGroup.mk p.2 : Circle)))) := by
  simpa [finiteHermiteSum] using
    (continuous_finsetSum (s := (Finset.univ : Finset (Fin D))) fun n _ =>
      continuous_const.mul ((continuous_Phi k n.1).comp continuous_circlePoint_mk))

private lemma integrableOn_annulus_polar_finiteHermiteSum
    (k : ℕ)
    {D : ℕ}
    (a : Fin D → ℂ)
    (j : ℕ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 *
          (‖finiteHermiteSum k a (circlePoint p.1 ((QuotientAddGroup.mk p.2 : Circle)))‖ ^ 2 *
            Real.exp (-p.1 ^ 2)))
      (Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)) ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  have hcompact :
      IsCompact
        (Set.Icc (j : ℝ) (((j + 1 : ℕ) : ℝ)) ×ˢ Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont :
      Continuous
        (fun p : ℝ × ℝ =>
          p.1 *
            (‖finiteHermiteSum k a (circlePoint p.1 ((QuotientAddGroup.mk p.2 : Circle)))‖ ^ 2 *
              Real.exp (-p.1 ^ 2))) := by
    exact
      Continuous.mul continuous_fst
        (Continuous.mul ((continuous_finiteHermiteSumCircle_comp k a).norm.pow 2)
          (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))
  have hbase :
      IntegrableOn
        (fun p : ℝ × ℝ =>
          p.1 *
            (‖finiteHermiteSum k a (circlePoint p.1 ((QuotientAddGroup.mk p.2 : Circle)))‖ ^ 2 *
              Real.exp (-p.1 ^ 2)))
        (Set.Icc (j : ℝ) (((j + 1 : ℕ) : ℝ)) ×ˢ Set.Icc (-Real.pi) Real.pi)
        (volume.prod volume) := by
    exact hcont.continuousOn.integrableOn_compact hcompact
  refine hbase.mono_set ?_
  exact Set.prod_mono Set.Ico_subset_Icc_self Set.Ioo_subset_Icc_self

/-- Rewrites the polar-coordinate integrand of the annulus integral as an explicit
indicator of the radial strip times the circle integrand.  Factored out of
`annulusIntegralSq_finiteHermiteSum_eq_radial` to keep its proof under the size
limit. -/
private lemma annulus_polar_indicator_rw
    (k : ℕ) {D : ℕ} (a : Fin D → ℂ) (j : ℕ)
    (F : ℂ → ℝ)
    (hF : F = fun z => ‖finiteHermiteSum k a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :
    (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      p.1 • Set.indicator (annulus j) F (Complex.polarCoord.symm p))
      =
    ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      Set.indicator
        ((Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
          Set.Ioo (-Real.pi) Real.pi)
        (fun p : ℝ × ℝ =>
          p.1 *
            (‖finiteHermiteSum k a (circlePoint p.1 ((QuotientAddGroup.mk p.2 : Circle)))‖ ^ 2 *
              Real.exp (-p.1 ^ 2))) p := by
  subst hF
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  rcases p with ⟨r, θ⟩
  rcases hp with ⟨hrpos, hθ⟩
  have hrpos' : 0 < r := by simpa using hrpos
  by_cases hrj : r ∈ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))
  · have hann : Complex.polarCoord.symm (r, θ) ∈ annulus j := by
      change (j : ℝ) ≤ ‖Complex.polarCoord.symm (r, θ)‖ ∧
          ‖Complex.polarCoord.symm (r, θ)‖ < (((j + 1 : ℕ) : ℝ))
      rw [Complex.norm_polarCoord_symm, abs_of_pos hrpos']
      exact hrj
    change r * Set.indicator (annulus j) _ (Complex.polarCoord.symm (r, θ)) = _
    rw [Set.indicator_of_mem hann]
    rw [Set.indicator_of_mem (show
      (r, θ) ∈
        (Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
          Set.Ioo (-Real.pi) Real.pi from ⟨⟨hrpos, hrj⟩, hθ⟩)]
    have hcircle :
        finiteHermiteSum k a (circlePoint r ((QuotientAddGroup.mk θ : Circle)))
          =
        circleLeadingFactor k r *
          (fourier (-(k : ℤ)) (QuotientAddGroup.mk θ : Circle) : ℂ) *
            finiteCirclePoly k r a (QuotientAddGroup.mk θ : Circle) := by
      simpa using (finiteHermiteSum_circle (k := k) (a := a) hrpos'
        (QuotientAddGroup.mk θ : Circle))
    have hfour : ‖(fourier (-(k : ℤ)) (QuotientAddGroup.mk θ : Circle) : ℂ)‖ ^ 2 = 1 := by
      rw [fourier_mk_norm]; norm_num
    have hpolar :
        finiteHermiteSum k a (Complex.polarCoord.symm (r, θ))
          =
        finiteHermiteSum k a (circlePoint r ((QuotientAddGroup.mk θ : Circle))) := by
      rw [← circlePoint_mk_eq_polarCoord_symm]
    have hnormPolar : ‖Complex.polarCoord.symm (r, θ)‖ ^ 2 = r ^ 2 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hrpos']
    have hFpolar :
        ‖finiteHermiteSum k a (Complex.polarCoord.symm (r, θ))‖ ^ 2 *
            Real.exp (-‖Complex.polarCoord.symm (r, θ)‖ ^ 2)
          =
        ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) *
          ‖finiteCirclePoly k r a (QuotientAddGroup.mk θ : Circle)‖ ^ 2) *
            Real.exp (-r ^ 2) := by
      rw [hpolar, hcircle, norm_mul, norm_mul, mul_pow, mul_pow, hfour,
        norm_sq_circleLeadingFactor, hnormPolar]
      ring_nf
    rw [hFpolar]
    rw [show (r, θ).1 = r by rfl, show (r, θ).2 = θ by rfl]
    rw [hcircle, norm_mul, norm_mul, mul_pow, mul_pow, hfour, norm_sq_circleLeadingFactor]
    ring_nf
  · have hann : Complex.polarCoord.symm (r, θ) ∉ annulus j := by
      intro hz
      apply hrj
      change (j : ℝ) ≤ ‖Complex.polarCoord.symm (r, θ)‖ ∧
          ‖Complex.polarCoord.symm (r, θ)‖ < (((j + 1 : ℕ) : ℝ)) at hz
      rw [Complex.norm_polarCoord_symm, abs_of_pos hrpos'] at hz
      exact hz
    change r * Set.indicator (annulus j) _ (Complex.polarCoord.symm (r, θ)) = _
    rw [Set.indicator_of_notMem hann]
    rw [Set.indicator_of_notMem (show
      (r, θ) ∉
        (Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
          Set.Ioo (-Real.pi) Real.pi from by
        intro hmem
        exact hrj hmem.1.2)]
    simp

private lemma annulusIntegralSq_finiteHermiteSum_eq_radial
    (k : ℕ)
    {D : ℕ}
    (a : Fin D → ℂ)
    (j : ℕ) :
    annulusIntegralSq (finiteHermiteSum k a) j
      =
    2 * ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
      r * Real.exp (-r ^ 2) *
        ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) *
          circleL2Sq (finiteCirclePoly k r a)) := by
  let F : ℂ → ℝ := fun z => ‖finiteHermiteSum k a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
  have hannulus_meas : MeasurableSet (annulus j) := by
    refine (measurableSet_le measurable_const measurable_norm).inter ?_
    exact measurableSet_lt measurable_norm measurable_const
  unfold HermitekLEAN.annulusIntegralSq HermiteLEAN.annulusIntegralSq
  rw [show (∫ z in annulus j, F z ∂(volume : Measure ℂ)) =
      ∫ z : ℂ, Set.indicator (annulus j) F z ∂(volume : Measure ℂ) by
      symm
      rw [MeasureTheory.integral_indicator hannulus_meas]]
  rw [← Complex.integral_comp_polarCoord_symm (fun z : ℂ => Set.indicator (annulus j) F z)]
  have hpolar_rw :=
    annulus_polar_indicator_rw k a j F rfl
  rw [polarCoord_target, hpolar_rw]
  rw [MeasureTheory.integral_indicator
    ((measurableSet_Ioi.inter measurableSet_Ico).prod measurableSet_Ioo)]
  rw [Measure.restrict_restrict
    ((measurableSet_Ioi.inter measurableSet_Ico).prod measurableSet_Ioo)]
  have hstrip :
      ((Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
          Set.Ioo (-Real.pi) Real.pi) ∩
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)
        =
      (Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
        Set.Ioo (-Real.pi) Real.pi := by
    ext p
    rcases p with ⟨r, θ⟩
    simp [and_left_comm, and_assoc]
  rw [hstrip]
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod _ ((integrableOn_annulus_polar_finiteHermiteSum k a j).mono_set
    (Set.prod_mono
      (by
        intro x hx
        exact hx.2)
      (by
        intro x hx
        exact hx)))]
  let srad : Set ℝ := Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))
  have inner_eq :
      ∀ r : ℝ, r ∈ srad →
        (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r *
            (‖finiteHermiteSum k a (circlePoint r ((QuotientAddGroup.mk θ : Circle)))‖ ^ 2 *
              Real.exp (-r ^ 2)))
          =
        T *
          (r * Real.exp (-r ^ 2) *
            ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) *
              circleL2Sq (finiteCirclePoly k r a))) := by
    intro r hr
    have hrpos : 0 < r := hr.1
    have hpoint :
        ∀ θ : ℝ,
          r *
              (‖finiteHermiteSum k a (circlePoint r ((QuotientAddGroup.mk θ : Circle)))‖ ^ 2 *
                Real.exp (-r ^ 2))
            =
          (r * Real.exp (-r ^ 2) *
            (((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2)) *
              ‖finiteCirclePoly k r a (QuotientAddGroup.mk θ : Circle)‖ ^ 2 := by
      intro θ
      have hcircle :
          finiteHermiteSum k a (circlePoint r ((QuotientAddGroup.mk θ : Circle)))
            =
          circleLeadingFactor k r *
            (fourier (-(k : ℤ)) (QuotientAddGroup.mk θ : Circle) : ℂ) *
              finiteCirclePoly k r a (QuotientAddGroup.mk θ : Circle) := by
        simpa using (finiteHermiteSum_circle (k := k) (a := a) hrpos
          (QuotientAddGroup.mk θ : Circle))
      have hfour : ‖(fourier (-(k : ℤ)) (QuotientAddGroup.mk θ : Circle) : ℂ)‖ ^ 2 = 1 := by
        rw [fourier_mk_norm]
        norm_num
      rw [hcircle, norm_mul, norm_mul, mul_pow, mul_pow, hfour, norm_sq_circleLeadingFactor]
      ring_nf
    simp_rw [hpoint]
    rw [MeasureTheory.integral_const_mul]
    have hhaar := integral_Ioo_eq_T_smul_haar
      (fun t : Circle => ‖finiteCirclePoly k r a t‖ ^ 2)
    simp only [smul_eq_mul] at hhaar
    rw [hhaar]
    unfold HermitekLEAN.circleL2Sq HermiteLEAN.circleL2Sq
    ring
  have houter :
      (∫ r in srad,
        ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r *
            (‖finiteHermiteSum k a (circlePoint r ((QuotientAddGroup.mk θ : Circle)))‖ ^ 2 *
              Real.exp (-r ^ 2)))
        =
      ∫ r in srad,
        T *
          (r * Real.exp (-r ^ 2) *
            ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) *
              circleL2Sq (finiteCirclePoly k r a))) := by
    apply MeasureTheory.setIntegral_congr_fun
    · exact measurableSet_Ioi.inter measurableSet_Ico
    · intro r hr
      exact inner_eq r hr
  rw [houter]
  rw [MeasureTheory.integral_const_mul]
  have hT_eq : (1 / Real.pi) * T = 2 := by
    simp [T, HermiteLEAN.T]
    field_simp
  let radial : ℝ → ℝ := fun r =>
    r * Real.exp (-r ^ 2) *
      ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) *
        circleL2Sq (finiteCirclePoly k r a))
  have hIoiIco_ae :
      srad =ᵐ[volume]
      Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)) := by
    have h0 :
        srad =ᵐ[volume] Set.inter (Set.Ici (0 : ℝ)) (Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) := by
      filter_upwards [Ioi_ae_eq_Ici (a := (0 : ℝ)) (μ := volume)] with x hx
      apply propext
      constructor
      · intro h
        exact ⟨hx.mp h.1, h.2⟩
      · intro h
        exact ⟨hx.mpr h.1, h.2⟩
    have h1 :
        (Set.Ici (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)))
          =
        Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)) := by
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        refine ⟨?_, hx⟩
        exact le_trans (show (0 : ℝ) ≤ (j : ℝ) by exact_mod_cast Nat.zero_le j) hx.1
    exact h0.trans (Filter.EventuallyEq.of_eq h1)
  have hset_eq :
      (∫ r in srad,
        radial r)
        =
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
        radial r := by
    calc
      (∫ r in srad, radial r)
        =
      ∫ r in Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)), radial r :=
        MeasureTheory.setIntegral_congr_set hIoiIco_ae
      _ =
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), radial r := by
        rw [intervalIntegral.integral_of_le
          (show (j : ℝ) ≤ (((j + 1 : ℕ) : ℝ)) by exact_mod_cast Nat.le_succ j)]
        have hIcoIoc :
            (∫ r in Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)), radial r)
              =
            ∫ r in Set.Ioc (j : ℝ) (((j + 1 : ℕ) : ℝ)), radial r := by
          simpa using
            (MeasureTheory.setIntegral_congr_set
              (f := radial)
              (μ := volume)
              (Ico_ae_eq_Ioc (a := (j : ℝ)) (b := (((j + 1 : ℕ) : ℝ)))))
        exact hIcoIoc
  calc
    (1 / Real.pi) *
        (T *
          ∫ r in srad,
            radial r)
      =
    ((1 / Real.pi) * T) *
        ∫ r in srad,
          radial r := by
            ring
    _ =
      2 *
        ∫ r in srad,
          radial r := by
            rw [hT_eq]
    _ =
      2 *
        ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
          radial r := by
            rw [hset_eq]

private def singleCoeff (n : ℕ) : Fin (n + 1) → ℂ :=
  fun m => if m.1 = n then 1 else 0

private lemma finiteHermiteSum_singleCoeff
    (k n : ℕ) :
    finiteHermiteSum k (singleCoeff n) = Phi k n := by
  funext z
  unfold finiteHermiteSum singleCoeff
  let n0 : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hn0 : n0 ∈ (Finset.univ : Finset (Fin (n + 1))) := by simp [n0]
  rw [Finset.sum_eq_single_of_mem n0 hn0]
  · simp [n0]
  · intro m hm hne
    have hm_ne : m.1 ≠ n := by
      intro hm_eq
      apply hne
      exact Fin.ext hm_eq
    simp [hm_ne]

private lemma annulusIntegralSq_Phi_eq
    (k n j : ℕ) :
    annulusIntegralSq (Phi k n) j
      =
    2 * ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
      r * Real.exp (-r ^ 2) *
        ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) *
          |qkn k n r| ^ 2) := by
  rw [← finiteHermiteSum_singleCoeff k n]
  rw [annulusIntegralSq_finiteHermiteSum_eq_radial k (singleCoeff n) j]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  change
    r * Real.exp (-r ^ 2) *
        ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) *
          circleL2Sq (finiteCirclePoly k r (singleCoeff n)))
      =
    r * Real.exp (-r ^ 2) *
        ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) *
          |qkn k n r| ^ 2)
  rw [show circleL2Sq (finiteCirclePoly k r (singleCoeff n)) =
      ∑ m : Fin (n + 1), ‖singleCoeff n m‖ ^ 2 * |qkn k m.1 r| ^ 2 by
      simpa using (finiteCirclePoly_l2_identity (k := k) (r := r) (a := singleCoeff n))]
  let n0 : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hn0 : n0 ∈ (Finset.univ : Finset (Fin (n + 1))) := by simp [n0]
  rw [Finset.sum_eq_single_of_mem n0 hn0]
  · have hn0_one : singleCoeff n n0 = 1 := by
      simp [singleCoeff, n0]
    rw [hn0_one]
    simp [n0]
  · intro m hm hne
    have hm_ne : m.1 ≠ n := by
      intro hm_eq
      apply hne
      exact Fin.ext hm_eq
    have hm_zero : singleCoeff n m = 0 := by
      simp [singleCoeff, hm_ne]
    rw [hm_zero]
    simp

private lemma intervalIntegrable_basisRadialTerm
    (k n j : ℕ) :
    IntervalIntegrable
      (fun r : ℝ =>
        r * Real.exp (-r ^ 2) *
          ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) *
            |qkn k n r| ^ 2))
      volume (j : ℝ) (((j + 1 : ℕ) : ℝ)) := by
  let t0 : Circle := QuotientAddGroup.mk 0
  let g : ℝ → ℝ := fun r =>
    r * Real.exp (-r ^ 2) * ‖Phi k n (circlePoint r t0)‖ ^ 2
  have hcircle0 : Continuous (fun r : ℝ => circlePoint r t0) := by
    have h := continuous_circlePoint_mk.comp
      (continuous_id.prodMk (continuous_const (y := (0 : ℝ))))
    simpa [t0, Function.comp_def] using h
  have hg : Continuous g := by
    dsimp [g]
    have h := continuous_id.mul
        ((Real.continuous_exp.comp (continuous_neg.comp (continuous_id.pow 2))).mul
          (((continuous_Phi k n).comp hcircle0).norm.pow 2))
    convert h using 1
    ext r
    simp only [Function.comp_apply, Pi.mul_apply, id_eq]
    ring
  have hgi :
      IntervalIntegrable g volume (j : ℝ) (((j + 1 : ℕ) : ℝ)) := by
    exact Continuous.intervalIntegrable
      (μ := volume) hg (j : ℝ) (((j + 1 : ℕ) : ℝ))
  refine hgi.congr_ae ?_
  change
    ∀ᵐ r ∂volume.restrict (Set.uIoc (j : ℝ) (((j + 1 : ℕ) : ℝ))),
      g r =
        r * Real.exp (-r ^ 2) *
          ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) *
            |qkn k n r| ^ 2)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards with r hr
  have hjle : (j : ℝ) ≤ (((j + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_succ j
  rw [Set.uIoc_of_le hjle] at hr
  have h0j : (0 : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast Nat.zero_le j
  have hrpos : 0 < r := by
    exact lt_of_le_of_lt h0j hr.1
  dsimp [g]
  have hphi := phi_polar (k := k) (n := n) hrpos t0
  have hfourk : ‖(fourier (-(k : ℤ)) t0 : ℂ)‖ ^ 2 = 1 := by
    calc
      ‖(fourier (-(k : ℤ)) t0 : ℂ)‖ ^ 2 = (‖(fourier (-(k : ℤ)) t0 : ℂ)‖) ^ 2 := by rfl
      _ = 1 ^ 2 := by rw [fourier_mk_norm (n := (-(k : ℤ))) (θ := (0 : ℝ))]
      _ = 1 := by norm_num
  have hfourn : ‖(fourier (n : ℤ) t0 : ℂ)‖ ^ 2 = 1 := by
    calc
      ‖(fourier (n : ℤ) t0 : ℂ)‖ ^ 2 = (‖(fourier (n : ℤ) t0 : ℂ)‖) ^ 2 := by rfl
      _ = 1 ^ 2 := by rw [fourier_mk_norm (n := (n : ℤ)) (θ := (0 : ℝ))]
      _ = 1 := by norm_num
  rw [hphi, norm_mul, norm_mul, mul_pow, mul_pow, hfourk, norm_sq_circleLeadingFactor]
  rw [norm_mul, mul_pow, hfourn]
  rw [Complex.norm_real, Real.norm_eq_abs]
  ring_nf

private lemma sqrt_sub_le_sub_of_one_le
    {a b : ℝ}
    (hb1 : 1 ≤ b)
    (hba : b ≤ a) :
    Real.sqrt a - Real.sqrt b ≤ a - b := by
  have hb_nonneg : 0 ≤ b := by linarith
  have ha_nonneg : 0 ≤ a := le_trans hb_nonneg hba
  have hdiff_nonneg : 0 ≤ Real.sqrt a - Real.sqrt b := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt hba)
  have hden : 1 ≤ Real.sqrt a + Real.sqrt b := by
    have hb_sqrt : 1 ≤ Real.sqrt b := by
      rw [Real.one_le_sqrt]
      linarith
    nlinarith [hb_sqrt, Real.sqrt_nonneg a]
  have hmul :
      (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    calc
      (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b)
        = (Real.sqrt a) ^ 2 - (Real.sqrt b) ^ 2 := by ring
      _ = a - b := by
        rw [sq, sq, Real.mul_self_sqrt ha_nonneg, Real.mul_self_sqrt hb_nonneg]
  calc
    Real.sqrt a - Real.sqrt b
      ≤
    (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
        nlinarith
    _ = a - b := hmul

private lemma sqrt_nat_sub_self_le
    (n i : ℕ)
    (hin : i < n) :
    |Real.sqrt (n : ℝ) - Real.sqrt ((n - i : ℕ) : ℝ)| ≤ i := by
  have hni_pos : 1 ≤ n - i := by
    omega
  have hni_le : ((n - i : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n i
  have hdiff_nonneg :
      0 ≤ Real.sqrt (n : ℝ) - Real.sqrt ((n - i : ℕ) : ℝ) := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt hni_le)
  rw [abs_of_nonneg hdiff_nonneg]
  calc
    Real.sqrt (n : ℝ) - Real.sqrt ((n - i : ℕ) : ℝ)
      ≤
    (n : ℝ) - ((n - i : ℕ) : ℝ) := by
        exact
          sqrt_sub_le_sub_of_one_le
            (by exact_mod_cast hni_pos)
            hni_le
    _ = ((n - (n - i) : ℕ) : ℝ) := by
        rw [← Nat.cast_sub (Nat.sub_le n i)]
    _ = (i : ℝ) := by
        exact_mod_cast (by omega : n - (n - i) = i)

private lemma sqrt_nat_sub_shift_le
    (n i k : ℕ)
    (hik : i < k)
    (hkn : k < n) :
    |Real.sqrt (n : ℝ) - Real.sqrt ((n - i : ℕ) : ℝ)| ≤ k := by
  have hin : i < n := lt_trans hik hkn
  exact le_trans (sqrt_nat_sub_self_le n i hin) (by exact_mod_cast Nat.le_of_lt hik)

private lemma rStar_shift_le
    (k n : ℕ)
    (hkn : k < n) :
    |Real.sqrt (n : ℝ) - FockSPR.rStar (n - k)| ≤ k + 1 := by
  have hnk_pos : 1 ≤ n - k := by
    omega
  have hbase :
      |Real.sqrt (n : ℝ) - Real.sqrt ((n - k : ℕ) : ℝ)| ≤ k := by
    simpa using sqrt_nat_sub_self_le n k hkn
  have hhalf :
      |Real.sqrt ((n - k : ℕ) : ℝ) - FockSPR.rStar (n - k)| ≤ 1 := by
    have hdiff_nonneg :
        0 ≤ FockSPR.rStar (n - k) - Real.sqrt ((n - k : ℕ) : ℝ) := by
      unfold FockSPR.rStar
      exact sub_nonneg.mpr
            (Real.sqrt_le_sqrt (by linarith : ((n - k : ℕ) : ℝ) ≤ ((n - k : ℕ) : ℝ) + 1 / 2))
    rw [abs_sub_comm, abs_of_nonneg hdiff_nonneg]
    unfold FockSPR.rStar
    calc
      Real.sqrt (((n - k : ℕ) : ℝ) + 1 / 2) - Real.sqrt ((n - k : ℕ) : ℝ)
        ≤
      (((n - k : ℕ) : ℝ) + 1 / 2) - ((n - k : ℕ) : ℝ) := by
          exact
            sqrt_sub_le_sub_of_one_le
              (by exact_mod_cast hnk_pos)
              (by linarith)
      _ = (1 / 2 : ℝ) := by ring
      _ ≤ 1 := by norm_num
  calc
    |Real.sqrt (n : ℝ) - FockSPR.rStar (n - k)|
      ≤
    |Real.sqrt (n : ℝ) - Real.sqrt ((n - k : ℕ) : ℝ)| +
        |Real.sqrt ((n - k : ℕ) : ℝ) - FockSPR.rStar (n - k)| := by
          simpa [abs_sub_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            abs_add_le
              (Real.sqrt (n : ℝ) - Real.sqrt ((n - k : ℕ) : ℝ))
              (Real.sqrt ((n - k : ℕ) : ℝ) - FockSPR.rStar (n - k))
    _ ≤ k + 1 := by
          have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
          nlinarith [hbase, hhalf, hk_nonneg]

private lemma centered_gap_le_rStar_dist
    (k n : ℕ)
    (hkn : k < n)
    (r : ℝ) :
    posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ))
      ≤
    |r - FockSPR.rStar (n - k)| := by
  have hshift :
      |r - Real.sqrt (n : ℝ)|
        ≤
      |r - FockSPR.rStar (n - k)| + |Real.sqrt (n : ℝ) - FockSPR.rStar (n - k)| := by
    calc
      |r - Real.sqrt (n : ℝ)|
        = |(r - FockSPR.rStar (n - k)) + (FockSPR.rStar (n - k) - Real.sqrt (n : ℝ))| := by
            ring_nf
      _ ≤ |r - FockSPR.rStar (n - k)| + |FockSPR.rStar (n - k) - Real.sqrt (n : ℝ)| := by
            exact abs_add_le _ _
      _ = |r - FockSPR.rStar (n - k)| + |Real.sqrt (n : ℝ) - FockSPR.rStar (n - k)| := by
            congr 1
            rw [abs_sub_comm]
  have hmain :
      |r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ)
        ≤
      |r - FockSPR.rStar (n - k)| := by
    have hshift' := rStar_shift_le k n hkn
    have hshift'' :
        |Real.sqrt (n : ℝ) - FockSPR.rStar (n - k)| ≤ ((k + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hshift'
    calc
      |r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ)
        ≤
      (|r - FockSPR.rStar (n - k)| + |Real.sqrt (n : ℝ) - FockSPR.rStar (n - k)|) -
          ((k + 3 : ℕ) : ℝ) := by
            exact sub_le_sub_right hshift _
      _ ≤ (|r - FockSPR.rStar (n - k)| + ((k + 1 : ℕ) : ℝ)) - ((k + 3 : ℕ) : ℝ) := by
            have hadd :
                |r - FockSPR.rStar (n - k)| + |Real.sqrt (n : ℝ) - FockSPR.rStar (n - k)| ≤
                  |r - FockSPR.rStar (n - k)| + ((k + 1 : ℕ) : ℝ) :=
              add_le_add_right hshift'' _
            exact sub_le_sub_right hadd _
      _ = |r - FockSPR.rStar (n - k)| + ((((k + 1 : ℕ) : ℝ) - ((k + 3 : ℕ) : ℝ)) : ℝ) := by
            ring
      _ = |r - FockSPR.rStar (n - k)| + (-2 : ℝ) := by norm_num [Nat.cast_add]
      _ ≤ |r - FockSPR.rStar (n - k)| := by nlinarith [abs_nonneg (r - FockSPR.rStar (n - k))]
  have hright_nonneg : 0 ≤ |r - FockSPR.rStar (n - k)| := abs_nonneg _
  exact max_le hmain hright_nonneg

private lemma monomial_core_pointwise
    (m : ℕ)
    (hm : 1 ≤ m)
    {r : ℝ}
    (hr : 0 < r) :
    r ^ (2 * m + 1) * Real.exp (-r ^ 2) / (Nat.factorial m : ℝ)
      ≤
    (Real.exp (1 / 4) / 2) * Real.exp (-(r - FockSPR.rStar m) ^ 2) := by
  have h_eq : r ^ (2 * m + 1) * Real.exp (-r ^ 2) = Real.exp (FockSPR.phiFunc m r) := by
    unfold FockSPR.phiFunc
    have hpow :
        r ^ (2 * m + 1) = Real.exp ((2 * (m : ℝ) + 1) * Real.log r) := by
      rw [← Real.exp_log hr, ← Real.exp_nsmul]
      simp [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul]
    rw [hpow, ← Real.exp_add]
    ring_nf
  have hfact_pos : 0 < (Nat.factorial m : ℝ) := by positivity
  have hcoef :
      Real.exp (FockSPR.phiFunc m (FockSPR.rStar m)) / (Nat.factorial m : ℝ)
        ≤
      Real.exp (1 / 4) / 2 := by
    have hfac := FockSPR.exp_phi_le_factorial hm
    exact
      (div_le_iff₀ hfact_pos).2
        (by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfac)
  calc
    r ^ (2 * m + 1) * Real.exp (-r ^ 2) / (Nat.factorial m : ℝ)
      = Real.exp (FockSPR.phiFunc m r) / (Nat.factorial m : ℝ) := by
          rw [h_eq]
    _ ≤ Real.exp (FockSPR.phiFunc m (FockSPR.rStar m) - (r - FockSPR.rStar m) ^ 2) /
          (Nat.factorial m : ℝ) := by
            gcongr
            exact FockSPR.phiFunc_quad_bound hm hr
    _ =
      (Real.exp (FockSPR.phiFunc m (FockSPR.rStar m)) / (Nat.factorial m : ℝ)) *
        Real.exp (-(r - FockSPR.rStar m) ^ 2) := by
          rw [sub_eq_add_neg, Real.exp_add]
          field_simp [hfact_pos.ne']
    _ ≤ (Real.exp (1 / 4) / 2) * Real.exp (-(r - FockSPR.rStar m) ^ 2) := by
          exact mul_le_mul_of_nonneg_right hcoef (by positivity)

private lemma normalized_qkn_factor_bound
    (k n i : ℕ)
    (hik : i ∈ Finset.range k)
    (hkn : k < n)
    {r : ℝ}
    (hr : 0 ≤ r) :
    |r ^ 2 - ((n - i : ℕ) : ℝ)| / Real.sqrt ((n - i : ℕ) : ℝ)
      ≤
    (|r - Real.sqrt (n : ℝ)| + k) * (|r - Real.sqrt (n : ℝ)| + k + 2) := by
  have hik' : i < k := Finset.mem_range.mp hik
  have hni_pos : 0 < n - i := by
    omega
  let s : ℝ := Real.sqrt ((n - i : ℕ) : ℝ)
  let y : ℝ := |r - Real.sqrt (n : ℝ)|
  have hs_pos : 0 < s := by
    dsimp [s]
    positivity
  have hs_ge_one : 1 ≤ s := by
    dsimp [s]
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ n - i by omega)
  have hsqrt_shift :
      |Real.sqrt (n : ℝ) - s| ≤ k := by
    dsimp [s]
    simpa using sqrt_nat_sub_shift_le n i k hik' hkn
  have hdist :
      |r - s| ≤ y + k := by
    dsimp [y]
    calc
      |r - s|
        ≤
      |r - Real.sqrt (n : ℝ)| + |Real.sqrt (n : ℝ) - s| := by
          have := abs_add_le (r - Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ) - s)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      _ ≤ y + k := by
          nlinarith
  have hratio :
      r / s + 1 ≤ y + k + 2 := by
    have hr_le : r ≤ |r - s| + s := by
      calc
        r = (r - s) + s := by ring
        _ ≤ |r - s| + s := by
            gcongr
            exact le_abs_self _
    have hdiv : r / s ≤ |r - s| + 1 := by
      calc
        r / s ≤ (|r - s| + s) / s := by
            exact div_le_div_of_nonneg_right hr_le hs_pos.le
        _ = |r - s| / s + 1 := by
            field_simp [hs_pos.ne']
        _ ≤ |r - s| + 1 := by
            have habs_nonneg : 0 ≤ |r - s| := abs_nonneg _
            have hdivabs : |r - s| / s ≤ |r - s| := by
              exact div_le_self habs_nonneg hs_ge_one
            linarith
    linarith [hdist]
  have hfactor :
      |r ^ 2 - ((n - i : ℕ) : ℝ)| / Real.sqrt ((n - i : ℕ) : ℝ)
        =
      |r - s| * (r / s + 1) := by
    have hs_sq : s ^ 2 = ((n - i : ℕ) : ℝ) := by
      dsimp [s]
      rw [Real.sq_sqrt]
      positivity
    calc
      |r ^ 2 - ((n - i : ℕ) : ℝ)| / Real.sqrt ((n - i : ℕ) : ℝ)
        = |r ^ 2 - s ^ 2| / s := by
            rw [hs_sq]
      _ = |(r - s) * (r + s)| / s := by
            congr 1
            ring_nf
      _ = |r - s| * |r + s| / s := by rw [abs_mul]
      _ = |r - s| * (r + s) / s := by
            have hsum_nonneg : 0 ≤ r + s := by positivity
            rw [abs_of_nonneg hsum_nonneg]
      _ = |r - s| * (r / s + 1) := by
            field_simp [hs_pos.ne']
  calc
    |r ^ 2 - ((n - i : ℕ) : ℝ)| / Real.sqrt ((n - i : ℕ) : ℝ)
      = |r - s| * (r / s + 1) := hfactor
    _ ≤ (y + k) * (y + k + 2) := by
          have hyk_nonneg : 0 ≤ y + k := by positivity
          have hratio_nonneg : 0 ≤ r / s + 1 := by
            have hdiv_nonneg : 0 ≤ r / s := by exact div_nonneg hr hs_pos.le
            linarith
          exact mul_le_mul hdist hratio hratio_nonneg hyk_nonneg
    _ = (|r - Real.sqrt (n : ℝ)| + k) * (|r - Real.sqrt (n : ℝ)| + k + 2) := by
          dsimp [y]

private lemma posPart_mono {x y : ℝ} (hxy : x ≤ y) : posPart x ≤ posPart y := by
  unfold posPart
  exact max_le_max hxy le_rfl

private lemma small_centered_gap_le_shell_gap
    (k n j : ℕ)
    (hn : 1 ≤ n)
    (hkn : n ≤ k) :
    posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ))
      ≤
    posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ)) := by
  have hsqrt_ge_one : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith
  have hsqrt_le_k : Real.sqrt (n : ℝ) ≤ (k : ℝ) := by
    exact le_trans hsqrt_le_n (by exact_mod_cast hkn)
  by_cases hjsqrt : Real.sqrt (n : ℝ) ≤ (j : ℝ)
  · have hmain :
        |((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)
          ≤
        (j : ℝ) - ((k + 5 : ℕ) : ℝ) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hjsqrt)]
      norm_num [Nat.cast_add]
      linarith
    exact posPart_mono hmain
  · have hjlt : (j : ℝ) < Real.sqrt (n : ℝ) := lt_of_not_ge hjsqrt
    have hleft_nonpos :
        |((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ) ≤ 0 := by
      rw [abs_of_neg (sub_neg.mpr hjlt)]
      have hj_nonneg : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
      norm_num [Nat.cast_add]
      linarith
    have hleft :
        posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) = 0 := by
      unfold posPart
      exact max_eq_right hleft_nonpos
    rw [hleft]
    unfold posPart
    exact le_max_right _ _

private lemma shell_centered_gap_le_pointwise_gap
    (k n j : ℕ)
    {r : ℝ}
    (hrj : r ∈ Set.Icc (j : ℝ) (((j + 1 : ℕ) : ℝ))) :
    posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ))
      ≤
    posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ)) := by
  have hdist :
      |((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)|
        ≤
      1 + |r - Real.sqrt (n : ℝ)| := by
    calc
      |((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)|
        = |(((j : ℕ) : ℝ) - r) + (r - Real.sqrt (n : ℝ))| := by ring_nf
      _ ≤ |((j : ℕ) : ℝ) - r| + |r - Real.sqrt (n : ℝ)| := abs_add_le _ _
      _ ≤ 1 + |r - Real.sqrt (n : ℝ)| := by
          have hjr : |((j : ℕ) : ℝ) - r| ≤ 1 := by
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hrj.1)]
            have hupper : r - (j : ℝ) ≤ 1 := by
              have := hrj.2
              norm_num at this
              linarith
            linarith
          linarith
  have hmain :
      |((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)
        ≤
      |r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ) := by
    calc
      |((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)
        ≤
      (1 + |r - Real.sqrt (n : ℝ)|) - ((k + 4 : ℕ) : ℝ) := by
          exact sub_le_sub_right hdist _
      _ = |r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ) := by
          norm_num [Nat.cast_add]
          ring
  exact posPart_mono hmain

private theorem phi0_support_zero (k : ℕ) :
    ∃ g : ℕ → ℂ,
      phi0 k = hermiteSeries k g ∧
      (∀ n : ℕ, 0 < n → g n = 0) ∧
      (∀ r : ℝ, 0 < r → ∀ t : Circle,
        phi0 k (circlePoint r t) = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * g 0) := by
  let g : ℕ → ℂ := fun n => if n = 0 then 1 else 0
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa [g, phi0] using (hermiteSeries_single k 0).symm
  · intro n hn
    simp [g, Nat.ne_of_gt hn]
  · intro r hr t
    rw [phi0, phi_polar (k := k) (n := 0) hr t, qkn_zero k hr]
    simp [g]

private theorem phi0_polar_norm_formula
    (k : ℕ)
    {g : ℕ → ℂ}
    (hpolar : ∀ r : ℝ, 0 < r → ∀ t : Circle,
      phi0 k (circlePoint r t) = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * g 0)
    {r θ : ℝ}
    (hr : 0 < r) :
    ‖phi0 k (Complex.polarCoord.symm (r, θ))‖ ^ 2 *
        Real.exp (-‖Complex.polarCoord.symm (r, θ)‖ ^ 2) =
      (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * ‖g 0‖ ^ 2) * Real.exp (-r ^ 2) := by
  have hcircle : circlePoint r (QuotientAddGroup.mk θ : Circle) = Complex.polarCoord.symm (r, θ) :=
    circlePoint_mk_eq_polarCoord_symm r θ
  rw [← hcircle, hpolar r hr (QuotientAddGroup.mk θ : Circle)]
  unfold circleLeadingFactor
  rw [norm_mul, norm_mul]
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Nat.factorial k : ℝ) := Real.sqrt_nonneg _
  have hnorm : ‖circlePoint r (QuotientAddGroup.mk θ : Circle)‖ = r := by
    rw [hcircle, Complex.norm_polarCoord_symm, abs_of_pos hr]
  rw [hnorm]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt_nonneg, abs_of_pos hr]
  ring

private def phi0AnnulusIntegrand (k : ℕ) (g0normsq : ℝ) (r : ℝ) : ℝ :=
  r * (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * g0normsq) * Real.exp (-r ^ 2)

private theorem continuous_phi0AnnulusIntegrand (k : ℕ) (g0normsq : ℝ) :
    Continuous (phi0AnnulusIntegrand k g0normsq) := by
  unfold phi0AnnulusIntegrand
  continuity

private theorem integrableOn_annulus_polar_phi0
    (k j : ℕ)
    (g0normsq : ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ => phi0AnnulusIntegrand k g0normsq p.1)
      ((Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ Set.Ioo (-Real.pi) Real.pi)
      volume := by
  let sclosed : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) (((j + 1 : ℕ) : ℝ)) ×ˢ Set.Icc (-Real.pi) Real.pi
  have hcompact : IsCompact sclosed := isCompact_Icc.prod isCompact_Icc
  have hbase :
      IntegrableOn (fun p : ℝ × ℝ => phi0AnnulusIntegrand k g0normsq p.1) sclosed volume := by
    have hcont : Continuous (fun p : ℝ × ℝ => phi0AnnulusIntegrand k g0normsq p.1) := by
      exact (continuous_phi0AnnulusIntegrand k g0normsq).comp continuous_fst
    exact hcont.continuousOn.integrableOn_compact hcompact
  refine hbase.mono_set ?_
  intro p hp
  rcases hp with ⟨⟨hp0, hpj⟩, hpθ⟩
  refine ⟨?_, ?_⟩
  · refine ⟨le_of_lt hp0, hpj.2.le⟩
  · exact ⟨le_of_lt hpθ.1, le_of_lt hpθ.2⟩

private theorem annulusIntegralSq_phi0_eq
    (k j : ℕ)
    {g : ℕ → ℂ}
    (hpolar : ∀ r : ℝ, 0 < r → ∀ t : Circle,
      phi0 k (circlePoint r t) = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * g 0) :
    annulusIntegralSq (phi0 k) j =
      2 * ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by
  let F : ℂ → ℝ := fun z => ‖phi0 k z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
  have hannulus_meas : MeasurableSet (annulus j) := by
    refine (measurableSet_le measurable_const measurable_norm).inter ?_
    exact measurableSet_lt measurable_norm measurable_const
  unfold HermitekLEAN.annulusIntegralSq HermiteLEAN.annulusIntegralSq
  rw [show (∫ z in annulus j, F z ∂(volume : Measure ℂ)) =
      ∫ z : ℂ, Set.indicator (annulus j) F z ∂(volume : Measure ℂ) by
      symm
      rw [MeasureTheory.integral_indicator hannulus_meas]]
  rw [← Complex.integral_comp_polarCoord_symm (fun z : ℂ => Set.indicator (annulus j) F z)]
  have hpolar_rw :
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 • Set.indicator (annulus j) F (Complex.polarCoord.symm p))
        =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        Set.indicator
          ((Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
            Set.Ioo (-Real.pi) Real.pi)
          (fun p : ℝ × ℝ => phi0AnnulusIntegrand k (‖g 0‖ ^ 2) p.1) p := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    rcases p with ⟨r, θ⟩
    rcases hp with ⟨hrpos, hθ⟩
    have hrpos' : 0 < r := by simpa using hrpos
    by_cases hrj : r ∈ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))
    · have hann :
          Complex.polarCoord.symm (r, θ) ∈ annulus j := by
        change (j : ℝ) ≤ ‖Complex.polarCoord.symm (r, θ)‖ ∧
            ‖Complex.polarCoord.symm (r, θ)‖ < (((j + 1 : ℕ) : ℝ))
        rw [Complex.norm_polarCoord_symm, abs_of_pos hrpos']
        exact hrj
      change
        r * Set.indicator (annulus j) F (Complex.polarCoord.symm (r, θ)) = _
      rw [Set.indicator_of_mem hann,
        Set.indicator_of_mem (show
          (r, θ) ∈
            (Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
              Set.Ioo (-Real.pi) Real.pi from by
            exact ⟨⟨hrpos, hrj⟩, hθ⟩)]
      have hFpolar :
          F (Complex.polarCoord.symm (r, θ))
            =
          (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * ‖g 0‖ ^ 2) * Real.exp (-r ^ 2) := by
        dsimp [F]
        exact phi0_polar_norm_formula k hpolar hrpos'
      rw [hFpolar]
      simp [phi0AnnulusIntegrand, mul_left_comm, mul_comm]
    · have hann :
          Complex.polarCoord.symm (r, θ) ∉ annulus j := by
        intro hz
        apply hrj
        change (j : ℝ) ≤ ‖Complex.polarCoord.symm (r, θ)‖ ∧
            ‖Complex.polarCoord.symm (r, θ)‖ < (((j + 1 : ℕ) : ℝ)) at hz
        rw [Complex.norm_polarCoord_symm, abs_of_pos hrpos'] at hz
        exact hz
      change r * Set.indicator (annulus j) F (Complex.polarCoord.symm (r, θ)) = _
      rw [Set.indicator_of_notMem hann,
        Set.indicator_of_notMem (show
          (r, θ) ∉
            (Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
              Set.Ioo (-Real.pi) Real.pi from by
            intro hmem
            exact hrj hmem.1.2)]
      simp
  change
    (1 / Real.pi) *
        ∫ p in Complex.polarCoord.target,
          p.1 • Set.indicator (annulus j) F (Complex.polarCoord.symm p)
      =
      2 * ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r
  rw [Complex.polarCoord_target, hpolar_rw]
  rw [MeasureTheory.integral_indicator
    ((measurableSet_Ioi.inter measurableSet_Ico).prod measurableSet_Ioo)]
  rw [Measure.restrict_restrict
    ((measurableSet_Ioi.inter measurableSet_Ico).prod measurableSet_Ioo)]
  have hstrip :
      ((Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
          Set.Ioo (-Real.pi) Real.pi) ∩
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)
        =
      (Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
        Set.Ioo (-Real.pi) Real.pi := by
    ext p
    rcases p with ⟨r, θ⟩
    simp [and_left_comm, and_assoc]
  rw [hstrip]
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod _ (integrableOn_annulus_polar_phi0 k j (‖g 0‖ ^ 2))]
  have inner_eq :
      ∀ r : ℝ,
        (∫ θ in Set.Ioo (-Real.pi) Real.pi, phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r)
          =
        T * phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by
    intro r
    have hvol : volume (Set.Ioo (-Real.pi) Real.pi) = ENNReal.ofReal (2 * Real.pi) := by
      rw [Real.volume_Ioo]
      congr 1
      ring
    have hμ :
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi)).real Set.univ = 2 * Real.pi := by
      rw [MeasureTheory.measureReal_restrict_apply_univ]
      rw [MeasureTheory.Measure.real, hvol, ENNReal.toReal_ofReal]
      positivity
    rw [MeasureTheory.integral_const, hμ, smul_eq_mul]
    have hT : T = 2 * Real.pi := by rfl
    rw [hT]
  simp_rw [inner_eq]
  rw [MeasureTheory.integral_const_mul]
  have hT_eq : (1 / Real.pi) * T = 2 := by
    rw [show T = 2 * Real.pi by rfl]
    field_simp
  let srad : Set ℝ := Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))
  let sradClosed : Set ℝ := Set.Ici (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))
  have hIoiIco_ae :
      srad =ᵐ[volume]
      Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)) := by
    have h0 : srad =ᵐ[volume] sradClosed := by
      filter_upwards [Ioi_ae_eq_Ici (a := (0 : ℝ)) (μ := volume)] with x hx
      apply propext
      constructor
      · intro h
        exact ⟨hx.mp h.1, h.2⟩
      · intro h
        exact ⟨hx.mpr h.1, h.2⟩
    have h1 :
        sradClosed
          =
        Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)) := by
      dsimp [sradClosed]
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        refine ⟨?_, hx⟩
        exact le_trans (show (0 : ℝ) ≤ (j : ℝ) by exact_mod_cast Nat.zero_le j) hx.1
    exact h0.trans (Filter.EventuallyEq.of_eq h1)
  have hset_eq :
      (∫ r in srad, phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r)
        =
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by
    calc
      (∫ r in srad, phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r)
        =
      ∫ r in Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r :=
        MeasureTheory.setIntegral_congr_set hIoiIco_ae
      _ =
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by
        rw [intervalIntegral.integral_of_le
          (show (j : ℝ) ≤ (((j + 1 : ℕ) : ℝ)) by exact_mod_cast Nat.le_succ j)]
        have hIcoIoc :
            (∫ r in Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r)
              =
            ∫ r in Set.Ioc (j : ℝ) (((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by
          simpa using
            (MeasureTheory.setIntegral_congr_set
              (f := phi0AnnulusIntegrand k (‖g 0‖ ^ 2))
              (μ := volume)
              (Ico_ae_eq_Ioc (a := (j : ℝ)) (b := (((j + 1 : ℕ) : ℝ)))))
        exact hIcoIoc
  calc
    (1 / Real.pi) *
        (T *
          ∫ r in srad,
            phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r)
      =
    ((1 / Real.pi) * T) *
        ∫ r in srad,
          phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by
            ring
    _ =
      2 *
        ∫ r in srad,
          phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by
            rw [hT_eq]
    _ =
      2 *
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
          phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by
            rw [hset_eq]

private theorem phi0AnnulusIntegrand_le_shell
    (k j : ℕ)
    (g0normsq : ℝ)
    {r : ℝ}
    (hr : r ∈ Set.Icc (j : ℝ) (((j + 1 : ℕ) : ℝ)))
    (hg0 : 0 ≤ g0normsq) :
    phi0AnnulusIntegrand k g0normsq r
      ≤ (g0normsq / (Nat.factorial k : ℝ)) *
          ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
  have hr_nonneg : 0 ≤ r := by
    exact le_trans (by exact_mod_cast Nat.zero_le j) hr.1
  have hsqrt_sq : (Real.sqrt (Nat.factorial k : ℝ)) ^ 2 = (Nat.factorial k : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hpow : r ^ (2 * k + 1) ≤ (((j + 1 : ℕ) : ℝ) ^ (2 * k + 1)) := by
    gcongr
    exact hr.2
  have hexp : Real.exp (-r ^ 2) ≤ Real.exp (-(j : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hr.1, hr.2]
  unfold phi0AnnulusIntegrand
  have hsqrt_nonzero : Real.sqrt (Nat.factorial k : ℝ) ≠ 0 := by
    positivity
  calc
    r * (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * g0normsq) * Real.exp (-r ^ 2)
      = (g0normsq / (Nat.factorial k : ℝ)) * (r ^ (2 * k + 1)) * Real.exp (-r ^ 2) := by
          field_simp [hsqrt_nonzero]
          rw [hsqrt_sq]
          ring
    _ ≤ (g0normsq / (Nat.factorial k : ℝ)) *
          ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
          have hcoeff_nonneg : 0 ≤ g0normsq / (Nat.factorial k : ℝ) := by positivity
          have hprod :
              r ^ (2 * k + 1) * Real.exp (-r ^ 2)
                ≤
              (((j + 1 : ℕ) : ℝ) ^ (2 * k + 1)) * Real.exp (-(j : ℝ) ^ 2) := by
            gcongr
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_of_nonneg_left hprod hcoeff_nonneg)

private theorem annulusIntegralSq_phi0_shell_bound
    (k j : ℕ)
    {g : ℕ → ℂ}
    (hpolar : ∀ r : ℝ, 0 < r → ∀ t : Circle,
      phi0 k (circlePoint r t) = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * g 0) :
    annulusIntegralSq (phi0 k) j ≤
      (2 * (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ))) *
        ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
  rw [annulusIntegralSq_phi0_eq k j hpolar]
  have hint :
      IntervalIntegrable (phi0AnnulusIntegrand k (‖g 0‖ ^ 2))
        volume (j : ℝ) (((j + 1 : ℕ) : ℝ)) := by
    exact (continuous_phi0AnnulusIntegrand k (‖g 0‖ ^ 2)).intervalIntegrable _ _
  have hbound :
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r
        ≤
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
        (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ)) *
          ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
    refine intervalIntegral.integral_mono_on
      (show (j : ℝ) ≤ (((j + 1 : ℕ) : ℝ)) by exact_mod_cast Nat.le_succ j)
      hint
      intervalIntegrable_const
      ?_
    intro r hr
    exact phi0AnnulusIntegrand_le_shell k j (‖g 0‖ ^ 2) hr (by positivity)
  have hconst :
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
        (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ)) *
          ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2)
        =
      (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ)) *
        ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
    rw [intervalIntegral.integral_const]
    norm_num
  calc
    2 * ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r
      ≤
    2 * ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
      (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ)) *
        ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
          gcongr
    _ =
      (2 * (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ))) *
        ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
          rw [hconst]
          ring

/-- Localization of the lowest vector `Phi k 0`. -/
theorem phi0_localization :
    ∀ k : ℕ,
      ∃ C c : ℝ,
        0 < C ∧ 0 < c ∧
          ∀ j : ℕ,
            annulusIntegralSq (phi0 k) j ≤
              C * Real.exp (-c * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := by
  intro k
  obtain ⟨g, _, _, hpolar⟩ := phi0_support_zero k
  let m : ℕ := 2 * k + 1
  obtain ⟨Cpoly, hCpoly_pos, hCpoly⟩ :=
    HermiteLEAN.polynomial_times_gaussian_le_gaussian (a := 1) (by norm_num) m
  let A : ℝ :=
    (2 * (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ))) * ((((k + 6 : ℕ) : ℝ) ^ m)) * (2 ^ (m - 1))
  let C : ℝ := A * Cpoly + 1
  refine ⟨C, (1 : ℝ) / 2, by positivity, by norm_num, ?_⟩
  intro j
  let x : ℝ := posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, posPart]
    exact le_max_right _ _
  have hx_le_j : x ≤ (j : ℝ) := by
    dsimp [x, posPart]
    refine max_le ?_ ?_
    · linarith
    · exact_mod_cast Nat.zero_le j
  have hj1_le : (((j + 1 : ℕ) : ℝ)) ≤ (((k + 6 : ℕ) : ℝ)) * (x + 1) := by
    have hx_lb : (j : ℝ) - ((k + 5 : ℕ) : ℝ) ≤ x := by
      dsimp [x, posPart]
      exact le_max_left _ _
    have hkcast : (((k + 6 : ℕ) : ℝ)) = ((k + 5 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    have hsum' : (j : ℝ) + 1 ≤ x + (((k + 6 : ℕ) : ℝ)) := by
      rw [hkcast]
      linarith
    have hsum : (((j + 1 : ℕ) : ℝ)) ≤ x + (((k + 6 : ℕ) : ℝ)) := by
      simpa [Nat.cast_add, Nat.cast_one] using hsum'
    have hk6_ge1_nat : 1 ≤ k + 6 := by omega
    have hk6_ge1 : (1 : ℝ) ≤ (((k + 6 : ℕ) : ℝ)) := by exact_mod_cast hk6_ge1_nat
    have hmul : x + (((k + 6 : ℕ) : ℝ)) ≤ (((k + 6 : ℕ) : ℝ)) * (x + 1) := by
      nlinarith
    exact le_trans hsum hmul
  have hpoly1 : (((j + 1 : ℕ) : ℝ) ^ m) ≤ ((((k + 6 : ℕ) : ℝ) ^ m)) * ((x + 1) ^ m) := by
    calc
      (((j + 1 : ℕ) : ℝ) ^ m) ≤ ((((k + 6 : ℕ) : ℝ) * (x + 1)) ^ m) := by
        gcongr
      _ = ((((k + 6 : ℕ) : ℝ) ^ m)) * ((x + 1) ^ m) := by rw [mul_pow]
  have hpoly2 : (x + 1) ^ m ≤ 2 ^ (m - 1) * (x ^ m + 1) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_pow_le hx_nonneg (show (0 : ℝ) ≤ 1 by norm_num) m
  have hpoly :
      (((j + 1 : ℕ) : ℝ) ^ m) ≤ ((((k + 6 : ℕ) : ℝ) ^ m)) * (2 ^ (m - 1)) * (1 + x ^ m) := by
    calc
      (((j + 1 : ℕ) : ℝ) ^ m) ≤ ((((k + 6 : ℕ) : ℝ) ^ m)) * ((x + 1) ^ m) := hpoly1
      _ ≤ ((((k + 6 : ℕ) : ℝ) ^ m)) * (2 ^ (m - 1) * (x ^ m + 1)) := by
            gcongr
      _ = ((((k + 6 : ℕ) : ℝ) ^ m)) * (2 ^ (m - 1)) * (1 + x ^ m) := by ring
  have hexp : Real.exp (-(j : ℝ) ^ 2) ≤ Real.exp (-x ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hx_nonneg, hx_le_j]
  have hshell := annulusIntegralSq_phi0_shell_bound k j hpolar
  have hmain :
      annulusIntegralSq (phi0 k) j ≤ A * (1 + x ^ m) * Real.exp (-x ^ 2) := by
    calc
      annulusIntegralSq (phi0 k) j
        ≤ (2 * (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ))) * ((((j + 1 : ℕ) : ℝ) ^ m)) *
            Real.exp (-(j : ℝ) ^ 2) := by
              simpa [m] using hshell
      _ ≤ (2 * (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ))) *
            ((((k + 6 : ℕ) : ℝ) ^ m) * (2 ^ (m - 1)) * (1 + x ^ m)) * Real.exp (-x ^ 2) := by
              gcongr
      _ = A * (1 + x ^ m) * Real.exp (-x ^ 2) := by
              dsimp [A]
              ring
  have hgauss : (1 + x ^ m) * Real.exp (-x ^ 2) ≤ Cpoly * Real.exp (-((1 : ℝ) / 2) * x ^ 2) := by
    simpa [one_mul] using hCpoly x hx_nonneg
  have hA_nonneg : 0 ≤ A := by positivity
  calc
    annulusIntegralSq (phi0 k) j
      ≤ A * (1 + x ^ m) * Real.exp (-x ^ 2) := hmain
    _ ≤ A * (Cpoly * Real.exp (-((1 : ℝ) / 2) * x ^ 2)) := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgauss hA_nonneg
    _ ≤ (A * Cpoly + 1) * Real.exp (-((1 : ℝ) / 2) * x ^ 2) := by
          have hexp_nonneg : 0 ≤ Real.exp (-((1 : ℝ) / 2) * x ^ 2) := (Real.exp_pos _).le
          have hcoeff : A * Cpoly ≤ A * Cpoly + 1 := by linarith
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff hexp_nonneg
    _ = C * Real.exp (-((1 : ℝ) / 2) * x ^ 2) := by rfl
    _ = C * Real.exp (-((1 : ℝ) / 2) * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := by
          rfl

private theorem qkn_eventual_upper_bound (k n : ℕ) :
    ∃ R C : ℝ,
      1 ≤ R ∧ 0 < C ∧ ∀ r ≥ R, ‖(qkn k n r : ℂ)‖ ≤ C * r ^ n := by
  let c : ℝ := (1 / Real.sqrt (Nat.factorial n : ℝ))
  obtain ⟨R0, hR0, hR0_bound⟩ := qkn_top_term_limit k n 1 zero_lt_one
  let C : ℝ := ‖(c : ℂ)‖ + 1
  refine ⟨R0, C, hR0, by positivity, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := le_trans hR0 hr
  have hr_nonneg : 0 ≤ r := by linarith
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrpow_nonneg : 0 ≤ r ^ n := pow_nonneg hr_nonneg n
  have hrpow_pos : 0 < r ^ n := pow_pos hr_pos n
  have hden : ‖(r ^ n : ℂ)‖ = r ^ n := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
  have hdiv_norm :
      ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖ = ‖(qkn k n r : ℂ)‖ / r ^ n := by
    rw [norm_div, hden]
  have hclose : ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖ ≤ C := by
    calc
      ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖
        ≤ ‖(qkn k n r : ℂ) / (r ^ n : ℂ) - (c : ℂ)‖ + ‖(c : ℂ)‖ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (norm_add_le ((qkn k n r : ℂ) / (r ^ n : ℂ) - (c : ℂ)) (c : ℂ))
      _ ≤ 1 + ‖(c : ℂ)‖ := by
            have htop := hR0_bound r hr
            have htop' : ‖(qkn k n r : ℂ) / (r ^ n : ℂ) - (c : ℂ)‖ ≤ 1 := by
              simpa [c] using htop
            have hc_nonneg : 0 ≤ ‖(c : ℂ)‖ := norm_nonneg _
            nlinarith
      _ = C := by
            dsimp [C, c]
            ring
  have hclose' : ‖(qkn k n r : ℂ)‖ / r ^ n ≤ C := by
    rw [hdiv_norm] at hclose
    exact hclose
  have hmul := mul_le_mul_of_nonneg_right hclose' hrpow_nonneg
  have hrewrite : (‖(qkn k n r : ℂ)‖ / r ^ n) * r ^ n = ‖(qkn k n r : ℂ)‖ := by
    field_simp [hrpow_pos.ne']
  calc
    ‖(qkn k n r : ℂ)‖ = (‖(qkn k n r : ℂ)‖ / r ^ n) * r ^ n := by
      rw [hrewrite]
    _ ≤ C * r ^ n := hmul

private theorem qkn_integrand_eventual_gamma_bound (k n : ℕ) :
    ∃ R C : ℝ,
      1 ≤ R ∧ 0 < C ∧
        ∀ r : ℝ, R ≤ r →
          r * (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
              Real.exp (-r ^ 2)
            ≤
          C * r ^ (2 * n + 2 * k + 1) * Real.exp (-r ^ 2) := by
  obtain ⟨R, C0, hR, hC0, hbound⟩ := qkn_eventual_upper_bound k n
  refine ⟨R, (C0 ^ 2) / (Nat.factorial k : ℝ), hR, by positivity, ?_⟩
  intro r hr
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one (le_trans hR hr)
  have hsqrt_pos : 0 < Real.sqrt (Nat.factorial k : ℝ) := by positivity
  have hq : |qkn k n r| ≤ C0 * r ^ n := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg] using hbound r hr
  have hq2mul : |qkn k n r| * |qkn k n r| ≤ (C0 * r ^ n) * (C0 * r ^ n) := by
    exact mul_le_mul hq hq (abs_nonneg _) (mul_nonneg (le_of_lt hC0) (pow_nonneg hr_nonneg _))
  have hq2 : |qkn k n r| ^ 2 ≤ (C0 * r ^ n) ^ 2 := by
    simpa [pow_two] using hq2mul
  have hmain :
      r * (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
          Real.exp (-r ^ 2)
        ≤
      r * (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * (C0 * r ^ n) ^ 2) *
          Real.exp (-r ^ 2) := by
    gcongr
  calc
    r * (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
        Real.exp (-r ^ 2)
      ≤
      r * (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * (C0 * r ^ n) ^ 2) *
        Real.exp (-r ^ 2) := hmain
    _ = (C0 ^ 2 / (Nat.factorial k : ℝ)) * r ^ (2 * n + 2 * k + 1) * Real.exp (-r ^ 2) := by
        have hsq : (Real.sqrt (Nat.factorial k : ℝ)) ^ 2 = (Nat.factorial k : ℝ) := by
          rw [Real.sq_sqrt]
          positivity
        have hC0sq : (C0 * r ^ n) ^ 2 = C0 ^ 2 * r ^ (2 * n) := by
          ring_nf
        have hratio :
            (r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2 =
              r ^ (2 * k) / (Nat.factorial k : ℝ) := by
          field_simp [Real.sqrt_ne_zero'.2 (by positivity), hsq]
          have hkpow : (r ^ k) ^ 2 = r ^ (2 * k) := by
            rw [← pow_mul, show k * 2 = 2 * k by omega]
          rw [hsq, hkpow, mul_comm]
        rw [hC0sq, hratio]
        ring

/-- The product `r^k * qkn(k,n,r)` equals `(1/√n!) * r^{n-k} * Pkn(k,n).eval(r²)`.
This is the correct formula using the Charlier polynomial evaluation,
replacing the false product-of-linear-factors version. -/
private theorem qkn_mul_rpow_eq_Pkn_eval
    (k n : ℕ)
    {r : ℝ}
    (hr : 0 < r)
    (hkn : k ≤ n) :
    r ^ k * qkn k n r =
      (1 / Real.sqrt (Nat.factorial n : ℝ)) *
        r ^ (n - k) * (Pkn k n).eval (r ^ 2) := by
  rw [qkn_eq_Pkn k n hr hkn]
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hzpow :
      r ^ k * r ^ ((n : ℤ) - 2 * (k : ℤ)) = r ^ (n - k) := by
    rw [← zpow_natCast, ← zpow_add₀ hr0]
    have hexp :
        ((k : ℤ) + ((n : ℤ) - 2 * (k : ℤ))) = (((n - k : ℕ) : ℤ)) := by
      omega
    rw [hexp, zpow_natCast]
  calc
    r ^ k * ((1 / Real.sqrt (Nat.factorial n : ℝ)) * r ^ ((n : ℤ) - 2 * (k : ℤ)) *
        (Pkn k n).eval (r ^ 2))
      = (1 / Real.sqrt (Nat.factorial n : ℝ)) *
          (r ^ k * r ^ ((n : ℤ) - 2 * (k : ℤ))) * (Pkn k n).eval (r ^ 2) := by ring
    _ = (1 / Real.sqrt (Nat.factorial n : ℝ)) *
          r ^ (n - k) * (Pkn k n).eval (r ^ 2) := by rw [hzpow]

/-- The radial integrand for `|Phi k n|² exp(-|z|²)` after polar decomposition.
Uses the correct Charlier/Laguerre polynomial evaluation, NOT the false
product-of-linear-factors formula. -/
private def phiLargeIntegrand (k n : ℕ) (r : ℝ) : ℝ :=
  (1 / ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) *
    r ^ (2 * (n - k) + 1) * ((Pkn k n).eval (r ^ 2)) ^ 2 *
    Real.exp (-r ^ 2)

-- Helper: for 0 ≤ r and 0 ≤ m ≤ 2*k, r^m ≤ 1 + r^(2*k)
private lemma pow_le_one_add_pow_of_le {r : ℝ} (hr : 0 ≤ r) {m : ℕ} {k : ℕ}
    (hm : m ≤ 2 * k) : r ^ m ≤ 1 + r ^ (2 * k) := by
  rcases le_or_gt r 1 with h1 | h1
  · -- r ≤ 1: r^m ≤ 1 ≤ 1 + r^(2k)
    have : r ^ m ≤ 1 := pow_le_one₀ hr h1
    linarith [pow_nonneg hr (2 * k)]
  · -- r > 1: r^m ≤ r^(2k) ≤ 1 + r^(2k)
    have : r ^ m ≤ r ^ (2 * k) := pow_le_pow_right₀ h1.le hm
    linarith

-- Helper: zpow to pow conversion for positive reals
private lemma zpow_mul_pow_eq {r : ℝ} (hr : 0 < r) (k n j : ℕ) (hjn : j ≤ n)
    (hnk : n ≤ k) :
    r ^ k * r ^ ((↑n : ℤ) - 2 * (↑j : ℤ)) = r ^ (k + n - 2 * j) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hexp : (↑k : ℤ) + ((↑n : ℤ) - 2 * (↑j : ℤ)) = ↑(k + n - 2 * j) := by
    have : 2 * j ≤ 2 * n := by omega
    have : 2 * j ≤ k + n := by omega
    omega
  rw [← zpow_natCast r k, ← zpow_add₀ hr0, hexp, zpow_natCast]

private theorem qkn_small_n_growth
    (k n : ℕ)
    (hn : 1 ≤ n)
    (hkn : n ≤ k)
    {r : ℝ}
    (hr : 0 ≤ r) :
    |r ^ k * qkn k n r| ≤
      (((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k * (k : ℝ) ^ k) * (1 + r ^ (2 * k)) := by
  -- Case split: r = 0 vs r > 0
  rcases eq_or_lt_of_le hr with rfl | hr_pos
  · -- r = 0
    have hk : 0 < k := lt_of_lt_of_le hn hkn
    rw [zero_pow hk.ne', zero_mul, abs_zero]
    positivity
  · -- r > 0: use qkn_explicit
    rw [qkn_explicit hr_pos, Nat.min_eq_right hkn]
    -- Goal: |r^k * (1/√(n!) * Σ_{j=0}^{n} ...)| ≤ C * (1 + r^(2k))
    have hfact_pos : (0 : ℝ) < ↑n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hsq_pos : (0 : ℝ) < Real.sqrt (↑n.factorial) := Real.sqrt_pos_of_pos hfact_pos
    have hc_nn : 0 ≤ 1 / Real.sqrt (↑n.factorial) := by positivity
    have hc_le : 1 / Real.sqrt (↑n.factorial) ≤ 1 := by
      rw [div_le_one hsq_pos, Real.one_le_sqrt]
      exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
    -- Main bound: use transitivity through three intermediate steps
    have hrk_nn : 0 ≤ r ^ k := pow_nonneg hr_pos.le k
    -- Bound each summand: r^k * |term_j| ≤ C(k,j) * descFact(n,j) * (1 + r^(2k))
    have hterm_bound : ∀ j ∈ Finset.range (n + 1),
        r ^ k * (↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
          |r ^ ((↑n : ℤ) - 2 * ↑j)|) ≤
        ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
          (1 + r ^ (2 * k)) := by
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hcoeff_nn : (0 : ℝ) ≤ ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) := by
        positivity
      rw [mul_comm (r ^ k) _, mul_assoc]
      gcongr
      rw [abs_of_pos (zpow_pos hr_pos _), mul_comm]
      rw [zpow_mul_pow_eq hr_pos k n j hjn hkn]
      exact pow_le_one_add_pow_of_le hr_pos.le (by omega)
    -- Bound coefficients: C(k,j) * descFact(n,j) ≤ 2^k * k^k
    have hcoeff_bound : ∀ j ∈ Finset.range (n + 1),
        (↑(k.choose j) : ℝ) * (↑n.factorial / ↑(n - j).factorial) ≤
        (2 : ℝ) ^ k * (k : ℝ) ^ k := by
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hfact_nj : (0 : ℝ) < ↑(n - j).factorial := by
        exact_mod_cast Nat.factorial_pos (n - j)
      have hchoose_le : (↑(k.choose j) : ℝ) ≤ (2 : ℝ) ^ k := by
        exact_mod_cast Nat.choose_le_two_pow k j
      have hdesc_le : (↑n.factorial : ℝ) / ↑(n - j).factorial ≤ (k : ℝ) ^ k := by
        rw [div_le_iff₀ hfact_nj]
        have hfact_eq : (↑n.factorial : ℝ) =
            ↑((n - j).factorial) * ↑(n.descFactorial j) := by
          push_cast [← Nat.factorial_mul_descFactorial hjn]; ring
        rw [hfact_eq, mul_comm]
        gcongr
        have h1 : n.descFactorial j ≤ n ^ j := Nat.descFactorial_le_pow n j
        have h2 : n ^ j ≤ k ^ j := Nat.pow_le_pow_left hkn j
        have h3 : k ^ j ≤ k ^ k := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · have : n = 0 := Nat.eq_zero_of_le_zero hkn
            subst this; simp only [Nat.le_zero] at hjn; subst hjn; simp
          · exact Nat.pow_le_pow_right hk (by omega)
        exact_mod_cast le_trans (le_trans h1 h2) h3
      exact mul_le_mul hchoose_le hdesc_le (by positivity) (by positivity)
    -- Assemble the bound
    have h1p : 0 ≤ 1 + r ^ (2 * k) := by positivity
    calc |r ^ k * (1 / Real.sqrt (↑n.factorial) *
          ∑ j ∈ Finset.range (n + 1),
            (-1) ^ j * ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
              r ^ ((↑n : ℤ) - 2 * ↑j))|
      ≤ r ^ k * (∑ j ∈ Finset.range (n + 1),
            ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
              |r ^ ((↑n : ℤ) - 2 * ↑j)|) := by
          rw [abs_mul, abs_of_nonneg hrk_nn]
          gcongr
          calc |1 / Real.sqrt (↑n.factorial) *
                ∑ j ∈ Finset.range (n + 1),
                  (-1) ^ j * ↑(k.choose j) *
                    (↑n.factorial / ↑(n - j).factorial) *
                    r ^ ((↑n : ℤ) - 2 * ↑j)|
            ≤ |1 / Real.sqrt (↑n.factorial)| *
                |∑ j ∈ Finset.range (n + 1),
                  (-1) ^ j * ↑(k.choose j) *
                    (↑n.factorial / ↑(n - j).factorial) *
                    r ^ ((↑n : ℤ) - 2 * ↑j)| := le_of_eq (abs_mul _ _)
            _ ≤ 1 * ∑ j ∈ Finset.range (n + 1),
                  ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
                    |r ^ ((↑n : ℤ) - 2 * ↑j)| := by
              gcongr
              · rw [abs_of_nonneg hc_nn]; exact hc_le
              · calc |∑ j ∈ Finset.range (n + 1), _|
                  ≤ ∑ j ∈ Finset.range (n + 1),
                      |(-1) ^ j * ↑(k.choose j) *
                        (↑n.factorial / ↑(n - j).factorial) *
                        r ^ ((↑n : ℤ) - 2 * ↑j)| :=
                    Finset.abs_sum_le_sum_abs _ _
                  _ ≤ ∑ j ∈ Finset.range (n + 1),
                      ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
                        |r ^ ((↑n : ℤ) - 2 * ↑j)| := by
                    apply Finset.sum_le_sum; intro j hj
                    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
                      abs_of_nonneg (by exact_mod_cast Nat.zero_le (k.choose j)),
                      abs_of_nonneg (div_nonneg (by exact_mod_cast Nat.zero_le _)
                        (by exact_mod_cast Nat.zero_le _))]
            _ = _ := one_mul _
      _ ≤ (∑ j ∈ Finset.range (n + 1),
            ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial)) *
              (1 + r ^ (2 * k)) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_le_sum hterm_bound
      _ ≤ (((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k * (k : ℝ) ^ k) *
              (1 + r ^ (2 * k)) := by
          gcongr
          calc ∑ j ∈ Finset.range (n + 1),
                (↑(k.choose j) : ℝ) * (↑n.factorial / ↑(n - j).factorial)
            ≤ ∑ _j ∈ Finset.range (n + 1), (2 : ℝ) ^ k * (k : ℝ) ^ k :=
              Finset.sum_le_sum hcoeff_bound
            _ = (↑(n + 1) : ℝ) * ((2 : ℝ) ^ k * (k : ℝ) ^ k) := by
              rw [Finset.sum_const, Finset.card_range]; push_cast; ring
            _ ≤ ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k * (k : ℝ) ^ k := by
              rw [mul_assoc]; gcongr

-- Helper: descFactorial shift identity (ℕ level)
private lemma descFactorial_succ_shift (n : ℕ) (s : ℕ) (hs : 1 ≤ s) :
    (n + 1).descFactorial s = n.descFactorial s + s * n.descFactorial (s - 1) := by
  obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  simp only [show s' + 1 - 1 = s' from by omega]
  rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
  rcases Nat.eq_zero_or_pos (n.descFactorial s') with h | h
  · simp [h]
  · have hsn : s' ≤ n := by
      by_contra h'; push Not at h'
      exact Nat.pos_iff_ne_zero.mp h (Nat.descFactorial_eq_zero_iff_lt.mpr h')
    rw [← Nat.add_mul, show (n - s') + (s' + 1) = n + 1 from by omega]

-- Shift identity: Pkn(k+1, n+1) = Pkn(k+1, n) - C(k+1) * Pkn(k, n)
private lemma Pkn_shift (k n : ℕ) :
    Pkn (k + 1) (n + 1) = Pkn (k + 1) n - Polynomial.C (↑(k + 1) : ℝ) * Pkn k n := by
  ext m
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rw [Pkn_coeff_single (k+1) (n+1) m, Pkn_coeff_single (k+1) n m, Pkn_coeff_single k n m]
  by_cases hm1 : m ≤ k + 1
  · by_cases hm2 : m ≤ k
    · simp only [hm1, hm2, ite_true]
      have hkm1 : k + 1 - m - 1 = k - m := by omega
      have hdF_nat : (n + 1).descFactorial (k + 1 - m) =
          n.descFactorial (k + 1 - m) + (k + 1 - m) * n.descFactorial (k - m) := by
        have h := descFactorial_succ_shift n (k + 1 - m) (by omega)
        rwa [hkm1] at h
      have hch_nat : (k + 1).choose (k + 1 - m) * (k + 1 - m) = (k + 1) * k.choose (k - m) := by
        have hs : k - m + 1 = k + 1 - m := by omega
        have := Nat.add_one_mul_choose_eq k (k - m)
        rw [hs] at this; linarith
      have hdF_R : ((n + 1).descFactorial (k + 1 - m) : ℝ) =
          (n.descFactorial (k + 1 - m) : ℝ) +
            ((k + 1 - m : ℕ) : ℝ) * (n.descFactorial (k - m) : ℝ) := by
        exact_mod_cast hdF_nat
      have hch_R : ((k + 1).choose (k + 1 - m) : ℝ) * ((k + 1 - m : ℕ) : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k.choose (k - m) : ℕ) : ℝ) := by
        exact_mod_cast hch_nat
      have hpow : ((-1 : ℝ) ^ (k + 1 - m)) = -((-1 : ℝ) ^ (k - m)) := by
        rw [show k + 1 - m = (k - m) + 1 from by omega, pow_succ]; ring
      rw [hdF_R, hpow]
      set p := ((-1 : ℝ) ^ (k - m))
      set A := ((↑((k + 1).choose (k + 1 - m))) : ℝ)
      set B := ((↑(k + 1 - m : ℕ)) : ℝ)
      set D := ((↑(n.descFactorial (k + 1 - m))) : ℝ)
      set E := ((↑(n.descFactorial (k - m))) : ℝ)
      set F := ((↑(k.choose (k - m))) : ℝ)
      have hab : A * B = (↑(k + 1) : ℝ) * F := hch_R
      have : -p * A * (D + B * E) = -p * A * D - (↑(k + 1) : ℝ) * (p * F * E) := by
        have step : -p * A * (D + B * E) = -p * A * D - p * (A * B) * E := by ring
        rw [step, hab]; ring
      linarith
    · push Not at hm2
      have hm_eq : m = k + 1 := by omega
      subst hm_eq
      simp only [show ¬(k + 1 ≤ k) from by omega, ite_false]
      simp
  · push Not at hm1
    simp only [show ¬(m ≤ k + 1) from by omega, show ¬(m ≤ k) from by omega,
      ite_false, mul_zero, sub_zero]

-- Combined identity: Pkn(k+2, n+1) = (X - C(n+1)) * Pkn(k+1, n) - C(k+1)*X*Pkn(k, n)
private lemma Pkn_combined (k n : ℕ) :
    Pkn (k + 2) (n + 1) =
      (Polynomial.X - Polynomial.C ((n + 1 : ℕ) : ℝ)) * Pkn (k + 1) n -
        Polynomial.C ((k + 1 : ℕ) : ℝ) * Polynomial.X * Pkn k n := by
  have h1 := Pkn_succ_succ k (n + 1)
  have h2 := Pkn_shift k n
  rw [h2] at h1
  rw [h1, show (n + 1 : ℕ) - 1 = n from by omega]
  simp only [map_mul]; ring

/-- GPT Lemma 3.1 (scaled Laguerre bound): For fixed k, there exists A_k > 0 such that
for all n ≥ k and all x ≥ 0, with m = n - k + 1:
  |Pkn(k,n).eval(x)| ≤ A_k * m^{k/2} * (1 + |x - m| / √m)^k.

Proved by induction on k using `Pkn_combined` (derived from `Pkn_succ_succ` + `Pkn_shift`).
Base cases: Pkn(0,n) = 1, Pkn(1,n)(x) = x - n.
Step: use Pkn(k+2,n) = (x-n)*Pkn(k+1,n-1) - (k+1)*x*Pkn(k,n-1) and bound. -/
private theorem scaled_laguerre_bound_Pkn (k : ℕ) :
    ∃ Ak : ℝ, 0 < Ak ∧
      ∀ (n : ℕ) (_hkn : k ≤ n) (x : ℝ),
        |(Pkn k n).eval x| ≤
          Ak * ((n - k + 1 : ℝ) ^ ((k : ℝ) / 2)) *
            (1 + |x - (n - k + 1 : ℝ)| / Real.sqrt (n - k + 1 : ℝ)) ^ k := by
  -- Induction on k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  match k with
  | 0 =>
    -- Base case k = 0: Pkn(0,n) = 1
    use 1; constructor; · norm_num
    intro n _ x
    rw [Pkn_eval]; simp
  | 1 =>
    -- Base case k = 1: Pkn(1,n)(x) = x - n, m = n.
    -- |x - n| ≤ 1 * n^(1/2) * (1 + |x-n|/√n) = √n + |x-n|
    use 1; constructor; · norm_num
    intro n hn x
    have hn_R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hm_pos : (0 : ℝ) < (n : ℝ) := by linarith
    have hm_eq : (n : ℝ) - (1 : ℕ) + 1 = (n : ℝ) := by push_cast; linarith
    -- Simplify Pkn 1 n eval x = x - n
    have heval : (Pkn 1 n).eval x = x - (n : ℝ) := by
      rw [Pkn_eval]; simp [Finset.sum_range_succ]; ring
    rw [heval, hm_eq]
    -- Goal: |x - n| ≤ 1 * n^(↑1/2) * (1 + |x - n| / √n)^1
    rw [one_mul, pow_one, Real.sqrt_eq_rpow]
    -- Normalize the Nat.cast in the exponent
    simp only [Nat.cast_one]
    -- Goal: |x - n| ≤ n^(1/2) * (1 + |x - n| / n^(1/2))
    have h_rpow_pos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2) := by positivity
    rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt h_rpow_pos)]
    linarith [Real.rpow_nonneg (le_of_lt hm_pos) ((1 : ℝ) / 2)]
  | k + 2 =>
    -- Inductive step for k + 2. Use IH for k + 1 and k.
    obtain ⟨Ak1, hAk1_pos, hAk1_bound⟩ := ih (k + 1) (by omega)
    obtain ⟨Ak, hAk_pos, hAk_bound⟩ := ih k (by omega)
    -- The constant: we need Ak2 such that the bound closes.
    -- Using the analysis: Ak2 = (k+3) * Ak1 + (k+1) * 4^(k+1) * Ak
    use (k + 3) * Ak1 + (k + 1) * 4 ^ (k + 1) * Ak
    constructor
    · positivity
    intro n hkn x
    -- We have n ≥ k + 2. Set N = n - 1, so n = N + 1 and N ≥ k + 1.
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    have hNk1 : k + 1 ≤ N := by omega
    have hNk : k ≤ N := by omega
    -- Centers: for Pkn(k+2, N+1), m = (N+1)-(k+2)+1 = N-k
    --          for Pkn(k+1, N),    m' = N-(k+1)+1 = N-k    (same!)
    --          for Pkn(k, N),      m'' = N-k+1              (m+1)
    -- So m = N - k and the k+1 term has the same center.
    -- The k term has center m+1 which needs a shift estimate.
    set m := (N - k : ℕ) with hm_def
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    -- Use Pkn_combined eval form
    have hcomb_eval : (Pkn (k + 2) (N + 1)).eval x =
        (x - ↑(N + 1)) * (Pkn (k + 1) N).eval x -
          ↑(k + 1) * x * (Pkn k N).eval x := by
      have h := Pkn_combined k N
      have := congr_arg (fun p => p.eval x) h
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C] at this
      push_cast at this ⊢; linarith
    -- Triangle inequality
    have htri : |(Pkn (k + 2) (N + 1)).eval x| ≤
        |x - ↑(N + 1)| * |(Pkn (k + 1) N).eval x| +
          ↑(k + 1) * |x| * |(Pkn k N).eval x| := by
      rw [hcomb_eval]
      have h1 : |x - ↑(N + 1)| * |(Pkn (k + 1) N).eval x| =
                |(x - ↑(N + 1)) * (Pkn (k + 1) N).eval x| :=
        (abs_mul _ _).symm
      have h2 : ↑(k + 1) * |x| * |(Pkn k N).eval x| = |↑(k + 1) * x * (Pkn k N).eval x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ↑(k + 1))]
      rw [h1, h2]
      exact abs_sub _ _
    -- Simplify centers: ↑(N+1) - ↑(k+2) + 1 = ↑m, ↑N - ↑(k+1) + 1 = ↑m, ↑N - ↑k + 1 = ↑m + 1
    have hm_cast : (m : ℝ) = (N : ℝ) - (k : ℝ) := by
      rw [hm_def]; push_cast [Nat.cast_sub hNk]; ring
    have hcenter : (↑(N + 1) : ℝ) - ↑(k + 2) + 1 = (m : ℝ) := by push_cast; linarith
    have hcenter1 : (↑N : ℝ) - ↑(k + 1) + 1 = (m : ℝ) := by push_cast; linarith
    have hcenter0 : (↑N : ℝ) - ↑k + 1 = (m : ℝ) + 1 := by linarith
    -- Apply IH for k+1 at N
    have hIH1 := hAk1_bound N hNk1 x
    rw [hcenter1] at hIH1
    -- Apply IH for k at N
    have hIH0 := hAk_bound N hNk x
    rw [hcenter0] at hIH0
    -- Rewrite the goal center
    rw [hcenter]
    -- Setup S = √m + |x - m| and key properties
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 0 ≤ m by omega)
    have hsqrt_pos : 0 < Real.sqrt (m : ℝ) :=
      Real.sqrt_pos_of_pos hm_pos
    have hsqrt_ne : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
    -- S^ℓ = m^(ℓ/2) * (1+|x-m|/√m)^ℓ
    have hSform : ∀ (y : ℝ) (ℓ : ℕ),
        (m : ℝ) ^ ((ℓ : ℝ) / 2) * (1 + |y| / Real.sqrt (m : ℝ)) ^ ℓ =
          (Real.sqrt (m : ℝ) + |y|) ^ ℓ := by
      intro y ℓ
      have h1 : (m : ℝ) ^ ((ℓ : ℝ) / 2) = (Real.sqrt (m : ℝ)) ^ ℓ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((m : ℝ) ^ ((1 : ℝ) / 2)) ℓ,
            ← Real.rpow_mul hm_nn]
        congr 1
        ring
      rw [h1, ← mul_pow, mul_add, mul_one, mul_div_cancel₀ _ hsqrt_ne]
    set S := Real.sqrt (m : ℝ) + |x - (m : ℝ)| with hS_def
    have hS_pos : 0 < S := by linarith [abs_nonneg (x - (m : ℝ))]
    have hS_ge_one : 1 ≤ S := by
      have : 1 ≤ Real.sqrt (m : ℝ) := by
        rw [Real.one_le_sqrt]; exact_mod_cast (show 1 ≤ m by omega)
      linarith [abs_nonneg (x - (m : ℝ))]
    -- Convert goal to S form via suffices
    suffices hgoal : |(Pkn (k + 2) (N + 1)).eval x| ≤
        (((k : ℝ) + 3) * Ak1 + ((k : ℝ) + 1) * 4 ^ (k + 1) * Ak) * S ^ (k + 2) by
      have hconv : S ^ (k + 2) =
          (m : ℝ) ^ ((↑(k + 2) : ℝ) / 2) *
            (1 + |x - (m : ℝ)| / Real.sqrt (m : ℝ)) ^ (k + 2) :=
        (hSform _ _).symm
      rw [show (((k : ℝ) + 3) * Ak1 + ((k : ℝ) + 1) * 4 ^ (k + 1) * Ak) *
            (m : ℝ) ^ ((↑(k + 2) : ℝ) / 2) *
            (1 + |x - (m : ℝ)| / Real.sqrt (m : ℝ)) ^ (k + 2) =
          (((k : ℝ) + 3) * Ak1 + ((k : ℝ) + 1) * 4 ^ (k + 1) * Ak) *
            ((m : ℝ) ^ ((↑(k + 2) : ℝ) / 2) *
            (1 + |x - (m : ℝ)| / Real.sqrt (m : ℝ)) ^ (k + 2)) from by ring]
      rw [← hconv]; exact hgoal
    -- IH1 in S form (same center)
    have hIH1_S : |(Pkn (k + 1) N).eval x| ≤ Ak1 * S ^ (k + 1) := by
      calc |(Pkn (k + 1) N).eval x|
          ≤ Ak1 * (m : ℝ) ^ ((↑(k + 1) : ℝ) / 2) *
              (1 + |x - (m : ℝ)| / Real.sqrt (m : ℝ)) ^ (k + 1) := hIH1
        _ = Ak1 * S ^ (k + 1) := by rw [mul_assoc, hSform]
    -- IH0 in S form (center m+1 → bound by 4^k * S^k)
    have hIH0_S : |(Pkn k N).eval x| ≤ Ak * (4 ^ k * S ^ k) := by
      -- Convert IH0 to (√(m+1) + |x-(m+1)|)^k form
      have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
      have hm1_nn : (0 : ℝ) ≤ (m : ℝ) + 1 := le_of_lt hm1_pos
      have hsqrt_m1_ne : Real.sqrt ((m : ℝ) + 1) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos_of_pos hm1_pos)
      have hS1_eq : ((m : ℝ) + 1) ^ ((k : ℝ) / 2) *
          (1 + |x - ((m : ℝ) + 1)| / Real.sqrt ((m : ℝ) + 1)) ^ k =
          (Real.sqrt ((m : ℝ) + 1) + |x - ((m : ℝ) + 1)|) ^ k := by
        have h1 : ((m : ℝ) + 1) ^ ((k : ℝ) / 2) = (Real.sqrt ((m : ℝ) + 1)) ^ k := by
          rw [Real.sqrt_eq_rpow,
              ← Real.rpow_natCast (((m : ℝ) + 1) ^ ((1 : ℝ) / 2)) k,
              ← Real.rpow_mul hm1_nn]
          congr 1
          ring
        rw [h1, ← mul_pow, mul_add, mul_one, mul_div_cancel₀ _ hsqrt_m1_ne]
      -- Bound √(m+1) + |x-(m+1)| ≤ S + 2
      have hshift : Real.sqrt ((m : ℝ) + 1) + |x - ((m : ℝ) + 1)| ≤ S + 2 := by
        have h1 : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (m : ℝ) + 1 := by
          nlinarith [Real.sq_sqrt hm_nn, Real.sq_sqrt hm1_nn,
                     Real.sqrt_nonneg (m : ℝ)]
        have h2 : |x - ((m : ℝ) + 1)| ≤ |x - (m : ℝ)| + 1 := by
          calc |x - ((m : ℝ) + 1)| = |(x - (m : ℝ)) + (-1)| := by ring_nf
            _ ≤ |x - (m : ℝ)| + |(-1 : ℝ)| := abs_add_le _ _
            _ = |x - (m : ℝ)| + 1 := by simp [abs_neg]
        linarith
      -- S + 2 ≤ 3 * S since S ≥ 1
      have hS_shift : S + 2 ≤ 3 * S := by nlinarith
      have hS1_nn : 0 ≤ Real.sqrt ((m : ℝ) + 1) + |x - ((m : ℝ) + 1)| := by
        positivity
      calc |(Pkn k N).eval x|
          ≤ Ak * ((m : ℝ) + 1) ^ ((k : ℝ) / 2) *
              (1 + |x - ((m : ℝ) + 1)| / Real.sqrt ((m : ℝ) + 1)) ^ k := hIH0
        _ = Ak * (Real.sqrt ((m : ℝ) + 1) + |x - ((m : ℝ) + 1)|) ^ k := by
            rw [mul_assoc, hS1_eq]
        _ ≤ Ak * (S + 2) ^ k := by gcongr
        _ ≤ Ak * (3 * S) ^ k := by gcongr
        _ = Ak * (3 ^ k * S ^ k) := by rw [mul_pow]
        _ ≤ Ak * (4 ^ k * S ^ k) := by
            gcongr; norm_num
    -- Bound |x - (N+1)| ≤ (k+2)*S
    have hxN : |x - ↑(N + 1)| ≤ ((k + 2 : ℕ) : ℝ) * S := by
      have hN1 : (↑(N + 1) : ℝ) = (m : ℝ) + (k : ℝ) + 1 := by push_cast; linarith
      rw [hN1]
      have hk1_nn : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
      calc |x - ((m : ℝ) + (k : ℝ) + 1)|
          ≤ |x - (m : ℝ)| + ((k : ℝ) + 1) := by
            calc |x - ((m : ℝ) + (k : ℝ) + 1)|
                = |(x - (m : ℝ)) - ((k : ℝ) + 1)| := by ring_nf
              _ ≤ |x - (m : ℝ)| + |(k : ℝ) + 1| := abs_sub _ _
              _ = _ := by rw [abs_of_nonneg hk1_nn]
        _ ≤ S + ((k : ℝ) + 1) := by linarith [Real.sqrt_nonneg (m : ℝ)]
        _ ≤ ((k + 2 : ℕ) : ℝ) * S := by push_cast; nlinarith
    -- Bound |x| ≤ 2*S^2
    have hx_bound : |x| ≤ 2 * S ^ 2 := by
      have h1 : |x| ≤ |x - (m : ℝ)| + (m : ℝ) := by
        calc |x| = |(x - (m : ℝ)) + (m : ℝ)| := by ring_nf
          _ ≤ |x - (m : ℝ)| + |(m : ℝ)| := abs_add_le _ _
          _ = |x - (m : ℝ)| + (m : ℝ) := by rw [abs_of_nonneg hm_nn]
      have h2 : |x - (m : ℝ)| ≤ S := le_add_of_nonneg_left (Real.sqrt_nonneg _)
      have h3 : (m : ℝ) ≤ S ^ 2 := by
        have hsqrt_le_S : Real.sqrt (m : ℝ) ≤ S := le_add_of_nonneg_right (abs_nonneg _)
        have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm_nn
        calc (m : ℝ) = Real.sqrt (m : ℝ) ^ 2 := hsq.symm
          _ ≤ S ^ 2 := by
              apply sq_le_sq'
              · linarith
              · exact hsqrt_le_S
      -- |x| ≤ S + S^2 and S ≤ S^2 (since S ≥ 1), so |x| ≤ 2*S^2
      have h4 : S ≤ S ^ 2 := by
        rw [sq]; exact le_mul_of_one_le_right (le_of_lt hS_pos) hS_ge_one
      linarith
    have hkx : ((k + 1 : ℕ) : ℝ) * |x| ≤ ((k + 1 : ℕ) : ℝ) * (2 * S ^ 2) := by
      apply mul_le_mul_of_nonneg_left hx_bound
      exact_mod_cast (show 0 ≤ k + 1 by omega)
    -- Final combination
    calc |(Pkn (k + 2) (N + 1)).eval x|
        ≤ |x - ↑(N + 1)| * |(Pkn (k + 1) N).eval x| +
            ↑(k + 1) * |x| * |(Pkn k N).eval x| := htri
      _ ≤ ((k + 2 : ℕ) : ℝ) * S * (Ak1 * S ^ (k + 1)) +
            ((k + 1 : ℕ) : ℝ) * (2 * S ^ 2) * (Ak * (4 ^ k * S ^ k)) := by
          gcongr
      _ = (((k + 2 : ℕ) : ℝ) * Ak1 +
            2 * ((k + 1 : ℕ) : ℝ) * Ak * 4 ^ k) * S ^ (k + 2) := by ring
      _ ≤ (((k : ℝ) + 3) * Ak1 +
            ((k : ℝ) + 1) * 4 ^ (k + 1) * Ak) * S ^ (k + 2) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (le_of_lt hS_pos) _)
          push_cast
          have h4 : (4 : ℝ) ^ (k + 1) = 4 * (4 : ℝ) ^ k := by ring
          rw [h4]
          have : 0 ≤ ((k : ℝ) + 1) * Ak * (4 : ℝ) ^ k := by positivity
          linarith

/-- Rising factorial: m^k ≤ m(m+1)...(m+k-1) when m ≥ 1. Equivalently, for k ≤ n,
  (n-k+1)^k ≤ n! / (n-k)!. -/
private lemma pow_le_descFactorial (n k : ℕ) (hkn : k ≤ n) :
    (n - k + 1) ^ k ≤ n.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ]
    have hk1n : k ≤ n := by omega
    have hk1n1 : k ≤ n - 1 := by omega
    have hm : n - k ≤ n - k := le_refl _
    -- n.descFactorial (k+1) = (n-k) * n.descFactorial k
    -- (n-(k+1)+1)^(k+1) = (n-k)^(k+1) = (n-k) * (n-k)^k
    -- Since n-k ≥ n-(k+1)+1 = n-k, this is (n-k) * (n-k)^k.
    -- And (n-k)^k ≤ n.descFactorial k by IH (with appropriate shift).
    -- Actually, n - (k+1) + 1 = n - k. So (n-k)^(k+1) = (n-k) * (n-k)^k.
    -- We need (n-k)^k ≤ n.descFactorial k.
    -- IH says (n - k + 1)^k ≤ n.descFactorial k. But we need (n-k)^k.
    -- Since n-k ≤ n-k+1, we have (n-k)^k ≤ (n-k+1)^k ≤ n.descFactorial k.
    have h1 : n - (k + 1) + 1 = n - k := by omega
    rw [pow_succ, h1, mul_comm]
    apply Nat.mul_le_mul_left
    calc (n - k) ^ k ≤ (n - k + 1) ^ k := Nat.pow_le_pow_left (by omega) k
      _ ≤ n.descFactorial k := ih hk1n

/-- Key coefficient bound: m^k / (k! * n!) * k! = m^k / n! ≤ 1/α! where α = n-k, m = n-k+1. -/
private lemma mk_div_nfact_le (k n : ℕ) (hkn : k ≤ n) :
    ((n - k + 1 : ℕ) : ℝ) ^ k / ((Nat.factorial n : ℝ)) ≤ 1 / (Nat.factorial (n - k) : ℝ) := by
  have hfact_n_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
  have hfact_nk_pos : (0 : ℝ) < (Nat.factorial (n - k) : ℝ) := by positivity
  rw [div_le_div_iff₀ hfact_n_pos hfact_nk_pos, one_mul]
  -- Need: (n-k+1)^k * (n-k)! ≤ n!
  -- n! = n.descFactorial k * (n-k)!
  have hfact_split : (Nat.factorial n : ℝ) =
      (Nat.factorial (n - k) : ℝ) * (n.descFactorial k : ℝ) := by
    have := Nat.factorial_mul_descFactorial hkn
    exact_mod_cast this.symm
  rw [hfact_split]
  have hfact_nk_nn : (0 : ℝ) ≤ (Nat.factorial (n - k) : ℝ) := by positivity
  calc ((n - k + 1 : ℕ) : ℝ) ^ k * (Nat.factorial (n - k) : ℝ)
      = (Nat.factorial (n - k) : ℝ) * ((n - k + 1 : ℕ) : ℝ) ^ k := by ring
    _ ≤ (Nat.factorial (n - k) : ℝ) * (n.descFactorial k : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hfact_nk_nn
        exact_mod_cast pow_le_descFactorial n k hkn

/-- Variable substitution bound: with t = r - √m, u = (r²-m)/√m,
  we have 1 + |u| ≤ (1 + |t|)² when m ≥ 1. -/
private lemma one_plus_abs_u_le_sq (m : ℕ) (hm : 1 ≤ m) (r : ℝ) (hr : 0 ≤ r) :
    1 + |r ^ 2 - (m : ℝ)| / Real.sqrt (m : ℝ) ≤ (1 + |r - Real.sqrt (m : ℝ)|) ^ 2 := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos hm_pos
  have hsqrt_nn : 0 ≤ Real.sqrt (m : ℝ) := le_of_lt hsqrt_pos
  -- r² - m = (r - √m)(r + √m), so |r²-m|/√m = |r-√m| * (r+√m)/√m
  have hfactor : r ^ 2 - (m : ℝ) = (r - Real.sqrt (m : ℝ)) * (r + Real.sqrt (m : ℝ)) := by
    have hsq := Real.sq_sqrt (le_of_lt hm_pos)
    nlinarith
  set t := r - Real.sqrt (m : ℝ)
  set s := r + Real.sqrt (m : ℝ)
  have hs_nn : 0 ≤ s := by positivity
  rw [hfactor, abs_mul, div_eq_mul_inv]
  -- |t| * |s| / √m = |t| * |s|/√m. Since s = r + √m ≥ √m, |s| = s.
  rw [abs_of_nonneg hs_nn]
  -- s/√m = (r + √m)/√m = r/√m + 1 ≤ |t| + 2 since r = t + √m, so r/√m = t/√m + 1
  -- Hence |t| * s / √m ≤ |t| * (|t| + 2) = |t|² + 2|t|
  -- And 1 + |t|² + 2|t| = (1+|t|)²
  have hs_bound : s / Real.sqrt (m : ℝ) ≤ |t| + 2 := by
    rw [div_le_iff₀ hsqrt_pos]
    -- s = r + √m = t + √m + √m = t + 2√m
    have hs_eq : s = t + 2 * Real.sqrt (m : ℝ) := by simp only [s, t]; ring
    rw [hs_eq]
    -- Need: t + 2√m ≤ (|t| + 2) * √m
    have h1 : 1 ≤ Real.sqrt (m : ℝ) := by
      rw [Real.one_le_sqrt]; exact_mod_cast hm
    -- Need: t + 2√m ≤ (|t| + 2) * √m = |t|*√m + 2*√m.
    -- Suffices: t ≤ |t| * √m. Since t ≤ |t| and 1 ≤ √m.
    have ht_le := le_abs_self t
    have hat_nn := abs_nonneg t
    -- t ≤ |t| ≤ |t| * √m since √m ≥ 1
    have : |t| ≤ |t| * Real.sqrt (m : ℝ) := le_mul_of_one_le_right hat_nn h1
    nlinarith
  have habs_t := abs_nonneg t
  calc 1 + |t| * s * (Real.sqrt (m : ℝ))⁻¹
      = 1 + |t| * (s / Real.sqrt (m : ℝ)) := by
        congr 1; rw [mul_assoc, div_eq_mul_inv]
    _ ≤ 1 + |t| * (|t| + 2) := by
        linarith [mul_le_mul_of_nonneg_left hs_bound habs_t]
    _ = (1 + |t|) ^ 2 := by ring

/-- Gaussian shift: exp(-(r - rStar(α))²) ≤ exp(2) * exp(-(r-√m)²/2) where m = α+1. -/
private lemma rStar_to_sqrt_gaussian (α : ℕ) (hα : 1 ≤ α) (r : ℝ) :
    Real.exp (-(r - FockSPR.rStar α) ^ 2) ≤
      Real.exp 2 * Real.exp (-(r - Real.sqrt ((α : ℝ) + 1)) ^ 2 / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- Need: -(r-rStar(α))² ≤ 2 + (-(r-√(α+1))²/2)
  -- i.e., (r-√(α+1))²/2 ≤ (r-rStar(α))² + 2
  -- rStar(α) = √(α + 1/2), so r - rStar(α) = t + (√(α+1) - √(α+1/2)) where t = r - √(α+1).
  -- Let δ = √(α+1) - √(α+1/2) ≥ 0 (and δ ≤ 1).
  -- (r - rStar(α))² = (t + δ)² = t² + 2tδ + δ²
  -- Need: t²/2 ≤ t² + 2tδ + δ² + 2
  -- i.e., 0 ≤ t²/2 + 2tδ + δ² + 2
  -- i.e., 0 ≤ t²/2 + 2tδ + δ² + 2
  -- Since 2tδ ≥ -t² - δ² (AM-GM: t² + δ² ≥ -2tδ),
  -- t²/2 + 2tδ + δ² + 2 ≥ t²/2 - t² - δ² + δ² + 2 = -t²/2 + 2 ... not great.
  -- Better: 2tδ ≥ -2|t|δ ≥ -2|t|. Then t²/2 + 2tδ + δ² + 2 ≥ t²/2 - 2|t| + 2
  -- = (|t|/√2 - √2)² + 2 - 2 = (|t|/√2 - √2)² ≥ 0... not quite.
  -- t²/2 - 2|t| + 2: disc = 4 - 4 = 0 if we view as (|t| - 2)²/2 ≥ 0?
  -- (|t| - 2)² = |t|² - 4|t| + 4, so t²/2 - 2|t| + 2 = (t² - 4|t| + 4)/2 = (|t|-2)²/2 ≥ 0.
  -- Yes!
  unfold FockSPR.rStar
  set s := Real.sqrt ((α : ℝ) + 1 / 2)
  set m := Real.sqrt ((α : ℝ) + 1)
  set t := r - m
  -- Need: -(r - s)² ≤ 2 - t²/2
  -- (r - s)² = (t + (m - s))² ≥ ... We need -(r-s)² ≤ 2 - t²/2, i.e. t²/2 - 2 ≤ (r-s)².
  -- (r - s) = t + (m - s). Let δ = m - s ≥ 0.
  -- (r-s)² = (t+δ)² = t² + 2tδ + δ² ≥ t² - 2|t|δ ≥ t² - 2|t| (since δ ≤ 1)
  -- And t² - 2|t| ≥ t²/2 - 2 by (|t|-2)²/2 ≥ 0.
  -- So (r-s)² ≥ t²/2 - 2, hence -(r-s)² ≤ -(t²/2 - 2) = 2 - t²/2.
  have hδ_nn : 0 ≤ m - s := by
    simp only [s, m]
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    linarith
  have hδ_le_one : m - s ≤ 1 := by
    simp only [s, m]
    have h1 : (0 : ℝ) ≤ (α : ℝ) + 1 / 2 := by positivity
    have h2 : (0 : ℝ) ≤ (α : ℝ) + 1 := by positivity
    -- √(α+1) - √(α+1/2) ≤ 1
    -- (√(α+1) - √(α+1/2)) * (√(α+1) + √(α+1/2)) = (α+1) - (α+1/2) = 1/2
    -- And √(α+1) + √(α+1/2) ≥ √(3/2) ≥ 1/2, so the difference ≤ 1.
    nlinarith [Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sqrt_nonneg ((α : ℝ) + 1),
               Real.sqrt_nonneg ((α : ℝ) + 1 / 2)]
  -- (r-s)² ≥ t²/2 - 2
  have hkey : t ^ 2 / 2 - 2 ≤ (r - s) ^ 2 := by
    have hrs : r - s = t + (m - s) := by simp only [t]; ring
    rw [hrs]
    set δ := m - s
    have h1 : (t + δ) ^ 2 = t ^ 2 + 2 * t * δ + δ ^ 2 := by ring
    rw [h1]
    have h2 : -2 * |t| ≤ 2 * t * δ := by
      have := le_abs_self t
      have := neg_abs_le t
      nlinarith
    have h3 : t ^ 2 / 2 - 2 * |t| + 2 ≥ 0 := by nlinarith [sq_nonneg (|t| - 2), sq_abs t]
    nlinarith [sq_nonneg δ]
  linarith

/-- Polynomial absorption: (1+|t|)^p * exp(-t²/2) ≤ C_p * exp(-t²/4). -/
private theorem poly_times_gaussian_absorption (p : ℕ) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ t : ℝ,
      (1 + |t|) ^ p * Real.exp (-t ^ 2 / 2) ≤ Cp * Real.exp (-t ^ 2 / 4) := by
  -- The factor (1+|t|)^p is absorbed by exp(-t²/4) since
  -- (1+|t|)^p ≤ exp(p*|t|) and p*|t| ≤ t²/4 + p² for all t.
  -- Hence (1+|t|)^p * exp(-t²/2) ≤ exp(p²) * exp(-t²/4).
  use Real.exp (p ^ 2 : ℝ)
  constructor
  · positivity
  intro t
  have h1 : (1 + |t|) ^ p ≤ Real.exp ((p : ℝ) * |t|) := by
    calc (1 + |t|) ^ p
        ≤ (Real.exp |t|) ^ p := by
          gcongr
          linarith [Real.add_one_le_exp |t|]
      _ = Real.exp ((p : ℝ) * |t|) := by
          rw [Real.exp_nat_mul]
  have h2 : (p : ℝ) * |t| - t ^ 2 / 4 ≤ (p : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((p : ℝ) - |t| / 2), sq_abs t, abs_nonneg t]
  calc (1 + |t|) ^ p * Real.exp (-t ^ 2 / 2)
      ≤ Real.exp ((p : ℝ) * |t|) * Real.exp (-t ^ 2 / 2) := by
        gcongr
      _ = Real.exp ((p : ℝ) * |t| + (-t ^ 2 / 2)) := by
        rw [← Real.exp_add]
      _ ≤ Real.exp ((p : ℝ) ^ 2 + (-t ^ 2 / 4)) := by
        apply Real.exp_le_exp.mpr; nlinarith
      _ = Real.exp ((p : ℝ) ^ 2) * Real.exp (-t ^ 2 / 4) := by
        rw [Real.exp_add]

/-- Squares the scaled-Laguerre pointwise bound on `Pkn k n` (for `k < n`).
Extracted from `radial_density_large_step` to respect the proof size limit. -/
private lemma Pkn_sq_bound (k n : ℕ) (hkn_strict : k < n) (r : ℝ) {Ak : ℝ}
    (hPkn : |(Pkn k n).eval (r ^ 2)| ≤
      Ak * ((n : ℝ) - (k : ℝ) + 1) ^ ((k : ℝ) / 2) *
        (1 + |r ^ 2 - ((n : ℝ) - (k : ℝ) + 1)| /
          Real.sqrt ((n : ℝ) - (k : ℝ) + 1)) ^ k) :
    ((Pkn k n).eval (r ^ 2)) ^ 2 ≤
      Ak ^ 2 * ((n : ℝ) - (k : ℝ) + 1) ^ k *
        (1 + |r ^ 2 - ((n : ℝ) - (k : ℝ) + 1)| /
          Real.sqrt ((n : ℝ) - (k : ℝ) + 1)) ^ (2 * k) := by
  have h_rpow_sq : (((n : ℝ) - (k : ℝ) + 1) ^ ((k : ℝ) / 2)) ^ 2 =
      ((n : ℝ) - (k : ℝ) + 1) ^ k := by
    set m := (n : ℝ) - (k : ℝ) + 1
    have hm_rpow_nat : m ^ (k : ℝ) = m ^ k := Real.rpow_natCast m k
    have hm_pos' : (0 : ℝ) < m := by
      have hkn_cast : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn_strict
      simp only [m]; linarith
    rw [sq, ← Real.rpow_add hm_pos', ← hm_rpow_nat]
    congr 1
    show (k : ℝ) / 2 + (k : ℝ) / 2 = (k : ℝ)
    ring
  have hP_abs_bound :=
    sq_le_sq' (by linarith [abs_nonneg ((Pkn k n).eval (r ^ 2))]) hPkn
  calc ((Pkn k n).eval (r ^ 2)) ^ 2
      = (|(Pkn k n).eval (r ^ 2)|) ^ 2 := (sq_abs _).symm
    _ ≤ (Ak * ((n : ℝ) - (k : ℝ) + 1) ^ ((k : ℝ) / 2) *
          (1 + |r ^ 2 - ((n : ℝ) - (k : ℝ) + 1)| /
            Real.sqrt ((n : ℝ) - (k : ℝ) + 1)) ^ k) ^ 2 := hP_abs_bound
    _ = Ak ^ 2 * ((n : ℝ) - (k : ℝ) + 1) ^ k *
          (1 + |r ^ 2 - ((n : ℝ) - (k : ℝ) + 1)| /
            Real.sqrt ((n : ℝ) - (k : ℝ) + 1)) ^ (2 * k) := by
        rw [mul_pow, mul_pow, ← pow_mul, h_rpow_sq]; ring

/-- The strictly-positive-shift (`n > k`) case of the large-index radial Gaussian
density bound.  Extracted from `radial_density_gaussian_bound_large` to respect
the proof size limit. -/
private lemma radial_density_large_step (k n : ℕ) (hkn_strict : k < n) (r : ℝ)
    (hr : 0 ≤ r) (hr_pos : 0 < r)
    {Ak : ℝ} (hAk_pos : 0 < Ak)
    (hAk_bound : ∀ (n : ℕ), k ≤ n → ∀ (x : ℝ),
      |(Pkn k n).eval x| ≤
        Ak * ((n - k + 1 : ℝ) ^ ((k : ℝ) / 2)) *
          (1 + |x - (n - k + 1 : ℝ)| / Real.sqrt (n - k + 1 : ℝ)) ^ k)
    {Cp : ℝ} (hCp_pos : 0 < Cp)
    (hCp_bound : ∀ t : ℝ,
      (1 + |t|) ^ (4 * k + 1) * Real.exp (-t ^ 2 / 2) ≤ Cp * Real.exp (-t ^ 2 / 4))
    {C0 : ℝ} (hC0_def : C0 = Real.exp (1 / 4) / 2) :
    r * (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
        Real.exp (-r ^ 2)
      ≤ (Ak ^ 2 * C0 * Real.exp 2 * Cp + Ak ^ 2 * Real.exp 1 * Cp + Cp * Real.exp 1) *
          Real.exp (-(r - Real.sqrt (n - k + 1 : ℝ)) ^ 2 / 4) := by
  have hα_pos : 1 ≤ n - k := by omega
  set α := n - k with hα_def
  have hm_pos : 1 ≤ (α + 1 : ℕ) := by omega
  have hm_R_eq : ((α + 1 : ℕ) : ℝ) = ((n : ℝ) - (k : ℝ) + 1) := by
    simp only [hα_def]; push_cast [Nat.cast_sub (le_of_lt hkn_strict)]
    ring
  -- Step 1: Rewrite qkn using Pkn
  have hqkn := qkn_mul_rpow_eq_Pkn_eval k n hr_pos (le_of_lt hkn_strict)
  -- Step 2: scaled_laguerre_bound_Pkn
  have hPkn := hAk_bound n (le_of_lt hkn_strict) (r ^ 2)
  -- Step 3: variable substitution bound
  have hu_bound := one_plus_abs_u_le_sq (α + 1) hm_pos r hr
  -- Step 4: monomial_core_pointwise
  have hmon := monomial_core_pointwise α hα_pos hr_pos
  -- Step 5: rStar shift
  have hshift := rStar_to_sqrt_gaussian α hα_pos r
  -- Step 6: poly_times_gaussian_absorption (already obtained)
  -- Key: express LHS in terms of r^(2α+1), |Pkn.eval(r²)|², exp(-r²)
  have hkfact_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
  have hnfact_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
  have hαfact_pos : (0 : ℝ) < (Nat.factorial α : ℝ) := by positivity
  have hsqrt_kfact_pos : (0 : ℝ) < Real.sqrt (Nat.factorial k : ℝ) := by positivity
  have hsqrt_nfact_pos : (0 : ℝ) < Real.sqrt (Nat.factorial n : ℝ) := by positivity
  have hm_cast : ((α + 1 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) + 1 := hm_R_eq
  -- Rewrite (r^k * qkn)² using hqkn
  have hrkqkn_sq :
      (r ^ k) ^ 2 * |qkn k n r| ^ 2 =
        (1 / (Nat.factorial n : ℝ)) * r ^ (2 * α) *
          ((Pkn k n).eval (r ^ 2)) ^ 2 := by
    -- |qkn|² = qkn² (since |x|² = x²)
    rw [sq_abs]
    -- (r^k)² * qkn² = (r^k * qkn)²
    rw [← mul_pow, hqkn, show n - k = α from rfl]
    -- (1/√n! * r^α * Pkn.eval(r²))² = 1/n! * r^(2α) * Pkn.eval(r²)²
    rw [mul_pow, mul_pow, one_div, inv_pow, Real.sq_sqrt (le_of_lt hnfact_pos),
        ← pow_mul]
    ring
  -- LHS = r * (r^k/√k!)² * |qkn|² * exp(-r²)
  --     = r * ((r^k)² * |qkn|² / k!) * exp(-r²)
  --     = (1/(k!*n!)) * r^(2α) * |Pkn.eval(r²)|² * r * exp(-r²)
  --     = (1/(k!*n!)) * |Pkn.eval(r²)|² * r^(2α+1) * exp(-r²)
  have hLHS_eq :
      r * (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
        Real.exp (-r ^ 2) =
      (1 / ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) *
        ((Pkn k n).eval (r ^ 2)) ^ 2 *
        (r ^ (2 * α + 1) * Real.exp (-r ^ 2)) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hkfact_pos)]
    -- Goal: r * ((r^k)² / k! * |qkn|²) * exp(-r²) = (1/(k!*n!)) * Pkn² * (r^(2α+1) * exp(-r²))
    have h1 : (r ^ k) ^ 2 / (Nat.factorial k : ℝ) * |qkn k n r| ^ 2 =
        (1 / (Nat.factorial k : ℝ)) * ((r ^ k) ^ 2 * |qkn k n r| ^ 2) := by
      field_simp
    rw [h1, hrkqkn_sq, show r ^ (2 * α + 1) = r ^ (2 * α) * r from pow_succ r (2 * α)]
    ring
  rw [hLHS_eq]
  -- Now bound |Pkn.eval(r²)|² ≤ Ak² * m^k * (1+|u|)^(2k)
  have hPkn_sq :
      ((Pkn k n).eval (r ^ 2)) ^ 2 ≤
        Ak ^ 2 * ((n : ℝ) - (k : ℝ) + 1) ^ k *
          (1 + |r ^ 2 - ((n : ℝ) - (k : ℝ) + 1)| /
            Real.sqrt ((n : ℝ) - (k : ℝ) + 1)) ^ (2 * k) :=
    Pkn_sq_bound k n hkn_strict r hPkn
  -- Now use mk_div_nfact_le: m^k / n! ≤ 1/α!
  have hm_R : ((n : ℝ) - (k : ℝ) + 1) = ((α + 1 : ℕ) : ℝ) := hm_R_eq.symm
  -- Bound (1+|u|)^(2k) using hu_bound
  have hu_sq_bound :
      (1 + |r ^ 2 - ((n : ℝ) - (k : ℝ) + 1)| /
        Real.sqrt ((n : ℝ) - (k : ℝ) + 1)) ^ (2 * k) ≤
      (1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k) := by
    rw [hm_R]
    calc (1 + |r ^ 2 - ↑(α + 1)| / √↑(α + 1)) ^ (2 * k)
        ≤ ((1 + |r - √↑(α + 1)|) ^ 2) ^ (2 * k) :=
          pow_le_pow_left₀ (by positivity) hu_bound (2 * k)
      _ = (1 + |r - √↑(α + 1)|) ^ (4 * k) := by
          rw [← pow_mul]; ring_nf
  -- Combine: |Pkn|² * m^k/n! ≤ Ak² * (1+|t|)^(4k) / α!
  -- monomial bound:
  -- r^(2α+1) * exp(-r²) / α! ≤ C0 * exp(-(r-rStar(α))²)
  -- rStar shift:
  -- exp(-(r-rStar(α))²) ≤ exp(2) * exp(-(r-√(α+1))²/2)
  -- poly_times_gaussian_absorption:
  -- (1+|t|)^(4k+1) * exp(-t²/2) ≤ Cp * exp(-t²/4)
  -- where t = r - √(α+1) = r - √m = r - √(n-k+1)
  -- Now assemble the full bound.
  -- We use that the RHS has the form (Ak²*C0*exp(2)*Cp + ...) * exp(-(r-√(n-k+1))²/4)
  -- and we only need the first term in the constant.
  have hle_first_term :
      (Ak ^ 2 * C0 * Real.exp 2 * Cp) *
        Real.exp (-(r - Real.sqrt ((n : ℝ) - (k : ℝ) + 1)) ^ 2 / 4) ≤
      (Ak ^ 2 * C0 * Real.exp 2 * Cp + Ak ^ 2 * Real.exp 1 * Cp + Cp * Real.exp 1) *
        Real.exp (-(r - Real.sqrt ((n : ℝ) - (k : ℝ) + 1)) ^ 2 / 4) := by
    have hcoeff_le :
        Ak ^ 2 * C0 * Real.exp 2 * Cp ≤
          Ak ^ 2 * C0 * Real.exp 2 * Cp + Ak ^ 2 * Real.exp 1 * Cp + Cp * Real.exp 1 := by
      have hnonneg : 0 ≤ Ak ^ 2 * Real.exp 1 * Cp + Cp * Real.exp 1 := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right hcoeff_le (by positivity)
  apply le_trans _ hle_first_term
  -- Now we need:
  -- (1/(k!*n!)) * |Pkn.eval(r²)|² * r^(2α+1) * exp(-r²) ≤ Ak²*C0*exp(2)*Cp * exp(-t²/4)
  -- Step: bound |Pkn|² ≤ Ak² * m^k * (1+|t|)^(4k)
  -- So LHS ≤ Ak²/(k!*n!) * m^k * (1+|t|)^(4k) * r^(2α+1) * exp(-r²)
  -- By mk_div_nfact_le: m^k/n! ≤ 1/α!
  -- So LHS ≤ Ak²/k! * (1+|t|)^(4k) * r^(2α+1) * exp(-r²) / α!
  -- Since 1/k! ≤ 1:
  -- LHS ≤ Ak² * (1+|t|)^(4k) * r^(2α+1) * exp(-r²) / α!
  -- By hmon: r^(2α+1)*exp(-r²)/α! ≤ C0 * exp(-(r-rStar(α))²)
  -- By hshift: exp(-(r-rStar(α))²) ≤ exp(2) * exp(-t²/2)
  -- So r^(2α+1)*exp(-r²)/α! ≤ C0 * exp(2) * exp(-t²/2)
  -- Combined: LHS ≤ Ak² * C0 * exp(2) * (1+|t|)^(4k) * exp(-t²/2)
  -- Since (1+|t|) ≥ 1: (1+|t|)^(4k) ≤ (1+|t|)^(4k+1)
  -- By hCp_bound: (1+|t|)^(4k+1) * exp(-t²/2) ≤ Cp * exp(-t²/4)
  -- Final: LHS ≤ Ak² * C0 * exp(2) * Cp * exp(-t²/4)
  have hα_eq : n - k = α := by simp [hα_def]
  have hmk :
      ((n - k + 1 : ℕ) : ℝ) ^ k / (Nat.factorial n : ℝ) ≤ 1 / (Nat.factorial α : ℝ) := by
    simpa [hα_eq] using mk_div_nfact_le k n (le_of_lt hkn_strict)
  have hk_nat : 1 ≤ Nat.factorial k := Nat.succ_le_of_lt (Nat.factorial_pos k)
  have hk_inv_le_one : (1 / (Nat.factorial k : ℝ)) ≤ (1 : ℝ) := by
    have hk_one : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast hk_nat
    have htmp : (1 : ℝ) / (Nat.factorial k : ℝ) ≤ (1 : ℝ) / 1 :=
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1) hk_one
    simpa using htmp
  have hpow_step :
      (1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k) ≤
        (1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k + 1) := by
    have hbase_ge_one : (1 : ℝ) ≤ 1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)| := by
      linarith [abs_nonneg (r - Real.sqrt ((α + 1 : ℕ) : ℝ))]
    exact pow_le_pow_right₀ hbase_ge_one (by omega)
  have hCp_at :
      (1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k + 1) *
          Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 2) ≤
        Cp * Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 4) := by
    simpa using hCp_bound (r - Real.sqrt ((α + 1 : ℕ) : ℝ))
  have hpoly_absorb :
      (1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k) *
          Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 2) ≤
        Cp * Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 4) := by
    have htmp :
        (1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k) *
            Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 2) ≤
          (1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k + 1) *
            Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_right hpow_step (by positivity)
    exact le_trans htmp hCp_at
  have hC0_nonneg : 0 ≤ C0 := by
    rw [hC0_def]
    positivity
  have hshift' :
      Real.exp (-(r - FockSPR.rStar α) ^ 2) ≤
        Real.exp 2 * Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 2) := by
    simpa [Nat.cast_add, Nat.cast_one] using hshift
  have hmon_shift :
      r ^ (2 * α + 1) * Real.exp (-r ^ 2) / (Nat.factorial α : ℝ) ≤
        C0 * (Real.exp 2 * Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 2)) := by
    calc
      r ^ (2 * α + 1) * Real.exp (-r ^ 2) / (Nat.factorial α : ℝ)
          ≤ C0 * Real.exp (-(r - FockSPR.rStar α) ^ 2) := by
            simpa [hC0_def] using hmon
      _ ≤ C0 * (Real.exp 2 * Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 2)) := by
            exact mul_le_mul_of_nonneg_left hshift' hC0_nonneg
  have hcoef_main :
      (1 / ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) * (((n - k + 1 : ℕ) : ℝ) ^ k) ≤
        1 / (Nat.factorial α : ℝ) := by
    have hmk_nonneg : 0 ≤ (((n - k + 1 : ℕ) : ℝ) ^ k) / (Nat.factorial n : ℝ) := by positivity
    calc
      (1 / ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) * (((n - k + 1 : ℕ) : ℝ) ^ k)
          = (1 / (Nat.factorial k : ℝ)) * ((((n - k + 1 : ℕ) : ℝ) ^ k) / (Nat.factorial n : ℝ))
          := by
              field_simp [show (Nat.factorial k : ℝ) ≠ 0 by positivity,
                show (Nat.factorial n : ℝ) ≠ 0 by positivity]
      _ ≤ 1 * (1 / (Nat.factorial α : ℝ)) := by
            exact mul_le_mul hk_inv_le_one hmk hmk_nonneg (by positivity)
      _ = 1 / (Nat.factorial α : ℝ) := by ring
  calc
    1 / (↑k.factorial * ↑n.factorial) * Polynomial.eval (r ^ 2) (Pkn k n) ^ 2 *
        (r ^ (2 * α + 1) * Real.exp (-r ^ 2))
        ≤
      1 / (↑k.factorial * ↑n.factorial) *
          (Ak ^ 2 * (↑n - ↑k + 1) ^ k *
            (1 + |r ^ 2 - (↑n - ↑k + 1)| / √(↑n - ↑k + 1)) ^ (2 * k)) *
          (r ^ (2 * α + 1) * Real.exp (-r ^ 2)) := by
        gcongr
    _ ≤
      1 / (↑k.factorial * ↑n.factorial) *
          (Ak ^ 2 * (↑n - ↑k + 1) ^ k * (1 + |r - √↑(α + 1)|) ^ (4 * k)) *
          (r ^ (2 * α + 1) * Real.exp (-r ^ 2)) := by
        have hm_nonneg : 0 ≤ (↑n - ↑k + 1 : ℝ) := by
          have hkn_cast : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn_strict
          linarith
        have hcoef_nonneg : 0 ≤ Ak ^ 2 * (↑n - ↑k + 1) ^ k := by
          positivity
        have hmid :
            Ak ^ 2 * (↑n - ↑k + 1) ^ k * (1 + |r ^ 2 - (↑n - ↑k + 1)| / √(↑n - ↑k + 1)) ^ (2 * k)
            ≤ Ak ^ 2 * (↑n - ↑k + 1) ^ k * (1 + |r - √↑(α + 1)|) ^ (4 * k) := by
          exact mul_le_mul_of_nonneg_left hu_sq_bound hcoef_nonneg
        have hmid' :
            (1 / (↑k.factorial * ↑n.factorial)) *
                (Ak ^ 2 * (↑n - ↑k + 1) ^ k *
                  (1 + |r ^ 2 - (↑n - ↑k + 1)| / √(↑n - ↑k + 1)) ^ (2 * k))
            ≤ (1 / (↑k.factorial * ↑n.factorial)) *
                (Ak ^ 2 * (↑n - ↑k + 1) ^ k * (1 + |r - √↑(α + 1)|) ^ (4 * k)) := by
          exact mul_le_mul_of_nonneg_left hmid (by positivity)
        exact mul_le_mul_of_nonneg_right hmid' (by positivity)
    _ =
      Ak ^ 2 *
        ((1 / ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) * (((n - k + 1 : ℕ) : ℝ) ^ k)) *
        ((1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k) *
          (r ^ (2 * α + 1) * Real.exp (-r ^ 2))) := by
        rw [hm_R]
        ring
    _ ≤
      Ak ^ 2 * (1 / (Nat.factorial α : ℝ)) *
        ((1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k) *
          (r ^ (2 * α + 1) * Real.exp (-r ^ 2))) := by
        gcongr
    _ =
      Ak ^ 2 * (1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k) *
        (r ^ (2 * α + 1) * Real.exp (-r ^ 2) / (Nat.factorial α : ℝ)) := by
        field_simp [show (Nat.factorial α : ℝ) ≠ 0 by positivity]
    _ ≤
      Ak ^ 2 * (1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k) *
        (C0 * (Real.exp 2 * Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 2))) := by
        gcongr
    _ =
      Ak ^ 2 * C0 * Real.exp 2 *
        ((1 + |r - Real.sqrt ((α + 1 : ℕ) : ℝ)|) ^ (4 * k) *
          Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 2)) := by
        ring
    _ ≤
      Ak ^ 2 * C0 * Real.exp 2 *
        (Cp * Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 4)) := by
        gcongr
    _ = Ak ^ 2 * C0 * Real.exp 2 * Cp *
        Real.exp (-(r - Real.sqrt ((α + 1 : ℕ) : ℝ)) ^ 2 / 4) := by ring
    _ = Ak ^ 2 * C0 * Real.exp 2 * Cp *
        Real.exp (-(r - Real.sqrt ((n : ℝ) - (k : ℝ) + 1)) ^ 2 / 4) := by
        rw [hm_R]

/-- The diagonal (`n = k`) case of the large-index radial Gaussian density bound.
Extracted from `radial_density_gaussian_bound_large` to respect the size limit. -/
private lemma radial_density_eq_step (k : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr_pos : 0 < r)
    {Ak : ℝ} (hAk_pos : 0 < Ak)
    (hAk_bound : ∀ (n : ℕ), k ≤ n → ∀ (x : ℝ),
      |(Pkn k n).eval x| ≤
        Ak * ((n - k + 1 : ℝ) ^ ((k : ℝ) / 2)) *
          (1 + |x - (n - k + 1 : ℝ)| / Real.sqrt (n - k + 1 : ℝ)) ^ k)
    {Cp : ℝ} (hCp_pos : 0 < Cp)
    (hCp_bound : ∀ t : ℝ,
      (1 + |t|) ^ (4 * k + 1) * Real.exp (-t ^ 2 / 2) ≤ Cp * Real.exp (-t ^ 2 / 4))
    {C0 : ℝ} (hC0_def : C0 = Real.exp (1 / 4) / 2) :
    r * (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k k r| ^ 2) *
        Real.exp (-r ^ 2)
      ≤ (Ak ^ 2 * C0 * Real.exp 2 * Cp + Ak ^ 2 * Real.exp 1 * Cp + Cp * Real.exp 1) *
          Real.exp (-(r - Real.sqrt (k - k + 1 : ℝ)) ^ 2 / 4) := by
  -- For n = k: √(n-k+1) = √1 = 1, so RHS = Ck * exp(-(r-1)²/4).
  have hkfact_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
  have hqkn :
      r ^ k * qkn k k r =
        (1 / Real.sqrt (Nat.factorial k : ℝ)) * (Pkn k k).eval (r ^ 2) := by
    simpa using qkn_mul_rpow_eq_Pkn_eval k k hr_pos le_rfl
  have hPkn :
      |(Pkn k k).eval (r ^ 2)| ≤ Ak * (1 + |r ^ 2 - 1|) ^ k := by
    simpa [show k - k + 1 = 1 by omega, Real.sqrt_one] using hAk_bound k le_rfl (r ^ 2)
  have hu_bound : 1 + |r ^ 2 - 1| ≤ (1 + |r - 1|) ^ 2 := by
    simpa [Real.sqrt_one] using one_plus_abs_u_le_sq 1 (by norm_num) r hr
  have hPkn_sq :
      ((Pkn k k).eval (r ^ 2)) ^ 2 ≤ Ak ^ 2 * (1 + |r - 1|) ^ (4 * k) := by
    have hu_pow : (1 + |r ^ 2 - 1|) ^ k ≤ (1 + |r - 1|) ^ (2 * k) := by
      calc
        (1 + |r ^ 2 - 1|) ^ k ≤ ((1 + |r - 1|) ^ 2) ^ k := by
          exact pow_le_pow_left₀ (by positivity) hu_bound k
        _ = (1 + |r - 1|) ^ (2 * k) := by rw [← pow_mul]
    calc
      ((Pkn k k).eval (r ^ 2)) ^ 2 = |(Pkn k k).eval (r ^ 2)| ^ 2 := (sq_abs _).symm
      _ ≤ (Ak * (1 + |r ^ 2 - 1|) ^ k) ^ 2 := by gcongr
      _ ≤ (Ak * (1 + |r - 1|) ^ (2 * k)) ^ 2 := by gcongr
      _ = Ak ^ 2 * (1 + |r - 1|) ^ (4 * k) := by
        rw [mul_pow, ← pow_mul]
        ring
  have hbase :
      r * Real.exp (-r ^ 2) ≤
        Real.exp 1 * (1 + |r - 1|) * Real.exp (-(r - 1) ^ 2 / 2) := by
    set t : ℝ := r - 1
    have hr_le : r ≤ 1 + |t| := by
      have ht_le : t ≤ |t| := le_abs_self t
      linarith
    have hexp :
        Real.exp (-r ^ 2) ≤ Real.exp 1 * Real.exp (-t ^ 2 / 2) := by
      have hr_eq : r = t + 1 := by simp [t]
      rw [hr_eq, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (t + 2)]
    calc
      r * Real.exp (-r ^ 2) ≤ (1 + |t|) * Real.exp (-r ^ 2) := by gcongr
      _ ≤ (1 + |t|) * (Real.exp 1 * Real.exp (-t ^ 2 / 2)) := by gcongr
      _ = Real.exp 1 * (1 + |t|) * Real.exp (-t ^ 2 / 2) := by ring
  have hrkqkn_sq :
      (r ^ k) ^ 2 * |qkn k k r| ^ 2 =
        (1 / (Nat.factorial k : ℝ)) * ((Pkn k k).eval (r ^ 2)) ^ 2 := by
    calc
      (r ^ k) ^ 2 * |qkn k k r| ^ 2 = (r ^ k * qkn k k r) ^ 2 := by
        rw [sq_abs, ← mul_pow]
      _ = ((1 / Real.sqrt (Nat.factorial k : ℝ)) * (Pkn k k).eval (r ^ 2)) ^ 2 := by
        rw [hqkn]
      _ = (1 / (Nat.factorial k : ℝ)) * ((Pkn k k).eval (r ^ 2)) ^ 2 := by
        rw [mul_pow, one_div, inv_pow, Real.sq_sqrt (le_of_lt hkfact_pos)]
        ring
  have hLHS_eq :
      r * (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k k r| ^ 2) *
        Real.exp (-r ^ 2) =
      (1 / ((Nat.factorial k : ℝ) ^ 2)) * ((Pkn k k).eval (r ^ 2)) ^ 2 *
        (r * Real.exp (-r ^ 2)) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hkfact_pos)]
    have h1 :
        (r ^ k) ^ 2 / (Nat.factorial k : ℝ) * |qkn k k r| ^ 2 =
          (1 / (Nat.factorial k : ℝ)) * ((r ^ k) ^ 2 * |qkn k k r| ^ 2) := by
      field_simp
    calc
      r * (((r ^ k) ^ 2 / (Nat.factorial k : ℝ)) * |qkn k k r| ^ 2) * Real.exp (-r ^ 2)
          = r * ((1 / (Nat.factorial k : ℝ)) * ((r ^ k) ^ 2 * |qkn k k r| ^ 2)) *
              Real.exp (-r ^ 2) := by rw [h1]
      _ = r * ((1 / (Nat.factorial k : ℝ)) *
            ((1 / (Nat.factorial k : ℝ)) * ((Pkn k k).eval (r ^ 2)) ^ 2)) *
            Real.exp (-r ^ 2) := by rw [hrkqkn_sq]
      _ = (1 / ((Nat.factorial k : ℝ) ^ 2)) * ((Pkn k k).eval (r ^ 2)) ^ 2 *
            (r * Real.exp (-r ^ 2)) := by ring
  have hfact_inv_le_one : 1 / ((Nat.factorial k : ℝ) ^ 2) ≤ 1 := by
    have hfac_ge_one_nat : 1 ≤ Nat.factorial k := Nat.succ_le_of_lt (Nat.factorial_pos k)
    have hfac_sq_ge : (1 : ℝ) ≤ (Nat.factorial k : ℝ) ^ 2 := by
      have hfac_ge_one : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast hfac_ge_one_nat
      nlinarith
    have htmp : (1 : ℝ) / ((Nat.factorial k : ℝ) ^ 2) ≤ (1 : ℝ) / 1 := by
      exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1) hfac_sq_ge
    simpa using htmp
  have hconst_le :
      Ak ^ 2 * Real.exp 1 * Cp ≤
        Ak ^ 2 * C0 * Real.exp 2 * Cp + Ak ^ 2 * Real.exp 1 * Cp + Cp * Real.exp 1 := by
    have hnonneg : 0 ≤ Ak ^ 2 * C0 * Real.exp 2 * Cp + Cp * Real.exp 1 := by
      rw [hC0_def]
      positivity
    linarith
  rw [hLHS_eq]
  calc
    (1 / ((Nat.factorial k : ℝ) ^ 2)) * ((Pkn k k).eval (r ^ 2)) ^ 2 * (r * Real.exp (-r ^ 2))
        ≤
      (1 / ((Nat.factorial k : ℝ) ^ 2)) *
          (Ak ^ 2 * (1 + |r - 1|) ^ (4 * k)) *
          (Real.exp 1 * (1 + |r - 1|) * Real.exp (-(r - 1) ^ 2 / 2)) := by
            gcongr
    _ = ((1 / ((Nat.factorial k : ℝ) ^ 2)) * Ak ^ 2 * Real.exp 1) *
          ((1 + |r - 1|) ^ (4 * k) * (1 + |r - 1|)) *
          Real.exp (-(r - 1) ^ 2 / 2) := by ring
    _ = ((1 / ((Nat.factorial k : ℝ) ^ 2)) * Ak ^ 2 * Real.exp 1) *
          (1 + |r - 1|) ^ (4 * k + 1) *
          Real.exp (-(r - 1) ^ 2 / 2) := by
            rw [← pow_succ]
    _ = ((1 / ((Nat.factorial k : ℝ) ^ 2)) * Ak ^ 2 * Real.exp 1) *
          ((1 + |r - 1|) ^ (4 * k + 1) * Real.exp (-(r - 1) ^ 2 / 2)) := by
            ring
    _ ≤ (Ak ^ 2 * Real.exp 1) *
          ((1 + |r - 1|) ^ (4 * k + 1) * Real.exp (-(r - 1) ^ 2 / 2)) := by
            have hcoef_le : ((1 / ((Nat.factorial k : ℝ) ^ 2)) * Ak ^ 2 * Real.exp 1) ≤
                Ak ^ 2 * Real.exp 1 := by
              have htmp : (1 / ((Nat.factorial k : ℝ) ^ 2)) * Ak ^ 2 ≤ 1 * Ak ^ 2 := by
                exact mul_le_mul_of_nonneg_right hfact_inv_le_one (sq_nonneg Ak)
              have htmp' : (1 / ((Nat.factorial k : ℝ) ^ 2)) * Ak ^ 2 ≤ Ak ^ 2 := by
                simpa using htmp
              nlinarith [Real.exp_pos 1, htmp']
            have hrest_nonneg :
                0 ≤ (1 + |r - 1|) ^ (4 * k + 1) * Real.exp (-(r - 1) ^ 2 / 2) := by
              positivity
            exact mul_le_mul_of_nonneg_right hcoef_le hrest_nonneg
    _ = (Ak ^ 2 * Real.exp 1) *
          (1 + |r - 1|) ^ (4 * k + 1) *
          Real.exp (-(r - 1) ^ 2 / 2) := by
            ring
    _ = (Ak ^ 2 * Real.exp 1) *
          ((1 + |r - 1|) ^ (4 * k + 1) * Real.exp (-(r - 1) ^ 2 / 2)) := by
            ring
    _ ≤ (Ak ^ 2 * Real.exp 1) * (Cp * Real.exp (-(r - 1) ^ 2 / 4)) := by
            have hcoef_nonneg : 0 ≤ Ak ^ 2 * Real.exp 1 := by positivity
            exact mul_le_mul_of_nonneg_left (hCp_bound (r - 1)) hcoef_nonneg
    _ = Ak ^ 2 * Real.exp 1 * Cp * Real.exp (-(r - 1) ^ 2 / 4) := by
            ring
    _ ≤ (Ak ^ 2 * C0 * Real.exp 2 * Cp + Ak ^ 2 * Real.exp 1 * Cp + Cp * Real.exp 1) *
          Real.exp (-(r - 1) ^ 2 / 4) := by
            exact mul_le_mul_of_nonneg_right hconst_le (by positivity)
    _ = (Ak ^ 2 * C0 * Real.exp 2 * Cp + Ak ^ 2 * Real.exp 1 * Cp + Cp * Real.exp 1) *
          Real.exp (-(r - Real.sqrt (k - k + 1 : ℝ)) ^ 2 / 4) := by
            simp [Real.sqrt_one]

/-- GPT Proposition 5.1 for n ≥ k: the radial density W_{k,n}(r) has Gaussian decay.
With m = n - k + 1, for all r ≥ 0:
  r * (r^k/√k!)² * |qkn k n r|² * exp(-r²) ≤ C_k * exp(-(r - √m)²/4). -/
private theorem radial_density_gaussian_bound_large (k : ℕ) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ (n : ℕ) (_hkn : k ≤ n) (r : ℝ) (_hr : 0 ≤ r),
      r * (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
        Real.exp (-r ^ 2)
      ≤ Ck * Real.exp (-(r - Real.sqrt (n - k + 1 : ℝ)) ^ 2 / 4) := by
  -- Obtain the three key bounds
  obtain ⟨Ak, hAk_pos, hAk_bound⟩ := scaled_laguerre_bound_Pkn k
  obtain ⟨Cp, hCp_pos, hCp_bound⟩ := poly_times_gaussian_absorption (4 * k + 1)
  set C0 := Real.exp (1 / 4) / 2 with hC0_def
  -- Constant handles both n=k and n>k cases
  use Ak ^ 2 * C0 * Real.exp 2 * Cp + Ak ^ 2 * Real.exp 1 * Cp + Cp * Real.exp 1
  constructor
  · positivity
  intro n hkn r hr
  -- Case r = 0: LHS = 0
  rcases eq_or_lt_of_le hr with rfl | hr_pos
  · simp only [sq_abs, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero,
      Real.exp_zero, mul_one, zero_sub, even_two, Even.neg_pow]
    positivity
  -- Now r > 0. Split n = k vs n > k.
  rcases eq_or_lt_of_le hkn with rfl | hkn_strict
  · exact radial_density_eq_step k r hr hr_pos hAk_pos hAk_bound hCp_pos hCp_bound hC0_def
  · exact radial_density_large_step k n hkn_strict r hr hr_pos hAk_pos hAk_bound
      hCp_pos hCp_bound hC0_def


/-- GPT Section 7: for n < k, the integrand decays super-exponentially.
Since b_{k,n}(r) is a polynomial of degree ≤ 2k-1, we get:
  r * (r^k/√k!)² * |qkn k n r|² * exp(-r²) ≤ C_k * (1+r^{4k+1}) * exp(-r²) ≤ C_k * exp(-r²/2). -/
private theorem radial_density_gaussian_bound_small (k : ℕ) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ (n : ℕ) (_hn : 1 ≤ n) (_hkn : n < k) (r : ℝ) (_hr : 0 ≤ r),
      r * (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
        Real.exp (-r ^ 2)
      ≤ Ck * Real.exp (-r ^ 2 / 2) := by
  -- Use `qkn_small_n_growth` to get polynomial growth in `r`, then absorb
  -- the polynomial with the reusable Gaussian absorption lemma.
  let A : ℝ := (((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k * (k : ℝ) ^ k)
  let m : ℕ := 4 * k + 1
  obtain ⟨Cpoly, hCpoly_pos, hCpoly⟩ :=
    HermiteLEAN.polynomial_times_gaussian_le_gaussian (a := 1) (by norm_num) m
  let K0 : ℝ := (4 * A ^ 2 / (Nat.factorial k : ℝ)) * Cpoly
  refine ⟨K0 + 1, by positivity, ?_⟩
  intro n hn hkn r hr
  have hA : |r ^ k * qkn k n r| ≤ A * (1 + r ^ (2 * k)) := by
    simpa [A] using qkn_small_n_growth k n hn hkn.le hr
  have hA_sq : |r ^ k * qkn k n r| ^ 2 ≤ (A * (1 + r ^ (2 * k))) ^ 2 := by
    nlinarith [hA, abs_nonneg (r ^ k * qkn k n r)]
  have hmain1 :
      r * (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
          Real.exp (-r ^ 2)
      = (r / (Nat.factorial k : ℝ)) * (|r ^ k * qkn k n r| ^ 2) * Real.exp (-r ^ 2) := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    have hmul : |r ^ k * qkn k n r| ^ 2 = (r ^ k) ^ 2 * |qkn k n r| ^ 2 := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hr k)]
      ring
    rw [hmul]
    ring
  rw [hmain1]
  have hmain2 :
      (r / (Nat.factorial k : ℝ)) * (|r ^ k * qkn k n r| ^ 2) * Real.exp (-r ^ 2)
      ≤ (r / (Nat.factorial k : ℝ)) * (A * (1 + r ^ (2 * k))) ^ 2 * Real.exp (-r ^ 2) := by
    gcongr
  refine le_trans hmain2 ?_
  have hsq : (1 + r ^ (2 * k)) ^ 2 ≤ 2 * (1 + (r ^ (2 * k)) ^ 2) := by
    nlinarith [sq_nonneg (r ^ (2 * k) - 1)]
  have hpoly_step : r * (1 + r ^ (2 * k)) ^ 2 ≤ 4 * (1 + r ^ (4 * k + 1)) := by
    have hsq' : r * (1 + r ^ (2 * k)) ^ 2 ≤ r * (2 * (1 + (r ^ (2 * k)) ^ 2)) := by
      gcongr
    have hpow4 : (r ^ (2 * k)) ^ 2 = r ^ (4 * k) := by
      rw [← pow_mul]
      ring_nf
    have hr_top : r ≤ 1 + r ^ (4 * k + 1) := by
      rcases le_or_gt r 1 with hr1 | hr1
      · linarith [pow_nonneg hr (4 * k + 1)]
      · have : r ^ (1 : ℕ) ≤ r ^ (4 * k + 1) := by
          apply pow_le_pow_right₀ hr1.le
          omega
        simpa using (le_trans this (by linarith))
    have htop_nonneg : 0 ≤ r ^ (4 * k + 1) := pow_nonneg hr _
    calc
      r * (1 + r ^ (2 * k)) ^ 2 ≤ r * (2 * (1 + (r ^ (2 * k)) ^ 2)) := hsq'
      _ = 2 * (r * (1 + r ^ (4 * k))) := by rw [hpow4]; ring
      _ = 2 * (r + r ^ (4 * k + 1)) := by ring_nf
      _ ≤ 2 * (2 * (1 + r ^ (4 * k + 1))) := by
            gcongr
            nlinarith [hr_top, htop_nonneg]
      _ = 4 * (1 + r ^ (4 * k + 1)) := by ring
  have hconst :
      (r / (Nat.factorial k : ℝ)) * (A * (1 + r ^ (2 * k))) ^ 2 * Real.exp (-r ^ 2)
      ≤ (4 * A ^ 2 / (Nat.factorial k : ℝ)) * ((1 + r ^ (4 * k + 1)) * Real.exp (-r ^ 2)) := by
    have hrew :
      (r / (Nat.factorial k : ℝ)) * (A * (1 + r ^ (2 * k))) ^ 2 * Real.exp (-r ^ 2)
      = (A ^ 2 / (Nat.factorial k : ℝ)) * (r * (1 + r ^ (2 * k)) ^ 2) * Real.exp (-r ^ 2) := by
      field_simp
    rw [hrew]
    have htmp :
      (A ^ 2 / (Nat.factorial k : ℝ)) * (r * (1 + r ^ (2 * k)) ^ 2) * Real.exp (-r ^ 2)
      ≤ (A ^ 2 / (Nat.factorial k : ℝ)) * (4 * (1 + r ^ (4 * k + 1))) * Real.exp (-r ^ 2) := by
      gcongr
    calc
      (A ^ 2 / (Nat.factorial k : ℝ)) * (r * (1 + r ^ (2 * k)) ^ 2) * Real.exp (-r ^ 2)
          ≤
        (A ^ 2 / (Nat.factorial k : ℝ)) * (4 * (1 + r ^ (4 * k + 1))) * Real.exp (-r ^ 2) := htmp
      _ = (4 * A ^ 2 / (Nat.factorial k : ℝ)) * ((1 + r ^ (4 * k + 1)) * Real.exp (-r ^ 2)) := by
            ring
  refine le_trans hconst ?_
  have hgauss_half : (1 + r ^ (4 * k + 1)) * Real.exp (-r ^ 2) ≤
                     Cpoly * Real.exp (-(1 / 2 : ℝ) * r ^ 2) := by
    simpa [m, one_mul] using hCpoly r hr
  have hmul :
      (4 * A ^ 2 / (Nat.factorial k : ℝ)) * ((1 + r ^ (4 * k + 1)) * Real.exp (-r ^ 2))
      ≤ (4 * A ^ 2 / (Nat.factorial k : ℝ)) * (Cpoly * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) := by
    gcongr
  refine le_trans hmul ?_
  have hrewrite_exp : Real.exp (-(1 / 2 : ℝ) * r ^ 2) = Real.exp (-r ^ 2 / 2) := by
    congr 1
    ring
  have hcoeff : K0 ≤ K0 + 1 := by linarith
  have hnonneg_exp : 0 ≤ Real.exp (-r ^ 2 / 2) := (Real.exp_pos _).le
  have hK0_le : K0 * Real.exp (-r ^ 2 / 2) ≤ (K0 + 1) * Real.exp (-r ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right hcoeff hnonneg_exp
  have hK0_eval :
      (4 * A ^ 2 / (Nat.factorial k : ℝ)) * (Cpoly * Real.exp (-(1 / 2 : ℝ) * r ^ 2))
      = K0 * Real.exp (-r ^ 2 / 2) := by
    dsimp [K0]
    rw [hrewrite_exp]
    ring
  calc
    (4 * A ^ 2 / (Nat.factorial k : ℝ)) * (Cpoly * Real.exp (-(1 / 2 : ℝ) * r ^ 2))
        = K0 * Real.exp (-r ^ 2 / 2) := hK0_eval
    _ ≤ (K0 + 1) * Real.exp (-r ^ 2 / 2) := hK0_le

/-- For n < k and r ≥ 0: exp(-r²/2) ≤ exp(-(1/4)*posPart(|r-√n|-(k+3))²).
Since n < k, √n ≤ k, so posPart(|r-√n|-(k+3)) ≤ r and p² ≤ r² ≤ 2r²,
hence -(1/4)*p² ≥ -(1/4)*r² ≥ -r²/2 when p ≤ r√2. Actually p ≤ r suffices
since (1/4)*p² ≤ (1/4)*r² ≤ r²/2. -/
private theorem exp_neg_sq_le_exp_posPart_sq (k n : ℕ) (hn : 1 ≤ n) (hnk : n < k)
    (r : ℝ) (hr : 0 ≤ r) :
    Real.exp (-r ^ 2 / 2) ≤
      Real.exp (-(1 / 4) *
        (posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ))) ^ 2) := by
  apply Real.exp_le_exp.mpr
  -- Need: -r²/2 ≤ -(1/4)*p², i.e. (1/4)*p² ≤ r²/2, i.e. p² ≤ 2r².
  -- Step 1: Show p ≤ r (where p = posPart(|r-√n|-(k+3)))
  have hsqrt_nn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt_le_k : Real.sqrt (n : ℝ) ≤ (k : ℝ) := by
    have hn_le_k : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk.le
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hsqrt_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [Real.sq_sqrt hn_nn, Real.sqrt_nonneg (n : ℝ)]
    linarith
  have hp_le_r : posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ)) ≤ r := by
    unfold posPart
    apply max_le _ hr
    -- |r - √n| ≤ r + √n (triangle inequality) and √n ≤ k (since n < k).
    -- So |r-√n| - (k+3) ≤ r + k - (k+3) = r - 3 ≤ r.
    have hab : |r - Real.sqrt (n : ℝ)| ≤ r + Real.sqrt (n : ℝ) := by
      rcases le_or_gt r (Real.sqrt (n : ℝ)) with hle | hgt
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        linarith
      · rw [abs_of_pos (sub_pos.mpr hgt)]
        linarith [hsqrt_nn]
    push_cast
    linarith
  -- Step 2: p² ≤ r² ≤ 2r², so (1/4)*p² ≤ (1/4)*2r² = r²/2.
  have hp_nn : 0 ≤ posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ)) :=
    le_max_right _ _
  nlinarith [sq_nonneg (posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ))),
    sq_le_sq' (by linarith) hp_le_r]

/-- Gaussian centered at √m implies Gaussian in posPart form with constant 1/4.
Since posPart(|r-√n|-(k+3)) ≤ |r-√m| (where m = n-k+1, using |√n-√m| ≤ k+1 ≤ k+3),
we get posPart(...)² ≤ (r-√m)² and hence:
  exp(-(r-√m)²/4) ≤ exp(-(1/4)*posPart(...)²). -/
private theorem gaussian_rStar_to_posPart (k n : ℕ) (hn : 1 ≤ n) (hkn : k ≤ n)
    (r : ℝ) (_hr : 0 ≤ r) :
    Real.exp (-(r - Real.sqrt (n - k + 1 : ℝ)) ^ 2 / 4) ≤
      Real.exp (-(1 / 4) *
        (posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ))) ^ 2) := by
  apply Real.exp_le_exp.mpr
  -- Need: -(r-√m)²/4 ≤ -(1/4)*p², i.e. p² ≤ (r-√m)².
  -- Suffices to show p ≤ |r-√m| where m = n-k+1.
  set m : ℝ := (n - k + 1 : ℝ)
  set p : ℝ := posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ))
  have hp_nn : 0 ≤ p := le_max_right _ _
  -- Key step: |√n - √m| ≤ k+2 (generous bound), so p ≤ |r-√m|.
  -- |r-√n| ≤ |r-√m| + |√m-√n| (triangle inequality).
  -- |√n-√m|: m = n-k+1, so √n-√m = √n - √(n-k+1).
  -- For k=0: m = n+1, √n ≤ √(n+1) = √m, so |√n-√m| ≤ 1 ≤ k+3.
  -- For k≥1: √n - √(n-k+1) ≤ n-(n-k+1) = k-1 < k+3 (using √a-√b ≤ a-b for b ≥ 1).
  -- In all cases: posPart(|r-√n|-(k+3)) ≤ posPart(|r-√m|+|√m-√n|-(k+3)) ≤ |r-√m|.
  suffices hp_le : p ≤ |r - Real.sqrt m| by
    nlinarith [sq_nonneg p, sq_abs (r - Real.sqrt m)]
  -- Prove p ≤ |r - √m|
  -- p = max(|r-√n|-(k+3), 0), so suffices to show |r-√n|-(k+3) ≤ |r-√m| and 0 ≤ |r-√m|.
  change posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ)) ≤ |r - Real.sqrt m|
  unfold posPart
  apply max_le _ (abs_nonneg _)
  -- Need: |r-√n|-(k+3) ≤ |r-√m|
  have htri : |r - Real.sqrt (n : ℝ)| ≤
      |r - Real.sqrt m| + |Real.sqrt m - Real.sqrt (n : ℝ)| := by
    calc |r - Real.sqrt (n : ℝ)|
        = |(r - Real.sqrt m) + (Real.sqrt m - Real.sqrt (n : ℝ))| := by ring_nf
      _ ≤ |r - Real.sqrt m| + |Real.sqrt m - Real.sqrt (n : ℝ)| := abs_add_le _ _
  -- Bound |√m - √n|. Since m = n-k+1, |√m-√n| ≤ k+1 ≤ k+3.
  have hshift : |Real.sqrt m - Real.sqrt (n : ℝ)| ≤ ((k + 1 : ℕ) : ℝ) := by
    -- m = (n:ℝ)-(k:ℝ)+1.
    have hm_pos : 1 ≤ m := by
      dsimp [m]
      have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      linarith
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- k = 0: m = n - 0 + 1 = n + 1.
      have hm_eq : m = (n : ℝ) + 1 := by dsimp [m]; simp
      rw [hm_eq]
      have hle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact le_trans
        (sqrt_sub_le_sub_of_one_le (by linarith) (by linarith))
        (by push_cast; linarith)
    · -- k ≥ 1: m = n-k+1 ≤ n, so √n ≥ √m.
      have hk_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hm_le_n : m ≤ (n : ℝ) := by
        change (n : ℝ) - (k : ℝ) + 1 ≤ (n : ℝ)
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      have hle : Real.sqrt m ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hm_le_n
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      -- -(√m - √n) = √n - √m ≤ n - m = k - 1 ≤ k + 1
      have hsub : Real.sqrt (n : ℝ) - Real.sqrt m ≤ (n : ℝ) - m :=
        sqrt_sub_le_sub_of_one_le hm_pos hm_le_n
      have hm_eq : (n : ℝ) - m = (k : ℝ) - 1 := by dsimp [m]; ring
      push_cast
      linarith
  push_cast at htri hshift ⊢
  linarith

/-- The key pointwise radial bound with decay constant 1/4.
Combines the scaled Laguerre bound, Poisson bound, and base Gaussian bound. -/
private theorem radial_integrand_pointwise_bound (k : ℕ) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 0 ≤ r →
      r * (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
        Real.exp (-r ^ 2)
      ≤ Ck * Real.exp (-(1 / 4) *
          (posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ))) ^ 2) := by
  -- Combine the two cases: n ≥ k and n < k.
  obtain ⟨C1, hC1_pos, hC1⟩ := radial_density_gaussian_bound_large k
  obtain ⟨C2, hC2_pos, hC2⟩ := radial_density_gaussian_bound_small k
  refine ⟨max C1 C2, by positivity, ?_⟩
  intro n hn r hr
  by_cases hkn : k ≤ n
  · -- Case n ≥ k: use Proposition 5.1 + gap conversion
    have h1 := hC1 n hkn r hr
    have hgauss := gaussian_rStar_to_posPart k n hn hkn r hr
    calc r * (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
          Real.exp (-r ^ 2)
        ≤ C1 * Real.exp (-(r - Real.sqrt (n - k + 1 : ℝ)) ^ 2 / 4) := h1
      _ ≤ C1 * Real.exp (-(1 / 4) *
            (posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hgauss (le_of_lt hC1_pos)
      _ ≤ max C1 C2 * Real.exp (-(1 / 4) *
            (posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- Case n < k: use the polynomial bound
    push Not at hkn
    have h2 := hC2 n hn hkn r hr
    have hsmall := exp_neg_sq_le_exp_posPart_sq k n hn hkn r hr
    calc r * (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
          Real.exp (-r ^ 2)
        ≤ C2 * Real.exp (-r ^ 2 / 2) := h2
      _ ≤ C2 * Real.exp (-(1 / 4) *
            (posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hsmall (le_of_lt hC2_pos)
      _ ≤ max C1 C2 * Real.exp (-(1 / 4) *
            (posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Single-basis localization near the annulus `|z| ~ sqrt n`. -/
theorem single_basis_localization :
    ∀ k : ℕ,
      ∃ C c : ℝ,
        0 < C ∧ 0 < c ∧
          ∀ n j : ℕ,
            1 ≤ n →
              annulusIntegralSq (Phi k n) j ≤
                C *
                  Real.exp
                    (-c *
                      (posPart
                        (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ))) ^ 2) := by
  -- The proof uses a pointwise radial bound (the key analytic estimate),
  -- then integrates over [j, j+1] and converts the radial gap to the shell gap.
  intro k
  -- Step 1: Obtain the pointwise radial bound.
  obtain ⟨Ck, hCk_pos, hCk⟩ := radial_integrand_pointwise_bound k
  -- Step 2: Use the pointwise bound to close the theorem (with c = 1/4).
  refine ⟨2 * Ck + 1, 1 / 4, by positivity, by norm_num, ?_⟩
  intro n j hn
  rw [annulusIntegralSq_Phi_eq k n j]
  have hjle : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j
  -- Integrability of the radial integrand on [j, j+1].
  have hint : IntervalIntegrable
      (fun r => r * Real.exp (-r ^ 2) *
        ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2))
      volume (j : ℝ) ((j + 1 : ℕ) : ℝ) := by
    exact intervalIntegrable_basisRadialTerm k n j
  -- Bound the integral pointwise: replace integrand by the shell-level Gaussian.
  have hbound_int :
      ∫ r in (j : ℝ)..((j + 1 : ℕ) : ℝ),
        r * Real.exp (-r ^ 2) *
          ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2)
      ≤ Ck * Real.exp (-(1 / 4) *
          (posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ))) ^ 2) := by
    calc
      ∫ r in (j : ℝ)..((j + 1 : ℕ) : ℝ),
          r * Real.exp (-r ^ 2) *
            ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2)
        ≤ ∫ r in (j : ℝ)..((j + 1 : ℕ) : ℝ),
          Ck * Real.exp (-(1 / 4) *
            (posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ))) ^ 2) := by
        refine intervalIntegral.integral_mono_on hjle hint intervalIntegrable_const ?_
        intro r hr
        have hr_nn : 0 ≤ r := le_trans (by exact_mod_cast Nat.zero_le j) hr.1
        -- Pointwise bound at r (with constant 1/4):
        have hpw := hCk n hn r hr_nn
        -- Reorder multiplication to match the integrand form.
        have hpw' : r * Real.exp (-r ^ 2) *
            (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2) =
          r * (((r ^ k / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2) *
            Real.exp (-r ^ 2) := by ring
        rw [hpw']
        -- Gap comparison: posPart(|j - √n| - (k+4)) ≤ posPart(|r - √n| - (k+3))
        have hgap := shell_centered_gap_le_pointwise_gap k n j
          (show r ∈ Set.Icc (j : ℝ) ((j + 1 : ℕ) : ℝ) from ⟨hr.1, hr.2⟩)
        have hgap_nn1 :
            0 ≤ posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) :=
          le_max_right _ _
        have hgap_nn2 :
            0 ≤ posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ)) :=
          le_max_right _ _
        -- Monotonicity of Gaussian: larger posPart => smaller exp
        have hexp : Real.exp (-(1 / 4) *
            posPart (|r - Real.sqrt (n : ℝ)| - ((k + 3 : ℕ) : ℝ)) ^ 2) ≤
          Real.exp (-(1 / 4) *
            posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| -
              ((k + 4 : ℕ) : ℝ)) ^ 2) := by
          apply Real.exp_le_exp.mpr; nlinarith [hgap, hgap_nn1, hgap_nn2]
        exact hpw.trans (mul_le_mul_of_nonneg_left hexp (le_of_lt hCk_pos))
      _ = Ck * Real.exp (-(1 / 4) *
            (posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| -
              ((k + 4 : ℕ) : ℝ))) ^ 2) := by
        rw [intervalIntegral.integral_const]; norm_num
  -- Assemble: 2 * integral ≤ 2 * Ck * Gaussian ≤ (2*Ck+1) * Gaussian.
  have hexp_nn : 0 ≤ Real.exp (-(1 / 4) *
      (posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ))) ^ 2) := by
    positivity
  calc
    2 * ∫ r in (j : ℝ)..((j + 1 : ℕ) : ℝ),
        r * Real.exp (-r ^ 2) *
          ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) ^ 2) * |qkn k n r| ^ 2)
      ≤ 2 * (Ck * Real.exp (-(1 / 4) *
          (posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| -
            ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
        gcongr
    _ = 2 * Ck * Real.exp (-(1 / 4) *
          (posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| -
            ((k + 4 : ℕ) : ℝ))) ^ 2) := by ring
    _ ≤ (2 * Ck + 1) * Real.exp (-(1 / 4) *
          (posPart (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| -
            ((k + 4 : ℕ) : ℝ))) ^ 2) := by
        nlinarith

end HermitekLEAN
