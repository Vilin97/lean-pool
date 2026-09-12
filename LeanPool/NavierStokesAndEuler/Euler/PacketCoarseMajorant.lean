/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift
import Mathlib.Algebra.Order.Star.Real
meta import Lean.Meta.Tactic.NormCast
import Mathlib.Tactic.Bound

/-! A polynomial base controls every surviving finite packet grade after the final factorial split.
-/

@[expose] public section


namespace EulerPacketCoarseMajorant

open EulerGevrey


/-- Its N-degree is 220, leaving room in the source's exponent 300 for finite sums. -/
def gradeBase (R : ℝ) (N : ℕ) : ℝ := (4*R*(550*(N : ℝ))^2)^110

theorem gradeBase_nonneg (R : ℝ) (N : ℕ) : 0 ≤ gradeBase R N := by
  unfold gradeBase
  positivity

theorem gradeBase_ge_one (R : ℝ) (hR : 1 ≤ R) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ gradeBase R N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase : (1 : ℝ) ≤ 4*R*(550*(N : ℝ))^2 := by nlinarith
  exact one_le_pow₀ hbase

theorem factorial_le_grade_power (N p d : ℕ) (hN : 1 ≤ N) (hp : p ≤ 2 * N + 2)
    (hd : d ≤ 110 * (p + 1)) : (d.factorial : ℝ) ≤ (550*(N : ℝ))^d := by
  have hdN : d ≤ 550*N := by omega
  have h := (Nat.factorial_le_pow d).trans (Nat.pow_le_pow_left hdN d)
  exact_mod_cast h

/-- The external derivative radius is enlarged once; all grade dependence is in one polynomial base.
-/
theorem majorant_grade_bound (R : ℝ) (hR : 1 ≤ R) (N p d n : ℕ)
    (hN : 1 ≤ N) (hp : p ≤ 2 * N + 2) (hd : d ≤ 110 * (p + 1)) :
    majorant R d n ≤ (gradeBase R N)^(p+1)*majorant (4*R) 0 n := by
  have hB : (1 : ℝ) ≤ 550*(N : ℝ) := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hbase : (1 : ℝ) ≤ 4*R*(550*(N : ℝ))^2 := by nlinarith
  have hfac := factorial_le_grade_power N p d hN hp hd
  have hfac2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (d.factorial : ℝ) by positivity) hfac 2
  have hfactor : (4*R)^d*(d.factorial : ℝ)^2 ≤ (gradeBase R N)^(p+1) := by
    calc
      _ ≤ (4*R)^d*((550*(N : ℝ))^d)^2 :=
        mul_le_mul_of_nonneg_left hfac2 (pow_nonneg (by linarith) _)
      _ = (4*R*(550*(N : ℝ))^2)^d := by
        have hpow : ((550*(N : ℝ))^d)^2=((550*(N : ℝ))^2)^d := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm d 2]
        rw [hpow]
        exact (mul_pow (4*R) ((550*(N : ℝ))^2) d).symm
      _ ≤ (4*R*(550*(N : ℝ))^2)^(110*(p+1)) := pow_le_pow_right₀ hbase hd
      _ = (gradeBase R N)^(p+1) := by rw [pow_mul]; rfl
  exact (majorant_coarse_split R (by linarith) d n).trans
    (mul_le_mul_of_nonneg_right hfactor (majorant_nonneg (4*R) (by linarith) 0 n))

end EulerPacketCoarseMajorant
