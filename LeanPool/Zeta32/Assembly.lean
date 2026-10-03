/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeObstruction
public import Mathlib.Analysis.PSeries

/-! Zeta32 — Assembly. -/

public section
open Polynomial Filter Topology
namespace Zeta32

theorem abs_P_aeval_eq_dtilde_Qtilde (r : ℚ) (n : ℕ) (x : ℝ) :
    |aeval x (P r n)| = (dtilde r n : ℝ) * |aeval x (Qtilde r n)| := by
  have h := congrArg (fun F : ℚ[X] => F.eval₂ (algebraMap ℚ ℝ) x)
    (P_eq_dtilde_Qtilde r n)
  rw [eval₂_map, eval₂_mul, eval₂_C] at h
  have heval : aeval x (P r n) = (dtilde r n : ℝ) * aeval x (Qtilde r n) := by
    simpa only [aeval_def, ← IsScalarTower.algebraMap_eq ℤ ℚ ℝ] using! h
  rw [heval, abs_mul,
    abs_of_pos (show (0 : ℝ) < (dtilde r n : ℝ) by exact_mod_cast dtilde_pos r n)]

/-- If `Q r n = 0` then the primitive polynomial is `0`. -/
theorem P_eq_zero_of_Q_eq_zero (r : ℚ) (n : ℕ) (hQ : Q r n = 0) : P r n = 0 := by
  simp [P, primitiveQ, hQ]

/-- The two growth nodes of the proof notes, §9, as hypotheses: arithmetic (`A = 283/50`, only
needed when `Q r n ≠ 0`)
and analytic (`F = −6`). -/
def ArithNode (r : ℚ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Q r n ≠ 0 → Real.log (dtilde r n) ≤ (283/50 + ε) * (n:ℝ)^2

/-- Eventual exponential bound for the scaled polynomial evaluated at the target zeta value. -/
def AnalyticNode (r : ℚ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, |Polynomial.aeval (Cr r) (Qtilde r n)| ≤ Real.exp ((-6 + ε) * (n:ℝ)^2)

/-- Nonzero constant reduction of the primitive polynomial at admissible prime edges. -/
def PrimeEdgeNode (r : ℚ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → p ∉ PrimeEdge.exceptional → ¬ p ∣ r.den →
    ∃ c : ZMod p, c ≠ 0 ∧ (P r (p-1)).map (Int.castRingHom (ZMod p)) = Polynomial.C c

theorem denominator_decay (r : ℚ) (hArith : ArithNode r) (hAnalytic : AnalyticNode r) (b : ℕ)
  (hb : 0 < b) :
    Tendsto (fun n => (b:ℝ)^(3*n) * |aeval (Cr r) (P r n)|) atTop (𝓝 0) := by
  have hA := hArith (1/100) (by norm_num)
  have hF := hAnalytic (1/100) (by norm_num)
  have hExp : Tendsto (fun n : ℕ => (b:ℝ)^(3*n) * Real.exp (-(8/25) * (n:ℝ)^2))
      atTop (𝓝 0) := by
    exact tendsto_pow_mul_exp_neg_sq_of_pos (by norm_num) 3 b hb
  refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg (by positivity) (abs_nonneg _))
    ?_ hExp
  filter_upwards [hA, hF] with n hAn' hFn
  by_cases hQ : Q r n = 0
  · rw [P_eq_zero_of_Q_eq_zero r n hQ]
    simp only [map_zero, abs_zero, mul_zero, neg_mul]
    positivity
  have hAn := hAn' hQ
  have hq : |aeval (Cr r) (Qtilde r n)| ≤ Real.exp ((-6 + 1/100) * (n:ℝ)^2) := hFn
  have hd : (dtilde r n : ℝ) ≤ Real.exp ((283/50 + 1/100) * (n:ℝ)^2) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast dtilde_pos r n)).mp hAn
  rw [abs_P_aeval_eq_dtilde_Qtilde]
  have hprod := mul_le_mul hd hq (abs_nonneg _) (Real.exp_nonneg _)
  have hsum : ((283:ℝ)/50 + 1/100 + (-6 + 1/100)) * (n:ℝ)^2 = -(8/25) * (n:ℝ)^2 := by
    norm_num
  rw [← Real.exp_add] at hprod
  have hadd : ((283:ℝ)/50 + 1 / 100) * (n:ℝ)^2 + (-6 + 1 / 100) * (n:ℝ)^2 =
      ((283:ℝ)/50 + 1 / 100 + (-6 + 1 / 100)) * (n:ℝ)^2 := by ring
  have hprod' : ↑(dtilde r n) * |(aeval (Cr r)) (Qtilde r n)| ≤
      Real.exp (((283:ℝ)/50 + 1 / 100) * (n:ℝ)^2 + (-6 + 1 / 100) * (n:ℝ)^2) := by
    convert hprod using 1
  rw [hadd, hsum] at hprod'
  exact mul_le_mul_of_nonneg_left hprod' (by positivity)

theorem rational_nonzero_infinitely_often (r : ℚ) (hEdge : PrimeEdgeNode r) (q : ℚ) :
    ∃ᶠ n in atTop, aeval (q : ℝ) (P r n) ≠ 0 := by
  rw [Filter.frequently_atTop]
  intro N
  let T := max (max (max 7 (q.den + 1)) (r.den + 1))
    (Zeta32.PrimeEdge.exceptional.sup id + 1)
  obtain ⟨p, hpT, hp⟩ := Nat.exists_infinite_primes (max T (N + 2))
  have hpT' : T ≤ p := le_trans (le_max_left _ _) hpT
  have hpN : N + 2 ≤ p := le_trans (le_max_right _ _) hpT
  have hqT : q.den + 1 ≤ T := by
    dsimp [T]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hrT : r.den + 1 ≤ T := by
    dsimp [T]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hsevenT : 7 ≤ T := by
    dsimp [T]
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hp7 : 7 ≤ p := le_trans hsevenT hpT'
  have hpden : q.den < p := by omega
  have hrden : r.den < p := by omega
  have hpE : p ∉ Zeta32.PrimeEdge.exceptional := by
    intro hmem
    have hle : p ≤ Zeta32.PrimeEdge.exceptional.sup id := Finset.le_sup (f := id) hmem
    have hsT : Zeta32.PrimeEdge.exceptional.sup id + 1 ≤ T := by
      dsimp [T]
      exact le_max_right _ _
    have hs : Zeta32.PrimeEdge.exceptional.sup id + 1 ≤ p := le_trans hsT hpT'
    omega
  have hpden' : ¬ p ∣ r.den := by
    intro hdiv
    have hle : p ≤ r.den := Nat.le_of_dvd r.den_pos hdiv
    omega
  let : Fact p.Prime := ⟨hp⟩
  have hqden : (q.den : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ q.den := (ZMod.natCast_eq_zero_iff q.den p).mp h
    have hle : p ≤ q.den := Nat.le_of_dvd q.den_pos hdiv
    omega
  obtain ⟨c, hc, hred⟩ := hEdge p hp7 hpE hpden'
  have hne := rational_nonzero_of_constant_reduction (P r (p - 1)) p c hc hred q hqden
  refine ⟨p - 1, ?_, hne⟩
  omega

/-- the proof notes, §9: the three nodes imply irrationality. -/
theorem main_of_nodes (r : ℚ) (hArith : ArithNode r) (hAnalytic : AnalyticNode r) (hEdge :
  PrimeEdgeNode r) :
    Irrational (Cr r) := by
  apply Zeta32.irrational_of_int_polynomials (Cr r) (P r) (fun n => 3*n)
  · exact fun n => P_natDegree_le r n
  · intro b hb
    exact denominator_decay r hArith hAnalytic b hb
  · exact rational_nonzero_infinitely_often r hEdge

end Zeta32

end
