/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.Pullback
import LeanPool.Zeta5Irrational.Arith.SmallPrime
import LeanPool.Zeta5Irrational.Arith.SmallPrimeRes
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Small primes: the analogue of Lemma 3.3

For `A` integer-valued on `ℤ` with `deg A ≤ d`, `2K ≤ d`:
`v_p^G(τ_X((K!)² A / ∏_{0<|r|≤K}(x - r))) ≥ -6 log_p (d+1) - v_p(24)`.

Instead of the paper's ball analysis we evaluate the polynomial part on the window
`K+1, …, d-K+1` beyond all poles, where `(K!)²/∏(m - r) = 1/(C(m-1,K) C(m+K,K))`, and use the
window lemma.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

lemma mem_PlK_iff {K : ℕ} {r : ℤ} (hr : r ∈ PlK K) :
    ∃ j ∈ Icc 1 K, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ r = ε * j := by
  simp only [PlK, Finset.mem_union, Finset.mem_image] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ⟨j, hj, 1, Or.inl rfl, by ring⟩
  · exact ⟨j, hj, -1, Or.inr rfl, by ring⟩

/-- `(K!)² / ((K-j)! (K+j)!) = C(2K, K+j) / C(2K, K)`. -/
lemma factorial_ratio {j K : ℕ} (hjK : j ≤ K) :
    (K.factorial : ℚ) ^ 2 / (((K - j).factorial : ℚ) * ((K + j).factorial : ℚ)) =
      ((2 * K).choose (K + j) : ℚ) / ((2 * K).choose K : ℚ) := by
  have h1 :
    ((2 * K).choose (K + j) : ℚ) * ((K + j).factorial : ℚ) * ((K - j).factorial : ℚ) =
      ((2 * K).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (by omega : K + j ≤ 2 * K)
    rw [show 2 * K - (K + j) = K - j by omega] at this
    exact_mod_cast this
  have h2 :
    ((2 * K).choose K : ℚ) * (K.factorial : ℚ) * (K.factorial : ℚ) = ((2 * K).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (by omega : K ≤ 2 * K)
    rw [show 2 * K - K = K by omega] at this
    exact_mod_cast this
  have hc : ((2 * K).choose K : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have ha : ((K - j).factorial : ℚ) ≠ 0 := by positivity
  have hb : ((K + j).factorial : ℚ) ≠ 0 := by positivity
  rw [div_eq_div_iff (mul_ne_zero ha hb) hc]
  linear_combination h2 - h1

/-- The residue factor `(K!)² / ∏_{s ≠ r} (r - s)` has valuation `≥ -log_p (2K)`. -/
lemma VG_res_factor {K : ℕ} {r : ℤ} (hr : r ∈ PlK K) :
    VG p ((K.factorial : ℚ) ^ 2 / ∏ s ∈ (PlK K).erase r, ((r : ℚ) - s))
      (-(Nat.log p (2 * K) : ℚ)) := by
  obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hr
  have hj' := Finset.mem_Icc.mp hj
  obtain ⟨σ, hσ, he⟩ := prod_erase_PlK hj'.1 hj'.2 ε hε
  rw [he]
  have hjf : (j.factorial : ℚ) = j * ((j - 1).factorial : ℚ) := by
    rw [← Nat.mul_factorial_pred (by omega : j ≠ 0)]; push_cast; ring
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have e :
    (K.factorial : ℚ) ^ 2 /
        (σ * ((j - 1).factorial : ℚ) * ((K - j).factorial : ℚ) * ((K + j).factorial : ℚ) /
          (j.factorial : ℚ)) =
      (σ * j) * (((2 * K).choose (K + j) : ℚ) * ((2 * K).choose K : ℚ)⁻¹) := by
    rw [← div_eq_mul_inv, ← factorial_ratio hj'.2, hjf]
    have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have h1 : ((j - 1).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((K - j).factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((K + j).factorial : ℚ) ≠ 0 := by positivity
    have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    field_simp
    linear_combination (-1 : ℚ) * hσ2
  rw [e]
  have hσv : VG p (σ * j) 0 := by
    rcases hσ with rfl | rfl
    · simpa using VG.natCast (p := p) j
    · simpa using (VG.natCast (p := p) j).neg
  have :=
    hσv.mul
      ((VG.natCast (p := p) ((2 * K).choose (K + j))).mul
        (VG_choose_inv (p := p) (by omega : K ≤ 2 * K)))
  exact this.mono (by simp)

/-- **The analogue of Lemma 3.3** for the poles `±1, …, ±K`. -/
theorem crude_tauX {K d : ℕ} (hK : 1 ≤ K) (hdK : 2 * K ≤ d) (A : ℚ[X]) (hA : A.natDegree ≤ d)
    (hint : ∀ z : ℤ, VG p (A.eval (z : ℚ)) 0) :
    GV p (tauX (C ((K.factorial : ℚ) ^ 2) * A) (PlK K))
      (-6 * (Nat.log p (d + 1) : ℚ) - padicValNat p 24) := by
  set g := C ((K.factorial : ℚ) ^ 2) * A with hg
  set Λ : ℚ := (Nat.log p (d + 1) : ℚ) with hΛ
  have hΛ0 : (0 : ℚ) ≤ Λ := by positivity
  have hlog2K : (Nat.log p (2 * K) : ℚ) ≤ Λ := log_mono (by omega)
  have hv24 : (0 : ℚ) ≤ padicValNat p 24 := by
    positivity
      -- residues
  have hres : ∀ r ∈ PlK K, VG p (resP g (PlK K) r) (-Λ) := by
    intro r hr
    unfold resP
    rw [hg, eval_mul, eval_C, mul_comm, mul_div_assoc]
    refine ((hint r).mul (VG_res_factor hr)).mono ?_
    linarith
  have hgdeg : g.natDegree ≤ d := (natDegree_C_mul_le _ _).trans hA
  unfold tauX
  refine GV.add (GV.C ?_) (GV.sum _ fun r hr => ?_)
  · -- the polynomial part
    set P := polyPart g (PlK K) with hP
    have hPd : P.natDegree ≤ d - 2 * K := by
      have := natDegree_polyPart_le g (PlK K)
      rw [card_PlK, ← hP] at this
      omega
        -- values on the window
    have hwin : ∀ i ≤ d - 2 * K, VG p (P.eval ((((K + 1 : ℕ) : ℤ) + i : ℤ) : ℚ)) (-2 * Λ) := by
      intro i hi
      set m : ℕ := K + 1 + i with hm
      have hmK : K < m := by omega
      have hmd : m + K ≤ d + 1 := by omega
      have hcast : ((((K + 1 : ℕ) : ℤ) + i : ℤ) : ℚ) = (m : ℚ) := by rw [hm]; push_cast; ring
      rw [hcast]
      have hpf :
        g.eval (m : ℚ) =
          P.eval (m : ℚ) * (piPl (PlK K)).eval (m : ℚ) +
            ∑ r ∈ PlK K,
              (C (resP g (PlK K) r) * ∏ s ∈ (PlK K).erase r, (X - C (s : ℚ))).eval (m : ℚ) := by
        conv_lhs => rw [partial_fractionsP g (PlK K)]
        rw [eval_add, eval_mul, eval_finsetSum]
      have hpi : (piPl (PlK K)).eval (m : ℚ) = ∏ s ∈ PlK K, ((m : ℚ) - s) := by
        unfold piPl;
        rw [eval_prod]; simp
      have hpi' := prod_PlK_sub (K := K) hmK
      have hne : ∀ s ∈ PlK K, (m : ℚ) - s ≠ 0 := by
        intro s hs
        obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hs
        have := (Finset.mem_Icc.mp hj).2
        rcases hε with rfl | rfl <;> push_cast <;> intro h
        · have : (m : ℚ) = j := by linarith
          have : m = j := by exact_mod_cast this
          omega
        · have : (m : ℚ) + j = 0 := by linarith
          have : m + j = 0 := by exact_mod_cast this
          omega
      have hPi0 : ∏ s ∈ PlK K, ((m : ℚ) - s) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
      have hterm :
        ∀ r ∈ PlK K,
          (C (resP g (PlK K) r) * ∏ s ∈ (PlK K).erase r, (X - C (s : ℚ))).eval (m : ℚ) =
            resP g (PlK K) r / ((m : ℚ) - r) * ∏ s ∈ PlK K, ((m : ℚ) - s) := by
        intro r hr
        rw [eval_mul, eval_C, eval_prod, ← Finset.mul_prod_erase _ _ hr]
        simp only [eval_sub, eval_X, eval_C]
        field_simp [hne r hr]
      rw [Finset.sum_congr rfl hterm, hpi, ← Finset.sum_mul] at hpf
      have hPm :
        P.eval (m : ℚ) =
          g.eval (m : ℚ) / ∏ s ∈ PlK K, ((m : ℚ) - s) -
            ∑ r ∈ PlK K, resP g (PlK K) r / ((m : ℚ) - r) := by
        rw [eq_sub_iff_add_eq, eq_div_iff hPi0, add_mul]
        exact hpf.symm
      rw [hPm]
      refine VG.sub ?_ (VG.sum _ fun r hr => ?_)
      · rw [hpi', hg, eval_mul, eval_C]
        have hc1 : ((m - 1).choose K : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
        have hc2 : ((m + K).choose K : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
        have hKf : (K.factorial : ℚ) ≠ 0 := by positivity
        have e :
          (K.factorial : ℚ) ^ 2 * A.eval (m : ℚ) /
              ((K.factorial : ℚ) ^ 2 * ((m - 1).choose K : ℚ) * ((m + K).choose K : ℚ)) =
            A.eval (m : ℚ) * (((m - 1).choose K : ℚ)⁻¹ * ((m + K).choose K : ℚ)⁻¹) :=
          by field_simp
        rw [e]
        have h1 := VG_choose_inv (p := p) (by omega : K ≤ m - 1)
        have h2 := VG_choose_inv (p := p) (by omega : K ≤ m + K)
        have l1 : (Nat.log p (m - 1) : ℚ) ≤ Λ := log_mono (by omega)
        have l2 : (Nat.log p (m + K) : ℚ) ≤ Λ := log_mono (by omega)
        have := (hint m).mul (h1.mul h2)
        push_cast at this
        exact this.mono (by linarith)
      · obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hr
        have hj' := Finset.mem_Icc.mp hj
        have hpos : ∃ u : ℕ, 1 ≤ u ∧ u ≤ d + 1 ∧ (m : ℚ) - ((ε * j : ℤ) : ℚ) = u := by
          rcases hε with rfl | rfl
          · exact ⟨m - j, by omega, by omega, by push_cast [show j ≤ m by omega]; ring⟩
          · exact ⟨m + j, by omega, by omega, by push_cast; ring⟩
        obtain ⟨u, hu1, hud, hu⟩ := hpos
        rw [div_eq_mul_inv, hu]
        have := (hres _ hr).mul (VG.inv_nat (p := p) hu1 hud)
        exact this.mono (by rw [← hΛ]; linarith)
    have hall := VG_eval_int_of_window hPd ((K + 1 : ℕ) : ℤ) hwin
    have htau :=
      tau_bound (p := p) hPd (β := -2 * Λ) (fun m _ => by have := hall m; simpa using this)
    refine htau.mono ?_
    have : (Nat.log p (d - 2 * K + 1) : ℚ) ≤ Λ := log_mono (by omega)
    linarith
  · -- the pole terms
    obtain ⟨j, hj, ε, hε, hrj⟩ := mem_PlK_iff hr
    have hj' := Finset.mem_Icc.mp hj
    have hdd : dd r ≤ d + 1 := by
      rw [hrj]; rcases hε with rfl | rfl
      · rw [one_mul, dd_nat]; omega
      · rw [neg_one_mul, dd_neg hj'.1]; omega
    have hH : GV p (C (H5 (dd r)) - X) (-5 * Λ) :=
      (GV.C
            ((VG_H5_log (p := p) (dd r)).mono
              (by
                have : (Nat.log p (dd r) : ℚ) ≤ Λ := log_mono hdd
                linarith))).sub
        (GV.X.mono (by linarith))
    refine (GV.C_mul (hres r hr) hH).mono ?_
    linarith

end Zeta5Irrational
