/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealPre2.Algebra

namespace Computable
namespace CReal
/-! ### Order Structure -/

/--
Definition of the order relation on CReal.Pre (Constructive Definition).
x ≤ y if ∀ n, x_{n+1} ≤ y_{n+1} + 1/2ⁿ.
-/
protected def Pre.le (x y : CReal.Pre) : Prop :=
  ∀ n : ℕ, x.approx (n + 1) ≤ y.approx (n + 1) + (1 : ℚ) / 2 ^ n

-- Helper for Epsilon-Delta arguments.
lemma find_index_for_bound {B ε : ℚ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ K : ℕ, B / 2 ^ K < ε := by
  rcases exists_pow_gt (div_pos hB hε) with ⟨K, hK⟩
  have h_step : B / 2 ^ K < ε := by
    apply (div_lt_iff (pow_pos (by norm_num) _)).mpr
    rw [mul_comm]; apply (div_lt_iff hε).mp hK
  exact ⟨K, h_step⟩

-- Reusable small algebra lemmas for combining fractions with equal denominators.
lemma one_plus_two_over_pow (t : ℕ) :
  (1 : ℚ) / 2 ^ t + 2 / 2 ^ t = 3 / 2 ^ t := by
  ring

lemma sum_two_halves (n : ℕ) :
  (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) = 2 / 2 ^ (n + 1) := by
  ring

lemma le_well_defined_forward
    {x₁ x₂ y₁ y₂ : CReal.Pre}
    (hx : CReal.Pre.Equiv x₁ x₂) (hy : CReal.Pre.Equiv y₁ y₂)
    (h_le : CReal.Pre.le x₁ y₁) : CReal.Pre.le x₂ y₂ := by
  intro n
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨m, hm_bound⟩ := find_index_for_bound (by norm_num : 0 < (3 : ℚ)) hε
  let k := max (n+1) (m+1)
  have h_n_le_k : n+1 ≤ k := le_max_left _ _
  have h_m_le_k : m+1 ≤ k := le_max_right _ _
  have h_k_sub_1_ge_m : m ≤ k-1 := Nat.le_sub_of_add_le h_m_le_k
  have hkpos : 1 ≤ k := le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_n_le_k
  have hk1 : (k - 1) + 1 = k := Nat.sub_add_cancel hkpos
  have h_error_bound : 3 / 2^(k-1) < ε := by
    have h_pow_bound : (2:ℚ)^m ≤ 2^(k-1) :=
      (pow_le_pow_iff_right₀ rfl).mpr h_k_sub_1_ge_m
    have h_div_le : (3:ℚ) / 2^(k-1) ≤ 3 / 2^m := by
      have hc : 0 < (2 : ℚ) ^ m := pow_pos (by norm_num) m
      exact div_le_div_of_le_left (by norm_num) hc h_pow_bound
    linarith [hm_bound]
  have h_hyp0 := h_le (k-1)
  have h_hyp : x₁.approx k ≤ y₁.approx k + 1 / 2^(k-1) := by
    simpa [hk1] using h_hyp0
  have hx_equiv := hx (k-1)
  have hy_equiv := hy (k-1)
  have hx_reg : |x₂.approx (n+1) - x₂.approx k| ≤ 1/2^(n+1) :=
    x₂.is_regular (n+1) k h_n_le_k
  have hy_reg : |y₂.approx (n+1) - y₂.approx k| ≤ 1/2^(n+1) :=
    y₂.is_regular (n+1) k h_n_le_k
  have h1 : x₂.approx (n+1) ≤ x₂.approx k + 1/2^(n+1) := by
    have h := (abs_sub_le_iff).1 hx_reg
    linarith [h.left]
  have h2 : x₂.approx k ≤ x₁.approx k + 1/2^(k-1) := by
    have h := (abs_sub_le_iff).1 hx_equiv
    have h' : x₂.approx k - x₁.approx k ≤ 1 / 2 ^ (k - 1) := by
      simpa [hk1] using h.right
    have : x₂.approx k ≤ (1 / 2 ^ (k - 1)) + x₁.approx k :=
      (sub_le_iff_le_add).1 h'
    simpa [add_comm] using this
  have h4 : y₁.approx k ≤ y₂.approx k + 1/2 ^ (k - 1) := by
    have h := (abs_sub_le_iff).1 hy_equiv
    have h' : y₁.approx k - y₂.approx k ≤ 1 / 2 ^ (k - 1) := by
      simpa [hk1] using h.left
    linarith
  have h5 : y₂.approx k ≤ y₂.approx (n+1) + 1/2^(n+1) := by
    have h := (abs_sub_le_iff).1 hy_reg
    linarith [h.right]
  have h_mid : x₂.approx k ≤ y₁.approx k + 2 / 2^(k-1) := by
    calc
      x₂.approx k ≤ x₁.approx k + 1/2^(k-1) := h2
      _ ≤ (y₁.approx k + 1/2^(k-1)) + 1/2^(k-1) := by
            exact Rat.add_le_add_right.mpr h_hyp
      _ = y₁.approx k + (1/2^(k-1) + 1/2^(k-1)) := by ring_nf
      _ = y₁.approx k + 2 / 2^(k-1) := by ring_nf
  have h_mid' : x₂.approx k ≤ y₂.approx k + 3 / 2^(k-1) := by
    have step : y₁.approx k + 2 / 2^(k-1)
                ≤ y₂.approx k + (1/2^(k-1) + 2 / 2^(k-1)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right h4 (2 / 2^(k-1))
    have : y₁.approx k + 2 / 2^(k-1)
          ≤ y₂.approx k + 3 / 2^(k-1) := by
      rw [one_plus_two_over_pow (k - 1)] at step
      exact step
    exact le_trans h_mid this
  have h_le_to_k :
      x₂.approx (n+1) ≤ y₂.approx k + 1/2^(n+1) + 3 / 2^(k-1) := by
    have step := add_le_add_right h_mid' (1 / 2^(n+1))
    exact le_trans h1 (by simpa [add_comm, add_left_comm, add_assoc] using step)
  have h_to_target :
      y₂.approx k + 1/2^(n+1) + 3 / 2^(k-1)
        ≤ y₂.approx (n+1) + 2/2^(n+1) + 3 / 2^(k-1) := by
    have step1 : y₂.approx k + 1/2^(n+1)
                 ≤ y₂.approx (n+1) + 1/2^(n+1) + 1/2^(n+1) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right h5 (1 / 2^(n+1))
    have step1a : y₂.approx k + 1/2^(n+1)
                 ≤ y₂.approx (n+1) + 2/2^(n+1) := by
      have h_two_halves : 1/2^(n+1) + 1/2^(n+1) = (2:ℚ)/2^(n+1) := by ring
      rw [add_assoc] at step1
      rw [h_two_halves] at step1
      exact step1
    exact Rat.add_le_add_right.mpr step1a
  have h_two : (2 : ℚ) / 2^(n+1) = (1 : ℚ) / 2^n := by
    field_simp [pow_succ]; ring
  calc
    x₂.approx (n+1)
        ≤ y₂.approx (n+1) + 2/2^(n+1) + 3/2^(k-1) := by
          exact (le_trans h_le_to_k h_to_target)
    _ = y₂.approx (n+1) + 1/2^n + 3/2^(k-1) := by
          simp [h_two]
    _ ≤ y₂.approx (n+1) + 1/2^n + ε := by
          have h_err_le : 3 / 2^(k-1) ≤ ε := le_of_lt h_error_bound
          linarith

lemma le_well_defined_backward
    {x₁ x₂ y₁ y₂ : CReal.Pre} (hx : CReal.Pre.Equiv x₁ x₂) (hy : CReal.Pre.Equiv y₁ y₂)
    (h_le : CReal.Pre.le x₂ y₂) : CReal.Pre.le x₁ y₁ :=
  le_well_defined_forward (Pre.equiv_symm hx) (Pre.equiv_symm hy) h_le

/--
The order relation respects equivalence.
This requires an epsilon-delta argument as direct index synchronization accumulates excessive error.
-/
theorem le_well_defined
    {x₁ x₂ y₁ y₂ : CReal.Pre}
    (hx : CReal.Pre.Equiv x₁ x₂) (hy : CReal.Pre.Equiv y₁ y₂) :
    Pre.le x₁ y₁ ↔ Pre.le x₂ y₂ := by
  constructor
  · intro h; exact le_well_defined_forward hx hy h
  · intro h; exact le_well_defined_backward hx hy h

instance : LE CReal := ⟨Quotient.lift₂ Pre.le (fun _ _ _ _ hx hy => propext (le_well_defined hx hy))⟩

/-! ### Proving the Partial Order Axioms -/

theorem le_refl (x : CReal) : x ≤ x := by
  induction x using Quotient.inductionOn
  intro n; simp

theorem le_trans (x y z : CReal) : x ≤ y → y ≤ z → x ≤ z := by
  refine Quot.induction_on₃ x y z (fun x y z => ?_)
  intro hxy hyz n
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨m, hm_bound⟩ := find_index_for_bound (by norm_num : 0 < (2 : ℚ)) hε
  let k := max (n + 1) (m + 1)
  have h_n_le_k : n + 1 ≤ k := le_max_left _ _
  have h_m_le_k : m + 1 ≤ k := le_max_right _ _
  have h_k_sub_1_ge_m : m ≤ k - 1 := Nat.le_sub_of_add_le h_m_le_k
  have h_error_bound : 2 / 2 ^ (k - 1) < ε := by
    have h_pow_bound : (2 : ℚ) ^ m ≤ 2 ^ (k - 1) :=
      (pow_le_pow_iff_right₀ rfl).mpr h_k_sub_1_ge_m
    have h_div_le : (2 : ℚ) / 2 ^ (k - 1) ≤ 2 / 2 ^ m := by
      have hc : 0 < (2 : ℚ) ^ m := pow_pos (by norm_num) m
      exact div_le_div_of_le_left (by norm_num) hc h_pow_bound
    linarith [hm_bound]
  have h_xy_hyp : x.approx k ≤ y.approx k + 1 / 2 ^ (k - 1) := by
    have h_k_ge_1 : 1 ≤ k := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_n_le_k
    simpa [Nat.sub_add_cancel h_k_ge_1] using hxy (k - 1)
  have h_yz_hyp : y.approx k ≤ z.approx k + 1 / 2 ^ (k - 1) := by
    have h_k_ge_1 : 1 ≤ k := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_n_le_k
    simpa [Nat.sub_add_cancel h_k_ge_1] using hyz (k - 1)
  have hx_reg : |x.approx (n + 1) - x.approx k| ≤ 1 / 2 ^ (n + 1) :=
    x.is_regular (n + 1) k h_n_le_k
  have hz_reg : |z.approx (n + 1) - z.approx k| ≤ 1 / 2 ^ (n + 1) :=
    z.is_regular (n + 1) k h_n_le_k
  have h1 : x.approx (n + 1) ≤ x.approx k + 1 / 2 ^ (n + 1) := by
    have h := (abs_sub_le_iff).1 hx_reg
    linarith [h.left]
  have h4 : z.approx k ≤ z.approx (n + 1) + 1 / 2 ^ (n + 1) := by
    have h := (abs_sub_le_iff).1 hz_reg
    linarith [h.right]
  have h_chain :
      x.approx (n + 1) ≤ z.approx (n + 1) + 2 / 2 ^ (n + 1) + 2 / 2 ^ (k - 1) := by
    calc
      x.approx (n + 1)
        ≤ x.approx k + 1 / 2 ^ (n + 1) := h1
      _ ≤ (y.approx k + 1 / 2 ^ (k - 1)) + 1 / 2 ^ (n + 1) := by gcongr
      _ ≤ (z.approx k + 1 / 2 ^ (k - 1) + 1 / 2 ^ (k - 1)) + 1 / 2 ^ (n + 1) := by gcongr
      _ = z.approx k + 2 / 2 ^ (k - 1) + 1 / 2 ^ (n + 1) := by ring_nf
      _ ≤ (z.approx (n + 1) + 1 / 2 ^ (n + 1)) + 2 / 2 ^ (k - 1) + 1 / 2 ^ (n + 1) := by gcongr
      _ = z.approx (n + 1) + 2 / 2 ^ (n + 1) + 2 / 2 ^ (k - 1) := by ring_nf
  have h_two : (2 : ℚ) / 2 ^ (n + 1) = (1 : ℚ) / 2 ^ n := by
    field_simp [pow_succ]; ring
  calc
    x.approx (n + 1)
        ≤ z.approx (n + 1) + 2 / 2 ^ (n + 1) + 2 / 2 ^ (k - 1) := h_chain
    _ = z.approx (n + 1) + 1 / 2 ^ n + 2 / 2 ^ (k - 1) := by simp [h_two]
    _ ≤ z.approx (n + 1) + 1 / 2 ^ n + ε := by
          have : 2 / 2 ^ (k - 1) ≤ ε := le_of_lt h_error_bound
          linarith

theorem le_antisymm (x y : CReal) : x ≤ y → y ≤ x → x = y := by
  refine Quot.induction_on₂ x y (fun x y => ?_)
  intro hxy hyx
  apply Quot.sound
  intro n
  have h_upper : x.approx (n + 1) - y.approx (n + 1) ≤ (1 : ℚ) / 2 ^ n := by
    have hx' : x.approx (n + 1) ≤ (1 : ℚ) / 2 ^ n + y.approx (n + 1) := by
      simpa [add_comm] using (hxy n)
    exact (sub_le_iff_le_add).mpr hx'
  have h_lower : -(1 / 2 ^ n : ℚ) ≤ x.approx (n + 1) - y.approx (n + 1) := by
    have hy' : y.approx (n + 1) ≤ (1 : ℚ) / 2 ^ n + x.approx (n + 1) := by
      simpa [add_comm] using (hyx n)
    have hy_sub : y.approx (n + 1) - x.approx (n + 1) ≤ (1 : ℚ) / 2 ^ n := by simp_all
    have := neg_le_neg hy_sub
    simpa [sub_eq_add_neg] using this
  exact (abs_le.mpr ⟨h_lower, h_upper⟩)

instance : PartialOrder CReal where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

/-! ### Lattice Structure (Max/Min) -/

/-- Maximum of two CReal.Pre. The pointwise definition preserves regularity. -/
protected def Pre.max (x y : CReal.Pre) : CReal.Pre where
  approx := fun n ↦ max (x.approx n) (y.approx n)
  is_regular := by
    intro n m h_le
    have h_max_diff :
        |max (x.approx n) (y.approx n) - max (x.approx m) (y.approx m)|
        ≤ max |x.approx n - x.approx m| |y.approx n - y.approx m| :=
      abs_max_sub_max_le_max (x.approx n) (y.approx n) (x.approx m) (y.approx m)
    have hx := x.is_regular n m h_le
    have hy := y.is_regular n m h_le
    have h_max_to_target :
        max |x.approx n - x.approx m| |y.approx n - y.approx m| ≤ (1 : ℚ) / 2 ^ n :=
      (max_le_iff).2 ⟨hx, hy⟩
    exact _root_.le_trans h_max_diff h_max_to_target

/-- Max respects the equivalence relation. -/
theorem Pre.max_respects_equiv
    {x₁ x₂ y₁ y₂ : CReal.Pre}
    (hx : CReal.Pre.Equiv x₁ x₂) (hy : CReal.Pre.Equiv y₁ y₂) :
    CReal.Pre.Equiv (CReal.Pre.max x₁ y₁) (CReal.Pre.max x₂ y₂) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.max]
  have h_max_diff :
      |max (x₁.approx (n+1)) (y₁.approx (n+1)) -
        max (x₂.approx (n+1)) (y₂.approx (n+1))|
      ≤ max |x₁.approx (n+1) - x₂.approx (n+1)|
            |y₁.approx (n+1) - y₂.approx (n+1)| :=
    abs_max_sub_max_le_max _ _ _ _
  have h_to_target :
      max |x₁.approx (n+1) - x₂.approx (n+1)|
          |y₁.approx (n+1) - y₂.approx (n+1)|
      ≤ (1 : ℚ) / 2 ^ n :=
    (max_le_iff).2 ⟨hx n, hy n⟩
  exact _root_.le_trans h_max_diff h_to_target

/-- Minimum of two CReal.Pre. -/
protected def Pre.min (x y : CReal.Pre) : CReal.Pre where
  approx := fun n ↦ min (x.approx n) (y.approx n)
  is_regular := by
    intro n m h_le
    have h_min_diff :
        |min (x.approx n) (y.approx n) - min (x.approx m) (y.approx m)|
        ≤ max |x.approx n - x.approx m| |y.approx n - y.approx m| :=
      abs_min_sub_min_le_max (x.approx n) (y.approx n) (x.approx m) (y.approx m)
    have hx := x.is_regular n m h_le
    have hy := y.is_regular n m h_le
    have h_max_to_target :
        max |x.approx n - x.approx m| |y.approx n - y.approx m| ≤ (1 : ℚ) / 2 ^ n :=
      (max_le_iff).2 ⟨hx, hy⟩
    exact _root_.le_trans h_min_diff h_max_to_target

/-- Min respects the equivalence relation. -/
theorem Pre.min_respects_equiv
    {x₁ x₂ y₁ y₂ : CReal.Pre}
    (hx : CReal.Pre.Equiv x₁ x₂) (hy : CReal.Pre.Equiv y₁ y₂) :
    CReal.Pre.Equiv (CReal.Pre.min x₁ y₁) (CReal.Pre.min x₂ y₂) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.min]
  have h_min_diff :
      |min (x₁.approx (n+1)) (y₁.approx (n+1)) -
        min (x₂.approx (n+1)) (y₂.approx (n+1))|
      ≤ max |x₁.approx (n+1) - x₂.approx (n+1)|
            |y₁.approx (n+1) - y₂.approx (n+1)| :=
    abs_min_sub_min_le_max _ _ _ _
  have h_to_target :
      max |x₁.approx (n+1) - x₂.approx (n+1)|
          |y₁.approx (n+1) - y₂.approx (n+1)|
      ≤ (1 : ℚ) / 2 ^ n :=
    (max_le_iff).2 ⟨hx n, hy n⟩
  exact _root_.le_trans h_min_diff h_to_target

-- Lattice axioms at the Pre level (proved pointwise via Equiv).
theorem Pre.sup_inf_self_pre (x y : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.max x (CReal.Pre.min x y)) x := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.max, CReal.Pre.min]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp

theorem Pre.inf_sup_self_pre (x y : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.min x (CReal.Pre.max x y)) x := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.max, CReal.Pre.min]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp

theorem Pre.sup_comm_pre (x y : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.max x y) (CReal.Pre.max y x) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.max]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp [max_comm]

theorem Pre.inf_comm_pre (x y : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.min x y) (CReal.Pre.min y x) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.min]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp [min_comm]

theorem Pre.sup_assoc_pre (x y z : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.max (CReal.Pre.max x y) z)
                    (CReal.Pre.max x (CReal.Pre.max y z)) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.max]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp [max_assoc]

theorem Pre.inf_assoc_pre (x y z : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.min (CReal.Pre.min x y) z)
                    (CReal.Pre.min x (CReal.Pre.min y z)) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.min]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp [min_assoc]

/-! ### Constructive Positivity -/

/-- Definition of strict positivity (0 < x) on CReal.Pre (Constructive Definition). -/
protected def Pre.Pos (x : CReal.Pre) : Prop := ∃ N, 1/2^N < x.approx (N+1)

/-- Positivity respects equivalence. -/
theorem Pre.pos_well_defined (x y : CReal.Pre) (hxy : CReal.Pre.Equiv x y) :
  Pre.Pos x ↔ Pre.Pos y := by
  constructor
  · intro h_pos
    obtain ⟨N, hN⟩ := h_pos
    let M := N + 2
    let K := M + 1
    have hN1_le_K : N + 1 ≤ K := by
      dsimp [K, M]; exact Nat.add_le_add_left (by decide : 1 ≤ 3) N
    have h_reg := x.is_regular (N + 1) K hN1_le_K
    have hx := (abs_sub_le_iff).1 h_reg
    have h_xK_ge : x.approx K ≥ x.approx (N + 1) - 1 / 2 ^ (N + 1) := by
      have h := hx.left
      linarith
    have h_sum_N : (1 : ℚ) / 2 ^ (N + 1) + 1 / 2 ^ (N + 1) = 2 / 2 ^ (N + 1) :=
      sum_two_halves N
    have h_two_over_pow : (2 : ℚ) / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ N := by
      field_simp [pow_succ]; ring
    have h_two_halves_to_pred :
        (1 : ℚ) / 2 ^ N = (1 : ℚ) / 2 ^ (N + 1) + 1 / 2 ^ (N + 1) := by
      simp; ring_nf
    have h_eq_half : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ (N + 1) := by
      linarith [h_two_halves_to_pred]
    have h_lt' : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) < x.approx (N + 1) - 1 / 2 ^ (N + 1) := by
      linarith [hN]
    have h_xK_gt_aux : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) < x.approx K :=
      lt_of_lt_of_le h_lt' h_xK_ge
    have h_xK : x.approx K > 1 / 2 ^ (N + 1) := by
      rwa [← h_eq_half]
    have h_equiv_M := hxy M
    have h_equiv := (abs_sub_le_iff).1 h_equiv_M
    have h_y_ge : x.approx K - 1 / 2 ^ M ≤ y.approx K := by
      have hxmy : x.approx (M + 1) - y.approx (M + 1) ≤ 1 / 2 ^ M := h_equiv.left
      have hxmyK : x.approx K - y.approx K ≤ 1 / 2 ^ M := by
        simpa [K] using hxmy
      linarith [hxmyK]
    have step : 1 / 2 ^ (N + 1) - 1 / 2 ^ M < x.approx K - 1 / 2 ^ M := by
      have : 1 / 2 ^ (N + 1) < x.approx K := h_xK
      linarith
    have h_sum_N1 : (1 : ℚ) / 2 ^ (N + 2) + 1 / 2 ^ (N + 2) = 2 / 2 ^ (N + 2) :=
      sum_two_halves (N + 1)
    have h_two_over_pow' : (2 : ℚ) / 2 ^ (N + 2) = (1 : ℚ) / 2 ^ (N + 1) := by
      field_simp [pow_succ]; ring
    have h_eq_add : (1 : ℚ) / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ (N + 2) + 1 / 2 ^ (N + 2) := by
      simp; ring_nf
    have h_sub_eq : (1 : ℚ) / 2 ^ (N + 1) - 1 / 2 ^ M = 1 / 2 ^ M := by
      dsimp [M] at *
      linarith [h_eq_add]
    have h_yK : y.approx K > 1 / 2 ^ M := by
      have : 1 / 2 ^ M < y.approx K := by
        have := lt_of_lt_of_le step h_y_ge
        rwa [h_sub_eq] at this
      simpa using this
    refine ⟨M, ?_⟩
    simpa [K] using h_yK
  · intro h_pos
    obtain ⟨N, hN⟩ := h_pos
    let M := N + 2
    let K := M + 1
    have hN1_le_K : N + 1 ≤ K := by
      dsimp [K, M]; exact Nat.add_le_add_left (by decide : 1 ≤ 3) N
    have h_reg := y.is_regular (N + 1) K hN1_le_K
    have hy := (abs_sub_le_iff).1 h_reg
    have h_yK_ge : y.approx K ≥ y.approx (N + 1) - 1 / 2 ^ (N + 1) := by
      have h := hy.left
      linarith
    have h_sum_N : (1 : ℚ) / 2 ^ (N + 1) + 1 / 2 ^ (N + 1) = 2 / 2 ^ (N + 1) :=
      sum_two_halves N
    have h_two_over_pow : (2 : ℚ) / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ N := by
      field_simp [pow_succ]; ring
    have h_two_halves_to_pred :
        (1 : ℚ) / 2 ^ N = (1 : ℚ) / 2 ^ (N + 1) + 1 / 2 ^ (N + 1) := by
      simp; ring_nf
    have h_eq_half : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ (N + 1) := by
      linarith [h_two_halves_to_pred]
    have h_lt' : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) < y.approx (N + 1) - 1 / 2 ^ (N + 1) := by
      linarith [hN]
    have h_yK_gt_aux : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) < y.approx K :=
      lt_of_lt_of_le h_lt' h_yK_ge
    have h_yK : y.approx K > 1 / 2 ^ (N + 1) := by
      rwa [h_eq_half] at h_yK_gt_aux
    have h_equiv_M := (CReal.Pre.equiv_symm hxy) M
    have h_equiv := (abs_sub_le_iff).1 h_equiv_M
    have h_x_ge : y.approx K - 1 / 2 ^ M ≤ x.approx K := by
      have hyxm : y.approx (M + 1) - x.approx (M + 1) ≤ 1 / 2 ^ M := h_equiv.left
      have hyxmK : y.approx K - x.approx K ≤ 1 / 2 ^ M := by
        simpa [K] using hyxm
      linarith [hyxmK]
    have h_eq_add : (1 : ℚ) / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ (N + 2) + 1 / 2 ^ (N + 2) := by
      field_simp [pow_succ]; ring
    have h_sub_eq : (1 : ℚ) / 2 ^ (N + 1) - 1 / 2 ^ M = 1 / 2 ^ M := by
      dsimp [M] at *
      linarith [h_eq_add]
    have step : 1 / 2 ^ (N + 1) - 1 / 2 ^ M < y.approx K - 1 / 2 ^ M := by
      have : 1 / 2 ^ (N + 1) < y.approx K := h_yK
      linarith
    have h_xK : x.approx K > 1 / 2 ^ M := by
      have t := lt_of_lt_of_le step h_x_ge
      rwa [h_sub_eq] at t
    refine ⟨M, ?_⟩
    simpa [K] using h_xK

/-! ### Lattice Structure and Absolute Value -/

/-- Supremum on CReal, lifted from Pre.max. -/
def sup (x y : CReal) : CReal :=
  Quotient.map₂ Pre.max
    (fun {a₁ a₂} (hx : Pre.Equiv a₁ a₂) {b₁ b₂} (hy : Pre.Equiv b₁ b₂) =>
      Pre.max_respects_equiv hx hy)
    x y

/-- Infimum on CReal, lifted from Pre.min. -/
def inf (x y : CReal) : CReal :=
  Quotient.map₂ Pre.min
    (fun {a₁ a₂} (hx : Pre.Equiv a₁ a₂) {b₁ b₂} (hy : Pre.Equiv b₁ b₂) =>
      Pre.min_respects_equiv hx hy)
    x y

/-- Absolute value on CReal: |x| = sup x (-x). -/
def abs (x : CReal) : CReal := sup x (-x)

instance : Lattice CReal where
  sup := sup
  inf := inf
  le_sup_left := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    intro n
    dsimp [CReal.Pre.le, sup, CReal.Pre.max]
    have h : x.approx (n+1) ≤ max (x.approx (n+1)) (y.approx (n+1)) := le_max_left _ _
    have h_pos : 0 ≤ (1 : ℚ) / 2 ^ n := by positivity
    linarith
  le_sup_right := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    intro n
    dsimp [CReal.Pre.le, sup, CReal.Pre.max]
    have h : y.approx (n+1) ≤ max (x.approx (n+1)) (y.approx (n+1)) := le_max_right _ _
    have h_pos : 0 ≤ (1 : ℚ) / 2 ^ n := by positivity
    linarith
  sup_le := by
    intro a b c hab hac
    refine Quot.induction_on₃ a b c (fun x y z hab hac => ?_) hab hac
    intro n
    dsimp [CReal.Pre.le, sup, CReal.Pre.max]
    have hx := hab n
    have hy := hac n
    have h : max (x.approx (n+1)) (y.approx (n+1)) ≤ z.approx (n+1) + 1/2^n := by
      exact max_le hx hy
    exact h
  inf_le_left := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    intro n
    dsimp [CReal.Pre.le, inf, CReal.Pre.min]
    have h : min (x.approx (n+1)) (y.approx (n+1)) ≤ x.approx (n+1) := min_le_left _ _
    have h_pos : 0 ≤ (1 : ℚ) / 2 ^ n := by positivity
    linarith
  inf_le_right := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    intro n
    dsimp [CReal.Pre.le, inf, CReal.Pre.min]
    have h : min (x.approx (n+1)) (y.approx (n+1)) ≤ y.approx (n+1) := min_le_right _ _
    have h_pos : 0 ≤ (1 : ℚ) / 2 ^ n := by positivity
    linarith
  le_inf := by
    intro a b c hab hac
    refine Quot.induction_on₃ a b c (fun x y z hab hac => ?_) hab hac
    intro n
    dsimp [CReal.Pre.le, inf, CReal.Pre.min]
    have hx := hab n
    have hy := hac n
    have h_min_le : min (y.approx (n+1)) (z.approx (n+1)) ≤ y.approx (n+1) := min_le_left _ _
    have h_min_le' : min (y.approx (n+1)) (z.approx (n+1)) ≤ z.approx (n+1) := min_le_right _ _
    have : x.approx (n+1) ≤ y.approx (n+1) + 1/2^n := hx
    have : x.approx (n+1) ≤ z.approx (n+1) + 1/2^n := hy
    have h_min_bound : x.approx (n+1) ≤ min (y.approx (n+1) + 1/2^n) (z.approx (n+1) + 1/2^n) := by
      exact le_min hx hy
    have h_distrib : min (y.approx (n+1) + 1/2^n) (z.approx (n+1) + 1/2^n) =
                     min (y.approx (n+1)) (z.approx (n+1)) + 1/2^n := by
      exact min_add_add_right (y.approx (n+1)) (z.approx (n+1)) (1/2^n)
    rw [h_distrib] at h_min_bound
    exact h_min_bound

/-! ### Ordered Ring Properties -/

/-- Addition preserves order. -/
theorem add_le_add_left (a b : CReal) (h : a ≤ b) (c : CReal) : c + a ≤ c + b := by
  refine Quot.induction_on₃ a b c (fun a b c h => ?_) h
  intro n
  dsimp [CReal.Pre.le, CReal.Pre.add]
  calc
    c.approx (n+2) + a.approx (n+2)
      ≤ c.approx (n+2) + (b.approx (n+2) + (1 : ℚ) / 2^(n+1)) := by
        gcongr
        exact h (n+1)
    _ = (c.approx (n+2) + b.approx (n+2)) + (1 : ℚ) / 2^(n+1) := by
        ring
    _ ≤ (c.approx (n+2) + b.approx (n+2)) + (1 : ℚ) / 2^n := by
        gcongr
        · simp_all only [Nat.one_le_ofNat]
        · simp_all only [le_add_iff_nonneg_right, zero_le]

theorem zero_le_one : (0 : CReal) ≤ 1 := by
  intro n
  dsimp [CReal.Pre.le, CReal.Pre.zero, CReal.Pre.one]
  positivity

/-- Multiplication of non-negative numbers is non-negative. -/
theorem mul_nonneg (a b : CReal) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  refine' Quot.induction_on₂ a b (fun a b ha hb => _) ha hb
  intro n
  dsimp [CReal.Pre.le, CReal.Pre.zero, CReal.Pre.mul]
  let S := CReal.Pre.mulShift a b
  let K := n + 1 + S
  have hK_pos : 0 < K := by positivity
  have haK_nonneg : 0 ≤ a.approx K + 1 / 2 ^ (K - 1) := by
    simp at ha
    simpa [Nat.sub_add_cancel hK_pos] using ha (K - 1)
  have hbK_nonneg : 0 ≤ b.approx K + 1 / 2 ^ (K - 1) := by
    simp at hb
    simpa [Nat.sub_add_cancel hK_pos] using hb (K - 1)
  have haK : -(1 : ℚ) / 2 ^ (K - 1) ≤ a.approx K := by
    have h' : 0 ≤ a.approx K + (1 : ℚ) / 2 ^ (K - 1) := by
      simpa [add_comm] using haK_nonneg
    have hneg := (neg_le_iff_add_nonneg).2 h'
    simp; ring_nf; simp_all only [add_pos_iff, zero_lt_one, or_true, true_or, Nat.succ_add_sub_one, one_div, inv_pow, K,
      S]
  have hbK : -(1 : ℚ) / 2 ^ (K - 1) ≤ b.approx K := by
    have h' : 0 ≤ b.approx K + (1 : ℚ) / 2 ^ (K - 1) := by
      simpa [add_comm] using hbK_nonneg
    have hneg := (neg_le_iff_add_nonneg).2 h'
    simp; ring_nf; simp_all only [add_pos_iff, zero_lt_one, or_true, true_or, Nat.succ_add_sub_one, one_div, inv_pow, K,
      S]
  let Ba : ℚ := a.cBound
  let Bb : ℚ := b.cBound
  have hS_sum : (a.cBound + b.cBound : ℚ) ≤ 2 ^ S :=
    CReal.Pre.sum_cBound_le_pow_mulShift a b
  have hBa_le_S : Ba ≤ 2 ^ S := by
    have hBb_nonneg : (0 : ℚ) ≤ Bb := Rat.natCast_nonneg
    have : Ba ≤ Ba + Bb := by linarith
    exact this.trans hS_sum
  have hBb_le_S : Bb ≤ 2 ^ S := by
    have hBa_nonneg : (0 : ℚ) ≤ Ba := Rat.natCast_nonneg
    have : Bb ≤ Ba + Bb := by linarith
    exact this.trans hS_sum
  have hK_sub_1 : K - 1 = n + S := by simp [K]
  have h_target_bound (B : ℚ) (hB_le_S : B ≤ 2 ^ S) : B / 2 ^ (n + S) ≤ 1 / 2 ^ n := by
    have h_inv_nonneg : (0 : ℚ) ≤ (1 / 2 ^ (n + S)) := by positivity
    have step := mul_le_mul_of_nonneg_right hB_le_S h_inv_nonneg
    have hstep : B / 2 ^ (n + S) ≤ (2 : ℚ) ^ S / 2 ^ (n + S) := by
      simpa [div_eq_mul_inv] using step
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    have hne1 : (2 : ℚ) ^ S ≠ 0 := pow_ne_zero _ h2
    have hne2 : (2 : ℚ) ^ (n + S) ≠ 0 := pow_ne_zero _ h2
    have h_cancel : (2 : ℚ) ^ S / 2 ^ (n + S) = 1 / 2 ^ n := by
      field_simp [pow_add, hne1, hne2, mul_comm, mul_left_comm, mul_assoc]
      ring_nf
    simpa [h_cancel] using hstep
  rcases le_or_gt 0 (a.approx K) with ha_pos | ha_neg
  rcases le_or_gt 0 (b.approx K) with hb_pos | hb_neg
  · have h_prod_nonneg : 0 ≤ a.approx K * b.approx K := _root_.mul_nonneg ha_pos hb_pos
    have h_half_pow_nonneg : 0 ≤ (1 : ℚ) / 2 ^ n := by
      positivity
    exact add_nonneg h_prod_nonneg h_half_pow_nonneg
  · have h_abs_b : |b.approx K| ≤ 1 / 2 ^ (K - 1) := by
      have : -b.approx K ≤ 1 / 2 ^ (K - 1) := by linarith [hbK]
      simpa [abs_of_neg hb_neg] using this
    have h_abs_a : |a.approx K| ≤ Ba := by
      simpa using a.abs_approx_le_cBound K
    have h_bound : |a.approx K * b.approx K| ≤ Ba / 2 ^ (K - 1) := by
      have hBa_nonneg : (0 : ℚ) ≤ Ba := Rat.natCast_nonneg
      have h_abs_b_nonneg : (0 : ℚ) ≤ |b.approx K| := abs_nonneg _
      have := mul_le_mul h_abs_a h_abs_b h_abs_b_nonneg hBa_nonneg
      simpa [abs_mul, div_eq_mul_inv] using this
    have h_target := h_target_bound Ba hBa_le_S
    have h_left : -(1 / 2 ^ n : ℚ) ≤ -(Ba / 2 ^ (K - 1)) := by
      have := neg_le_neg h_target
      simpa [hK_sub_1] using this
    have h_prod_nonpos : a.approx K * b.approx K ≤ 0 :=
      _root_.mul_nonpos_of_nonneg_of_nonpos ha_pos (le_of_lt hb_neg)
    have h_abs_eq_neg : |a.approx K * b.approx K| = -(a.approx K * b.approx K) :=
      abs_of_nonpos h_prod_nonpos
    have h_right : -(Ba / 2 ^ (K - 1)) ≤ a.approx K * b.approx K := by
      have := neg_le_neg h_bound
      simpa [h_abs_eq_neg] using this
    have h_prod_ge : -(1 / 2 ^ n : ℚ) ≤ a.approx K * b.approx K := h_left.trans h_right
    have h_final : 0 ≤ a.approx K * b.approx K + 1 / 2 ^ n := by
      linarith [h_prod_ge]
    exact h_final
  · have h_abs_a : |a.approx K| ≤ 1 / 2 ^ (K - 1) := by
      have : -a.approx K ≤ 1 / 2 ^ (K - 1) := by linarith [haK]
      simpa [abs_of_neg ha_neg] using this
    have h_abs_b : |b.approx K| ≤ Bb := by
      simpa using b.abs_approx_le_cBound K
    have h_bound : |a.approx K * b.approx K| ≤ Bb / 2 ^ (K - 1) := by
      have hBb_nonneg : (0 : ℚ) ≤ Bb := Rat.natCast_nonneg
      have h_div_nonneg : (0 : ℚ) ≤ 1 / 2 ^ (K - 1) := by
        have hpow : 0 < (2 : ℚ) ^ (K - 1) := pow_pos (by norm_num) _
        exact le_of_lt (div_pos (by norm_num) hpow)
      have := mul_le_mul h_abs_a h_abs_b (by exact abs_nonneg _) h_div_nonneg
      simpa [abs_mul, div_eq_mul_inv, mul_comm] using this
    have h_target := h_target_bound Bb hBb_le_S
    have h_left : -(1 / 2 ^ n : ℚ) ≤ -(Bb / 2 ^ (K - 1)) := by
      have := neg_le_neg h_target
      simpa [hK_sub_1] using this
    have h_right : -(Bb / 2 ^ (K - 1)) ≤ a.approx K * b.approx K :=
      (abs_le.mp h_bound).1
    have h_prod_ge : -(1 / 2 ^ n : ℚ) ≤ a.approx K * b.approx K := h_left.trans h_right
    have h_final : 0 ≤ a.approx K * b.approx K + 1 / 2 ^ n := by
      linarith [h_prod_ge]
    exact h_final

/-! ### Strict Positivity and Final Instance -/

/-- Strict positivity (0 < x) on CReal. Lifted from CReal.Pre.Pos. -/
def Pos (x : CReal) : Prop := Quotient.lift Pre.Pos (fun _ _ h => propext (CReal.Pre.pos_well_defined _ _ h)) x

/-- Pre-level: from Pos (y − x) derive x ≤ y. -/
private lemma pre_pos_sub_implies_le
  (x y : CReal.Pre) (hpos : CReal.Pre.Pos (CReal.Pre.add y (CReal.Pre.neg x))) :
  CReal.Pre.le x y := by
  intro n
  rcases hpos with ⟨N, hN⟩
  let K := max (n + 1) (N + 2)
  have hK_ge_n1 : n + 1 ≤ K := le_max_left _ _
  have hK_ge_N2 : N + 2 ≤ K := le_max_right _ _
  have hy_reg' : |y.approx (N + 2) - y.approx K| ≤ (1 : ℚ) / 2 ^ (N + 2) :=
    y.is_regular (N + 2) K hK_ge_N2
  have hy_reg : |y.approx K - y.approx (N + 2)| ≤ (1 : ℚ) / 2 ^ (N + 2) := by
    simpa [abs_sub_comm] using hy_reg'
  have hx_reg' : |x.approx (N + 2) - x.approx K| ≤ (1 : ℚ) / 2 ^ (N + 2) :=
    x.is_regular (N + 2) K hK_ge_N2
  have hx_reg : |x.approx K - x.approx (N + 2)| ≤ (1 : ℚ) / 2 ^ (N + 2) := by
    simpa [abs_sub_comm] using hx_reg'
  have yK_ge : y.approx K ≥ y.approx (N + 2) - 1 / 2 ^ (N + 2) := by
    have h := (abs_sub_le_iff).1 hy_reg
    linarith [h.right]
  have xK_le : x.approx K ≤ x.approx (N + 2) + 1 / 2 ^ (N + 2) := by
    have h := (abs_sub_le_iff).1 hx_reg
    linarith [h.left]
  have h_gap_at_N2 : (1 : ℚ) / 2 ^ N < y.approx (N + 2) - x.approx (N + 2) := by
    simpa [CReal.Pre.add, CReal.Pre.neg, sub_eq_add_neg,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hN
  have h_half_eq : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) = 1 / 2 ^ (N + 1) := by
    field_simp [pow_succ]; ring
  have h_yxK : (1 : ℚ) / 2 ^ (N + 1) < y.approx K - x.approx K := by
    have h_lower_bound :
        y.approx K - x.approx K
          ≥ y.approx (N + 2) - x.approx (N + 2) - (2 : ℚ) / 2 ^ (N + 2) := by
      have h_neg_x : -x.approx K ≥ -(x.approx (N + 2) + 1 / 2 ^ (N + 2)) := by
        exact neg_le_neg xK_le
      have := add_le_add yK_ge h_neg_x
      have h_rhs_rewrite : (y.approx (N + 2) - 1 / 2 ^ (N + 2)) + -(x.approx (N + 2) + 1 / 2 ^ (N + 2)) =
                           (y.approx (N + 2) - x.approx (N + 2)) - (2 / 2 ^ (N + 2)) := by ring
      rw [h_rhs_rewrite] at this
      linarith [this]
    have h_two_over : (2 : ℚ) / 2 ^ (N + 2) = (1 : ℚ) / 2 ^ (N + 1) := by
      field_simp [pow_succ]; ring
    have h_target : (y.approx (N + 2) - x.approx (N + 2)) - (2 : ℚ) / 2 ^ (N + 2)
                      > 1 / 2 ^ (N + 1) := by
      have : (y.approx (N + 2) - x.approx (N + 2)) - 1 / 2 ^ (N + 1)
               > 1 / 2 ^ N - 1 / 2 ^ (N + 1) := by
        linarith [h_gap_at_N2]
      simp_all only [one_div, Nat.add_max_add_right, add_le_add_iff_right, le_sup_left, Nat.reduceLeDiff, le_sup_right,
        ge_iff_le, tsub_le_iff_right, gt_iff_lt, K]
    exact lt_of_lt_of_le h_target h_lower_bound
  have hx_tail : x.approx (n + 1) ≤ x.approx K + 1 / 2 ^ (n + 1) := by
    have h := x.is_regular (n + 1) K hK_ge_n1
    have h' := (abs_sub_le_iff).1 h
    linarith [h'.left]
  have hy_tail : y.approx K ≤ y.approx (n + 1) + 1 / 2 ^ (n + 1) := by
    have h := y.is_regular (n + 1) K hK_ge_n1
    have h' := (abs_sub_le_iff).1 h
    linarith [h'.right]
  let a : ℚ := 1 / 2 ^ (n + 1)
  let b : ℚ := 1 / 2 ^ (N + 1)
  have hxK_le : x.approx K ≤ y.approx K - b := by
    have : b < y.approx K - x.approx K := h_yxK
    linarith
  have hx_step : x.approx (n + 1) ≤ (y.approx K - b) + a := by
    calc x.approx (n + 1)
      ≤ x.approx K + a := hx_tail
      _ ≤ (y.approx K - b) + a := by linarith [hxK_le]
  have hy_sub1 : y.approx K - b ≤ (y.approx (n + 1) + a) - b := by
    linarith [hy_tail]
  have hy_sub2 : (y.approx K - b) + a ≤ ((y.approx (n + 1) + a) - b) + a := by
    linarith [hy_sub1]
  have hx_step' : x.approx (n + 1) ≤ ((y.approx (n + 1) + a) - b) + a :=
    _root_.le_trans hx_step hy_sub2
  have hb_nonneg : (0 : ℚ) ≤ b := by
    have : 0 < (2 : ℚ) ^ (N + 1) := pow_pos (by norm_num) _
    exact le_of_lt (div_pos (by norm_num) this)
  have drop_sub :
      ((y.approx (n + 1) + a) - b) + a ≤ y.approx (n + 1) + (a + a) := by
    linarith [hb_nonneg]
  have hx_final_sum : x.approx (n + 1) ≤ y.approx (n + 1) + (a + a) :=
    _root_.le_trans hx_step' drop_sub
  have h_two : a + a = (1 : ℚ) / 2 ^ n := by
    dsimp [a]
    field_simp [pow_succ]; ring
  have : x.approx (n + 1) ≤ y.approx (n + 1) + (1 : ℚ) / 2 ^ n := by
    rwa [← h_two]
  exact this

/-- Quotient level: from Pos (y − x) derive x ≤ y. -/
lemma pos_sub_implies_le (x y : CReal) (h : Pos (y - x)) : x ≤ y := by
  refine Quot.induction_on₂ x y (fun x_pre y_pre h_pre => ?_) h
  simpa using pre_pos_sub_implies_le x_pre y_pre h_pre

/-- Pos (y − x) implies x ≠ y. -/
lemma pos_sub_implies_ne (x y : CReal) (h : Pos (y - x)) : x ≠ y := by
  intro hxy
  have : Pos (0 : CReal) := by simpa [hxy, sub_self] using h
  rcases this with this
  dsimp [Pos] at this
  rcases this with ⟨N, hN⟩
  dsimp [CReal.Pre.zero] at hN
  have : 0 < (1 : ℚ) / 2 ^ N := by
    exact div_pos (by norm_num) (pow_pos (by norm_num) _)
  exact (not_lt_of_ge (le_of_lt this)).elim hN

theorem lt_iff_pos (x y : CReal) : x < y ↔ Pos (y - x) := by
  constructor
  · refine Quot.induction_on₂ x y (fun x_pre y_pre => ?_)
    intro hlt

    have h_le : CReal.Pre.le x_pre y_pre := by
      simpa using hlt.1
    have h_not_le : ¬ CReal.Pre.le y_pre x_pre := by
      intro h
      have hyx : (⟦y_pre⟧ : CReal) ≤ ⟦x_pre⟧ := by simpa using h
      exact hlt.2 hyx
    obtain ⟨n, hn⟩ :
        ∃ n : ℕ, ¬ y_pre.approx (n + 1) ≤ x_pre.approx (n + 1) + (1 : ℚ) / 2 ^ n :=
      not_forall.mp h_not_le
    have hn_strict :
        y_pre.approx (n + 1) > x_pre.approx (n + 1) + (1 : ℚ) / 2 ^ n :=
      not_le.mp hn
    let δ : ℚ := (y_pre.approx (n + 1) - x_pre.approx (n + 1)) - (1 : ℚ) / 2 ^ n
    have h_gap_pos : 0 < δ := by
      have : (1 : ℚ) / 2 ^ n < y_pre.approx (n + 1) - x_pre.approx (n + 1) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hn_strict
      exact sub_pos.mpr this
    obtain ⟨M0, hM0⟩ := find_index_for_bound (by norm_num : 0 < (1 : ℚ)) h_gap_pos
    let M := Nat.max M0 n
    have hM_ge_M0 : M0 ≤ M := le_max_left _ _
    have hM_ge_n  : n ≤ M  := le_max_right _ _
    have h_pow_monotone : (1 : ℚ) / 2 ^ M ≤ 1 / 2 ^ M0 := by
      apply one_div_le_one_div_of_le
      · exact pow_pos (by norm_num) _
      · exact (pow_le_pow_iff_right₀ rfl).mpr hM_ge_M0
    have h_small : (1 : ℚ) / 2 ^ M < δ := lt_of_le_of_lt h_pow_monotone hM0
    have h_n1_le_M2 : n + 1 ≤ M + 2 := by
      have : n + 1 ≤ M + 1 := Nat.succ_le_succ hM_ge_n
      exact this.trans (Nat.le_succ (M + 1))
    have hy_reg := y_pre.is_regular (n + 1) (M + 2) h_n1_le_M2
    have hy_pair := (abs_sub_le_iff).1 hy_reg
    have hy_ge : y_pre.approx (M + 2) ≥ y_pre.approx (n + 1) - 1 / 2 ^ (n + 1) := by
      have h := hy_pair.left
      linarith [h]
    have hx_reg := x_pre.is_regular (n + 1) (M + 2) h_n1_le_M2
    have hx_pair := (abs_sub_le_iff).1 hx_reg
    have hx_le : x_pre.approx (M + 2) ≤ x_pre.approx (n + 1) + 1 / 2 ^ (n + 1) := by
      have h := hx_pair.right
      linarith [h]
    have h_diff_lower_aux :
        (y_pre.approx (n + 1) - 1 / 2 ^ (n + 1)) -
            (x_pre.approx (n + 1) + 1 / 2 ^ (n + 1))
          ≤ y_pre.approx (M + 2) - x_pre.approx (M + 2) :=
      sub_le_sub hy_ge hx_le
    have h_rewrite :
        (y_pre.approx (n + 1) - 1 / 2 ^ (n + 1)) -
            (x_pre.approx (n + 1) + 1 / 2 ^ (n + 1))
        = (y_pre.approx (n + 1) - x_pre.approx (n + 1)) -
            (2 : ℚ) / 2 ^ (n + 1) := by
      ring
    have h_two : (2 : ℚ) / 2 ^ (n + 1) = (1 : ℚ) / 2 ^ n := by
      field_simp [pow_succ]; ring
    have h_diff_lower :
        (y_pre.approx (n + 1) - x_pre.approx (n + 1)) - (1 : ℚ) / 2 ^ n
          ≤ y_pre.approx (M + 2) - x_pre.approx (M + 2) := by
      have htmp := h_diff_lower_aux
      rw [h_rewrite, h_two] at htmp
      exact htmp
    dsimp [Pos]
    refine ⟨M, ?_⟩
    dsimp [CReal.Pre.add, CReal.Pre.neg]
    have h_small' :
        (1 : ℚ) / 2 ^ M
          < (y_pre.approx (n + 1) - x_pre.approx (n + 1)) - 1 / 2 ^ n := h_small
    have h_diff_lower' :
        (y_pre.approx (n + 1) - x_pre.approx (n + 1)) - 1 / 2 ^ n
          ≤ y_pre.approx (M + 2) + (-x_pre.approx (M + 2)) := by
      simpa [sub_eq_add_neg] using h_diff_lower
    exact lt_of_lt_of_le h_small' h_diff_lower'
  · intro h
    have h_le : x ≤ y := pos_sub_implies_le x y h
    have h_ne : x ≠ y := pos_sub_implies_ne x y h
    exact lt_of_le_of_ne h_le h_ne

/-- Multiplication of strictly positive numbers is strictly positive. (Constructive Proof) -/
theorem mul_pos (a b : CReal) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  refine Quot.induction_on₂ a b (fun xa xb ha hb => ?_) ha hb
  have ha_pos_pre : CReal.Pre.Pos xa := by
    have ha' : (0 : CReal) < ⟦xa⟧ := ha
    have : Pos (⟦xa⟧ - 0 : CReal) := (lt_iff_pos 0 ⟦xa⟧).mp ha
    have : Pos (⟦xa⟧ : CReal) := by simpa using this
    dsimp [Pos] at this
    simpa using this
  have hb_pos_pre : CReal.Pre.Pos xb := by
    have hb' : (0 : CReal) < ⟦xb⟧ := hb
    have : Pos (⟦xb⟧ - 0 : CReal) := (lt_iff_pos 0 ⟦xb⟧).mp hb
    have : Pos (⟦xb⟧ : CReal) := by simpa using this
    dsimp [Pos] at this
    simpa using this
  rcases ha_pos_pre with ⟨Na, hNa⟩
  rcases hb_pos_pre with ⟨Nb, hNb⟩
  let M := Na + Nb + 2
  let S := CReal.Pre.mulShift xa xb
  let K := M + 1 + S
  have hK_ge_a : K ≥ Na + 1 := by dsimp [K, M]; linarith
  have hK_ge_b : K ≥ Nb + 1 := by dsimp [K, M]; linarith
  have h_a_stable : xa.approx K > 1 / 2 ^ (Na + 1) := by
    have h_reg := xa.is_regular (Na + 1) K hK_ge_a
    have h_reg' : |xa.approx K - xa.approx (Na + 1)| ≤ 1 / 2 ^ (Na + 1) := by
      simpa [abs_sub_comm] using h_reg
    have h_ge : xa.approx K ≥ xa.approx (Na + 1) - 1 / 2 ^ (Na + 1) := by
      have hpair := (abs_sub_le_iff).1 h_reg'
      linarith [hpair.left]
    have h_eq : (1 : ℚ) / 2 ^ Na - 1 / 2 ^ (Na + 1) = 1 / 2 ^ (Na + 1) := by
      field_simp [pow_succ]; ring
    have : (1 : ℚ) / 2 ^ Na - 1 / 2 ^ (Na + 1) < xa.approx K := by
      have : (1 : ℚ) / 2 ^ Na < xa.approx (Na + 1) := hNa
      exact lt_of_lt_of_le (by linarith) h_ge
    simp_all only [one_div, ge_iff_le, tsub_le_iff_right, gt_iff_lt, K, M, S]
  have h_b_stable : xb.approx K > 1 / 2 ^ (Nb + 1) := by
    have h_reg := xb.is_regular (Nb + 1) K hK_ge_b
    have h_reg' : |xb.approx K - xb.approx (Nb + 1)| ≤ 1 / 2 ^ (Nb + 1) := by
      simpa [abs_sub_comm] using h_reg
    have h_ge : xb.approx K ≥ xb.approx (Nb + 1) - 1 / 2 ^ (Nb + 1) := by
      have hpair := (abs_sub_le_iff).1 h_reg'
      linarith [hpair.left]
    have h_eq : (1 : ℚ) / 2 ^ Nb - 1 / 2 ^ (Nb + 1) = 1 / 2 ^ (Nb + 1) := by
      field_simp [pow_succ]; ring
    have : (1 : ℚ) / 2 ^ Nb - 1 / 2 ^ (Nb + 1) < xb.approx K := by
      have : (1 : ℚ) / 2 ^ Nb < xb.approx (Nb + 1) := hNb
      exact lt_of_lt_of_le (by linarith) h_ge
    simp_all only [one_div, ge_iff_le, gt_iff_lt, tsub_le_iff_right, K, M, S]
  have h_prod : xa.approx K * xb.approx K > 1 / 2 ^ M := by
    have h_pos_a : (0 : ℚ) < 1 / 2 ^ (Na + 1) := by
      exact div_pos (by norm_num) (pow_pos (by norm_num) _)
    have h_pos_b : (0 : ℚ) < 1 / 2 ^ (Nb + 1) := by
      exact div_pos (by norm_num) (pow_pos (by norm_num) _)
    have h_nonneg_b : (0 : ℚ) ≤ 1 / 2 ^ (Nb + 1) := le_of_lt h_pos_b
    have h_pos_xa_K : (0 : ℚ) < xa.approx K := lt_trans h_pos_a h_a_stable
    calc
      xa.approx K * xb.approx K
          > (1 / 2 ^ (Na + 1)) * (1 / 2 ^ (Nb + 1)) := by
              exact mul_lt_mul' (le_of_lt h_a_stable) h_b_stable h_nonneg_b h_pos_xa_K
      _ = 1 / 2 ^ (Na + Nb + 2) := by
              have : (1 : ℚ) / 2 ^ (Na + 1) * (1 / 2 ^ (Nb + 1)) = 1 / (2 ^ (Na + 1) * 2 ^ (Nb + 1)) := by
                field_simp
              rw [this]
              congr 1
              rw [← pow_add]
              congr 1
              ring
      _ = 1 / 2 ^ M := by rfl
  have h_pre_pos_prod : CReal.Pre.Pos (CReal.Pre.mul xa xb) := by
    refine ⟨M, ?_⟩
    dsimp [CReal.Pre.mul]
    simpa [K] using h_prod
  have hpos_prod_C : Pos (((⟦xa⟧ : CReal) * ⟦xb⟧) - 0) := by
    have : Pos (⟦CReal.Pre.mul xa xb⟧ : CReal) := by
      dsimp [Pos]; exact h_pre_pos_prod
    simpa [mul_def, sub_zero] using this
  exact (lt_iff_pos (0 : CReal) ((⟦xa⟧ : CReal) * ⟦xb⟧)).2 hpos_prod_C

theorem zero_lt_one : (0 : CReal) < (1 : CReal) := by
  have h : Pos (1 : CReal) := by
    change Pos ⟦CReal.Pre.one⟧
    dsimp [Pos, CReal.Pre.Pos, CReal.Pre.one]
    use 1
    simp
    norm_num
  simpa [sub_zero] using (lt_iff_pos (0 : CReal) (1 : CReal)).2 (by simpa using h)

instance : ZeroLEOneClass CReal where
  zero_le_one := le_of_lt zero_lt_one

instance : Nontrivial CReal :=
  ⟨⟨0, 1, by exact ne_of_lt zero_lt_one⟩⟩


/-- CReal has AddRightMono property. -/
instance : AddRightMono CReal where
  elim a b c h := by
    have h' : a + b ≤ a + c := add_le_add_left b c h a
    rwa [add_comm a b, add_comm a c] at h'


/-
Ordered structure for CReal using the modern mixin style.
We rely on the existing CommRing and PartialOrder instances and provide the
axioms required by IsOrderedRing.
-/
/-- Left multiplication by nonnegative elements preserves order. -/
theorem mul_le_mul_of_nonneg_left' (a b c : CReal) (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  have h_sub_nonneg : 0 ≤ b - a := by
    exact sub_nonneg_of_le h
  have h_prod_nonneg : 0 ≤ c * (b - a) := mul_nonneg c (b - a) hc h_sub_nonneg
  have h_expand : c * (b - a) = c * b - c * a := by ring
  rw [h_expand] at h_prod_nonneg
  exact le_of_sub_nonneg h_prod_nonneg

/-- Right multiplication by nonnegative elements preserves order. -/
theorem mul_le_mul_of_nonneg_right' (a b c : CReal) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [mul_comm a c, mul_comm b c]
  exact mul_le_mul_of_nonneg_left' a b c h hc

instance : IsOrderedRing CReal where
  add_le_add_left := fun a b a_1 c ↦ _root_.add_le_add_left a_1 c
  zero_le_one := zero_le_one
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    -- `PosMulMono` expects the nonneg multiplier first.
    exact mul_le_mul_of_nonneg_left' b c a hbc ha
  mul_le_mul_of_nonneg_right := by
    intro a ha b c hbc
    -- `MulPosMono` expects the nonneg multiplier first.
    exact mul_le_mul_of_nonneg_right' b c a hbc ha

/-! ### Archimedean Property -/

/-- Embedding of natural numbers into CReal.Pre. -/
def Pre.ofNat (n : ℕ) : CReal.Pre where
  approx := fun _ => (n : ℚ)
  is_regular := by intro k m _; simp

instance : NatCast CReal where
  natCast n := ⟦Pre.ofNat n⟧

/-- Pre-level n-fold addition of a pre-real (compatible with `CReal`'s `nsmul`). -/
def Pre.nsmul (n : ℕ) (y : CReal.Pre) : CReal.Pre :=
  Nat.rec CReal.Pre.zero (fun _ acc => CReal.Pre.add acc y) n

@[simp] lemma nsmul_zero (y : CReal.Pre) : CReal.Pre.nsmul 0 y = CReal.Pre.zero := rfl
@[simp] lemma nsmul_succ (n : ℕ) (y : CReal.Pre) :
    CReal.Pre.nsmul (n + 1) y = (CReal.Pre.nsmul n y).add y := rfl

/-- nsmul respects equivalence at the Pre level. -/
lemma nsmul_respects_equiv {y₁ y₂ : CReal.Pre} (h : CReal.Pre.Equiv y₁ y₂) (n : ℕ) :
    CReal.Pre.Equiv (CReal.Pre.nsmul n y₁) (CReal.Pre.nsmul n y₂) := by
  induction n with
  | zero =>
      intro k
      dsimp [CReal.Pre.Equiv, CReal.Pre.nsmul, CReal.Pre.zero]
      simp
  | succ n ih =>
      intro k
      dsimp [CReal.Pre.nsmul, CReal.Pre.add, CReal.Pre.Equiv]
      exact add_respects_equiv ih h k

/-- If on a block of length `n` starting at `m+1` we have a pointwise lower bound
    `δ ≤ y.approx (m+t)` for `t = 1..n`, then `(n • y).approx m ≥ (n:ℚ) * δ`. -/
lemma nsmul_approx_lower_bound
    (y : CReal.Pre) (δ : ℚ) (m n : ℕ)
    (h : ∀ t : ℕ, 1 ≤ t → t ≤ n → δ ≤ y.approx (m + t)) :
    (CReal.Pre.nsmul n y).approx m ≥ (n : ℚ) * δ := by
  induction n generalizing m with
  | zero =>
      simp [CReal.Pre.nsmul, CReal.Pre.zero]
  | succ n ih =>
      have h0 : δ ≤ y.approx (m + 1) := by
        have h1 : 1 ≤ 1 := le_rfl
        have h2 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        simpa using h 1 h1 h2
      have hstep : ∀ t, 1 ≤ t → t ≤ n → δ ≤ y.approx ((m + 1) + t) := by
        intro t ht₁ ht₂
        have h1' : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
        have h2' : t + 1 ≤ n + 1 := Nat.succ_le_succ ht₂
        have := h (t + 1) h1' h2'
        simpa [Nat.add_assoc, add_comm, add_left_comm] using this
      have ih' := ih (m := m + 1) hstep
      dsimp [CReal.Pre.nsmul, CReal.Pre.add] at ih' ⊢
      have h_sum_eq : (n : ℚ) * δ + δ = ((n+1 : ℕ) : ℚ) * δ := by
        have : ((n+1 : ℕ) : ℚ) * δ = (n : ℚ) * δ + δ := by
          simp [Nat.cast_succ, add_mul, one_mul]
        simpa [eq_comm] using this
      calc
        (CReal.Pre.nsmul n y).approx (m + 1) + y.approx (m + 1)
            ≥ (n : ℚ) * δ + δ := add_le_add ih' h0
        _ = ((n+1 : ℕ) : ℚ) * δ := h_sum_eq

/-- From `Pos y` we extract a uniform positive rational lower bound valid for all
    sufficiently large indices. -/
lemma pos_uniform_lower_bound (y : CReal.Pre) (hy : CReal.Pre.Pos y) :
    ∃ K : ℕ, ∃ δ : ℚ, 0 < δ ∧ ∀ m : ℕ, K ≤ m → δ ≤ y.approx m := by
  rcases hy with ⟨N, hN⟩
  let K := N + 2
  let δ : ℚ := 1 / 2 ^ (N + 2)
  have hδ_pos : 0 < δ := by exact div_pos (by norm_num) (pow_pos (by norm_num) _)
  have hN1_le_K : N + 1 ≤ K := by dsimp [K]; exact Nat.le_succ (N + 1)
  have h_reg := y.is_regular (N + 1) K hN1_le_K
  have yK_ge : y.approx K ≥ y.approx (N + 1) - 1 / 2 ^ (N + 1) := by
    have hpair := (abs_sub_le_iff).1 h_reg
    have h1 : y.approx (N + 1) ≤ y.approx K + 1 / 2 ^ (N + 1) := by
      have h := hpair.right
      linarith
    linarith [h1]
  have h_sub_half : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) = 1 / 2 ^ (N + 1) := by
    field_simp [pow_succ]; ring
  have h_half_lt : (1 : ℚ) / 2 ^ (N + 1) < y.approx (N + 1) - 1 / 2 ^ (N + 1) := by
    rw [← h_sub_half]; linarith [hN]
  have yK_gt_half_succ : y.approx K > 1 / 2 ^ (N + 1) :=
    lt_of_lt_of_le h_half_lt yK_ge
  have h_sub_id : (1 : ℚ) / 2 ^ (N + 1) - 1 / 2 ^ K = 1 / 2 ^ (N + 2) := by
    dsimp [K]; field_simp [pow_succ]; ring
  refine ⟨K, δ, hδ_pos, ?_⟩
  intro m hm
  have hreg2 := y.is_regular K m hm
  have hpair2 := (abs_sub_le_iff).1 hreg2
  have ym_ge : y.approx m ≥ y.approx K - 1 / 2 ^ K := by
    have h1 : y.approx K - y.approx m ≤ 1 / 2 ^ K := hpair2.left
    have h2 : - y.approx m ≤ 1 / 2 ^ K - y.approx K := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        sub_le_sub_right h1 (y.approx K)
    have h3 := neg_le_neg h2
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h3
  have h_delta_lt : δ < y.approx K - 1 / 2 ^ K := by
    have haux : (1 / 2 ^ (N + 1) - 1 / 2 ^ K) < (y.approx K - 1 / 2 ^ K) :=
      sub_lt_sub_right yK_gt_half_succ (1 / 2 ^ K)
    simp_all only [one_div, inv_pos, Nat.ofNat_pos, pow_succ_pos, add_le_add_iff_left, Nat.one_le_ofNat, ge_iff_le,
      tsub_le_iff_right, gt_iff_lt, δ, K]
  have hK_sub_le : y.approx K - 1 / 2 ^ K ≤ y.approx m := by
    linarith [ym_ge]
  exact (le_of_lt (lt_of_lt_of_le h_delta_lt hK_sub_le))

/-- Bridge: the quotient value of `n • ⟦y⟧` is represented by `Pre.nsmul n y`. -/
@[simp] lemma nsmul_def (y : CReal.Pre) (n : ℕ) :
    (n : ℕ) • (⟦y⟧ : CReal) = ⟦CReal.Pre.nsmul n y⟧ := by
  induction n with
  | zero =>
      simp [CReal.Pre.nsmul]
      rfl
  | succ n ih =>
      rw [add_nsmul, one_nsmul, ih]
      simp [CReal.Pre.nsmul]
      rfl

/-- A small arithmetic helper: with δ > 0, we have
    B ≤ ⌈B/δ⌉ * δ, and with one more step,
    B ≤ (⌈B/δ⌉ + 1) * δ as well. -/
lemma nat_ceil_mul_lower {B δ : ℚ} (hδ : 0 < δ) :
    B ≤ (Nat.ceil (B / δ) : ℚ) * δ := by
  have h1 : B / δ ≤ (Nat.ceil (B / δ) : ℚ) := by
    exact_mod_cast Nat.le_ceil (B / δ)
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hδ)
  have h3 : B / δ * δ = B := div_mul_cancel₀ B (ne_of_gt hδ)
  rwa [h3] at h2

lemma nat_ceil_succ_mul_lower {B δ : ℚ} (hδ : 0 < δ) :
    B ≤ ((Nat.ceil (B / δ) + 1 : ℕ) : ℚ) * δ := by
  have base := nat_ceil_mul_lower (B := B) (δ := δ) hδ
  have add_step : (Nat.ceil (B / δ) : ℚ) * δ ≤ ((Nat.ceil (B / δ) : ℕ) + 1 : ℕ) * δ := by
    have : (Nat.ceil (B / δ) : ℚ) ≤ ((Nat.ceil (B / δ) : ℕ) + 1 : ℕ) := by norm_cast; exact Nat.le_succ _
    exact mul_le_mul_of_nonneg_right this (le_of_lt hδ)
  exact base.trans add_step

instance : Archimedean CReal := by
  constructor
  intro x y hy
  refine Quot.induction_on₂ x y (fun x_pre y_pre hy => ?_) hy
  have hy_pos_pre : CReal.Pre.Pos y_pre := by
    have : Pos (⟦y_pre⟧ - 0 : CReal) := (lt_iff_pos (0 : CReal) ⟦y_pre⟧).mp hy
    dsimp [Pos] at this
    simpa using this
  obtain ⟨K0, δ, hδ_pos, h_uniform⟩ := pos_uniform_lower_bound y_pre hy_pos_pre
  obtain ⟨K1, hK1⟩ := find_index_for_bound (by norm_num : 0 < (1 : ℚ)) hδ_pos
  let K := Nat.max K0 K1
  have hK0_le_K : K0 ≤ K := le_max_left _ _
  have hK1_le_K : K1 ≤ K := le_max_right _ _
  have h_pow_mono : (1 : ℚ) / 2 ^ K ≤ 1 / 2 ^ K1 := by
    apply one_div_le_one_div_of_le
    · exact pow_pos (by norm_num) _
    · exact (pow_le_pow_iff_right₀ rfl).mpr hK1_le_K
  have h_small_half : (1 : ℚ) / 2 ^ K < δ := lt_of_le_of_lt h_pow_mono hK1
  have h_uniform' : ∀ m : ℕ, K ≤ m → δ ≤ y_pre.approx m := by
    intro m hm
    simp_all only [one_div, le_sup_left, le_sup_right, sup_le_iff, K]
  let Bx : ℕ := x_pre.cBound
  let n := Nat.ceil ((Bx : ℚ) / δ) + 1
  have hBx_base : (Bx : ℚ) ≤ (Nat.ceil ((Bx : ℚ) / δ) : ℚ) * δ :=
    nat_ceil_mul_lower (B := (Bx : ℚ)) (δ := δ) hδ_pos
  have hBx_plus : (Bx : ℚ) + δ ≤ (n : ℚ) * δ := by
    have h_sum : (Nat.ceil ((Bx : ℚ) / δ) : ℚ) * δ + δ
        = ((Nat.ceil ((Bx : ℚ) / δ) + 1 : ℕ) : ℚ) * δ := by
      simp [Nat.cast_add, add_mul, one_mul]
    have := add_le_add_right hBx_base δ
    rw [add_comm] at this
    calc (Bx : ℚ) + δ ≤ (Nat.ceil ((Bx : ℚ) / δ) : ℚ) * δ + δ := by linarith
      _ = ((Nat.ceil ((Bx : ℚ) / δ) + 1 : ℕ) : ℚ) * δ := h_sum
      _ = (n : ℚ) * δ := by rfl
  have h_nsmul_lower :
      (n : ℚ) * δ ≤ (CReal.Pre.nsmul n y_pre).approx (K + 1) := by
    apply nsmul_approx_lower_bound (y := y_pre) (δ := δ) (m := K + 1) (n := n)
    intro t ht₁ _ht₂
    have hK_le : K ≤ (K + 1) + t := by
      exact Nat.le_trans (Nat.le_succ K) (Nat.le_add_right (K + 1) t)
    exact h_uniform' ((K + 1) + t) hK_le
  have h_lt : ⟦x_pre⟧ < (n : ℕ) • (⟦y_pre⟧ : CReal) := by
    rw [nsmul_def]
    apply (lt_iff_pos ⟦x_pre⟧ ⟦CReal.Pre.nsmul n y_pre⟧).mpr
    dsimp [Pos]
    refine ⟨K, ?_⟩
    have hx_abs : |x_pre.approx (K + 2)| ≤ (Bx : ℚ) := by
      simpa using x_pre.abs_approx_le_cBound (K + 2)
    have hx_le : x_pre.approx (K + 2) ≤ (Bx : ℚ) := (abs_le.mp hx_abs).2
    have h_nsmul_lower' : (n : ℚ) * δ ≤ (CReal.Pre.nsmul n y_pre).approx (K + 2) := by
      apply nsmul_approx_lower_bound (y := y_pre) (δ := δ) (m := K + 2) (n := n)
      intro t ht₁ _ht₂
      have hK_le : K ≤ (K + 2) + t := by
        exact Nat.le_trans (Nat.le_add_right K 2) (Nat.le_add_right (K + 2) t)
      exact h_uniform' ((K + 2) + t) hK_le
    have h_delta_le_sub : δ ≤ (n : ℚ) * δ - (Bx : ℚ) := by
      linarith [hBx_plus]
    have h_delta_le_diff : δ ≤ (n : ℚ) * δ - x_pre.approx (K + 2) := by
      have hstep : (n : ℚ) * δ - (Bx : ℚ) ≤ (n : ℚ) * δ - x_pre.approx (K + 2) :=
        sub_le_sub_left hx_le _
      exact _root_.le_trans h_delta_le_sub hstep
    have h_sub_mono :
        (n : ℚ) * δ - x_pre.approx (K + 2)
          ≤ (CReal.Pre.nsmul n y_pre).approx (K + 2) - x_pre.approx (K + 2) :=
      sub_le_sub_right h_nsmul_lower' _
    calc
      (1 : ℚ) / 2 ^ K
          < δ := h_small_half
      _ ≤ (n : ℚ) * δ - x_pre.approx (K + 2) := h_delta_le_diff
      _ ≤ (CReal.Pre.nsmul n y_pre).approx (K + 2) - x_pre.approx (K + 2) := h_sub_mono
      _ = (CReal.Pre.add (CReal.Pre.nsmul n y_pre) (CReal.Pre.neg x_pre)).approx (K + 1) := by
          dsimp [CReal.Pre.add, CReal.Pre.neg]; ring_nf
  use n
  exact le_of_lt h_lt


end CReal
end Computable
