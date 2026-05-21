/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealPre2.Order

namespace Computable
namespace CReal
namespace Pre

/-! ### Inversion (1/x) -/

/--
A pre-real x is separated from zero if we can constructively find a dyadic bound 1/2^N < |x|.
-/
def Separated (x : CReal.Pre) : Prop := ∃ N : ℕ, 1/2^N < |x.approx (N+1)|

/-- Structure to hold the witness data for separation. -/
structure InvWitness (x : CReal.Pre) where
  N : ℕ
  h_bound : 1/2^N < |x.approx (N+1)|

/--
Stability Lemma: The lower bound persists further out in the sequence.
If |x_{N+1}| > 1/2^N, then for K ≥ N+1, |x_K| > 1/2^{N+1}.
-/
lemma inv_witness_stability (x : CReal.Pre) (W : InvWitness x) (K : ℕ) (hK : W.N + 1 ≤ K) :
    1/2^(W.N+1) < |x.approx K| := by
  have h_reg := x.is_regular (W.N+1) K hK
  have h_tri : |x.approx K| ≥ |x.approx (W.N+1)| - |x.approx K - x.approx (W.N+1)| := by
    have h_triangle :
        |x.approx (W.N+1)| ≤ |x.approx (W.N+1) - x.approx K| + |x.approx K| := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (abs_add_le (x.approx (W.N+1) - x.approx K) (x.approx K))
    have h_rewrite : |x.approx (W.N+1) - x.approx K| = |x.approx K - x.approx (W.N+1)| := by
      rw [abs_sub_comm]
    have h_triangle' :
        |x.approx (W.N+1)| ≤ |x.approx K - x.approx (W.N+1)| + |x.approx K| := by
      simpa [h_rewrite]
        using h_triangle
    linarith [h_triangle']
  have h_diff_le : |x.approx K - x.approx (W.N+1)| ≤ 1/2^(W.N+1) := by
    simpa [abs_sub_comm] using h_reg
  calc
    |x.approx K|
        ≥ |x.approx (W.N+1)| - |x.approx K - x.approx (W.N+1)| := h_tri
    _ ≥ |x.approx (W.N+1)| - 1/2^(W.N+1) := by
      exact (sub_le_sub_left h_diff_le _)
    _ > 1/2^W.N - 1/2^(W.N+1) := by
      linarith [W.h_bound]
    _ = 1/2^(W.N+1) := by
      field_simp [pow_succ]; ring

/--
The inverse (reciprocal) of a CReal.Pre, given a witness.
Shift S = 2N+2. (x⁻¹)ₙ := 1 / x_{n + S}.
-/
def inv (x : CReal.Pre) (W : InvWitness x) : CReal.Pre where
  approx := fun n =>
    let N := W.N
    let S := 2*N + 2
    (x.approx (n + S))⁻¹
  is_regular := by
    intro n m hnm
    let N := W.N; let S := 2*N + 2
    let Kn := n + S; let Km := m + S
    have hKnm : Kn ≤ Km := Nat.add_le_add_right hnm S
    have hKn_ge_N1 : N+1 ≤ Kn := by dsimp [Kn, S]; linarith
    have hKm_ge_N1 : N+1 ≤ Km := _root_.le_trans hKn_ge_N1 hKnm
    have h_bound_Kn := x.inv_witness_stability W Kn hKn_ge_N1
    have h_bound_Km := x.inv_witness_stability W Km hKm_ge_N1
    have h_denom : 1/2^S < |x.approx Kn * x.approx Km| := by
      have h_eq : (1 : ℚ) / 2 ^ S = (1 / 2 ^ (N + 1)) * (1 / 2 ^ (N + 1)) := by
        dsimp [S]
        simp [pow_add, one_div, mul_comm, mul_left_comm]
        ring_nf
      set d : ℚ := 1 / 2 ^ (N + 1) with hd
      have hd_pos : 0 < d := by
        have : 0 < (2 : ℚ) ^ (N + 1) := pow_pos (by norm_num) _
        simp [d, one_div, this]
      have h_bound_Kn' : d < |x.approx Kn| := by simpa [d, hd] using h_bound_Kn
      have h_bound_Km' : d < |x.approx Km| := by simpa [d, hd] using h_bound_Km
      have h_bound_Kn_pos : 0 < |x.approx Kn| := lt_trans hd_pos h_bound_Kn'
      have h_bound_Km_pos : 0 < |x.approx Km| := lt_trans hd_pos h_bound_Km'
      have h_step1 : d * d < d * |x.approx Km| := by
        exact (mul_lt_mul_iff_right₀ hd_pos).mpr h_bound_Km'
      have h_step2 : d * |x.approx Km| < |x.approx Kn| * |x.approx Km| := by
        exact (Rat.mul_lt_mul_right h_bound_Km_pos).mpr h_bound_Kn
      have h_trans : d * d < |x.approx Kn| * |x.approx Km| := lt_trans h_step1 h_step2
      have : (1 : ℚ) / 2 ^ S = d * d := by
        simp [h_eq, d, one_div]
      simpa [this, abs_mul, mul_comm, mul_left_comm, mul_assoc]
    have h_num := x.is_regular Kn Km hKnm
    have h_ne_zero_Kn : x.approx Kn ≠ 0 := by
      intro h_eq_zero
      rw [h_eq_zero, abs_zero] at h_bound_Kn
      have h_pos : (0 : ℚ) < 1 / 2 ^ (W.N + 1) := by positivity
      have h_contra := h_pos.trans h_bound_Kn
      exact lt_irrefl 0 h_contra
    have h_ne_zero_Km : x.approx Km ≠ 0 := by
      intro h_eq_zero
      rw [h_eq_zero, abs_zero] at h_bound_Km
      have h_pos : (0 : ℚ) < 1 / 2 ^ (W.N + 1) := by positivity
      have h_contra := h_pos.trans h_bound_Km
      exact lt_irrefl 0 h_contra
    calc |(x.approx Kn)⁻¹ - (x.approx Km)⁻¹|
      = |x.approx Km - x.approx Kn| / |x.approx Kn * x.approx Km| := by
          rw [inv_sub_inv h_ne_zero_Kn h_ne_zero_Km, abs_div, abs_mul, mul_comm]
      _ ≤ (1/2^Kn) / (1/2^S) := by
        have h_num' : |x.approx Km - x.approx Kn| ≤ (1 : ℚ) / 2 ^ Kn := by
          simpa [abs_sub_comm] using h_num
        have h_den_pos : 0 < |x.approx Kn * x.approx Km| := by
          have : 0 < (1 : ℚ) / 2 ^ S := by
            have hpow : 0 < (2 : ℚ) ^ S := pow_pos (by norm_num) _
            exact div_pos (by norm_num) hpow
          exact lt_trans this h_denom
        have step1 :
            |x.approx Km - x.approx Kn| / |x.approx Kn * x.approx Km|
              ≤ (1 : ℚ) / 2 ^ Kn / |x.approx Kn * x.approx Km| :=
          div_le_div_of_le_right h_den_pos h_num'
        have step2 :
            (1 : ℚ) / 2 ^ Kn / |x.approx Kn * x.approx Km|
              ≤ (1 : ℚ) / 2 ^ Kn / ((1 : ℚ) / 2 ^ S) := by
          have ha_nonneg : 0 ≤ (1 : ℚ) / 2 ^ Kn := by
            have hpow : 0 < (2 : ℚ) ^ Kn := pow_pos (by norm_num) _
            exact le_of_lt (div_pos (by norm_num) hpow)
          have hc_pos : 0 < (1 : ℚ) / 2 ^ S := by
            have hpow : 0 < (2 : ℚ) ^ S := pow_pos (by norm_num) _
            exact div_pos (by norm_num) hpow
          exact div_le_div_of_le_left ha_nonneg hc_pos (le_of_lt h_denom)
        exact step1.trans step2
      _ = 1/2^n := by
        dsimp [Kn]; rw [pow_add]; field_simp [pow_ne_zero]

/-- Helper lemma for stability using the maximum witness. -/
lemma stability_at_max_witness (x : CReal.Pre) (W1 W2 : InvWitness x) (Nmax : ℕ) (hNmax : Nmax = max W1.N W2.N) (K : ℕ) (hK : Nmax+1 ≤ K) :
    1/2^(Nmax+1) < |x.approx K| := by
  cases le_total W1.N W2.N with
  | inl h_le => rw [hNmax, max_eq_right h_le] at hK ⊢; exact x.inv_witness_stability W2 K hK
  | inr h_le => rw [hNmax, max_eq_left h_le] at hK ⊢; exact x.inv_witness_stability W1 K hK

/--
The definition of the inverse is independent of the chosen witness.
-/
theorem inv_witness_irrelevant (x : CReal.Pre) (W1 W2 : InvWitness x) :
    CReal.Pre.Equiv (CReal.Pre.inv x W1) (CReal.Pre.inv x W2) := by
  intro n
  apply le_of_forall_pos_le_add
  intro ε hε
  let I1 := CReal.Pre.inv x W1; let I2 := CReal.Pre.inv x W2
  let N1 := W1.N; let N2 := W2.N
  let Nmax := max N1 N2; let Nmin := min N1 N2
  let D := 2 * (Nmax - Nmin)
  have hε3 : 0 < ε / 3 := by exact div_pos hε (by norm_num)
  obtain ⟨K_D, hK_D_bound⟩ : ∃ K, (2^D:ℚ) / 2^K < ε/3 := by
    have one_lt_two : (1 : ℚ) < 2 := by norm_num
    rcases pow_unbounded_of_one_lt ((2^D:ℚ) / (ε/3)) one_lt_two with ⟨K, hK⟩
    use K
    apply (div_lt_iff (pow_pos (by norm_num) _)).mpr
    have hh : (2^D:ℚ) / (ε/3) < 2^K := hK
    have hstep := (div_lt_iff hε3).1 hh
    simpa [mul_comm] using hstep
  let K := max (n+1) K_D
  have h_n1_le_K : n+1 ≤ K := le_max_left _ _
  have h_KD_le_K : K_D ≤ K := le_max_right _ _
  let K1' := K + 2*N1 + 2; let K2' := K + 2*N2 + 2
  have hK1'_ge : N1 + 1 ≤ K1' := by dsimp [K1']; linarith
  have hK2'_ge : N2 + 1 ≤ K2' := by dsimp [K2']; linarith
  have h_bound_K1' := x.inv_witness_stability W1 K1' hK1'_ge
  have h_bound_K2' := x.inv_witness_stability W2 K2' hK2'_ge
  have h_denom' : 1 / 2 ^ (2 * Nmax + 2) < |x.approx K1' * x.approx K2'| := by
    have h_mul_lt :
        (1 : ℚ) / 2 ^ (N1 + 1) * ((1 : ℚ) / 2 ^ (N2 + 1))
          < |x.approx K1'| * |x.approx K2'| := by
      have hposK1 : 0 < |x.approx K1'| := lt_trans (by positivity) h_bound_K1'
      have hposK2 : 0 < |x.approx K2'| := lt_trans (by positivity) h_bound_K2'
      have step1 :
          (1 : ℚ) / 2 ^ (N1 + 1) * (1 / 2 ^ (N2 + 1))
            < |x.approx K1'| * (1 / 2 ^ (N2 + 1)) :=
        mul_lt_mul_of_pos_right h_bound_K1' (by positivity)
      have step2 :
          |x.approx K1'| * (1 / 2 ^ (N2 + 1))
            < |x.approx K1'| * |x.approx K2'| :=
        mul_lt_mul_of_pos_left h_bound_K2' hposK1
      exact step1.trans step2
    have h_eq : (1 : ℚ) / 2 ^ (N1 + 1) * ((1 : ℚ) / 2 ^ (N2 + 1))
                = (1 : ℚ) / 2 ^ (N1 + N2 + 2) := by
      have hden :
          (2 : ℚ) ^ (N1 + 1) * 2 ^ (N2 + 1) = 2 ^ (N1 + N2 + 2) := by
        calc
          (2 : ℚ) ^ (N1 + 1) * 2 ^ (N2 + 1)
              = (2 : ℚ) ^ ((N1 + 1) + (N2 + 1)) := by
                  simpa using (pow_add (2 : ℚ) (N1 + 1) (N2 + 1)).symm
          _ = 2 ^ (N1 + N2 + 2) := by
                  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      calc
        (1 : ℚ) / 2 ^ (N1 + 1) * ((1 : ℚ) / 2 ^ (N2 + 1))
            = (1 : ℚ) / ((2 : ℚ) ^ (N1 + 1) * 2 ^ (N2 + 1)) := by
                field_simp
        _ = (1 : ℚ) / 2 ^ (N1 + N2 + 2) := by simp [hden]
    have h_exp_le : N1 + N2 + 2 ≤ 2 * Nmax + 2 := by
      have h1 : N1 ≤ Nmax := le_max_left _ _
      have h2 : N2 ≤ Nmax := le_max_right _ _
      have hsum : N1 + N2 ≤ Nmax + Nmax := add_le_add h1 h2
      simpa [two_mul] using add_le_add_right hsum 2
    have h_pow_mono :
        (1 : ℚ) / 2 ^ (2 * Nmax + 2) ≤ (1 : ℚ) / 2 ^ (N1 + N2 + 2) := by
      exact one_div_pow_le_one_div_pow_of_le rfl h_exp_le
    have h_right_aux : (1 : ℚ) / 2 ^ (N1 + N2 + 2) < |x.approx K1'| * |x.approx K2'| := by
      simp_all only [div_pos_iff_of_pos_left, Nat.ofNat_pos, le_sup_left, le_sup_right, add_le_add_iff_right, one_div,
        D, Nmax, N1, N2, Nmin, K, K1', K2']
    have h_right : (1 : ℚ) / 2 ^ (N1 + N2 + 2) < |x.approx K1' * x.approx K2'| := by
      simpa [abs_mul] using h_right_aux
    exact lt_of_le_of_lt h_pow_mono h_right
  have h_num' := CReal.abs_approx_diff_le x K1' K2'
  have h_diff_K : |I1.approx K - I2.approx K| < ε/3 := by
    have h_ne_zero_K1' : x.approx K1' ≠ 0 := by
      intro h0
      have : 0 < |x.approx K1'| := lt_trans (by positivity) h_bound_K1'
      have : |x.approx K1'| ≠ 0 := ne_of_gt this
      simp [h0, abs_zero] at this
    have h_ne_zero_K2' : x.approx K2' ≠ 0 := by
      intro h0
      have : 0 < |x.approx K2'| := lt_trans (by positivity) h_bound_K2'
      have : |x.approx K2'| ≠ 0 := ne_of_gt this
      simp [h0, abs_zero] at this
    have h_calc := calc
      |I1.approx K - I2.approx K|
        = |x.approx K2' - x.approx K1'| / |x.approx K1' * x.approx K2'| := by
          dsimp [I1, I2, CReal.Pre.inv]
          change |(x.approx K1')⁻¹ - (x.approx K2')⁻¹|
                = |x.approx K2' - x.approx K1'| / |x.approx K1' * x.approx K2'|
          rw [inv_sub_inv h_ne_zero_K1' h_ne_zero_K2', abs_div]
      _ ≤ (1 / 2 ^ (min K1' K2')) / |x.approx K1' * x.approx K2'| := by
        have h_den_pos : 0 < |x.approx K1' * x.approx K2'| := lt_trans (by positivity) h_denom'
        have h_num'' : |x.approx K2' - x.approx K1'| ≤ 1 / 2 ^ (min K1' K2') := by
          simpa [abs_sub_comm] using h_num'
        exact CReal.div_le_div_of_le (hc := h_den_pos) h_num''
      _ ≤ (1 / 2 ^ (min K1' K2')) / (1 / 2 ^ (2 * Nmax + 2)) := by
        have ha : 0 ≤ (1 : ℚ) / 2 ^ (min K1' K2') := by positivity
        have hc : 0 < (1 : ℚ) / 2 ^ (2 * Nmax + 2) := by positivity
        have h_le : (1 : ℚ) / 2 ^ (2 * Nmax + 2) ≤ |x.approx K1' * x.approx K2'| := le_of_lt h_denom'
        exact CReal.div_le_div_of_le_left (a := (1 : ℚ) / 2 ^ (min K1' K2')) ha hc h_le
    have h_bound_simplified :
        (1 / 2 ^ (min K1' K2')) / (1 / 2 ^ (2 * Nmax + 2)) = (2 ^ D : ℚ) / 2 ^ K := by
      have h_min_K' : min K1' K2' = K + 2 * Nmin + 2 := by
        dsimp [K1', K2', Nmin]
        cases le_total N1 N2 with
        | inl hle =>
            have hmin : min N1 N2 = N1 := by
              exact min_eq_left hle
            have horder : 2 * N1 + 2 ≤ 2 * N2 + 2 := by
              exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hle) 2
            have hmin' : min (K + (2 * N1 + 2)) (K + (2 * N2 + 2)) = K + (2 * N1 + 2) :=
              min_eq_left (Nat.add_le_add_left horder K)
            simpa [hmin, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmin'
        | inr hle =>
            have hmin : min N1 N2 = N2 := by
              exact min_eq_right hle
            have horder : 2 * N2 + 2 ≤ 2 * N1 + 2 := by
              exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hle) 2
            have hmin' : min (K + (2 * N1 + 2)) (K + (2 * N2 + 2)) = K + (2 * N2 + 2) :=
              min_eq_right (Nat.add_le_add_left horder K)
            simpa [hmin, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmin'
      have h_exp_diff : 2 * Nmax + 2 = D + (2 * Nmin + 2) := by
        dsimp [D]
        have hminle : Nmin ≤ Nmax := by
          dsimp [Nmin, Nmax]
          cases le_total N1 N2 with
          | inl h => simpa [min_eq_left h, max_eq_right h]
          | inr h => simpa [min_eq_right h, max_eq_left h]
        have hsplit : Nmax = (Nmax - Nmin) + Nmin := by
          simpa using (Nat.sub_add_cancel hminle).symm
        have h := congrArg (fun t => 2 * t + 2) hsplit
        calc
          2 * Nmax + 2 = 2 * ((Nmax - Nmin) + Nmin) + 2 := by
            simpa using h
          _ = (2 * (Nmax - Nmin) + 2 * Nmin) + 2 := by
            simp [Nat.mul_add]
          _ = 2 * (Nmax - Nmin) + (2 * Nmin + 2) := by
            ac_rfl
      calc
        (1 / 2 ^ (min K1' K2')) / (1 / 2 ^ (2 * Nmax + 2))
            = (1 / 2 ^ (K + 2 * Nmin + 2)) / (1 / 2 ^ (D + (2 * Nmin + 2))) := by
                simp [h_min_K', h_exp_diff]
        _ = (2 : ℚ) ^ (D + (2 * Nmin + 2)) / (2 : ℚ) ^ (K + 2 * Nmin + 2) := by
              simp [div_eq_mul_inv, mul_comm]
        _ = ((2 : ℚ) ^ D * (2 : ℚ) ^ (2 * Nmin + 2)) /
            ((2 : ℚ) ^ K * (2 : ℚ) ^ (2 * Nmin + 2)) := by
              simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
        _ = (2 : ℚ) ^ D / (2 : ℚ) ^ K := by
              have hpow_ne : (2 : ℚ) ^ (2 * Nmin + 2) ≠ 0 := pow_ne_zero _ (by norm_num)
              field_simp [hpow_ne]
    rw [h_bound_simplified] at h_calc
    have h_K_bound : (2^D:ℚ) / 2^K ≤ (2^D:ℚ) / 2^K_D := by
      have ha : 0 ≤ (2 ^ D : ℚ) := by positivity
      have hc : 0 < (2 : ℚ) ^ K_D := by positivity
      have h_le_pow : (2 : ℚ) ^ K_D ≤ 2 ^ K :=
        (pow_le_pow_iff_right₀ rfl).mpr h_KD_le_K
      exact CReal.div_le_div_of_le_left (a := (2 ^ D : ℚ)) ha hc h_le_pow
    linarith [h_calc, h_K_bound, hK_D_bound]
  have h_reg1 := I1.is_regular (n+1) K h_n1_le_K
  have h_reg2 := I2.is_regular (n+1) K h_n1_le_K
  have h_diff_K_le : |I1.approx K - I2.approx K| ≤ ε/3 := le_of_lt h_diff_K
  have h_step1 :
      |I1.approx (n+1) - I2.approx (n+1)|
        ≤ |I1.approx (n+1) - I1.approx K| + |I1.approx K - I2.approx (n+1)| :=
    abs_sub_le _ _ _
  have h_step2 :
      |I1.approx K - I2.approx (n+1)|
        ≤ |I1.approx K - I2.approx K| + |I2.approx K - I2.approx (n+1)| := by
    simpa using abs_sub_le (I1.approx K) (I2.approx K) (I2.approx (n+1))
  have h_tri :
      |I1.approx (n+1) - I2.approx (n+1)|
        ≤ |I1.approx (n+1) - I1.approx K|
          + (|I1.approx K - I2.approx K| + |I2.approx K - I2.approx (n+1)|) := by
    exact _root_.le_trans h_step1 (Rat.add_le_add_left.mpr h_step2)
  have h_reg2' : |I2.approx K - I2.approx (n+1)| ≤ 1 / 2 ^ (n+1) := by
    simpa [abs_sub_comm] using h_reg2
  have h_final_bound :
      |I1.approx (n+1) - I2.approx (n+1)|
        ≤ 1/2^(n+1) + (ε/3 + 1/2^(n+1)) := by
    apply _root_.le_trans h_tri
    gcongr
  calc
    |I1.approx (n+1) - I2.approx (n+1)|
      ≤ 1/2^(n+1) + (ε/3 + 1/2^(n+1)) := h_final_bound
    _ = 1/2^n + ε/3 := by field_simp [pow_succ]; ring
    _ ≤ 1/2^n + ε := by gcongr; linarith

lemma abs_lower_of_abs_sub_le {a b t : ℚ} (h : |a - b| ≤ t) :
    |b| ≥ |a| - t := by
  have h' : -|b - a| ≤ |b| - |a| :=
    (abs_le.mp (abs_abs_sub_abs_le_abs_sub b a)).1
  have h0 : |a| - |b - a| ≤ |b| := by
    have := _root_.add_le_add_right h' |a|
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hba : |b - a| ≤ t := by simpa [abs_sub_comm] using h
  have hmono' : |a| - t ≤ |a| - |b - a| := by
    have := neg_le_neg hba
    have := _root_.add_le_add_left this |a|
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  exact (_root_.le_trans hmono' h0)

lemma abs_lower_via_equiv_pos
    {x y : CReal.Pre} (hxy : CReal.Pre.Equiv x y) {K : ℕ} (hK : 0 < K) :
    |y.approx K| ≥ |x.approx K| - 1 / 2 ^ (K - 1) := by
  have hx : |x.approx K - y.approx K| ≤ (1 : ℚ) / 2 ^ (K - 1) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hK)] using hxy (K - 1)
  exact abs_lower_of_abs_sub_le hx

lemma separated_of_equiv_left
    {x y : CReal.Pre} (hxy : CReal.Pre.Equiv x y) (hx : Separated x) : Separated y := by
  rcases hx with ⟨N, hN⟩
  let Wx : InvWitness x := ⟨N, hN⟩
  let K := N + 3
  have hK : 0 < K := by exact Nat.succ_pos _
  have hxK : (1 : ℚ) / 2 ^ (N + 1) < |x.approx K| := by
    have hK_ge : Wx.N + 1 ≤ K := by
      dsimp [K]
      have : N + 1 ≤ N + 3 := Nat.add_le_add_left (by decide : 1 ≤ 3) N
      simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, add_le_add_iff_left, Nat.one_le_ofNat, K,
        Wx]
    exact inv_witness_stability x Wx K hK_ge
  have hyK_lower : |y.approx K| ≥ |x.approx K| - (1 : ℚ) / 2 ^ (K - 1) :=
    abs_lower_via_equiv_pos hxy hK
  have hdiff : (1 : ℚ) / 2 ^ (N + 1) - 1 / 2 ^ (N + 2) = 1 / 2 ^ (N + 2) := by
    simpa using CReal.two_halves_to_succ_sub N
  have hKpred : K - 1 = N + 2 := by
    simp [K]
  have : (1 : ℚ) / 2 ^ (N + 2) < |x.approx K| - 1 / 2 ^ (N + 2) := by
    have hstep := sub_lt_sub_right hxK ((1 : ℚ) / 2 ^ (N + 2))
    simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, one_div, Nat.add_one_sub_one, ge_iff_le,
      tsub_le_iff_right, K]
  have hyK : (1 : ℚ) / 2 ^ (N + 2) < |y.approx K| := by
    have hyK' : |x.approx K| - (1 : ℚ) / 2 ^ (N + 2) ≤ |y.approx K| := by
      simpa [hKpred] using hyK_lower
    exact lt_of_lt_of_le this hyK'
  refine ⟨N + 2, ?_⟩
  simpa [K, Nat.add_assoc] using hyK

-- The reverse direction follows by symmetry of Equiv.
lemma separated_of_equiv_right
    {x y : CReal.Pre} (hxy : CReal.Pre.Equiv x y) (hy : Separated y) : Separated x :=
  separated_of_equiv_left (CReal.Pre.equiv_symm hxy) hy

-- Now the main equivalence is just two lines:
theorem separated_well_defined (x y : CReal.Pre) (hxy : CReal.Pre.Equiv x y) :
  CReal.Pre.Separated x ↔ CReal.Pre.Separated y := by
  constructor
  · exact CReal.Pre.separated_of_equiv_left hxy
  · exact CReal.Pre.separated_of_equiv_right hxy

/-- Helper to construct a witness for y based on a witness for x, assuming x ≈ y. -/
def transfer_witness (x y : CReal.Pre) (hxy : CReal.Pre.Equiv x y) (Wx : InvWitness x) : InvWitness y :=
  let N := Wx.N
  let M := N + 2
  let K := N + 3
  have hK_ge : Wx.N + 1 ≤ K := by
    dsimp [K]
    exact Nat.add_le_add_left (by decide : 1 ≤ 3) N
  have h_xK : (1 : ℚ) / 2 ^ (N + 1) < |x.approx K| :=
    inv_witness_stability x Wx K hK_ge
  have hK_pos : 0 < K := Nat.succ_pos _
  have hyK_lower : |y.approx K| ≥ |x.approx K| - (1 : ℚ) / 2 ^ (K - 1) :=
    abs_lower_via_equiv_pos hxy hK_pos
  have hKpred : K - 1 = N + 2 := by simp [K]
  have hdiff : (1 : ℚ) / 2 ^ (N + 1) - 1 / 2 ^ (N + 2) = 1 / 2 ^ (N + 2) := by
    simpa using CReal.two_halves_to_succ_sub N
  have h_strict : (1 : ℚ) / 2 ^ (N + 2) < |x.approx K| - 1 / 2 ^ (N + 2) := by
    have := sub_lt_sub_right h_xK ((1 : ℚ) / 2 ^ (N + 2))
    simp_all only [add_le_add_iff_left, Nat.one_le_ofNat, one_div, lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos,
      or_true, Nat.add_one_sub_one, ge_iff_le, tsub_le_iff_right, K, N]
  have h_mono : |x.approx K| - (1 : ℚ) / 2 ^ (N + 2) ≤ |y.approx K| := by
    simpa [hKpred] using hyK_lower
  have hyK : (1 : ℚ) / 2 ^ (N + 2) < |y.approx K| := lt_of_lt_of_le h_strict h_mono
  ⟨M, by
    simpa [M, K, Nat.add_assoc] using hyK⟩

namespace CReal.Pre

-- A convenient algebraic identity for inverse differences, with absolute values.
lemma inv_abs_diff_formula (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0) :
  |r⁻¹ - s⁻¹| = |s - r| / |r*s| := by
  rw [inv_sub_inv hr hs, abs_div, abs_mul, mul_comm]

-- If |r - s| ≤ α and we have positive lower bounds Lr ≤ |r|, Ls ≤ |s|,
-- then the inverse difference is controlled by α / (Lr*Ls).
lemma inv_sub_inv_bound_of_bounds {r s Lr Ls α : ℚ}
  (hα : |r - s| ≤ α)
  (hLr_pos : 0 < Lr) (hLs_pos : 0 < Ls)
  (hLr : Lr ≤ |r|) (hLs : Ls ≤ |s|) :
  |r⁻¹ - s⁻¹| ≤ α / (Lr * Ls) := by
  have hr_ne : r ≠ 0 := by
    have : 0 < |r| := lt_of_lt_of_le hLr_pos hLr
    exact (abs_ne_zero.mp (ne_of_gt this))
  have hs_ne : s ≠ 0 := by
    have : 0 < |s| := lt_of_lt_of_le hLs_pos hLs
    exact (abs_ne_zero.mp (ne_of_gt this))
  have hα_nn : 0 ≤ α := (abs_nonneg _).trans hα
  have hden_pos : 0 < |r * s| := by
    have hr : 0 < |r| := lt_of_lt_of_le hLr_pos hLr
    have hs : 0 < |s| := lt_of_lt_of_le hLs_pos hLs
    simpa [abs_mul] using (_root_.mul_pos hr hs)
  have hden_ge : (Lr * Ls) ≤ |r * s| := by
    have hLs_nn : 0 ≤ Ls := le_of_lt hLs_pos
    have h1 : Lr * Ls ≤ |r| * Ls := by
      exact mul_le_mul_of_nonneg_right hLr hLs_nn
    have h2 : |r| * Ls ≤ |r| * |s| := by
      exact mul_le_mul_of_nonneg_left hLs (abs_nonneg _)
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using h1.trans h2
  have hα' : |s - r| ≤ α := by simpa [abs_sub_comm] using hα
  calc
    |r⁻¹ - s⁻¹|
        = |s - r| / |r * s| := inv_abs_diff_formula r s hr_ne hs_ne
    _ ≤ α / |r * s| := by
      exact div_le_div_of_le_right hden_pos hα'
    _ ≤ α / (Lr * Ls) := by
      exact div_le_div_of_le_left hα_nn (_root_.mul_pos hLr_pos hLs_pos) hden_ge

-- Extract a non-strict lower bound from stability (witness)
lemma abs_lower_from_witness (x : CReal.Pre) (W : InvWitness x) {K : ℕ} (hK : W.N + 1 ≤ K) :
  (1 : ℚ) / 2 ^ (W.N + 1) ≤ |x.approx K| :=
  le_of_lt (inv_witness_stability x W K hK)

-- Equivalence bound at a single index K (needs K > 0 to rewrite K = (K-1)+1)
lemma equiv_at_index_bound {x y : CReal.Pre}
  (hxy : CReal.Pre.Equiv x y) {K : ℕ} (hKpos : 0 < K) :
  |x.approx K - y.approx K| ≤ (1 : ℚ) / 2 ^ (K - 1) := by
  have h : K - 1 + 1 = K := Nat.sub_add_cancel (Nat.succ_le_of_lt hKpos)
  simpa [h] using hxy (K - 1)

-- “Same-index” inverse bound from Equiv + denominator lower bounds.
lemma inv_same_index_bound_of_equiv
  {x y : CReal.Pre} (hxy : CReal.Pre.Equiv x y)
  {K : ℕ} {Lx Ly : ℚ}
  (hKpos : 0 < K)
  (hLx_pos : 0 < Lx) (hLy_pos : 0 < Ly)
  (hLx : Lx ≤ |x.approx K|) (hLy : Ly ≤ |y.approx K|) :
  |(x.approx K)⁻¹ - (y.approx K)⁻¹| ≤ ((1 : ℚ) / 2 ^ (K - 1)) / (Lx * Ly) := by
  have hα := equiv_at_index_bound (x := x) (y := y) hxy hKpos
  exact inv_sub_inv_bound_of_bounds (r := x.approx K) (s := y.approx K)
    (Lr := Lx) (Ls := Ly) (α := (1 : ℚ) / 2 ^ (K - 1))
    hα hLx_pos hLy_pos hLx hLy

-- “Two-index” inverse bound for a single pre-real using regularity + lower bounds.
lemma inv_two_index_bound_of_regular_and_bounds
  (x : CReal.Pre) (K K' : ℕ)
  {L : ℚ} (hL_pos : 0 < L)
  (hL_K  : L ≤ |x.approx K|)
  (hL_K' : L ≤ |x.approx K'|)
  (h_reg : |x.approx K - x.approx K'| ≤ (1 : ℚ) / 2 ^ (min K K')) :
  |(x.approx K)⁻¹ - (x.approx K')⁻¹| ≤ ((1 : ℚ) / 2 ^ (min K K')) / (L * L) := by
  exact inv_sub_inv_bound_of_bounds (r := x.approx K) (s := x.approx K')
    (Lr := L) (Ls := L) (α := (1 : ℚ) / 2 ^ (min K K'))
    h_reg hL_pos hL_pos hL_K hL_K'

-- algebra helpers for dyadic powers
lemma one_div_pow_mul_one_div_pow (a b : ℕ) :
  (1 : ℚ) / 2 ^ a * (1 / 2 ^ b) = (1 : ℚ) / 2 ^ (a + b) := by
  field_simp [div_eq_mul_inv, pow_add, mul_comm, mul_left_comm, mul_assoc]; exact pow_add 2 a b

lemma div_one_div_pow_simp (a b : ℕ) :
  ((1 : ℚ) / 2 ^ (a + b)) / ((1 : ℚ) / 2 ^ b) = (1 : ℚ) / 2 ^ a := by
  field_simp [div_eq_mul_inv, pow_add, mul_comm, mul_left_comm, mul_assoc]; ring_nf

theorem inv_respects_equiv
    (x y : CReal.Pre)
    (hxy : CReal.Pre.Equiv x y)
    (Wx : CReal.Pre.InvWitness x) (Wy : CReal.Pre.InvWitness y) :
    CReal.Pre.Equiv (CReal.Pre.inv x Wx) (CReal.Pre.inv y Wy) := by
  let W'y := CReal.Pre.transfer_witness x y hxy Wx
  have h_irrel_y : CReal.Pre.Equiv (CReal.Pre.inv y Wy) (CReal.Pre.inv y W'y) :=
    CReal.Pre.inv_witness_irrelevant y Wy W'y
  have h_core : CReal.Pre.Equiv (CReal.Pre.inv x Wx) (CReal.Pre.inv y W'y) := by
    intro n
    let Nx := Wx.N
    let L  : ℚ := (1 : ℚ) / 2 ^ (Nx + 1)
    let k  := n + 1
    let Sx := 2 * Nx + 2
    let Sy := 2 * (Nx + 2) + 2
    let Kx := k + Sx
    let Ky := k + Sy
    have hKx_le_Ky : Kx ≤ Ky := by
      dsimp [Kx, Ky, Sx, Sy, k]
      have : 2 * Nx + 2 ≤ 2 * Nx + 6 := by
        simp [Nat.add_assoc, two_mul]
      exact Nat.add_le_add_left this (n + 1)
    have hL_Kx : L ≤ |x.approx Kx| := by
      have : Nx + 1 ≤ Kx := by
        dsimp [Kx, Sx, k]
        have hNx_le_2Nx : Nx ≤ 2 * Nx := by
          simpa [Nat.mul_comm, one_mul] using
            Nat.mul_le_mul_left Nx (by decide : 1 ≤ 2)
        have hNx1_le_2Nx1 : Nx + 1 ≤ 2 * Nx + 1 :=
          Nat.add_le_add_right hNx_le_2Nx 1
        have hNx1_le_2Nx2 : Nx + 1 ≤ 2 * Nx + 2 :=
          _root_.le_trans hNx1_le_2Nx1 (Nat.le_succ (2 * Nx + 1))
        exact _root_.le_trans hNx1_le_2Nx2 (Nat.le_add_left _ _)
      simpa [L] using CReal.Pre.abs_lower_from_witness x Wx this
    have hL_Ky_x : L ≤ |x.approx Ky| := by
      have : Nx + 1 ≤ Ky := by
        dsimp [Ky, Sy, k]
        have h1 : Nx + 1 ≤ Nx + 5 :=
          Nat.add_le_add_left (by decide : 1 ≤ 5) Nx
        have h2 : Nx + 5 ≤ 2 * Nx + 6 := by
          have hNx_le_2Nx : Nx ≤ 2 * Nx := by
            simpa [one_mul, Nat.mul_comm] using
              Nat.mul_le_mul_left Nx (by decide : 1 ≤ 2)
          have h2' : Nx + 5 ≤ 2 * Nx + 5 := Nat.add_le_add_right hNx_le_2Nx 5
          exact _root_.le_trans h2' (Nat.le_succ _)
        have hNxSy : Nx + 1 ≤ Sy := by
          dsimp [Sy]; exact _root_.le_trans h1 h2
        have hSy_le : Sy ≤ k + Sy := Nat.le_add_left _ _
        exact _root_.le_trans hNxSy hSy_le
      simpa [L] using CReal.Pre.abs_lower_from_witness x Wx this
    let Ly : ℚ := (1 : ℚ) / 2 ^ (Nx + 3)
    have hLy_Ky : Ly ≤ |y.approx Ky| := by
      have hWyN : W'y.N = Nx + 2 := by
        dsimp [W'y, CReal.Pre.transfer_witness]
      have hWyN_le : W'y.N + 1 ≤ Ky := by
        have h1 : Nx + 3 ≤ 2 * Nx + 6 := by
          have hNx_le_2Nx : Nx ≤ 2 * Nx := by
            have h := Nat.mul_le_mul_left Nx (by decide : 1 ≤ 2)
            simpa [Nat.mul_comm, Nat.one_mul] using h
          have h3_le_6 : 3 ≤ 6 := by decide
          exact add_le_add hNx_le_2Nx h3_le_6
        have h2 : 2 * Nx + 6 ≤ k + (2 * Nx + 6) := Nat.le_add_left _ _
        have hKy : Ky = k + (2 * Nx + 6) := by
          dsimp [Ky, Sy, k]; simp [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        have : Nx + 3 ≤ Ky := by simpa [hKy] using (Nat.le_add_left_of_le h1)
        simpa [hWyN] using this
      have := CReal.Pre.abs_lower_from_witness y W'y (K := Ky) (hK := hWyN_le)
      simpa [Ly, hWyN] using this
    have h_reg_x : |x.approx Kx - x.approx Ky| ≤ (1 : ℚ) / 2 ^ (min Kx Ky) := by
      simpa [abs_sub_comm] using CReal.abs_approx_diff_le x Kx Ky
    have h_term1 :=
      CReal.Pre.inv_two_index_bound_of_regular_and_bounds x Kx Ky
        (hL_pos := by positivity) hL_Kx hL_Ky_x h_reg_x
    have h_term1' : |(x.approx Kx)⁻¹ - (x.approx Ky)⁻¹| ≤ (1 : ℚ) / 2 ^ k := by
      have hmin : min Kx Ky = Kx := min_eq_left hKx_le_Ky
      have hLL : L * L = (1 : ℚ) / 2 ^ (2 * Nx + 2) := by
        simpa [L, two_mul, pow_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, div_eq_mul_inv] using
          CReal.Pre.one_div_pow_mul_one_div_pow (Nx + 1) (Nx + 1)
      have hcore :
          |(x.approx Kx)⁻¹ - (x.approx Ky)⁻¹|
            ≤ ((1 : ℚ) / 2 ^ Kx) / ((1 : ℚ) / 2 ^ (2 * Nx + 2)) := by
        simpa [hmin, hLL] using h_term1
      have hKx : Kx = k + (2 * Nx + 2) := by
        dsimp [Kx, Sx, k]
      have hsimps :
          ((1 : ℚ) / 2 ^ Kx) / ((1 : ℚ) / 2 ^ (2 * Nx + 2)) = (1 : ℚ) / 2 ^ k := by
        simpa [hKx] using CReal.Pre.div_one_div_pow_simp k (2 * Nx + 2)
      simp_all only [add_le_add_iff_left, add_le_add_iff_right, Nat.ofNat_pos, mul_le_mul_iff_right₀,
        le_add_iff_nonneg_right, zero_le, one_div, inf_of_le_left, div_inv_eq_mul, ge_iff_le,
        W'y, Kx, k, Sx, Nx, Ky, Sy, L, Ly]
    have hKpos : 0 < Ky := by dsimp [Ky]; exact Nat.succ_pos _
    have h_term2 :=
      CReal.Pre.inv_same_index_bound_of_equiv (x := x) (y := y) hxy
        (K := Ky) (Lx := L) (Ly := Ly)
        (hKpos := by exact Nat.succ_pos _) (hLx_pos := by positivity) (hLy_pos := by positivity)
        (hLx := hL_Ky_x) (hLy := hLy_Ky)
    have h_term2' : |(x.approx Ky)⁻¹ - (y.approx Ky)⁻¹| ≤ (1 : ℚ) / 2 ^ (n + 2) := by
      have hden : L * Ly = (1 : ℚ) / 2 ^ (2 * Nx + 4) := by
        simpa [L, Ly, two_mul, pow_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, div_eq_mul_inv] using
          CReal.Pre.one_div_pow_mul_one_div_pow (Nx + 1) (Nx + 3)
      have hKy_eq : Ky = k + (2 * Nx + 6) := by
        dsimp [Ky, Sy, k]; simp [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hKy_pred : Ky - 1 = k + (2 * Nx + 5) := by
        have : Ky = (k + (2 * Nx + 5)) + 1 := by
          rfl
        simp [this]
      have hdiv :
          (1 : ℚ) / 2 ^ (Ky - 1) / (L * Ly) = (1 : ℚ) / 2 ^ (k + 1) := by
        have : (Ky - 1) = (k + 1) + (2 * Nx + 4) := by
          simp +arith [*]
        simpa [this, hden] using CReal.Pre.div_one_div_pow_simp (k + 1) (2 * Nx + 4)
      have hk : k + 1 = n + 2 := by simp [k]
      have : |(x.approx Ky)⁻¹ - (y.approx Ky)⁻¹| ≤ (1 : ℚ) / 2 ^ (k + 1) := by
        simp_all only [add_le_add_iff_left, add_le_add_iff_right, Nat.ofNat_pos, mul_le_mul_iff_right₀,
          le_add_iff_nonneg_right, zero_le, one_div, inf_of_le_left, add_pos_iff, _root_.zero_lt_one, or_true,
          mul_pos_iff_of_pos_left, or_self, Nat.add_succ_sub_one, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
          div_inv_eq_mul, W'y, Kx, k, Sx, Nx, Ky, Sy, L, Ly]
      simpa [hk] using this
    have := calc
      |(x.approx Kx)⁻¹ - (y.approx Ky)⁻¹|
          ≤ |(x.approx Kx)⁻¹ - (x.approx Ky)⁻¹| +
            |(x.approx Ky)⁻¹ - (y.approx Ky)⁻¹| := by
              simpa using abs_sub_le ((x.approx Kx)⁻¹) ((x.approx Ky)⁻¹) ((y.approx Ky)⁻¹)
      _ ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ (n + 2) := add_le_add h_term1' h_term2'
      _ ≤ (1 : ℚ) / 2 ^ n := by
            have hk : k = n + 1 := rfl
            have hmono : (1 : ℚ) / 2 ^ (n + 2) ≤ (1 : ℚ) / 2 ^ (n + 1) := by
              simpa using inv_pow_antitone_succ (n + 1)
            calc
              (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ (n + 2)
                  = (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2) := by simp [hk]
              _ ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) := by gcongr
              _ = (1 : ℚ) / 2 ^ n := two_halves_to_pred n
    simpa [CReal.Pre.inv, CReal.Pre.mul, k, Kx, Ky] using this
  exact CReal.Pre.equiv_trans h_core (CReal.Pre.equiv_symm h_irrel_y)

/-- The cancellation property: x * (1/x) ≈ 1. -/
theorem mul_inv_cancel (x : CReal.Pre) (W : CReal.Pre.InvWitness x) :
  CReal.Pre.Equiv (x.mul (CReal.Pre.inv x W)) CReal.Pre.one := by
  intro n
  let inv_x := CReal.Pre.inv x W
  let prod := x.mul inv_x
  let N := W.N
  let L : ℚ := (1:ℚ) / 2^(N+1)
  let M := N + n + 2
  have h_M_pos : 0 < M := by positivity
  have h_diff_M : |prod.approx M - 1| ≤ 1/2^(n+1) := by
    dsimp [CReal.Pre.mul, CReal.Pre.inv, CReal.Pre.one]
    let S_inv := 2*N + 2
    let S_mul := x.mulShift inv_x
    let K := M + S_mul
    let K_final := K + S_inv
    have h_K_final_ge : N + 1 ≤ K_final := by
      dsimp [K_final, K, S_inv, M]; linarith
    have h_bound_K_final := inv_witness_stability x W K_final h_K_final_ge
    have h_den_pos : 0 < |x.approx K_final| := lt_trans (by positivity) h_bound_K_final
    have hx_ne : x.approx K_final ≠ 0 := by
      exact abs_pos.mp h_den_pos
    have h_num_reg : |x.approx K - x.approx K_final| ≤ (1 : ℚ) / 2 ^ K := by
      simpa [abs_sub_comm] using x.is_regular K K_final (Nat.le_add_right _ _)
    have h_eq_div :
        |x.approx K * (x.approx K_final)⁻¹ - 1|
          = |x.approx K - x.approx K_final| * |x.approx K_final|⁻¹ := by
      have h1 :
          x.approx K / x.approx K_final - 1
            = (x.approx K - x.approx K_final) / x.approx K_final := by
        calc
          x.approx K / x.approx K_final - 1
              = x.approx K / x.approx K_final - x.approx K_final / x.approx K_final := by
                  simp [div_self hx_ne]
          _ = (x.approx K - x.approx K_final) / x.approx K_final := by
                  simpa using (sub_div (x.approx K) (x.approx K_final) (x.approx K_final)).symm
      calc
        |x.approx K * (x.approx K_final)⁻¹ - 1|
            = |x.approx K / x.approx K_final - 1| := by
                simp [div_eq_mul_inv, sub_eq_add_neg, add_comm]
        _ = |(x.approx K - x.approx K_final) / x.approx K_final| := by
                simp [h1]
        _ = |x.approx K - x.approx K_final| / |x.approx K_final| := by
                simp [abs_div]
        _ = |x.approx K - x.approx K_final| * |x.approx K_final|⁻¹ := by
                simp [div_eq_mul_inv]
    have h_num_step :
        |(x.approx K - x.approx K_final) / x.approx K_final|
          ≤ ((1 : ℚ) / 2 ^ K) / |x.approx K_final| := by
      have := div_le_div_of_le_right h_den_pos h_num_reg
      simpa [abs_div] using this
    have h_den_step :
        ((1 : ℚ) / 2 ^ K) / |x.approx K_final| ≤ ((1 : ℚ) / 2 ^ K) / L := by
      have ha : 0 ≤ (1 : ℚ) / 2 ^ K := by
        have hp : 0 < (2 : ℚ) ^ K := pow_pos (by norm_num) _
        exact div_nonneg (by norm_num) (le_of_lt hp)
      have h1 : |x.approx K * (x.approx K_final)⁻¹ - 1|
                ≤ ((1 : ℚ) / 2 ^ K) / |x.approx K_final| := by
        simpa [h_eq_div, div_eq_mul_inv] using h_num_step
      have hLpos : 0 < L := by
        have hpow : 0 < (2 : ℚ) ^ (N + 1) := pow_pos (by norm_num) _
        exact div_pos (by norm_num) hpow
      have h_le : L ≤ |x.approx K_final| := by
        exact le_of_lt (by simpa [L] using h_bound_K_final)
      have h_inv : (1 : ℚ) / |x.approx K_final| ≤ 1 / L :=
        one_div_le_one_div_of_le hLpos h_le
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h_inv ha
    have h_main :
        |x.approx K * (x.approx K_final)⁻¹ - 1|
          ≤ ((1 : ℚ) / 2 ^ K) / L := by
      have h1 : |x.approx K * (x.approx K_final)⁻¹ - 1|
                ≤ ((1 : ℚ) / 2 ^ K) / |x.approx K_final| := by
        rw [h_eq_div]
        have h_nonneg : 0 ≤ |x.approx K_final|⁻¹ := by
          exact inv_nonneg.mpr (abs_nonneg _)
        have h_mul := mul_le_mul_of_nonneg_right h_num_reg h_nonneg
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          using h_mul
      exact _root_.le_trans h1 h_den_step
    have h_prod_eq : prod.approx M = x.approx K * (x.approx K_final)⁻¹ := by
      dsimp [prod, CReal.Pre.mul, inv_x, CReal.Pre.inv, K, K_final, S_inv]
      rfl
    have h_simp :
        ((1 : ℚ) / 2 ^ K) / L = (1 : ℚ) / 2 ^ (n + 1 + S_mul) := by
      dsimp [L]
      have hK' : K = (N + 1) + (n + 1 + S_mul) := by
        have : N + n + 2 + S_mul = (N + 1) + (n + 1 + S_mul) := by
          calc
            N + n + 2 + S_mul
                = N + (n + 1) + (1 + S_mul) := by simp [Nat.add_assoc]; simp +arith
            _ = (N + 1) + (n + 1 + S_mul) := by
                simp [Nat.add_assoc, Nat.add_left_comm]
        simpa [K, M] using this
      have : ((1 : ℚ) / 2 ^ ((N + 1) + (n + 1 + S_mul))) / ((1 : ℚ) / 2 ^ (N + 1))
                = (1 : ℚ) / 2 ^ (n + 1 + S_mul) := by
        simpa [Nat.add_comm] using
          CReal.Pre.div_one_div_pow_simp (a := n + 1 + S_mul) (b := N + 1)
      simpa [hK'] using this
    have h_mono :
        (1 : ℚ) / 2 ^ (n + 1 + S_mul) ≤ (1 : ℚ) / 2 ^ (n + 1) := by
      exact one_div_pow_le_one_div_pow_of_le rfl (Nat.le_add_right _ _)
    have h_main' : |prod.approx M - 1| ≤ (1 : ℚ) / 2 ^ (n + 1 + S_mul) := by
      simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, one_div, abs_pos, ne_eq,
        not_false_eq_true, div_inv_eq_mul, M, N, K_final, K, S_mul, inv_x, S_inv, L, prod]
    exact h_main'.trans h_mono
  dsimp [CReal.Pre.Equiv, CReal.Pre.one]
  have h_reg : |prod.approx (n+1) - prod.approx M| ≤ 1 / 2 ^ (n+1) := by
    apply prod.is_regular
    have : n + 1 ≤ (n + 1) + (N + 1) := Nat.le_add_right _ _
    simp [M, Nat.add_assoc, Nat.add_left_comm]
  calc
    |prod.approx (n+1) - 1|
      ≤ |prod.approx (n+1) - prod.approx M| + |prod.approx M - 1| := by
          apply abs_sub_le
    _ ≤ 1/2^(n+1) + 1/2^(n+1) := by
          have h1 : |prod.approx (n+1) - prod.approx M| ≤ 1 / 2 ^ (n+1) := by
            simpa [abs_sub_comm] using h_reg
          exact add_le_add h1 h_diff_M
    _ = 1/2^n := by
          field_simp [pow_succ]; ring

end CReal.Pre

namespace CReal
open CReal.Pre

/-- Embed a rational as a constant pre-real. -/
def Pre.ofRat (q : ℚ) : CReal.Pre where
  approx := fun _ => q
  is_regular := by
    intro n m _hm
    simp

/-- Rational coercion into `CReal` via constant pre-real. -/
instance : RatCast CReal where
  ratCast q := ⟦Pre.ofRat q⟧

/-- A Cauchy sequence of computable real numbers with dyadic modulus. -/
structure RCauSeq' where
  seq : ℕ → CReal
  is_cauchy :
    ∀ n m, n ≤ m →
      seq n ≤ seq m + (((1 : ℚ) / ((2 : ℚ) ^ n)) : CReal) ∧
      seq m ≤ seq n + (((1 : ℚ) / ((2 : ℚ) ^ n)) : CReal)

/-- A Cauchy sequence of computable real numbers with dyadic modulus, together with explicit representatives. -/
structure RCauSeq where
  seq : ℕ → CReal
  pre : ℕ → CReal.Pre
  seq_spec : ∀ n, seq n = ⟦pre n⟧
  is_cauchy :
    ∀ n m, n ≤ m →
      |(pre (n + 2)).approx (n + 2) - (pre (m + 2)).approx (n + 2)| ≤
        (1 : ℚ) / 2 ^ (n + 1)

@[simp] lemma RCauSeq.seq_spec' (s : RCauSeq) (n : ℕ) :
    s.seq n = ⟦s.pre n⟧ := s.seq_spec n

/-! ### Properties of Separation -/

-- We rely on the decidability of order on ℚ for constructive choice (Nat.find) later.
instance decidable_separated_prop (x : CReal.Pre) (N : ℕ) : Decidable (1/2^N < |x.approx (N+1)|) :=
  inferInstance

/-- Pos x ∨ Pos (-x) implies Separated x. (Constructive) -/
lemma pos_or_neg_pos_implies_separated (x : CReal.Pre) :
  (CReal.Pre.Pos x ∨ CReal.Pre.Pos (CReal.Pre.neg x)) → CReal.Pre.Separated x := by
  intro h
  rcases h with h_pos | h_neg
  · rcases h_pos with ⟨N, hN⟩
    have h_pos_approx : 0 < x.approx (N+1) := lt_trans (by positivity) hN
    have h_abs : |x.approx (N+1)| = x.approx (N+1) := abs_of_pos h_pos_approx
    exact ⟨N, by rwa [h_abs]⟩
  · rcases h_neg with ⟨N, hN⟩
    dsimp [CReal.Pre.neg] at hN
    have h_neg_approx : x.approx (N+1) < 0 := by
      have : 0 < -x.approx (N+1) := lt_trans (by positivity) hN
      exact neg_pos.mp this
    have h_abs : |x.approx (N+1)| = -x.approx (N+1) := abs_of_neg h_neg_approx
    exact ⟨N, by rwa [h_abs]⟩

/-- Separated x implies Pos x ∨ Pos (-x). (Constructive, relies on decidability of ℚ order) -/
lemma separated_implies_pos_or_neg_pos (x : CReal.Pre) (h : CReal.Pre.Separated x) :
  (CReal.Pre.Pos x ∨ CReal.Pre.Pos (CReal.Pre.neg x)) := by
  rcases h with ⟨N, hN⟩
  let approx_val := x.approx (N+1)
  rcases lt_trichotomy approx_val 0 with h_lt | h_eq | h_gt
  · right
    dsimp [CReal.Pre.Pos, CReal.Pre.neg]
    have h_abs : |approx_val| = -approx_val := abs_of_neg h_lt
    exact ⟨N, by rwa [h_abs] at hN⟩
  · have h_rewrite : x.approx (N + 1) = 0 := h_eq
    rw [h_rewrite, abs_zero] at hN
    have h_pos : 0 < (1:ℚ)/2^N := by positivity
    exfalso
    exact lt_irrefl 0 (lt_trans h_pos hN)
  · left
    dsimp [CReal.Pre.Pos]
    have h_abs : |approx_val| = approx_val := abs_of_pos h_gt
    exact ⟨N, by rwa [h_abs] at hN⟩

/-! ### Heyting Field Structure (Constructive Field) -/

/--
Apartness relation: x # y if |x - y| > 0 (constructively).
-/
def Apart (x y : CReal) : Prop :=
  Quotient.lift₂
    (fun x y => Pre.Pos (Pre.add x (Pre.neg y)) ∨ Pre.Pos (Pre.add y (Pre.neg x)))
    (fun x₁ y₁ x₂ y₂ hx hy => propext (by
      constructor
      · intro h
        cases h with
        | inl h =>
          left
          exact (Pre.pos_well_defined _ _ (add_respects_equiv hx (neg_respects_equiv _ _ hy))).mp h
        | inr h =>
          right
          exact (Pre.pos_well_defined _ _ (add_respects_equiv hy (neg_respects_equiv _ _ hx))).mp h
      · intro h
        cases h with
        | inl h =>
          left
          exact (Pre.pos_well_defined _ _ (add_respects_equiv hx (neg_respects_equiv _ _ hy))).mpr h
        | inr h =>
          right
          exact (Pre.pos_well_defined _ _ (add_respects_equiv hy (neg_respects_equiv _ _ hx))).mpr h))
    x y

-- Fixed lim_pre definition
/-- The representative sequence for the limit of an RCauSeq. -/
def lim_pre (s : RCauSeq) : CReal.Pre :=
  let pre_seq (n : ℕ) := (s.pre (n + 2)).approx (n + 2)
  {
    approx := pre_seq
    is_regular := by
      intro n m hnm
      let intermediate := (s.pre (m + 2)).approx (n + 2)
      have h_term₁ : |pre_seq n - intermediate| ≤ (1 : ℚ) / 2 ^ (n + 1) := by
        dsimp [pre_seq]
        exact s.is_cauchy n m hnm
      have h_term₂ : |intermediate - pre_seq m| ≤ (1 : ℚ) / 2 ^ (n + 2) := by
        dsimp [pre_seq]
        have h_le : n + 2 ≤ m + 2 := Nat.add_le_add_right hnm 2
        simpa [abs_sub_comm] using
          (s.pre (m + 2)).is_regular (n + 2) (m + 2) h_le
      have h_sum : (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2) ≤ (1 : ℚ) / 2 ^ n := by
        have h_mono : (1 : ℚ) / 2 ^ (n + 2) ≤ (1 : ℚ) / 2 ^ (n + 1) :=
          inv_pow_antitone_succ (n + 1)
        calc
          (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2)
              ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) := by
                exact add_le_add le_rfl h_mono
          _ = (1 : ℚ) / 2 ^ n := two_halves_to_pred n
      calc
        |pre_seq n - pre_seq m|
          ≤ |pre_seq n - intermediate| + |intermediate - pre_seq m| := abs_sub_le _ _ _
        _ ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2) := add_le_add h_term₁ h_term₂
        _ ≤ (1 : ℚ) / 2 ^ n := h_sum
  }

/-- The limit of a Cauchy sequence of `CReal`s. -/
def lim (s : RCauSeq) : CReal := ⟦lim_pre s⟧

/-- Helper: `(-0) ≈ 0` at the Pre level. -/
lemma neg_zero_equiv_pre : CReal.Pre.Equiv (CReal.Pre.neg CReal.Pre.zero) CReal.Pre.zero := by
  intro n
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have h_nonneg : 0 ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp [CReal.Pre.neg, CReal.Pre.zero, sub_self, abs_zero]

/-- x is apart from 0 if and only if its underlying representation is Separated. -/
theorem apart_zero_iff_separated (x : CReal) :
  Apart x 0 ↔ Quotient.lift Pre.Separated (fun _ _ h => propext (Pre.separated_well_defined _ _ h)) x := by
  refine Quot.induction_on x (fun x_pre => ?_)
  dsimp [Apart, Quotient.lift]
  constructor
  · intro h
    have hx_or : Pre.Pos x_pre ∨ Pre.Pos (CReal.Pre.neg x_pre) := by
      cases h with
      | inl hpos =>
        have h_eq1 : CReal.Pre.Equiv (x_pre.add (CReal.Pre.neg CReal.Pre.zero)) x_pre :=
          CReal.Pre.equiv_trans
            (add_respects_equiv
              (by
                intro n
                have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
                have h_nonneg : 0 ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
                simp)
              neg_zero_equiv_pre)
            (add_zero_pre x_pre)
        left
        exact (Pre.pos_well_defined _ _ h_eq1).mp hpos
      | inr hpos =>
        have h_eq2 : CReal.Pre.Equiv (CReal.Pre.zero.add (CReal.Pre.neg x_pre)) (CReal.Pre.neg x_pre) :=
          zero_add_pre (CReal.Pre.neg x_pre)
        right
        exact (Pre.pos_well_defined _ _ h_eq2).mp hpos
    exact pos_or_neg_pos_implies_separated x_pre hx_or
  · intro h
    have hx_or : Pre.Pos x_pre ∨ Pre.Pos (CReal.Pre.neg x_pre) :=
      separated_implies_pos_or_neg_pos x_pre h
    cases hx_or with
    | inl hx =>
      have h_eq1 : CReal.Pre.Equiv (x_pre.add (CReal.Pre.neg CReal.Pre.zero)) x_pre :=
        CReal.Pre.equiv_trans
          (add_respects_equiv
            (by
              intro n
              have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
              have h_nonneg : 0 ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
              simp)
            neg_zero_equiv_pre)
          (add_zero_pre x_pre)
      exact Or.inl ((Pre.pos_well_defined _ _ h_eq1).mpr hx)
    | inr hnx =>
      have h_eq2 : CReal.Pre.Equiv (CReal.Pre.zero.add (CReal.Pre.neg x_pre)) (CReal.Pre.neg x_pre) :=
        zero_add_pre (CReal.Pre.neg x_pre)
      exact Or.inr ((Pre.pos_well_defined _ _ h_eq2).mpr hnx)

/-! ### Pseudo-Order Structure -/

set_option maxHeartbeats 0 in
/--
CReal forms a pseudo-order. This is the constructive analogue of a linear order
for structures where equality is not decidable: if x < y, then for any z, either x < z or z < y.
-/
theorem pseudo_order_property (x y z : CReal) (hxy : x < y) : x < z ∨ z < y := by
  have h_pos := (lt_iff_pos x y).mp hxy
  refine Quot.induction_on₃ x y z (fun x_pre y_pre z_pre h_pos => ?_) h_pos
  dsimp [Pos, CReal.Pre.Pos] at h_pos
  rcases h_pos with ⟨N, hN⟩
  dsimp [CReal.Pre.add, CReal.Pre.neg] at hN
  let M := N + 3
  let K := M + 1
  have h_reg_diff := (y_pre.add (x_pre.neg)).is_regular (N+1) K (by simp [K,M])
  dsimp [CReal.Pre.add, CReal.Pre.neg] at h_reg_diff
  have h_diff_K_ge :
      (y_pre.approx (N+2) - x_pre.approx (N+2)) - 1/2^(N+1)
        ≤ y_pre.approx (K+1) - x_pre.approx (K+1) := by
    have h_pair := (abs_sub_le_iff).1 h_reg_diff
    have h_aux :
        (y_pre.approx (N+2) - x_pre.approx (N+2)) -
          (y_pre.approx (K+1) - x_pre.approx (K+1))
          ≤ 1 / 2 ^ (N + 1) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_pair.left
    linarith
  have h_gap_stable : 1/2^(N+1) < y_pre.approx (K+1) - x_pre.approx (K+1) := by
    have h_sub : (1:ℚ)/2^N - 1/2^(N+1) = 1/2^(N+1) := by
      field_simp [pow_succ]; ring
    calc
      1/2^(N+1) = 1/2^N - 1/2^(N+1) := h_sub.symm
      _ < (y_pre.approx (N+2) + -x_pre.approx (N+2)) - 1/2^(N+1) :=
            sub_lt_sub_right hN _
      _ = (y_pre.approx (N+2) - x_pre.approx (N+2)) - 1/2^(N+1) := by simp [sub_eq_add_neg]
      _ ≤ y_pre.approx (K+1) - x_pre.approx (K+1) := h_diff_K_ge
  let m_K := (x_pre.approx K + y_pre.approx K) / 2
  cases le_or_gt (z_pre.approx K) m_K with
  | inl h_le =>
    right
    apply (lt_iff_pos ⟦z_pre⟧ ⟦y_pre⟧).mpr
    dsimp [Pos, CReal.Pre.Pos]
    have h_diff_ge_half : (y_pre.approx K - x_pre.approx K)/2 ≤
        y_pre.approx K - z_pre.approx K := by
      calc
        (y_pre.approx K - x_pre.approx K)/2
            = y_pre.approx K - (x_pre.approx K + y_pre.approx K)/2 := by ring
        _ ≤ y_pre.approx K - z_pre.approx K := sub_le_sub_left h_le _
    have hy_pair :=
      (abs_sub_le_iff).1 (by simpa using y_pre.is_regular K (K+1) (Nat.le_succ _))
    have hz_pair :=
      (abs_sub_le_iff).1 (by simpa using z_pre.is_regular K (K+1) (Nat.le_succ _))
    have hx_pair :=
      (abs_sub_le_iff).1 (by simpa using x_pre.is_regular K (K+1) (Nat.le_succ _))
    have hz_up : z_pre.approx (K+1) ≤ z_pre.approx K + 1 / 2 ^ K := by
      have h := (sub_le_iff_le_add).mp hz_pair.right
      simpa [add_comm, one_div] using h
    have hx_ge : x_pre.approx (K+1) ≥ x_pre.approx K - 1 / 2 ^ K := by
      have h := (sub_le_iff_le_add).mp hx_pair.left
      have : x_pre.approx K - (2^K)⁻¹ ≤ x_pre.approx (K+1) :=
        (sub_le_iff_le_add).2 (by simpa [add_comm] using h)
      simpa [one_div] using this
    have hy_ge : y_pre.approx (K+1) ≥ y_pre.approx K - 1 / 2 ^ K := by
      have h := (sub_le_iff_le_add).mp hy_pair.left
      have : y_pre.approx K - (2^K)⁻¹ ≤ y_pre.approx (K+1) :=
        (sub_le_iff_le_add).2 (by simpa [add_comm] using h)
      simpa [one_div] using this
    have hm_ge :
        (x_pre.approx (K+1) + y_pre.approx (K+1))/2 ≥
          (x_pre.approx K + y_pre.approx K)/2 - 1/2^K := by
      linarith [hx_ge, hy_ge]
    have hz_up' :
        z_pre.approx (K+1) ≤
          (x_pre.approx (K+1) + y_pre.approx (K+1))/2 + 2/2^K := by
      have hz_to_mK :
          z_pre.approx (K+1) ≤ (x_pre.approx K + y_pre.approx K)/2 + 1/2^K :=
        (hz_up.trans (Rat.add_le_add_right.mpr h_le))
      have : (x_pre.approx K + y_pre.approx K)/2
              ≤ (x_pre.approx (K+1) + y_pre.approx (K+1))/2 + 1/2^K := by
        linarith [hm_ge]
      have step' := add_le_add_right this (1/2^K)
      have htwo : (1/2^K : ℚ) + 1/2^K = 2/2^K := by ring
      have h_lift :
          (x_pre.approx K + y_pre.approx K)/2 + 1/2^K
            ≤ (x_pre.approx (K+1) + y_pre.approx (K+1))/2 + 2/2^K := by
        calc
          (x_pre.approx K + y_pre.approx K)/2 + 1/2^K
              ≤ (x_pre.approx (K+1)+y_pre.approx (K+1))/2 + 1/2^K + 1/2^K :=
                Rat.add_le_add_right.mpr this
          _ = (x_pre.approx (K+1)+y_pre.approx (K+1))/2 + (1/2^K + 1/2^K) := by ring
          _ = (x_pre.approx (K+1)+y_pre.approx (K+1))/2 + 2/2^K := by simp; ring_nf
      exact hz_to_mK.trans h_lift
    have hK_expr : K = N + 4 := by
      simp [K,M, Nat.add_comm, Nat.add_left_comm]
    have h_two_over : (2:ℚ)/2^K = (1:ℚ)/2^(N+3) := by
      have : (2:ℚ)/2^(N+4) = (1:ℚ)/2^(N+3) := by
        field_simp [pow_succ]; ring
      simpa [hK_expr]
    have h_gap_half_K1 :
        (1:ℚ)/2^(N+2) < (y_pre.approx (K+1) - x_pre.approx (K+1))/2 := by
      have h_mul := (mul_lt_mul_of_pos_right h_gap_stable (by norm_num : 0 < (1:ℚ)/2))
      simpa [one_div, pow_succ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using h_mul
    have h_core_margin :
        (1:ℚ)/2^(N+3)
          < y_pre.approx (K+1)
              - ( (x_pre.approx (K+1)+y_pre.approx (K+1))/2 )
              - (1:ℚ)/2^(N+3) := by
      have hrewrite :
          y_pre.approx (K+1) - ((x_pre.approx (K+1)+y_pre.approx (K+1))/2)
            = (y_pre.approx (K+1) - x_pre.approx (K+1))/2 := by
        field_simp; ring
      have h_sub : (1:ℚ)/2^(N+2) - (1:ℚ)/2^(N+3) = (1:ℚ)/2^(N+3) := by
        field_simp [pow_succ]; ring
      have h := sub_lt_sub_right h_gap_half_K1 ((1:ℚ)/2^(N+3))
      calc
        (1:ℚ)/2^(N+3)
            = (1:ℚ)/2^(N+2) - (1:ℚ)/2^(N+3) := h_sub.symm
        _ < (y_pre.approx (K+1) - x_pre.approx (K+1))/2 - (1:ℚ)/2^(N+3) := h
        _ = y_pre.approx (K+1)
              - ((x_pre.approx (K+1)+y_pre.approx (K+1))/2)
              - (1:ℚ)/2^(N+3) := by
              simp [sub_eq_add_neg, add_comm]
              ring_nf
    have h_margin :
        (1:ℚ)/2^M < y_pre.approx (K+1) - z_pre.approx (K+1) := by
      have h_comp :
          y_pre.approx (K+1)
            - ((x_pre.approx (K+1)+y_pre.approx (K+1))/2 + (2:ℚ)/2^K)
              ≤ y_pre.approx (K+1) - z_pre.approx (K+1) :=
        sub_le_sub_left hz_up' _
      have h_base :
          (1:ℚ)/2^(N+3) <
            y_pre.approx (K+1)
              - ((x_pre.approx (K+1)+y_pre.approx (K+1))/2 + (2:ℚ)/2^K) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, h_two_over]
          using h_core_margin
      have h_trans := lt_of_lt_of_le h_base h_comp
      simpa [M] using h_trans
    refine ⟨M, ?_⟩
    have h_expand :
      (y_pre.add z_pre.neg).approx (M+1) =
        y_pre.approx (K+1) - z_pre.approx (K+1) := by
      have hK1 : K + 1 = M + 2 := by simp [K,M]
      dsimp [CReal.Pre.add, CReal.Pre.neg]
      simp [hK1, sub_eq_add_neg, add_comm]
      ring_nf
    have h_witness :
      (1 : ℚ)/2^M < (y_pre.add z_pre.neg).approx (M+1) := by
      simpa [h_expand]
        using h_margin
    exact h_witness
  | inr h_gt =>
    left
    apply (lt_iff_pos ⟦x_pre⟧ ⟦z_pre⟧).mpr
    dsimp [Pos, CReal.Pre.Pos]
    have h_diff_gt_half :
        (y_pre.approx K - x_pre.approx K)/2 < z_pre.approx K - x_pre.approx K := by
      calc
        (y_pre.approx K - x_pre.approx K)/2
            = (x_pre.approx K + y_pre.approx K)/2 - x_pre.approx K := by ring
        _ < z_pre.approx K - x_pre.approx K := sub_lt_sub_right h_gt _
    have hN2_le_K : N + 2 ≤ K := by simp [K,M]
    have hy_reg := (abs_sub_le_iff).1 (by simpa using y_pre.is_regular (N+2) K hN2_le_K)
    have hx_reg := (abs_sub_le_iff).1 (by simpa using x_pre.is_regular (N+2) K hN2_le_K)
    have hy_ge : y_pre.approx K ≥ y_pre.approx (N+2) - 1/2^(N+2) := by
      have : y_pre.approx (N+2) - y_pre.approx K ≤ 1/2^(N+2) := by
        simpa [one_div] using hy_reg.left
      linarith
    have hx_le : x_pre.approx K ≤ x_pre.approx (N+2) + 1/2^(N+2) := by
      have : x_pre.approx K - x_pre.approx (N+2) ≤ 1/2^(N+2) := by
        simpa [one_div] using hx_reg.right
      linarith
    have h_yx :
        y_pre.approx K - x_pre.approx K ≥
          (y_pre.approx (N+2) - x_pre.approx (N+2)) - 2 / 2 ^ (N+2) := by
      calc
        y_pre.approx K - x_pre.approx K
            ≥ (y_pre.approx (N+2) - 1/2^(N+2)) - (x_pre.approx (N+2) + 1/2^(N+2)) :=
              sub_le_sub hy_ge hx_le
        _ = (y_pre.approx (N+2) - x_pre.approx (N+2)) - 2/2^(N+2) := by ring
    have h_core :
        (y_pre.approx (N+2) - x_pre.approx (N+2)) - 2 / 2 ^ (N + 2)
          > 1 / 2 ^ (N + 1) := by
      have hyx : 1 / 2 ^ N < y_pre.approx (N+2) - x_pre.approx (N+2) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hN
      have h_split : (1 : ℚ) / 2 ^ N = (1 : ℚ) / 2 ^ (N + 1) + (1 : ℚ) / 2 ^ (N + 1) := by
        field_simp [pow_succ]; ring
      have h_big :
          (1 : ℚ) / 2 ^ (N + 1) + (1 : ℚ) / 2 ^ (N + 1)
            < y_pre.approx (N+2) - x_pre.approx (N+2) := by
        simpa [h_split]
          using hyx
      have h_goal :
          (y_pre.approx (N+2) - x_pre.approx (N+2)) - (1 : ℚ) / 2 ^ (N + 1)
            > (1 : ℚ) / 2 ^ (N + 1) := by
        linarith
      have h_two : (2 : ℚ) / 2 ^ (N + 2) = (1 : ℚ) / 2 ^ (N + 1) := by
        simp [pow_succ, mul_comm]; ring_nf
      simpa [h_two] using h_goal
    have h_yx_strong :
        1 / 2 ^ (N + 1) < y_pre.approx K - x_pre.approx K :=
      lt_of_lt_of_le h_core h_yx
    have h_gap_half :
        1 / 2 ^ (N + 2) < (y_pre.approx K - x_pre.approx K)/2 := by
      have hpos : (0:ℚ) < (1:ℚ)/2 := by norm_num
      have := mul_lt_mul_of_pos_right h_yx_strong hpos
      simpa [one_div, pow_succ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have h_final_at_K :
        1 / 2 ^ (N + 2) < z_pre.approx K - x_pre.approx K :=
      lt_trans h_gap_half h_diff_gt_half
    have hz_pair :=
      (abs_sub_le_iff).1 (by simpa using z_pre.is_regular K (K+1) (Nat.le_succ _))
    have hx_pair :=
      (abs_sub_le_iff).1 (by simpa using x_pre.is_regular K (K+1) (Nat.le_succ _))
    have hz_lower : z_pre.approx (K+1) ≥ z_pre.approx K - 1/2^K := by
      have : z_pre.approx K - z_pre.approx (K+1) ≤ 1/2^K := by
        simpa [one_div] using hz_pair.left
      linarith
    have hx_upper : x_pre.approx (K+1) ≤ x_pre.approx K + 1/2^K := by
      have : x_pre.approx (K+1) - x_pre.approx K ≤ 1/2^K := by
        simpa [one_div] using hx_pair.right
      linarith
    have h_lower_shift :
        z_pre.approx (K+1) - x_pre.approx (K+1)
          ≥ z_pre.approx K - x_pre.approx K - 2/2^K := by
      calc
        z_pre.approx (K+1) - x_pre.approx (K+1)
            ≥ (z_pre.approx K - 1/2^K) - (x_pre.approx K + 1/2^K) :=
              sub_le_sub hz_lower hx_upper
        _ = z_pre.approx K - x_pre.approx K - 2/2^K := by ring
    have hK_expr : K = N + 4 := by simp [K,M]
    have h_two_over : (2:ℚ)/2^K = (1:ℚ)/2^(N+3) := by
      have : (2:ℚ)/2^(N+4) = (1:ℚ)/2^(N+3) := by
        field_simp [pow_succ]; ring
      simpa [hK_expr]
    have base_shift :
      1 / 2 ^ (N + 2) - 2 / 2 ^ K < z_pre.approx K - x_pre.approx K - 2 / 2 ^ K := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using (sub_lt_sub_right h_final_at_K ((2:ℚ)/2^K))
    have h_left_rewrite :
        (1 : ℚ) / 2 ^ (N + 2) - (2 : ℚ) / 2 ^ K = (1 : ℚ) / 2 ^ (N + 3) := by
      have h2 : (2 : ℚ) / (2 : ℚ) ^ K = (1 : ℚ) / (2 : ℚ) ^ (N + 3) := h_two_over
      have h_sub : (1:ℚ)/2^(N+2) - (1:ℚ)/2^(N+3) = (1:ℚ)/2^(N+3) := by
        field_simp [one_div, pow_succ]; ring
      calc
        (1 : ℚ) / 2 ^ (N + 2) - (2 : ℚ) / 2 ^ K
            = (1 : ℚ) / 2 ^ (N + 2) - (1 : ℚ) / 2 ^ (N + 3) := by rw [h2]
        _ = (1 : ℚ) / 2 ^ (N + 3) := h_sub
    have h_at_K1 :
        1 / 2 ^ (N + 3) < z_pre.approx K - x_pre.approx K - 2 / 2 ^ K := by
      have h_sum_halves :
          (1:ℚ)/2^(N+3) + (1:ℚ)/2^(N+3) = 1 / 2 ^ (N + 2) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using two_halves_to_succ (N + 1)
      have h_gap' : (1:ℚ)/2^(N+3) + (1:ℚ)/2^(N+3) < z_pre.approx K - x_pre.approx K := by
        rw [h_sum_halves]
        simp_all only [one_div, lt_add_neg_iff_add_lt, tsub_le_iff_right, add_le_add_iff_right, le_add_iff_nonneg_right,
          zero_le, ge_iff_le, gt_iff_lt, sub_lt_sub_iff_right, K, M, m_K]
      have h_goal :
          (1:ℚ)/2^(N+3) < z_pre.approx K - x_pre.approx K - 1/2^(N+3) := by
        have : (1:ℚ)/2^(N+3) + (1:ℚ)/2^(N+3) < z_pre.approx K - x_pre.approx K := h_gap'
        linarith
      simpa [h_two_over] using h_goal
    have h_step :
        1 / 2 ^ (N + 3) < z_pre.approx (K+1) - x_pre.approx (K+1) :=
      lt_of_lt_of_le h_at_K1 h_lower_shift
    have h_step_stronger :
        1 / 2 ^ M < z_pre.approx (K+1) - x_pre.approx (K+1) := by
      have hM : M = N + 3 := rfl
      simpa [hM] using h_step
    refine ⟨M, ?_⟩
    have h_expand :
      (z_pre.add x_pre.neg).approx (M+1) =
        z_pre.approx (K+1) - x_pre.approx (K+1) := by
      have hK1 : K + 1 = M + 2 := by simp [K,M]
      dsimp [CReal.Pre.add, CReal.Pre.neg]
      simp [hK1, sub_eq_add_neg]
    simpa [h_expand] using h_step_stronger

-- A simp lemma to rewrite the limit representative at any index
@[simp]
lemma lim_pre_approx_simp (s : RCauSeq) (t : ℕ) :
  (lim_pre s).approx t = (s.pre (t + 2)).approx (t + 2) := rfl

-- Collapse 1/2^n + 1/2^(n-1) + 1/2^n to 1/2^(n-2) (for n ≥ 2)
private lemma three_terms_collapse_aux (m : ℕ) :
    (1 : ℚ) / 2 ^ (m + 2) + 1 / 2 ^ (m + 1) + 1 / 2 ^ (m + 2) = 1 / 2 ^ m := by
  calc
    (1 : ℚ) / 2 ^ (m + 2) + 1 / 2 ^ (m + 1) + 1 / 2 ^ (m + 2)
        = ((1 : ℚ) / 2 ^ (m + 2) + 1 / 2 ^ (m + 2)) + 1 / 2 ^ (m + 1) := by
          simp [add_comm, add_left_comm]
    _ = 1 / 2 ^ (m + 1) + 1 / 2 ^ (m + 1) := by
          simp [add_comm]; ring_nf
    _ = 1 / 2 ^ m := two_halves_to_pred m

lemma three_terms_collapse (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℚ) / 2 ^ n + 1 / 2 ^ (n - 1) + 1 / 2 ^ n = 1 / 2 ^ (n - 2) := by
  let m := n - 2
  have hm_add : m + 2 = n := Nat.sub_add_cancel hn
  have hn_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hm1 : m + 1 = n - 1 := by
    apply Nat.succ_injective
    have h_left : Nat.succ (m + 1) = n := by
      simp [m, Nat.add_comm]; simp +arith [*]
    have h_right : Nat.succ (n - 1) = n := Nat.succ_pred_eq_of_pos hn_pos
    simp_all only [Nat.sub_add_cancel, Nat.succ_eq_add_one, m]
  have hm0 : m = n - 2 := rfl
  simpa [m, hm0, hm_add, hm1, add_comm, add_left_comm, add_assoc] using
    three_terms_collapse_aux m

-- Synchronous (single-index) bound at index n+2:
-- |(s.pre n)_(n+2) - (lim_pre s)_(n+2)| ≤ 1/2^(n-2)
lemma diff_at_sync_bound (s : RCauSeq) (n : ℕ) (hn : 2 ≤ n) :
  |(s.pre n).approx (n + 2) - (lim_pre s).approx (n + 2)| ≤ (1 : ℚ) / 2 ^ (n - 2) := by
  -- A := (s.pre n).approx (n+2)
  -- B := (s.pre n).approx n
  -- C := (s.pre (n+4)).approx n  (since K = n+2 ⇒ K+2 = n+4)
  -- L := (lim_pre s).approx (n+2) = (s.pre (n+4)).approx (n+4)
  set A := (s.pre n).approx (n + 2) with hA
  set B := (s.pre n).approx n with hB
  set C := (s.pre (n + 4)).approx n with hC
  set L := (lim_pre s).approx (n + 2) with hL
  have h1 : |A - B| ≤ (1 : ℚ) / 2 ^ n := by
    simpa [A, B, abs_sub_comm] using (s.pre n).is_regular n (n + 2) (Nat.le_add_right _ _)
  have h2 : |B - C| ≤ (1 : ℚ) / 2 ^ (n - 1) := by
    have hnm : n - 2 ≤ n + 2 := by
      have : n - 2 ≤ n := Nat.sub_le _ _
      exact this.trans (Nat.le_add_right _ _)
    have one_lt_n : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
    have hpos : 0 < n - 1 := Nat.sub_pos_of_lt one_lt_n
    have h_succ : Nat.succ (n - 2) = n - 1 := by
      simpa using Nat.succ_pred_eq_of_pos hpos
    have h := s.is_cauchy (n - 2) (n + 2) hnm
    dsimp [B, C, Nat.sub_add_cancel hn, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
           h_succ, Nat.succ_eq_add_one, Nat.one_add]
    simp_all only [lim_pre_approx_simp, one_div, tsub_le_iff_right, tsub_pos_iff_lt, Nat.succ_eq_add_one,
      Nat.sub_add_cancel, A, B, C, L]
  have h3 : |C - L| ≤ (1 : ℚ) / 2 ^ n := by
    simpa [C, L, lim_pre_approx_simp, abs_sub_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (s.pre (n + 4)).is_regular n (n + 4) (Nat.le_add_right _ _)
  have h_bound : |A - L| ≤ 1/2^n + 1/2^(n-1) + 1/2^n := by
    calc
      |A - L| ≤ |A - B| + |B - C| + |C - L| := by
        have := abs_add_three (A - B) (B - C) (C - L)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      _ ≤ (1/2^n) + (1/2^(n-1)) + (1/2^n) := by
        have := add_le_add (add_le_add h1 h2) h3
        simpa [add_comm, add_left_comm, add_assoc]
  have h_three := three_terms_collapse n hn
  have h_value :
      (1 : ℚ) / 2 ^ n + ((1 : ℚ) / 2 ^ n + (1 : ℚ) / 2 ^ (n - 1)) =
        (1 : ℚ) / 2 ^ (n - 2) := by
    calc
      (1 : ℚ) / 2 ^ n + ((1 : ℚ) / 2 ^ n + (1 : ℚ) / 2 ^ (n - 1))
          = ((1 : ℚ) / 2 ^ n + (1 : ℚ) / 2 ^ (n - 1)) + (1 : ℚ) / 2 ^ n := by
            simp [add_comm]
      _ = (1 : ℚ) / 2 ^ (n - 2) := by
            simpa [add_comm, add_left_comm, add_assoc] using h_three
  have : |A - L| ≤ (1 : ℚ) / 2 ^ (n - 2) := by
    simp; simp_all
  exact this

lemma lift_sync_bound_to_all_indices
  (d : CReal.Pre) {K : ℕ} {r : ℚ} (hK : |d.approx K| ≤ r) :
  ∀ j : ℕ, |d.approx (j + 1)| ≤ r + (1 : ℚ) / 2 ^ (min j K) := by
  intro j
  have h_tri : |d.approx (j + 1)| ≤ |d.approx (j + 1) - d.approx K| + |d.approx K| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (abs_add_le (d.approx (j + 1) - d.approx K) (d.approx K))
  have hreg : |d.approx (j + 1) - d.approx K| ≤ (1 : ℚ) / 2 ^ (min (j + 1) K) :=
    CReal.abs_approx_diff_le d (j + 1) K
  have hmin : min j K ≤ min (j + 1) K := by
    exact min_le_min (Nat.le_succ j) le_rfl
  have hpow_mono :
      (2 : ℚ) ^ (min j K) ≤ (2 : ℚ) ^ (min (j + 1) K) :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).2 hmin
  have h_one_div :
      (1 : ℚ) / 2 ^ (min (j + 1) K) ≤ (1 : ℚ) / 2 ^ (min j K) :=
    one_div_le_one_div_of_le (pow_pos (by norm_num) _) hpow_mono
  have hreg' : |d.approx (j + 1) - d.approx K| ≤ (1 : ℚ) / 2 ^ (min j K) :=
    hreg.trans h_one_div
  have h_sum : |d.approx (j + 1) - d.approx K| + |d.approx K|
      ≤ (1 : ℚ) / 2 ^ (min j K) + |d.approx K| := Rat.add_le_add_right.mpr hreg'
  --  Nat.add_le_add_right hreg' _
  have h_step : |d.approx (j + 1)|
      ≤ (1 : ℚ) / 2 ^ (min j K) + |d.approx K| :=
    _root_.le_trans h_tri h_sum
  have h_step' : |d.approx (j + 1)|
      ≤ |d.approx K| + (1 : ℚ) / 2 ^ (min j K) := by
    simpa [add_comm] using h_step
  have hK_add :
      |d.approx K| + (1 : ℚ) / 2 ^ (min j K) ≤ r + (1 : ℚ) / 2 ^ (min j K) :=
        Rat.add_le_add_right.mpr hK
  exact _root_.le_trans h_step' hK_add

-- From absolute pre-bounds at all indices to a CReal absolute-value bound
lemma abs_le_of_pre_abs_bound (d : CReal.Pre) {r : ℚ}
  (hall : ∀ j : ℕ, |d.approx (j + 1)| ≤ r + (1 : ℚ) / 2 ^ j) :
  |(⟦d⟧ : CReal)| ≤ (r : CReal) := by
  have h1 : (⟦d⟧ : CReal) ≤ (r : CReal) := by
    change CReal.Pre.le d (CReal.Pre.ofRat r)
    intro j
    exact (abs_le.mp (hall j)).2
  have h2 : -(⟦d⟧ : CReal) ≤ (r : CReal) := by
    change CReal.Pre.le (CReal.Pre.neg d) (CReal.Pre.ofRat r)
    intro j
    have h := hall j
    have : -(d.approx (j + 1)) ≤ |d.approx (j + 1)| := by
      simpa using (neg_le_abs (d.approx (j + 1)))
    exact (this.trans h)
  change sup ⟦d⟧ (-⟦d⟧) ≤ (r : CReal)
  exact sup_le h1 h2

lemma min_tail_split (j n : ℕ) :
  (1 : ℚ) / 2 ^ (min j (n + 1)) ≤ (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
  cases le_total j (n + 1) with
  | inl h =>
      have hnn : 0 ≤ (1 : ℚ) / 2 ^ (n + 1) := by positivity
      have this : (1 : ℚ) / 2 ^ j ≤ (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
        exact le_add_of_nonneg_right hnn
      simp [min_eq_left h]
  | inr h =>
      have hnn : 0 ≤ (1 : ℚ) / 2 ^ j := by positivity
      have this : (1 : ℚ) / 2 ^ (n + 1) ≤ (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
        exact le_add_of_nonneg_left hnn
      simp [min_eq_right h]

lemma lift_sync_bound_with_uniform_tail
  (d : CReal.Pre) (n : ℕ) {r : ℚ}
  (h_sync : |d.approx (n + 1)| ≤ r) :
  ∀ j, |d.approx (j + 1)| ≤ r + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
  intro j
  have h_base :=
    CReal.lift_sync_bound_to_all_indices (d := d) (K := n + 1) (r := r) (by simpa using h_sync) j
  have h_tail := min_tail_split j n
  have h_mono := add_le_add_right h_tail r
  calc |d.approx (j + 1)|
    ≤ r + (1 : ℚ) / 2 ^ (min j (n + 1)) := h_base
    _ ≤ r + ((1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1)) := by gcongr
    _ = r + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by ring

lemma diff_sync_bound_for_d (s : CReal.RCauSeq) (n : ℕ) (hn : 2 ≤ n) :
  |((CReal.Pre.add (s.pre n) (CReal.Pre.neg (CReal.lim_pre s))).approx (n + 1))| ≤ (1 : ℚ) / 2 ^ (n - 2) := by
  let d := CReal.Pre.add (s.pre n) (CReal.Pre.neg (CReal.lim_pre s))
  have hJ :
    d.approx (n + 1)
      = (s.pre n).approx (n + 2) - (CReal.lim_pre s).approx (n + 2) := by
    dsimp [d, CReal.Pre.add, CReal.Pre.neg]; ring
  have hlim : (CReal.lim_pre s).approx (n + 2) = (s.pre (n + 4)).approx (n + 4) := by
    simp [lim_pre_approx_simp]
  rw [hJ, hlim]
  exact CReal.diff_at_sync_bound s n hn

lemma all_indices_bound_from_sync
  (d : CReal.Pre) (n k : ℕ)
  (_ : 2 ≤ n)
  (h_sync : |d.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ (n - 2))
  (hk : k ≤ n - 2) :
  ∀ j, |d.approx (j + 1)| ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
  intro j
  have h_all_sync :
      |d.approx (j + 1)| ≤ (1 : ℚ) / 2 ^ (n - 2) + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) :=
    lift_sync_bound_with_uniform_tail d n (r := (1 : ℚ) / 2 ^ (n - 2)) (by simpa using h_sync) j
  have hmono :
      (1 : ℚ) / 2 ^ (n - 2) ≤ (1 : ℚ) / 2 ^ k :=
    one_div_pow_le_one_div_pow_of_le rfl hk
  have h_stronger :
      (1 : ℚ) / 2 ^ (n - 2) + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1)
        ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
    have := add_le_add_right (add_le_add_right hmono ((1 : ℚ) / 2 ^ j)) ((1 : ℚ) / 2 ^ (n + 1))
    simpa [add_comm, add_left_comm, add_assoc] using this
  exact h_all_sync.trans h_stronger

theorem converges_to_lim (s : CReal.RCauSeq) (k : ℕ) :
    ∀ n ≥ k+2, |s.seq n - CReal.lim s| ≤ ((((1 : ℚ) / (2 : ℚ) ^ k) + ((1 : ℚ) / (2 : ℚ) ^ (n + 1))) : CReal) := by
  intro n hn
  have hseq : s.seq n = ⟦s.pre n⟧ := s.seq_spec' n
  have hlim : CReal.lim s = ⟦CReal.lim_pre s⟧ := rfl
  let d : CReal.Pre := CReal.Pre.add (s.pre n) (CReal.Pre.neg (CReal.lim_pre s))
  have hn2 : 2 ≤ n := Nat.le_of_add_left_le hn
  have h_sync : |d.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ (n - 2) :=
    diff_sync_bound_for_d s n hn2
  have hk_le : k ≤ n - 2 := Nat.le_sub_of_add_le hn
  have hall_with_tail :
    ∀ j, |d.approx (j + 1)| ≤ (1 : ℚ) / (2 : ℚ) ^ k + 1 / (2 : ℚ) ^ j + 1 / 2 ^ (n + 1) :=
    all_indices_bound_from_sync d n k hn2 h_sync hk_le
  have hall' :
    ∀ j, |d.approx (j + 1)| ≤ ((1 : ℚ) / (2 : ℚ) ^ k + (1 : ℚ) / (2 : ℚ) ^ (n + 1)) + 1 / (2 : ℚ) ^ j := by
    intro j
    simpa [add_comm, add_left_comm, add_assoc] using (hall_with_tail j)
  have h_abs : |(⟦d⟧ : CReal)| ≤ ((((1 : ℚ) / (2 : ℚ) ^ k) + ((1 : ℚ) / (2 : ℚ) ^ (n + 1))) : CReal) :=
    by simpa using (CReal.abs_le_of_pre_abs_bound d hall')
  simpa [hseq, hlim, d, CReal.Pre.add, CReal.Pre.neg, sub_eq_add_neg] using h_abs

end CReal

namespace Computable

-- Functional Framework

/-- A Gauge is a strictly positive rational number. (From Approach 2) -/
structure Gauge where
  val : ℚ
  property : 0 < val
deriving DecidableEq

instance : Coe Gauge ℚ where
  coe g := g.val

lemma Gauge.pos (g : Gauge) : 0 < (g : ℚ) := g.property

/-- Formalized Uniformly Continuous function on ℚ. (Enhanced Approach 2) -/
structure UniformCtsQQ where
  toFun : ℚ → ℚ
  modulus : Gauge → Gauge
  /-- The proof that the function adheres to the modulus. -/
  uniform_continuity_proof : ∀ (ε : Gauge) (x y : ℚ),
    |x - y| < (modulus ε : ℚ) → |toFun x - toFun y| < (ε : ℚ)

-- Lifting Mechanism

/-- Helper function to find k such that 1/2^k < δ. -/
def find_k (δ : Gauge) : ℕ :=
  let h_exists : ∃ k : ℕ, 1/(δ:ℚ) < (2:ℚ)^k :=
    exists_pow_gt (by rw [one_div_pos]; exact δ.pos)
  Nat.find h_exists

lemma find_k_bound (δ : Gauge) : (1:ℚ) / 2^(find_k δ) < (δ:ℚ) := by
  rw [one_div_lt]
  · exact Nat.find_spec (p := fun k => 1/(δ:ℚ) < (2:ℚ)^k) _
  · positivity
  · exact δ.pos

/-- Helper function to find k such that 1/2^(k-1) < δ. Ensures k > 0. -/
def find_k' (δ : Gauge) : ℕ :=
  find_k δ + 1

lemma find_k'_bound (δ : Gauge) : (1:ℚ) / 2^(find_k' δ - 1) < (δ:ℚ) := by
  unfold find_k'
  simpa [Nat.add_sub_cancel] using find_k_bound δ

/--
Lifts a uniformly continuous function on ℚ to a function on CReal.Pre.
This implementation uses find_k' to ensure that the input precision is sufficient
for both regularity and equivalence proofs.
-/
def makeCRealFunPre (f : UniformCtsQQ) (x : CReal.Pre) : CReal.Pre where
  approx := fun n =>
    let ε : Gauge := ⟨(1:ℚ)/2^(n+1), by positivity⟩
    let δ := f.modulus ε
    let k := find_k' δ
    f.toFun (x.approx k)
  is_regular := by
    intro n m hnm
    let ε_n : Gauge := ⟨(1:ℚ)/2^(n+1), by positivity⟩
    let ε_m : Gauge := ⟨(1:ℚ)/2^(m+1), by positivity⟩
    let k_n := find_k' (f.modulus ε_n)
    let k_m := find_k' (f.modulus ε_m)
    let K := max k_n k_m
    -- Term 1: |f(x_kn) - f(x_K)|. Bound < ε_n.
    have h_term_1 : |f.toFun (x.approx k_n) - f.toFun (x.approx K)| < (ε_n:ℚ) := by
      apply f.uniform_continuity_proof ε_n
      calc
        |x.approx k_n - x.approx K|
          ≤ 1/2^k_n := x.is_regular k_n K (le_max_left _ _)
        _ ≤ 1/2^(k_n-1) := by
          have h_kn_pos : 0 < k_n := by dsimp [k_n, find_k']; exact Nat.succ_pos _
          have hk : k_n = (k_n - 1) + 1 := (Nat.succ_pred_eq_of_pos h_kn_pos).symm
          rw [hk]
          exact inv_pow_antitone_succ (k_n - 1)
        _ < (f.modulus ε_n : ℚ) := find_k'_bound (f.modulus ε_n)
    -- Term 2: |f(x_K) - f(x_km)|. Bound < ε_m. (Symmetric argument)
    have h_term_2 : |f.toFun (x.approx K) - f.toFun (x.approx k_m)| < (ε_m:ℚ) := by
      apply f.uniform_continuity_proof ε_m
      calc
        |x.approx K - x.approx k_m|
          ≤ 1/2^k_m := by
            rw [abs_sub_comm]; exact x.is_regular k_m K (le_max_right _ _)
        _ ≤ 1/2^(k_m-1) := by
          have h_km_pos : 0 < k_m := by dsimp [k_m, find_k']; exact Nat.succ_pos _
          have hk : k_m = (k_m - 1) + 1 := (Nat.succ_pred_eq_of_pos h_km_pos).symm
          rw [hk]
          exact inv_pow_antitone_succ (k_m - 1)
        _ < (f.modulus ε_m : ℚ) := find_k'_bound (f.modulus ε_m)
    have hlt :
        |f.toFun (x.approx k_n) - f.toFun (x.approx k_m)| < 1 / 2 ^ n := by
      calc
        |f.toFun (x.approx k_n) - f.toFun (x.approx k_m)|
            ≤ |f.toFun (x.approx k_n) - f.toFun (x.approx K)| +
              |f.toFun (x.approx K) - f.toFun (x.approx k_m)| := by
                apply abs_sub_le
        _ < (ε_n:ℚ) + (ε_m:ℚ) := add_lt_add h_term_1 h_term_2
        _ = 1/2^(n+1) + 1/2^(m+1) := rfl
        _ ≤ 1/2^(n+1) + 1/2^(n+1) := by
              gcongr
              exact rfl
        _ = 1/2^n := by
              field_simp [pow_succ]; ring
    exact hlt.le

/--
Proof that the lifting mechanism respects equivalence.
-/
theorem makeCRealFunPre_respects_equiv (f : UniformCtsQQ) (x y : CReal.Pre) (hxy : CReal.Pre.Equiv x y) :
  CReal.Pre.Equiv (makeCRealFunPre f x) (makeCRealFunPre f y) := by
  intro n
  -- We need to show |(makeCRealFunPre f x).approx (n+1) - (makeCRealFunPre f y).approx (n+1)| ≤ 1/2^n.
  -- The approximations are calculated using ε' = 1/2^(n+2).
  let ε' : Gauge := ⟨(1:ℚ)/2^(n+2), by positivity⟩
  let δ' := f.modulus ε'
  let k' := find_k' δ'
  -- The approximations are f(x.approx k') and f(y.approx k').
  have h_bound : |f.toFun (x.approx k') - f.toFun (y.approx k')| < (ε':ℚ) := by
    apply f.uniform_continuity_proof ε'
    have h_k'_pos : k' > 0 := by dsimp [k', find_k']; exact Nat.succ_pos _
    have h_xy_k' : |x.approx k' - y.approx k'| ≤ 1/2^(k'-1) := by
      simpa [Nat.sub_add_cancel h_k'_pos] using hxy (k' - 1)
    calc
      |x.approx k' - y.approx k'|
        ≤ 1/2^(k'-1) := h_xy_k'
      _ < (δ':ℚ) := find_k'_bound δ'
  have hlt :
      |(makeCRealFunPre f x).approx (n+1) - (makeCRealFunPre f y).approx (n+1)| < 1 / 2 ^ n := by
    calc
      |(makeCRealFunPre f x).approx (n+1) - (makeCRealFunPre f y).approx (n+1)|
          = |f.toFun (x.approx k') - f.toFun (y.approx k')| := rfl
      _ < (ε':ℚ) := h_bound
      _ = 1/2^(n+2) := rfl
      _ ≤ 1/2^n := by
        have h1 := CReal.inv_pow_antitone_succ (n + 1)
        have h2 := CReal.inv_pow_antitone_succ n
        exact h1.trans h2
  exact hlt.le

/--
Lifts a UniformCtsQQ function to CReal.
-/
def makeCRealFun (f : UniformCtsQQ) : CReal → CReal :=
  Quotient.lift (fun x_pre => ⟦makeCRealFunPre f x_pre⟧) (by
    intro x y hxy
    apply Quotient.sound
    exact makeCRealFunPre_respects_equiv f x y hxy
  )

end Computable

-- 5. Integration Point: Elementary Functions (Based on Approach 2 Algorithms)

/-!
# Transcendental Functions

We now integrate the algorithms from the "Few Digits" approach (Approach 2).
This requires implementing the algorithms (Taylor series, argument reduction)
to produce `CReal.Pre` sequences and proving their regularity based on rigorous error analysis.
-/

-- Prerequisite functions on ℚ (from Approach 2).

/--
Generate the list of factorials: [1, 1, 1*2, 1*2*3, ...].
Returns the first `n` terms (from 0! to (n-1)!).
-/
def factorials (n : ℕ) : List ℚ :=
  let rec fact (acc i : ℚ) (k : ℕ) : List ℚ :=
    if k = 0 then [] else acc :: fact (acc * i) (i + 1) (k - 1)
  fact 1 1 n

/--
Generate the list of powers of a rational number x^0, x^1, ..., x^(n-1).
-/
def powers (x : ℚ) (n : ℕ) : List ℚ :=
  List.zipWith (fun _ k => x ^ k) (List.range n) (List.range n)

/-! ### Exponential Function (exp) -/

/--
Helper: the truncation height N(n) used for the Taylor approximation of `exp`.
We take a very simple choice: N(n) = n + 2.
-/
@[inline] def expTruncLevel (n : ℕ) : ℕ := n + 2

/-- The k-th Taylor coefficient for exp at x (as a rational). -/
@[inline] def expCoeff (x : ℚ) (k : ℕ) : ℚ :=
  x^k / (Nat.factorial k)

/-- Partial sum up to (inclusive) height `N`. -/
def expPartial (x : ℚ) (N : ℕ) : ℚ :=
  (Finset.range (N + 1)).sum (fun k => expCoeff x k)

/-- Simple factorial lower bound: for all k we have (k+1)! ≥ 2^k. -/
lemma two_pow_le_factorial_succ (k : ℕ) :
    (2 : ℕ) ^ k ≤ Nat.factorial (k + 1) := by
  -- Strong induction on k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hkpos : 2 ≤ k + 2 := by exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
      have : (2 : ℕ)^(k+1) = 2 * 2^k := by
        simp [pow_succ, Nat.mul_comm]
      calc
        (2 : ℕ) ^ (k + 1)
            = 2 * 2^k := this
        _ ≤ (k+2) * 2^k := by
              apply Nat.mul_le_mul_right
              exact hkpos
        _ ≤ (k+2) * Nat.factorial (k+1) := by
              exact Nat.mul_le_mul_left _ ih
        _ = Nat.factorial (k+2) := by
              simp [Nat.factorial_succ]

/-- Factorial inequality in ℚ form. -/
lemma two_pow_le_factorial_succ_q (k : ℕ) :
  (2 : ℚ) ^ k ≤ (Nat.factorial (k+1) : ℚ) := by
  exact_mod_cast two_pow_le_factorial_succ k

/--
Monotonic ratio bound for successive absolute Taylor terms:
If |x| ≤ 1/2 then
|x^{k+1} / (k+1)!| ≤ (1/2) * |x^k / k!|.
-/
lemma exp_term_ratio (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (k : ℕ) :
  |x^(k+1) / (Nat.factorial (k+1))| ≤ ( (1:ℚ) / 2 ) * |x^k / (Nat.factorial k)| := by
  have hkpos : 0 < (k+1 : ℚ) := by exact_mod_cast Nat.succ_pos k
  have hfacpos : 0 < (Nat.factorial k : ℚ) := by exact_mod_cast Nat.factorial_pos k
  have hsuccfacpos : 0 < (Nat.factorial (k+1) : ℚ) := by exact_mod_cast Nat.factorial_pos (k+1)
  have h_fact : (Nat.factorial (k+1) : ℚ) = (k+1 : ℚ) * Nat.factorial k := by
    norm_cast
  have h_main :
      |x^(k+1) / (Nat.factorial (k+1))|
        = (|x| / (k+1 : ℚ)) * (|x^k| / Nat.factorial k) := by
    have : x^(k+1) = x^k * x := by
      simp [pow_succ, mul_comm]
    calc
      |x^(k+1) / (Nat.factorial (k+1))|
          = |x^(k+1)| / (Nat.factorial (k+1) : ℚ) := by
                simp [abs_div, abs_of_pos hsuccfacpos]
      _ = |x^k * x| / ((k+1:ℚ) * Nat.factorial k) := by
                simp [this, h_fact]
      _ = (|x^k| * |x|) / ((k+1:ℚ) * Nat.factorial k) := by
                simp [abs_mul, mul_comm]
      _ = (|x| * |x^k|) / ((k+1:ℚ) * Nat.factorial k) := by
                ac_rfl
      _ = (|x| / (k+1:ℚ)) * (|x^k| / Nat.factorial k) := by
                field_simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hk_ge_one : (1 : ℚ) ≤ (k+1 : ℚ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have h_inv_le_one : (1 : ℚ) / (k+1 : ℚ) ≤ 1 := (div_le_one₀ hkpos).mpr hk_ge_one
  have h_abs_nonneg : 0 ≤ |x| := abs_nonneg _
  have h_div_le_abs : |x| / (k+1 : ℚ) ≤ |x| := by
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left h_inv_le_one h_abs_nonneg
  have h_div_le_half : |x| / (k+1 : ℚ) ≤ (1/2 : ℚ) := h_div_le_abs.trans hx
  have h_nonneg_right : 0 ≤ |x^k| / (Nat.factorial k : ℚ) :=
    div_nonneg (abs_nonneg _) (le_of_lt hfacpos)
  have h_mul :
      (|x| / (k+1 : ℚ)) * (|x^k| / Nat.factorial k)
        ≤ (1/2 : ℚ) * (|x^k| / Nat.factorial k) :=
    mul_le_mul_of_nonneg_right h_div_le_half h_nonneg_right
  have h_abs_div :
      |x^k / (Nat.factorial k : ℚ)| = |x^k| / Nat.factorial k := by
    simp [abs_div, abs_of_pos hfacpos]
  calc
    |x^(k+1) / (Nat.factorial (k+1))|
        = (|x| / (k+1 : ℚ)) * (|x^k| / Nat.factorial k) := h_main
    _ ≤ (1/2 : ℚ) * (|x^k| / Nat.factorial k) := h_mul
    _ = (1/2 : ℚ) * |x^k / (Nat.factorial k)| := by simp [h_abs_div]
    _ = ((1:ℚ)/2) * |x^k / (Nat.factorial k)| := rfl

@[simp] private lemma abs_pow (x : ℚ) (n : ℕ) : |x^n| = |x|^n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, abs_mul, mul_comm]

-- Closed form of the geometric sum
lemma geom_closed (u : ℕ) :
    (Finset.range u).sum (fun j => (1/2 : ℚ)^j)
      = 2 - 2 * (1/2 : ℚ)^u := by
  induction u with
  | zero =>
      simp
  | succ u ih =>
      have : (Finset.range (u + 1)).sum (fun j => (1/2 : ℚ)^j)
            = (Finset.range u).sum (fun j => (1/2 : ℚ)^j) + (1/2 : ℚ)^u := by
        simp [Finset.sum_range_succ, add_comm]
      calc
        (Finset.range (u + 1)).sum (fun j => (1/2 : ℚ)^j)
            = (Finset.range u).sum (fun j => (1/2 : ℚ)^j) + (1/2 : ℚ)^u := this
        _ = (2 - 2 * (1/2 : ℚ)^u) + (1/2 : ℚ)^u := by rw [ih]
        _ = 2 - (2 * (1/2 : ℚ)^u - (1/2 : ℚ)^u) := by ring_nf
        _ = 2 - ((2 - 1) * (1/2 : ℚ)^u) := by ring
        _ = 2 - (1/2 : ℚ)^u := by norm_num
        _ = 2 - 2 * (1/2 : ℚ)^(u+1) := by
            simp [pow_succ, mul_comm]

lemma exp_tail_le_geom (x : ℚ) (hx : |x| ≤ (1/2 : ℚ))
  (N M : ℕ) (hNM : N ≤ M) :
  |(Finset.range (M + 1)).sum (fun k => expCoeff x k) -
    (Finset.range (N + 1)).sum (fun k => expCoeff x k)| ≤
    2 * |x^(N+1) / (Nat.factorial (N+1))| := by
  let a : ℕ → ℚ := fun k => expCoeff x k
  set t := M - N
  have hM : M = N + t := (Nat.add_sub_of_le hNM).symm
  have hM_succ : M + 1 = N + t + 1 := by
    simp [hM, Nat.add_assoc]
  have tail_split :
      (Finset.range (M + 1)).sum a - (Finset.range (N + 1)).sum a
        = (Finset.range t).sum (fun j => a (N + 1 + j)) := by
    have aux :
        ∀ t, (Finset.range (N + t + 1)).sum a - (Finset.range (N + 1)).sum a
            = (Finset.range t).sum (fun j => a (N + 1 + j)) := by
      intro t'
      induction t' with
      | zero =>
          simp
      | succ t' ih =>
          have : (Finset.range (N + (t' + 1) + 1)).sum a
                = (Finset.range (N + t' + 1)).sum a + a (N + t' + 1) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using Finset.sum_range_succ (fun k => a k) (N + t' + 1)
          calc
            (Finset.range (N + (t'+1) + 1)).sum a - (Finset.range (N + 1)).sum a
                = ((Finset.range (N + t' + 1)).sum a + a (N + t' + 1))
                    - (Finset.range (N + 1)).sum a := by
                  simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
            _ = ((Finset.range (N + t' + 1)).sum a - (Finset.range (N + 1)).sum a)
                  + a (N + t' + 1) := by ring
            _ = (Finset.range t').sum (fun j => a (N + 1 + j)) + a (N + t' + 1) := by
                  simpa using congrArg id ih
            _ = (Finset.range (t' + 1)).sum (fun j => a (N + 1 + j)) := by
                  simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
    have := aux t
    simpa [hM_succ]
  have ratio : ∀ k, |a (k+1)| ≤ (1/2 : ℚ) * |a k| := by
    intro k; simpa [a] using exp_term_ratio x hx k
  -- Geometric domination of successive tail terms
  have geom_dom :
      ∀ j, |a (N + 1 + j)| ≤ (1/2 : ℚ)^j * |a (N + 1)| := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have rstep : |a (N + 1 + (j + 1))| ≤ (1/2 : ℚ) * |a (N + 1 + j)| := by
          have : (N + 1 + j) + 1 = N + 1 + (j + 1) := by
            simp [Nat.add_comm, Nat.add_left_comm]
          simpa [this] using ratio (N + 1 + j)
        calc
          |a (N + 1 + (j + 1))| ≤ (1/2 : ℚ) * |a (N + 1 + j)| := rstep
          _ ≤ (1/2 : ℚ) * ((1/2 : ℚ)^j * |a (N + 1)|) :=
                mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1/2 : ℚ)^(j+1) * |a (N + 1)| := by
                simp [pow_succ, mul_comm, mul_assoc]
  have h_abs_tail :
      |(Finset.range t).sum (fun j => a (N + 1 + j))|
        ≤ (Finset.range t).sum (fun j => |a (N + 1 + j)|) :=
    Finset.abs_sum_le_sum_abs _ _
  have h_sum_bound_pointwise :
      (Finset.range t).sum (fun j => |a (N + 1 + j)|)
        ≤ (Finset.range t).sum (fun j => (1/2 : ℚ)^j * |a (N + 1)|) := by
    refine Finset.sum_le_sum ?_
    intro j _
    have := geom_dom j
    simpa [mul_comm, mul_left_comm, mul_assoc]
  have h_factor :
      (Finset.range t).sum (fun j => (1/2 : ℚ)^j * |a (N + 1)|)
        = |a (N + 1)| * (Finset.range t).sum (fun j => (1/2 : ℚ)^j) := by
    simp [Finset.mul_sum, mul_comm]
  have geom_sum_le_two :
      (Finset.range t).sum (fun j => (1/2 : ℚ)^j) ≤ 2 := by
    have hcf := geom_closed t
    have hpow_nonneg : 0 ≤ (1/2 : ℚ)^t := by positivity
    have hterm_nonneg : 0 ≤ 2 * (1/2 : ℚ)^t := Rat.mul_nonneg rfl hpow_nonneg --mul_nonneg (by norm_num) hpow_nonneg
    have : 2 - 2 * (1/2 : ℚ)^t ≤ 2 := by
      have : 2 - 2 * (1/2 : ℚ)^t ≤ 2 - 0 := by
        gcongr
      simp
    simp_all
  have tail_bound :
      |(Finset.range t).sum (fun j => a (N + 1 + j))|
        ≤ |a (N + 1)| * (Finset.range t).sum (fun j => (1/2 : ℚ)^j) := by
    have h_chain := h_abs_tail.trans h_sum_bound_pointwise
    have h_factor' :
        (Finset.range t).sum (fun j => (1/2 : ℚ)^j * |a (N + 1)|)
          = |a (N + 1)| * (Finset.range t).sum (fun j => (1/2 : ℚ)^j) := by
      rw [Finset.mul_sum]
      congr 1
      ext j
      ring
    calc |(Finset.range t).sum (fun j => a (N + 1 + j))|
        ≤ (Finset.range t).sum (fun j => |a (N + 1 + j)|) := h_abs_tail
      _ ≤ (Finset.range t).sum (fun j => (1/2 : ℚ)^j * |a (N + 1)|) := h_sum_bound_pointwise
      _ = |a (N + 1)| * (Finset.range t).sum (fun j => (1/2 : ℚ)^j) := h_factor'
  have : |(Finset.range (M + 1)).sum a - (Finset.range (N + 1)).sum a|
        ≤ 2 * |a (N + 1)| := by
    have h_tail_rewrite :
        |(Finset.range (M + 1)).sum a - (Finset.range (N + 1)).sum a|
          = |(Finset.range t).sum (fun j => a (N + 1 + j))| := by
      simp [tail_split]
    have hgeom : |a (N + 1)| * (Finset.range t).sum (fun j => (1/2 : ℚ)^j) ≤ |a (N + 1)| * 2 :=
      mul_le_mul_of_nonneg_left geom_sum_le_two (abs_nonneg (a (N + 1)))
    calc
      |(Finset.range (M + 1)).sum a - (Finset.range (N + 1)).sum a|
          = |(Finset.range t).sum (fun j => a (N + 1 + j))| := h_tail_rewrite
      _ ≤ |a (N + 1)| * (Finset.range t).sum (fun j => (1/2 : ℚ)^j) := tail_bound
      _ ≤ |a (N + 1)| * 2 := by
            simpa [two_mul, mul_comm, mul_left_comm, mul_assoc]
              using hgeom
      _ = 2 * |a (N + 1)| := by ring
  simpa [a, expCoeff]

/--
Tail bound between truncations N(n)=n+2 and N(m)=m+2:
|expPartial x (n+2) - expPartial x (m+2)| ≤ 1 / 2^n (for n ≤ m, |x| ≤ 1/2).
-/
lemma exp_tail_bound_core (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (n m : ℕ)
  (hnm : n ≤ m) :
  |expPartial x (expTruncLevel m) - expPartial x (expTruncLevel n)| ≤ (1 : ℚ) / 2^n := by
  -- Abbreviations
  set Nn := expTruncLevel n        -- = n + 2
  set Nm := expTruncLevel m
  have hN : Nn ≤ Nm := by
    dsimp [Nn, Nm, expTruncLevel]; exact Nat.add_le_add_right hnm 2
  -- Geometric tail (already proved)
  have hgeom := exp_tail_le_geom x hx Nn Nm hN
  -- (1/2)^k = 1 / 2^k
  have half_pow : ∀ k, (1/2 : ℚ)^k = (1 : ℚ) / 2^k := by
    intro k; induction k with
    | zero => simp
    | succ k ih => simp [pow_succ, one_div]; ring_nf
  -- Bound |x|^k ≤ (1/2)^k
  have pow_abs_bound : ∀ k, |x|^k ≤ (1/2 : ℚ)^k := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      calc
        |x|^(k+1) = |x|^k * |x| := by simp [pow_succ]
        _ ≤ (1/2 : ℚ)^k * |x| := mul_le_mul_of_nonneg_right ih (abs_nonneg _)
        _ ≤ (1/2 : ℚ)^k * (1/2 : ℚ) := mul_le_mul_of_nonneg_left hx (by positivity)
        _ = (1/2 : ℚ)^(k+1) := by simp [pow_succ]
  -- |x^(Nn+1)| = |x|^(Nn+1)
  have h_abs_pow : |x^(Nn+1)| = |x|^(Nn+1) := by
    simp
  -- Factorial lower bound 2^Nn ≤ (Nn+1)!
  have hfac_nat : (2 : ℕ)^Nn ≤ Nat.factorial (Nn+1) := two_pow_le_factorial_succ Nn
  have hfac_q : (2 : ℚ)^Nn ≤ (Nat.factorial (Nn+1) : ℚ) := by exact_mod_cast hfac_nat
  have hfac_pos : 0 < (Nat.factorial (Nn+1) : ℚ) := by exact_mod_cast Nat.factorial_pos (Nn+1)
  -- Core (Nn+1)-th term bound
  have core_term :
      |x^(Nn+1) / (Nat.factorial (Nn+1))|
        ≤ (1/2 : ℚ)^(Nn+1) / (2:ℚ)^Nn := by
    have num_le : |x^(Nn+1)| ≤ (1/2 : ℚ)^(Nn+1) := by
      simpa [h_abs_pow] using pow_abs_bound (Nn+1)
    have : |x^(Nn+1) / (Nat.factorial (Nn+1) : ℚ)|
            = |x^(Nn+1)| / (Nat.factorial (Nn+1) : ℚ) := by
      simp [abs_div, abs_of_pos hfac_pos]
    have hinv :
        (Nat.factorial (Nn+1) : ℚ)⁻¹ ≤ ((2:ℚ)^Nn)⁻¹ := by
      have hpow_pos : 0 < (2:ℚ)^Nn := pow_pos (by norm_num) _
      exact inv_anti₀ hpow_pos hfac_q-- inv_le_inv_of_le hpow_pos hfac_q
    calc
      |x^(Nn+1) / (Nat.factorial (Nn+1))|
          = |x^(Nn+1)| / (Nat.factorial (Nn+1) : ℚ) := this
      _ = |x^(Nn+1)| * ((Nat.factorial (Nn+1):ℚ)⁻¹) := by simp [div_eq_mul_inv]
      _ ≤ (1/2 : ℚ)^(Nn+1) * ((Nat.factorial (Nn+1):ℚ)⁻¹) :=
            mul_le_mul_of_nonneg_right num_le (by positivity)
      _ ≤ (1/2 : ℚ)^(Nn+1) * ((2:ℚ)^Nn)⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (1/2 : ℚ)^(Nn+1) / (2:ℚ)^Nn := by simp [div_eq_mul_inv]
  -- Simplify RHS
  have simpl :
      (1/2 : ℚ)^(Nn+1) / (2:ℚ)^Nn = (1 : ℚ) / 2^(2*Nn + 1) := by
    have h1 : (1/2 : ℚ)^(Nn+1) = (1 : ℚ) / 2^(Nn+1) := half_pow (Nn+1)
    calc
      (1/2 : ℚ)^(Nn+1) / (2:ℚ)^Nn
          = ((1:ℚ)/2^(Nn+1)) / 2^Nn := by simp
      _ = (1:ℚ) / (2^(Nn+1) * 2^Nn) := by simp [div_eq_mul_inv]; ring_nf
      _ = (1:ℚ) / 2^((Nn+1)+Nn) := by simp [pow_add]
      _ = (1:ℚ) / 2^(2*Nn + 1) := by ring_nf
  have core_term' :
      |x^(Nn+1) / (Nat.factorial (Nn+1))| ≤ (1 : ℚ) / 2^(2*Nn + 1) := by
    rw [simpl] at core_term
    exact core_term
  -- 2 * |term| ≤ 1 / 2^(2*Nn)
  have two_mul_term :
      2 * |x^(Nn+1) / (Nat.factorial (Nn+1))|
        ≤ (1 : ℚ) / 2^(2*Nn) := by
    have hsplit :
        (1:ℚ)/2^(2*Nn + 1) = ((1:ℚ)/2^(2*Nn)) * (1/2 : ℚ) := by
      -- 1 / 2^(k+1) = (1 / 2^k) * (1/2)
      simp [pow_succ, one_div, mul_comm]
    have : 2 * ((1:ℚ)/2^(2*Nn + 1)) = (1:ℚ) / 2^(2*Nn) := by
      -- 2 * (1 / 2^(k+1)) = 1 / 2^k
      have : (2:ℚ) * (1 / 2^(2*Nn + 1)) = (1:ℚ) / 2^(2*Nn) := by
        simp [pow_succ, one_div, mul_comm]
      simpa [two_mul, one_div, hsplit, mul_comm, mul_left_comm, mul_assoc]
    calc
      2 * |x^(Nn+1) / (Nat.factorial (Nn+1))|
          ≤ 2 * ((1:ℚ)/2^(2*Nn + 1)) :=
            mul_le_mul_of_nonneg_left core_term' (by norm_num)
      _ = (1:ℚ) / 2^(2*Nn) := this
  -- Combine geometric tail bound and factorial/power bound
  have diff_bound :
      |expPartial x Nm - expPartial x Nn| ≤ (1 : ℚ) / 2^(2*Nn) :=
    hgeom.trans two_mul_term
  -- Show n ≤ 2*Nn (since Nn = n+2 ⇒ 2*Nn = 2n+4)
  have n_le_2Nn : n ≤ 2 * Nn := by
    dsimp [Nn, expTruncLevel]
    -- Need: n ≤ 2*(n+2) = 2n+4
    have h1 : n ≤ n + n := Nat.le_add_right _ _
    have h2 : n + n ≤ n + n + 4 := Nat.le_add_right _ _
    have : n ≤ n + n + 4 := Nat.le_trans h1 h2
    simp [two_mul, add_comm, add_left_comm]
  -- Monotonicity of inverse powers: if a ≤ b then 1/2^b ≤ 1/2^a
  have one_div_pow_mono :
      ∀ {a b : ℕ}, a ≤ b → (1:ℚ)/2^b ≤ (1:ℚ)/2^a := by
    intro a b h
    have hpow : (2:ℚ)^a ≤ (2:ℚ)^b :=
      (pow_le_pow_iff_right₀ (by norm_num)).mpr h
    have hpos : 0 < (2:ℚ)^a := pow_pos (by norm_num) _
    exact one_div_le_one_div_of_le hpos hpow
  have final_step : (1:ℚ)/2^(2*Nn) ≤ (1:ℚ) / 2^n :=
    one_div_pow_mono n_le_2Nn
  exact diff_bound.trans final_step

/--
Final definition: pre-real for exp(x) when |x| ≤ 1/2, with regularity.
We use the Taylor polynomial up to degree N(n) = n + 2 at index n.
-/
def small_exp (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) : CReal.Pre :=
{ approx := fun n => expPartial x (expTruncLevel n)
  , is_regular := by
      intro n m hnm
      -- Use the tail bound lemma, applying abs_sub_comm to match the required order
      have h := exp_tail_bound_core x hx n m hnm
      simpa [one_div, abs_sub_comm] using h
}

/-- Cast the partial exponential sum to ℝ. -/
def expPartialR (x : ℚ) (N : ℕ) : ℝ := (expPartial x N : ℚ)
end Pre
end CReal
end Computable
