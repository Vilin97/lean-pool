/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Local.Entry
public import LeanPool.Zeta32.Arith.Profiles
public import LeanPool.Zeta32.Arith.Local.Alloc

/-! the proof notes, §3 Lemma 4 (greedy lower bound), proved by class-wise partial fractions
(Zeta32/Arith/Local/) instead of the Tate-algebra functional of the proof notes, §§1–2.

With the greedy allocation `galloc n p (3n)` and the monic basis
`f_i = ∏_{b<p} (t+b)^{galloc n p i b}`, every entry `U_r(f_i f_k R_n)` has `v_p ≥ (π_i + π_k)/2`
coefficientwise in `X` (`entry_GV`), so `v_p(Q_n) ≥ ∑ π_i = allocCost` (`Q_GV`). The only
hypotheses used are `p` prime, `p ∤ den r` and `5n < p²`; condition (D), `p ≥ 5` and `p > K`
of the proof notes, Lemma 4 are not needed by this route. `5n < p²` follows from `n^{2/3} < p` for
`n ≥ 125`. -/

/-! the proof notes, §1, Lemma 1 and Corollary 2.

Route change: the Tate-algebra distribution formula is not
formalized. The local bounds it served (the proof notes, Lemma 3, Lemma 4) are proved directly by
class-wise partial fractions: `Zeta32.Arith.Local.VG_polynomialMoment` (Local/Binom.lean,
the polynomial part of `U_r`), `Zeta32.Arith.Local.VG_res`, `VG_polyPart_eval`
(Local/PoleFun.lean) and `Zeta32.Arith.Local.Lfun_GV` (Local/Entry.lean). -/

public section

open Filter Polynomial Finset

namespace Zeta32.Arith.Local

lemma VG_of_not_dvd_den {p : ℕ} {r : ℚ} (h : ¬ p ∣ r.den) : VG p r 0 := by
  right
  have : (0 : ℤ) ≤ padicValRat p r := by
    rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd h]
    simp
  exact_mod_cast this

lemma natDegree_D_le (m : ℕ) : (Zeta32.D m).natDegree ≤ m := by
  unfold Zeta32.D
  refine (natDegree_prod_le _ _).trans ?_
  rw [Finset.sum_congr rfl fun j _ => natDegree_X_add_C ((j : ℕ) : ℚ)]
  simp

lemma card_plc_Pl5 {p : ℕ} [Fact p.Prime] (n : ℕ) (c : ZMod p) :
    (plc p (Pl5 n) c).card =
      ((Finset.Icc 1 (5 * n)).filter fun j : ℕ => j % p = (-c).val).card := by
  unfold plc Pl5
  rw [Finset.filter_image, Finset.card_image_of_injective _ neg_natCast_injective]
  exact card_class (5 * n) c

/-- The entry bound `v_p(U_r(f_i f_k R_n)) ≥ (π_i + π_k)/2`. -/
theorem entry_GV {r : ℚ} {n p : ℕ} [hp : Fact p.Prime] (hr : VG p r 0) (hn : 5 * n < p ^ 2)
    (i k : Fin (3 * n)) :
    GV p (Lfun r n (gbasis n p i * gbasis n p k * Zeta32.D n ^ 4))
      ((gval n p i : ℚ) / 2 + (gval n p k : ℚ) / 2) := by
  have hp0 : 0 < p := hp.out.pos
  have hA : Adm p (gbasis n p i * gbasis n p k * Zeta32.D n ^ 4)
      (fun c => (galloc n p i (-c).val : ℤ) + (galloc n p k (-c).val : ℤ) +
        4 * (((Finset.Icc 1 n).filter fun j : ℕ => j % p = (-c).val).card : ℤ)) := by
    refine (((Adm_gbasis (n := n) (p := p) i).mul (Adm_gbasis (n := n) (p := p) k)).mul
      ((Adm_D (p := p) n).pow 4)).mono fun c => le_of_eq ?_
    simp [Pi.add_apply]
  have hdeg : (gbasis n p i * gbasis n p k * Zeta32.D n ^ 4).natDegree + 2 ≤ 10 * n := by
    have h1 := natDegree_mul_le (p := gbasis n p i * gbasis n p k) (q := Zeta32.D n ^ 4)
    have h2 := natDegree_mul_le (p := gbasis n p i) (q := gbasis n p k)
    have h3 := natDegree_pow_le (p := Zeta32.D n) (n := 4)
    have h4 := natDegree_D_le n
    rw [gbasis_natDegree hp0, gbasis_natDegree hp0] at h2
    have := i.isLt
    have := k.isLt
    omega
  have key := Lfun_GV hr hn hA hdeg ((gval n p i : ℚ) / 2 + (gval n p k : ℚ) / 2 + 2)
    (fun c => by
      have hb := neg_val_lt (p := p) c
      have h1 := gval_le (n := n) hp0 i hb
      have h2 := gval_le (n := n) hp0 k hb
      rw [card_plc_Pl5]
      unfold colVal at h1 h2
      have hz : (-c).val = 0 ↔ c = 0 := neg_val_eq_zero_iff c
      by_cases hc : c = 0
      · rw [ite_eq_left hc]
        rw [ite_eq_left (hz.mpr hc)] at h1 h2
        have h1q := (Int.cast_le (R := ℚ)).mpr h1
        have h2q := (Int.cast_le (R := ℚ)).mpr h2
        push_cast at h1q h2q ⊢
        linarith
      · rw [ite_eq_right hc]
        rw [ite_eq_right (fun h => hc (hz.mp h))] at h1 h2
        have h1q := (Int.cast_le (R := ℚ)).mpr h1
        have h2q := (Int.cast_le (R := ℚ)).mpr h2
        push_cast at h1q h2q ⊢
        linarith)
  exact key.mono (by linarith)

/-- **the proof notes, Lemma 4**: `v_p(Q_n) ≥ allocCost` for the greedy allocation. -/
theorem Q_GV {r : ℚ} {n p : ℕ} [hp : Fact p.Prime] (hr : ¬ p ∣ r.den) (hn : 5 * n < p ^ 2) :
    GV p (Zeta32.Q r n) (allocCost n p (galloc n p (3 * n))) := by
  have hp0 : 0 < p := hp.out.pos
  rw [Q_eq_det_basis r n (fun i => gbasis n p i) (fun i => gbasis_monic i)
    (fun i => gbasis_natDegree hp0 i)]
  have hdet := det_GV (p := p) (Matrix.of fun i k : Fin (3 * n) =>
      Lfun r n (gbasis n p i * gbasis n p k * Zeta32.D n ^ 4))
    (fun i => (gval n p i : ℚ) / 2) (fun k => (gval n p k : ℚ) / 2)
    (fun i k => by
      rw [Matrix.of_apply]
      exact entry_GV (VG_of_not_dvd_den hr) hn i k)
  refine hdet.mono (le_of_eq ?_)
  rw [allocCost_galloc hp0, ← Fin.sum_univ_eq_sum_range, ← Finset.sum_add_distrib]
  push_cast
  refine Finset.sum_congr rfl fun i _ => by ring

theorem greedyBound_of_sq {r : ℚ} {n p : ℕ} [hp : Fact p.Prime] (hr : ¬ p ∣ r.den)
    (hn : 5 * n < p ^ 2) : GreedyBound r n p := by
  have hp0 : 0 < p := hp.out.pos
  refine ⟨galloc n p (3 * n), sum_galloc hp0 _, fun i hi => ?_⟩
  exact ((Q_GV hr hn) i).resolve_left hi

/-- `n^{2/3} < p` gives `5n < p²` once `n ≥ 125`. -/
lemma five_mul_lt_sq {n p : ℕ} (hn : 125 ≤ n) (h : (n : ℝ) ^ (2 / 3 : ℝ) < p) :
    5 * n < p ^ 2 := by
  have h3 : (n : ℝ) ^ 2 < (p : ℝ) ^ 3 := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have := pow_lt_pow_left₀ h hnn (by norm_num : (3 : ℕ) ≠ 0)
    rw [← Real.rpow_natCast ((n : ℝ) ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul (Nat.cast_nonneg n)]
      at this
    have e : (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rwa [e, Real.rpow_natCast] at this
  have h3' : n ^ 2 < p ^ 3 := by exact_mod_cast h3
  by_contra hle
  push Not at hle
  have h1 : (p ^ 2) ^ 3 ≤ (5 * n) ^ 3 := Nat.pow_le_pow_left hle 3
  have h2 : (n ^ 2) ^ 2 < (p ^ 3) ^ 2 := Nat.pow_lt_pow_left h3' (by norm_num)
  have h4 : 125 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
  have a : n ^ 4 < p ^ 6 := by
    calc n ^ 4 = (n ^ 2) ^ 2 := by ring
      _ < (p ^ 3) ^ 2 := h2
      _ = p ^ 6 := by ring
  have b : p ^ 6 ≤ 125 * n ^ 3 := by
    calc p ^ 6 = (p ^ 2) ^ 3 := by ring
      _ ≤ (5 * n) ^ 3 := h1
      _ = 125 * n ^ 3 := by ring
  have c : 125 * n ^ 3 ≤ n ^ 4 := by
    calc 125 * n ^ 3 ≤ n * n ^ 3 := h4
      _ = n ^ 4 := by ring
  exact absurd (lt_of_lt_of_le a (b.trans c)) (lt_irrefl _)

end Zeta32.Arith.Local

namespace Zeta32.Arith

open Local

/-- the proof notes, Lemma 4 in allocation form, for `n^{2/3} < p ≤ 5n`. -/
theorem greedy_valuation_bound (r : ℚ) : ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, p.Prime →
    (n:ℝ)^(2/3:ℝ) < p → p ≤ 5*n → ¬ p ∣ r.den → GreedyBound r n p := by
  filter_upwards [eventually_ge_atTop 125] with n hn p hp hlow _ hden
  have := Fact.mk hp
  exact greedyBound_of_sq hden (five_mul_lt_sq hn hlow)

end Zeta32.Arith

end
