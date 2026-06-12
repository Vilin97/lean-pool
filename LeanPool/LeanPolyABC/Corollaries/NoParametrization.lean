/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/

import Mathlib.FieldTheory.RatFunc.AsPolynomial

import LeanPool.LeanPolyABC.Corollaries.FltCatalan

/-!
# LeanPool.LeanPolyABC.Corollaries.NoParametrization
-/

noncomputable section

open scoped Polynomial

open RatFunc

namespace LeanPolyABC

variable {k : Type _} [Field k]

/-- A rational function is constant if it equals `RatFunc.C c` for some scalar `c`. -/
def IsConst (x : RatFunc k) :=
  ∃ c : k, x = RatFunc.C c

theorem associates_pow_eq_pow_iff {A B : Associates k[X]} {n : ℕ} (hn : n ≠ 0) :
    A ^ n = B ^ n ↔ A = B := by
  classical
  by_cases hA : A = 0
  · subst hA
    rw [zero_pow hn, eq_comm, pow_eq_zero_iff hn, eq_comm]
  by_cases hB : B = 0
  · subst hB
    rw [zero_pow hn, pow_eq_zero_iff hn]
  · constructor
    swap
    · intro h; subst h; rfl
    · intro h
      apply Associates.eq_of_eq_counts hA hB
      intro p hp
      apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_ne_zero hn)
      rw [← Associates.count_pow hA hp n, ← Associates.count_pow hB hp n, h]

theorem isConst_of_associated {f : RatFunc k} (h : Associated f.num f.denom) : IsConst f := by
  rcases h.symm with ⟨u, heq⟩
  rcases Polynomial.isUnit_iff.mp u.isUnit with ⟨c, _, eq_c⟩
  rw [← eq_c] at heq
  have tt := congr_arg (algebraMap (Polynomial k) (RatFunc k)) heq.symm
  rw [map_mul, mul_comm] at tt
  have uu := div_eq_of_eq_mul (algebraMap_ne_zero f.denom_ne_zero) tt
  rw [f.num_div_denom, RatFunc.algebraMap_C] at uu
  exact ⟨c, uu⟩

theorem isConst_of_root_unity {n : ℕ} (hn : n ≠ 0) {f : RatFunc k} (h : f ^ n = 1) : IsConst f := by
  rw [← f.num_div_denom, div_pow, ← map_pow, ← map_pow] at h
  have nz : algebraMap k[X] (RatFunc k) (f.denom ^ n) ≠ 0 := by
    apply algebraMap_ne_zero; apply pow_ne_zero; exact f.denom_ne_zero
  rw [← mul_left_inj' nz, div_mul_cancel₀ (algebraMap k[X] (RatFunc k) (f.num ^ n)) nz,
    one_mul] at h
  have hh := congr_arg Associates.mk (algebraMap_injective k h)
  rw [Associates.mk_pow, Associates.mk_pow, associates_pow_eq_pow_iff hn,
    Associates.mk_eq_mk_iff_associated] at hh
  exact isConst_of_associated hh

theorem associated_pow_pow_coprime_iff {a b : k[X]} {m n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (_hm : m ≠ 0) (hn : n ≠ 0) (h : Associated (a ^ m) (b ^ n)) (hcp : m.Coprime n) :
    ∃ c : k[X], c ≠ 0 ∧ Associated a (c ^ n) ∧ Associated b (c ^ m) := by
  classical
  -- change to associates
  simp_rw [← Associates.mk_eq_mk_iff_associated, Associates.mk_pow] at h ⊢
  rw [← Associates.mk_ne_zero] at ha hb
  set A := Associates.mk a with eq_A
  set B := Associates.mk b with eq_B
  rename' ha => hA; rename' hb => hB
  clear_value A B; clear eq_A eq_B
  suffices goal : ∃ C, A = C ^ n ∧ B = C ^ m by
    rcases goal with ⟨C, hC⟩
    refine ⟨C.out, ?_, ?_⟩
    · rw [← Associates.mk_ne_zero, Associates.mk_out, ← pow_ne_zero_iff hn, ← hC.1]
      exact hA
    · simp only [Associates.mk_out]; exact hC
  have subgoal : ∃ C, A = C ^ n := by
    apply Associates.is_pow_of_dvd_count hA
    intro p hp
    apply hcp.symm.dvd_of_dvd_mul_left
    rw [← Associates.count_pow hA hp, h, Associates.count_pow hB hp]
    exact Nat.dvd_mul_right _ _
  rcases subgoal with ⟨C, eq_ACn⟩
  refine ⟨C, eq_ACn, ?_⟩
  rw [eq_ACn, pow_right_comm, associates_pow_eq_pow_iff hn] at h
  exact h.symm

-- Auxiliary steps
theorem calcstep {n N m M : k[X]} (nz_M : M ≠ 0) (nz_N : N ≠ 0)
    (eqn :
      (algebraMap _ (RatFunc k)) n ^ 2 / (algebraMap _ (RatFunc k)) N ^ 2 =
        (algebraMap _ (RatFunc k)) m ^ 3 / (algebraMap _ (RatFunc k)) M ^ 3 + 1) :
    n ^ 2 * M ^ 3 = (m ^ 3 + M ^ 3) * N ^ 2 := by
  have nz_rM := RatFunc.algebraMap_ne_zero nz_M
  have nz_rN := RatFunc.algebraMap_ne_zero nz_N
  rw [← (RatFunc.algebraMap_injective k).eq_iff]
  simp_rw [RingHom.map_mul, RingHom.map_add, RingHom.map_pow]
  set rm := algebraMap k[X] (RatFunc k) m with eq_rm
  set rM := algebraMap k[X] (RatFunc k) M with eq_rM
  set rn := algebraMap k[X] (RatFunc k) n with eq_rn
  set rN := algebraMap k[X] (RatFunc k) N with eq_rN
  rw [eq_rm, eq_rM, eq_rn, eq_rN]
  calc
    rn ^ 2 * rM ^ 3 = rn ^ 2 / rN ^ 2 * rN ^ 2 * rM ^ 3 := by
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 nz_rN)]
    _ = (rm ^ 3 / rM ^ 3 + 1) * rM ^ 3 * rN ^ 2 := by
      rw [eqn, mul_assoc, mul_assoc, mul_comm (rN ^ 2) _]
    _ = (rm ^ 3 + rM ^ 3) * rN ^ 2 := by
      rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 3 nz_rM), one_mul]

theorem calcstep2 {m M n N : k[X]} (nz_M : M ≠ 0) (nz_N : N ≠ 0) (cp_mM : IsCoprime m M)
    (cp_nN : IsCoprime n N) (_nz_m : m ≠ 0) (_nz_n : n ≠ 0)
    (flat_eqn : n ^ 2 * M ^ 3 = (m ^ 3 + M ^ 3) * N ^ 2) :
    ∃ (w : k[X]) (u v : k[X]ˣ),
      w ≠ 0 ∧
        ↑u * w ^ 2 = M ∧
          ↑v * w ^ 3 = N ∧
            IsCoprime m w ∧ (↑u) ^ 3 * n ^ 2 = (↑v) ^ 2 * m ^ 3 + (↑v) ^ 2 * (↑u) ^ 3 * w ^ 6 := by
  have assoc_M3_N2 : Associated (M ^ 3) (N ^ 2) := by
    refine associated_of_dvd_dvd ?_ ?_
    · have cp : IsCoprime (M ^ 3) (m ^ 3 + 1 * M ^ 3) := cp_mM.symm.pow.add_mul_right_right 1
      rw [one_mul] at cp
      apply cp.dvd_of_dvd_mul_left
      rw [← flat_eqn]; exact dvd_mul_left _ _
    · have cp : IsCoprime (N ^ 2) (n ^ 2) := cp_nN.symm.pow
      apply cp.dvd_of_dvd_mul_left
      rw [flat_eqn]; exact dvd_mul_left _ _
  rcases associated_pow_pow_coprime_iff nz_M nz_N (by decide) (by decide) assoc_M3_N2 (by decide)
    with ⟨w, nz_w, assoc_M_w2, assoc_N_w3⟩
  rcases assoc_M_w2.symm with ⟨u, eq_Mw⟩; rw [mul_comm] at eq_Mw
  rcases assoc_N_w3.symm with ⟨v, eq_Nw⟩; rw [mul_comm] at eq_Nw
  refine ⟨w, u, v, nz_w, eq_Mw, eq_Nw, ?_⟩
  simp_rw [← eq_Mw, ← eq_Nw, mul_pow, ← pow_mul, ← mul_assoc] at flat_eqn
  simp only [Nat.reduceMul, mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    pow_eq_zero_iff] at flat_eqn
  constructor
  · rw [← eq_Mw, isCoprime_mul_unit_left_right u.isUnit, IsCoprime.pow_right_iff] at cp_mM
    · exact cp_mM
    · decide
  · rcases flat_eqn with eqn | w0
    · convert eqn using 1 <;> ring_nf
    · contradiction

-- Main corollary
theorem no_parametrization_y2_x3_1 (chk : ¬ringChar k ∣ 6) {x y : RatFunc k}
    (eqn : y ^ 2 = x ^ 3 + 1) : IsConst x ∧ IsConst y := by
  rcases eq_or_ne x 0 with eq_x | nz_x
  · subst x
    rw [zero_pow (by decide), zero_add] at eqn
    refine ⟨⟨0, (map_zero _).symm⟩, isConst_of_root_unity (by decide) eqn⟩
  rcases eq_or_ne y 0 with eq_y | nz_y
  · subst y; rw [eq_comm, zero_pow (by decide), ← eq_neg_iff_add_eq_zero] at eqn
    have tt : (x ^ 3) ^ 2 = 1 := by rw [sq_eq_one_iff]; right; exact eqn
    ring_nf at tt
    refine ⟨isConst_of_root_unity (by decide) tt, ⟨0, (map_zero _).symm⟩⟩
  have eq_x := x.num_div_denom.symm
  have eq_y := y.num_div_denom.symm
  have nz_m := num_ne_zero nz_x
  have nz_n := num_ne_zero nz_y
  have nz_M := x.denom_ne_zero
  have nz_N := y.denom_ne_zero
  have cp_mM := isCoprime_num_denom x
  have cp_nN := isCoprime_num_denom y
  set m := x.num
  set M := x.denom
  set n := y.num
  set N := y.denom
  clear_value m M n N
  rw [eq_x, eq_y] at eqn
  simp only [div_pow] at eqn
  subst eq_x; subst eq_y
  have flat_eqn : n ^ 2 * M ^ 3 = (m ^ 3 + M ^ 3) * N ^ 2 := by apply calcstep <;> assumption
  clear eqn
  have eqn2 :
    ∃ (w : k[X]) (u v : k[X]ˣ),
      w ≠ 0 ∧
        ↑u * w ^ 2 = M ∧
          ↑v * w ^ 3 = N ∧
            IsCoprime m w ∧ (↑u) ^ 3 * n ^ 2 = (↑v) ^ 2 * m ^ 3 + (↑v) ^ 2 * (↑u) ^ 3 * w ^ 6 := by
    apply calcstep2 <;> assumption
  clear flat_eqn
  rcases eqn2 with ⟨w, u, v, nz_w, eq_M, eq_N, cp_mw, eqn2⟩
  have chk2 : ¬ringChar k ∣ 2 := by intro h; apply chk; apply h.trans; exact ⟨3, by norm_num⟩
  have chk3 : ¬ringChar k ∣ 3 := by intro h; apply chk; apply h.trans; exact ⟨2, by norm_num⟩
  rw [eq_comm, ← sub_eq_zero, sub_eq_add_neg, ← neg_mul] at eqn2
  obtain ⟨u0, hu0, eq_u0⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨v0, hv0, eq_v0⟩ := Polynomial.isUnit_iff.mp v.isUnit
  rw [isUnit_iff_ne_zero] at hu0 hv0
  simp_rw [← eq_u0, ← eq_v0, ← map_pow, ← map_mul, ← map_neg] at eqn2
  have deriv_eq_zero := Polynomial.flt_catalan
    (by decide) (by decide) (by decide) (by decide)
    chk3 chk chk2 nz_m nz_w nz_n cp_mw ?nz0 ?nz1 ?nz2
    (by convert eqn2)
  case nz0 => exact pow_ne_zero 2 hv0
  case nz1 => exact mul_ne_zero (pow_ne_zero 2 hv0) (pow_ne_zero 3 hu0)
  case nz2 => exact neg_ne_zero.mpr (pow_ne_zero 3 hu0)
  rcases deriv_eq_zero with ⟨eq_dm, eq_dw, eq_dn⟩
  constructor
  · rw [Polynomial.eq_C_of_natDegree_eq_zero eq_dm]
    rw [← eq_M]; rw [Polynomial.eq_C_of_natDegree_eq_zero eq_dw]
    rcases Polynomial.isUnit_iff.mp u.isUnit with ⟨cu, -, eq_cu⟩
    rw [← eq_cu]
    rw [← map_pow, ← map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C, ← map_div₀, IsConst]
    exact ⟨_, rfl⟩
  · rw [Polynomial.eq_C_of_natDegree_eq_zero eq_dn]
    rw [← eq_N]; rw [Polynomial.eq_C_of_natDegree_eq_zero eq_dw]
    rcases Polynomial.isUnit_iff.mp v.isUnit with ⟨cv, -, eq_cv⟩
    rw [← eq_cv]
    rw [← map_pow, ← map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C, ← map_div₀, IsConst]
    exact ⟨_, rfl⟩

end LeanPolyABC
