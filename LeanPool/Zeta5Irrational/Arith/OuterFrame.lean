/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.Val
public import LeanPool.Zeta5Irrational.Construction
import LeanPool.Zeta5Irrational.Arith.ClassFrame
import LeanPool.Zeta5Irrational.Arith.LowRank
import LeanPool.Zeta5Irrational.Arith.MomentVal
import LeanPool.Zeta5Irrational.Arith.Unimodular
import LeanPool.Zeta5Irrational.PartialFractions
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Rat.Star
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic

/-! # The outer-range framework

`μ = μ_{<} + μ_{≥}` where `μ_{≥}` collects the moments `μ(t^e)` with `e ≥ 2p - 3` (which may have
`v_p = -1`). In any basis the `μ_{≥}`-part of the Hankel matrix has rank `≤ r` and is `p⁻¹` times
an integral product `U V`; with weights `w ≤ 0` for the integral part this gives
`v_p^G(Δ) ≥ 2 ∑ w - r`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

/-- The moments `e ≥ 2p - 3` of a polynomial. -/
@[expose] noncomputable def μGe (p : ℕ) (Q : ℚ[X]) : ℚ :=
  ∑ e ∈ range (Q.natDegree + 1), if 2 * p ≤ e + 3 then Q.coeff e * μmono e else 0

lemma μGe_eq (p : ℕ) (Q : ℚ[X]) {N : ℕ} (hN : Q.natDegree < N) :
    μGe p Q = ∑ e ∈ range N, if 2 * p ≤ e + 3 then Q.coeff e * μmono e else 0 := by
  unfold μGe
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
  intro e _ he
  rw [Finset.mem_range] at he
  rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp

omit hp in
lemma μGe_add (P Q : ℚ[X]) : μGe p (P + Q) = μGe p P + μGe p Q := by
  set N := max (max P.natDegree Q.natDegree) (P + Q).natDegree + 1 with hN
  rw [μGe_eq p (P + Q) (N := N) (by omega), μGe_eq p P (N := N) (by omega),
    μGe_eq p Q (N := N) (by omega), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [add_mul]

omit hp in
lemma μGe_C_mul (c : ℚ) (Q : ℚ[X]) : μGe p (C c * Q) = c * μGe p Q := by
  set N := max Q.natDegree (C c * Q).natDegree + 1 with hN
  rw [μGe_eq p (C c * Q) (N := N) (by omega), μGe_eq p Q (N := N) (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [coeff_C_mul]; ring

omit hp in
lemma μGe_eq_zero {Q : ℚ[X]} (hQ : Q.natDegree + 3 < 2 * p) : μGe p Q = 0 := by
  unfold μGe
  refine Finset.sum_eq_zero fun e he => ?_
  rw [Finset.mem_range] at he
  rw [ite_eq_right (by omega)]

lemma VG_p_μGe (hp5 : 5 ≤ p) {Q : ℚ[X]} (hQ : GV p Q 0) : VG p ((p : ℚ) * μGe p Q) 0 := by
  have h : VG p (μGe p Q) (-1) := by
    unfold μGe
    refine VG.sum _ fun e _ => ?_
    split_ifs
    · simpa using (hQ e).mul (VG_μmono hp5 e)
    · exact VG.zero _
  simpa using (VG.primePow (p := p) 1).mul h

omit hp in
/-- The quotient of an integer polynomial by `D_K` has integral coefficients. -/
lemma GV_divByMonic_D (K : ℕ) (Pz : ℤ[X]) : GV p (Pz.map (Int.castRingHom ℚ) /ₘ D K) 0 := by
  have hD : D K = (tpolZ ((Icc 1 K).val.map fun j : ℕ => (j : ℤ))).map (Int.castRingHom ℚ) := by
    rw [tpolZ_map_Q, D_eq_tpol]
  have hmon : (tpolZ ((Icc 1 K).val.map fun j : ℕ => (j : ℤ))).Monic := by
    unfold tpolZ
    exact monic_multiset_prod_of_monic _ _ fun γ _ => monic_X_add_C _
  rw [hD, ← map_divByMonic _ hmon]
  intro n
  rw [coeff_map]
  exact VG.intCast _

omit hp in
lemma μGe_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    μGe p (∑ i ∈ s, f i) = ∑ i ∈ s, μGe p (f i) := by
  classical
    induction s using Finset.induction_on with
  | empty => simp [μGe]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, μGe_add, ih]

lemma divByMonic_sum' {q : ℚ[X]} (hq : q.Monic) {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    (∑ i ∈ s, f i) /ₘ q = ∑ i ∈ s, f i /ₘ q := by
  classical
    induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, divByMonic_add' hq, ih]

lemma D_pow_mul_X_pow_int (N e : ℕ) : ∃ Pz : ℤ[X], Pz.map (Int.castRingHom ℚ) = D N ^ 6 * X ^ e :=
  by
  refine ⟨tpolZ ((Icc 1 N).val.map fun j : ℕ => (j : ℤ)) ^ 6 * X ^ e, ?_⟩
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X, tpolZ_map_Q,
    D_eq_tpol]

/-- **The outer-range framework.** -/
theorem outer_frame (hp5 : 5 ≤ p) (n : ℕ) (Ez : Fin (37 * n) → ℤ[X])
    (hdegZ : ∀ s, (Ez s).natDegree < 37 * n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ZMod p) (hγ : Function.Injective γ) (Lc : ι → ℕ) (cls : Fin (37 * n) → ι)
    (idx : Fin (37 * n) → ℕ) (hidx : ∀ a, idx a < Lc (cls a))
    (hinj : ∀ a b, cls a = cls b → idx a = idx b → a = b)
    (hred :
      ∀ a,
        (Ez a).map (Int.castRingHom (ZMod p)) =
          (∏ c ∈ Finset.univ.erase (cls a), (X - C (γ c)) ^ Lc c) * (X - C (γ (cls a))) ^ idx a)
    (w : Fin (37 * n) → ℚ) (hw : ∀ s, w s ≤ 0)
    (hA :
      ∀ s t,
        GV p
          (μX (40 * n)
              (D (3 * n) ^ 6 * (Ez s).map (Int.castRingHom ℚ) * (Ez t).map (Int.castRingHom ℚ)) -
            C
              (μGe p
                ((D (3 * n) ^ 6 * (Ez s).map (Int.castRingHom ℚ) *
                    (Ez t).map (Int.castRingHom ℚ)) /ₘ
                  D (40 * n))))
          (w s + w t)) :
    GV p (Δ n) (2 * ∑ s, w s - ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)) := by
  classical
  set k0 := (2 * p + 22 * n - 3) - (37 * n - 1) with hk0
  set r := 37 * n - k0 with hr
  set E : Fin (37 * n) → ℚ[X] := fun s => (Ez s).map (Int.castRingHom ℚ) with hE
  have hdegE : ∀ s, (E s).natDegree < 37 * n := fun s => (natDegree_map_le).trans_lt (hdegZ s)
  have hunit := coeffMat_det_unit Ez hdegZ γ hγ Lc cls idx hidx hinj hred
  set dC := (coeffMat E).det with hdC
  have hbc := det_basis_change n E hdegE
  set Cq := coeffMat E with hCq
  have hCqint : ∀ s k, VG p (Cq s k) 0 := fun s k => by
    simp only [hCq, coeffMat, Matrix.of_apply, hE, coeff_map]; exact VG.intCast _
  set β0 : ℕ → ℚ := fun e => μGe p ((D (3 * n) ^ 6 * X ^ e) /ₘ D (40 * n)) with hβ0
  have hβ0int : ∀ e, VG p ((p : ℚ) * β0 e) 0 := fun e =>
    by
    obtain ⟨Pz, hPz⟩ := D_pow_mul_X_pow_int (3 * n) e
    have := GV_divByMonic_D (p := p) (40 * n) Pz
    rw [hPz] at this
    exact VG_p_μGe hp5 this
  have hβ0zero : ∀ e, e + 18 * n < 2 * p - 3 + 40 * n → β0 e = 0 := by
    intro e he
    apply μGe_eq_zero
    rw [natDegree_divByMonic _ (D_monic _),
      natDegree_mul (pow_ne_zero _ (D_monic _).ne_zero) (pow_ne_zero _ X_ne_zero), natDegree_pow,
      natDegree_D, natDegree_D, natDegree_X_pow]
    omega
      -- the correction as a double sum
  have hβ :
    ∀ s t,
      μGe p ((D (3 * n) ^ 6 * E s * E t) /ₘ D (40 * n)) =
        ∑ k : Fin (37 * n), ∑ l : Fin (37 * n), Cq s k * Cq t l * β0 (k + l) := by
    intro s t
    have hexp :
      D (3 * n) ^ 6 * E s * E t =
        ∑ k : Fin (37 * n),
          ∑ l : Fin (37 * n), C (Cq s k * Cq t l) * (D (3 * n) ^ 6 * X ^ ((k : ℕ) + (l : ℕ))) := by
      rw [sum_coeffMat E hdegE s, sum_coeffMat E hdegE t]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [C_mul, pow_add]; ring
    rw [hexp, divByMonic_sum' (D_monic _), μGe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [divByMonic_sum' (D_monic _), μGe_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [divByMonic_C_mul' (D_monic _), μGe_C_mul]
      -- the low-rank factorization
  set U : Matrix (Fin (37 * n)) (Fin r) ℚ := fun s u => Cq s ⟨k0 + u, by omega⟩ with hU
  set V : Matrix (Fin r) (Fin (37 * n)) ℚ := fun u t =>
    (p : ℚ) * ∑ l : Fin (37 * n), β0 (k0 + u + l) * Cq t l with hV
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hUV :
    ∀ s t, μGe p ((D (3 * n) ^ 6 * E s * E t) /ₘ D (40 * n)) = ((p : ℚ)⁻¹ • (U * V)) s t := by
    intro s t
    rw [hβ, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum]
    set F : Fin (37 * n) → ℚ := fun k => ∑ l : Fin (37 * n), Cq s k * Cq t l * β0 (k + l)
    have hF0 : ∀ k : Fin (37 * n), (k : ℕ) < k0 → F k = 0 := by
      intro k hk
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hβ0zero _ (by have := l.isLt; omega), mul_zero]
    set F' : ℕ → ℚ := fun k => if hk : k < 37 * n then F ⟨k, hk⟩ else 0 with hF'
    have hL : ∑ k : Fin (37 * n), F k = ∑ k ∈ range (37 * n), F' k := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => F' k) (37 * n)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hF', k.isLt]
    have hR : ∑ u : Fin r, (p : ℚ)⁻¹ * (U s u * V u t) = ∑ u ∈ range r, F' (k0 + u) := by
      rw [← Fin.sum_univ_eq_sum_range (fun u => F' (k0 + u)) r]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hu : k0 + (u : ℕ) < 37 * n := by omega
      simp only [hF', dite_eq_left hu, F, hU, hV]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      field_simp
    have hzero : ∀ k, k < k0 → F' k = 0 := by
      intro k hk
      simp only [hF']
      split_ifs with h
      · exact hF0 ⟨k, h⟩ hk
      · rfl
    rw [hL, hR]
    by_cases hk : k0 ≤ 37 * n
    · rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k0) hk,
        Finset.sum_eq_zero (fun k hk' => hzero k (Finset.mem_Ico.mp hk').2), zero_add,
        Finset.sum_Ico_eq_sum_range]
    · rw [show r = 0 by omega, Finset.sum_range_zero]
      exact
        Finset.sum_eq_zero fun k hk' =>
          hzero k
            (by rw [Finset.mem_range] at hk'; omega)
              -- the matrix identity
  set A' : Matrix (Fin (37 * n)) (Fin (37 * n)) ℚ[X] :=
    Matrix.of fun s t =>
      μX (40 * n) (D (3 * n) ^ 6 * E s * E t) -
        C (μGe p ((D (3 * n) ^ 6 * E s * E t) /ₘ D (40 * n)))
  have hG :
    (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)) =
      A' + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X])) := by
    refine Matrix.ext fun s t => ?_
    simp only [A', Matrix.add_apply, Matrix.of_apply, Matrix.map_apply, ← hUV]
    ring
  have hlow :=
    det_lowrank_bound A' U V w hw (fun s t => by simp only [A', Matrix.of_apply]; exact hA s t)
      (fun s u => hCqint s _)
      (fun u t => by
        simp only [hV, Finset.mul_sum]
        exact VG.sum _ fun l _ => by rw [← mul_assoc]; simpa using (hβ0int _).mul (hCqint t l))
  rw [← hG, hbc] at hlow
  have hΔ : Δ n = C ((dC ^ 2)⁻¹) * (C (dC ^ 2) * Δ n) := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hunit.1), C_1, one_mul]
  rw [hΔ]
  have hu : VG p ((dC ^ 2)⁻¹) 0 := by
    refine (VG.inv (p := p) (r := 0) (pow_ne_zero _ hunit.1) ?_).mono (by norm_num)
    rw [padicValRat.pow, hunit.2]; simp
  have := GV.C_mul hu hlow
  rw [zero_add] at this
  exact this

end Zeta5Irrational
