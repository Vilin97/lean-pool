/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.BasisChange
import LeanPool.Zeta5Irrational.Arith.DirectBound
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring.Basic

/-! # Unimodularity of the class bases

Let `E a ∈ ℤ[t]` (`a : Fin h`) be such that, modulo `p`,
`E a ≡ ∏_{c ≠ cls a} (t - γ_c)^{L_c} · (t - γ_{cls a})^{idx a}`,
where the `γ_c ∈ 𝔽_p` are distinct, `idx a < L (cls a)` and `(cls, idx)` is injective.
Then the coefficient matrix of the `E a` has a determinant prime to `p`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {F : Type*} [Field F]

/-- A polynomial `∑_{i ∈ s} λ_i (X - γ)^i` vanishes only if all `λ_i` vanish. -/
lemma sum_pow_X_sub_C_eq_zero {ι : Type*} (s : Finset ι) (d : ι → ℕ) (hd : Set.InjOn d s)
    (lam : ι → F) (γ : F) (h : ∑ a ∈ s, C (lam a) * (X - C γ) ^ d a = 0) : ∀ a ∈ s, lam a = 0 := by
  intro a ha
  have h2 := congrArg (fun f : F[X] => (f.comp (X + C γ)).coeff (d a)) h
  simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, sub_comp, X_comp,
    add_sub_cancel_right, zero_comp, coeff_zero, finsetSum_coeff, coeff_C_mul, coeff_X_pow] at h2
  rw [Finset.sum_eq_single a] at h2
  · simpa using h2
  · intro b hb hba
    rw [ite_eq_right (fun h => hba (hd hb ha h.symm)), mul_zero]
  · intro h; exact absurd ha h

/-- **Independence of the class bases over a field.** -/
theorem classBasis_independent {h : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (γ : ι → F)
    (hγ : Function.Injective γ) (L : ι → ℕ) (cls : Fin h → ι) (idx : Fin h → ℕ)
    (hidx : ∀ a, idx a < L (cls a)) (hinj : ∀ a b, cls a = cls b → idx a = idx b → a = b)
    (v : Fin h → F)
    (hv :
      ∑ a,
          C (v a) *
            ((∏ c ∈ Finset.univ.erase (cls a), (X - C (γ c)) ^ L c) *
              (X - C (γ (cls a))) ^ idx a) =
        0) :
    v = 0 := by
  funext a0
  set c := cls a0 with hc
  set U := ∏ c' ∈ Finset.univ.erase c, (X - C (γ c')) ^ L c' with hU
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => cls a = c)
      (fun a =>
        C (v a) *
          ((∏ c' ∈ Finset.univ.erase (cls a), (X - C (γ c')) ^ L c') *
            (X - C (γ (cls a))) ^ idx a))
  rw [hv] at hsplit
        -- the rows of other classes are divisible by `(X - γ_c)^{L_c}`
  have hdvd_other :
    (X - C (γ c)) ^ L c ∣
      ∑ a ∈ Finset.univ.filter (fun a => ¬cls a = c),
        C (v a) *
          ((∏ c' ∈ Finset.univ.erase (cls a), (X - C (γ c')) ^ L c') *
            (X - C (γ (cls a))) ^ idx a) := by
    refine Finset.dvd_sum fun a ha => ?_
    rw [Finset.mem_filter] at ha
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm ha.2, Finset.mem_univ _⟩)
  have hsame :
    ∑ a ∈ Finset.univ.filter (fun a => cls a = c),
        C (v a) *
          ((∏ c' ∈ Finset.univ.erase (cls a), (X - C (γ c')) ^ L c') *
            (X - C (γ (cls a))) ^ idx a) =
      U * ∑ a ∈ Finset.univ.filter (fun a => cls a = c), C (v a) * (X - C (γ c)) ^ idx a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    rw [ha.2]; ring
  have hdvd :
    (X - C (γ c)) ^ L c ∣
      U * ∑ a ∈ Finset.univ.filter (fun a => cls a = c), C (v a) * (X - C (γ c)) ^ idx a := by
    rw [← hsame]
    have :
      ∑ a ∈ Finset.univ.filter (fun a => cls a = c),
          C (v a) *
            ((∏ c' ∈ Finset.univ.erase (cls a), (X - C (γ c')) ^ L c') *
              (X - C (γ (cls a))) ^ idx a) =
        -(∑ a ∈ Finset.univ.filter (fun a => ¬cls a = c),
            C (v a) *
              ((∏ c' ∈ Finset.univ.erase (cls a), (X - C (γ c')) ^ L c') *
                (X - C (γ (cls a))) ^ idx a)) :=
      by rw [eq_neg_iff_add_eq_zero]; exact hsplit
    rw [this]; exact (dvd_neg).mpr hdvd_other
  have hcop : IsCoprime ((X - C (γ c)) ^ L c) U := by
    rw [hU]
    refine IsCoprime.prod_right fun c' hc' => ?_
    refine IsCoprime.pow ?_
    exact
      isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hc').1 (hγ h).symm).isUnit
  have hdvd2 := hcop.dvd_of_dvd_mul_left hdvd
  set f := ∑ a ∈ Finset.univ.filter (fun a => cls a = c), C (v a) * (X - C (γ c)) ^ idx a
  have hdeg : f.natDegree < L c := by
    rcases Nat.eq_zero_or_pos (L c) with h0 | hpos
    · exact absurd (hidx a0) (by rw [← hc, h0]; omega)
    refine
      lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := L c - 1) fun a ha => ?_) (by omega)
    rw [Finset.mem_filter] at ha
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    have := hidx a; rw [ha.2] at this; omega
  have hf0 : f = 0 := by
    by_contra hne
    have := natDegree_le_of_dvd hdvd2 hne
    rw [natDegree_pow, natDegree_X_sub_C, mul_one] at this
    omega
  have :=
    sum_pow_X_sub_C_eq_zero (Finset.univ.filter (fun a => cls a = c)) idx
      (fun a ha b hb h => hinj a b (by rw [Finset.coe_filter] at ha hb; rw [ha.2, hb.2]) h) v
      (γ c) hf0
  exact this a0 (by simp [hc])

/-- **Unimodularity**: the rational determinant of the coefficient matrix is a `p`-adic unit. -/
theorem coeffMat_det_unit {h : ℕ} {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Ez : Fin h → ℤ[X]) (hdeg : ∀ a, (Ez a).natDegree < h) (γ : ι → ZMod p)
    (hγ : Function.Injective γ) (L : ι → ℕ) (cls : Fin h → ι) (idx : Fin h → ℕ)
    (hidx : ∀ a, idx a < L (cls a)) (hinj : ∀ a b, cls a = cls b → idx a = idx b → a = b)
    (hred :
      ∀ a,
        (Ez a).map (Int.castRingHom (ZMod p)) =
          (∏ c ∈ Finset.univ.erase (cls a), (X - C (γ c)) ^ L c) * (X - C (γ (cls a))) ^ idx a) :
    (coeffMat fun a => (Ez a).map (Int.castRingHom ℚ)).det ≠ 0 ∧
      padicValRat p (coeffMat fun a => (Ez a).map (Int.castRingHom ℚ)).det = 0 := by
  set Mz : Matrix (Fin h) (Fin h) ℤ := Matrix.of fun a k => (Ez a).coeff k with hMz
  have hQ : coeffMat (fun a => (Ez a).map (Int.castRingHom ℚ)) = Mz.map (Int.castRingHom ℚ) := by
    ext a k; simp [coeffMat, hMz, coeff_map]
  have hdetQ : (coeffMat fun a => (Ez a).map (Int.castRingHom ℚ)).det = (Mz.det : ℚ) := by
    rw [hQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; simp
  have hdetP : ((Mz.det : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have h1 : (Mz.map (Int.castRingHom (ZMod p))).transpose.det = 0 := by
      rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; simpa using h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1
    apply hv0
    apply classBasis_independent γ hγ L cls idx hidx hinj v
    rw [← Finset.sum_congr rfl fun a _ => by rw [← hred a]]
    ext k
    rw [finsetSum_coeff, coeff_zero]
    simp only [coeff_C_mul, coeff_map]
    by_cases hk : k < h
    · have := congrFun hv ⟨k, hk⟩
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, hMz,
        Matrix.of_apply, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [mul_comm]
    · refine Finset.sum_eq_zero fun a _ => ?_
      rw [coeff_eq_zero_of_natDegree_lt (by have := hdeg a; omega)]; simp
  have hndvd : ¬(p : ℤ) ∣ Mz.det := fun h => hdetP ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
  rw [hdetQ]
  refine
    ⟨fun h => hndvd (by exact_mod_cast (show Mz.det = 0 by exact_mod_cast h) ▸ dvd_zero _), ?_⟩
  exact padicValRat_int_eq_zero hndvd

end Zeta5Irrational
