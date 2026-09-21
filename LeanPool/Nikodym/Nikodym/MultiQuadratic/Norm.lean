/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.MultiQuadratic.Basis
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Legendre

/-!
# The conjugate norm and the small-kernel property

Blueprint node K05. The conjugate norm `nm r x = ∏ ε, conj r ε x` of an element of the
multiquadratic order `𝒪_r` is invariant under all conjugations (`conj_nm`), hence an integer
`normInt hr1 hsq hcop x` (`nm_eq_normInt`), which equals `∏ ε, emb r ε x` (`normInt_eq_prod`)
and is divisible by `x` (`dvd_nm`). Consequently, for a ring homomorphism `φ : 𝒪_r →+* F` into
a field of prime cardinality, an element of the kernel with `∏ ε, |emb r ε x| < |F|` vanishes
(`eq_zero_of_map_eq_zero`, the `small_ker` field of the scaffold).

As in `Nikodym.MultiQuadratic.Basis`, the K01 hypotheses `hr1`, `hsq`, `hcop` are passed as
three separate arguments.
-/

open Finset

namespace Nikodym.MultiQuad

noncomputable section

variable {m : ℕ} {r : Fin m → ℕ}

/-- Blueprint K05: the conjugate norm `nm x = ∏ ε, τ_ε(x)`. -/
def nm (r : Fin m → ℕ) (x : Order r) : Order r :=
  ∏ ε : Fin m → ℤˣ, conj r ε x

/-- Blueprint K05: the conjugate norm is fixed by every conjugation. -/
theorem conj_nm (r : Fin m → ℕ) (δ : Fin m → ℤˣ) (x : Order r) :
    conj r δ (nm r x) = nm r x := by
  simp only [nm, map_prod]
  refine Fintype.prod_equiv (Equiv.mulLeft δ) _ _ fun ε ↦ ?_
  rw [Equiv.coe_mulLeft]
  exact RingHom.congr_fun (conj_comp_conj r δ ε) x

/-- Blueprint K05: an element fixed by all conjugations has no non-constant coordinates. -/
theorem repr_eq_zero_of_conj_eq (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) {y : Order r}
    (hy : ∀ δ, conj r δ y = y) {S : Finset (Fin m)} (hS : S ≠ ∅) :
    (monoBasis hr1 hsq hcop).repr y S = 0 := by
  obtain ⟨c, hc⟩ := exists_repr r y
  subst hc
  obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.2 hS
  set δ : Fin m → ℤˣ := Pi.mulSingle j (-1) with hδdef
  have hδ : sgn δ S = -1 := by
    rw [sgn, ← mul_prod_erase S _ hj, prod_eq_one fun x hx ↦ ?_]
    · simp [δ]
    · simp [δ, Pi.mulSingle_eq_of_ne (ne_of_mem_erase hx)]
  have h1 : (monoBasis hr1 hsq hcop).repr (∑ T, (c T : Order r) * mono r T) S = c S :=
    repr_eq_of_sum_eq hr1 hsq hcop rfl S
  have h2 : (monoBasis hr1 hsq hcop).repr (∑ T, (c T : Order r) * mono r T) S =
      sgn δ S * c S := by
    have h := hy δ
    simp only [map_sum, map_mul, conj_intCast, conj_mono] at h
    refine repr_eq_of_sum_eq hr1 hsq hcop (c := fun T ↦ sgn δ T * c T)
      (h.symm.trans (sum_congr rfl fun T _ ↦ ?_)) S
    push_cast
    ring
  rw [h1] at h2 ⊢
  rw [hδ] at h2
  linarith

/-- Blueprint K05: the integer `N(x)` with `nm x = N(x) · 1`, defined as the constant
coordinate of `nm x`. -/
def normInt (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) (x : Order r) : ℤ :=
  (monoBasis hr1 hsq hcop).repr (nm r x) ∅

/-- Blueprint K05: the conjugate norm is the integer `N(x)`. -/
theorem nm_eq_normInt (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) (x : Order r) :
    nm r x = (normInt hr1 hsq hcop x : Order r) := by
  have h := monoBasis_repr_sum hr1 hsq hcop (nm r x)
  rw [← h, sum_eq_single ∅ (fun S _ hS ↦ ?_) fun h ↦ absurd (mem_univ _) h]
  · simp [normInt]
  · rw [repr_eq_zero_of_conj_eq hr1 hsq hcop (fun δ ↦ conj_nm r δ x) hS]
    simp

/-- Blueprint K05: the conjugate norm is an integer. -/
theorem exists_int_nm (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) (x : Order r) :
    ∃ N : ℤ, nm r x = (N : Order r) :=
  ⟨normInt hr1 hsq hcop x, nm_eq_normInt hr1 hsq hcop x⟩

/-- Blueprint K05: `N(x) = ∏ ε, σ_ε(x)`. -/
theorem normInt_eq_prod (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) (x : Order r) :
    (normInt hr1 hsq hcop x : ℝ) = ∏ ε : Fin m → ℤˣ, emb r ε x := by
  have h := congrArg (emb r 1) (nm_eq_normInt hr1 hsq hcop x)
  rw [emb_intCast, nm, map_prod] at h
  rw [← h]
  exact prod_congr rfl fun ε _ ↦ (emb_conj r ε x).symm

/-- Blueprint K05: `x` divides its conjugate norm. -/
theorem dvd_nm (r : Fin m → ℕ) (x : Order r) : x ∣ nm r x := by
  rw [nm, ← mul_prod_erase univ _ (mem_univ (1 : Fin m → ℤˣ)), conj_one, RingHom.id_apply]
  exact dvd_mul_right x _

/-- Blueprint K05: the small-kernel property (the `small_ker` field of the scaffold). If
`φ : 𝒪_r →+* F` with `F` a field of prime cardinality, `φ x = 0` and
`∏ ε, |σ_ε(x)| < |F|`, then `x = 0`. -/
theorem eq_zero_of_map_eq_zero (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) {F : Type*} [Field F] [Fintype F]
    (hp : (Fintype.card F).Prime) (φ : Order r →+* F) {x : Order r} (hx : φ x = 0)
    (hsmall : ∏ ε : Fin m → ℤˣ, |emb r ε x| < Fintype.card F) : x = 0 := by
  have := charP_of_card_prime hp
  have hnm : φ (nm r x) = 0 := by
    obtain ⟨y, hy⟩ := dvd_nm r x
    rw [hy, map_mul, hx, zero_mul]
  rw [nm_eq_normInt hr1 hsq hcop x, map_intCast] at hnm
  have hdvd : (Fintype.card F : ℤ) ∣ normInt hr1 hsq hcop x :=
    (CharP.intCast_eq_zero_iff F _ _).1 hnm
  have habs : |normInt hr1 hsq hcop x| < Fintype.card F := by
    have h : ((|normInt hr1 hsq hcop x| : ℤ) : ℝ) < Fintype.card F := by
      rw [Int.cast_abs, normInt_eq_prod hr1 hsq hcop, abs_prod]
      exact hsmall
    exact_mod_cast h
  have hN : normInt hr1 hsq hcop x = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have hprod : ∏ ε : Fin m → ℤˣ, emb r ε x = 0 := by
    rw [← normInt_eq_prod hr1 hsq hcop, hN, Int.cast_zero]
  obtain ⟨ε, -, hε⟩ := prod_eq_zero_iff.1 hprod
  rw [emb_conj] at hε
  have h0 : conj r ε x = 0 := emb_one_injective hr1 hsq hcop (hε.trans (map_zero _).symm)
  exact conj_injective r ε (h0.trans (map_zero _).symm)

end

end Nikodym.MultiQuad

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
