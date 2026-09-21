/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.MultiQuadratic.Order
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Kummer

/-!
# The monomial basis of the multiquadratic order

Blueprint nodes K03 and K04. Under the standing hypotheses of K01 (`hr1 : ∀ j, 1 < r j`,
`hsq : ∀ j, Squarefree (r j)`, `hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)`), which are
always passed as three separate arguments:

* K03: `emb_one_injective` (the embedding `σ₁` is injective), the `ℤ`-basis
  `monoBasis hr1 hsq hcop : Module.Basis (Finset (Fin m)) ℤ (Order r)` given by the monomials
  `mono r S`, the character orthogonality `sum_sgn_mul_sgn`, the coordinate formula
  `sum_sgn_mul_emb`, the bounds `abs_emb_mono_le` (`K₀ = ∏ j, r j`) and `abs_repr_le`
  (`K₁ = 1`).
* K04: `sum_emb_eq` and `exists_int_sum_emb` (the trace `∑ ε, σ_ε x` is `2 ^ m` times the
  constant coordinate, in particular an integer).
-/

open Finset
open scoped symmDiff

namespace Nikodym.MultiQuad

noncomputable section

variable {m : ℕ} {r : Fin m → ℕ}

/-! ### Blueprint K03: injectivity of `σ₁` and the monomial basis -/

/-- Blueprint K03: the embedding `σ₁ : 𝒪_r → ℝ` is injective. -/
theorem emb_one_injective (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) : Function.Injective (emb r 1) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := exists_repr r x
  have h : ∑ S, (c S : ℝ) * Real.sqrt (∏ j ∈ S, (r j : ℝ)) = 0 := by
    simpa [map_sum, emb_mono] using hx
  rw [sum_intCast_mul_sqrt_prod_eq_zero hr1 hsq hcop c h]
  simp

/-- Blueprint K03: the monomials `mono r S` are `ℤ`-linearly independent. -/
theorem linearIndependent_mono (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) : LinearIndependent ℤ (mono r) := by
  refine LinearIndependent.of_comp (emb r 1).toAddMonoidHom.toIntLinearMap ?_
  have h : (⇑(emb r 1).toAddMonoidHom.toIntLinearMap ∘ mono r) =
      fun S : Finset (Fin m) ↦ Real.sqrt (∏ j ∈ S, (r j : ℝ)) := by
    funext S
    simp [emb_mono]
  rw [h]
  exact linearIndependent_sqrt_prod_int hr1 hsq hcop

/-- Blueprint K03: the monomials `mono r S`, `S ⊆ Fin m`, form a `ℤ`-basis of `𝒪_r`. -/
def monoBasis (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) :
    Module.Basis (Finset (Fin m)) ℤ (Order r) :=
  Module.Basis.mk (linearIndependent_mono hr1 hsq hcop) (mono_span r).ge

/-- Blueprint K03: the basis vectors are the monomials. -/
@[simp]
theorem monoBasis_apply (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) (S : Finset (Fin m)) :
    monoBasis hr1 hsq hcop S = mono r S :=
  Module.Basis.mk_apply _ _ S

/-- Blueprint K03: every element is the sum of its coordinates times the monomials. -/
theorem monoBasis_repr_sum (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) (x : Order r) :
    ∑ S, ((monoBasis hr1 hsq hcop).repr x S : Order r) * mono r S = x := by
  have h := (monoBasis hr1 hsq hcop).sum_repr x
  simpa [zsmul_eq_mul] using h

/-- Blueprint K03: uniqueness of coordinates. -/
theorem repr_eq_of_sum_eq (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) {x : Order r} {c : Finset (Fin m) → ℤ}
    (hx : x = ∑ S, (c S : Order r) * mono r S) (S : Finset (Fin m)) :
    (monoBasis hr1 hsq hcop).repr x S = c S := by
  have h := (monoBasis hr1 hsq hcop).repr_sum_self c
  simp only [monoBasis_apply, zsmul_eq_mul] at h
  rw [hx, h]

/-! ### Blueprint K03: character orthogonality -/

/-- Blueprint K03: the sign of the empty set is `1`. -/
@[simp]
theorem sgn_empty (ε : Fin m → ℤˣ) : sgn ε ∅ = 1 := by
  simp [sgn]

/-- Blueprint K03: `sgn ε S` is `±1`. -/
theorem sgn_eq_one_or (ε : Fin m → ℤˣ) (S : Finset (Fin m)) :
    sgn ε S = 1 ∨ sgn ε S = -1 := by
  have h : sgn ε S = ((∏ j ∈ S, ε j : ℤˣ) : ℤ) := by simp [sgn, Units.coe_prod]
  rw [h]
  rcases Int.units_eq_one_or (∏ j ∈ S, ε j) with h1 | h1 <;> simp [h1]

/-- Blueprint K03: `|sgn ε S| = 1`. -/
@[simp]
theorem abs_sgn (ε : Fin m → ℤˣ) (S : Finset (Fin m)) : |sgn ε S| = 1 := by
  rcases sgn_eq_one_or ε S with h | h <;> simp [h]

/-- Blueprint K03: flipping the coordinate `j ∈ S` of the sign vector. -/
theorem sgn_update_of_mem (ε : Fin m → ℤˣ) {j : Fin m} {S : Finset (Fin m)} (hj : j ∈ S)
    (u : ℤˣ) :
    sgn (Function.update ε j u) S = (u : ℤ) * ∏ x ∈ S.erase j, (ε x : ℤ) := by
  simp only [sgn]
  rw [← mul_prod_erase S _ hj, Function.update_self]
  congr 1
  refine prod_congr rfl fun x hx ↦ ?_
  rw [Function.update_of_ne (ne_of_mem_erase hx)]

/-- Blueprint K03: `∑ ε, sgn ε S` is `2 ^ m` if `S = ∅` and `0` otherwise. -/
theorem sum_sgn (S : Finset (Fin m)) :
    ∑ ε : Fin m → ℤˣ, sgn ε S = if S = ∅ then 2 ^ m else 0 := by
  split_ifs with hS
  · subst hS
    simp [sum_const, card_univ, Fintype.card_units_int]
  · obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.2 hS
    refine sum_ninvolution (fun ε ↦ Function.update ε j (-ε j)) ?_ ?_ (fun _ ↦ mem_univ _) ?_
    · intro ε
      rw [sgn_update_of_mem ε hj, sgn, ← mul_prod_erase S _ hj, Units.val_neg]
      ring
    · intro ε _ h
      have := congr_fun h j
      simp at this
    · intro ε
      simp [Function.update_idem, Function.update_eq_self]

/-- Blueprint K03: character orthogonality `∑ ε, ε_S ε_T = 2 ^ m [S = T]`. -/
theorem sum_sgn_mul_sgn (S T : Finset (Fin m)) :
    ∑ ε : Fin m → ℤˣ, sgn ε S * sgn ε T = if S = T then 2 ^ m else 0 := by
  simp_rw [sgn_mul_sgn]
  rw [sum_sgn]
  simp only [symmDiff_eq_empty]

/-! ### Blueprint K03: the coordinate formula and the coordinate bound -/

/-- Blueprint K03: the coordinate formula
`∑ ε, ε_T σ_ε(x) = 2 ^ m c_T(x) √r_T`. -/
theorem sum_sgn_mul_emb (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) (x : Order r) (T : Finset (Fin m)) :
    ∑ ε : Fin m → ℤˣ, (sgn ε T : ℝ) * emb r ε x =
      2 ^ m * ((monoBasis hr1 hsq hcop).repr x T : ℝ) * Real.sqrt (∏ j ∈ T, (r j : ℝ)) := by
  obtain ⟨c, hc⟩ := exists_repr r x
  rw [repr_eq_of_sum_eq hr1 hsq hcop hc T, hc]
  simp only [map_sum, map_mul, emb_intCast, emb_mono, mul_sum]
  rw [sum_comm]
  have key : ∀ S : Finset (Fin m),
      ∑ ε : Fin m → ℤˣ, (sgn ε T : ℝ) * ((c S : ℝ) * ((sgn ε S : ℝ) *
        Real.sqrt (∏ j ∈ S, (r j : ℝ)))) =
      if S = T then 2 ^ m * (c T : ℝ) * Real.sqrt (∏ j ∈ T, (r j : ℝ)) else 0 := by
    intro S
    have h : ∑ ε : Fin m → ℤˣ, ((sgn ε S * sgn ε T : ℤ) : ℝ) =
        if S = T then (2 : ℝ) ^ m else 0 := by
      rw [← Int.cast_sum, sum_sgn_mul_sgn]
      split_ifs <;> simp
    calc ∑ ε : Fin m → ℤˣ, (sgn ε T : ℝ) * ((c S : ℝ) * ((sgn ε S : ℝ) *
          Real.sqrt (∏ j ∈ S, (r j : ℝ))))
        = (c S : ℝ) * Real.sqrt (∏ j ∈ S, (r j : ℝ)) *
            ∑ ε : Fin m → ℤˣ, ((sgn ε S * sgn ε T : ℤ) : ℝ) := by
          rw [mul_sum]
          refine sum_congr rfl fun ε _ ↦ ?_
          push_cast
          ring
      _ = _ := by
          rw [h]
          split_ifs with hST
          · subst hST
            ring
          · simp
  simp_rw [key]
  simp

/-- Blueprint K03: `1 ≤ √r_T`. -/
theorem one_le_sqrt_prod (hr1 : ∀ j, 1 < r j) (T : Finset (Fin m)) :
    1 ≤ Real.sqrt (∏ j ∈ T, (r j : ℝ)) := by
  rw [Real.one_le_sqrt, ← Nat.cast_prod]
  exact_mod_cast one_le_prod fun j _ ↦ (hr1 j).le

/-- Blueprint K03: `√r_T ≤ r_T ≤ ∏ j, r j`. -/
theorem sqrt_prod_le_prod (hr1 : ∀ j, 1 < r j) (T : Finset (Fin m)) :
    Real.sqrt (∏ j ∈ T, (r j : ℝ)) ≤ ∏ j, (r j : ℝ) := by
  have h1 : (1 : ℝ) ≤ ∏ j ∈ T, (r j : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast one_le_prod fun j _ ↦ (hr1 j).le
  have h2 : ∏ j ∈ T, (r j : ℝ) ≤ ∏ j, (r j : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.cast_prod]
    exact_mod_cast prod_le_prod_of_subset_of_one_le (subset_univ T) fun j _ _ ↦ (hr1 j).le
  calc Real.sqrt (∏ j ∈ T, (r j : ℝ)) ≤ ∏ j ∈ T, (r j : ℝ) := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
    _ ≤ ∏ j, (r j : ℝ) := h2

/-- Blueprint K03: `|σ_ε(mono T)| ≤ ∏ j, r j`; this is the constant `K₀` of the scaffold. -/
theorem abs_emb_mono_le (hr1 : ∀ j, 1 < r j) (ε : Fin m → ℤˣ) (T : Finset (Fin m)) :
    |emb r ε (mono r T)| ≤ ∏ j, (r j : ℝ) := by
  rw [emb_mono, abs_mul, ← Int.cast_abs, abs_sgn, Int.cast_one, one_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_prod_le_prod hr1 T

/-- Blueprint K03: the coordinate bound with `K₁ = 1`: if `|σ_ε(x)| ≤ T` for all `ε`, then
every coordinate of `x` in the monomial basis is bounded by `T`. -/
theorem abs_repr_le (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) {x : Order r} {T : ℝ}
    (hx : ∀ ε, |emb r ε x| ≤ T) (S : Finset (Fin m)) :
    |((monoBasis hr1 hsq hcop).repr x S : ℝ)| ≤ T := by
  set c : ℝ := ((monoBasis hr1 hsq hcop).repr x S : ℝ) with hc
  have hsqrt := one_le_sqrt_prod hr1 S
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hbound : |∑ ε : Fin m → ℤˣ, (sgn ε S : ℝ) * emb r ε x| ≤ 2 ^ m * T := by
    calc |∑ ε : Fin m → ℤˣ, (sgn ε S : ℝ) * emb r ε x|
        ≤ ∑ ε : Fin m → ℤˣ, |(sgn ε S : ℝ) * emb r ε x| := abs_sum_le_sum_abs _ _
      _ = ∑ ε : Fin m → ℤˣ, |emb r ε x| := by
          refine sum_congr rfl fun ε _ ↦ ?_
          rw [abs_mul, ← Int.cast_abs, abs_sgn, Int.cast_one, one_mul]
      _ ≤ ∑ _ε : Fin m → ℤˣ, T := sum_le_sum fun ε _ ↦ hx ε
      _ = 2 ^ m * T := by
          simp [sum_const, card_univ, Fintype.card_units_int]
  rw [sum_sgn_mul_emb hr1 hsq hcop x S, ← hc, abs_mul, abs_mul, abs_of_pos h2,
    abs_of_pos (by linarith : 0 < Real.sqrt (∏ j ∈ S, (r j : ℝ)))] at hbound
  have h3 : 2 ^ m * |c| ≤ 2 ^ m * T := by
    calc 2 ^ m * |c| = 2 ^ m * |c| * 1 := by ring
      _ ≤ 2 ^ m * |c| * Real.sqrt (∏ j ∈ S, (r j : ℝ)) := by gcongr
      _ ≤ 2 ^ m * T := hbound
  exact le_of_mul_le_mul_left h3 h2

/-! ### Blueprint K04: trace integrality -/

/-- Blueprint K04: `∑ ε, σ_ε(x) = 2 ^ m c_∅(x)`. -/
theorem sum_emb_eq (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) (x : Order r) :
    ∑ ε : Fin m → ℤˣ, emb r ε x = 2 ^ m * ((monoBasis hr1 hsq hcop).repr x ∅ : ℝ) := by
  have h := sum_sgn_mul_emb hr1 hsq hcop x ∅
  simpa using h

/-- Blueprint K04: the trace `∑ ε, σ_ε(x)` is an integer (the `trace_int` field of the
scaffold). -/
theorem exists_int_sum_emb (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) (x : Order r) :
    ∃ z : ℤ, ∑ ε : Fin m → ℤˣ, emb r ε x = z :=
  ⟨2 ^ m * (monoBasis hr1 hsq hcop).repr x ∅, by
    rw [sum_emb_eq hr1 hsq hcop]
    push_cast
    ring⟩

end

end Nikodym.MultiQuad

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
