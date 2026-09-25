/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Grid.Jets
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface
public import LeanPool.Nikodym.Nikodym.LowerBound.PrivateFamily

/-!
# Affine point count from grid jets

This file implements blueprint node **C01** of the lower-bound side of the sharp finite-field
Nikodym exponent.

Let `F ⊆ K` be the finite grid field, `q = |F|`, and let `I` be a prime ideal of
`P_d = MvPolynomial (Fin d) K` of quotient dimension `k = quotDim I` and degree `Δ = degree I`.
Write `N` for the number of grid points `x ∈ F^d` lying on `I`, i.e. with `I ≤ 𝔪_{ι(x)}`.

* `Nikodym.LowerBound.card_points_mul_choose_le`: for every `r ≥ 1`,
  `N * (r + k - 1).choose k ≤ Δ * (U + k).choose k` with `U = q (r - 1) + d (q - 1)`. This
  combines the local jet minimum (J02, field `choose_le_jetDim` of `AlgebraInterface`), the grid
  jet interpolation `sum_jetDim_le_hilbert` (G03) and the Hilbert upper bound (A08, field
  `hilbert_le_degree_mul_choose`).
* `Nikodym.LowerBound.card_points_mul_pow_le`: clearing `k!`,
  `N * r ^ k ≤ Δ * (q r + d q + k) ^ k` for every `r ≥ 1`.
* `Nikodym.LowerBound.card_points_le`: `N ≤ Δ q ^ k`, obtained from the previous bound by letting
  `r → ∞` (in `ℝ`).
* `Nikodym.LowerBound.PrivateFamily.card_le_degree_mul_pow`: a private family of `L` lines lying
  on `I` has `L ≤ Δ q ^ k`, since the anchors are distinct grid points on `I`.

The blueprint suggests comparing leading coefficients of polynomials in `r`; we instead pass to
the limit `r → ∞` of `N ≤ Δ (q + (d q + k) / r) ^ k`, which is shorter in Mathlib.
-/

@[expose] public section

namespace Nikodym.LowerBound

open Finset Filter Topology

variable {K : Type*} [Field K] {d : ℕ}
variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

/-! ### Arithmetic auxiliaries -/

/-- Blueprint C01: `r ^ k ≤ k! * (r + k - 1).choose k`, since `k! * (r + k - 1).choose k` is the
ascending factorial `r (r + 1) ⋯ (r + k - 1)`. -/
theorem pow_le_factorial_mul_choose (r k : ℕ) :
    r ^ k ≤ k.factorial * (r + k - 1).choose k := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose']
  exact Nat.pow_succ_le_ascFactorial r k

/-- Blueprint C01: `k! * (U + k).choose k ≤ (U + k) ^ k`, since `k! * (U + k).choose k` is the
ascending factorial `(U + 1) (U + 2) ⋯ (U + k)`. -/
theorem factorial_mul_choose_le_pow (U k : ℕ) :
    k.factorial * (U + k).choose k ≤ (U + k) ^ k := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose]
  exact Nat.ascFactorial_le_pow_add U k

/-! ### Counting grid points on a prime -/

section Points

variable (H : AlgebraInterface K d) {I : Ideal (MvPolynomial (Fin d) K)} (hI : I.IsPrime)
variable [DecidablePred fun x : Fin d → F ↦ I ≤ pointIdeal (liftPt x)]

include H hI

/-- Blueprint C01: for every `r ≥ 1`, with `N` the number of grid points `x ∈ F^d` on `I`,
`k = quotDim I`, `Δ = degree I` and `U = q (r - 1) + d (q - 1)`,
`N * (r + k - 1).choose k ≤ Δ * (U + k).choose k`. -/
theorem card_points_mul_choose_le {r : ℕ} (hr : 1 ≤ r) :
    #(univ.filter fun x : Fin d → F ↦ I ≤ pointIdeal (liftPt x)) *
        (r + quotDim I - 1).choose (quotDim I) ≤
      degree I *
        (Fintype.card F * (r - 1) + d * (Fintype.card F - 1) + quotDim I).choose (quotDim I) :=
  calc #(univ.filter fun x : Fin d → F ↦ I ≤ pointIdeal (liftPt x)) *
        (r + quotDim I - 1).choose (quotDim I)
      = #(univ.filter fun x : Fin d → F ↦ I ≤ pointIdeal (liftPt x)) •
          (r + quotDim I - 1).choose (quotDim I) := (smul_eq_mul _ _).symm
    _ ≤ ∑ x ∈ univ.filter (fun x : Fin d → F ↦ I ≤ pointIdeal (liftPt x)),
          jetDim I (liftPt x) r :=
        card_nsmul_le_sum _ _ _ fun _ hx ↦ H.choose_le_jetDim I hI _ (mem_filter.mp hx).2 r hr
    _ ≤ ∑ x : Fin d → F, jetDim I (liftPt x) r := sum_le_sum_of_subset (filter_subset _ _)
    _ ≤ hilbert I (Fintype.card F * (r - 1) + d * (Fintype.card F - 1)) :=
        sum_jetDim_le_hilbert I r
    _ ≤ _ := H.hilbert_le_degree_mul_choose I hI _

/-- Blueprint C01: for every `r ≥ 1`, `N * r ^ k ≤ Δ * (q r + (d q + k)) ^ k`. -/
theorem card_points_mul_pow_le {r : ℕ} (hr : 1 ≤ r) :
    #(univ.filter fun x : Fin d → F ↦ I ≤ pointIdeal (liftPt x)) * r ^ quotDim I ≤
      degree I * (Fintype.card F * r + (d * Fintype.card F + quotDim I)) ^ quotDim I := by
  set N := #(univ.filter fun x : Fin d → F ↦ I ≤ pointIdeal (liftPt x))
  set k := quotDim I
  set q := Fintype.card F
  set U := q * (r - 1) + d * (q - 1)
  have hU : U + k ≤ q * r + (d * q + k) := by
    have h1 : q * (r - 1) ≤ q * r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have h2 : d * (q - 1) ≤ d * q := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  calc N * r ^ k ≤ N * (k.factorial * (r + k - 1).choose k) :=
        Nat.mul_le_mul_left _ (pow_le_factorial_mul_choose r k)
    _ = k.factorial * (N * (r + k - 1).choose k) := by ring
    _ ≤ k.factorial * (degree I * (U + k).choose k) :=
        Nat.mul_le_mul_left _ (card_points_mul_choose_le H hI hr)
    _ = degree I * (k.factorial * (U + k).choose k) := by ring
    _ ≤ degree I * (U + k) ^ k := Nat.mul_le_mul_left _ (factorial_mul_choose_le_pow U k)
    _ ≤ degree I * (q * r + (d * q + k)) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hU k)

/-- Blueprint C01: the number of grid points `x ∈ F^d` on a prime `I` of quotient dimension `k`
and degree `Δ` is at most `Δ q ^ k`. -/
theorem card_points_le :
    #(univ.filter fun x : Fin d → F ↦ I ≤ pointIdeal (liftPt x)) ≤
      degree I * Fintype.card F ^ quotDim I := by
  set N := #(univ.filter fun x : Fin d → F ↦ I ≤ pointIdeal (liftPt x))
  set k := quotDim I
  set q := Fintype.card F
  set c := d * q + k
  have key : ∀ r : ℕ, 1 ≤ r → (N : ℝ) ≤ degree I * ((q : ℝ) + (c : ℝ) / r) ^ k := by
    intro r hr
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have h : (N : ℝ) * (r : ℝ) ^ k ≤ degree I * ((q : ℝ) * r + c) ^ k := by
      exact_mod_cast card_points_mul_pow_le H hI hr
    have hq : (q : ℝ) + c / r = (q * r + c) / r := by
      field_simp
    rw [hq, div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hr' k)]
    exact h
  have hlim : Tendsto (fun r : ℕ ↦ (degree I : ℝ) * ((q : ℝ) + (c : ℝ) / r) ^ k) atTop
      (𝓝 (degree I * (q : ℝ) ^ k)) := by
    have := (((tendsto_const_nhds (x := (q : ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))).pow k).const_mul (degree I : ℝ)
    rwa [add_zero] at this
  have hle : (N : ℝ) ≤ degree I * (q : ℝ) ^ k :=
    ge_of_tendsto hlim ((eventually_ge_atTop 1).mono key)
  exact_mod_cast hle

end Points

/-! ### Private families on a prime -/

namespace PrivateFamily

variable {E : Type*} [Fintype E] (P : PrivateFamily F d E)

/-- Blueprint C01: a private family of `L` lines lying on a prime `I` of quotient dimension `k`
and degree `Δ` has `L ≤ Δ q ^ k`: the anchors are `L` distinct grid points on `I`. -/
theorem card_le_degree_mul_pow (H : AlgebraInterface K d) {I : Ideal (MvPolynomial (Fin d) K)}
    (hI : I.IsPrime) (hIP : ∀ e, I ≤ P.lineIdeal (K := K) e) :
    Fintype.card E ≤ degree I * Fintype.card F ^ quotDim I := by
  classical
  refine le_trans ?_ (card_points_le (F := F) H hI)
  rw [← card_univ, ← card_image_of_injective univ P.b_injective]
  refine card_le_card fun x hx ↦ ?_
  obtain ⟨e, -, rfl⟩ := mem_image.mp hx
  exact mem_filter.mpr ⟨mem_univ _, (hIP e).trans (P.lineIdeal_le_pointIdeal_b e)⟩

end PrivateFamily

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
