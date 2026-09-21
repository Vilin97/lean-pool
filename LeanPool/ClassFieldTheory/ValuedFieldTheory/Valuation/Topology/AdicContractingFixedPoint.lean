/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.RingTheory.AdicCompletion.Basic
/-!
# Fixed points of adically contracting additive maps

An additive endomorphism which sends `I ^ n` into `I ^ (n + 1)` is
topologically nilpotent for the `I`-adic topology.  Completeness therefore
solves the affine fixed-point equation

`x = b + T x`

uniquely.  The proof uses the successive approximations
`x₀ = 0`, `xₙ₊₁ = b + T xₙ` and mathlib's `IsPrecomplete.prec`.
-/

namespace IsAdicComplete

variable {R : Type*} [CommRing R]

private def contractingApproximation
    (T : R →+ R) (b : R) : ℕ → R
  | 0 => 0
  | n + 1 => b + T (contractingApproximation T b n)

private theorem contractingApproximation_succ
    (T : R →+ R) (b : R) (n : ℕ) :
    contractingApproximation T b (n + 1) =
      b + T (contractingApproximation T b n) :=
  rfl

private theorem ideal_smul_top_eq_self (J : Ideal R) :
    J • (⊤ : Submodule R R) = (J : Submodule R R) := by
  rw [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id,
    Submodule.restrictScalars_self]

private theorem map_smodEq_pow_succ
    (I : Ideal R) (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (n : ℕ) {x y : R}
    (hxy : x ≡ y [SMOD (I ^ n : Ideal R)]) :
    T x ≡ T y [SMOD (I ^ (n + 1) : Ideal R)] := by
  rw [SModEq.sub_mem, ← T.map_sub]
  exact hT n ((SModEq.sub_mem).1 hxy)

private theorem contractingApproximation_sub_mem_pow
    (I : Ideal R) (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (b : R) :
    ∀ n, contractingApproximation T b n -
      contractingApproximation T b (n + 1) ∈ I ^ n := by
  intro n
  induction n with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      exact (Submodule.mem_top :
        contractingApproximation T b 0 -
          contractingApproximation T b (0 + 1) ∈ (⊤ : Ideal R))
  | succ n ih =>
      simpa only [contractingApproximation_succ,
        add_sub_add_left_eq_sub, ← T.map_sub] using hT n ih

private theorem contractingApproximation_limit_is_fixed
    (I : Ideal R) [IsHausdorff I R]
    (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (b a : R)
    (ha : ∀ n, contractingApproximation T b n ≡
      a [SMOD (I ^ n : Ideal R)]) :
    a = b + T a := by
  apply (IsHausdorff.eq_iff_smodEq (I := I)).2
  intro n
  rw [ideal_smul_top_eq_self]
  have hpow :
      (I ^ (n + 1) : Ideal R) ≤ I ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n)
  have haleft :
      a ≡ contractingApproximation T b (n + 1)
        [SMOD (I ^ n : Ideal R)] :=
    SModEq.mono hpow (ha (n + 1)).symm
  have hTcongr :
      T (contractingApproximation T b n) ≡ T a
        [SMOD (I ^ (n + 1) : Ideal R)] :=
    map_smodEq_pow_succ I T hT n (ha n)
  have haright :
      contractingApproximation T b (n + 1) ≡ b + T a
        [SMOD (I ^ n : Ideal R)] := by
    apply SModEq.mono hpow
    simpa only [contractingApproximation_succ] using
      SModEq.add
        (SModEq.rfl :
          b ≡ b [SMOD (I ^ (n + 1) : Ideal R)])
        hTcongr
  exact haleft.trans haright

private theorem eq_of_eq_add_of_maps_pow_succ
    (I : Ideal R) [IsHausdorff I R]
    (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (b : R) {x y : R}
    (hx : x = b + T x) (hy : y = b + T y) :
    x = y := by
  have hsub : ∀ n, x - y ∈ I ^ n := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, Ideal.one_eq_top]
        exact (Submodule.mem_top : x - y ∈ (⊤ : Ideal R))
    | succ n ih =>
        rw [hx, hy, add_sub_add_left_eq_sub, ← T.map_sub]
        exact hT n ih
  apply (IsHausdorff.eq_iff_smodEq (I := I)).2
  intro n
  rw [ideal_smul_top_eq_self, SModEq.sub_mem]
  exact hsub n

/-- An additive endomorphism which raises the `I`-adic filtration by one
has a unique affine fixed point on an `I`-adically complete ring. -/
theorem existsUnique_eq_add_of_maps_pow_succ
    (I : Ideal R) [IsAdicComplete I R]
    (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (b : R) :
    ∃! x : R, x = b + T x := by
  let x : ℕ → R := contractingApproximation T b
  have hcauchy : AdicCompletion.IsAdicCauchy I R x :=
    (AdicCompletion.isAdicCauchy_iff I R x).2 (by
      intro n
      rw [ideal_smul_top_eq_self, SModEq.sub_mem]
      simpa only [x] using contractingApproximation_sub_mem_pow I T hT b n)
  obtain ⟨a, ha⟩ :=
    (inferInstance : IsPrecomplete I R).prec hcauchy
  have ha' :
      ∀ n, x n ≡ a [SMOD (I ^ n : Ideal R)] := by
    intro n
    simpa only [ideal_smul_top_eq_self] using ha n
  have hfix : a = b + T a :=
    contractingApproximation_limit_is_fixed I T hT b a (by
      simpa only [x] using ha')
  refine ⟨a, hfix, ?_⟩
  intro y hy
  exact eq_of_eq_add_of_maps_pow_succ I T hT b hy hfix

end IsAdicComplete
