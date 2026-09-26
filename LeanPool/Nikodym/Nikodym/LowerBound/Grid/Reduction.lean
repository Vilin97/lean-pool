/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.PolynomialSpaces
public import LeanPool.Nikodym.Nikodym.LowerBound.Jets.Defs

/-!
# Bounded reduction modulo a power of a grid ideal

This file implements blueprint node **G01** of the lower-bound side of the sharp finite-field
Nikodym exponent.

Let `g i : K[T]` (`i : Fin d`) be monic univariate polynomials of common degree `q ≥ 1`, put
`Z i = g i (X i) ∈ P_d = MvPolynomial (Fin d) K` and `J = (Z 1, …, Z d)`. We show that every class
of `P_d ⧸ J ^ r` has a representative of total degree at most `U = q (r - 1) + d (q - 1)`.

* `Nikodym.LowerBound.Z g i`, `Nikodym.LowerBound.gridIdeal g`: the polynomials `Z i` and the
  ideal `J`;
* `Nikodym.LowerBound.totalDegree_Z_le`: `Z i` has total degree at most `q`;
* `Nikodym.LowerBound.exists_bounded_rep`: for every `f` there is `f'` of total degree at most
  `q (r - 1) + d (q - 1)` with `f - f' ∈ J ^ r`;
* `Nikodym.LowerBound.map_restrictTotalDegree_gridIdeal_pow_eq_top`: the same statement packaged
  as `P_{d, ≤ U} → P_d ⧸ J ^ r` being surjective (as a `K`-linear map).

The proof reduces one coordinate at a time: modulo `J`, every monomial is a combination of monomials
`X ^ α` with `α i < q` for all `i` (`exists_bounded_rep_one`), and an element of `J ^ r` is a
`P_d`-combination of products of `r` of the `Z i`; reducing the coefficients modulo `J` gives a
representative of degree at most `q r + d (q - 1)` modulo `J ^ (r + 1)` (`exists_bounded_rep_pow`).
Spanning is all that is proved; no basis statement is made.

For the finite grid `F ⊆ K` we also define the grid polynomial
`Nikodym.LowerBound.gridPoly F K = ∏ a : F, (T - ι a)`, record that it is monic of degree
`Fintype.card F` and vanishes on `ι (F)`, and deduce `Nikodym.LowerBound.Z_grid_mem_pointIdeal`:
the grid polynomials `Z i` lie in the point ideal of every grid point.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial Finset
open scoped Pointwise

/-! ### Grid ideals -/

section GridIdeal

variable {K : Type*} [Field K] {d : ℕ}

/-- Blueprint G01: the coordinate polynomial `Z i = g i (X i) ∈ P_d`. -/
noncomputable def Z (g : Fin d → Polynomial K) (i : Fin d) : MvPolynomial (Fin d) K :=
  Polynomial.aeval (X i) (g i)

/-- Blueprint G01: the grid ideal `J = (Z 1, …, Z d)`. -/
noncomputable def gridIdeal (g : Fin d → Polynomial K) : Ideal (MvPolynomial (Fin d) K) :=
  Ideal.span (Set.range (Z g))

/-- Blueprint G01: `Z i ∈ J`. -/
theorem Z_mem_gridIdeal (g : Fin d → Polynomial K) (i : Fin d) : Z g i ∈ gridIdeal g :=
  Ideal.subset_span ⟨i, rfl⟩

variable {g : Fin d → Polynomial K} {q : ℕ}

/-- Blueprint G01: `Z i = ∑_{k ≤ q} MvPolynomial.coeff k (g i) • X i ^ k`. -/
theorem Z_eq_sum (hdeg : ∀ i, (g i).natDegree = q) (i : Fin d) :
    Z g i = ∑ k ∈ range (q + 1), (g i).coeff k • X i ^ k := by
  rw [Z, Polynomial.aeval_eq_sum_range, hdeg]

/-- Blueprint G01: `Z i` has total degree at most `q`. -/
theorem totalDegree_Z_le (hdeg : ∀ i, (g i).natDegree = q) (i : Fin d) :
    (Z g i).totalDegree ≤ q := by
  rw [Z_eq_sum hdeg i]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun k hk ↦ ?_)
  rw [mem_range] at hk
  refine (totalDegree_smul_le _ _).trans ?_
  rw [totalDegree_X_pow]
  omega

/-- Blueprint G01: for monic `g i` of degree `q ≥ 1`, the difference `Z i - X i ^ q` has total
degree `< q`. -/
theorem totalDegree_Z_sub_X_pow_lt (hg : ∀ i, (g i).Monic) (hdeg : ∀ i, (g i).natDegree = q)
    (hq : 1 ≤ q) (i : Fin d) : (Z g i - X i ^ q).totalDegree < q := by
  have hcoeff : (g i).coeff q = 1 := by
    rw [← hdeg i]
    exact (hg i).coeff_natDegree
  rw [Z_eq_sum hdeg i, sum_range_succ, hcoeff, one_smul, add_sub_cancel_right]
  refine (totalDegree_finsetSum _ _).trans_lt
    ((Finset.sup_lt_iff (by change 0 < q; omega)).mpr fun k hk ↦ ?_)
  rw [mem_range] at hk
  refine (totalDegree_smul_le _ _).trans_lt ?_
  rw [totalDegree_X_pow]
  exact hk

/-- Blueprint G01: a monomial `X ^ α` with `α i < q` for all `i` has total degree at most
`d (q - 1)`. -/
theorem degree_le_of_forall_lt {α : Fin d →₀ ℕ} (hα : ∀ i, α i < q) : α.degree ≤ d * (q - 1) := by
  rw [Finsupp.degree_eq_sum]
  calc ∑ i, α i ≤ ∑ _i : Fin d, (q - 1) := sum_le_sum fun i _ ↦ by have := hα i; omega
    _ = d * (q - 1) := by simp

/-- Blueprint G01 (level `r = 1`): every polynomial is congruent modulo `J` to a polynomial of
total degree at most `d (q - 1)`. -/
theorem exists_bounded_rep_one (hg : ∀ i, (g i).Monic) (hdeg : ∀ i, (g i).natDegree = q)
    (hq : 1 ≤ q) (f : MvPolynomial (Fin d) K) :
    ∃ f' ∈ restrictTotalDegree (Fin d) K (d * (q - 1)), f - f' ∈ gridIdeal g := by
  classical
  -- the `K`-submodule of polynomials admitting a bounded representative
  set S : Submodule K (MvPolynomial (Fin d) K) :=
    restrictTotalDegree (Fin d) K (d * (q - 1)) ⊔ (gridIdeal g).restrictScalars K with hS
  have hS_iff : ∀ p, p ∈ S ↔ ∃ f' ∈ restrictTotalDegree (Fin d) K (d * (q - 1)),
      p - f' ∈ gridIdeal g := by
    intro p
    rw [hS, Submodule.mem_sup]
    constructor
    · rintro ⟨f', hf', j, hj, rfl⟩
      exact ⟨f', hf', by simpa using hj⟩
    · rintro ⟨f', hf', hj⟩
      exact ⟨f', hf', p - f', hj, by ring⟩
  have hRTD : ∀ n, ∀ p ∈ restrictTotalDegree (Fin d) K n, p ∈ S := by
    intro n
    induction n with
    | zero =>
      intro p hp
      exact Submodule.mem_sup_left (restrictTotalDegree_mono (Nat.zero_le _) hp)
    | succ n ih =>
      intro p hp
      rw [mem_restrictTotalDegree_iff_forall_support] at hp
      rw [p.as_sum]
      refine Submodule.sum_mem _ fun α hα ↦ ?_
      have hαn := hp α hα
      by_cases hle : α.degree ≤ n
      · exact ih _ (monomial_mem_restrictTotalDegree hle _)
      by_cases hlt : ∀ i, α i < q
      · exact Submodule.mem_sup_left
          (monomial_mem_restrictTotalDegree (degree_le_of_forall_lt hlt) _)
      push Not at hlt
      obtain ⟨i, hi⟩ := hlt
      set β : Fin d →₀ ℕ := α - Finsupp.single i q with hβ
      have hβα : β + Finsupp.single i q = α := by
        rw [hβ, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)]
      have hβdeg : β.degree + q = α.degree := by
        rw [← hβα, map_add, Finsupp.degree_single]
      have hsplit : monomial α (p.coeff α) =
          monomial β (p.coeff α) * Z g i - monomial β (p.coeff α) * (Z g i - X i ^ q) := by
        rw [mul_sub, sub_sub_cancel, X_pow_eq_monomial, monomial_mul_monomial, mul_one, hβα]
      rw [hsplit]
      refine Submodule.sub_mem _ (Submodule.mem_sup_right ?_) (ih _ ?_)
      · exact Ideal.mul_mem_left _ _ (Z_mem_gridIdeal g i)
      · rw [mem_restrictTotalDegree_iff]
        have h1 := totalDegree_mul (monomial β (p.coeff α)) (Z g i - X i ^ q)
        have h2 : (monomial β (p.coeff α)).totalDegree ≤ β.degree :=
          totalDegree_monomial_le β (p.coeff α)
        have h3 := totalDegree_Z_sub_X_pow_lt hg hdeg hq i
        omega
  exact (hS_iff f).mp (hRTD _ f (mem_restrictTotalDegree_iff.mpr le_rfl))

/-- Blueprint G01: a product of `n` of the polynomials `Z i` has total degree at most `q n`. -/
theorem totalDegree_le_of_mem_range_Z_pow (hdeg : ∀ i, (g i).natDegree = q) (n : ℕ) :
    ∀ p ∈ (Set.range (Z g)) ^ n, p.totalDegree ≤ q * n := by
  induction n with
  | zero =>
    intro p hp
    rw [pow_zero, Set.mem_one] at hp
    rw [hp, totalDegree_one]
    exact Nat.zero_le _
  | succ n ih =>
    intro p hp
    rw [pow_succ, Set.mem_mul] at hp
    obtain ⟨x, hx, y, ⟨i, rfl⟩, rfl⟩ := hp
    have h1 := totalDegree_mul x (Z g i)
    have h2 := ih x hx
    have h3 := totalDegree_Z_le hdeg i
    rw [Nat.mul_succ]
    omega

/-- Blueprint G01 (inductive step): every element of `J ^ n` is congruent modulo `J ^ (n + 1)` to
a polynomial of total degree at most `q n + d (q - 1)`. -/
theorem exists_bounded_rep_pow (hg : ∀ i, (g i).Monic) (hdeg : ∀ i, (g i).natDegree = q)
    (hq : 1 ≤ q) (n : ℕ) {j : MvPolynomial (Fin d) K} (hj : j ∈ gridIdeal g ^ n) :
    ∃ j' ∈ restrictTotalDegree (Fin d) K (q * n + d * (q - 1)),
      j - j' ∈ gridIdeal g ^ (n + 1) := by
  have hpow : gridIdeal g ^ n = Ideal.span (Set.range (Z g) ^ n) := Submodule.span_pow _ n
  rw [hpow] at hj
  have key : ∀ h : MvPolynomial (Fin d) K,
      ∃ j' ∈ restrictTotalDegree (Fin d) K (q * n + d * (q - 1)),
        h * j - j' ∈ gridIdeal g ^ (n + 1) := by
    induction hj using Submodule.span_induction with
    | mem p hp =>
      intro h
      obtain ⟨h', hh', hmem⟩ := exists_bounded_rep_one hg hdeg hq h
      have hpJ : p ∈ gridIdeal g ^ n := hpow ▸ Ideal.subset_span hp
      refine ⟨h' * p, ?_, ?_⟩
      · rw [add_comm]
        exact mul_mem_restrictTotalDegree' hh' (totalDegree_le_of_mem_range_Z_pow hdeg n p hp)
      · rw [← sub_mul, pow_succ']
        exact Ideal.mul_mem_mul hmem hpJ
    | zero =>
      intro h
      exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro h
      obtain ⟨jx, hjx, hx'⟩ := hx h
      obtain ⟨jy, hjy, hy'⟩ := hy h
      refine ⟨jx + jy, Submodule.add_mem _ hjx hjy, ?_⟩
      rw [mul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx' hy'
    | smul a x _ hx =>
      intro h
      obtain ⟨j', hj', hx'⟩ := hx (h * a)
      refine ⟨j', hj', ?_⟩
      rwa [smul_eq_mul, ← mul_assoc]
  simpa using key 1

/-- Blueprint G01: for every `r` and every `f ∈ P_d`, there is a polynomial `f'` of total degree at
most `U = q (r - 1) + d (q - 1)` with `f ≡ f'` modulo `J ^ r`. (For `r = 0` the statement is
trivial, so no hypothesis `1 ≤ r` is needed.) -/
theorem exists_bounded_rep (hg : ∀ i, (g i).Monic) (hdeg : ∀ i, (g i).natDegree = q)
    (hq : 1 ≤ q) (r : ℕ) (f : MvPolynomial (Fin d) K) :
    ∃ f' ∈ restrictTotalDegree (Fin d) K (q * (r - 1) + d * (q - 1)),
      f - f' ∈ gridIdeal g ^ r := by
  induction r with
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ r ih =>
    obtain ⟨f', hf', hmem⟩ := ih
    obtain ⟨j', hj', hmem'⟩ := exists_bounded_rep_pow hg hdeg hq r hmem
    refine ⟨f' + j', Submodule.add_mem _ ?_ ?_, ?_⟩
    · refine restrictTotalDegree_mono ?_ hf'
      rw [Nat.add_sub_cancel]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left q (Nat.sub_le r 1)) _
    · rwa [Nat.add_sub_cancel]
    · rwa [← sub_sub]

/-- Blueprint G01, packaged: the `K`-linear map `P_{d, ≤ U} → P_d ⧸ J ^ r` induced by the quotient
map is surjective, where `U = q (r - 1) + d (q - 1)`. -/
theorem map_restrictTotalDegree_gridIdeal_pow_eq_top (hg : ∀ i, (g i).Monic)
    (hdeg : ∀ i, (g i).natDegree = q) (hq : 1 ≤ q) (r : ℕ) :
    (restrictTotalDegree (Fin d) K (q * (r - 1) + d * (q - 1))).map
      (Ideal.Quotient.mkₐ K (gridIdeal g ^ r)).toLinearMap = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective v
  obtain ⟨f', hf', hmem⟩ := exists_bounded_rep hg hdeg hq r f
  refine ⟨f', hf', ?_⟩
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, ← neg_sub]
  exact Submodule.neg_mem _ hmem

end GridIdeal

/-! ### The finite grid -/

section Grid

variable (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K] {d : ℕ}

/-- Blueprint G01: the grid polynomial `∏_{a ∈ F} (T - ι a) ∈ K[T]`. -/
noncomputable def gridPoly : Polynomial K :=
  ∏ a : F, (Polynomial.X - Polynomial.C (algebraMap F K a))

/-- Blueprint G01: the grid polynomial is monic. -/
theorem gridPoly_monic : (gridPoly F K).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_X_sub_C _

/-- Blueprint G01: the grid polynomial has degree `q = |F|`. -/
theorem natDegree_gridPoly : (gridPoly F K).natDegree = Fintype.card F := by
  rw [gridPoly, Polynomial.natDegree_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_X_sub_C _]
  simp

variable {F}

/-- Blueprint G01: the grid polynomial vanishes on `ι (F)`. -/
theorem gridPoly_eval (a : F) : (gridPoly F K).eval (algebraMap F K a) = 0 := by
  rw [gridPoly, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)

variable {K} in
/-- Blueprint G01: for the grid polynomials, `Z i` lies in the point ideal of every grid point. -/
theorem Z_grid_mem_pointIdeal (x : Fin d → F) (i : Fin d) :
    Z (fun _ ↦ gridPoly F K) i ∈ pointIdeal (fun i ↦ algebraMap F K (x i)) := by
  rw [mem_pointIdeal, Z, ← coe_aeval_eq_eval, RingHom.coe_coe, ← Polynomial.aeval_algHom_apply,
    aeval_X, Polynomial.coe_aeval_eq_eval]
  exact gridPoly_eval K (x i)

end Grid

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
