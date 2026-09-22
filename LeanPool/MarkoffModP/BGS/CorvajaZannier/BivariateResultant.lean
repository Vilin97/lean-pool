/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.AuxiliaryFamily
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Degree bounds for bivariate resultants

Corvaja--Zannier eliminate the first variable from a defining polynomial
`f(U,V)` and an auxiliary relation `P(U,V)`.  They use the Sylvester
determinant estimate

`deg_V Res_U(f, P) ≤ deg_U(f) * deg_V(P) + deg_U(P) * deg_V(f)`.

Here bivariate polynomials are represented as polynomials in `U` whose
coefficients lie in `C[V]`.  The proof records the sharper columnwise degree
bound for determinants: each determinant term uses exactly one entry from
every Sylvester column, so the coefficient bounds add with the correct
multiplicities.
-/

namespace BGS.CorvajaZannier

noncomputable section

open scoped BigOperators

variable {C : Type*} [Field C]

/-- Exchange the two variables of an iterated bivariate polynomial.  Both the
source and target have Lean type `C[U][V]`; the target is interpreted as
`C[V][U]`. -/
def transposeBivariate :
    Polynomial (Polynomial C) →+* Polynomial (Polynomial C) :=
  Polynomial.eval₂RingHom
    (Polynomial.mapRingHom (Polynomial.C : C →+* Polynomial C))
    (Polynomial.C Polynomial.X)

@[simp]
theorem transposeBivariate_C (p : Polynomial C) :
    transposeBivariate (Polynomial.C p) = p.map Polynomial.C := by
  simp [transposeBivariate]

@[simp]
theorem transposeBivariate_X :
    transposeBivariate (Polynomial.X : Polynomial (Polynomial C)) =
      Polynomial.C Polynomial.X := by
  simp [transposeBivariate]

private theorem evalBivariate_add
    {L : Type*} [Field L] [Algebra C L]
    (u v : L) (P Q : Polynomial (Polynomial C)) :
    evalBivariate u v (P + Q) =
      evalBivariate u v P + evalBivariate u v Q := by
  unfold evalBivariate
  exact Polynomial.eval₂_add
    (Polynomial.eval₂RingHom (algebraMap C L) u) v

private theorem evalBivariate_mul
    {L : Type*} [Field L] [Algebra C L]
    (u v : L) (P Q : Polynomial (Polynomial C)) :
    evalBivariate u v (P * Q) =
      evalBivariate u v P * evalBivariate u v Q := by
  unfold evalBivariate
  exact Polynomial.eval₂_mul
    (Polynomial.eval₂RingHom (algebraMap C L) u) v

@[simp]
theorem evalBivariate_map_C
    {L : Type*} [Field L] [Algebra C L]
    (u v : L) (p : Polynomial C) :
    evalBivariate v u (p.map Polynomial.C) =
      p.eval₂ (algebraMap C L) u := by
  unfold evalBivariate
  rw [Polynomial.eval₂_map]
  congr 1
  exact Polynomial.eval₂RingHom_comp_C (algebraMap C L) v

@[simp]
theorem evalBivariate_C_X_pow
    {L : Type*} [Field L] [Algebra C L]
    (u v : L) (n : ℕ) :
    evalBivariate v u
      ((Polynomial.C Polynomial.X : Polynomial (Polynomial C)) ^ n) = v ^ n := by
  unfold evalBivariate
  rw [Polynomial.eval₂_pow, Polynomial.eval₂_C]
  change (Polynomial.eval₂ (algebraMap C L) v Polynomial.X) ^ n = v ^ n
  rw [Polynomial.eval₂_X]

/-- Swapping variables and then evaluating at the swapped point preserves the
value of a bivariate polynomial. -/
theorem evalBivariate_transposeBivariate
    {L : Type*} [Field L] [Algebra C L]
    (u v : L) (P : Polynomial (Polynomial C)) :
    evalBivariate v u (transposeBivariate P) = evalBivariate u v P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [map_add, evalBivariate_add, evalBivariate_add, hP, hQ]
  | monomial n p =>
      rw [show transposeBivariate (Polynomial.monomial n p) =
          p.map Polynomial.C *
            (Polynomial.C Polynomial.X : Polynomial (Polynomial C)) ^ n by
        simp [transposeBivariate, Polynomial.eval₂_monomial]]
      rw [evalBivariate_mul, evalBivariate_map_C, evalBivariate_C_X_pow]
      unfold evalBivariate
      rw [Polynomial.eval₂_monomial]
      rfl

/-- A coefficientwise degree bound becomes an outer degree bound after
transposing the variables. -/
theorem transposeBivariate_natDegree_le
    (P : Polynomial (Polynomial C)) (k : ℕ)
    (hcoeff : ∀ s, (P.coeff s).natDegree ≤ k) :
    (transposeBivariate P).natDegree ≤ k := by
  classical
  change (P.eval₂
    (Polynomial.mapRingHom (Polynomial.C : C →+* Polynomial C))
    (Polynomial.C Polynomial.X)).natDegree ≤ k
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s _
  calc
    ((P.coeff s).map Polynomial.C *
        (Polynomial.C Polynomial.X : Polynomial (Polynomial C)) ^ s).natDegree
        ≤ ((P.coeff s).map Polynomial.C).natDegree +
          ((Polynomial.C Polynomial.X : Polynomial (Polynomial C)) ^ s).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ k + 0 := by
      exact Nat.add_le_add
        (Polynomial.natDegree_map_le.trans (hcoeff s)) (by simp)
    _ = k := Nat.add_zero k

/-- An outer degree bound becomes a coefficientwise degree bound after
transposing the variables. -/
theorem transposeBivariate_coeff_natDegree_le
    (P : Polynomial (Polynomial C)) (h : ℕ)
    (hdegree : P.natDegree ≤ h) (r : ℕ) :
    ((transposeBivariate P).coeff r).natDegree ≤ h := by
  classical
  change ((P.eval₂
    (Polynomial.mapRingHom (Polynomial.C : C →+* Polynomial C))
    (Polynomial.C Polynomial.X)).coeff r).natDegree ≤ h
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  rw [show (Polynomial.C Polynomial.X : Polynomial (Polynomial C)) ^ s =
      Polynomial.C (Polynomial.X ^ s) by simp]
  rw [Polynomial.coeff_mul_C, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]
  exact (Polynomial.natDegree_C_mul_X_pow_le _ s).trans
    ((Polynomial.le_natDegree_of_mem_supp s hs).trans hdegree)

private theorem auxiliaryPowerPolynomial_mul_one_sub_X_natDegree_le
    {k : ℕ} (hk : 0 < k) (c : Fin k → C) :
    (auxiliaryPowerPolynomial c * (1 - Polynomial.X)).natDegree ≤ k := by
  have hfactor :
      (1 - Polynomial.X : Polynomial C).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  calc
    (auxiliaryPowerPolynomial c * (1 - Polynomial.X)).natDegree
        ≤ (auxiliaryPowerPolynomial c).natDegree +
          (1 - Polynomial.X : Polynomial C).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (auxiliaryPowerPolynomial c).natDegree + 1 :=
      Nat.add_le_add_left hfactor _
    _ ≤ k := by
      have := auxiliaryPowerPolynomial_natDegree_lt hk c
      omega

/-- The source-oriented auxiliary relation has degree at most `h` in its
outer variable `V`. -/
theorem auxiliaryRelationPolynomial_natDegree_le
    {h k : ℕ} (hh : 0 < h) (c : Fin k → C)
    (d : Fin (k + 1) × Fin h → C) :
    (auxiliaryRelationPolynomial c d).natDegree ≤ h := by
  have hfactor :
      (1 - Polynomial.X : Polynomial (Polynomial C)).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hgrid : (auxiliaryGridPolynomial d).natDegree + 1 ≤ h := by
    have := auxiliaryGridPolynomial_natDegree_lt hh d
    omega
  have hconstant :
      (Polynomial.C
        (auxiliaryPowerPolynomial c * (1 - Polynomial.X)) :
          Polynomial (Polynomial C)).natDegree ≤ h := by
    rw [Polynomial.natDegree_C]
    exact Nat.zero_le h
  unfold auxiliaryRelationPolynomial
  apply Polynomial.natDegree_add_le_of_degree_le
  · simpa only [map_mul, map_sub, map_one, Polynomial.map_X] using hconstant
  · calc
      (auxiliaryGridPolynomial d * (1 - Polynomial.X)).natDegree
          ≤ (auxiliaryGridPolynomial d).natDegree +
            (1 - Polynomial.X : Polynomial (Polynomial C)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (auxiliaryGridPolynomial d).natDegree + 1 :=
        Nat.add_le_add_left hfactor _
      _ ≤ h := hgrid

/-- Every `V`-coefficient of the source-oriented auxiliary relation has
`U`-degree at most `k`. -/
theorem auxiliaryRelationPolynomial_coeff_natDegree_le
    {h k : ℕ} (hk : 0 < k) (c : Fin k → C)
    (d : Fin (k + 1) × Fin h → C) (s : ℕ) :
    ((auxiliaryRelationPolynomial c d).coeff s).natDegree ≤ k := by
  let A : Polynomial C := auxiliaryPowerPolynomial c * (1 - Polynomial.X)
  let G : Polynomial (Polynomial C) := auxiliaryGridPolynomial d
  have hA : A.natDegree ≤ k :=
    auxiliaryPowerPolynomial_mul_one_sub_X_natDegree_le hk c
  have hG (i : ℕ) : (G.coeff i).natDegree ≤ k :=
    auxiliaryGridPolynomial_coeff_natDegree_le d i
  have hrewrite : auxiliaryRelationPolynomial c d =
      Polynomial.C A + G - G * Polynomial.X := by
    simp only [auxiliaryRelationPolynomial, A, G]
    ring
  rw [hrewrite]
  cases s with
  | zero =>
      simp only [Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_C_zero, Polynomial.coeff_mul_X_zero, sub_zero]
      exact Polynomial.natDegree_add_le_of_degree_le hA (hG 0)
  | succ s =>
      simp only [Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_C, ite_eq_right (Nat.succ_ne_zero s), zero_add,
        Polynomial.coeff_mul_X]
      simpa using Polynomial.natDegree_sub_le_of_le (hG (s + 1)) (hG s)

/-- In the `U`-oriented representation required by `Res_U`, the auxiliary
relation has `U`-degree at most `k`. -/
theorem transpose_auxiliaryRelationPolynomial_natDegree_le
    {h k : ℕ} (hk : 0 < k) (c : Fin k → C)
    (d : Fin (k + 1) × Fin h → C) :
    (transposeBivariate (auxiliaryRelationPolynomial c d)).natDegree ≤ k :=
  transposeBivariate_natDegree_le _ k
    (auxiliaryRelationPolynomial_coeff_natDegree_le hk c d)

/-- In the `U`-oriented representation required by `Res_U`, every coefficient
has `V`-degree at most `h`. -/
theorem transpose_auxiliaryRelationPolynomial_coeff_natDegree_le
    {h k : ℕ} (hh : 0 < h) (c : Fin k → C)
    (d : Fin (k + 1) × Fin h → C) (r : ℕ) :
    ((transposeBivariate (auxiliaryRelationPolynomial c d)).coeff r).natDegree ≤ h :=
  transposeBivariate_coeff_natDegree_le _ h
    (auxiliaryRelationPolynomial_natDegree_le hh c d) r

/-- A determinant over `C[V]` has degree at most the sum of columnwise degree
bounds. -/
theorem Matrix.natDegree_det_le_sum_columnDegree
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial C)) (columnDegree : n → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ columnDegree j) :
    M.det.natDegree ≤ ∑ j, columnDegree j := by
  classical
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  calc
    (Equiv.Perm.sign σ * ∏ i, M (σ i) i).natDegree
        ≤ (∏ i, M (σ i) i).natDegree := by
          exact Polynomial.natDegree_C_mul_le _ _
    _ ≤ ∑ i, (M (σ i) i).natDegree := by
      simpa using Polynomial.natDegree_prod_le Finset.univ (fun i => M (σ i) i)
    _ ≤ ∑ i, columnDegree i := by
      exact Finset.sum_le_sum fun i _ => hM (σ i) i

/-- The exact coefficient-degree estimate for a resultant over `C[V]`.

`f` has `U`-degree bounded by `m` and every `V`-coefficient degree bounded by
`df`; `g` has the analogous bounds `n` and `dg`. -/
theorem natDegree_resultant_le
    (f g : Polynomial (Polynomial C)) (m n df dg : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ dg) :
    (Polynomial.resultant f g m n).natDegree ≤ m * dg + n * df := by
  rw [Polynomial.resultant]
  let columnDegree : Fin (m + n) → ℕ := fun j =>
    j.addCases (fun _ => dg) (fun _ => df)
  have hcolumns : ∀ i j,
      ((Polynomial.sylvester f g m n) i j).natDegree ≤ columnDegree j := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left,
          columnDegree]
        split_ifs
        · exact hg _
        · simp
    | right j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right,
          columnDegree]
        split_ifs
        · exact hf _
        · simp
  calc
    (Polynomial.sylvester f g m n).det.natDegree
        ≤ ∑ j, columnDegree j :=
      Matrix.natDegree_det_le_sum_columnDegree
        (Polynomial.sylvester f g m n) columnDegree hcolumns
    _ = m * dg + n * df := by
      simp [columnDegree, Fin.sum_univ_add]

/-- The source-faithful version using the ordinary resultant at the actual
degrees, while bounding those degrees by `m` and `n`. -/
theorem natDegree_resultant_le_of_degree_le
    (f g : Polynomial (Polynomial C)) (m n df dg : ℕ)
    (hfDegree : f.natDegree ≤ m) (hgDegree : g.natDegree ≤ n)
    (hf : ∀ i, (f.coeff i).natDegree ≤ df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ dg) :
    (Polynomial.resultant f g).natDegree ≤ m * dg + n * df := by
  calc
    (Polynomial.resultant f g).natDegree
        ≤ f.natDegree * dg + g.natDegree * df :=
      natDegree_resultant_le f g f.natDegree g.natDegree df dg hf hg
    _ ≤ m * dg + n * df := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_right dg hfDegree)
        (Nat.mul_le_mul_right df hgDegree)

/-- The exact Corvaja--Zannier resultant degree bound for the transposed
auxiliary relation. -/
theorem natDegree_resultant_auxiliaryRelation_le
    (f : Polynomial (Polynomial C)) (a b h k : ℕ) (hh : 0 < h)
    (c : Fin k → C) (d : Fin (k + 1) × Fin h → C)
    (hf : ∀ i, (f.coeff i).natDegree ≤ b) :
    (Polynomial.resultant f
      (transposeBivariate (auxiliaryRelationPolynomial c d)) a k).natDegree
      ≤ a * h + k * b :=
  natDegree_resultant_le f
    (transposeBivariate (auxiliaryRelationPolynomial c d)) a k b h hf
    (transpose_auxiliaryRelationPolynomial_coeff_natDegree_le hh c d)

/-- The ordinary-resultant degree bound for the transposed auxiliary relation.
This is the version used by the subsequent irreducibility/divisibility
argument. -/
theorem natDegree_resultant_auxiliaryRelation_default_le
    (f : Polynomial (Polynomial C)) (a b h k : ℕ)
    (hh : 0 < h) (hk : 0 < k)
    (c : Fin k → C) (d : Fin (k + 1) × Fin h → C)
    (hfDegree : f.natDegree ≤ a)
    (hf : ∀ i, (f.coeff i).natDegree ≤ b) :
    (Polynomial.resultant f
      (transposeBivariate (auxiliaryRelationPolynomial c d))).natDegree
      ≤ a * h + k * b :=
  natDegree_resultant_le_of_degree_le f
    (transposeBivariate (auxiliaryRelationPolynomial c d)) a k b h
    hfDegree (transpose_auxiliaryRelationPolynomial_natDegree_le hk c d) hf
    (transpose_auxiliaryRelationPolynomial_coeff_natDegree_le hh c d)

/-- Two polynomials of the prescribed degree bounds with a common root have
zero explicit-degree resultant. -/
theorem resultant_eq_zero_of_common_root
    {K : Type*} [Field K] (f g : Polynomial K) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hmn : m ≠ 0 ∨ n ≠ 0) (x : K)
    (hfx : f.eval x = 0) (hgx : g.eval x = 0) :
    Polynomial.resultant f g m n = 0 := by
  obtain ⟨p, q, _, _, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hmn
  have heval := congrArg (Polynomial.eval x) hbezout
  simpa [hfx, hgx] using heval.symm

/-- If two bivariate polynomials vanish at `(u,v)`, their resultant in `U`
vanishes at `v`. -/
theorem eval₂_resultant_eq_zero_of_common_zero
    {L : Type*} [Field L] [Algebra C L]
    (f g : Polynomial (Polynomial C)) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hmn : m ≠ 0 ∨ n ≠ 0) (u v : L)
    (hfu : evalBivariate v u f = 0)
    (hgu : evalBivariate v u g = 0) :
    (Polynomial.resultant f g m n).eval₂ (algebraMap C L) v = 0 := by
  let ev : Polynomial C →+* L :=
    Polynomial.eval₂RingHom (algebraMap C L) v
  have hfmap : (f.map ev).natDegree ≤ m :=
    Polynomial.natDegree_map_le.trans hf
  have hgmap : (g.map ev).natDegree ≤ n :=
    Polynomial.natDegree_map_le.trans hg
  have hfeval : (f.map ev).eval u = 0 := by
    simpa [ev, evalBivariate, Polynomial.eval_map] using hfu
  have hgeval : (g.map ev).eval u = 0 := by
    simpa [ev, evalBivariate, Polynomial.eval_map] using hgu
  have hmapped : Polynomial.resultant (f.map ev) (g.map ev) m n = 0 :=
    resultant_eq_zero_of_common_root
      (f.map ev) (g.map ev) m n hfmap hgmap hmn u hfeval hgeval
  rw [Polynomial.resultant_map_map] at hmapped
  exact hmapped

/-- The common-zero implication specialized to the Corvaja--Zannier
auxiliary relation. -/
theorem eval₂_resultant_auxiliaryRelation_eq_zero_of_common_zero
    {L : Type*} [Field L] [Algebra C L]
    (f : Polynomial (Polynomial C)) (a h k : ℕ)
    (ha : 0 < a) (hk : 0 < k)
    (c : Fin k → C) (d : Fin (k + 1) × Fin h → C)
    (hfDegree : f.natDegree ≤ a) (u v : L)
    (hfZero : evalBivariate v u f = 0)
    (hauxZero :
      evalBivariate u v (auxiliaryRelationPolynomial c d) = 0) :
    (Polynomial.resultant f
      (transposeBivariate (auxiliaryRelationPolynomial c d)) a k).eval₂
        (algebraMap C L) v = 0 := by
  apply eval₂_resultant_eq_zero_of_common_zero f
    (transposeBivariate (auxiliaryRelationPolynomial c d)) a k
    hfDegree (transpose_auxiliaryRelationPolynomial_natDegree_le hk c d)
    (Or.inl ha.ne') u v hfZero
  rw [evalBivariate_transposeBivariate]
  exact hauxZero

/-- A nonzero polynomial vanishing at an algebraic element has degree at least
the degree of that element's minimal polynomial. -/
theorem minpoly_natDegree_le_of_eval₂_eq_zero
    {L : Type*} [Field L] [Algebra C L]
    (y : L) (P : Polynomial C) (hP : P ≠ 0)
    (hzero : P.eval₂ (algebraMap C L) y = 0) :
    (minpoly C y).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_le_of_dvd (minpoly.dvd C y ?_) hP
  simpa [Polynomial.aeval_def] using hzero

/-- A polynomial whose degree is strictly smaller than the minimal-polynomial
degree cannot vanish at the element unless it is zero. -/
theorem eq_zero_of_natDegree_lt_minpoly_of_eval₂_eq_zero
    {L : Type*} [Field L] [Algebra C L]
    (y : L) (P : Polynomial C)
    (hdegree : P.natDegree < (minpoly C y).natDegree)
    (hzero : P.eval₂ (algebraMap C L) y = 0) : P = 0 := by
  by_contra hP
  exact (not_lt_of_ge (minpoly_natDegree_le_of_eval₂_eq_zero y P hP hzero))
    hdegree

/-- The complete nonzero-resultant contradiction in the
Corvaja--Zannier auxiliary-family argument.  Under `a*h + k*b < q` and
minimal-polynomial degree `q`, the resultant must vanish identically. -/
theorem resultant_auxiliaryRelation_eq_zero_of_common_zero
    {L : Type*} [Field L] [Algebra C L]
    (f : Polynomial (Polynomial C)) (a b h k q : ℕ)
    (ha : 0 < a) (hh : 0 < h) (hk : 0 < k)
    (c : Fin k → C) (d : Fin (k + 1) × Fin h → C)
    (hfDegree : f.natDegree ≤ a)
    (hfCoeffDegree : ∀ i, (f.coeff i).natDegree ≤ b)
    (u v : L) (hminpoly : (minpoly C v).natDegree = q)
    (hfZero : evalBivariate v u f = 0)
    (hauxZero :
      evalBivariate u v (auxiliaryRelationPolynomial c d) = 0)
    (hsize : a * h + k * b < q) :
    Polynomial.resultant f
      (transposeBivariate (auxiliaryRelationPolynomial c d)) a k = 0 := by
  apply eq_zero_of_natDegree_lt_minpoly_of_eval₂_eq_zero v
  · rw [hminpoly]
    exact (natDegree_resultant_auxiliaryRelation_le
      f a b h k hh c d hfCoeffDegree).trans_lt hsize
  · exact eval₂_resultant_auxiliaryRelation_eq_zero_of_common_zero
      f a h k ha hk c d hfDegree u v hfZero hauxZero

/-- Over a field, an irreducible polynomial divides any nonzero polynomial
with which it has zero resultant. -/
theorem irreducible_dvd_of_resultant_eq_zero
    {K : Type*} [Field K] {f g : Polynomial K}
    (hf : Irreducible f)
    (hresultant : Polynomial.resultant f g = 0) : f ∣ g := by
  have hnotCoprime : ¬ IsCoprime f g :=
    (Polynomial.resultant_eq_zero_iff.mp hresultant).2
  exact (hf.dvd_iff_not_isCoprime).mpr hnotCoprime

/-- The zero-resultant divisibility branch after embedding the coefficient
ring into a field (in the application, `C[V] → C(V)`). -/
theorem map_dvd_of_resultant_eq_zero
    {R K : Type*} [CommRing R] [Field K]
    (f g : Polynomial R) (phi : R →+* K) (hphi : Function.Injective phi)
    (hf : Irreducible (f.map phi))
    (hresultant : Polynomial.resultant f g = 0) :
    f.map phi ∣ g.map phi := by
  have hfgDegree : (f.map phi).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hphi f
  have hggDegree : (g.map phi).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hphi g
  have hresultantMappedExplicit :
      Polynomial.resultant (f.map phi) (g.map phi)
        f.natDegree g.natDegree = 0 := by
    rw [Polynomial.resultant_map_map, hresultant, map_zero]
  have hresultantMapped :
      Polynomial.resultant (f.map phi) (g.map phi) = 0 := by
    simpa only [hfgDegree, hggDegree] using hresultantMappedExplicit
  exact irreducible_dvd_of_resultant_eq_zero hf hresultantMapped

/-- The zero-resultant branch already forces the defining polynomial's
degree in the eliminated variable to be no larger than that of the auxiliary
relation after any injective coefficient-field embedding. -/
theorem natDegree_le_of_map_irreducible_of_resultant_eq_zero
    {R K : Type*} [CommRing R] [Field K]
    (f g : Polynomial R) (phi : R →+* K) (hphi : Function.Injective phi)
    (hf : Irreducible (f.map phi)) (hg : g ≠ 0)
    (hresultant : Polynomial.resultant f g = 0) :
    f.natDegree ≤ g.natDegree := by
  have hdvd := map_dvd_of_resultant_eq_zero f g phi hphi hf hresultant
  have hgmapped : g.map phi ≠ 0 := by
    intro hzero
    apply hg
    apply Polynomial.map_injective phi hphi
    simpa using hzero
  rw [← Polynomial.natDegree_map_eq_of_injective hphi f,
    ← Polynomial.natDegree_map_eq_of_injective hphi g]
  exact Polynomial.natDegree_le_of_dvd hdvd hgmapped

end

end BGS.CorvajaZannier
