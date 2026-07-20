/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Sym.Card

/-!
# The Bannai-Bannai-Stanton bound on distance sets

Formalizes the Bannai-Bannai-Stanton theorem bounding the size of a distance
set `S` in `ℝ^d` with `s` distinct distances by `Nat.choose (d + s) s`, following
the short proof of Petrov and Pohoata via the Croot-Lev-Pach lemma.
-/

open MvPolynomial

namespace BannaiBannaiStanton

-- Given a set S (possibly infinite) in a metric space, we define its distance set
-- as the set of all distances between distinct points in S.
/-- The set of distances realized between distinct points of a set `S`. -/
def distanceSet {M : Type*} [MetricSpace M] (S : Set M) : Set ℝ :=
  { r : ℝ | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ r = dist x y }

section Polynomials

variable {R : Type*} [CommRing R]

-- Some useful definitions of polynomials.
-- We define the squared distance polynomial
-- in 2d variables (representing two points in ℝ^d):
/-- The squared-distance polynomial used to encode pairwise distances of a distance set. -/
noncomputable def distPoly (d : ℕ) :
  MvPolynomial (Fin (2 * d)) R :=
  ∑ i : Fin d,
    (X (Fin.castLE (by linarith) i) - X ⟨d + i, by omega⟩)^2

-- For a fixed point y ∈ R^d, we define the squared distance polynomial in d variables
-- representing the squared distance from y:
/-- The squared-distance polynomial expressed from a fixed reference point. -/
noncomputable def distPolyFrom {d : ℕ}
 (y : EuclideanSpace R (Fin d)) : MvPolynomial (Fin d) R :=
  ∑ i : Fin d, (X i - C (y i))^2

-- The product of the polynomials (r^2 - distPoly) for all r in a finite set D.
/-- The product over a finite distance set of the shifted squared-distance polynomials. -/
noncomputable def productDistPoly (d : ℕ) (D : Finset R) :
    MvPolynomial (Fin (2 * d)) R :=
  ∏ r ∈ D, (C (r^2) - distPoly d)

-- The product of the polynomials (r^2 - distPolyFrom y) for all r in a finite set D.
/-- The product form of `productDistPoly` taken from a fixed reference point. -/
noncomputable def productDistPolyFrom {d : ℕ}
  (y : EuclideanSpace R (Fin d)) (D : Finset R) : MvPolynomial (Fin d) R :=
  ∏ r ∈ D, (C (r^2) - distPolyFrom y)

-- Bound on the total degree of distPolyFrom.
lemma degree_distPolyFrom_le {d : ℕ}
    (y : EuclideanSpace R (Fin d)) :
     (distPolyFrom y).totalDegree ≤ 2 := by
  by_cases R_nontrivial : Nontrivial R
  · apply (totalDegree_finsetSum _ _).trans
    simp only [sub_eq_add_neg, Finset.sup_le_iff, Finset.mem_univ, forall_const]
    intro i
    apply (totalDegree_pow _ _).trans
    rw [mul_le_iff_le_one_right Nat.zero_lt_two]
    apply (totalDegree_add _ _).trans
    simp [totalDegree_X, totalDegree_neg]
  · rw [not_nontrivial_iff_subsingleton] at R_nontrivial
    simp [Subsingleton.elim (distPolyFrom y) 0]

-- Bound on the total degree of distPoly.
lemma degree_distPoly (d : ℕ) :
    (distPoly d : MvPolynomial (Fin (2 * d)) R).totalDegree ≤ 2 := by
  by_cases R_nontrivial : Nontrivial R
  · apply (totalDegree_finsetSum _ _).trans
    simp only [sub_eq_add_neg, Finset.sup_le_iff, Finset.mem_univ, forall_const]
    intro i
    apply (totalDegree_pow _ _).trans
    rw [mul_le_iff_le_one_right Nat.zero_lt_two]
    apply (totalDegree_add _ _).trans
    simp [totalDegree_X, totalDegree_neg]
  · rw [not_nontrivial_iff_subsingleton] at R_nontrivial
    simp [Subsingleton.elim (distPoly d)  0]

-- Bound on the total degree of productDistPoly.
lemma degree_productDistPoly_le
    {d : ℕ}
    (D : Finset R) : (productDistPoly d D).totalDegree ≤ 2 * D.card := by
  apply (totalDegree_finsetProd _ _).trans
  have : ∑ r ∈ D, 2 =  2 * D.card:= by simp [mul_comm]
  -- each degree is ≤ 2 by previous lemma
  rw [← this]
  apply Finset.sum_le_sum
  intro i hi
  apply (totalDegree_sub _ _).trans
  simpa only [totalDegree_neg, totalDegree_C, zero_le, sup_of_le_right] using degree_distPoly d

-- Bound on the total degree of productDistPolyFrom.
lemma degree_productDistPolyFrom_le
    {d : ℕ}
    (y : EuclideanSpace R (Fin d)) (D : Finset R) :
    totalDegree (productDistPolyFrom y D) ≤ 2 * D.card := by
  -- Degree of a product is ≤ sum of degrees
  apply (totalDegree_finsetProd _ _).trans
  have : ∑ r ∈ D, 2 =  2 * D.card:= by simp only [Finset.sum_const, smul_eq_mul, mul_comm]
  -- each degree is ≤ 2 by previous lemma
  rw [← this]
  apply Finset.sum_le_sum
  intro i hi
  -- Degree of (C - P) is ≤ max(degree C, degree P)
  apply (totalDegree_sub _ _).trans
  simpa only [totalDegree_C, zero_le, sup_of_le_right] using degree_distPolyFrom_le _

-- Connecting distPoly and distPolyFrom via evaluation. More precisely,
-- evaluating distPoly at the point (x,y) ∈ R^{2d} is equivalent to
-- evaluating distPolyFrom y at the point x ∈ R^d.
lemma eval_distPoly_eq_eval_distPolyFrom {d : ℕ}
    (x y : EuclideanSpace R (Fin d)) :
    eval ((Fin.append x y) ∘ Fin.cast (by rw [two_mul])) (distPoly d) =
    eval x (distPolyFrom y) := by
  simp only [distPoly, map_sum, map_pow, map_sub, eval_X, Function.comp_apply, Fin.cast_castLE,
    Fin.append_left', Fin.cast_mk, distPolyFrom, eval_C]
  congr with i
  congr
  change Fin.append x.ofLp y.ofLp (Fin.natAdd d i) = y.ofLp i
  rw [Fin.append_right]

-- Evaluating the polynomial productDistPolyFrom y at y
-- yields a non-zero value (provided 0 is not in the distance set D).
-- This requires R to be an integral domain.
lemma eval_productDistPolyFrom_eq
    {d : ℕ} [IsDomain R]
    (y : EuclideanSpace R (Fin d)) (D : Finset R) (h_nul : 0 ∉ D) :
    eval y (productDistPolyFrom y D) ≠ 0 := by
  unfold productDistPolyFrom distPolyFrom
  simpa [Finset.prod_eq_zero_iff]

-- In ℝ, evaluating the polynomial productDistPolyFrom y at a point x
-- yields 0 (provided dist(x,y) ∈ D).
lemma eval_productDistPolyFrom_ne {d : ℕ} (x y : EuclideanSpace ℝ (Fin d))
 (D : Finset ℝ) (h_dist : dist x y ∈ D) :
    -- For Real Euclidean Space specifically:
    eval x (productDistPolyFrom y D) = 0 := by
  unfold productDistPolyFrom distPolyFrom
  simp only [map_prod, map_sub, map_pow, eval_C, map_sum, eval_X, Finset.prod_eq_zero_iff]
  use dist x y, h_dist
  rw [PiLp.dist_sq_eq_of_L2, sub_eq_zero]
  congr with i
  rw [sq_eq_sq_iff_abs_eq_abs, abs_dist]; rfl

end Polynomials

section Finiteness

variable {R : Type*} [CommRing R]

-- The "Diagonal" Argument:
-- If a family of vectors (here, polynomials) evaluates to 0 off-diagonal
-- and non-zero on-diagonal with respect to a family of points, it is linearly independent.
lemma linearIndependent_of_eval_eq_zero
    {d : ℕ} [IsDomain R]
    {ι : Type*}
    (f : ι → MvPolynomial (Fin d) R) (p : ι → EuclideanSpace R (Fin d))
    (h_diag : ∀ i, eval (p i) (f i) ≠ 0)
    (h_off : ∀ i j : ι, i ≠ j → eval (p j) (f i) = 0) :
    LinearIndependent R f := by
  rw [linearIndependent_iff']
  intro s g h_sum i hi
  have : 0 = g i * eval (p i) (f i) := by
    calc
    0 = eval (p i) (0) := by simp only [map_zero]
    _ = eval (p i) (∑ t ∈ s, g t • f t) := by rw [h_sum]
    _ = g i * eval (p i) (f i) := by
      simp only [map_sum, smul_eval]
      rw [Finset.sum_eq_single i (fun t g hti ↦ ?_) (fun h => (h hi).elim)]
      rwa [h_off, mul_zero]
  exact (mul_eq_zero_iff_right (h_diag i)).mp (this.symm)

lemma finite_distance_set_imp_finite_set
    {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hdis_fin : (distanceSet S).Finite) : S.Finite := by
  let D : Finset ℝ := hdis_fin.toFinset
  -- Define the family of polynomials: For every y ∈ S, P_y.
  let p : S → EuclideanSpace ℝ (Fin d) := fun y => y.1
  let f : S → MvPolynomial (Fin d) ℝ := fun y => productDistPolyFrom (p y) D
  -- Bound on the dimension of the space where the range of f lives.
  -- The range of f lives in a finite dimensional vector space
  -- of polynomials of degree ≤ 2*s where s = card(D).
  have h_deg (y) : f y ∈ restrictTotalDegree (Fin d) ℝ (2 * D.card) :=
      (mem_restrictTotalDegree _ _ _).mpr (degree_productDistPolyFrom_le _ _)
  -- Lift the family f to the submodule.
  let f_sub : S → restrictTotalDegree (Fin d) ℝ (2 * D.card) := fun y => ⟨f y, h_deg y⟩
  -- 0 is not in D.
  have zero_not_in : 0 ∉ D := by simp [D, distanceSet]
  -- Any distance dist(p y, p x) is in D when x ≠ y and x,y ∈ S.
  have dist_in_D (x : S) (y : S) (hxy : x ≠ y) : dist (p x) (p y) ∈ D := by
    simp only [distanceSet, ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq, D, p]
    refine ⟨x.1, x.2, y.1, y.2, Subtype.coe_ne_coe.mpr hxy, rfl⟩
  -- Prove linear independence of f_sub using the diagonal argument.
  have h_li : LinearIndependent ℝ f := by
    refine linearIndependent_of_eval_eq_zero f p (fun i ↦ ?_) (fun i j h_ij ↦ ?_)
    · exact (eval_productDistPolyFrom_eq (p i) D) zero_not_in
    · exact (eval_productDistPolyFrom_ne (p j) (p i) D) (dist_in_D _ _ h_ij.symm )
  -- Lift linear independence to the submodule.
  have h_li_sub : LinearIndependent ℝ f_sub := by
    rw [linearIndependent_iff'] at h_li ⊢
    intro s g h_sum i hi
    apply h_li s g _ i hi
    -- We just need to show the sum equals 0 in the larger space
    apply_fun Submodule.subtype (restrictTotalDegree (Fin d) ℝ (2 * D.card)) at h_sum
    simp only [map_sum, map_smul, map_zero] at h_sum
    exact h_sum
  -- Conclusion: An LI set in a finite dimensional space must be finite.
  exact LinearIndependent.finite h_li_sub

end Finiteness

section Dimension


variable {F : Type*} [Field F]

-- Definition of the dimension of the space of polynomial functions of
-- degree ≤ s on a set A ⊆ F^d. This is defined as the dimension of
-- the range of the evaluation map from the submodule of
-- multivariate polynomials of restricted degree ≤ s to the space of functions A → F.
-- We first define this evaluation map.
/-- Evaluation of restricted polynomials as a linear map on bounded-degree monomials. -/
noncomputable def evalMapRestricted {d : ℕ}
  (A : Finset (EuclideanSpace F (Fin d))) (s : ℕ) :
    restrictTotalDegree (Fin d) F s →ₗ[F] (A → F) := {
  toFun := fun p a => eval (a : Fin d → F) p.1
  map_add' := by intros; ext; simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' := by intros; ext; simp only [SetLike.val_smul, smul_eval, RingHom.id_apply,
    Pi.smul_apply, smul_eq_mul]}

-- Now we define dim A s as the finite rank (dimension) of the range of evalMapRestricted A s.
/-- The dimension of the space of polynomials of bounded total degree used in the rank bound. -/
noncomputable def dim {d : ℕ}
    (A : Finset (EuclideanSpace F (Fin d))) (s : ℕ) : ℕ :=
  Module.finrank F (LinearMap.range (evalMapRestricted A s))

-- By the rank-nullity theorem, we can bound dim A s by
-- the number of monomials in F[X_0,...,X_{d-1}] of degree ≤ s,
-- which is given by (d + s) choose s = (s + d) choose d (a classic stars & bars
-- combinatorial argument). While this counting argument is standard,
-- its formalization in Mathlib requires some work. We utilise the lemma
-- `Sym.card_sym_eq_choose`, which counts the elements in the d-th symmetric
-- power of a type α (representing d-tuples up to permutation).
-- This is relevant because monomials of degree ≤ s in d variables are
-- in bijection with multisets over Fin d of cardinality ≤ s.
-- We establish equivalences to count the number of such monomials.
-- This section involves significant technical details. We first define an equivalence
-- between monomials of degree ≤ s and multisets over Fin d of cardinality ≤ s.
open Multiset

/-- Sends a bounded-degree monomial exponent vector to its multiset of variables. -/
noncomputable def finsuppToMultisetRestricted {d s : ℕ} :
  {f : Fin d →₀ ℕ | f.sum (fun _ n ↦ n) ≤ s} ≃ {m : Multiset (Fin d) // Multiset.card m ≤ s} :=
  Equiv.subtypeEquiv Multiset.toFinsupp.symm.toEquiv (by
    intro f
    simp [AddEquiv.toEquiv_eq_coe, Multiset.toFinsupp_symm_apply]
    rfl)

-- Next, we define an equivalence between multisets of cardinality ≤ s
-- and the symmetric power of Option (Fin d) of order s. We use the
-- fact that the cardinality of the filterMap of a multiset over Option α
-- equals the count of elements 'a' in the multiset such that (f a).isSome.
-- Introducing Option allows us to "pad" multisets of cardinality ≤ s
-- to multisets of cardinality s by adding 'none' elements (representing
-- the slack variable in the combinatorial argument).
-- First, we prove a general lemma about filterMap and countP.
lemma card_filterMap_eq_countP {α β} (f : α → Option β) (s : Multiset α) :
  Multiset.card (s.filterMap f) = Multiset.countP (fun a => (f a).isSome) s := by
  induction s using Multiset.induction_on with
  | empty => simp only [filterMap_zero, card_zero, countP_zero]
  | cons a s ih =>
    rw [filterMap_cons, countP_cons]
    cases h : f a
    · simp only [Option.map_none, Option.getD_none, zero_add, ih, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, add_zero]
    · simp only [Option.map_some, Option.getD_some, singleton_add, card_cons, ih,
      Option.isSome_some, ↓reduceIte]

-- We also need a decomposition lemma for multisets over Option α,
-- separating them into multisets over α and the count of 'none' elements.
-- This facilitates the equivalence definition by isolating the 'some' elements
-- from the 'none' elements.

lemma multiset_decomposition_option {α : Type*} [DecidableEq α] (m : Multiset (Option α)) :
  m = (m.filterMap id).map Option.some + replicate (m.count Option.none) Option.none := by
  induction m using Multiset.induction_on with
  | empty => simp only [filterMap_zero, map_zero, notMem_zero, not_false_eq_true,
    count_eq_zero_of_notMem, replicate_zero, add_zero]
  | cons a s ih =>
    induction a with
    | none => simp only [← ih, filterMap_cons_none, id_eq, count_cons_self, replicate_succ,add_cons]
    | some val => simpa only [id_eq, Option.some.injEq, filterMap_cons_some, map_cons, ne_eq,
      reduceCtorEq, not_false_eq_true, count_cons_of_ne, cons_add, cons_inj_right]

-- We now define the equivalence between multisets of cardinality ≤ s
-- and the symmetric power of Option (Fin d) of order s. This final equivalence
-- allows us to count the monomials of degree ≤ s. Essentially, multisets of
-- cardinality ≤ s over Fin d are in bijection with multisets of cardinality s
-- over Option (Fin d) via padding with 'none' elements.
/-- Encodes a degree-`s` multiset over `Fin d` in a symmetric power of `Option (Fin d)`. -/
def multisetToSymOption {d s : ℕ} :
  {m : Multiset (Fin d) // card m ≤ s} ≃ Sym (Option (Fin d)) s :=
  { toFun := fun ⟨m, hm⟩ => ⟨m.map Option.some + replicate (s - m.card) Option.none, by
      simpa only [card_add, card_map, card_replicate] using Nat.add_sub_of_le hm⟩
    invFun := fun ⟨m', hm'⟩ => ⟨m'.filterMap id, by
      rw [← hm', card_filterMap_eq_countP]
      exact countP_le_card _ _⟩
    left_inv := fun ⟨m, hm⟩ => by
      simp only [filterMap_add, filterMap_map, CompTriple.comp_eq,  Subtype.mk.injEq]
      have h1 : filterMap some m = m := by
        induction m using Multiset.induction_on <;> simp
      erw [h1]
      simp only [add_eq_left, eq_zero_iff_forall_notMem, mem_filterMap, mem_replicate, ne_eq, id_eq,
        exists_eq_right, reduceCtorEq, and_false, not_false_eq_true, implies_true]
    right_inv := fun ⟨m', hm'⟩ => by
      apply Subtype.ext
      subst hm'
      dsimp
      conv_rhs => rw [multiset_decomposition_option m']
      congr 2
      have : m'.card = m'.countP (fun x => x.isSome) + m'.countP (fun x => x.isNone) := by
        rw [card_eq_countP_add_countP (fun x => x.isSome)]
        congr; ext x; simp [Option.isNone]
      simp only [this, countP_eq_card_filter, Option.isNone_iff_eq_none, card_filterMap_eq_countP,
        id_eq, add_tsub_cancel_left, count_eq_card_filter_eq]
      congr with x; rw [eq_comm] }

-- We can now instantiate the Fintype structure on the set of monomials of degree ≤ s.
noncomputable instance fintypeMonomialsBoundedDegree {d s : ℕ} :
    Fintype {f : Fin d →₀ ℕ | f.sum (fun _ n ↦ n) ≤ s} :=
  Fintype.ofEquiv (Sym (Option (Fin d)) s)
  (finsuppToMultisetRestricted.trans multisetToSymOption).symm

-- We compute the finrank of restrictTotalDegree (Fin d) F s,
-- which corresponds to the number of monomials of degree ≤ s in d variables,
-- using the derived equivalences and the lemma `Sym.card_sym_eq_choose`.
lemma restrictTotalDegree_finrank {d : ℕ} (s : ℕ) :
    Module.finrank F (restrictTotalDegree (Fin d) F s) = Nat.choose (d + s) s := by
    -- We know the dimension is the number of monomials of degree ≤ s.
    have h_rank_eq_card : Module.finrank F (restrictTotalDegree (Fin d) F s)
    = Fintype.card {f : Fin d →₀ ℕ | f.sum (fun _ n ↦ n) ≤ s} := by
      let b := basisMonomials (Fin d) F
      let S := {f : Fin d →₀ ℕ | f.sum (fun _ n ↦ n) ≤ s}
      -- We need tos show restrictTotalDegree is the span of monomials in S.
      rw [restrictTotalDegree, restrictSupport, Finsupp.supported_eq_span_single]
      -- We need to show b '' S is linearly independent.
      have h_li : LinearIndependent F (b ∘ (Subtype.val : S → (Fin d →₀ ℕ))) :=
        b.linearIndependent.comp Subtype.val Subtype.coe_injective
      erw [Set.image_eq_range, finrank_span_eq_card h_li]
    rw [h_rank_eq_card, Fintype.card_congr (finsuppToMultisetRestricted.trans multisetToSymOption),
      Sym.card_sym_eq_choose, Fintype.card_option, Fintype.card_fin, Nat.succ_add_sub_one]

-- Finally, we prove the bound dim A s ≤ (d + s) choose s
-- using the rank-nullity theorem and the previous lemma.
lemma dim_le_min_card_and_binom
    {d : ℕ}
    (A : Finset (EuclideanSpace F (Fin d)))
    (s : ℕ) :
    dim A s ≤ (Nat.choose (d + s) s) := by
  rw [dim]
  -- Apply Rank-Nullity Inequality.
  have := LinearMap.finrank_range_add_finrank_ker (evalMapRestricted A s)
  rw [restrictTotalDegree_finrank s] at this
  exact Nat.le.intro this

end Dimension

section CrootLevPach

variable {F : Type*} [Field F]

-- We will soon state the Croot-Lev-Pach lemma.
-- Before that, we need to establish some preliminary lemmas.
/-
The first preliminary lemma:
We define Ω_F_A_s as the range of the evaluation map from
restrictTotalDegree (Fin d) F s to functions A → F. We consider the
orthogonal complement of Ω_F_A_s with respect to the standard
inner product on (A → F), denoted by Ω_F_A_s_orth.
Since the inner product is non-degenerate (and the dimension is
finite), we have card A = dim (A → F) = dim Ω_F_A_s_orth +
dim Ω_F_A_s = dim Ω_F_A_s_orth + dim A s.
-/
lemma orthogonal_complement_dimension
    {d : ℕ}
    [DecidableEq (EuclideanSpace F (Fin d))]
    (A : Finset (EuclideanSpace F (Fin d)))
    (s : ℕ) :
    let Ω_F_A_s := LinearMap.range (evalMapRestricted A s)
    let B := Matrix.toBilin (Pi.basisFun F A) (1 : Matrix A A F)
    A.card = Module.finrank F ((Ω_F_A_s.dualAnnihilator).comap B) + dim A s := by
  -- We first introduce notations.
  intro Ω_F_A_s B
  -- We show that the bilinear form B is an isomorphism.
  have hB_inj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    ext a
    have : B v (Pi.basisFun F A a) = 0 := by rw [hv]; simp
    rw [Matrix.toBilin_apply] at this
    simp only [Matrix.one_apply, Pi.basisFun_apply] at this
    rw [Finset.sum_eq_single a] at this
    · simp at this; assumption
    · intros b _ hba; simp [hba]
    · intro ha; exact (ha (Finset.mem_univ a)).elim
  have hB_surj : Function.Surjective B := by
    have h_dim : Module.finrank F (A → F) = Module.finrank F (Module.Dual F (A → F)) := by
      simp_all only [Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Subspace.dual_finrank_eq, B]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_dim).mp hB_inj
  let B_iso := LinearEquiv.ofBijective B ⟨hB_inj, hB_surj⟩
  -- Now we can compute the dimension.
  simp only [dim]
  -- We have an isomorphism between Ω_F_A_s_orth and
  -- the dual annihilator of Ω_F_A_s.
  have h_iso : Module.finrank F ((Ω_F_A_s.dualAnnihilator).comap B) =
               Module.finrank F Ω_F_A_s.dualAnnihilator := by
    have : (Ω_F_A_s.dualAnnihilator).comap B =
           (Ω_F_A_s.dualAnnihilator).map (B_iso.symm : Module.Dual F (A → F) →ₗ[F] (A → F)) := by
      ext x
      simp only [Submodule.mem_comap, Submodule.mem_map]
      constructor
      · intro h
        use B x
        constructor
        · exact h
        · change (B_iso.symm) (B_iso x) = x
          rw [LinearEquiv.symm_apply_apply]
      · rintro ⟨y, hy, rfl⟩
        change B_iso (B_iso.symm y) ∈ _
        rw [LinearEquiv.apply_symm_apply]
        exact hy
    rw [this]
    exact LinearEquiv.finrank_map_eq B_iso.symm Ω_F_A_s.dualAnnihilator
  -- We use a very classical result on dual annihilators.
  have h_ann : Module.finrank F Ω_F_A_s + Module.finrank F Ω_F_A_s.dualAnnihilator =
               Module.finrank F (A → F) := Subspace.finrank_add_finrank_dualAnnihilator_eq _
  have h_card : Module.finrank F (A → F) = A.card := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  linarith

/-
The second preliminary lemma:
Retaining the previous notation, we define for a monomial m (with coefficient 1)
where m : Fin (2 * d) →₀ ℕ, two polynomials m_left : Fin d →₀ ℕ and m_right : Fin d →₀ ℕ.
These are defined by m_left i = m i and m_right i = m (d + i) for i ∈ Fin d.
Then, for all a, b ∈ F^d, we have:
eval ((Fin.append a b) ∘ Fin.cast (by rw [two_mul])) (monomial m 1)
= eval a (monomial (m_left m) 1) * eval b (monomial (m_right m) 1).
This follows from the definition of evaluation on monomials.
-/
lemma eval_split {d : ℕ}
    (m : Fin (2 * d) →₀ ℕ)
    (a b : EuclideanSpace F (Fin d)) :
    let h_cast : 2 * d = d + d := by rw [two_mul]
    let m_left (m : Fin (2 * d) →₀ ℕ) : Fin d →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => m (Fin.cast h_cast.symm (Fin.castAdd d i)))
    let m_right (m : Fin (2 * d) →₀ ℕ) : Fin d →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => m (Fin.cast h_cast.symm (Fin.natAdd d i)))
    eval ((Fin.append a b) ∘ Fin.cast (by rw [two_mul])) (monomial m 1)
    = eval a (monomial (m_left m) 1) * eval b (monomial (m_right m) 1) := by
  -- We first introduce notations.
  intro h_cast m_left m_right
  simp only [eval_monomial, one_mul]
  rw [Finsupp.prod_fintype, Fintype.prod_equiv (finCongr h_cast) _
  (fun x => ((Fin.append a.1 b.1) x) ^ m ((finCongr h_cast).symm x))]
  · rw [Fin.prod_univ_add]
    congr 1
    · rw [Finsupp.prod_fintype]
      · apply Finset.prod_congr rfl
        intro i _
        · simp [m_left, Finsupp.equivFunOnFinite, Fin.append_left]
      · simp only [pow_zero, implies_true]
    · rw [Finsupp.prod_fintype]
      · apply Finset.prod_congr rfl
        intro i _
        simp only [Fin.natAdd_eq_addNat, finCongr_symm, finCongr_apply, Finsupp.equivFunOnFinite,
         Equiv.coe_fn_symm_mk, Finsupp.coe_mk, m_right]
        rw [← Fin.natAdd_eq_addNat, Fin.append_right]
      · simp only [pow_zero, implies_true]
  · simp [Function.comp_apply, implies_true]
  · intro x
    simp only [Function.comp_apply, pow_zero]
/-
The third preliminary lemma:
We define the matrix M_P_A : A × A → F by
M_P_A(a,b) = eval ((Fin.append a b) ∘ Fin.cast (by rw [two_mul])) P,
where P is a polynomial of degree ≤ 2s + 1. We also consider the bilinear form
Φ_P_A defined by the matrix M_P_A.
Then, if f, g ∈ Ω_F_A_s_orth, we have Φ_P_A(f,g) = 0.
The intuition is as follows: f and g correspond to polynomials P_f, P_g of degree ≤ s,
while P has degree ≤ 2s + 1. In the expansion of Φ_P_A(f,g), we encounter terms like
eval a P_f * eval (a,b) P * eval b P_g. Expanding P into monomials, each monomial
has degree ≤ 2s + 1, so at least one of its parts (involving a or b) has degree ≤ s.
Consequently, either the term involving f or the term involving g vanishes because
f, g ∈ Ω_F_A_s_orth. This lemma relies on `eval_split`.
-/
lemma bilinear_form_vanishes_on_orthogonal_complement
    {d : ℕ}
    [DecidableEq (EuclideanSpace F (Fin d))]
    (A : Finset (EuclideanSpace F (Fin d)))
    (s : ℕ)
    (p : MvPolynomial (Fin (2 * d)) F)
    (hp_deg : p.totalDegree ≤ 2 * s + 1) :
    let B := Matrix.toBilin (Pi.basisFun F A) (1 : Matrix A A F)
    let Ω_F_A_s_orth := (LinearMap.range (evalMapRestricted A s)).dualAnnihilator.comap B
    let M : Matrix A A F :=
      fun a b => eval ((Fin.append a.1 b.1) ∘ Fin.cast (by rw [two_mul])) p
    let Φ_P_A : (A → F) →ₗ[F] (A → F) →ₗ[F] F := Matrix.toBilin (Pi.basisFun F A) M
    ∀ f ∈ Ω_F_A_s_orth, ∀ g ∈ Ω_F_A_s_orth, Φ_P_A f g = 0 := by
  -- We first introduce notations.
  intros B Ω_F_A_s_orth M Φ_P_A f hf g hg
  -- Now, we expand Φ_P_A f g and rewrite the sum over all monomials in p.
  have : Φ_P_A f g = ∑ a : A, ∑ b : A, f a * M a b * g b := by simp [Φ_P_A, Matrix.toBilin_apply]
  simp only [this, M]
  have hexp : ∀ a b : A,
      f a * (eval ((Fin.append a.1 b.1) ∘ Fin.cast (by rw [two_mul])) p) * g b
      = ∑ m ∈ p.support, f a *
          (eval ((Fin.append a.1 b.1) ∘ Fin.cast (by rw [two_mul]))
            (Finsupp.single m (coeff m p))) * g b := by
    intro a b
    conv_lhs => rw [p.as_sum, map_sum]
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [MvPolynomial.single_eq_monomial]
  simp only [Finset.univ_eq_attach, hexp]
  have h_swap : ∑ b : A, ∑ a : A, ∑ m ∈ p.support, f a * (eval ((Fin.append a.1 b.1)
      ∘ Fin.cast (by rw [two_mul])) (Finsupp.single m (coeff m p))) * g b =
      ∑ b : A, ∑ m ∈ p.support, ∑ a : A,
      f a * (eval ((Fin.append a.1 b.1)
      ∘ Fin.cast (by rw [two_mul])) (Finsupp.single m (coeff m p))) * g b := by
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  change ∑ b : A, ∑ a : A, ∑ m ∈ p.support, f a * (eval ((Fin.append a.1 b.1)
  ∘ Fin.cast (by rw [two_mul])) (Finsupp.single m (coeff m p))) * g b = 0
  rw [h_swap, Finset.sum_comm]
  -- It then suffices to show that each term in the rewritten sum is 0.
  apply Finset.sum_eq_zero
  intro m hm
  -- For this, we write one summand (a double sum) as a product of
  -- two sums involving only a or b respectively.
  rw [Finset.sum_comm]
  let h_cast : 2 * d = d + d := two_mul _
  let m_left : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (Fin.cast h_cast.symm (Fin.castAdd d i)))
  let m_right : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (Fin.cast h_cast.symm (Fin.natAdd d i)))
  have monomial_eq_single : ∀ (n : Fin (2 * d) →₀ ℕ) (a : F),
  monomial n a = Finsupp.single n a := fun _ _ => rfl
  have monomial_eq_smul_monomial (n : Fin (2 * d) →₀ ℕ) (a : F) :
    monomial n a = a • monomial n 1 := by simp [smul_monomial]
  rw [← monomial_eq_single, monomial_eq_smul_monomial]
  have h_eq : (∑ a : A, ∑ b : A, f a * (coeff m p *
  ((eval a.1 (monomial m_left 1)) * eval b.1 (monomial m_right 1))) * g b)
  = coeff m p * (∑ a : A, f a * eval a.1 (monomial m_left 1)) *
  (∑ b : A, g b * eval b.1 (monomial m_right 1)) := by
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.univ_eq_attach, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  simp only [Finset.univ_eq_attach] at h_eq
  simp only [Finset.univ_eq_attach, smul_eval]
  convert h_eq
  · exact eval_split _ _ _
  -- It then suffices to prove that one of the two sums in this
  -- product is 0. For this we use the fact that f,g ∈ Ω_F_A_s_orth
  -- and the degree condition on p. Indeed, since p has degree ≤ 2s + 1,
  -- at least one of m_left or m_right has degree ≤ s.
  · have h_deg : m_left.support.sum (fun i => m_left i) +
    m_right.support.sum (fun i => m_right i) ≤ 2 * s + 1 := by
      rw [totalDegree, Finset.sup_le_iff] at hp_deg
      have h_split : m_left.support.sum (fun i => m_left i) +
          m_right.support.sum (fun i => m_right i) = m.sum (fun _ x => x) := by
        change m_left.sum (fun _ x => x) + m_right.sum (fun _ x => x) = m.sum (fun _ x => x)
        simp only [implies_true, Finsupp.sum_fintype _]
        rw [← Equiv.sum_comp (finCongr h_cast).symm, Fin.sum_univ_add]
        rfl
      rw [h_split]
      exact hp_deg m hm
    -- We do a case distinction on which of m_left or m_right
    -- has degree ≤ s.
    rcases le_or_gt (m_left.support.sum (fun i => m_left i)) s with h_left_le | h_left_gt
    · -- Case 1: m_left degree ≤ s, we must have ⟨f, eval monomial m_left⟩
      -- = ∑ x ∈ A.attach, f x * (eval (↑x).ofLp) ((monomial m_left) 1)) = 0
      -- because f ∈ Ω_F_A_s_orth.
      have h_S_left : (∑ a, f a * eval a.1 (monomial m_left 1)) = 0 := by
        let P := monomial m_left (1:F)
        have : P.totalDegree ≤ s := by rwa [totalDegree_monomial _ one_ne_zero  ]
        have hP_in : P ∈ restrictTotalDegree (Fin d) F s := by rwa [mem_restrictTotalDegree]
        let P_res : restrictTotalDegree (Fin d) F s := ⟨P, hP_in⟩
        have h_orth : B f (evalMapRestricted A s P_res) = 0 := by
          rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator] at hf
          exact hf (evalMapRestricted A s P_res) (LinearMap.mem_range_self _ _)
        unfold B at h_orth
        simp only [Matrix.toBilin_apply, Matrix.one_apply, evalMapRestricted,
        Finset.sum_ite_eq, Finset.mem_univ, if_true,
        mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Pi.basisFun_repr] at h_orth
        convert h_orth
        rfl
      simp only [Finset.univ_eq_attach] at h_S_left
      rw [h_S_left]
      simp only [mul_zero, zero_mul]
    · -- Case 2: m_left degree > s => m_right degree ≤ s and hence, we must
      -- have ⟨g, eval monomial m_right⟩ = ∑ y ∈ A.attach, g y *
      -- (eval (↑y).ofLp) ((monomial m_right) 1)) = 0 because g ∈ Ω_F_A_s_orth.
      have h_right_le : m_right.support.sum (fun i => m_right i) ≤ s := by
        linarith
      have h_S_right : (∑ b, g b * eval b.1 (monomial m_right 1)) = 0 := by
        let P := monomial m_right (1 :F)
        have hP_deg : P.totalDegree ≤ s := by rwa [totalDegree_monomial _ one_ne_zero ]
        have hP_in : P ∈ restrictTotalDegree (Fin d) F s := by
          rwa [mem_restrictTotalDegree]
        have h_orth : B g (evalMapRestricted A s ⟨P, hP_in⟩) = 0 := by
          rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator] at hg
          exact hg (evalMapRestricted A s ⟨P, hP_in⟩) (LinearMap.mem_range_self _ _)
        unfold B at h_orth
        simp only [Matrix.toBilin_apply, Finset.univ_eq_attach,  Matrix.one_apply, mul_ite, mul_one,
          mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_attach] at h_orth
        exact h_orth
      simp only [Finset.univ_eq_attach] at h_S_right
      rw [h_S_right]
      simp only [mul_zero]

/-
The fourth preliminary lemma:
We prove the subadditivity of the matrix rank:
rank(A + B) ≤ rank(A) + rank(B).
This is a standard linear algebra result.
-/
lemma matrix_rank_add_le {n : Type*} [Fintype n]
  (A B : Matrix n n F) :
  (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank]
  simp only [Matrix.mulVecLin]
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rw [map_add]
  exact LinearMap.range_add_le _ _

-- We now state the Croot-Lev-Pach lemma as presented in the paper by
-- Petrov and Pohoata (slightly generalised). We split it into two parts for clarity.
-- First part: Rank bound on the matrix defined by a polynomial of bounded degree.
/-
The proof strategy is as follows:
Let Ω_F_A_s and Ω_F_A_s_orth be as defined previously. Let
F' be a basis of Ω_F_A_s_orth, and extend it to a basis
F of (A → F). Consider the matrix of M in the basis F.
By the previous lemma (`bilinear_form_vanishes_on_orthogonal_complement`),
the submatrix indexed by F' × F' is zero. Thus, the
matrix has a zero block of size dim Ω_F_A_s_orth ×
dim Ω_F_A_s_orth. Consequently, its rank is bounded by the
size of the complementary block, which is dim Ω_F_A_s +
dim Ω_F_A_s = 2 * dim A s. Therefore, the rank of M
is bounded by 2 * dim A s.
This argument relies on the first, third, and fourth preliminary lemmas.
-/
lemma Croot_Lev_Pach_lemma_generalised_1st_part
    {d : ℕ}
    (A : Finset (EuclideanSpace F (Fin d)))
    (s : ℕ)
    (p : MvPolynomial (Fin (2 * d)) F)
    (hp_deg : p.totalDegree ≤ 2 * s + 1) :
    let M : Matrix A A F :=
      fun a b => eval ((Fin.append a.1 b.1) ∘ Fin.cast (by rw [two_mul])) p
    -- 1) Rank bound.
    M.rank ≤ 2 * dim A s := by
    intro M
    -- Note: The formal proof below differs slightly from the sketch
    -- above (which used orthogonal complements). Instead, we decompose
    -- the matrix M into a sum of two matrices M1 and M2.
    -- M1 corresponds to terms with "left degree" ≤ s, and M2 corresponds
    -- to terms with "left degree" > s (implying "right degree" ≤ s).
    -- We then bound the rank of M1 and M2 separately by dim A s.
    -- For M1, the columns are low-degree polynomials, so we
    -- bound the column rank. For M2, the rows are low-degree
    -- polynomials, so we bound the row rank (via transpose).
    -- This approach avoids the orthogonal complement argument
    -- for the rank bound and utilises the second and fourth preliminary lemmas.
    let h_cast : 2 * d = d + d := by rw [two_mul]
    -- We use the preliminary lemma `eval_split`
    -- (implicitly via the definition of M1, M2 and h_M_eq)
    -- to decompose the evaluation of p(x, y) into a sum
    -- of products of evaluations of monomials. Specifically,
    -- we split each monomial m in p into m_left and m_right.
    let m_left (m : Fin (2 * d) →₀ ℕ) : Fin d →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => m (Fin.cast h_cast.symm (Fin.castAdd d i)))
    let m_right (m : Fin (2 * d) →₀ ℕ) : Fin d →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => m (Fin.cast h_cast.symm (Fin.natAdd d i)))
    -- We split the support of p into two sets S1 and S2 based on the degree of m_left.
    -- S1 contains monomials where deg(m_left) ≤ s.
    -- S2 contains monomials where deg(m_left) > s.
    let S1 := p.support.filter (fun m => (m_left m).support.sum (fun i => m_left m i) ≤ s)
    let S2 := p.support.filter (fun m => s < (m_left m).support.sum (fun i => m_left m i))
    -- We define M1 and M2 corresponding to S1 and S2.
    let M1 : Matrix A A F := fun a b => ∑ m ∈ S1,
      (coeff m p) * eval a.1 (monomial (m_left m) 1) * eval b.1 (monomial (m_right m) 1)
    let M2 : Matrix A A F := fun a b => ∑ m ∈ S2,
      (coeff m p) * eval a.1 (monomial (m_left m) 1) * eval b.1 (monomial (m_right m) 1)
    have h_M_eq : M = M1 + M2 := by
      ext a b
      simp only [M, M1, M2, Matrix.add_apply]
      rw [← Finset.sum_union]
      · conv_lhs => rw [p.as_sum, map_sum]
        apply Finset.sum_congr
        · ext m
          simp only [Finset.mem_union, Finset.mem_filter, S1, S2]
          constructor
          · intro hm
            by_cases h : (m_left m).support.sum (fun i => m_left m i) ≤ s
            · left; exact ⟨hm, h⟩
            · right; exact ⟨hm, not_le.mp h⟩
          · intro h
            rcases h with h | h <;> exact h.1
        · intro m hm
          conv => lhs; arg 2; change monomial m (coeff m p);
          rw [← mul_one (coeff m p)]; simp only [← smul_eq_mul]; rw [← smul_monomial]
          simp only [smul_eval]
          -- Here we use the preliminary lemma `eval_split` to show that
          -- eval (x, y) m = eval x m_left * eval y m_right.
          have h_eval_split' : (eval (Fin.append a.1 b.1
          ∘ Fin.cast (by rw [two_mul]))) (monomial m 1) =
            eval a.1 (monomial (m_left m) 1) * eval b.1 (monomial (m_right m) 1) := by
            convert eval_split m a.1 b.1 -- We use the second preliminary lemma here.
          erw [h_eval_split']
          ring
      · rw [Finset.disjoint_filter]
        intro m _ h1 h2
        linarith
    -- We now bound the rank of M1.
    -- Since M1 is a sum of terms where the "left" part has degree ≤ s,
    -- for each fixed column index 'b', the function a ↦ M1(a,b) is the evaluation
    -- of a single polynomial in 'a' of degree ≤ s (specifically, a linear combination
    -- of the m_left monomials).
    -- Hence the column space of M1 is contained in the range
    -- of `evalMapRestricted A s`. Thus rank(M1) ≤ dim A s.
    have h_rank1 : M1.rank ≤ dim A s := by
      rw [dim]
      have h_cols (b) : (fun a => M1 a b) ∈ LinearMap.range (evalMapRestricted A s) := by
        let P := ∑ m ∈ S1, (coeff m p *
        eval b.1 (monomial (m_right m) (1 : F))) • monomial (m_left m) (1 : F)
        have hP : P ∈ restrictTotalDegree (Fin d) F s := by
          apply Submodule.sum_mem
          intro m hm
          rw [Finset.mem_filter] at hm
          apply Submodule.smul_mem
          rw [mem_restrictTotalDegree, totalDegree_monomial (m_left m) one_ne_zero]
          · exact hm.2
        have h_eval : (fun a => ∑ m ∈ S1, coeff m p *
        eval a.1 (monomial (m_left m) (1 : F)) *
        eval b.1 (monomial (m_right m) (1 : F))) = evalMapRestricted A s ⟨P, hP⟩ := by
          ext a
          simp only [evalMapRestricted, LinearMap.coe_mk, AddHom.coe_mk, map_sum, smul_eval, P]
          apply Finset.sum_congr rfl
          intro m _
          ring
        rw [h_eval]
        exact LinearMap.mem_range_self _ _
      rw [Matrix.rank]
      apply Submodule.finrank_mono
      rw [Matrix.range_mulVecLin, Submodule.span_le]
      intro v hv
      obtain ⟨b, hb⟩ := Set.mem_range.mp hv
      rw [← hb]
      exact h_cols b
    -- We now bound the rank of M2.
    -- For M2, the "left" part (corresponding to rows/index 'a') has degree > s.
    -- However, since the total degree is ≤ 2s + 1, this forces the "right" part
    -- (corresponding to columns/index 'b') to have degree ≤ s.
    -- This means for each fixed row index 'a', the function b ↦ M2(a,b) is the evaluation
    -- of a single polynomial in 'b' of degree ≤ s.
    -- Since rank is column rank, we look at M2^T. The columns of M2^T (which are
    -- the rows of M2) are in the range of `evalMapRestricted A s`.
    -- Thus rank(M2) = rank(M2^T) ≤ dim A s.
    have h_rank2 : M2.rank ≤ dim A s := by
      rw [← Matrix.rank_transpose, dim]
      let W := LinearMap.range (evalMapRestricted A s)
      have h_rows (a) : (fun b => M2 a b) ∈ LinearMap.range (evalMapRestricted A s) := by
        let P := ∑ m ∈ S2, (coeff m p *
        eval a.1 (monomial (m_left m) (1 : F))) • monomial (m_right m) (1 : F)
        have hP : P ∈ restrictTotalDegree (Fin d) F s := by
          apply Submodule.sum_mem
          intro m hm
          rw [Finset.mem_filter] at hm
          apply Submodule.smul_mem
          rw [mem_restrictTotalDegree, totalDegree_monomial (m_right m) one_ne_zero]
          · -- Prove degree of m_right is <= s
            have h_deg_m : (m_left m).support.sum (fun i ↦ m_left m i)
            + (m_right m).support.sum (fun i ↦ m_right m i) ≤ 2 * s + 1 := by
              have h_m_deg : m.support.sum m ≤ 2 * s + 1 :=
              le_trans (le_totalDegree hm.1) hp_deg
              convert h_m_deg
              change (m_left m).sum (fun _ x ↦ x)
              + (m_right m).sum (fun _ x ↦ x) = m.sum (fun _ x ↦ x)
              simp only [implies_true, Finsupp.sum_fintype _]
              rw [← Equiv.sum_comp (finCongr h_cast).symm, Fin.sum_univ_add]
              rfl
            have h_left_gt : s < (m_left m).support.sum (fun i ↦ m_left m i) := hm.2
            generalize h_dL : (m_left m).support.sum (fun i ↦ m_left m i) = dL at *
            generalize h_dR : (m_right m).sum (fun _ e ↦ ↑e) = dR at *
            rw [Finsupp.sum] at h_dR
            rw [h_dR] at h_deg_m
            zify at *
            linarith
        have h_eval : (fun b => ∑ m ∈ S2, coeff m p *
        eval a.1 (monomial (m_left m) (1 : F)) * eval b.1 (monomial (m_right m) (1 : F)))
        = evalMapRestricted A s ⟨P, hP⟩ := by
          ext b
          simp [evalMapRestricted, P, map_sum, smul_eval]
        rw [h_eval]
        apply LinearMap.mem_range_self
      rw [Matrix.rank]
      apply Submodule.finrank_mono
      rw [Matrix.range_mulVecLin, Submodule.span_le]
      intro v hv
      obtain ⟨a, rfl⟩ := Set.mem_range.mp hv
      simpa only [Matrix.col_apply', Matrix.transpose_apply, SetLike.mem_coe] using h_rows a
    rw [h_M_eq, two_mul]
    -- Finally, we use the subadditivity of rank
    -- (fourth preliminary lemma: `matrix_rank_add_le`).
    have bound : (M1 + M2).rank ≤ M1.rank + M2.rank :=  matrix_rank_add_le _ _
    linarith

-- Second part: Bound on the positive and negative inertia indices of the matrix.
-- Note: To discuss positive definiteness and inertia indices, we require an order on F
-- compatible with its field structure.
/-
The proof proceeds as follows:
Let Ω_F_A_s and Ω_F_A_s_orth be as defined. Let Q be the quadratic form
defined by M. Although M is not necessarily symmetric, since F is an
ordered field (characteristic 0), Q arises from a symmetric bilinear form,
making it a valid quadratic form. We consider any subspace V± on which Q
is positive (respectively, negative) definite. We show that V± ∩ Ω_F_A_s_orth = ⊥.
If v ∈ V± ∩ Ω_F_A_s_orth, then by the lemma `bilinear_form_vanishes_on_orthogonal_complement`,
we have Q(v) = Φ_P_A(v,v) = 0, which contradicts the definiteness of Q on V±
unless v = 0. Thus, V± ∩ Ω_F_A_s_orth = ⊥.
By the dimension formula, dim V± + dim Ω_F_A_s_orth = dim (V± + Ω_F_A_s_orth) ≤ dim (A → F).
Therefore, dim V± ≤ dim (A → F) - dim Ω_F_A_s_orth = dim A s
(using the lemma `orthogonal_complement_dimension`).
-/
lemma Croot_Lev_Pach_lemma_generalised_2nd_part
    {d : ℕ} [LinearOrder F] [IsStrictOrderedRing F]
    (A : Finset (EuclideanSpace F (Fin d))) {s : ℕ}
    (p : MvPolynomial (Fin (2 * d)) F)
    (hp_deg : p.totalDegree ≤ 2 * s + 1) :
    let M : Matrix A A F :=
      fun a b => eval ((Fin.append a.1 b.1) ∘ Fin.cast (by rw [two_mul])) p
    let Q : (A → F) → F :=
      fun v => ∑ a : A, ∑ b : A, v a * M a b * v b
    (∀ (V : Submodule F (A → F)), (∀ v ∈ V, v ≠ 0 → Q v > 0) →
      Module.finrank F V ≤ dim A s) ∧
    -- The dimension of any subspace on which Q is negative definite is bounded by dim.
    (∀ (V : Submodule F (A → F)), (∀ v ∈ V, v ≠ 0 → Q v < 0) →
      Module.finrank F V ≤ dim A s) := by
    -- We first introduce notations.
    intro M Q
    let B := Matrix.toBilin (Pi.basisFun F A) (1 : Matrix A A F)
    let Ω_F_A_s_orth := ((LinearMap.range (evalMapRestricted A s)).dualAnnihilator).comap B
    let Φ_P_A : (A → F) →ₗ[F] (A → F) →ₗ[F] F := Matrix.toBilin (Pi.basisFun F A) M
    have h_dim_orth : Module.finrank F Ω_F_A_s_orth = A.card - dim A s := by
      -- preliminary lemma `orthogonal_complement_dimension`
      rw [orthogonal_complement_dimension A s, add_tsub_cancel_right]
    constructor
    · -- Positive definite case
      intro V hV
      -- We show that V ∩ Ω_F_A_s_orth = ⊥
      have h_inter : V ⊓ Ω_F_A_s_orth = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro v hv
        by_contra h_nonzero
        have h_pos : Q v > 0 := hV v hv.1 h_nonzero
        have h_zero : Q v = 0 := by
           -- Apply bilinear_form_vanishes_on_orthogonal_complement
           -- We need to unfold Q and relate it to Φ_P_A
           have : Q v = Φ_P_A v v := by
              unfold Q Φ_P_A
              simp only [Finset.univ_eq_attach, Matrix.toBilin_apply, Pi.basisFun_repr]
           rw [this]
           exact bilinear_form_vanishes_on_orthogonal_complement A s p hp_deg v hv.2 v hv.2
        linarith
      -- Now we use the dimension formula
      have h_dim_sum : Module.finrank F V + Module.finrank F Ω_F_A_s_orth =
                       Module.finrank F ↥(V ⊔ Ω_F_A_s_orth) := by
         rw [← Submodule.finrank_sup_add_finrank_inf_eq, h_inter, finrank_bot, add_zero]
      -- and bound the total dimension
      have h_le_total := (V ⊔ Ω_F_A_s_orth).finrank_le
      have h_card : Module.finrank F (A → F) = A.card := by
        simp [Module.finrank_fintype_fun_eq_card]
      omega
    · -- Negative definite case
      intro V hV
      -- We show that V ∩ Ω_F_A_s_orth = ⊥
      have h_inter : V ⊓ Ω_F_A_s_orth = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro v hv
        by_contra h_nonzero
        have h_pos : Q v < 0 := hV v hv.1 h_nonzero
        have h_zero : Q v = 0 := by
           -- Apply bilinear_form_vanishes_on_orthogonal_complement
           -- We need to unfold Q and relate it to Φ_P_A
           have : Q v = Φ_P_A v v := by
              unfold Q Φ_P_A
              simp only [Finset.univ_eq_attach, Matrix.toBilin_apply, Pi.basisFun_repr]
           rw [this]
           exact bilinear_form_vanishes_on_orthogonal_complement A s p hp_deg v hv.2 v hv.2
        linarith
      -- Now we use the dimension formula
      have h_dim_sum : Module.finrank F V + Module.finrank F Ω_F_A_s_orth =
                       Module.finrank F ↥(V ⊔ Ω_F_A_s_orth) := by
         rw [← Submodule.finrank_sup_add_finrank_inf_eq, h_inter, finrank_bot, add_zero]
      -- and bound the total dimension
      have h_le_total : Module.finrank F ↥(V ⊔ Ω_F_A_s_orth) ≤ Module.finrank F (A → F) :=
        (V ⊔ Ω_F_A_s_orth).finrank_le
      have h_card : Module.finrank F (A → F) = A.card := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      omega

end CrootLevPach

section MainResult

-- We now prove the Bannai-Bannai-Stanton bound on the size of distance sets.
-- Proof sketch:
/-
We construct the polynomial P(X_0, ..., X_{2d-1}) as the product over r
in the distance set of S of (r^2 - distPoly), where distPoly is the squared
distance polynomial. By hypothesis, the distance set has cardinality s,
so the degree of P is at most 2s ≤ 2s + 1. Since S is finite (by a previous lemma),
we define the matrix M_{P(X),S}: S × S → ℝ by M_{P(X),S}(x,y) = P(x, y).
A brief computation shows that if x ≠ y, then M_{P(X),S}(x,y) = 0
(by construction of the distance set), and if x = y, then
M_{P(X),S}(x,y) = ∏_{r ∈ D} r^2 > 0 (since each distance r > 0).
Thus, M_{P(X),S}(x,x) > 0 for all x ∈ S. Consequently, the quadratic form Q
is positive definite, meaning its positive inertia index equals card(S).
Applying the Croot-Lev-Pach lemma, we conclude that card(S) ≤ dim A s,
which is bounded by Nat.choose (d + s) s.
-/
theorem bannai_bannai_stanton_bound {d s : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
  (hdis : (distanceSet S).Finite) (hs : s = (hdis.toFinset).card) :
  S.encard ≤ Nat.choose (d + s) s := by
  -- We show that S is finite.
  have hS_fin : S.Finite := finite_distance_set_imp_finite_set S hdis
  -- Define the distance set D as a finset.
  let D : Finset ℝ := hdis.toFinset
  -- Define the polynomial P and bound its degree
  -- (this uses previous lemmas: degree_productDistPoly_le).
  let P : MvPolynomial (Fin (2 * d)) ℝ := productDistPoly d D
  have hP_deg : P.totalDegree ≤ 2 * D.card + 1 := by
    have : totalDegree (productDistPoly d D) ≤ 2 * D.card := degree_productDistPoly_le D
    linarith
  -- Define the set A = S as a finset.
  let A : Finset (EuclideanSpace ℝ (Fin d)) := hS_fin.toFinset
  -- Definition of the matrix M and the quadratic form Q.
  let M : Matrix A A ℝ := fun a b => eval ((Fin.append a.1 b.1) ∘ Fin.cast (by rw [two_mul])) P
  let Q : (A → ℝ) → ℝ := fun v => ∑ a : A, ∑ b : A, v a * M a b * v b
  -- We show that M = (product over r in D of r^2) Id_A
  -- (this uses previous lemmas: eval_distPoly_eq_eval_distPolyFrom
  -- and eval_productDistPolyFrom_ne).
  have h_eval (a c : EuclideanSpace ℝ (Fin d)) : eval (Fin.append a c ∘ Fin.cast (by rw [two_mul]))
    (distPoly d) = eval a (distPolyFrom c) := eval_distPoly_eq_eval_distPolyFrom _ _
  have M_eval (a b : A) : M a b = if a = b then ∏ r ∈ D, r ^ 2  else 0 := by
    simp only [M, P, productDistPoly, map_prod, map_sub, eval_C]
    by_cases hab : a = b
    · rw [if_pos hab]
      simp_all only [P, D, A, distPolyFrom, map_sum, map_pow,
      map_sub, eval_X, eval_C, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero, sub_zero]
    · rw [if_neg hab, h_eval]
      -- We want to use our productDistPolyFrom b at a.
      have h_eval_prod : ∏ x ∈ D, (x ^ 2 - (eval a.1) (distPolyFrom b.1))
      = eval a.1 (productDistPolyFrom b.1 D) := by
          simp only [productDistPolyFrom, map_prod, map_sub, map_pow, eval_C]
      rw [h_eval_prod]
      apply eval_productDistPolyFrom_ne a.1 b.1 D
      -- We use the fact that dist(a,b) ∈ D when a ≠ b.
      have h_dist_in_D : dist a.1 b.1 ∈ D := by
        obtain ⟨a_val, a_property⟩ := a
        obtain ⟨b_val, b_property⟩ := b
        simp only [distanceSet, ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq, D]
        simp only [Set.Finite.mem_toFinset, Subtype.mk.injEq, A] at a_property b_property hab
        use a_val, a_property, b_val, b_property
      exact h_dist_in_D
  -- In this case, Q is positive definite (if A is non-empty).
  have h_Q_definite : A.Nonempty → ∀ v : A → ℝ, v ≠ 0 → Q v > 0 := by
    intro hA_nonempty v hv
    simp only [Q, M_eval, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, P, M, D]
    have h_prod_pos: 0 < ∏ r ∈ D, r ^ 2 := by
      apply Finset.prod_pos
      intro r hr
      rw [sq_pos_iff]
      contrapose! hr
      simp [hr, D, Set.Finite.mem_toFinset, distanceSet]
    apply Finset.sum_pos'
    · ring_nf
      intro a h
      rw [if_pos (Finset.mem_univ a)]
      nlinarith
    · obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
      use a, Finset.mem_univ a
      rw [if_pos (Finset.mem_univ a)]
      have h1 : 0 < v a ^ 2 := sq_pos_of_ne_zero ha
      nlinarith
  -- We can now conclude the proof, by doing a disjunction of
  -- cases (A≠∅) and by applying the Croot-Lev-Pach lemma.
  by_cases hA_empty : A.Nonempty
  · -- We apply the Croot-Lev-Pach lemma (when A non-empty).
    obtain ⟨h_pos, _⟩ := Croot_Lev_Pach_lemma_generalised_2nd_part  hS_fin.toFinset P hP_deg
    specialize h_pos ⊤ (fun v a a_1 ↦ h_Q_definite hA_empty v a_1)
    rw [finrank_top, Module.finrank_pi _, Fintype.card_coe] at h_pos
    subst hs
    -- We now use our lemma to bound dim A s.
    rw [Set.Finite.encard_eq_coe_toFinset_card hS_fin]
    exact_mod_cast le_trans h_pos <| dim_le_min_card_and_binom A D.card
  · -- When A is empty the result is trivial.
    have : S = ∅ := by
      simp [A, Set.not_nonempty_iff_eq_empty] at hA_empty
      assumption
    simp only [this, Set.encard_empty, zero_le]

end MainResult

end BannaiBannaiStanton
