/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringTensor
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Statements.PrincipalSubringPrimality
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.DegreeValuation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Monomial
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportUnit

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.ReducibleSpan

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.PrincipalIrreducible
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.SupportSupremumMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentDegree
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedDivisibility
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeSum
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Block forms in the degree-graded ring

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Proposition 3.2, proves irreducibility of `b = ∑ b_i t^{γ_i} + r` from that of `rv(b_m)` by
working in the degree-graded ring `RV̂` of LM24: the initial form of `b` is
`t^{γ_m} · B` with `B = ∑ rv(b_i) t^{γ_i - γ_m}`, and a factorisation of `b` gives one of `B`
after the monomial `t^{γ_m}` has been split between the factors. This module carries out the
graded part of the argument.

`RV̂ ≅ P̂ ⊗_K K(ℝ^{≤0})` (LM24, Proposition 6.1.2). A *block form* is an element
`∑ᵢ X_i · t^{δ_i}` with `X_i ∈ P_n` linearly independent, `δ_i ≤ 0`, one `δ_m = 0` and all other
`δ_i < 0`; its image under the graded projection `RV̂ → P̂` is `X_m`. If `X_m` is irreducible in
`P̂`, the block form is irreducible in `RV̂`: a factorisation `B = A C` has homogeneous factors,
the projection of one factor is a unit of `P̂`, so that factor has grade zero and is a
finite-support series `p`; the coordinate functional extracting the coefficient of `X_m` is
`K(ℝ^{≤0})`-linear and sends `B` to `t^{δ_m} = 1`, whence `p` is a unit. The source words this
step as "`p(B) = 1` implies `p(A) = 1`" and "`deg_J(a_i) = 0` for every `i`".

Finite-support series are primal in `RV̂` (LM24, Corollary 6.3.6), and the divisors of a monomial
in `K(ℝ^{≤0})` are monomials. Hence in any factorisation `A C = t^γ · B` one factor is a monomial
`k t^x`; and a series whose initial form is the image of a finite-support series is that series.
-/

open scoped DirectSum HahnSeries NatOrdinal TensorProduct

universe v

public noncomputable section

namespace FLLM24

open Berarducci HahnSeries.Nonpositive

variable {K : Type v} [Field K]

/-! ### Monomials and units -/

/-- A factor of a nonzero monomial of `K((ℝ^{≤0}))` is a monomial: the order and the support
supremum of a product are both additive (Berarducci, Corollary 9.8 for the supremum), and they
agree on a monomial, so they agree on each factor. -/
theorem isMonomial_of_mul_eq_single [CharZero K] {p q : Series K} {γ : ℝ} {k : K} (hk : k ≠ 0)
    (hγ : γ ≤ 0) (h : p * q = single γ k hγ) : IsMonomial p := by
  have hsingle : single γ k hγ ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun x : Series K ↦ (x : K⟦ℝ⟧).coeff γ) hzero
    exact hk (by simpa [coe_single] using hcoeff)
  have hp : p ≠ 0 := fun hp ↦ hsingle (by rw [← h, hp, zero_mul])
  have hq : q ≠ 0 := fun hq ↦ hsingle (by rw [← h, hq, mul_zero])
  have hp' : (p : K⟦ℝ⟧) ≠ 0 := fun h' ↦ hp (Subtype.ext h')
  have hq' : (q : K⟦ℝ⟧) ≠ 0 := fun h' ↦ hq (Subtype.ext h')
  -- The supremum of the support is additive.
  have hsup : sSup (p : K⟦ℝ⟧).support + sSup (q : K⟦ℝ⟧).support = γ := by
    have h1 := supportSup_mul p q
    rw [h, supportSup_single hk hγ, supportSup_of_ne hp, supportSup_of_ne hq, ← WithBot.coe_add]
      at h1
    exact WithBot.coe_inj.mp h1.symm
  -- The order is additive.
  have horder : (p : K⟦ℝ⟧).order + (q : K⟦ℝ⟧).order = γ := by
    have h1 := congrArg (fun x : Series K ↦ (x : K⟦ℝ⟧).order) h
    simp only [Subring.coe_mul, coe_single] at h1
    rw [HahnSeries.order_mul hp' hq', HahnSeries.order_single hk] at h1
    exact h1
  have hpmem : (p : K⟦ℝ⟧).order ∈ (p : K⟦ℝ⟧).support :=
    HahnSeries.coeff_order_eq_zero.not.mpr hp'
  have hqmem : (q : K⟦ℝ⟧).order ∈ (q : K⟦ℝ⟧).support :=
    HahnSeries.coeff_order_eq_zero.not.mpr hq'
  have hple : (p : K⟦ℝ⟧).order ≤ sSup (p : K⟦ℝ⟧).support :=
    le_csSup (bddAbove_support p) hpmem
  have hqle : (q : K⟦ℝ⟧).order ≤ sSup (q : K⟦ℝ⟧).support :=
    le_csSup (bddAbove_support q) hqmem
  have hpeq : (p : K⟦ℝ⟧).order = sSup (p : K⟦ℝ⟧).support := by linarith
  rw [isMonomial_iff_support_eq_singleton]
  refine ⟨(p : K⟦ℝ⟧).order, Set.Subset.antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_)⟩
  · have h1 : (p : K⟦ℝ⟧).order ≤ y := HahnSeries.order_le_of_coeff_ne_zero hy
    have h2 : y ≤ (p : K⟦ℝ⟧).order := by
      rw [hpeq]
      exact le_csSup (bddAbove_support p) hy
    exact Set.mem_singleton_iff.mpr (le_antisymm h2 h1)
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hpmem

/-- Every element of grade zero in `RV̂` is the image of a finite-support series. -/
theorem exists_finiteSupportGradedEmbedding_eq_of
    (y : (degreeValuation K).Component 0) :
    ∃ p : Berarducci.FiniteSupportRing (K := K),
      finiteSupportGradedEmbedding K p = DirectSum.of (degreeValuation K).Component 0 y := by
  refine ⟨(degreeFiniteSupportResidueEquiv K).symm y, ?_⟩
  rw [finiteSupportGradedEmbedding_apply, RingEquiv.apply_symm_apply]

/-- A nonzero factor of a nonzero homogeneous element of `RV̂` is homogeneous, with grades
adding up to the grade of the product. -/
theorem exists_of_eq_of_mul_eq_of [CharZero K] {n : NatOrdinal}
    {Y : (degreeValuation K).Component n} (hY : Y ≠ 0) {A C : DegreeGraded K}
    (hAC : A * C = DirectSum.of (degreeValuation K).Component n Y) :
    ∃ (a c : NatOrdinal) (A₀ : (degreeValuation K).Component a)
      (C₀ : (degreeValuation K).Component c), A₀ ≠ 0 ∧ C₀ ≠ 0 ∧ a + c = n ∧
        A = DirectSum.of (degreeValuation K).Component a A₀ ∧
        C = DirectSum.of (degreeValuation K).Component c C₀ := by
  have hne : DirectSum.of (degreeValuation K).Component n Y ≠ 0 := fun h ↦
    hY (DirectSum.of_injective n (by rw [h, map_zero]))
  have hA : A ≠ 0 := fun h ↦ hne (by rw [← hAC, h, zero_mul])
  have hC : C ≠ 0 := fun h ↦ hne (by rw [← hAC, h, mul_zero])
  have hhom : A * C ∈ (degreeValuation K).homogeneousClasses := by
    rw [hAC, MaxAddDegree.mem_homogeneousClasses_iff]
    exact Or.inr ⟨n, Y, rfl⟩
  obtain ⟨hAhom, hChom⟩ := (degreeValuation K).mem_homogeneousClasses_of_mul_mem hA hC hhom
  rcases (MaxAddDegree.mem_homogeneousClasses_iff _ A).mp hAhom with rfl | ⟨a, A₀, rfl⟩
  · exact absurd rfl hA
  rcases (MaxAddDegree.mem_homogeneousClasses_iff _ C).mp hChom with rfl | ⟨c, C₀, rfl⟩
  · exact absurd rfl hC
  have hA₀ : A₀ ≠ 0 := fun h ↦ hA (by rw [h, map_zero])
  have hC₀ : C₀ ≠ 0 := fun h ↦ hC (by rw [h, map_zero])
  refine ⟨a, c, A₀, C₀, hA₀, hC₀, ?_, rfl, rfl⟩
  by_contra hne'
  have hcomp := congrArg (fun w : DegreeGraded K ↦ w (a + c)) hAC
  simp only [DirectSum.of_mul_of, DirectSum.of_eq_of_ne _ _ _ hne', DirectSum.of_eq_same] at hcomp
  exact MaxAddDegree.componentMul_ne_zero (degreeValuation K) A₀ C₀ hA₀ hC₀ hcomp

/-- The units of `RV̂` are the nonzero scalars: a unit is homogeneous of grade zero, hence a
finite-support series, and the units of `K(ℝ^{≤0})` are `K^×`. -/
theorem exists_algebraMap_eq_of_isUnit [CharZero K] {A : DegreeGraded K} (hA : IsUnit A) :
    ∃ k : K, k ≠ 0 ∧ A = algebraMap K (DegreeGraded K) k := by
  obtain ⟨A', hAA'⟩ := hA.exists_right_inv
  have hone : A * A' = DirectSum.of (degreeValuation K).Component 0
      (degreeValuation K).componentOne := by
    rw [hAA']
    exact DirectSum.one_def _
  have hone_ne : (degreeValuation K).componentOne ≠ 0 := by
    rw [MaxAddDegree.componentOne_eq_componentMk, Ne, MaxAddDegree.componentMk_eq_zero_iff,
      (degreeValuation K).map_one_eq_zero_of_isSeparated (degreeValuation_isSeparated K)]
    exact lt_irrefl _
  obtain ⟨a, c, A₀, C₀, -, -, hac, rfl, rfl⟩ := exists_of_eq_of_mul_eq_of hone_ne hone
  obtain ⟨ha, hc⟩ := NatOrdinal.add_eq_zero_iff.mp hac
  subst ha hc
  obtain ⟨p, hp⟩ := exists_finiteSupportGradedEmbedding_eq_of A₀
  obtain ⟨q, hq⟩ := exists_finiteSupportGradedEmbedding_eq_of C₀
  rw [← hp, ← hq, ← map_mul, ← map_one (finiteSupportGradedEmbedding K)] at hAA'
  have hpq : p * q = 1 := finiteSupportGradedEmbedding_injective K hAA'
  obtain ⟨k, hk, hpk⟩ := (isUnit_finiteSupport_iff_exists_scalar p).mp
    (isUnit_iff_exists_inv.mpr ⟨q, hpq⟩)
  refine ⟨k, hk, ?_⟩
  rw [← hp, hpk,
    show finiteSupportScalarHom (G := ℝ) k =
      algebraMap K (Berarducci.FiniteSupportRing (K := K)) k from rfl]
  exact (finiteSupportGradedEmbedding K).commutes k

/-! ### The coordinate functional -/

/-- A linearly independent family in a vector space admits, for each index `m`, a linear
functional equal to `1` at the `m`-th vector and `0` at the others. -/
theorem _root_.LinearIndependent.exists_dual_apply_eq {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [DecidableEq ι] {v : ι → V} (hv : LinearIndependent K v) (m : ι) :
    ∃ φ : V →ₗ[K] K, ∀ i, φ (v i) = if i = m then 1 else 0 := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Finsupp.lapply m) ∘ₗ hv.repr)
  refine ⟨φ, fun i ↦ ?_⟩
  have h := congrArg (fun f : Submodule.span K (Set.range v) →ₗ[K] K ↦
    f ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩) hφ
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
  rw [h, hv.repr_eq_single i ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ rfl,
    Finsupp.lapply_apply, Finsupp.single_apply]

variable (K) in
/-- The `K(ℝ^{≤0})`-coordinate of `RV̂ ≅ P̂ ⊗ K(ℝ^{≤0})` along a linear functional
`φ : P̂ → K`: the composite `RV̂ ≃ P̂ ⊗ K(ℝ^{≤0}) → K ⊗ K(ℝ^{≤0}) ≃ K(ℝ^{≤0})`. -/
def coordinate [CharZero K] (φ : PrincipalSubring K →ₗ[K] K) :
    DegreeGraded K →ₗ[K] Berarducci.FiniteSupportRing (K := K) :=
  (TensorProduct.lid K (Berarducci.FiniteSupportRing (K := K))).toLinearMap ∘ₗ
    TensorProduct.map φ LinearMap.id ∘ₗ (principalSubringTensorEquiv K).symm.toLinearMap

theorem coordinate_tmul [CharZero K] (φ : PrincipalSubring K →ₗ[K] K) (x : PrincipalSubring K)
    (p : Berarducci.FiniteSupportRing (K := K)) :
    coordinate K φ
        (principalSubringEmbedding K x * finiteSupportGradedEmbedding K p) =
      φ x • p := by
  rw [coordinate, LinearMap.comp_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    ← principalSubringTensorEquiv_tmul, AlgEquiv.symm_apply_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_toLinearMap, TensorProduct.lid_tmul]

/-- The coordinate functional is `K(ℝ^{≤0})`-linear for the grade-zero action. -/
theorem coordinate_finiteSupportGradedEmbedding_mul [CharZero K] (φ : PrincipalSubring K →ₗ[K] K)
    (p : Berarducci.FiniteSupportRing (K := K)) (z : DegreeGraded K) :
    coordinate K φ (finiteSupportGradedEmbedding K p * z) = p * coordinate K φ z := by
  obtain ⟨t, rfl⟩ := (principalSubringTensorEquiv K).surjective z
  rw [← principalSubringTensorEquiv_one_tmul, ← map_mul]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x q =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, principalSubringTensorEquiv_tmul,
        principalSubringTensorEquiv_tmul, coordinate_tmul, coordinate_tmul, mul_smul_comm]
  | add t₁ t₂ h₁ h₂ =>
      simp only [mul_add, map_add, h₁, h₂]

/-! ### The graded projection on finite-support series -/

/-- The graded projection `RV̂ → P̂` sends the image of a finite-support series `p` to the class
of `p` in grade zero of `P̂`, which is its constant coefficient. -/
theorem rvProjection_finiteSupportGradedEmbedding [CharZero K]
    (p : Berarducci.FiniteSupportRing (K := K)) :
    rvProjection K (finiteSupportGradedEmbedding K p) = gradeClass 0 (p : Series K) := by
  have hcut : ordinalValue (p : Series K) < ω^ ((0 : NatOrdinal) + 1) := by
    rw [← ordinalValueDegree_le_coe_iff]
    refine (ordinalValueDegree_le_degree _).trans ?_
    rw [WithBot.coe_zero, HahnSeries.degree_le_zero_iff]
    exact (mem_finiteSupportSubring_iff (p : Series K)).mp p.2
  rw [finiteSupportGradedEmbedding_eq_homogeneousMk, MaxAddDegree.homogeneousMk_apply,
    rvProjection_of, degreeLayerToPrincipalComponent_componentMk,
    gradeClass_eq_homogeneousMk hcut, MaxAddDegree.homogeneousMk_apply]
  exact congrArg _ (congrArg _ (Subtype.ext (coe_finiteSupportFiltrationRepresentative p)))

/-- The graded projection kills the image of a strictly negative monomial. -/
theorem rvProjection_finiteSupportMonomial_of_neg [CharZero K]
    {g : exponentMonoid ℝ} (hg : (g : ℝ) < 0) :
    rvProjection K (finiteSupportGradedEmbedding K (finiteSupportMonomial g)) = 0 := by
  rw [rvProjection_finiteSupportGradedEmbedding]
  apply gradeClass_eq_zero_of_lt
  have heq : ((finiteSupportMonomial (K := K) g : Berarducci.FiniteSupportRing (K := K)) :
      Series K) = single (g : ℝ) 1 g.2 :=
    Subtype.ext ((coe_finiteSupportMonomial g).trans (coe_single _ _ _).symm)
  rw [heq, ordinalValue_of_mem_negativeMonomialIdeal (single_one_mem_negativeMonomialIdeal hg),
    NatOrdinal.wpow_zero]
  exact zero_lt_one

/-- The graded projection sends the image of `t^0 = 1` to `1`. -/
theorem rvProjection_finiteSupportMonomial_zero [CharZero K] :
    rvProjection K (finiteSupportGradedEmbedding K
      (finiteSupportMonomial (K := K) (0 : exponentMonoid ℝ))) = 1 := by
  have h1 : finiteSupportMonomial (K := K) (0 : exponentMonoid ℝ) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_finiteSupportMonomial]
    exact HahnSeries.single_zero_one
  rw [h1, map_one, map_one]

/-! ### Block forms -/

variable (K) in
/-- The block form `∑ᵢ rv_J(X_i) · t^{δ_i}` in `RV̂`, for classes `X_i ∈ P̂` and exponents
`δ_i ≤ 0`. -/
def blockForm [CharZero K] {ι : Type*} [Fintype ι] (X : ι → PrincipalSubring K)
    (δ : ι → exponentMonoid ℝ) : DegreeGraded K :=
  ∑ i, principalSubringEmbedding K (X i) *
    finiteSupportGradedEmbedding K (finiteSupportMonomial (δ i))

theorem blockForm_def [CharZero K] {ι : Type*} [Fintype ι] (X : ι → PrincipalSubring K)
    (δ : ι → exponentMonoid ℝ) :
    blockForm K X δ = ∑ i, principalSubringEmbedding K (X i) *
      finiteSupportGradedEmbedding K (finiteSupportMonomial (δ i)) :=
  (rfl)

/-- The graded projection of a block form with a single exponent `δ_m = 0` is `X_m`. -/
theorem rvProjection_blockForm [CharZero K] {ι : Type*} [Fintype ι]
    (X : ι → PrincipalSubring K) (δ : ι → exponentMonoid ℝ) (m : ι) (hm : δ m = 0)
    (hδ : ∀ i, δ i = 0 → i = m) :
    rvProjection K (blockForm K X δ) = X m := by
  classical
  rw [blockForm_def, map_sum]
  rw [Finset.sum_eq_single m]
  · rw [map_mul, rvProjection_principalGradedEmbedding, hm,
      rvProjection_finiteSupportMonomial_zero, mul_one]
  · intro i _ hi
    have hneg : ((δ i : exponentMonoid ℝ) : ℝ) < 0 := by
      rcases lt_or_eq_of_le (show ((δ i : exponentMonoid ℝ) : ℝ) ≤ 0 from (δ i).2) with h | h
      · exact h
      · exact absurd (hδ i (Subtype.ext h)) hi
    rw [map_mul, rvProjection_finiteSupportMonomial_of_neg hneg, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ m) h

/-- The block form is homogeneous of grade `n` when its classes lie in `P_n`. -/
theorem blockForm_eq_of [CharZero K] {n : NatOrdinal} {ι : Type*} [Fintype ι]
    (x : ι → PrincipalComponent K n) (δ : ι → exponentMonoid ℝ) :
    blockForm K (fun i ↦ DirectSum.of (PrincipalComponent K) n (x i)) δ =
      DirectSum.of (degreeValuation K).Component n
        (∑ i, degreeFiniteSupportResidueEquiv K (finiteSupportMonomial (δ i)) •
          principalComponentToHahnDegreeLayer K n (x i)) := by
  rw [blockForm_def, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm, principalSubringEmbedding_of, finiteSupportGradedEmbedding_mul_of]

/-- The coordinate of a block form along a functional with `φ(X_i) = δ_{im}` is `t^{δ_m}`. -/
theorem coordinate_blockForm [CharZero K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → PrincipalSubring K) (δ : ι → exponentMonoid ℝ) (m : ι) (φ : PrincipalSubring K →ₗ[K] K)
    (hφ : ∀ i, φ (X i) = if i = m then 1 else 0) :
    coordinate K φ (blockForm K X δ) = finiteSupportMonomial (δ m) := by
  classical
  rw [blockForm_def, map_sum]
  rw [Finset.sum_eq_single m]
  · rw [coordinate_tmul, hφ, if_pos rfl, one_smul]
  · intro i _ hi
    rw [coordinate_tmul, hφ, if_neg hi, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ m) h

/-- FLLM24, proof of Proposition 3.2: a block form `∑ᵢ X_i t^{δ_i}` in `RV̂` with `X_i ∈ P_n`
linearly independent, `δ_m = 0` the only zero exponent and `X_m` irreducible in `P̂` is
irreducible in `RV̂`. -/
theorem irreducible_blockForm [CharZero K] {n : NatOrdinal} {ι : Type*} [Fintype ι]
    (x : ι → PrincipalComponent K n)
    (hli : LinearIndependent K (fun i ↦ DirectSum.of (PrincipalComponent K) n (x i)))
    (δ : ι → exponentMonoid ℝ) (m : ι) (hm : δ m = 0) (hδ : ∀ i, δ i = 0 → i = m)
    (hirr : Irreducible (DirectSum.of (PrincipalComponent K) n (x m))) :
    Irreducible (blockForm K (fun i ↦ DirectSum.of (PrincipalComponent K) n (x i)) δ) := by
  classical
  set B := blockForm K (fun i ↦ DirectSum.of (PrincipalComponent K) n (x i)) δ with hB
  have hproj : rvProjection K B = DirectSum.of (PrincipalComponent K) n (x m) :=
    rvProjection_blockForm _ δ m hm hδ
  obtain ⟨φ, hφ⟩ := hli.exists_dual_apply_eq m
  -- A factor whose projection is a unit is itself a unit.
  have key : ∀ A C : DegreeGraded K, B = A * C → IsUnit (rvProjection K A) →
      IsUnit A := by
    intro A C hAC hunit
    have hY : (∑ i, degreeFiniteSupportResidueEquiv K (finiteSupportMonomial (δ i)) •
        principalComponentToHahnDegreeLayer K n (x i)) ≠ 0 := by
      intro hzero
      have hBzero : B = 0 := by rw [hB, blockForm_eq_of, hzero, map_zero]
      rw [hBzero, map_zero] at hproj
      exact hirr.ne_zero hproj.symm
    have hAC' : A * C = DirectSum.of (degreeValuation K).Component n
        (∑ i, degreeFiniteSupportResidueEquiv K (finiteSupportMonomial (δ i)) •
          principalComponentToHahnDegreeLayer K n (x i)) := by
      rw [← hAC, hB, blockForm_eq_of]
    obtain ⟨a, c, A₀, C₀, hA₀, -, -, rfl, rfl⟩ := exists_of_eq_of_mul_eq_of hY hAC'
    -- The unit projection forces grade zero.
    have ha : a = 0 := by
      by_contra ha
      rw [rvProjection_of] at hunit
      exact not_isUnit_of_grade_ne_zero ha _ hunit
    subst ha
    obtain ⟨p, hp⟩ := exists_finiteSupportGradedEmbedding_eq_of A₀
    rw [← hp] at hAC ⊢
    -- The coordinate along `φ` shows that `p` divides `1`.
    have hcoord := congrArg (coordinate K φ) hAC
    rw [coordinate_blockForm _ δ m φ hφ, coordinate_finiteSupportGradedEmbedding_mul, hm] at hcoord
    have hone : finiteSupportMonomial (K := K) (0 : exponentMonoid ℝ) = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [coe_finiteSupportMonomial]
      exact HahnSeries.single_zero_one
    rw [hone] at hcoord
    have hunit : IsUnit p :=
      ⟨Units.mkOfMulEqOne p _ hcoord.symm, Units.val_mkOfMulEqOne hcoord.symm⟩
    exact hunit.map (finiteSupportGradedEmbedding K)
  refine ⟨fun hunit ↦ hirr.not_isUnit (hproj ▸ hunit.map (rvProjection K)),
    fun A C hAC ↦ ?_⟩
  have hprod : rvProjection K A * rvProjection K C =
      DirectSum.of (PrincipalComponent K) n (x m) := by
    rw [← map_mul, ← hAC, hproj]
  rcases hirr.isUnit_or_isUnit hprod.symm with hA | hC
  · exact Or.inl (key A C hAC hA)
  · exact Or.inr (key C A (by rw [hAC, mul_comm]) hC)

/-- FLLM24, proof of Proposition 3.2, the monomial step: if `A · C = t^γ · B` with `B` an
irreducible block form, then one of `A`, `C` is the image of a monomial `k t^x` of
`K(ℝ^{≤0})`. Finite-support series are primal in `RV̂` (LM24, Corollary 6.3.6), so `t^γ`
splits as `p₁ p₂` with `p₁ ∣ A` and `p₂ ∣ C`; the `p_i` are monomials, and cancelling them
leaves a factorisation of `B`. -/
theorem exists_isMonomial_factor_of_mul_eq [CharZero K] {n : NatOrdinal}
    {ι : Type*} [Fintype ι] (x : ι → PrincipalComponent K n)
    (hli : LinearIndependent K (fun i ↦ DirectSum.of (PrincipalComponent K) n (x i)))
    (δ : ι → exponentMonoid ℝ) (m : ι) (hm : δ m = 0) (hδ : ∀ i, δ i = 0 → i = m)
    (hirr : Irreducible (DirectSum.of (PrincipalComponent K) n (x m)))
    (γ : exponentMonoid ℝ) {A C : DegreeGraded K}
    (hAC : A * C = finiteSupportGradedEmbedding K (finiteSupportMonomial γ) *
      blockForm K (fun i ↦ DirectSum.of (PrincipalComponent K) n (x i)) δ) :
    ∃ p : Berarducci.FiniteSupportRing (K := K), IsMonomial (p : Series K) ∧
      (A = finiteSupportGradedEmbedding K p ∨ C = finiteSupportGradedEmbedding K p) := by
  set B := blockForm K (fun i ↦ DirectSum.of (PrincipalComponent K) n (x i)) δ with hB
  have hBirr : Irreducible B := irreducible_blockForm x hli δ m hm hδ hirr
  have hdvd : finiteSupportGradedEmbedding K (finiteSupportMonomial γ) ∣ A * C :=
    ⟨B, hAC⟩
  obtain ⟨a₁, a₂, ⟨A', hA'⟩, ⟨C', hC'⟩, hsplit⟩ :=
    finiteSupportGradedEmbedding_isPrimal (finiteSupportMonomial γ) hdvd
  -- The two factors of `t^γ` are monomials.
  have hres_ne : degreeFiniteSupportResidueEquiv K (finiteSupportMonomial (K := K) γ) ≠ 0 := by
    intro h
    have h1 : finiteSupportMonomial (K := K) γ = 0 :=
      (degreeFiniteSupportResidueEquiv K).injective (by rw [h, map_zero])
    have h2 := congrArg
      (fun q : Berarducci.FiniteSupportRing (K := K) ↦ ((q : Series K) : K⟦ℝ⟧).coeff γ) h1
    simp [coe_finiteSupportMonomial] at h2
  have hsplit' : a₁ * a₂ = DirectSum.of (degreeValuation K).Component 0
      (degreeFiniteSupportResidueEquiv K (finiteSupportMonomial γ)) := by
    rw [← hsplit, finiteSupportGradedEmbedding_apply]
  obtain ⟨a, c, A₀, C₀, -, -, hac, rfl, rfl⟩ := exists_of_eq_of_mul_eq_of hres_ne hsplit'
  obtain ⟨ha, hc⟩ := NatOrdinal.add_eq_zero_iff.mp hac
  subst ha hc
  obtain ⟨p₁, hp₁⟩ := exists_finiteSupportGradedEmbedding_eq_of A₀
  obtain ⟨p₂, hp₂⟩ := exists_finiteSupportGradedEmbedding_eq_of C₀
  rw [← hp₁, ← hp₂, ← map_mul] at hsplit
  have hp₁p₂ : p₁ * p₂ = finiteSupportMonomial γ :=
    finiteSupportGradedEmbedding_injective K hsplit.symm
  have hγ0 : ((γ : exponentMonoid ℝ) : ℝ) ≤ 0 := γ.2
  have hp₁p₂' : (p₁ : Series K) * (p₂ : Series K) = single (γ : ℝ) (1 : K) hγ0 := by
    have h1 := congrArg Subtype.val hp₁p₂
    rw [Subring.coe_mul] at h1
    rw [h1]
    exact Subtype.ext ((coe_finiteSupportMonomial γ).trans (coe_single _ _ _).symm)
  have hmono₁ : IsMonomial (p₁ : Series K) := isMonomial_of_mul_eq_single one_ne_zero hγ0 hp₁p₂'
  have hmono₂ : IsMonomial (p₂ : Series K) :=
    isMonomial_of_mul_eq_single one_ne_zero hγ0 (by rw [mul_comm]; exact hp₁p₂')
  -- Cancel `t^γ` to obtain a factorisation of `B`.
  have hγne : finiteSupportGradedEmbedding K (finiteSupportMonomial (K := K) γ) ≠ 0 := by
    rw [finiteSupportGradedEmbedding_apply]
    intro h
    exact hres_ne (DirectSum.of_injective 0 (by rw [h, map_zero]))
  have hBeq : B = A' * C' := by
    apply mul_left_cancel₀ hγne
    rw [← hAC, hA', hC', ← hp₁, ← hp₂, hsplit, map_mul]
    ring
  rcases hBirr.isUnit_or_isUnit hBeq with hA'u | hC'u
  · obtain ⟨k, hk, hk'⟩ := exists_algebraMap_eq_of_isUnit hA'u
    refine ⟨p₁ * algebraMap K _ k, ?_, Or.inl ?_⟩
    · obtain ⟨g, l, hg, hl, hp₁eq⟩ := isMonomial_iff.mp hmono₁
      refine isMonomial_iff.mpr ⟨g, l * k, hg, mul_ne_zero hl hk, ?_⟩
      rw [Subring.coe_mul,
        show ((algebraMap K (Berarducci.FiniteSupportRing (K := K)) k :
          Berarducci.FiniteSupportRing (K := K)) : Series K) = HahnSeries.Nonpositive.C k from
          congrArg Subtype.val (show algebraMap K (Berarducci.FiniteSupportRing (K := K)) k =
            finiteSupportScalarHom k from rfl) |>.trans
            (Subtype.ext ((coe_finiteSupportScalarHom k).trans
              (HahnSeries.Nonpositive.coe_C k).symm)),
        hp₁eq]
      apply Subtype.ext
      simp only [Subring.coe_mul, coe_single, HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply,
        HahnSeries.single_mul_single, add_zero]
    · rw [hA', ← hp₁, hk', map_mul, (finiteSupportGradedEmbedding K).commutes]
  · obtain ⟨k, hk, hk'⟩ := exists_algebraMap_eq_of_isUnit hC'u
    refine ⟨p₂ * algebraMap K _ k, ?_, Or.inr ?_⟩
    · obtain ⟨g, l, hg, hl, hp₂eq⟩ := isMonomial_iff.mp hmono₂
      refine isMonomial_iff.mpr ⟨g, l * k, hg, mul_ne_zero hl hk, ?_⟩
      rw [Subring.coe_mul,
        show ((algebraMap K (Berarducci.FiniteSupportRing (K := K)) k :
          Berarducci.FiniteSupportRing (K := K)) : Series K) = HahnSeries.Nonpositive.C k from
          congrArg Subtype.val (show algebraMap K (Berarducci.FiniteSupportRing (K := K)) k =
            finiteSupportScalarHom k from rfl) |>.trans
            (Subtype.ext ((coe_finiteSupportScalarHom k).trans
              (HahnSeries.Nonpositive.coe_C k).symm)),
        hp₂eq]
      apply Subtype.ext
      simp only [Subring.coe_mul, coe_single, HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply,
        HahnSeries.single_mul_single, add_zero]
    · rw [hC', ← hp₂, hk', map_mul, (finiteSupportGradedEmbedding K).commutes]

/-! ### Back to series -/

/-- A series whose initial form is the image of a nonzero finite-support series `p` is `p`. -/
theorem eq_of_initialForm_eq_finiteSupportGradedEmbedding [CharZero K] {a : Series K}
    {p : Berarducci.FiniteSupportRing (K := K)} (hp : p ≠ 0)
    (h : (degreeValuation K).initialForm a = finiteSupportGradedEmbedding K p) :
    a = (p : Series K) := by
  have hp' : (p : Series K) ≠ 0 := fun h' ↦ hp (Subtype.ext h')
  have hdeg0 : degreeValuation K (p : Series K) = 0 := degreeValuation_finiteSupport_eq_zero p hp
  -- `a` has degree zero, because its initial form lives in grade zero.
  have ha0 : degreeValuation K a = 0 := by
    have hne : (degreeValuation K).initialForm a ≠ 0 := by
      rw [h, finiteSupportGradedEmbedding_eq_initialForm]
      exact (degreeValuation K).initialForm_ne_zero_of_ne_zero (degreeValuation_isSeparated K) hp'
    have hbot : degreeValuation K a ≠ ⊥ := fun hbot ↦ hne
      ((degreeValuation K).initialForm_eq_zero_of_eq_bot hbot)
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hbot
    by_contra hd0
    have hcomp := congrArg (fun z : DegreeGraded K ↦ z d) h
    rw [finiteSupportGradedEmbedding_eq_initialForm, MaxAddDegree.initialForm_apply,
      MaxAddDegree.initialForm_apply, dif_pos hd.symm, dif_neg (by
        rw [hdeg0]
        intro h0
        exact hd0 (by rw [← hd, ← h0]))] at hcomp
    exact ((degreeValuation K).componentMk_eq_zero_iff d _).not.mpr
      (by rw [← hd]; exact lt_irrefl _) hcomp
  -- Hence `a` has finite support and its image in `RV̂` is its initial form.
  have hafin : a ∈ (finiteSupportSubring : Subring (Series K)) := by
    rw [mem_finiteSupportSubring_iff]
    rw [degreeValuation_apply] at ha0
    exact (HahnSeries.degree_eq_zero.mp ha0).2
  have ha : finiteSupportGradedEmbedding K ⟨a, hafin⟩ = finiteSupportGradedEmbedding K p := by
    rw [finiteSupportGradedEmbedding_eq_initialForm]
    exact h
  exact congrArg Subtype.val (finiteSupportGradedEmbedding_injective K ha)

end FLLM24

end
