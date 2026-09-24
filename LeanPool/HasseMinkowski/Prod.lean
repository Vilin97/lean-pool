/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Orthogonal sums and base change for quadratic forms

This file supplies the infrastructure relating Mathlib's orthogonal sum `QuadraticMap.prod`
and base change `QuadraticForm.baseChange`:

* `baseChange_prod`: base change commutes with the orthogonal sum.
* `baseChange_prod_neg`: the same with a negated second factor.
* `QuadraticMap.Equivalent.nondegenerate{,_iff}`: nondegeneracy is invariant under equivalence.
* `mul_unit_isotropic_iff`: isotropy is unchanged by scaling all weights by a unit.
* `weightedSumSquares_mul_squares_equivalent`: multiplying weights by squares gives an
  equivalent form.

The proofs mirror the reference development, adapted to Mathlib 4.33's API
(`baseChange_ext` on pure tensors avoids the bilinear-form machinery of the original).
-/

@[expose] public section

open Module QuadraticMap TensorProduct

namespace HasseMinkowski

/-! ### Base change of an orthogonal sum -/

section BaseChangeProd

variable {R A M₁ M₂ : Type*} [CommRing R] [CommRing A] [Algebra R A] [Invertible (2 : R)]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

-- Theorem: base change commutes with the orthogonal sum of quadratic forms.
theorem baseChange_prod (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (QuadraticForm.baseChange A (Q₁.prod Q₂)).Equivalent
      ((QuadraticForm.baseChange A Q₁).prod (QuadraticForm.baseChange A Q₂)) := by
  let pr : (A ⊗[R] (M₁ × M₂)) ≃ₗ[A] ((A ⊗[R] M₁) × (A ⊗[R] M₂)) :=
    TensorProduct.prodRight R A A M₁ M₂
  refine ⟨pr, ?_⟩
  have h : ((QuadraticForm.baseChange A Q₁).prod (QuadraticForm.baseChange A Q₂)).comp
        (pr : (A ⊗[R] (M₁ × M₂)) →ₗ[A] _) =
      QuadraticForm.baseChange A (Q₁.prod Q₂) := by
    apply baseChange_ext
    intro x
    rw [QuadraticMap.comp_apply]
    change ((QuadraticForm.baseChange A Q₁).prod (QuadraticForm.baseChange A Q₂))
        (TensorProduct.prodRight R A A M₁ M₂ (1 ⊗ₜ[R] x)) =
      QuadraticForm.baseChange A (Q₁.prod Q₂) (1 ⊗ₜ[R] x)
    rw [TensorProduct.prodRight_tmul]
    simp only [QuadraticMap.prod_apply, QuadraticForm.baseChange_tmul, mul_one, add_smul]
  intro m
  simpa using congr_fun h m

-- Theorem: base change commutes with negation.
theorem baseChange_neg (Q : QuadraticForm R M₁) :
    QuadraticForm.baseChange A (-Q) = -(QuadraticForm.baseChange A Q) := by
  apply baseChange_ext
  intro m
  simp [QuadraticForm.baseChange_tmul]

-- Theorem: base change commutes with an orthogonal sum with negated second factor.
theorem baseChange_prod_neg (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (QuadraticForm.baseChange A (Q₁.prod (-Q₂))).Equivalent
      ((QuadraticForm.baseChange A Q₁).prod (-(QuadraticForm.baseChange A Q₂))) := by
  rw [← baseChange_neg]
  exact baseChange_prod Q₁ (-Q₂)

end BaseChangeProd

/-! ### Base change of the matrix and discriminant -/

section BaseChangeDiscr

variable {R A ι M : Type*} [CommRing R] [CommRing A] [Algebra R A] [Invertible (2 : R)]
  [Invertible (2 : A)] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]

-- Theorem: base change multiplies the matrix of a quadratic form entrywise by `algebraMap`.
theorem baseChange_toMatrix (b : Basis ι R M) (Q : QuadraticForm R M) :
    QuadraticForm.toMatrix (b.baseChange A) (QuadraticForm.baseChange A Q) =
      (QuadraticForm.toMatrix b Q).map (algebraMap R A) := by
  ext i j
  simp only [QuadraticForm.toMatrix, LinearMap.toMatrix₂_apply, Matrix.map_apply,
    QuadraticForm.associated_baseChange, Module.Basis.baseChange_apply,
    LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.algebraMap_eq_smul_one]

-- Theorem: base change multiplies the discriminant by `algebraMap`.
theorem baseChange_discr (b : Basis ι R M) (Q : QuadraticForm R M) :
    QuadraticForm.discr (b.baseChange A) (QuadraticForm.baseChange A Q) =
      algebraMap R A (QuadraticForm.discr b Q) := by
  simp only [QuadraticForm.discr, baseChange_toMatrix, RingHom.map_det]
  rfl

end BaseChangeDiscr

/-! ### Nondegeneracy is invariant under equivalence -/

namespace QuadraticMap

namespace Equivalent

variable {R M M' N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup M']
  [Module R M] [Module R M'] [AddCommGroup N] [Module R N] [Invertible (2 : R)]

-- Theorem: equivalent quadratic maps are nondegenerate simultaneously.
theorem nondegenerate {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N}
    (h : Q.Equivalent Q') (hQ : Q.Nondegenerate) : Q'.Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot] at hQ ⊢
  obtain ⟨e⟩ := h
  have he := e.map_radical
  rw [hQ, Submodule.map_bot] at he
  exact he.symm

-- Theorem: equivalence preserves nondegeneracy in both directions.
theorem nondegenerate_iff {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N}
    (h : Q.Equivalent Q') : Q.Nondegenerate ↔ Q'.Nondegenerate :=
  ⟨fun hQ ↦ nondegenerate h hQ,
    fun hQ' ↦ nondegenerate (Nonempty.map (fun e ↦ e.symm) h) hQ'⟩

end Equivalent

end QuadraticMap

/-! ### Isotropy and rescaling weights

Multiplying every weight by a fixed unit multiplies the whole form by that unit, and
multiplying weights by squares is an isometry (Mathlib's
`isometryEquivWeightedSumSquaresWeightedSumSquares`).  Both leave isotropy unchanged. -/

section WeightedSumSquaresIsotropy

variable {S R ι : Type*} [Monoid S] [CommSemiring R] [Fintype ι]
  [DistribMulAction S R] [SMulCommClass S R R] {w w' : ι → Sˣ}

-- Theorem: scaling all weights of a weighted sum of squares by a unit preserves isotropy.
theorem mul_unit_isotropic_iff {a : Sˣ} (h : ∀ i, w' i = a * w i) :
    (weightedSumSquares R (fun i => (w i : S))).Isotropic ↔
      (weightedSumSquares R (fun i => (w' i : S))).Isotropic := by
  have hsmul : ∀ x : ι → R,
      (weightedSumSquares R (fun i => (w' i : S))) x =
        (a : S) • (weightedSumSquares R (fun i => (w i : S))) x := by
    intro x
    simp only [QuadraticMap.weightedSumSquares_apply, h, Units.val_mul, mul_smul,
      Finset.smul_sum]
  constructor
  · rintro ⟨x, hx, h0⟩
    exact ⟨x, hx, by rw [hsmul, h0, smul_zero]⟩
  · rintro ⟨x, hx, h0⟩
    refine ⟨x, hx, ?_⟩
    exact (IsUnit.smul_eq_zero a.isUnit).mp (by rw [← hsmul]; exact h0)

end WeightedSumSquaresIsotropy

section WeightedSumSquaresSquares

variable {S R ι : Type*} [Monoid S] [CommSemiring R] [Fintype ι]
  [DistribMulAction S R] [SMulCommClass S R R] [IsScalarTower S R R]

-- Theorem: replacing the weights by themselves times squares gives an equivalent form.
theorem weightedSumSquares_mul_squares_equivalent {w w' : ι → S}
    (u : ι → Sˣ) (h : ∀ i, w' i * u i ^ 2 = w i) :
    (weightedSumSquares R w).Equivalent (weightedSumSquares R w') :=
  ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares u h⟩

end WeightedSumSquaresSquares

/-! ### Discriminants of weighted sums of squares -/

section WeightedSumSquaresDiscr

variable {S R ι : Type*} [CommRing R] [Invertible (2 : R)]
  [Fintype ι] [DecidableEq ι] [CommMonoid S] [DistribMulAction S R] [SMulCommClass S R R]

-- Theorem: the matrix of a weighted sum of squares in the standard basis is diagonal.
theorem weightedSumSquares_toMatrix (w : ι → S) :
    QuadraticForm.toMatrix (Pi.basisFun R ι) (weightedSumSquares R w) =
      Matrix.diagonal fun i ↦ w i • (1 : R) := by
  ext i j
  simp only [QuadraticForm.toMatrix, LinearMap.toMatrix₂_apply, Pi.basisFun_apply,
    QuadraticMap.associated_apply, QuadraticMap.weightedSumSquares_apply, Pi.add_apply,
    Module.End.smul_def, QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul,
    Matrix.diagonal_apply]
  split_ifs with hij
  · simp only [hij, Pi.single_apply, mul_ite, mul_one, mul_zero, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_eq_single j (fun _ _ hkj ↦ by simp [hkj]) (by aesop)]
    · simp only [↓reduceIte]
      ring_nf
      have h4 : (4 : R) = 2 * 2 := by ring
      rw [← mul_smul_one, mul_right_comm _ _ 2]
      simp only [h4, ← mul_assoc, invOf_mul_self', one_mul]
      ring
  · simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_eq_add i j hij (fun _ _ hkj ↦ by simp [hkj]) (by aesop) (by aesop)]
    simp [(Ne.symm hij), hij]

-- Theorem: the discriminant of a weighted sum of squares is the product of the weights.
theorem weightedSumSquares_discr (w : ι → S) :
    QuadraticForm.discr (Pi.basisFun R ι) (weightedSumSquares R w) = ∏ i, w i • (1 : R) := by
  rw [QuadraticForm.discr, weightedSumSquares_toMatrix, Matrix.det_diagonal]

end WeightedSumSquaresDiscr

/-! ### Nondegeneracy via the discriminant

Over a domain in which `2` is invertible, a quadratic form is nondegenerate exactly when its
discriminant (the determinant of its matrix in a basis) is nonzero.  This is the standard
criterion: the radical of `Q` is the kernel of the associated bilinear form
(`QuadraticMap.radical_eq_ker_associated`), and a bilinear form over a domain is nondegenerate
iff its determinant is nonzero (`LinearMap.nondegenerate_iff_det_ne_zero`). -/

section NondegenerateDiscr

variable {R M ι : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι] [Invertible (2 : R)]

-- Theorem: over a domain with `2` invertible, `Q` is nondegenerate iff its discriminant
-- (determinant of its matrix in a basis) is nonzero.
theorem nondegenerate_iff_discr_ne_zero (b : Basis ι R M) (Q : QuadraticForm R M) :
    Q.Nondegenerate ↔ Q.discr b ≠ 0 := by
  rw [← QuadraticMap.nondegenerate_associated_iff, QuadraticForm.discr, QuadraticForm.toMatrix]
  exact LinearMap.nondegenerate_iff_det_ne_zero b

end NondegenerateDiscr

/-! ### Base change preserves nondegeneracy

`baseChange_discr` turns base change into the `algebraMap` on discriminants, and an injective
`algebraMap` (equivalently, `FaithfulSMul R A`) preserves being nonzero.  Applying the
discriminant criterion `nondegenerate_iff_discr_ne_zero` on both sides gives the result.

The hypotheses are necessarily a little stronger than "`A` is nontrivial": `ℚ → A` is injective
for every nontrivial `A`, but over a general domain `R` this can fail (e.g. `ℤ → 𝔽_p`), so
injectivity is recorded as `FaithfulSMul R A`.  The target must again be a domain (with `2`
invertible) for the discriminant criterion to apply there. -/

section NondegenerateBaseChange

variable {R M ι : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)]

-- Theorem: base change along a faithful algebra map (e.g. an injective one) preserves
-- nondegeneracy, provided the target is a domain with `2` invertible.
theorem nondegenerate_baseChange {A : Type*} [CommRing A] [Algebra R A] [IsDomain A]
    [Invertible (2 : A)] [FaithfulSMul R A] [Finite ι] (b : Basis ι R M)
    (Q : QuadraticForm R M) (hQ : Q.Nondegenerate) :
    (QuadraticForm.baseChange A Q).Nondegenerate := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [nondegenerate_iff_discr_ne_zero (b.baseChange A), baseChange_discr]
  intro h
  exact (nondegenerate_iff_discr_ne_zero b Q).mp hQ
    ((FaithfulSMul.algebraMap_eq_zero_iff R A).mp h)

end NondegenerateBaseChange

/-! ### Isotropy of an orthogonal sum

The orthogonal sum `Q₁.prod Q₂` evaluates to `(x, y) ↦ Q₁ x + Q₂ y`.  It is isotropic
exactly when some summand already is, or when the two summands represent a common nonzero
value with opposite signs: a nonzero isotropic vector `(x, y)` with `Q₁ x + Q₂ y = 0` has
`Q₁ x = -Q₂ y`, and the problematic case `Q₁ x = Q₂ y = 0` is precisely when a summand is
isotropic.  Nondegeneracy is *not* needed. -/

section ProdIsotropic

variable {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]
  [Module R M₁] [Module R M₂]

-- Theorem: an orthogonal sum is isotropic iff one summand is isotropic, or the two summands
-- represent a common nonzero value with opposite signs.
theorem prod_isotropic_iff (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.prod Q₂).Isotropic ↔
      Q₁.Isotropic ∨ Q₂.Isotropic ∨
        ∃ a : R, a ≠ 0 ∧ Q₁.represents a ∧ Q₂.represents (-a) := by
  constructor
  · rintro ⟨p, hp, h0⟩
    obtain ⟨x, y⟩ := p
    rw [QuadraticMap.prod_apply] at h0
    by_cases hx : x = 0
    · refine Or.inr (Or.inl ⟨y, fun hy ↦ hp ?_, ?_⟩)
      · rw [Prod.mk_eq_zero]; exact ⟨hx, hy⟩
      · rw [hx, map_zero, zero_add] at h0; exact h0
    · by_cases hy : y = 0
      · exact Or.inl ⟨x, hx, by rw [hy, map_zero, add_zero] at h0; exact h0⟩
      · by_cases ha : Q₁ x = 0
        · exact Or.inl ⟨x, hx, ha⟩
        · refine Or.inr (Or.inr ⟨Q₁ x, ha, ⟨x, hx, rfl⟩, ⟨y, hy, ?_⟩⟩)
          rw [add_eq_zero_iff_eq_neg] at h0
          rw [h0, neg_neg]
  · rintro (h | h | ⟨a, ha, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩)
    · obtain ⟨x, hx, hx0⟩ := h
      exact ⟨(x, 0), by simp [Prod.mk_eq_zero, hx], by simp [QuadraticMap.prod_apply, hx0]⟩
    · obtain ⟨y, hy, hy0⟩ := h
      exact ⟨(0, y), by simp [Prod.mk_eq_zero, hy], by simp [QuadraticMap.prod_apply, hy0]⟩
    · refine ⟨(x, y), by simp [Prod.mk_eq_zero, hx], ?_⟩
      rw [QuadraticMap.prod_apply, hx', hy']
      simp

end ProdIsotropic

/-! ### A common value from a signed orthogonal sum

Over a field, isotropy together with nondegeneracy is very strong: a nondegenerate isotropic
form represents *every* value.  Indeed, if `Q x₀ = 0` with `x₀ ≠ 0`, nondegeneracy supplies
`z` with `polarBilin Q x₀ z ≠ 0`, and then `Q (z + t • x₀) = Q z + t · polarBilin Q x₀ z`
ranges over all of `K` as `t` varies.

This upgrades the "opposite signs" disjunct of `prod_isotropic_iff` for `Q₁.prod (-Q₂)`: on
nontrivial spaces the two nondegenerate forms represent a common nonzero value.  (The
hypotheses that the spaces are nontrivial cannot be dropped: if, say, `V₂ = 0` then `Q₂`
represents nothing while `Q₁.prod (-Q₂) ≅ Q₁` can still be isotropic.) -/

section FieldProdNeg

variable {K V₁ V₂ : Type*} [Field K] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module K V₁] [Module K V₂] [Invertible (2 : K)]

-- Theorem: over a field a nondegenerate isotropic quadratic form represents every value.
theorem represents_of_isotropic_nondegenerate {Q : QuadraticForm K V₁}
    (hQ : Q.Nondegenerate) (h : Isotropic Q) (a : K) :
    represents Q a := by
  obtain ⟨x₀, hx₀, hx₀Q⟩ := h
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨x₀, hx₀, hx₀Q⟩
  have hpol : (QuadraticMap.polarBilin Q).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  obtain ⟨z, hz⟩ : ∃ z, QuadraticMap.polarBilin Q x₀ z ≠ 0 := by
    by_contra hc
    exact hx₀ (hpol.1 x₀ fun y ↦ not_not.mp (not_exists.mp hc y))
  set t : K := (a - Q z) / QuadraticMap.polarBilin Q x₀ z with ht
  have hQw : Q (z + t • x₀) = a := by
    rw [QuadraticMap.map_add Q z (t • x₀), QuadraticMap.map_smul Q t x₀, hx₀Q, smul_zero,
      add_zero, QuadraticMap.polar_smul_right Q t z x₀, QuadraticMap.polar_comm Q z x₀,
      ← QuadraticMap.polarBilin_apply_apply, ht]
    rw [smul_eq_mul, div_mul_cancel₀ (a - Q z) hz]
    ring
  refine ⟨z + t • x₀, fun hw ↦ ha ?_, hQw⟩
  rw [← hQw, hw, map_zero]

-- Theorem: a nondegenerate quadratic form on a nontrivial space represents a nonzero value.
omit [Invertible (2 : K)] in
theorem exists_ne_zero_represents_of_nondegenerate [Nontrivial V₁] {Q : QuadraticForm K V₁}
    (hQ : Q.Nondegenerate) : ∃ b : K, b ≠ 0 ∧ Q.represents b := by
  have hQne : Q ≠ 0 := by
    intro h0
    have htop : Q.radical = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro x
      rw [QuadraticMap.mem_radical_iff']
      simp [h0]
    rw [hQ.radical_eq_bot] at htop
    obtain ⟨x, hx⟩ := exists_ne (0 : V₁)
    have hxbot : x ∈ (⊥ : Submodule K V₁) := by rw [htop]; exact Submodule.mem_top
    exact hx (by simpa using hxbot)
  obtain ⟨v, hv⟩ : ∃ v, Q v ≠ 0 := by
    by_contra hc
    exact hQne (by ext v; simpa using not_not.mp (not_exists.mp hc v))
  exact ⟨Q v, hv, v, fun hvv ↦ hv (by rw [hvv, map_zero]), rfl⟩

-- Theorem: if `Q₁ ⊥ (-Q₂)` is isotropic, then over a field the nondegenerate forms `Q₁`, `Q₂`
-- on nontrivial spaces represent a common nonzero value.
theorem iso_prod_neg [Nontrivial V₁] [Nontrivial V₂] {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (h₁ : Q₁.Nondegenerate) (h₂ : Q₂.Nondegenerate)
    (h : (Q₁.prod (-Q₂)).Isotropic) :
    ∃ a : K, a ≠ 0 ∧ Q₁.represents a ∧ Q₂.represents a := by
  obtain ⟨b₁, hb₁, hQ₁b₁⟩ := exists_ne_zero_represents_of_nondegenerate h₁
  obtain ⟨b₂, hb₂, hQ₂b₂⟩ := exists_ne_zero_represents_of_nondegenerate h₂
  rcases (prod_isotropic_iff Q₁ (-Q₂)).mp h with hQi | hQ₂i | ⟨a, ha, hQ₁a, hQ₂a⟩
  · exact ⟨b₂, hb₂, represents_of_isotropic_nondegenerate h₁ hQi b₂, hQ₂b₂⟩
  · have hQ₂ : Isotropic Q₂ := by
      obtain ⟨y, hy, hyv⟩ := hQ₂i
      exact ⟨y, hy, neg_eq_zero.mp (by simpa using hyv)⟩
    exact ⟨b₁, hb₁, hQ₁b₁, represents_of_isotropic_nondegenerate h₂ hQ₂ b₁⟩
  · obtain ⟨y, hy, hyv⟩ := hQ₂a
    exact ⟨a, ha, hQ₁a, ⟨y, hy, neg_injective (by simpa using hyv)⟩⟩

end FieldProdNeg

end HasseMinkowski
