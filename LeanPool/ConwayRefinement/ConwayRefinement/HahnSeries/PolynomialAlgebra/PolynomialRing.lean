/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PolynomialAlgebra.InitialForms
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.Polynomiality
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.Extension
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.BasisOver
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.BaseChange

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.DegreeValuation

/-!
# The series ring is a polynomial ring over the series with finite support

Let `K((ℝ^{≤0}))` be the series ring and `K(ℝ^{≤0})` its subring of series with finite support
[LM24, Not. 2.1.5], written `K_fin` below. Let `𝓑` be a minimal system of homogeneous generators
of `P̂` — in Lean the classes `x i`, of degrees `wt i` — and choose series `b_i` with
initial form `x i ⊗ 1` and `deg b_i = wt i` (`GeneratorLifts`): the lifts `b_B` of the minimal
system.
Then evaluation `K_fin[X_i] → K((ℝ^{≤0}))`, `X_i ↦ b_i`, is an isomorphism of `K_fin`-algebras
(`polynomialRingEquiv`), and for a non-zero polynomial `F`, `deg F(b) = deg F` for the grading
`deg X_i = wt i`, with initial form the evaluation in `RV̂` of the homogeneous component of `F` of
largest degree.

This is the theorem `S = K_fin[b_B : B ∈ 𝓑]` of `FiniteDegreePolynomialRing`, with the ring `S`
of series of finite degree replaced by the whole series ring and the finite-degree part `P̂_{<ω}`
by `P̂`: injectivity is the degree formula, which rests on the polynomiality of `P̂`
(`Berarducci.aeval_injective_of_isMinimalSystem`) through the identification
`RV̂ ≅ P̂ ⊗_K K_fin`, and surjectivity is well-founded induction on the degree, the generators
spanning `P̂` (`OrdinalGraded.IsMinimalSystem.aeval_surjective`).
-/

open HahnSeries HahnSeries.Nonpositive Berarducci MvPolynomial OrdinalGraded

open scoped TensorProduct MaxAddDegree NatOrdinal

universe v w

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]
variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

/-! ### The lifts `b_i` of the minimal system -/

variable (wt x) in
/-- The lifts `b_i` of a family `x i ∈ P_{wt i}` of homogeneous elements of `P̂`: series `b_i`
with `deg b_i = wt i` whose initial form is `x i ⊗ 1` under `P̂ ⊗_K K_fin ≅ RV̂`, that is,
`rv(b_i) = x i`. This is `Berarducci.GeneratorLifts` for an arbitrary family of
homogeneous elements of `P̂` in place of the minimal system `𝓑` of `P̂_{<ω}`. -/
structure GeneratorLifts where
  /-- The series `b_i` lifting `x i`. -/
  lift : ι → Series K
  /-- `deg b_i = wt i`. -/
  degree_lift : ∀ i, ((lift i : Series K) : K⟦ℝ⟧).degree = (wt i : WithBot NatOrdinal)
  /-- `rv(b_i) = x i`: the initial form of `b_i` is `x i ⊗ 1` under `P̂ ⊗_K K_fin ≅ RV̂`. -/
  initialForm_lift : ∀ i,
    principalSubringTensorEquiv K (x i ⊗ₜ[K] 1) = (degreeValuation K).initialForm (lift i)

/-- Every non-zero homogeneous element of `P_α` is `rv(b)` for a principal series `b` of degree
`α` (Berarducci's principal representatives), so lifts exist for every family of non-zero
homogeneous elements. -/
theorem exists_generatorLifts (hmem : ∀ i, x i ∈ Berarducci.principalGrading K (wt i))
    (hne : ∀ i, x i ≠ 0) : Nonempty (GeneratorLifts wt x) := by
  have h : ∀ i, ∃ b : Series K, ((b : Series K) : K⟦ℝ⟧).degree = (wt i : WithBot NatOrdinal) ∧
      principalSubringTensorEquiv K (x i ⊗ₜ[K] 1) = (degreeValuation K).initialForm b := fun i ↦ by
    obtain ⟨a, ha⟩ := (DirectSum.mem_rangeLof_iff K _ _ _).mp (hmem i)
    rw [DirectSum.lof_eq_of] at ha
    have ha0 : a ≠ 0 := fun h0 ↦ hne i (by rw [← ha, h0, map_zero])
    obtain ⟨b, hb, hprin, hdeg, hmk⟩ := exists_principal_representative_of_ne_zero (wt i) a ha0
    refine ⟨b, hdeg, ?_⟩
    rw [← ha, ← hmk]
    exact Berarducci.principalSubringTensorEquiv_of_tmul_one_eq_initialForm b hb hprin hdeg
  choose b hdeg hin using h
  exact ⟨⟨b, hdeg, hin⟩⟩

namespace GeneratorLifts

variable (σ : GeneratorLifts wt x)

/-- `deg b_i = wt i`, for the degree as a `MaxAddDegree`. -/
theorem degreeValuation_lift (i : ι) :
    degreeValuation K (σ.lift i) = (wt i : WithBot NatOrdinal) := by
  rw [degreeValuation_apply]
  exact σ.degree_lift i

end GeneratorLifts

/-! ### The evaluation `K_fin[X_i] → P̂ ⊗_K K_fin ≅ RV̂` -/

variable (x) in
/-- The evaluation `K_fin[X_i] → P̂ ⊗_K K_fin`, `X_i ↦ x i ⊗ 1`. -/
def coordinateTensorEval :
    MvPolynomial ι (FiniteSupportRing (K := K)) →ₐ[FiniteSupportRing (K := K)]
      (PrincipalSubring K ⊗[K] FiniteSupportRing (K := K)) :=
  aeval fun i ↦ x i ⊗ₜ[K] 1

omit [CharZero K] in
/-- The evaluation into `P̂ ⊗_K K_fin` on a variable: `X_i ↦ x i ⊗ 1`. -/
theorem coordinateTensorEval_X (i : ι) : coordinateTensorEval x (X i) = x i ⊗ₜ[K] 1 :=
  aeval_X _ _

omit [CharZero K] in
/-- The evaluation into `P̂ ⊗_K K_fin` of a constant `c ∈ K_fin` is `1 ⊗ c`. -/
theorem coordinateTensorEval_C (c : FiniteSupportRing (K := K)) :
    coordinateTensorEval x (C c) = (1 : PrincipalSubring K) ⊗ₜ[K] c := by
  rw [coordinateTensorEval, aeval_C, Algebra.TensorProduct.right_algebraMap_apply]

omit [CharZero K] in
/-- The evaluation `K_fin[X_i] → P̂ ⊗_K K_fin` is, as a function, the evaluation at the `x i ⊗ 1`
of `K[X_i] → P̂` after extending scalars to `K_fin`. -/
theorem coe_coordinateTensorEval :
    ⇑(coordinateTensorEval x) = ⇑(aevalTmulOne K (FiniteSupportRing (K := K)) x) := by
  funext F
  induction F using MvPolynomial.induction_on with
  | C c => rw [coordinateTensorEval_C, aevalTmulOne_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, hp, coordinateTensorEval_X, aevalTmulOne_X]

variable (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
include hx

/-- **The polynomiality of `P̂` over `K_fin`.** The evaluation `K_fin[X_i] → P̂ ⊗_K K_fin` at a
minimal system of homogeneous generators is injective: the generators `x i` remain algebraically
independent after extending scalars to `K_fin`. -/
theorem coordinateTensorEval_injective : Function.Injective (coordinateTensorEval x) := by
  rw [coe_coordinateTensorEval]
  exact aevalTmulOne_injective (aeval_injective_of_isMinimalSystem hx)

omit [CharZero K] in
/-- The evaluation `K_fin[X_i] → P̂ ⊗_K K_fin` at a minimal system of homogeneous generators is
surjective: the generators `x i` generate `P̂` over `K`. -/
theorem coordinateTensorEval_surjective : Function.Surjective (coordinateTensorEval x) := by
  rw [coe_coordinateTensorEval]
  exact aevalTmulOne_surjective
    (hx.aeval_surjective (Berarducci.principalGrading_gradeZeroScalars K))

omit hx

variable (x) in
/-- The evaluation `K_fin[X_i] → RV̂`, `X_i ↦ rv(b_i) = x i`: the evaluation into `P̂ ⊗_K K_fin`
followed by the identification `P̂ ⊗_K K_fin ≅ RV̂`, as a ring homomorphism. -/
def gradedCoordinateEval :
    MvPolynomial ι (FiniteSupportRing (K := K)) →+* (degreeValuation K).AssociatedGraded :=
  (principalSubringTensorEquiv K).toRingEquiv.toRingHom.comp (coordinateTensorEval x).toRingHom

theorem gradedCoordinateEval_apply (F : MvPolynomial ι (FiniteSupportRing (K := K))) :
    gradedCoordinateEval x F = principalSubringTensorEquiv K (coordinateTensorEval x F) :=
  (rfl)

/-! ### Evaluation at the lifts `b_i` and the degree formula -/

variable (σ : GeneratorLifts wt x)

/-- Evaluation `K_fin[X_i] → K((ℝ^{≤0}))`, `F ↦ F(b)`, at the lifts `b_i`. -/
def evalAtLifts :
    MvPolynomial ι (FiniteSupportRing (K := K)) →ₐ[FiniteSupportRing (K := K)] Series K :=
  aeval σ.lift

/-- The evaluation `F ↦ F(b)` unfolded. -/
theorem evalAtLifts_eq : evalAtLifts σ = aeval σ.lift := (rfl)

/-- `X_i(b) = b_i`. -/
theorem evalAtLifts_X (i : ι) : evalAtLifts σ (X i) = σ.lift i :=
  aeval_X _ _

/-- A constant `c ∈ K_fin` evaluates to itself: `c(b) = c`. -/
theorem evalAtLifts_C (c : FiniteSupportRing (K := K)) : evalAtLifts σ (C c) = (c : Series K) :=
  aeval_C _ _

include hx

/-- The lifts `b_i` are initial-form coordinates of `K((ℝ^{≤0}))` over `K_fin`: `deg b_i = wt i`,
the non-zero scalars of `K_fin` have degree zero, and the evaluation into `RV̂` is an injective ring
homomorphism sending a constant `c` to `in(c)` and `X_i` to `in(b_i) = rv(b_i)`. -/
theorem isInitialFormCoordinates :
    MaxAddDegree.IsInitialFormCoordinates (degreeValuation K) wt σ.lift
      (gradedCoordinateEval x) where
  degree_algebraMap := Berarducci.degreeValuation_algebraMap_eq_zero
  degree_x := σ.degreeValuation_lift
  injective := (principalSubringTensorEquiv K).injective.comp (coordinateTensorEval_injective hx)
  map_C c := by
    rw [gradedCoordinateEval_apply, coordinateTensorEval_C,
      Berarducci.principalSubringTensorEquiv_one_tmul_eq_initialForm]
  map_X i := by
    rw [gradedCoordinateEval_apply, coordinateTensorEval_X]
    exact σ.initialForm_lift i

/-- `deg F(b) ≤ deg F`, the degree of `F` taken for the grading `deg X_i = wt i` (Mathlib's
`weightedTotalDegree`). -/
theorem degree_evalAtLifts_le (F : MvPolynomial ι (FiniteSupportRing (K := K))) :
    degreeValuation K (evalAtLifts σ F) ≤
      ((weightedTotalDegree wt F : NatOrdinal) : WithBot NatOrdinal) :=
  (isInitialFormCoordinates hx σ).degree_aeval_le F

/-- For non-zero `F`, `deg F(b) = deg F` for the grading `deg X_i = wt i`, and the initial form
of `F(b)` is the evaluation in `RV̂` of the homogeneous component of `F` of largest degree. -/
theorem degree_evalAtLifts_eq_and_initialForm {F : MvPolynomial ι (FiniteSupportRing (K := K))}
    (hF : F ≠ 0) :
    degreeValuation K (evalAtLifts σ F) =
        ((weightedTotalDegree wt F : NatOrdinal) : WithBot NatOrdinal) ∧
      (degreeValuation K).initialForm (evalAtLifts σ F) =
        principalSubringTensorEquiv K
          (coordinateTensorEval x (weightedHomogeneousComponent wt (weightedTotalDegree wt F) F)) :=
  (isInitialFormCoordinates hx σ).degree_aeval_eq_and_initialForm hF

/-- For `G` homogeneous for the grading `deg X_i = wt i`, the initial form of `G(b)` is the
evaluation of `G` in `RV̂`; both sides vanish for `G = 0`. -/
theorem initialForm_evalAtLifts_of_isWeightedHomogeneous
    {G : MvPolynomial ι (FiniteSupportRing (K := K))} {d : NatOrdinal}
    (hG : G.IsWeightedHomogeneous wt d) :
    (degreeValuation K).initialForm (evalAtLifts σ G) =
      principalSubringTensorEquiv K (coordinateTensorEval x G) :=
  (isInitialFormCoordinates hx σ).initialForm_aeval_of_isWeightedHomogeneous hG

/-- For non-zero `F`, `deg F(b) = deg F` for the grading `deg X_i = wt i`. -/
@[blueprint "thm:series-polynomial-degree"
  (phase := "Polynomial presentations")
  (title := "Weighted degree under evaluation at series lifts")
  (statement := /--
    Let $K$ be a field of characteristic zero, and let $(x_i)_{i\in I}$ be a
    minimal homogeneous generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$. For each $i$, choose a series
    $b_i\in K((\mathbb R^{\le0}))$ of degree $w_i$ whose initial form is the
    image of $x_i\otimes1$ under
    $\widehat{\mathrm P}\otimes_KK(\mathbb R^{\le0})
      \simeq\widehat{\mathrm{RV}}$.

    If $0\ne F\in K(\mathbb R^{\le0})[X_i:i\in I]$, then the degree of
    $F(b_i)$ equals the weighted total degree of $F$ for
    $\deg(X_i)=w_i$.
  -/)
  (proof := /--
  By \ref{fact:principal-subring-tensor-decomposition}, the associated graded
  ring is
  $\widehat{\mathrm P}\otimes_KK(\mathbb R^{\le0})$.
  \ref{thm:polynomial} makes evaluation at
  $(x_i\otimes1)$ injective after scalar extension. The hypotheses on $b_i$
  therefore make their initial forms an initial-form coordinate system. The
  top weighted homogeneous component of a non-zero $F$ has non-zero initial
  form after evaluation, so the degree of $F(b_i)$ is its weighted degree.
  -/)]
theorem degree_evalAtLifts_eq {F : MvPolynomial ι (FiniteSupportRing (K := K))} (hF : F ≠ 0) :
    degreeValuation K (evalAtLifts σ F) =
      ((weightedTotalDegree wt F : NatOrdinal) : WithBot NatOrdinal) :=
  (degree_evalAtLifts_eq_and_initialForm hx σ hF).1

/-- Evaluation `F ↦ F(b)` is injective: the lifts `b_i` are algebraically independent over
`K_fin`. -/
@[blueprint "thm:series-lifts-algebraically-independent"
  (phase := "Polynomial presentations")
  (title := "Algebraic independence of series lifts")
  (statement := /--
    Let $K$ be a field of characteristic zero, and let $(x_i)_{i\in I}$ be a
    minimal homogeneous generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$. For each $i$, choose a series
    $b_i\in K((\mathbb R^{\le0}))$ of degree $w_i$ whose initial form is the
    image of $x_i\otimes1$ under
    $\widehat{\mathrm P}\otimes_KK(\mathbb R^{\le0})
      \simeq\widehat{\mathrm{RV}}$. Then evaluation
    \[
      K(\mathbb R^{\le0})[X_i:i\in I]\longrightarrow
        K((\mathbb R^{\le0})),\qquad X_i\longmapsto b_i,
    \]
    is injective.
  -/)
  (proof := /--
  \ref{fact:principal-subring-tensor-decomposition} identifies the associated
  graded ring with
  $\widehat{\mathrm P}\otimes_KK(\mathbb R^{\le0})$.
  By \ref{thm:polynomial}, evaluation at the minimal homogeneous generating
  system is injective, and it remains injective after scalar extension. Hence
  a non-zero polynomial in the $b_i$ has a non-zero initial form and cannot
  evaluate to zero.
  -/)]
theorem evalAtLifts_injective : Function.Injective (evalAtLifts σ) :=
  (isInitialFormCoordinates hx σ).aeval_injective

/-- A polynomial `G` whose value `G(b)` has degree at most zero is constant: its weighted total
degree is zero, and every generator has positive degree. -/
theorem eq_C_of_degree_evalAtLifts_le_zero {G : MvPolynomial ι (FiniteSupportRing (K := K))}
    (hG : degreeValuation K (evalAtLifts σ G) ≤ 0) : G = C (G.coeff 0) := by
  classical
  by_cases hzero : G = 0
  · rw [hzero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, C_0]
  rw [degree_evalAtLifts_eq hx σ hzero, ← WithBot.coe_zero, WithBot.coe_le_coe] at hG
  refine MvPolynomial.ext _ _ fun d ↦ ?_
  rw [coeff_C]
  split_ifs with hd
  · rw [hd]
  · by_contra h
    have hw : Finsupp.weight wt d = 0 :=
      le_antisymm ((le_weightedTotalDegree wt (mem_support_iff.mpr h)).trans hG) bot_le
    exact hd (eq_zero_of_weight_eq_zero hx.ne_zero hw).symm

/-! ### Surjectivity: `K((ℝ^{≤0})) = K_fin[b_i]` -/

/-- Every element of `RV̂` is a finite sum of initial forms of values `F(b)`: it is the image of a
polynomial under `K_fin[X_i] → P̂ ⊗_K K_fin ≅ RV̂`, and the homogeneous components of that
polynomial evaluate to series whose initial forms are their images. -/
theorem exists_eq_sum_initialForm_evalAtLifts (g : (degreeValuation K).AssociatedGraded) :
    ∃ (κ : Type 1) (_ : Fintype κ) (p : κ → (evalAtLifts σ).range),
      g = ∑ k, (degreeValuation K).initialForm (p k : Series K) := by
  classical
  obtain ⟨F, hF⟩ := coordinateTensorEval_surjective hx ((principalSubringTensorEquiv K).symm g)
  set W : Finset NatOrdinal := F.support.image fun s ↦ Finsupp.weight wt s with hW
  refine ⟨{m // m ∈ W}, inferInstance,
    fun k ↦ ⟨evalAtLifts σ (weightedHomogeneousComponent wt k.1 F),
      (evalAtLifts σ).mem_range_self _⟩, ?_⟩
  have hg : g = principalSubringTensorEquiv K (coordinateTensorEval x F) := by
    rw [hF, AlgEquiv.apply_symm_apply]
  rw [hg]
  conv_lhs => rw [eq_sum_weightedHomogeneousComponent wt F]
  rw [map_sum, map_sum, ← Finset.sum_coe_sort W]
  exact Finset.sum_congr rfl fun (k : {m // m ∈ W}) _ ↦
    (initialForm_evalAtLifts_of_isWeightedHomogeneous hx σ
      (weightedHomogeneousComponent_isWeightedHomogeneous k.1 F)).symm

/-- Evaluation `F ↦ F(b)` is surjective: every series is a polynomial in the lifts `b_i` with
coefficients in `K_fin`, by well-founded induction on the degree. -/
@[blueprint "thm:series-lifts-generate-series-ring"
  (phase := "Polynomial presentations")
  (title := "Generation of the series ring by series lifts")
  (statement := /--
    Let $K$ be a field of characteristic zero, and let $(x_i)_{i\in I}$ be a
    minimal homogeneous generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$. For each $i$, choose a series
    $b_i\in K((\mathbb R^{\le0}))$ of degree $w_i$ whose initial form is the
    image of $x_i\otimes1$ under
    $\widehat{\mathrm P}\otimes_KK(\mathbb R^{\le0})
      \simeq\widehat{\mathrm{RV}}$. Then every element of
    $K((\mathbb R^{\le0}))$ is the value at $(b_i)$ of a polynomial in
    $K(\mathbb R^{\le0})[X_i:i\in I]$.
  -/)
  (proof := /--
  By \ref{fact:principal-subring-tensor-decomposition}, every element of the
  associated graded ring comes from a polynomial over
  $K(\mathbb R^{\le0})$ in the $x_i\otimes1$. By \ref{thm:polynomial}, its
  weighted homogeneous components are the initial forms of the corresponding
  values at the $b_i$. Thus every
  associated-graded element is a finite sum of initial forms of elements in
  the range of evaluation. Apply
  \ref{lem:initial-forms-generate-subalgebra} to that range and the separated
  degree to conclude that evaluation is surjective.
  -/)]
theorem evalAtLifts_surjective : Function.Surjective (evalAtLifts σ) := fun t ↦
  (AlgHom.mem_range _).mp
    (MaxAddDegree.mem_of_forall_exists_sum_initialForm (degreeValuation_isSeparated K)
      (exists_eq_sum_initialForm_evalAtLifts hx σ) t)

/-- The polynomial presentation of the series ring: evaluation `X_i ↦ b_i` on `K_fin[X_i]` has
image the whole ring, `K((ℝ^{≤0})) = K_fin[b_i]`. -/
theorem range_evalAtLifts_eq_top : (evalAtLifts σ).range = ⊤ :=
  eq_top_iff.mpr fun t _ ↦ (AlgHom.mem_range _).mpr (evalAtLifts_surjective hx σ t)

/-- **The series ring is a polynomial ring over the series with finite support.**
`K_fin[X_i] ≅ K((ℝ^{≤0}))`, `X_i ↦ b_i`, for the lifts `b_i` of a minimal system of homogeneous
generators of `P̂`. -/
@[blueprint "thm:hahn-series-polynomial-algebra"
  (phase := "Polynomial presentations")
  (title := "Polynomial presentation of the series ring")
  (statement := /--
    Let $K$ be a field of characteristic zero, and let $(x_i)_{i\in I}$ be a
    minimal homogeneous generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$. For each $i$, choose a series
    $b_i\in K((\mathbb R^{\le0}))$ of degree $w_i$ whose initial form is the
    image of $x_i\otimes1$ under
    $\widehat{\mathrm P}\otimes_KK(\mathbb R^{\le0})
      \simeq\widehat{\mathrm{RV}}$. Evaluation at the $b_i$ is an isomorphism
    of $K(\mathbb R^{\le0})$-algebras
    \[
      K(\mathbb R^{\le0})[X_i:i\in I]\simeq K((\mathbb R^{\le0})),
    \]
    sending $X_i$ to $b_i$.
  -/)
  (proof := /--
  Evaluation is injective by
  \ref{thm:series-lifts-algebraically-independent} and surjective by
  \ref{thm:series-lifts-generate-series-ring}; hence it defines the stated
  algebra isomorphism.
  -/)
  (highlight)]
def polynomialRingEquiv :
    MvPolynomial ι (FiniteSupportRing (K := K)) ≃ₐ[FiniteSupportRing (K := K)] Series K :=
  AlgEquiv.ofBijective (evalAtLifts σ) ⟨evalAtLifts_injective hx σ, evalAtLifts_surjective hx σ⟩

/-- The isomorphism `K_fin[X_i] ≅ K((ℝ^{≤0}))` is `F ↦ F(b)`. -/
theorem polynomialRingEquiv_apply (F : MvPolynomial ι (FiniteSupportRing (K := K))) :
    polynomialRingEquiv hx σ F = evalAtLifts σ F :=
  (rfl)

/-- `K((ℝ^{≤0})) ≅ K_fin[X_i]`: the series ring is a polynomial ring over `K_fin` on variables
indexed by a minimal system of homogeneous generators of `P̂`, the inverse of
`polynomialRingEquiv`. -/
def seriesPolynomialRingEquiv :
    Series K ≃ₐ[FiniteSupportRing (K := K)] MvPolynomial ι (FiniteSupportRing (K := K)) :=
  (polynomialRingEquiv hx σ).symm

/-- The inverse isomorphism sends `F(b)` back to `F`. -/
theorem seriesPolynomialRingEquiv_evalAtLifts (F : MvPolynomial ι (FiniteSupportRing (K := K))) :
    seriesPolynomialRingEquiv hx σ (evalAtLifts σ F) = F :=
  (polynomialRingEquiv hx σ).symm_apply_apply F

omit hx

/-! ### Existence of a minimal system and of its lifts -/

variable (K) in
/-- `P̂` has a minimal system of homogeneous generators, and any such system has lifts: there are
series `b_i` of degrees `wt i` forming a polynomial presentation `K((ℝ^{≤0})) = K_fin[b_i]`. -/
theorem exists_isMinimalSystem_and_generatorLifts :
    ∃ (ι' : Type (max v 1)) (wt' : ι' → NatOrdinal) (x' : ι' → PrincipalSubring K),
      IsMinimalSystem (Berarducci.principalGrading K) wt' x' ∧
        Nonempty (GeneratorLifts wt' x') := by
  obtain ⟨ι', wt', x', hx⟩ :=
    exists_isMinimalSystem (Berarducci.principalGrading K)
  exact ⟨ι', wt', x', hx, exists_generatorLifts hx.mem hx.apply_ne_zero⟩

end Berarducci
