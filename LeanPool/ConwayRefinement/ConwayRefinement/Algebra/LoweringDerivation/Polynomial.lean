/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.LoweringDerivation.Mu
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermPolynomial

/-!
# Polynomiality of the finite-degree part

The real-line lowering derivation is an instance of the filter-germ lowering derivation. This file
keeps the original real-line interface and transports its polynomiality statements from the single
filter-generic algebraic-independence theorem.
-/

universe u v w

open scoped DirectSum
open Filter Topology MvPolynomial

public noncomputable section

namespace LoweringDerivation

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]
variable (A : NatOrdinal → Submodule E R) [GradedAlgebra A]

/-! ### Homogeneous coordinates -/

/-- The decomposable part of degree `n`. -/
abbrev decomposable (n : ℕ) : Submodule E R :=
  GermPolynomial.decomposable A n

omit [GradedAlgebra A] in
theorem decomposable_le {n : ℕ} {N : Submodule E R}
    (h : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i + j = n →
      A (i : NatOrdinal) * A (j : NatOrdinal) ≤ N) :
    decomposable A n ≤ N :=
  GermPolynomial.decomposable_le A h

omit [GradedAlgebra A] in
theorem mul_mem_decomposable {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) {a b : R}
    (ha : a ∈ A (i : NatOrdinal)) (hb : b ∈ A (j : NatOrdinal)) :
    a * b ∈ decomposable A (i + j) :=
  GermPolynomial.mul_mem_decomposable A hi hj ha hb

variable {ι : Type w} (wt : ι → ℕ) (x : ι → R)

/-- Positive homogeneous generators, independent modulo decomposables and generating each finite
grade. -/
abbrev IsHomogeneousCoordinates : Prop :=
  GermPolynomial.IsHomogeneousCoordinates A wt x

variable {A wt x}

/-- Evaluation of a homogeneous polynomial lands in its prescribed grade. -/
theorem aeval_mem_of_forall_mem (hmem : ∀ i, x i ∈ A (wt i : NatOrdinal))
    {F : MvPolynomial ι E} {n : ℕ} (hF : IsWeightedHomogeneous wt F n) :
    aeval x F ∈ A (n : NatOrdinal) :=
  GermPolynomial.aeval_mem_of_forall_mem hmem hF

/-- Evaluation at homogeneous coordinates commutes with taking a homogeneous component. -/
theorem decompose_aeval (hmem : ∀ i, x i ∈ A (wt i : NatOrdinal))
    (F : MvPolynomial ι E) (n : ℕ) :
    (DirectSum.decompose A (aeval x F) (n : NatOrdinal) : R) =
      aeval x (weightedHomogeneousComponent wt n F) :=
  GermPolynomial.decompose_aeval hmem F n

/-- Arbitrary polynomial generation may be replaced by homogeneous polynomial generation. -/
theorem IsHomogeneousCoordinates.of_surjective (one_le : ∀ i, 1 ≤ wt i)
    (hmem : ∀ i, x i ∈ A (wt i : NatOrdinal))
    (independent : ∀ (n : ℕ) (c : ι →₀ E), (∀ i ∈ c.support, wt i = n) →
      Finsupp.linearCombination E x c ∈ decomposable A n → c = 0)
    (surj : ∀ (n : ℕ), ∀ y ∈ A (n : NatOrdinal),
      ∃ F : MvPolynomial ι E, aeval x F = y) :
    IsHomogeneousCoordinates A wt x :=
  GermPolynomial.IsHomogeneousCoordinates.of_surjective one_le hmem independent surj

variable (A wt x) in
/-- A minimal system of positive homogeneous generators. -/
abbrev IsMinimalSystem : Prop := GermPolynomial.IsMinimalSystem A wt x

/-- A minimal system generates every finite grade. -/
theorem IsMinimalSystem.isHomogeneousCoordinates (h0 : GradeZeroScalars A)
    (hx : IsMinimalSystem A wt x) : IsHomogeneousCoordinates A wt x :=
  GermPolynomial.IsMinimalSystem.isHomogeneousCoordinates h0 hx

/-- A positive-degree homogeneous polynomial is its linear part modulo decomposables. -/
theorem exists_linear_part (hwt : ∀ i, 1 ≤ wt i)
    (hmem : ∀ i, x i ∈ A (wt i : NatOrdinal))
    {F : MvPolynomial ι E} {n : ℕ} (hn : 1 ≤ n) (hF : IsWeightedHomogeneous wt F n) :
    ∃ c : ι →₀ E, (∀ i ∈ c.support, wt i = n) ∧
      aeval x F - Finsupp.linearCombination E x c ∈ decomposable A n ∧
      ∀ i, c i = F.coeff (Finsupp.single i 1) := by
  exact GermPolynomial.exists_linear_part hwt hmem hn hF

/-! ### The real-line derivation as a filter-germ derivation -/

variable {Δ : R →ₗ[E] FunAtZeroMinus R}

private theorem smul_eq_const_mul (a : R) (f : FunAtZeroMinus R) :
    a • f = (a : FunAtZeroMinus R) * f := by
  induction f using Filter.Germ.inductionOn with
  | h f => rfl

/-- The real-line lowering map with its Leibniz law, regarded as a derivation. -/
def IsLoweringDerivation.toDerivation (hΔ : IsLoweringDerivation A Δ) :
    Derivation E R (FunAtZeroMinus R) :=
  Derivation.mk' Δ fun a b => by
    rw [hΔ.map_mul, smul_eq_const_mul, smul_eq_const_mul,
      mul_comm (Δ a) (b : FunAtZeroMinus R), add_comm]

omit [GradedAlgebra A] in
@[simp]
theorem IsLoweringDerivation.toDerivation_apply (hΔ : IsLoweringDerivation A Δ) (a : R) :
    hΔ.toDerivation a = Δ a := by
  change Δ a = Δ a
  rfl

omit [GradedAlgebra A] in
private theorem germSubmodule_eq_funAtZeroMinusSubmodule (W : Submodule E R) :
    GermPolynomial.germSubmodule (l := 𝓝[<] (0 : ℝ)) W = funAtZeroMinusSubmodule W := by
  ext f
  rw [GermPolynomial.mem_germSubmodule_iff, mem_funAtZeroMinusSubmodule_iff]

omit [GradedAlgebra A] in
/-- The real-line lowering derivation satisfies the filter-germ lowering conditions. -/
theorem IsLoweringDerivation.toGerm (hΔ : IsLoweringDerivation A Δ) :
    GermPolynomial.IsLoweringDerivation A hΔ.toDerivation where
  mem_lower {α} hα {a} ha := by
    rw [IsLoweringDerivation.toDerivation_apply,
      germSubmodule_eq_funAtZeroMinusSubmodule]
    exact hΔ.mem_lower hα ha
  eq_zero {α} hα {a} ha := by
    rw [IsLoweringDerivation.toDerivation_apply]
    exact hΔ.eq_zero hα ha
  injective {α} hα {a} ha hzero := by
    rw [IsLoweringDerivation.toDerivation_apply] at hzero
    exact hΔ.injective hα ha hzero

namespace IsHomogeneousCoordinates

variable (hx : IsHomogeneousCoordinates A wt x)
include hx

/-- Evaluation of a homogeneous polynomial lands in its prescribed grade. -/
theorem aeval_mem {F : MvPolynomial ι E} {n : ℕ} (hF : IsWeightedHomogeneous wt F n) :
    aeval x F ∈ A (n : NatOrdinal) :=
  GermPolynomial.IsHomogeneousCoordinates.aeval_mem hx hF

variable (hΔ : IsLoweringDerivation A Δ)
include hΔ

omit hx in
theorem map_algebraMap (e : E) : Δ (algebraMap E R e) = 0 :=
  GermPolynomial.IsHomogeneousCoordinates.map_algebraMap hΔ.toGerm e

omit hx in
/-- The chain rule for evaluation along homogeneous coordinates. -/
theorem map_aeval (g : ι → ℝ → MvPolynomial ι E)
    (hg : ∀ i, Δ (x i) = ((fun γ ↦ aeval x (g i γ)) : FunAtZeroMinus R))
    (F : MvPolynomial ι E) :
    Δ (aeval x F) =
      ((fun γ ↦ aeval x (mkDerivation E (fun i ↦ g i γ) F)) : FunAtZeroMinus R) :=
  GermPolynomial.IsHomogeneousCoordinates.map_aeval hΔ.toGerm g hg F

omit [GradedAlgebra A] in
/-- Polynomial representatives of the derivatives of the homogeneous coordinates. -/
theorem exists_lifts : ∃ g : ι → ℝ → MvPolynomial ι E,
    (∀ i γ, IsWeightedHomogeneous wt (g i γ) (wt i - 1)) ∧
      ∀ i, Δ (x i) = ((fun γ ↦ aeval x (g i γ)) : FunAtZeroMinus R) :=
  GermPolynomial.IsHomogeneousCoordinates.exists_lifts hx hΔ.toGerm

end IsHomogeneousCoordinates

/-- A positive-weight homogeneous polynomial of degree zero is constant. -/
theorem eq_C_of_isWeightedHomogeneous_zero (hwt : ∀ i, 1 ≤ wt i)
    {p : MvPolynomial ι E} (hp : IsWeightedHomogeneous wt p 0) :
    p = C (p.coeff 0) :=
  GermPolynomial.eq_C_of_isWeightedHomogeneous_zero hwt hp

/-- A positive-degree homogeneous polynomial in the joint kernel of the pointwise derivations is
zero. -/
theorem eq_zero_of_eventually_mkDerivation_eq_zero [CharZero E]
    (hwt : ∀ i, 1 ≤ wt i) (hmem : ∀ i, x i ∈ A (wt i : NatOrdinal))
    (hind : ∀ (n : ℕ) (c : ι →₀ E), (∀ i ∈ c.support, wt i = n) →
      Finsupp.linearCombination E x c ∈ decomposable A n → c = 0)
    (hΔ : IsLoweringDerivation A Δ) (g : ι → ℝ → MvPolynomial ι E)
    (hghom : ∀ i γ, IsWeightedHomogeneous wt (g i γ) (wt i - 1))
    (hg : ∀ i, Δ (x i) = ((fun γ ↦ aeval x (g i γ)) : FunAtZeroMinus R)) (n : ℕ) :
    ∀ F : MvPolynomial ι E, 1 ≤ n → IsWeightedHomogeneous wt F n →
      (∀ᶠ γ in 𝓝[<] (0 : ℝ), mkDerivation E (fun i ↦ g i γ) F = 0) → F = 0 := by
  apply GermPolynomial.eq_zero_of_eventually_mkDerivation_eq_zero hwt hmem hind
    hΔ.toGerm g hghom hg n

namespace IsHomogeneousCoordinates

variable [CharZero E] (hx : IsHomogeneousCoordinates A wt x)
  (hΔ : IsLoweringDerivation A Δ)
include hx hΔ

/-- No nonzero homogeneous relation holds among the coordinates. -/
theorem eq_zero_of_aeval_eq_zero_of_isWeightedHomogeneous [Nontrivial R] (n : ℕ) :
    ∀ F : MvPolynomial ι E, IsWeightedHomogeneous wt F n → aeval x F = 0 → F = 0 :=
  GermPolynomial.IsHomogeneousCoordinates.eq_zero_of_aeval_eq_zero_of_isWeightedHomogeneous
    hx hΔ.toGerm n

/-- The homogeneous coordinates are algebraically independent. -/
theorem aeval_injective [Nontrivial R] :
    Function.Injective (aeval x : MvPolynomial ι E →ₐ[E] R) :=
  GermPolynomial.IsHomogeneousCoordinates.aeval_injective hx hΔ.toGerm

end IsHomogeneousCoordinates

end LoweringDerivation
