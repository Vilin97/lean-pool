/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.Expansion
public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Filter.Germ.LinearMap
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.InternalGrading
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.LoweringDerivation.Mu
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.OrdinalGenerators
public import Mathlib.RingTheory.Derivation.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.WeightedTotalDegree

/-!
# Finite-degree polynomiality for filter-germ lowering derivations

Let `A` be an ordinal-graded algebra over a field `K`, and choose positive homogeneous generators
whose images form a basis modulo the decomposable part in each finite degree. Suppose that `A`
has a derivation into filter germs which lowers successor degrees by one, vanishes on degrees that
are limit ordinals,
and is injective on every homogeneous component of successor degree. Then those generators are
algebraically independent.

The proof represents the derivatives of the generators by homogeneous polynomials. The chain rule
sends a least-degree homogeneous relation to the joint kernel of the resulting pointwise
derivations. Comparing the two highest powers of a variable reduces that kernel calculation to
independence modulo decomposables. This is the finite-degree algebraic-independence argument; the
choice of filter and the universe of the grading play no role.
-/

universe u v w z q

open scoped DirectSum
open Filter MvPolynomial

public noncomputable section

namespace GermPolynomial

export LoweringDerivation (GradeZeroScalars gradeZeroScalars_iff)

variable {K : Type u} {R : Type v} {T : Type q}
variable [Field K] [CommRing R] [Algebra K R]
variable {l : Filter T}
variable (A : NatOrdinal.{z} → Submodule K R) [GradedAlgebra A]

/-- Germs whose values eventually lie in a submodule. -/
def germSubmodule (W : Submodule K R) : Submodule K (Germ l R) :=
  LinearMap.range (Germ.mapLinear W.subtype)

/-- Membership in the germ submodule is eventual pointwise membership. -/
theorem mem_germSubmodule_iff (W : Submodule K R) (f : Germ l R) :
    f ∈ germSubmodule (l := l) W ↔ Germ.LiftPred (· ∈ W) f := by
  classical
  constructor
  · rintro ⟨g, rfl⟩
    induction g using Germ.inductionOn with
    | h g =>
      rw [Germ.mapLinear_coe, Germ.liftPred_coe]
      exact Filter.Eventually.of_forall fun x ↦ (g x).property
  · intro hf
    induction f using Germ.inductionOn with
    | h f =>
      rw [Germ.liftPred_coe] at hf
      let g : T → W := fun x ↦ if hx : f x ∈ W then ⟨f x, hx⟩ else 0
      refine ⟨(g : Germ l W), ?_⟩
      rw [Germ.mapLinear_coe, Germ.coe_eq]
      exact hf.mono fun x hx ↦ by simp [g, hx]

/-- A germ eventually valued in a submodule has an everywhere-valued representative. -/
theorem exists_rep_of_mem_germSubmodule (W : Submodule K R) {f : Germ l R}
    (hf : f ∈ germSubmodule (l := l) W) :
    ∃ g : T → R, (∀ x, g x ∈ W) ∧ f = (g : Germ l R) := by
  classical
  rw [mem_germSubmodule_iff] at hf
  induction f using Germ.inductionOn with
  | h f =>
    rw [Germ.liftPred_coe] at hf
    let g : T → R := fun x ↦ if hx : f x ∈ W then f x else 0
    refine ⟨g, fun x ↦ by
      by_cases hx : f x ∈ W
      · simp [g, hx]
      · simp [g, hx], ?_⟩
    rw [Germ.coe_eq]
    exact hf.mono fun x hx ↦ by simp [g, hx]

/-- A derivation valued in germs which lowers every successor degree by one. -/
structure IsLoweringDerivation (Δ : Derivation K R (Germ l R)) : Prop where
  mem_lower : ∀ {α : NatOrdinal.{z}}, 0 < α.constantCoeff → ∀ {x : R}, x ∈ A α →
    Δ x ∈ germSubmodule (l := l) (A (α.removeNat 1))
  eq_zero : ∀ {α : NatOrdinal.{z}}, α.constantCoeff = 0 → ∀ {x : R}, x ∈ A α → Δ x = 0
  injective : ∀ {α : NatOrdinal.{z}}, 0 < α.constantCoeff → ∀ {x : R},
    x ∈ A α → Δ x = 0 → x = 0

namespace IsLoweringDerivation

variable {A} {Δ : Derivation K R (Germ l R)} (hΔ : IsLoweringDerivation (l := l) A Δ)

theorem natCast_removeNat_one (j : ℕ) (hj : 1 ≤ j) :
    (j : NatOrdinal.{z}).removeNat 1 = ((j - 1 : ℕ) : NatOrdinal.{z}) := by
  have hcoeff : 1 ≤ (j : NatOrdinal.{z}).constantCoeff := by
    rwa [NatOrdinal.constantCoeff_natCast]
  symm
  apply (NatOrdinal.eq_removeNat_iff_add_natCast_eq hcoeff).mpr
  rw [← Nat.cast_add, Nat.sub_add_cancel hj]

theorem natCast_constantCoeff_pos (j : ℕ) (hj : 1 ≤ j) :
    0 < (j : NatOrdinal.{z}).constantCoeff := by
  rw [NatOrdinal.constantCoeff_natCast]
  exact hj

include hΔ

omit [GradedAlgebra A] in
theorem mem_lower_natCast {j : ℕ} (hj : 1 ≤ j) {x : R}
    (hx : x ∈ A (j : NatOrdinal.{z})) :
    Δ x ∈ germSubmodule (l := l) (A ((j - 1 : ℕ) : NatOrdinal.{z})) := by
  rw [← natCast_removeNat_one j hj]
  exact IsLoweringDerivation.mem_lower hΔ (natCast_constantCoeff_pos j hj) hx

end IsLoweringDerivation

/-- The Leibniz rule with the factors embedded as constant germs. -/
theorem derivation_leibniz (Δ : Derivation K R (Germ l R)) (x y : R) :
    Δ (x * y) = Δ x * (y : Germ l R) + (x : Germ l R) * Δ y := by
  rw [Δ.leibniz]
  change (x : Germ l R) * Δ y + (y : Germ l R) * Δ x = _
  ac_rfl


/-! ### Decomposables -/

/-- The decomposables `(A_{<ω})₊² ∩ A_n = ∑_{i+k=n, i,k ≥ 1} A_i A_k` in finite degree `n`. -/
def decomposable (n : ℕ) : Submodule K R :=
  ⨆ (i : ℕ) (j : ℕ) (_ : 1 ≤ i) (_ : 1 ≤ j) (_ : i + j = n),
    A (i : NatOrdinal.{z}) * A (j : NatOrdinal.{z})

omit [GradedAlgebra A] in
theorem decomposable_le {n : ℕ} {N : Submodule K R}
    (h : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i + j = n →
      A (i : NatOrdinal.{z}) * A (j : NatOrdinal.{z}) ≤ N) :
    decomposable A n ≤ N :=
  iSup_le fun i ↦ iSup_le fun j ↦ iSup_le fun hi ↦ iSup_le fun hj ↦ iSup_le fun hij ↦
    h i j hi hj hij

omit [GradedAlgebra A] in
theorem mul_mem_decomposable {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) {a b : R}
    (ha : a ∈ A (i : NatOrdinal.{z})) (hb : b ∈ A (j : NatOrdinal.{z})) :
    a * b ∈ decomposable A (i + j) :=
  Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hi
    (Submodule.mem_iSup_of_mem hj (Submodule.mem_iSup_of_mem rfl (Submodule.mul_mem_mul ha hb)))))

omit [GradedAlgebra A] in
/-- At a finite ordinal degree, ordinal decomposables are the ordinary finite-degree
decomposables. -/
theorem decomposableAt_natCast (n : ℕ) :
    OrdinalGraded.decomposableAt A (n : NatOrdinal.{z}) = decomposable A n := by
  apply le_antisymm
  · refine OrdinalGraded.decomposableAt_le A fun i j hi hj hij ↦ ?_
    have hi_lt : i < NatOrdinal.of Ordinal.omega0 :=
      (le_add_of_nonneg_right (zero_le : 0 ≤ j)).trans_lt
        (hij.le.trans_lt (NatOrdinal.natCast_lt_omega0 n))
    have hj_lt : j < NatOrdinal.of Ordinal.omega0 :=
      (le_add_of_nonneg_left (zero_le : 0 ≤ i)).trans_lt
        (hij.le.trans_lt (NatOrdinal.natCast_lt_omega0 n))
    obtain ⟨i, rfl⟩ := NatOrdinal.lt_omega0.mp hi_lt
    obtain ⟨j, rfl⟩ := NatOrdinal.lt_omega0.mp hj_lt
    rw [← Nat.cast_add] at hij
    have hij' : i + j = n := Nat.cast_injective hij
    have hi' : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hi)
    have hj' : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hj)
    exact fun _ h ↦ Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem j
      (Submodule.mem_iSup_of_mem hi' (Submodule.mem_iSup_of_mem hj'
        (Submodule.mem_iSup_of_mem hij' h))))
  · refine decomposable_le A fun i j hi hj hij ↦ ?_
    have hi' : (i : NatOrdinal.{z}) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hi)
    have hj' : (j : NatOrdinal.{z}) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hj)
    refine Submodule.mul_le.mpr fun a ha b hb ↦ ?_
    simpa [← hij] using OrdinalGraded.mul_mem_decomposableAt A hi' hj' ha hb

/-! ### Homogeneous generators of `A_{<ω}` -/

variable {ι : Type w} (wt : ι → ℕ) (x : ι → R)

/-- A family of homogeneous generators of `A_{<ω}`: `x i ∈ A_{wt i}` with `wt i ≥ 1`, the `x i` of
degree `n` linearly independent modulo the decomposables `(A_{<ω})₊² ∩ A_n`, and every element of
`A_n` a polynomial in the `x i` homogeneous of degree `n` for the grading `deg X_i = wt i`
(Mathlib's `IsWeightedHomogeneous wt`). The paper's minimal systems `𝓑` are exactly such families,
and these two properties are all its proofs use. -/
structure IsHomogeneousCoordinates : Prop where
  one_le : ∀ i, 1 ≤ wt i
  mem : ∀ i, x i ∈ A (wt i : NatOrdinal.{z})
  independent : ∀ (n : ℕ) (c : ι →₀ K), (∀ i ∈ c.support, wt i = n) →
    Finsupp.linearCombination K x c ∈ decomposable A n → c = 0
  surj : ∀ (n : ℕ), ∀ y ∈ A (n : NatOrdinal.{z}),
    ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F n ∧ aeval x F = y

variable {A wt x}

/-- Evaluation of a polynomial homogeneous of degree `n` (for `deg X_i = wt i`) at homogeneous
elements `x i ∈ A_{wt i}` lands in `A_n`. -/
theorem aeval_mem_of_forall_mem (hmem : ∀ i, x i ∈ A (wt i : NatOrdinal.{z}))
    {F : MvPolynomial ι K} {n : ℕ} (hF : IsWeightedHomogeneous wt F n) :
    aeval x F ∈ A (n : NatOrdinal.{z}) :=
  OrdinalGraded.aeval_mem_of_forall_mem hmem
    ((isWeightedHomogeneous_natCast_comp_iff wt).mpr hF)

/-- Evaluation at homogeneous `x i ∈ A_{wt i}` is graded: the degree-`n` component of `F(x)` is
the evaluation of the degree-`n` component of `F`. -/
theorem decompose_aeval (hmem : ∀ i, x i ∈ A (wt i : NatOrdinal.{z})) (F : MvPolynomial ι K)
    (n : ℕ) :
    (DirectSum.decompose A (aeval x F) (n : NatOrdinal.{z}) : R) =
      aeval x (weightedHomogeneousComponent wt n F) := by
  rw [OrdinalGraded.decompose_aeval hmem F (n : NatOrdinal.{z}),
    weightedHomogeneousComponent_natCast_comp]

/-- Homogeneous generators from a generation hypothesis by arbitrary polynomials: the homogeneous
component of the right degree still evaluates to a given homogeneous element. -/
theorem IsHomogeneousCoordinates.of_surjective (one_le : ∀ i, 1 ≤ wt i)
    (hmem : ∀ i, x i ∈ A (wt i : NatOrdinal.{z}))
    (independent : ∀ (n : ℕ) (c : ι →₀ K), (∀ i ∈ c.support, wt i = n) →
      Finsupp.linearCombination K x c ∈ decomposable A n → c = 0)
    (surj : ∀ (n : ℕ), ∀ y ∈ A (n : NatOrdinal.{z}), ∃ F : MvPolynomial ι K, aeval x F = y) :
    IsHomogeneousCoordinates A wt x where
  one_le := one_le
  mem := hmem
  independent := independent
  surj n y hy := by
    obtain ⟨F, hF⟩ := surj n y hy
    refine ⟨weightedHomogeneousComponent wt n F,
      weightedHomogeneousComponent_isWeightedHomogeneous (w := wt) (n := n) (φ := F), ?_⟩
    rw [← decompose_aeval hmem, hF, DirectSum.decompose_of_mem_same A hy]

variable (A wt x) in
/-- The paper's minimal system of homogeneous generators of `A_{<ω}`: a family `x i ∈ A_{wt i}` of
homogeneous elements of positive degree `wt i ≥ 1` whose image in `(A_{<ω})₊/(A_{<ω})₊²` is an
`K`-basis; equivalently, for each `n ≥ 1` the `x i` of degree `n` form a basis of a complement of
`(A_{<ω})₊² ∩ A_n = ∑_{i+k=n, i,k ≥ 1} A_i A_k` in `A_n` — they are linearly independent modulo
`(A_{<ω})₊² ∩ A_n` and span `A_n` modulo it. -/
structure IsMinimalSystem : Prop where
  /-- Every generator has positive degree. -/
  one_le : ∀ i, 1 ≤ wt i
  /-- `x i` is homogeneous of degree `wt i`. -/
  mem : ∀ i, x i ∈ A (wt i : NatOrdinal.{z})
  /-- The generators of degree `n` are linearly independent modulo `(A_{<ω})₊² ∩ A_n`. -/
  independent : ∀ (n : ℕ) (c : ι →₀ K), (∀ i ∈ c.support, wt i = n) →
    Finsupp.linearCombination K x c ∈ decomposable A n → c = 0
  /-- The generators of degree `n` span `A_n` modulo `(A_{<ω})₊² ∩ A_n`, for `n ≥ 1`. -/
  spans : ∀ n : ℕ, 1 ≤ n → ∀ y ∈ A (n : NatOrdinal.{z}), ∃ c : ι →₀ K,
    (∀ i ∈ c.support, wt i = n) ∧ y - Finsupp.linearCombination K x c ∈ decomposable A n

/-- A minimal system generates `A_{<ω}`: evaluation is onto each `A_n`, by induction on `n`, using
`A_0 = K` in degree zero. -/
theorem IsMinimalSystem.isHomogeneousCoordinates (h0 : GradeZeroScalars A)
    (hx : IsMinimalSystem A wt x) :
    IsHomogeneousCoordinates A wt x := by
  refine IsHomogeneousCoordinates.of_surjective hx.one_le hx.mem hx.independent ?_
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hy
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨e, rfl⟩ := (gradeZeroScalars_iff A).mp h0 y (by rwa [Nat.cast_zero] at hy)
    exact ⟨C e, aeval_C x e⟩
  · obtain ⟨c, -, hc⟩ := hx.spans n hn y hy
    have hD : decomposable A n ≤
        Subalgebra.toSubmodule (aeval x : MvPolynomial ι K →ₐ[K] R).range := by
      refine decomposable_le A fun i j hi hj hij ↦ Submodule.mul_le.mpr fun a ha b hb ↦ ?_
      obtain ⟨F, hF⟩ := ih i (by omega) a ha
      obtain ⟨G, hG⟩ := ih j (by omega) b hb
      exact (Subalgebra.mem_toSubmodule _).mpr ((AlgHom.mem_range _).mpr
        ⟨F * G, by rw [map_mul, hF, hG]⟩)
    obtain ⟨G, hG⟩ := (AlgHom.mem_range _).mp ((Subalgebra.mem_toSubmodule _).mp (hD hc))
    have hlc : aeval x (Finsupp.linearCombination K (X : ι → MvPolynomial ι K) c) =
        Finsupp.linearCombination K x c := by
      rw [← AlgHom.toLinearMap_apply, Finsupp.apply_linearCombination]
      congr 2
      funext i
      exact aeval_X x i
    exact ⟨G + Finsupp.linearCombination K (X : ι → MvPolynomial ι K) c,
      by rw [map_add, hG, hlc, sub_add_cancel]⟩

/-- A polynomial homogeneous of degree `n ≥ 1` evaluates at homogeneous generators of positive
degrees to its linear part in the degree-`n` variables plus an element of `(A_{<ω})₊² ∩ A_n`; the
linear coefficients are read off the polynomial. -/
theorem exists_linear_part (hwt : ∀ i, 1 ≤ wt i) (hmem : ∀ i, x i ∈ A (wt i : NatOrdinal.{z}))
    {F : MvPolynomial ι K} {n : ℕ} (hn : 1 ≤ n) (hF : IsWeightedHomogeneous wt F n) :
    ∃ c : ι →₀ K, (∀ i ∈ c.support, wt i = n) ∧
      aeval x F - Finsupp.linearCombination K x c ∈ decomposable A n ∧
      ∀ i, c i = F.coeff (Finsupp.single i 1) := by
  obtain ⟨c, hcwt, hc, hcoeff⟩ := OrdinalGraded.exists_linear_part
    (fun i ↦ Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (hwt i))) hmem
    (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn))
    ((isWeightedHomogeneous_natCast_comp_iff wt).mpr hF)
  refine ⟨c, fun i hi ↦ Nat.cast_injective (hcwt i hi), ?_, hcoeff⟩
  rwa [decomposableAt_natCast] at hc

namespace IsHomogeneousCoordinates

variable (hx : IsHomogeneousCoordinates A wt x)
include hx

/-- Evaluation of a polynomial homogeneous of degree `n` lands in `A_n`. -/
theorem aeval_mem {F : MvPolynomial ι K} {n : ℕ} (hF : IsWeightedHomogeneous wt F n) :
    aeval x F ∈ A (n : NatOrdinal.{z}) :=
  aeval_mem_of_forall_mem hx.mem hF

/-! ### The chain rule for `∂` -/

variable {Δ : Derivation K R (Germ l R)} (hΔ : IsLoweringDerivation A Δ)
include hΔ

omit hx in
theorem map_algebraMap (e : K) : Δ (algebraMap K R e) = 0 :=
  hΔ.eq_zero (by rw [NatOrdinal.constantCoeff_zero]) (SetLike.algebraMap_mem_graded A e)

omit hx in
/-- The chain rule: if `∂(x i)` is represented by `γ ↦ (g i γ)(x)`, then `∂(F(x))` is represented
by `γ ↦ (∂_γ F)(x)`, where `∂_γ = ∑ g i γ ∂/∂X_i` (Lean `mkDerivation K (fun i ↦ g i γ)`). -/
theorem map_aeval (g : ι → T → MvPolynomial ι K)
    (hg : ∀ i, Δ (x i) = ((fun γ ↦ aeval x (g i γ)) : Germ l R)) (F : MvPolynomial ι K) :
    Δ (aeval x F) = ((fun γ ↦ aeval x (mkDerivation K (fun i ↦ g i γ) F)) : Germ l R) := by
  induction F using MvPolynomial.induction_on with
  | C e =>
    rw [aeval_C, map_algebraMap hΔ]
    have : ∀ γ, aeval x (mkDerivation K (fun i ↦ g i γ) (C e)) = 0 := fun γ ↦ by
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero]
    simp only [this]
    rfl
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]
    simp only [map_add]
    rfl
  | mul_X p i hp =>
    rw [map_mul, aeval_X, derivation_leibniz, hp, hg i]
    have : ∀ γ, aeval x (mkDerivation K (fun i ↦ g i γ) (p * X i)) =
        aeval x (mkDerivation K (fun i ↦ g i γ) p) * x i + aeval x p * aeval x (g i γ) := fun γ ↦ by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mkDerivation_X, map_add, map_mul, map_mul,
        aeval_X, add_comm, mul_comm (x i)]
    simp only [this]
    rfl

omit [GradedAlgebra A] in
/-- Polynomial representatives of `∂(x i)`, the paper's `G_B(γ)`: polynomials `g i γ` homogeneous
of degree `wt i - 1` with `γ ↦ (g i γ)(x)` representing `∂(x i)`. -/
theorem exists_lifts : ∃ g : ι → T → MvPolynomial ι K,
    (∀ i γ, IsWeightedHomogeneous wt (g i γ) (wt i - 1)) ∧
      ∀ i, Δ (x i) = ((fun γ ↦ aeval x (g i γ)) : Germ l R) := by
  have hrep : ∀ i, ∃ f : T → R, (∀ γ, f γ ∈ A ((wt i - 1 : ℕ) : NatOrdinal.{z})) ∧
      Δ (x i) = (f : Germ l R) := fun i ↦
    exists_rep_of_mem_germSubmodule _ (hΔ.mem_lower_natCast (hx.one_le i) (hx.mem i))
  choose f hf hfΔ using hrep
  choose g hg hgf using fun i γ ↦ hx.surj (wt i - 1) (f i γ) (hf i γ)
  refine ⟨g, hg, fun i ↦ ?_⟩
  rw [hfΔ i]
  congr 1
  funext γ
  exact (hgf i γ).symm

end IsHomogeneousCoordinates

/-! ### The kernel of the pointwise derivations -/

variable {Δ : Derivation K R (Germ l R)}

omit [GradedAlgebra A] in
/-- Polynomials homogeneous of degree zero (for `deg X_i = wt i ≥ 1`) are constants. -/
theorem eq_C_of_isWeightedHomogeneous_zero (hwt : ∀ i, 1 ≤ wt i) {p : MvPolynomial ι K}
    (hp : IsWeightedHomogeneous wt p 0) : p = C (p.coeff 0) :=
  OrdinalGraded.eq_C_of_isWeightedHomogeneous_zero (wt := fun i ↦ (wt i : NatOrdinal.{0}))
    (fun i ↦ Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (hwt i)))
    ((isWeightedHomogeneous_natCast_comp_iff (M := NatOrdinal.{0}) wt).mpr hp)

/-- The joint-kernel lemma: no non-zero polynomial homogeneous of positive degree satisfies
`∂_γ F = 0` for all `γ < 0` sufficiently close to `0`, for homogeneous generators of positive
degrees independent modulo the decomposables. Induction on the degree: write a putative kernel
element `F = ∑ c_d X₀^d` in a variable `X₀` of maximal degree and compare the coefficients of
`X₀^D` and `X₀^(D-1)` in `∂_γ F`. The leading coefficient `c_D` is a kernel element of smaller
degree, hence a scalar `a`, and the next coefficient combines with `D·a·X₀` into a polynomial `h`
homogeneous of degree `deg X₀` with `∂(h(x)) = 0`; injectivity of `∂` and independence modulo the
decomposables force `D a = 0`. -/
theorem eq_zero_of_eventually_mkDerivation_eq_zero [CharZero K] (hwt : ∀ i, 1 ≤ wt i)
    (hmem : ∀ i, x i ∈ A (wt i : NatOrdinal.{z}))
    (hind : ∀ (n : ℕ) (c : ι →₀ K), (∀ i ∈ c.support, wt i = n) →
      Finsupp.linearCombination K x c ∈ decomposable A n → c = 0)
    (hΔ : IsLoweringDerivation A Δ) (g : ι → T → MvPolynomial ι K)
    (hghom : ∀ i γ, IsWeightedHomogeneous wt (g i γ) (wt i - 1))
    (hg : ∀ i, Δ (x i) = ((fun γ ↦ aeval x (g i γ)) : Germ l R)) (w : ℕ) :
    ∀ F : MvPolynomial ι K, 1 ≤ w → IsWeightedHomogeneous wt F w →
      (∀ᶠ γ in l, mkDerivation K (fun i ↦ g i γ) F = 0) → F = 0 := by
  classical
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro F hw hF hD
  by_contra hF0
  -- a variable `X x₀` of maximal degree `wt x₀`; `F` has positive degree `D` in `X x₀`
  have hvars : F.vars.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, vars_eq_empty_iff_eq_C]
    intro hC
    exact hF0 (by rw [hC, hF.coeff_eq_zero 0 (by rw [map_zero]; omega), map_zero])
  obtain ⟨x₀, hx₀, hmax⟩ := F.vars.exists_max_image wt hvars
  have hn1 : 1 ≤ wt x₀ := hwt x₀
  set D := F.degreeOf x₀ with hDdef
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (mem_vars_iff_degreeOf_ne_zero.mp hx₀)
  -- write `F = ∑ c_d (X x₀)^d`
  set c : ℕ → MvPolynomial ι K := fun d ↦ xCoeff x₀ d F with hc
  have hexp : F = ∑ d ∈ Finset.range (D + 1), c d * X x₀ ^ d := (sum_xCoeff_mul_X_pow x₀ F).symm
  have hcD : c D ≠ 0 := xCoeff_degreeOf_ne_zero x₀ hF0
  have hcD1 : c (D + 1) = 0 := xCoeff_eq_zero_of_degreeOf_lt x₀ (Nat.lt_succ_self D)
  have hchom : ∀ d, IsWeightedHomogeneous wt (c d) (w - d * wt x₀) := fun d ↦
    xCoeff_isWeightedHomogeneous wt x₀ hF d
  have hcsupp : ∀ d, c d ∈ supported K {x₀}ᶜ := fun d ↦ xCoeff_mem_supported x₀ d F
  have hgsupp : ∀ γ, g x₀ γ ∈ supported K {x₀}ᶜ := fun γ ↦
    (hghom x₀ γ).mem_supported_of_lt wt (by omega)
  have hDsupp : ∀ γ d, mkDerivation K (fun i ↦ g i γ) (c d) ∈ supported K {x₀}ᶜ := fun γ d ↦
    mkDerivation_mem_supported wt hwt _ (fun i ↦ hghom i γ) (hcsupp d) fun i hi ↦
      hmax i (vars_xCoeff_subset x₀ d F hi)
  -- `∂_γ F = ∑_d (∂_γ c_d + (d + 1) c_(d+1) g_(x₀)) (X x₀)^d`; compare coefficients
  set q : T → ℕ → MvPolynomial ι K := fun γ d ↦ mkDerivation K (fun i ↦ g i γ) (c d) +
    ((d + 1 : ℕ) : MvPolynomial ι K) * (c (d + 1) * g x₀ γ) with hq
  have hqsupp : ∀ γ d, q γ d ∈ supported K {x₀}ᶜ := fun γ d ↦
    add_mem (hDsupp γ d) (mul_mem (Subalgebra.natCast_mem _ _) (mul_mem (hcsupp _) (hgsupp γ)))
  have hDexp : ∀ γ, mkDerivation K (fun i ↦ g i γ) F =
      ∑ d ∈ Finset.range (D + 1), q γ d * X x₀ ^ d := by
    intro γ
    have hterm : ∀ d, mkDerivation K (fun i ↦ g i γ) (c d * X x₀ ^ d) =
        mkDerivation K (fun i ↦ g i γ) (c d) * X x₀ ^ d +
          (d : MvPolynomial ι K) * (c d * g x₀ γ) * X x₀ ^ (d - 1) := fun d ↦ by
      rw [Derivation.leibniz, Derivation.leibniz_pow, mkDerivation_X]
      simp only [smul_eq_mul, nsmul_eq_mul]
      ring
    conv_lhs => rw [hexp, map_sum, Finset.sum_congr rfl fun d _ ↦ hterm d, Finset.sum_add_distrib]
    simp only [hq, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [Nat.cast_zero, zero_mul, add_zero, hcD1, mul_zero, Nat.add_sub_cancel]
  have hcoeff : ∀ γ, mkDerivation K (fun i ↦ g i γ) F = 0 → ∀ d ≤ D, q γ d = 0 := by
    intro γ hγ d hd
    have := xCoeff_sum_mul_X_pow x₀ (Finset.range (D + 1)) (q := q γ) (fun d _ ↦ hqsupp γ d) d
    rwa [← hDexp γ, hγ, map_zero, ite_eq_left (Finset.mem_range.mpr (by omega)), eq_comm] at this
  -- the coefficient of `(X x₀)^D`: `∂_γ c_D = 0`, so `c_D` is a non-zero scalar `a`
  have hcD0 : ∀ᶠ γ in l, mkDerivation K (fun i ↦ g i γ) (c D) = 0 :=
    hD.mono fun γ hγ ↦ by simpa [hq, hcD1] using hcoeff γ hγ D le_rfl
  have hwD : w = D * wt x₀ := by
    by_contra hne
    have hle := le_of_xCoeff_ne_zero wt x₀ hF hcD
    have hpos : 0 < D * wt x₀ := Nat.mul_pos hD1 hn1
    exact hcD (ih _ (by omega) (c D) (by omega) (hchom D) hcD0)
  have hw0 : w - D * wt x₀ = 0 := by omega
  set a := (c D).coeff 0 with ha
  have hcDa : c D = C a := eq_C_of_isWeightedHomogeneous_zero hwt (hw0 ▸ hchom D)
  have ha0 : a ≠ 0 := fun h ↦ hcD (by rw [hcDa, h, map_zero])
  -- the coefficient of `(X x₀)^(D-1)`: `h := c_(D-1) + D a X x₀` has degree `wt x₀`, `∂_γ h = 0`
  set h : MvPolynomial ι K := c (D - 1) + C ((D : K) * a) * X x₀ with hh
  have hhhom : IsWeightedHomogeneous wt h (wt x₀) := by
    refine IsWeightedHomogeneous.add ?_ ?_
    · have := hchom (D - 1)
      have hw' : w - (D - 1) * wt x₀ = wt x₀ := by
        rw [hwD]
        have : D * wt x₀ = (D - 1) * wt x₀ + wt x₀ := by
          conv_lhs => rw [← Nat.sub_add_cancel hD1]
          ring
        omega
      rwa [hw'] at this
    · have := (isWeightedHomogeneous_C wt ((D : K) * a)).mul (isWeightedHomogeneous_X K wt x₀)
      rwa [zero_add] at this
  have hDh : ∀ γ, mkDerivation K (fun i ↦ g i γ) h = q γ (D - 1) := by
    intro γ
    rw [hh, hq]
    simp only [Nat.sub_add_cancel hD1, hcDa]
    rw [map_add, ← smul_eq_C_mul, Derivation.map_smul, mkDerivation_X, smul_eq_C_mul, map_mul,
      map_natCast]
    ring
  have hh0 : ∀ᶠ γ in l, mkDerivation K (fun i ↦ g i γ) h = 0 :=
    hD.mono fun γ hγ ↦ by rw [hDh]; exact hcoeff γ hγ (D - 1) (Nat.sub_le D 1)
  -- `∂(h(x)) = 0`, hence `h(x) = 0`, and the linear part of `h` in the variables of degree
  -- `wt x₀` vanishes: `D a = 0`
  have hΔh : Δ (aeval x h) = 0 := by
    rw [IsHomogeneousCoordinates.map_aeval hΔ g hg h]
    change _ = ((fun _ ↦ (0 : R) : T → R) : Germ l R)
    rw [Filter.Germ.coe_eq]
    exact hh0.mono fun γ hγ ↦ by
      change aeval x (mkDerivation K (fun i ↦ g i γ) h) = 0
      rw [hγ, map_zero]
  have haeval : aeval x h = 0 :=
    hΔ.injective (IsLoweringDerivation.natCast_constantCoeff_pos (wt x₀) hn1)
      (aeval_mem_of_forall_mem hmem hhhom) hΔh
  obtain ⟨cf, hcfw, hcf, hcfcoeff⟩ := exists_linear_part hwt hmem hn1 hhhom
  rw [haeval, zero_sub, neg_mem_iff] at hcf
  have hcx := hcfcoeff x₀
  rw [hind (wt x₀) cf hcfw hcf, Finsupp.coe_zero, Pi.zero_apply, hh, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, hc, coeff_xCoeff,
    ite_eq_right (by simp), zero_add, C_mul_X_eq_monomial, coeff_monomial, ite_eq_left rfl] at hcx
  exact ha0 ((mul_eq_zero.mp hcx.symm).resolve_left (Nat.cast_ne_zero.mpr (by omega)))

/-! ### Algebraic independence -/

namespace IsHomogeneousCoordinates

variable [CharZero K] (hx : IsHomogeneousCoordinates A wt x) (hΔ : IsLoweringDerivation A Δ)
include hx hΔ

/-- No non-zero polynomial homogeneous of degree `w` vanishes at the generators: induction on
`w`; by the chain rule, a relation of degree `w` has as `∂`-derivative a family of relations of
degree `w - 1`, which vanish by induction, so the relation lies in the joint kernel and
vanishes. -/
theorem eq_zero_of_aeval_eq_zero_of_isWeightedHomogeneous [Nontrivial R] (w : ℕ) :
    ∀ F : MvPolynomial ι K, IsWeightedHomogeneous wt F w → aeval x F = 0 → F = 0 := by
  classical
  obtain ⟨g, hghom, hg⟩ := hx.exists_lifts hΔ
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro F hF hF0
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [eq_C_of_isWeightedHomogeneous_zero hx.one_le hF] at hF0 ⊢
    rw [aeval_C] at hF0
    rw [(algebraMap K R).injective (hF0.trans (map_zero _).symm), map_zero]
  · refine eq_zero_of_eventually_mkDerivation_eq_zero hx.one_le hx.mem hx.independent hΔ g hghom
      hg w F hw hF ?_
    have h1 := map_aeval hΔ g hg F
    rw [hF0, map_zero] at h1
    change ((fun _ ↦ (0 : R) : T → R) : Germ l R) = _ at h1
    rw [Filter.Germ.coe_eq] at h1
    refine h1.mono fun γ hγ ↦ ?_
    exact ih (w - 1) (by omega) _ (mkDerivation_isWeightedHomogeneous wt _ (fun i ↦ hghom i γ)
      hx.one_le hF) hγ.symm

/-- The homogeneous generators are algebraically independent: evaluation `K[X_B : B ∈ 𝓑] → A`
is injective. -/
theorem aeval_injective [Nontrivial R] :
    Function.Injective (aeval x : MvPolynomial ι K →ₐ[K] R) := by
  apply OrdinalGraded.aeval_injective_of_forall_injectiveAt hx.mem
  intro β
  rw [OrdinalGraded.injectiveAt_iff]
  intro F hF hF0
  by_cases hzero : F = 0
  · exact hzero
  obtain ⟨n, hn⟩ := hF.exists_degree_eq_natCast hzero
  subst β
  exact hx.eq_zero_of_aeval_eq_zero_of_isWeightedHomogeneous hΔ n F
    ((isWeightedHomogeneous_natCast_comp_iff wt).mp hF) hF0

end IsHomogeneousCoordinates


end GermPolynomial
