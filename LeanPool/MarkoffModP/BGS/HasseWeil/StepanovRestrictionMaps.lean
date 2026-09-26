/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointIncrement
public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointStepanovGrid
public import LeanPool.MarkoffModP.BGS.HasseWeil.StepanovLinearAlgebra
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic

/-!
# Stepanov restriction maps on a finite coefficient grid

For finite families `f : α → L` and `g : β → L`, the coefficient space is
the free `K`-module `(α × β →₀ K)`.  Its two restriction maps evaluate the
same coefficient grid against

* `f i * (g j) ^ s`, and
* `(f i) ^ s * g j`.

The maps are defined with `Finsupp.linearCombination`.  One-point pole bounds
give codomain restrictions with budgets `ell + s * m` and `s * ell + m`.
The final results expose exactly the injectivity and finrank interfaces used
by `exists_auxiliary_of_finrank_lt`.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial BigOperators

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance stepanovRestrictionConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance stepanovRestrictionConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The first Stepanov restriction: evaluate the coefficient grid against
`f i * (g j) ^ s`. -/
def onePointStepanovFirstRestrictionMap
    {α β : Type*} (f : α → L) (g : β → L) (s : ℕ) :
    (α × β →₀ K) →ₗ[K] L :=
  Finsupp.linearCombination K
    (fun ij : α × β => f ij.1 * (g ij.2) ^ s)

/-- The second Stepanov restriction: evaluate the coefficient grid against
`(f i) ^ s * g j`. -/
def onePointStepanovSecondRestrictionMap
    {α β : Type*} (f : α → L) (g : β → L) (s : ℕ) :
    (α × β →₀ K) →ₗ[K] L :=
  Finsupp.linearCombination K
    (fun ij : α × β => (f ij.1) ^ s * g ij.2)

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem onePointStepanovFirstRestrictionMap_single
    {α β : Type*} (f : α → L) (g : β → L) (s : ℕ)
    (ij : α × β) (c : K) :
    onePointStepanovFirstRestrictionMap K L f g s
        (Finsupp.single ij c) =
      c • (f ij.1 * (g ij.2) ^ s) := by
  simp [onePointStepanovFirstRestrictionMap]

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem onePointStepanovSecondRestrictionMap_single
    {α β : Type*} (f : α → L) (g : β → L) (s : ℕ)
    (ij : α × β) (c : K) :
    onePointStepanovSecondRestrictionMap K L f g s
        (Finsupp.single ij c) =
      c • ((f ij.1) ^ s * g ij.2) := by
  simp [onePointStepanovSecondRestrictionMap]

/-- Powers multiply a one-point pole budget. -/
theorem finiteExtensionOnePointRiemannSpace_pow_mem
    (P : FiniteExtensionPlace K L) {m : ℕ} {x : L}
    (hx : x ∈ finiteExtensionOnePointRiemannSpace K L P m)
    (s : ℕ) :
    x ^ s ∈ finiteExtensionOnePointRiemannSpace K L P (s * m) := by
  classical
  change x ^ s ∈ finiteExtensionRiemannSpace K L
    (Finsupp.single P ((s * m : ℕ) : ℤ))
  have hpow := finiteExtensionRiemannSpace_pow_mem K L hx s
  have hdivisor :
      s • Finsupp.single P (m : ℤ) =
        Finsupp.single P ((s * m : ℕ) : ℤ) := by
    ext v
    by_cases hv : v = P
    · subst v
      simp
    · simp [Finsupp.single_eq_of_ne hv]
  rw [← hdivisor]
  exact hpow

/-- Every basis value of the first restriction has pole budget
`ell + s * m`. -/
theorem onePointStepanovFirstGrid_mem
    {α β : Type*} (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (ell m s : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace K L P m)
    (ij : α × β) :
    f ij.1 * (g ij.2) ^ s ∈
      finiteExtensionOnePointRiemannSpace K L P (ell + s * m) := by
  exact finiteExtensionOnePointRiemannSpace_mul_mem K L P
    (hf ij.1)
    (finiteExtensionOnePointRiemannSpace_pow_mem K L P (hg ij.2) s)

/-- Every basis value of the second restriction has pole budget
`s * ell + m`. -/
theorem onePointStepanovSecondGrid_mem
    {α β : Type*} (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (ell m s : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace K L P m)
    (ij : α × β) :
    (f ij.1) ^ s * g ij.2 ∈
      finiteExtensionOnePointRiemannSpace K L P (s * ell + m) := by
  exact finiteExtensionOnePointRiemannSpace_mul_mem K L P
    (finiteExtensionOnePointRiemannSpace_pow_mem K L P (hf ij.1) s)
    (hg ij.2)

/-- The whole first linear combination has pole budget `ell + s * m`. -/
theorem onePointStepanovFirstRestrictionMap_mem
    {α β : Type*} (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (ell m s : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace K L P m)
    (c : α × β →₀ K) :
    onePointStepanovFirstRestrictionMap K L f g s c ∈
      finiteExtensionOnePointRiemannSpace K L P (ell + s * m) := by
  rw [onePointStepanovFirstRestrictionMap,
    Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro ij hij
  exact (finiteExtensionOnePointRiemannSpace K L P (ell + s * m)).smul_mem
    (c ij) (onePointStepanovFirstGrid_mem K L P f g ell m s hf hg ij)

/-- The whole second linear combination has pole budget `s * ell + m`. -/
theorem onePointStepanovSecondRestrictionMap_mem
    {α β : Type*} (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (ell m s : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace K L P m)
    (c : α × β →₀ K) :
    onePointStepanovSecondRestrictionMap K L f g s c ∈
      finiteExtensionOnePointRiemannSpace K L P (s * ell + m) := by
  rw [onePointStepanovSecondRestrictionMap,
    Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro ij hij
  exact (finiteExtensionOnePointRiemannSpace K L P (s * ell + m)).smul_mem
    (c ij) (onePointStepanovSecondGrid_mem K L P f g ell m s hf hg ij)

/-- The first restriction with its one-point codomain made explicit. -/
def onePointStepanovFirstCodRestrictionMap
    {α β : Type*} (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (ell m s : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace K L P m) :
    (α × β →₀ K) →ₗ[K]
      finiteExtensionOnePointRiemannSpace K L P (ell + s * m) :=
  LinearMap.codRestrict _
    (onePointStepanovFirstRestrictionMap K L f g s)
    (onePointStepanovFirstRestrictionMap_mem K L P f g ell m s hf hg)

/-- The second restriction with its one-point codomain made explicit. -/
def onePointStepanovSecondCodRestrictionMap
    {α β : Type*} (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (ell m s : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace K L P m) :
    (α × β →₀ K) →ₗ[K]
      finiteExtensionOnePointRiemannSpace K L P (s * ell + m) :=
  LinearMap.codRestrict _
    (onePointStepanovSecondRestrictionMap K L f g s)
    (onePointStepanovSecondRestrictionMap_mem K L P f g ell m s hf hg)

@[simp]
theorem onePointStepanovFirstCodRestrictionMap_coe
    {α β : Type*} (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (ell m s : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace K L P m)
    (c : α × β →₀ K) :
    ((onePointStepanovFirstCodRestrictionMap K L P f g ell m s hf hg c :
      finiteExtensionOnePointRiemannSpace K L P (ell + s * m)) : L) =
        onePointStepanovFirstRestrictionMap K L f g s c := by
  rfl

@[simp]
theorem onePointStepanovSecondCodRestrictionMap_coe
    {α β : Type*} (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (ell m s : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace K L P m)
    (c : α × β →₀ K) :
    ((onePointStepanovSecondCodRestrictionMap K L P f g ell m s hf hg c :
      finiteExtensionOnePointRiemannSpace K L P (s * ell + m)) : L) =
        onePointStepanovSecondRestrictionMap K L f g s c := by
  rfl

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- Linear independence of the first product grid is exactly injectivity of
the first restriction map. -/
theorem onePointStepanovFirstRestrictionMap_injective_of_linearIndependent
    {α β : Type*} (f : α → L) (g : β → L) (s : ℕ)
    (hLI : LinearIndependent K
      (fun ij : α × β => f ij.1 * (g ij.2) ^ s)) :
    Function.Injective (onePointStepanovFirstRestrictionMap K L f g s) := by
  intro c d hcd
  apply sub_eq_zero.mp
  apply (linearIndependent_iff.mp hLI)
  change onePointStepanovFirstRestrictionMap K L f g s (c - d) = 0
  rw [map_sub, hcd, sub_self]

omit [DecidableEq K] in
/-- The mixed-order Stepanov-grid criterion proves injectivity of the first
restriction. -/
theorem onePointStepanovFirstRestrictionMap_injective_of_grid
    {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (d : α → ℕ) (e : β → ℕ) (s : ℕ)
    (hf : ∀ i, f i ≠ 0) (hg : ∀ j, g j ≠ 0)
    (hfOrder : ∀ i, finiteExtensionPrincipalDivisor K L (f i) P =
      -(d i : ℤ))
    (hgOrder : ∀ j, finiteExtensionPrincipalDivisor K L (g j) P =
      -(e j : ℤ))
    (hd : Function.Injective d) (he : Function.Injective e)
    (hdigit : ∀ i, d i < s) :
    Function.Injective (onePointStepanovFirstRestrictionMap K L f g s) := by
  apply onePointStepanovFirstRestrictionMap_injective_of_linearIndependent
  exact onePointStepanovGrid_linearIndependent K L P f g d e s
    hf hg hfOrder hgOrder hd he hdigit

/-- The first codomain restriction remains injective. -/
theorem onePointStepanovFirstCodRestrictionMap_injective_of_linearIndependent
    {α β : Type*} (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (ell m s : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace K L P m)
    (hLI : LinearIndependent K
      (fun ij : α × β => f ij.1 * (g ij.2) ^ s)) :
    Function.Injective
      (onePointStepanovFirstCodRestrictionMap K L P f g ell m s hf hg) := by
  intro c d hcd
  apply onePointStepanovFirstRestrictionMap_injective_of_linearIndependent
    K L f g s hLI
  exact congrArg Subtype.val hcd

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- The coefficient space has dimension equal to the cardinality of its
finite product index. -/
@[simp]
theorem onePointStepanovCoefficientSpace_finrank
    {α β : Type*} [Fintype α] [Fintype β] :
    Module.finrank K (α × β →₀ K) =
      Fintype.card α * Fintype.card β := by
  rw [Module.finrank_finsupp_self, Fintype.card_prod]

/-- A target finrank upper bound and a numerical strict inequality give the
dimension inequality required by rank-nullity. -/
theorem onePointStepanovTarget_finrank_lt_coefficientSpace
    {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteExtensionPlace K L) (n targetBound : ℕ)
    (hupper : Module.finrank K
      (finiteExtensionOnePointRiemannSpace K L P n) ≤ targetBound)
    (hnumeric : targetBound < Fintype.card α * Fintype.card β) :
    Module.finrank K (finiteExtensionOnePointRiemannSpace K L P n) <
      Module.finrank K (α × β →₀ K) := by
  rw [onePointStepanovCoefficientSpace_finrank K]
  exact hupper.trans_lt hnumeric

/-- Concrete rank-nullity interface for the two Stepanov restrictions.

An upper bound for the second one-point target, strictly below the product
index cardinality, produces a nonzero coefficient grid killed by the second
restriction and detected by the first. -/
theorem exists_onePointStepanovAuxiliary_of_target_finrank_upper
    {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteExtensionPlace K L)
    (f : α → L) (g : β → L) (ell m s targetBound : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace K L P m)
    (hLI : LinearIndependent K
      (fun ij : α × β => f ij.1 * (g ij.2) ^ s))
    (hupper : Module.finrank K
      (finiteExtensionOnePointRiemannSpace K L P (s * ell + m)) ≤
        targetBound)
    (hnumeric : targetBound < Fintype.card α * Fintype.card β) :
    ∃ c : α × β →₀ K,
      c ≠ 0 ∧
      onePointStepanovSecondCodRestrictionMap K L P f g ell m s hf hg c = 0 ∧
      onePointStepanovFirstRestrictionMap K L f g s c ≠ 0 := by
  let : Module.Finite K
      (finiteExtensionOnePointRiemannSpace K L P (s * ell + m)) :=
    finiteExtensionOnePointRiemannSpace_moduleFinite K L P _
  apply exists_auxiliary_of_finrank_lt
    (onePointStepanovFirstRestrictionMap K L f g s)
    (onePointStepanovSecondCodRestrictionMap K L P f g ell m s hf hg)
  · exact onePointStepanovFirstRestrictionMap_injective_of_linearIndependent
      K L f g s hLI
  · exact onePointStepanovTarget_finrank_lt_coefficientSpace
      K L P (s * ell + m) targetBound hupper hnumeric

end

end BGS.HasseWeil
