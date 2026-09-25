/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.CechRiemannLinearAlgebra
public import LeanPool.MarkoffModP.BGS.HasseWeil.LocalPoleFiltration
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite principal parts

This file assembles the one-place calculation in `LocalPoleFiltration` over a
finite family of discrete valuation rings.  At one place the principal parts
of order at most `n` are the genuine quotient

`localPoleSpace π n / localPoleSpace π 0`.

The filtration by pole order proves that its dimension is `n` times the
residue-field degree.  Taking a finite product therefore has dimension the
weighted degree of the chosen pole bounds.

The last section constructs the diagonal principal-parts map on any global
subspace satisfying those pole bounds.  Its kernel is exactly the subspace
regular at every chosen place.  Thus, once the all-place function-field layer
identifies that regular subspace with the constants, the quotient by constants
embeds in this finite-dimensional principal-parts space.
-/

@[expose] public section

namespace BGS.HasseWeil

open Submodule
open scoped nonZeroDivisors

noncomputable section

section OnePlace

variable {K R L : Type*} [Field K] [CommRing R]
  [IsDedekindDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra K R] [Algebra R L] [Algebra K L]
  [IsScalarTower K R L] [IsFractionRing R L]

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] [IsFractionRing R L] in
/-- Monotonicity of the local pole filtration for an arbitrary increase in
the allowed pole order. -/
theorem localPoleSpace_mono_of_le (π : R) {m n : ℕ} (hmn : m ≤ n) :
    localPoleSpace (K := K) (L := L) π m ≤
      localPoleSpace (K := K) (L := L) π n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
      exact ih.trans (by simpa [Nat.succ_eq_add_one] using
        localPoleSpace_mono (K := K) (L := L) π n)

/-- Principal parts of order at most `n` at one DVR. -/
abbrev localPrincipalPartSpace (π : R) (n : ℕ) :=
  localPoleSpace (K := K) (L := L) π n ⧸
    relativeSubmodule
      (localPoleSpace (K := K) (L := L) π 0)
      (localPoleSpace (K := K) (L := L) π n)

/-- The last graded layer in the local pole filtration. -/
abbrev localPrincipalPartLayer (π : R) (n : ℕ) :=
  localPoleSpace (K := K) (L := L) π (n + 1) ⧸
    relativeSubmodule
      (localPoleSpace (K := K) (L := L) π n)
      (localPoleSpace (K := K) (L := L) π (n + 1))

/-- Enlarging the pole bound by one gives an inclusion of principal-part
spaces. -/
def localPrincipalPartInclusion (π : R) (n : ℕ) :
    localPrincipalPartSpace (K := K) (L := L) π n →ₗ[K]
      localPrincipalPartSpace (K := K) (L := L) π (n + 1) := by
  let hnn : localPoleSpace (K := K) (L := L) π n ≤
      localPoleSpace (K := K) (L := L) π (n + 1) :=
    localPoleSpace_mono (K := K) (L := L) π n
  let inclusion : localPoleSpace (K := K) (L := L) π n →ₗ[K]
      localPoleSpace (K := K) (L := L) π (n + 1) :=
    Submodule.inclusion hnn
  exact (Submodule.comap
      (localPoleSpace (K := K) (L := L) π n).subtype
      (localPoleSpace (K := K) (L := L) π 0)).mapQ
    (Submodule.comap
      (localPoleSpace (K := K) (L := L) π (n + 1)).subtype
      (localPoleSpace (K := K) (L := L) π 0)) inclusion (by
        intro x hx
        change (x : L) ∈ localPoleSpace (K := K) (L := L) π 0 at hx ⊢
        exact hx)

/-- Forgetting the top pole layer maps principal parts of order `n + 1` onto
the last local quotient. -/
def localPrincipalPartLayerMap (π : R) (n : ℕ) :
    localPrincipalPartSpace (K := K) (L := L) π (n + 1) →ₗ[K]
      localPrincipalPartLayer (K := K) (L := L) π n := by
  apply Submodule.factor
  intro x hx
  change (x : L) ∈ localPoleSpace (K := K) (L := L) π 0 at hx
  change (x : L) ∈ localPoleSpace (K := K) (L := L) π n
  exact localPoleSpace_mono_of_le (K := K) (L := L) π (Nat.zero_le n) hx

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] [IsFractionRing R L] in
theorem localPrincipalPartInclusion_injective (π : R) (n : ℕ) :
    Function.Injective
      (localPrincipalPartInclusion (K := K) (L := L) π n) := by
  rw [← LinearMap.ker_eq_bot]
  ext x
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  change (Submodule.Quotient.mk
      (Submodule.inclusion
        (localPoleSpace_mono (K := K) (L := L) π n) x) = 0) ↔
    Submodule.Quotient.mk x = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
  rfl

theorem range_localPrincipalPartInclusion_eq_ker_layerMap
    (π : R) (n : ℕ) :
    LinearMap.range
        (localPrincipalPartInclusion (K := K) (L := L) π n) =
      LinearMap.ker
        (localPrincipalPartLayerMap (K := K) (L := L) π n) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    refine Submodule.Quotient.induction_on _ y ?_
    intro y
    simp [localPrincipalPartInclusion, localPrincipalPartLayerMap]
  · intro hx
    obtain ⟨x, rfl⟩ := Quotient.exists_rep x
    rw [LinearMap.mem_ker] at hx
    change Submodule.Quotient.mk x = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    let y : localPoleSpace (K := K) (L := L) π n := ⟨x.1, hx⟩
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rfl

/-- Every local principal-part space is finite-dimensional. -/
theorem localPrincipalPartSpace_finite
    (π : R) (hπ : π ≠ 0)
    (hπIdeal : (IsDiscreteValuationRing.maximalIdeal R).asIdeal =
      Ideal.span {π}) (n : ℕ)
    [Module.Finite K (IsLocalRing.ResidueField R)] :
    Module.Finite K (localPrincipalPartSpace (K := K) (L := L) π n) := by
  induction n with
  | zero =>
      have htop : Submodule.comap
          (localPoleSpace (K := K) (L := L) π 0).subtype
          (localPoleSpace (K := K) (L := L) π 0) = ⊤ := by
        ext x
        simp
      change Module.Finite K
        (localPoleSpace (K := K) (L := L) π 0 ⧸
          Submodule.comap
            (localPoleSpace (K := K) (L := L) π 0).subtype
            (localPoleSpace (K := K) (L := L) π 0))
      rw [htop]
      infer_instance
  | succ n ih =>
      let f := localPrincipalPartLayerMap (K := K) (L := L) π n
      let : Module.Finite K (localPrincipalPartLayer (K := K) (L := L) π n) :=
        Module.Finite.equiv
          (localPoleQuotientEquivResidueField
            (K := K) (L := L) π hπ hπIdeal n).symm
      let : Module.Finite K f.ker := by
        rw [show f.ker = LinearMap.range
          (localPrincipalPartInclusion (K := K) (L := L) π n) by
            exact (range_localPrincipalPartInclusion_eq_ker_layerMap
              (K := K) (L := L) π n).symm]
        infer_instance
      let : Module.Finite K f.range := inferInstance
      let : Module.Finite K
          (localPrincipalPartSpace (K := K) (L := L) π (n + 1) ⧸ f.ker) :=
        Module.Finite.equiv f.quotKerEquivRange.symm
      exact Module.Finite.of_submodule_quotient f.ker

/-- The dimension of the genuine local principal-part quotient is the pole
order times the residue-field degree. -/
theorem localPrincipalPartSpace_finrank
    (π : R) (hπ : π ≠ 0)
    (hπIdeal : (IsDiscreteValuationRing.maximalIdeal R).asIdeal =
      Ideal.span {π}) (n : ℕ)
    [Module.Finite K (IsLocalRing.ResidueField R)] :
    Module.finrank K (localPrincipalPartSpace (K := K) (L := L) π n) =
      n * Module.finrank K (IsLocalRing.ResidueField R) := by
  induction n with
  | zero =>
      have htop : Submodule.comap
          (localPoleSpace (K := K) (L := L) π 0).subtype
          (localPoleSpace (K := K) (L := L) π 0) = ⊤ := by
        ext x
        simp
      change Module.finrank K
          (localPoleSpace (K := K) (L := L) π 0 ⧸
            Submodule.comap
              (localPoleSpace (K := K) (L := L) π 0).subtype
              (localPoleSpace (K := K) (L := L) π 0)) =
        0 * Module.finrank K (IsLocalRing.ResidueField R)
      rw [htop]
      simpa using (Module.finrank_zero_of_subsingleton
        (R := K)
        (M := localPoleSpace (K := K) (L := L) π 0 ⧸
          (⊤ : Submodule K
            (localPoleSpace (K := K) (L := L) π 0))))
  | succ n ih =>
      let := localPrincipalPartSpace_finite
        (K := K) (L := L) π hπ hπIdeal n
      let := localPrincipalPartSpace_finite
        (K := K) (L := L) π hπ hπIdeal (n + 1)
      let f := localPrincipalPartLayerMap (K := K) (L := L) π n
      have hsurj : Function.Surjective f := by
        intro x
        obtain ⟨x, rfl⟩ := Quotient.exists_rep x
        exact ⟨Submodule.Quotient.mk x, rfl⟩
      have hker := range_localPrincipalPartInclusion_eq_ker_layerMap
        (K := K) (L := L) π n
      have hker' : f.ker = LinearMap.range
          (localPrincipalPartInclusion (K := K) (L := L) π n) := by
        simpa [f] using hker.symm
      calc
        Module.finrank K
            (localPrincipalPartSpace (K := K) (L := L) π (n + 1)) =
            Module.finrank K f.range + Module.finrank K f.ker :=
          f.finrank_range_add_finrank_ker.symm
        _ = Module.finrank K
              (localPrincipalPartLayer (K := K) (L := L) π n) +
            Module.finrank K
              (localPrincipalPartSpace (K := K) (L := L) π n) := by
          rw [show f.range = ⊤ from LinearMap.range_eq_top.mpr hsurj,
            finrank_top, hker',
            LinearMap.finrank_range_of_inj
              (localPrincipalPartInclusion_injective
                (K := K) (L := L) π n)]
        _ = Module.finrank K (IsLocalRing.ResidueField R) +
            n * Module.finrank K (IsLocalRing.ResidueField R) := by
          rw [localPoleQuotient_finrank
            (K := K) (L := L) π hπ hπIdeal n, ih]
        _ = (n + 1) * Module.finrank K (IsLocalRing.ResidueField R) := by
          simp [Nat.add_mul, Nat.add_comm]

end OnePlace

section QuotientByKernel

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A linear map descends injectively after quotienting by a submodule known
to be its kernel. -/
def quotientLinearMapOfKerEq
    (f : V →ₗ[K] W) (P : Submodule K V) (hker : f.ker = P) :
    (V ⧸ P) →ₗ[K] W :=
  P.liftQ f hker.symm.le

theorem quotientLinearMapOfKerEq_injective
    (f : V →ₗ[K] W) (P : Submodule K V) (hker : f.ker = P) :
    Function.Injective (quotientLinearMapOfKerEq f P hker) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot P f hker.symm.le hker.le

/-- The quotient by the kernel of a map into a finite-dimensional space has
dimension at most that of the target. -/
theorem finrank_quotient_le_of_ker_eq
    (f : V →ₗ[K] W) (P : Submodule K V) (hker : f.ker = P)
    [Module.Finite K W] :
    Module.finrank K (V ⧸ P) ≤ Module.finrank K W := by
  rw [← hker, f.quotKerEquivRange.finrank_eq]
  exact f.range.finrank_le

end QuotientByKernel

section FiniteFamily

variable {K L I : Type*} [Field K] [Field L] [Fintype I]
  {R : I → Type*}
  [∀ i, CommRing (R i)] [∀ i, IsDedekindDomain (R i)]
  [∀ i, IsDiscreteValuationRing (R i)]
  [∀ i, Algebra K (R i)] [∀ i, Algebra (R i) L] [Algebra K L]
  [∀ i, IsScalarTower K (R i) L] [∀ i, IsFractionRing (R i) L]

/-- A finite family of local principal-part spaces. -/
abbrev finitePrincipalPartsSpace (π : ∀ i, R i) (n : I → ℕ) :=
  ∀ i, localPrincipalPartSpace (K := K) (L := L) (π i) (n i)

/-- The weighted degree of a finite family of pole bounds. -/
def finitePrincipalPartsDegree (n : I → ℕ) : ℕ :=
  ∑ i, n i * Module.finrank K (IsLocalRing.ResidueField (R i))

/-- Finite principal parts have dimension equal to the weighted pole degree. -/
theorem finitePrincipalPartsSpace_finrank
    (π : ∀ i, R i) (hπ : ∀ i, π i ≠ 0)
    (hπIdeal : ∀ i,
      (IsDiscreteValuationRing.maximalIdeal (R i)).asIdeal =
        Ideal.span {π i}) (n : I → ℕ)
    [∀ i, Module.Finite K (IsLocalRing.ResidueField (R i))] :
    Module.finrank K (finitePrincipalPartsSpace (K := K) (L := L) π n) =
      finitePrincipalPartsDegree (K := K) (R := R) n := by
  let localPrincipalPartModule (i : I) : Module K
      (localPrincipalPartSpace (K := K) (L := L) (π i) (n i)) :=
    inferInstance
  let finitePrincipalPartsModule : Module K
      (finitePrincipalPartsSpace (K := K) (L := L) π n) :=
    Pi.module I
      (fun i => localPrincipalPartSpace (K := K) (L := L) (π i) (n i)) K
  let (i : I) : Module.Finite K
      (localPrincipalPartSpace (K := K) (L := L) (π i) (n i)) :=
    localPrincipalPartSpace_finite
      (K := K) (L := L) (π i) (hπ i) (hπIdeal i) (n i)
  let (i : I) : Module.Free K
      (localPrincipalPartSpace (K := K) (L := L) (π i) (n i)) :=
    Module.Free.of_divisionRing K
      (localPrincipalPartSpace (K := K) (L := L) (π i) (n i))
  rw [Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact localPrincipalPartSpace_finrank
    (K := K) (L := L) (π i) (hπ i) (hπIdeal i) (n i)

/-- A global subspace with the prescribed local pole bounds maps diagonally
to its finite family of principal parts. -/
def finitePrincipalPartsDiagonalMap
    (π : ∀ i, R i) (n : I → ℕ) (S : Submodule K L)
    (hS : ∀ i, S ≤ localPoleSpace (K := K) (L := L) (π i) (n i)) :
    S →ₗ[K] finitePrincipalPartsSpace (K := K) (L := L) π n :=
  LinearMap.pi fun i =>
    (Submodule.comap
      (localPoleSpace (K := K) (L := L) (π i) (n i)).subtype
      (localPoleSpace (K := K) (L := L) (π i) 0)).mkQ.comp
      (Submodule.inclusion (hS i))

/-- The elements of a global subspace that are regular at every chosen
place. -/
def regularAtFiniteFamily
    (π : ∀ i, R i) (S : Submodule K L) : Submodule K S :=
  ⨅ i, Submodule.comap S.subtype
    (localPoleSpace (K := K) (L := L) (π i) 0)

omit [Fintype I] [∀ i, IsDedekindDomain (R i)]
  [∀ i, IsDiscreteValuationRing (R i)]
  [∀ i, IsFractionRing (R i) L] in
/-- The kernel of the diagonal principal-parts map is exactly simultaneous
regularity at the chosen places. -/
theorem finitePrincipalPartsDiagonalMap_ker
    (π : ∀ i, R i) (n : I → ℕ) (S : Submodule K L)
    (hS : ∀ i, S ≤ localPoleSpace (K := K) (L := L) (π i) (n i)) :
    LinearMap.ker
        (finitePrincipalPartsDiagonalMap
          (K := K) (L := L) π n S hS) =
      regularAtFiniteFamily (K := K) (L := L) π S := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    rw [regularAtFiniteFamily, Submodule.mem_iInf]
    intro i
    have hi := congrFun hx i
    change Submodule.Quotient.mk
      (Submodule.inclusion (hS i) x) = 0 at hi
    rw [Submodule.Quotient.mk_eq_zero] at hi
    exact hi
  · intro hx
    funext i
    rw [regularAtFiniteFamily, Submodule.mem_iInf] at hx
    change Submodule.Quotient.mk
      (Submodule.inclusion (hS i) x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx i

/-- Consequently, the global quotient by simultaneous regularity has
dimension at most the weighted pole degree. -/
theorem finrank_quotient_regularAtFiniteFamily_le_degree
    (π : ∀ i, R i) (hπ : ∀ i, π i ≠ 0)
    (hπIdeal : ∀ i,
      (IsDiscreteValuationRing.maximalIdeal (R i)).asIdeal =
        Ideal.span {π i})
    (n : I → ℕ) (S : Submodule K L)
    (hS : ∀ i, S ≤ localPoleSpace (K := K) (L := L) (π i) (n i))
    [∀ i, Module.Finite K (IsLocalRing.ResidueField (R i))] :
    Module.finrank K
        (S ⧸ regularAtFiniteFamily (K := K) (L := L) π S) ≤
      finitePrincipalPartsDegree (K := K) (R := R) n := by
  let localPrincipalPartModule (i : I) : Module K
      (localPrincipalPartSpace (K := K) (L := L) (π i) (n i)) :=
    inferInstance
  let finitePrincipalPartsModule : Module K
      (finitePrincipalPartsSpace (K := K) (L := L) π n) :=
    Pi.module I
      (fun i => localPrincipalPartSpace (K := K) (L := L) (π i) (n i)) K
  let (i : I) : Module.Finite K
      (localPrincipalPartSpace (K := K) (L := L) (π i) (n i)) :=
    localPrincipalPartSpace_finite
      (K := K) (L := L) (π i) (hπ i) (hπIdeal i) (n i)
  let : Module.Finite K
      (finitePrincipalPartsSpace (K := K) (L := L) π n) := inferInstance
  let f : S →ₗ[K] finitePrincipalPartsSpace (K := K) (L := L) π n :=
    finitePrincipalPartsDiagonalMap (K := K) (L := L) π n S hS
  have hfker : f.ker = regularAtFiniteFamily (K := K) (L := L) π S := by
    simpa [f] using finitePrincipalPartsDiagonalMap_ker
      (K := K) (L := L) π n S hS
  let q := quotientLinearMapOfKerEq
    (K := K) (V := S)
    (W := finitePrincipalPartsSpace (K := K) (L := L) π n) f
    (regularAtFiniteFamily (K := K) (L := L) π S) hfker
  have hq : Function.Injective q :=
    quotientLinearMapOfKerEq_injective
      (K := K) (V := S)
      (W := finitePrincipalPartsSpace (K := K) (L := L) π n) f
      (regularAtFiniteFamily (K := K) (L := L) π S) hfker
  calc
    Module.finrank K
        (S ⧸ regularAtFiniteFamily (K := K) (L := L) π S) ≤
        Module.finrank K
        (finitePrincipalPartsSpace (K := K) (L := L) π n) :=
      q.finrank_le_finrank_of_injective hq
    _ = finitePrincipalPartsDegree (K := K) (R := R) n :=
      finitePrincipalPartsSpace_finrank
        (K := K) (L := L) π hπ hπIdeal n

end FiniteFamily

end

end BGS.HasseWeil
