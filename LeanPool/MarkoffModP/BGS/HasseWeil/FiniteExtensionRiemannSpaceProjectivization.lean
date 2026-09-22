/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceEffectiveIncrement
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Projectivized Riemann-space counts

For a finite constant field, nonzero vectors in a finite-dimensional vector
space modulo multiplication by nonzero scalars form its projectivization.
This file records the three equivalent cardinality formulas needed in the
function-field zeta argument:

* the quotient by the scalar action;
* the set of one-dimensional subspaces; and
* the geometric sum `1 + q + ... + q^(l - 1)`.

The final statements specialize these formulas to every effective exhaustive
divisor, using the already proved finite-dimensionality of its Riemann space.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped LinearAlgebra.Projectivization Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K]
variable (V : Type*) [AddCommGroup V] [Module K V]

/-- One-dimensional subspaces of a finite vector space over `K` are counted
by the geometric sum in the dimension. -/
theorem finiteVectorSpace_oneDimensionalSubspace_card_eq_geomSum :
    Nat.card {W : Submodule K V // Module.finrank K W = 1} =
      ∑ i ∈ Finset.range (Module.finrank K V), Nat.card K ^ i := by
  rw [Nat.card_congr (Projectivization.equivSubmodule K V).symm]
  exact Projectivization.card_of_finrank K V rfl

/-- The orbit quotient of nonzero vectors by nonzero scalar multiplication is
counted by the same geometric sum. -/
theorem finiteVectorSpace_nonzeroScalarOrbitQuotient_card_eq_geomSum :
    Nat.card
        (Quotient
          (MulAction.orbitRel Kˣ {v : V // v ≠ 0})) =
      ∑ i ∈ Finset.range (Module.finrank K V), Nat.card K ^ i := by
  rw [Nat.card_congr (Projectivization.equivQuotientOrbitRel K V).symm]
  exact Projectivization.card_of_finrank K V rfl

variable [Module.Finite K V]

/-- Division form of the projective-space cardinality formula. -/
theorem finiteVectorSpace_nonzeroScalarOrbitQuotient_card_eq_div :
    Nat.card
        (Quotient
          (MulAction.orbitRel Kˣ {v : V // v ≠ 0})) =
      (Nat.card K ^ Module.finrank K V - 1) / (Nat.card K - 1) := by
  rw [Nat.card_congr (Projectivization.equivQuotientOrbitRel K V).symm,
    Projectivization.card'', Module.natCard_eq_pow_finrank (K := K)]

variable [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance projectivizedRiemannSpaceConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance projectivizedRiemannSpaceConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Effective exhaustive divisors in the principal-divisor class represented
by `D`.  The sign convention matches the Riemann-space definition:
`x \in L(D)` gives the effective divisor `div(x) + D`. -/
def EffectiveDivisorInPrincipalClass (D : FiniteExtensionDivisor K L) :=
  {E : FiniteExtensionDivisor K L //
    (∀ v, 0 ≤ E v) ∧
      ∃ x : L, x ≠ 0 ∧
        E = finiteExtensionPrincipalDivisor K L x + D}

/-- A nonzero Riemann-space section determines an effective divisor in the
principal class represented by `D`. -/
def effectiveDivisorInPrincipalClassOfNonzeroSection
    (D : FiniteExtensionDivisor K L)
    (x : {x : finiteExtensionRiemannSpace K L D // x ≠ 0}) :
    EffectiveDivisorInPrincipalClass K L D := by
  have hx0 : (x.1.1 : L) ≠ 0 := Subtype.coe_injective.ne x.2
  refine ⟨finiteExtensionPrincipalDivisor K L x.1.1 + D, ?_,
    x.1.1, hx0, rfl⟩
  have hxmem := x.1.2
  rw [mem_finiteExtensionRiemannSpace] at hxmem
  rcases hxmem with hx | ⟨_, hx⟩
  · exact (hx0 hx).elim
  · simpa only [Finsupp.add_apply] using hx

/-- Multiplying a nonzero section by a nonzero base-field scalar does not
change its associated effective divisor. -/
theorem effectiveDivisorInPrincipalClassOfNonzeroSection_smul
    (D : FiniteExtensionDivisor K L)
    (a b : {x : finiteExtensionRiemannSpace K L D // x ≠ 0})
    (c : K) (hab : a = c • (b : finiteExtensionRiemannSpace K L D)) :
    effectiveDivisorInPrincipalClassOfNonzeroSection K L D a =
      effectiveDivisorInPrincipalClassOfNonzeroSection K L D b := by
  have hc : c ≠ 0 := by
    intro hc
    apply a.2
    simpa [hc] using hab
  have hcL : algebraMap K L c ≠ 0 :=
    by simpa only [map_zero] using (algebraMap K L).injective.ne hc
  have hb0 : (b.1.1 : L) ≠ 0 := Subtype.coe_injective.ne b.2
  apply Subtype.ext
  dsimp only [effectiveDivisorInPrincipalClassOfNonzeroSection]
  have habL : (a.1.1 : L) = algebraMap K L c * (b.1.1 : L) := by
    simpa [Algebra.smul_def] using
      congrArg (fun z : finiteExtensionRiemannSpace K L D ↦ (z.1 : L)) hab
  rw [habL, finiteExtensionPrincipalDivisor_mul K L _ _ hcL hb0,
    finiteExtensionPrincipalDivisor_algebraMap_constant K L c hc, zero_add]

/-- Projectivizing the nonzero sections makes the associated effective
divisor independent of the chosen representative. -/
def projectiveRiemannSectionToEffectiveDivisorInPrincipalClass
    (D : FiniteExtensionDivisor K L) :
    Projectivization K (finiteExtensionRiemannSpace K L D) →
      EffectiveDivisorInPrincipalClass K L D :=
  Projectivization.lift
    (effectiveDivisorInPrincipalClassOfNonzeroSection K L D)
    (effectiveDivisorInPrincipalClassOfNonzeroSection_smul K L D)

@[simp]
theorem projectiveRiemannSectionToEffectiveDivisorInPrincipalClass_mk
    (D : FiniteExtensionDivisor K L)
    (x : finiteExtensionRiemannSpace K L D) (hx : x ≠ 0) :
    projectiveRiemannSectionToEffectiveDivisorInPrincipalClass K L D
        (Projectivization.mk K x hx) =
      effectiveDivisorInPrincipalClassOfNonzeroSection K L D ⟨x, hx⟩ :=
  rfl

/-- Every effective divisor in the represented principal class arises from
a projective nonzero section. -/
theorem projectiveRiemannSectionToEffectiveDivisorInPrincipalClass_surjective
    (D : FiniteExtensionDivisor K L) :
    Function.Surjective
      (projectiveRiemannSectionToEffectiveDivisorInPrincipalClass K L D) := by
  intro E
  obtain ⟨hEeffective, x, hx0, hE⟩ := E.2
  have hxmem : x ∈ finiteExtensionRiemannSpace K L D := by
    rw [mem_finiteExtensionRiemannSpace]
    exact Or.inr ⟨hx0, by
      intro v
      have hv := hEeffective v
      rw [hE, Finsupp.add_apply] at hv
      exact hv⟩
  let xD : finiteExtensionRiemannSpace K L D := ⟨x, hxmem⟩
  have hxD0 : xD ≠ 0 := by
    intro hxD
    apply hx0
    exact congrArg Subtype.val hxD
  refine ⟨Projectivization.mk K xD hxD0, ?_⟩
  apply Subtype.ext
  change finiteExtensionPrincipalDivisor K L x + D = E.1
  exact hE.symm

/-- Under exact constants, a nonzero function has zero exhaustive principal
divisor exactly when it is a nonzero base-field constant. -/
theorem finiteExtensionPrincipalDivisor_eq_zero_iff_isBaseConstant
    (hconstants : algebraicClosure K L = ⊥) (x : L) (hx0 : x ≠ 0) :
    finiteExtensionPrincipalDivisor K L x = 0 ↔
      ∃ c : K, c ≠ 0 ∧ algebraMap K L c = x := by
  constructor
  · intro hx
    have hxmem : x ∈ finiteExtensionRiemannSpace K L 0 := by
      rw [mem_finiteExtensionRiemannSpace]
      exact Or.inr ⟨hx0, by simp [hx]⟩
    rw [finiteExtensionRiemannSpace_zero_eq_range K L hconstants] at hxmem
    obtain ⟨c, hc⟩ := hxmem
    refine ⟨c, ?_, hc⟩
    intro hc0
    subst c
    exact hx0 (by simpa using hc.symm)
  · rintro ⟨c, hc, rfl⟩
    exact finiteExtensionPrincipalDivisor_algebraMap_constant K L c hc

/-- With exact constants, two nonzero functions have the same exhaustive
principal divisor exactly when they differ by a base-field scalar. -/
theorem finiteExtensionPrincipalDivisor_eq_iff_exists_smul
    (hconstants : algebraicClosure K L = ⊥)
    (x y : L) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    finiteExtensionPrincipalDivisor K L x =
        finiteExtensionPrincipalDivisor K L y ↔
      ∃ c : K, c • y = x := by
  constructor
  · intro hxy
    have hquot : finiteExtensionPrincipalDivisor K L (x / y) = 0 := by
      rw [finiteExtensionPrincipalDivisor_div K L x y hx0 hy0, hxy, sub_self]
    obtain ⟨c, _, hc⟩ :=
      (finiteExtensionPrincipalDivisor_eq_zero_iff_isBaseConstant
        K L hconstants (x / y) (div_ne_zero hx0 hy0)).mp hquot
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc, div_mul_cancel₀ x hy0]
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro hczero
      subst c
      exact hx0 (hc.symm.trans (zero_smul K y))
    have hcL : algebraMap K L c ≠ 0 :=
      by simpa only [map_zero] using (algebraMap K L).injective.ne hc0
    rw [← hc, Algebra.smul_def,
      finiteExtensionPrincipalDivisor_mul K L _ _ hcL hy0,
      finiteExtensionPrincipalDivisor_algebraMap_constant K L c hc0, zero_add]

/-- Exact constants make the projective-section map injective. -/
theorem projectiveRiemannSectionToEffectiveDivisorInPrincipalClass_injective
    (D : FiniteExtensionDivisor K L)
    (hconstants : algebraicClosure K L = ⊥) :
    Function.Injective
      (projectiveRiemannSectionToEffectiveDivisorInPrincipalClass K L D) := by
  intro p q hpq
  induction p using Projectivization.ind with
  | h x hx =>
      induction q using Projectivization.ind with
      | h y hy =>
          apply (Projectivization.mk_eq_mk_iff' K x y hx hy).2
          change
            effectiveDivisorInPrincipalClassOfNonzeroSection K L D ⟨x, hx⟩ =
              effectiveDivisorInPrincipalClassOfNonzeroSection K L D ⟨y, hy⟩
            at hpq
          have hdivAdd :
              finiteExtensionPrincipalDivisor K L x.1 + D =
                finiteExtensionPrincipalDivisor K L y.1 + D := by
            exact congrArg Subtype.val hpq
          have hdiv : finiteExtensionPrincipalDivisor K L x.1 =
              finiteExtensionPrincipalDivisor K L y.1 := add_right_cancel hdivAdd
          have hx0 : (x.1 : L) ≠ 0 := by
            intro hxzero
            apply hx
            exact Subtype.ext hxzero
          have hy0 : (y.1 : L) ≠ 0 := by
            intro hyzero
            apply hy
            exact Subtype.ext hyzero
          obtain ⟨c, hc⟩ :=
            (finiteExtensionPrincipalDivisor_eq_iff_exists_smul
              K L hconstants x.1 y.1
                hx0 hy0).mp hdiv
          refine ⟨c, Subtype.ext ?_⟩
          exact hc

/-- With exact constants, projective nonzero sections are equivalent to the
effective divisors in the represented principal class. -/
def projectiveRiemannSectionEquivEffectiveDivisorInPrincipalClass
    (D : FiniteExtensionDivisor K L)
    (hconstants : algebraicClosure K L = ⊥) :
    Projectivization K (finiteExtensionRiemannSpace K L D) ≃
      EffectiveDivisorInPrincipalClass K L D :=
  Equiv.ofBijective
    (projectiveRiemannSectionToEffectiveDivisorInPrincipalClass K L D)
    ⟨projectiveRiemannSectionToEffectiveDivisorInPrincipalClass_injective
        K L D hconstants,
      projectiveRiemannSectionToEffectiveDivisorInPrincipalClass_surjective
        K L D⟩

/-- Nonzero sections of `L(D)` modulo nonzero constant scalars satisfy the
projective-space `Nat.card` identity.  The following finiteness theorem turns
this into an ordinary finite count when `D` is effective. -/
theorem effectiveRiemannSpace_nonzeroScalarOrbitQuotient_card_eq_geomSum
    (D : FiniteExtensionDivisor K L) :
    Nat.card
        (Quotient
          (MulAction.orbitRel Kˣ
            {x : finiteExtensionRiemannSpace K L D // x ≠ 0})) =
      ∑ i ∈ Finset.range
          (Module.finrank K (finiteExtensionRiemannSpace K L D)),
        Nat.card K ^ i := by
  exact finiteVectorSpace_nonzeroScalarOrbitQuotient_card_eq_geomSum
    K (finiteExtensionRiemannSpace K L D)

/-- For effective `D`, the scalar-orbit quotient of nonzero sections is a
finite type. -/
theorem effectiveRiemannSpace_nonzeroScalarOrbitQuotient_finite
    (D : FiniteExtensionDivisor K L) (hD : ∀ v, 0 ≤ D v) :
    Finite
      (Quotient
        (MulAction.orbitRel Kˣ
          {x : finiteExtensionRiemannSpace K L D // x ≠ 0})) := by
  let : Module.Finite K (finiteExtensionRiemannSpace K L D) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L D hD
  let : Finite (finiteExtensionRiemannSpace K L D) :=
    Module.finite_of_finite K
  exact Finite.of_equiv
    (Projectivization K (finiteExtensionRiemannSpace K L D))
    (Projectivization.equivQuotientOrbitRel K
      (finiteExtensionRiemannSpace K L D))

/-- Division form of the projectivized effective Riemann-space count. -/
theorem effectiveRiemannSpace_nonzeroScalarOrbitQuotient_card_eq_div
    (D : FiniteExtensionDivisor K L) (hD : ∀ v, 0 ≤ D v) :
    Nat.card
        (Quotient
          (MulAction.orbitRel Kˣ
            {x : finiteExtensionRiemannSpace K L D // x ≠ 0})) =
      (Nat.card K ^
            Module.finrank K (finiteExtensionRiemannSpace K L D) - 1) /
        (Nat.card K - 1) := by
  let : Module.Finite K (finiteExtensionRiemannSpace K L D) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L D hD
  exact finiteVectorSpace_nonzeroScalarOrbitQuotient_card_eq_div
    K (finiteExtensionRiemannSpace K L D)

/-- Under exact constants, an effective divisor class represented by an
effective `D` is finite. -/
theorem effectiveDivisorInPrincipalClass_finite
    (D : FiniteExtensionDivisor K L) (hD : ∀ v, 0 ≤ D v)
    (hconstants : algebraicClosure K L = ⊥) :
    Finite (EffectiveDivisorInPrincipalClass K L D) := by
  let : Module.Finite K (finiteExtensionRiemannSpace K L D) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L D hD
  let : Finite (finiteExtensionRiemannSpace K L D) :=
    Module.finite_of_finite K
  exact Finite.of_equiv
    (Projectivization K (finiteExtensionRiemannSpace K L D))
    (projectiveRiemannSectionEquivEffectiveDivisorInPrincipalClass
      K L D hconstants)

/-- Cardinality of the effective divisors in a fixed principal class under
the exact-constants hypothesis. -/
theorem effectiveDivisorInPrincipalClass_card_eq_geomSum
    (D : FiniteExtensionDivisor K L)
    (hconstants : algebraicClosure K L = ⊥) :
    Nat.card (EffectiveDivisorInPrincipalClass K L D) =
      ∑ i ∈ Finset.range
          (Module.finrank K (finiteExtensionRiemannSpace K L D)),
        Nat.card K ^ i := by
  rw [Nat.card_congr
    (projectiveRiemannSectionEquivEffectiveDivisorInPrincipalClass
      K L D hconstants).symm]
  exact Projectivization.card_of_finrank K
    (finiteExtensionRiemannSpace K L D) rfl

/-- Division form of the fixed-principal-class count. -/
theorem effectiveDivisorInPrincipalClass_card_eq_div
    (D : FiniteExtensionDivisor K L) (hD : ∀ v, 0 ≤ D v)
    (hconstants : algebraicClosure K L = ⊥) :
    Nat.card (EffectiveDivisorInPrincipalClass K L D) =
      (Nat.card K ^
            Module.finrank K (finiteExtensionRiemannSpace K L D) - 1) /
        (Nat.card K - 1) := by
  let : Module.Finite K (finiteExtensionRiemannSpace K L D) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L D hD
  rw [Nat.card_congr
      (projectiveRiemannSectionEquivEffectiveDivisorInPrincipalClass
        K L D hconstants).symm,
    Projectivization.card'', Module.natCard_eq_pow_finrank (K := K)]

end

end BGS.HasseWeil
