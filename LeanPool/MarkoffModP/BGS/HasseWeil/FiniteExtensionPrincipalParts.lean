/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionLocalPoleQuotient
import LeanPool.MarkoffModP.BGS.HasseWeil.FinitePrincipalParts
import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceConstants

/-!
# Principal parts of an effective exhaustive divisor

For an effective divisor `D` on the exhaustive places of a finite extension
of `K(X)`, this file forms the product of the local principal-part spaces over
the finite support of `D`.  The local cumulative quotient calculation gives
this product dimension equal to `deg D`.

The Riemann space `L(D)` maps diagonally to those principal parts.  Its kernel
is exactly `L(0)`: vanishing of the principal part gives regularity on the
support, while membership in `L(D)` already gives regularity off the support.
Consequently `L(D) / L(0)` is finite-dimensional and has dimension at most
`deg D`.  Under the exact-constant-field hypothesis, the denominator is the
space of constants.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open Submodule
open scoped Polynomial BigOperators

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance finitePrincipalPartsConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance finitePrincipalPartsConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Principal parts at a place in the support of an effective exhaustive
divisor. -/
abbrev finiteExtensionPrincipalPartAt
    (D : FiniteExtensionDivisor K L) (P : ↥D.support) :=
  finiteExtensionLocalPoleSpace K L P.1 (D P.1).toNat ⧸
    relativeSubmodule
      (finiteExtensionLocalPoleSpace K L P.1 0)
      (finiteExtensionLocalPoleSpace K L P.1 (D P.1).toNat)

/-- The finite product of local principal parts supported by `D`. -/
abbrev finiteExtensionPrincipalPartsSpace
    (D : FiniteExtensionDivisor K L) :=
  ∀ P : ↥D.support, finiteExtensionPrincipalPartAt K L D P

/-- The natural-number weighted degree of an effective exhaustive divisor. -/
def finiteExtensionEffectiveDivisorNatDegree
    (D : FiniteExtensionDivisor K L) : ℕ :=
  ∑ P : ↥D.support,
    (D P.1).toNat * finiteExtensionPlaceDegree K L P.1

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- A nonzero effective coefficient has positive natural part. -/
theorem finiteExtensionDivisor_toNat_pos_of_mem_support
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P)
    (P : ↥D.support) :
    0 < (D P.1).toNat := by
  rw [← Int.pos_iff_toNat_pos]
  have hne : D P.1 ≠ 0 := Finsupp.mem_support_iff.mp P.2
  exact lt_of_le_of_ne (hD P.1) (Ne.symm hne)

/-- Each supported local principal-part quotient is finite-dimensional. -/
theorem finiteExtensionPrincipalPartAt_moduleFinite
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P)
    (P : ↥D.support) :
    Module.Finite K (finiteExtensionPrincipalPartAt K L D P) := by
  apply Module.finite_of_finrank_pos
  rw [finiteExtensionLocalPoleSpace_cumulative_finrank K L P.1
    (D P.1).toNat]
  exact Nat.mul_pos
    (finiteExtensionDivisor_toNat_pos_of_mem_support K L D hD P)
    (finiteExtensionPlaceDegree_pos K L P.1)

/-- The supported product of local principal parts is finite-dimensional. -/
theorem finiteExtensionPrincipalPartsSpace_moduleFinite
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P) :
    Module.Finite K (finiteExtensionPrincipalPartsSpace K L D) := by
  let (P : ↥D.support) : Module.Finite K
      (finiteExtensionPrincipalPartAt K L D P) :=
    finiteExtensionPrincipalPartAt_moduleFinite K L D hD P
  exact Module.Finite.pi

/-- The supported product has dimension equal to the natural weighted degree
of `D`. -/
theorem finiteExtensionPrincipalPartsSpace_finrank
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P) :
    Module.finrank K (finiteExtensionPrincipalPartsSpace K L D) =
      finiteExtensionEffectiveDivisorNatDegree K L D := by
  let (P : ↥D.support) : Module.Finite K
      (finiteExtensionPrincipalPartAt K L D P) :=
    finiteExtensionPrincipalPartAt_moduleFinite K L D hD P
  let (P : ↥D.support) : Module.Free K
      (finiteExtensionPrincipalPartAt K L D P) :=
    Module.Free.of_divisionRing K (finiteExtensionPrincipalPartAt K L D P)
  rw [Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro P _
  exact finiteExtensionLocalPoleSpace_cumulative_finrank K L P.1
    (D P.1).toNat

omit [Fintype K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- For an effective divisor, the natural weighted degree casts to the usual
integer-valued divisor degree. -/
theorem finiteExtensionEffectiveDivisorNatDegree_cast
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P) :
    (finiteExtensionEffectiveDivisorNatDegree K L D : ℤ) =
      finiteExtensionDivisorDegree K L D := by
  rw [finiteExtensionEffectiveDivisorNatDegree, finiteExtensionDivisorDegree,
    Finsupp.sum]
  push_cast
  calc
    (∑ P : ↥D.support,
        ((D P.1).toNat : ℤ) *
          (finiteExtensionPlaceDegree K L P.1 : ℤ)) =
        ∑ P ∈ D.support,
          ((D P).toNat : ℤ) *
            (finiteExtensionPlaceDegree K L P : ℤ) :=
      Finset.sum_coe_sort D.support (fun P =>
        ((D P).toNat : ℤ) *
          (finiteExtensionPlaceDegree K L P : ℤ))
    _ = ∑ P ∈ D.support,
        D P * (finiteExtensionPlaceDegree K L P : ℤ) := by
      apply Finset.sum_congr rfl
      intro P _
      rw [Int.toNat_of_nonneg (hD P)]

/-- Membership in `L(D)` supplies the local pole bound at every place. -/
theorem finiteExtensionRiemannSpace_le_localPoleSpace
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P)
    (P : FiniteExtensionPlace K L) :
    finiteExtensionRiemannSpace K L D ≤
      finiteExtensionLocalPoleSpace K L P (D P).toNat := by
  intro x hx
  rw [mem_finiteExtensionRiemannSpace] at hx
  rw [mem_finiteExtensionLocalPoleSpace_iff]
  rcases hx with rfl | ⟨hx0, hx⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨hx0, ?_⟩
    have hcoeff : ((D P).toNat : ℤ) = D P :=
      Int.toNat_of_nonneg (hD P)
    have hP := hx P
    omega

/-- The diagonal principal-parts map from `L(D)`. -/
def finiteExtensionRiemannPrincipalPartsDiagonalMap
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P) :
    finiteExtensionRiemannSpace K L D →ₗ[K]
      finiteExtensionPrincipalPartsSpace K L D :=
  LinearMap.pi fun P =>
    (relativeSubmodule
      (finiteExtensionLocalPoleSpace K L P.1 0)
      (finiteExtensionLocalPoleSpace K L P.1 (D P.1).toNat)).mkQ.comp
      (Submodule.inclusion
        (finiteExtensionRiemannSpace_le_localPoleSpace K L D hD P.1))

/-- The kernel of the diagonal map is the copy of `L(0)` inside `L(D)`. -/
theorem finiteExtensionRiemannPrincipalPartsDiagonalMap_ker
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P) :
    LinearMap.ker
        (finiteExtensionRiemannPrincipalPartsDiagonalMap K L D hD) =
      relativeSubmodule
        (finiteExtensionRiemannSpace K L 0)
        (finiteExtensionRiemannSpace K L D) := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  constructor
  · intro hxker
    rw [mem_finiteExtensionRiemannSpace]
    have hxD := x.2
    rw [mem_finiteExtensionRiemannSpace] at hxD
    rcases hxD with hx0 | ⟨hx0, hxorders⟩
    · exact Or.inl hx0
    · refine Or.inr ⟨hx0, ?_⟩
      intro P
      by_cases hP : P ∈ D.support
      · let P' : ↥D.support := ⟨P, hP⟩
        have hcomponent := congrFun hxker P'
        change Submodule.Quotient.mk
            (Submodule.inclusion
              (finiteExtensionRiemannSpace_le_localPoleSpace
                K L D hD P) x) = 0 at hcomponent
        rw [Submodule.Quotient.mk_eq_zero] at hcomponent
        change (x : L) ∈
          finiteExtensionLocalPoleSpace K L P 0 at hcomponent
        rw [mem_finiteExtensionLocalPoleSpace_iff] at hcomponent
        rcases hcomponent with hzero | ⟨_, horder⟩
        · exact (hx0 hzero).elim
        · simpa using horder
      · have hDP : D P = 0 := by
          simpa [Finsupp.mem_support_iff] using hP
        have horder := hxorders P
        rw [hDP] at horder
        simpa using horder
  · intro hxzero
    funext P
    change Submodule.Quotient.mk
        (Submodule.inclusion
          (finiteExtensionRiemannSpace_le_localPoleSpace
            K L D hD P.1) x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change (x : L) ∈
      finiteExtensionLocalPoleSpace K L P.1 0
    rw [mem_finiteExtensionRiemannSpace] at hxzero
    rw [mem_finiteExtensionLocalPoleSpace_iff]
    rcases hxzero with hxzero | ⟨hx0, hxorders⟩
    · exact Or.inl hxzero
    · exact Or.inr ⟨hx0, by simpa using hxorders P.1⟩

/-- The diagonal map descends injectively from `L(D) / L(0)`. -/
def finiteExtensionRiemannPrincipalPartsQuotientMap
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P) :
    (finiteExtensionRiemannSpace K L D ⧸
      relativeSubmodule
        (finiteExtensionRiemannSpace K L 0)
        (finiteExtensionRiemannSpace K L D)) →ₗ[K]
      finiteExtensionPrincipalPartsSpace K L D := by
  letI localPrincipalPartModule (P : ↥D.support) : Module K
      (finiteExtensionPrincipalPartAt K L D P) := inferInstance
  letI finitePrincipalPartsModule : Module K
      (finiteExtensionPrincipalPartsSpace K L D) :=
    Pi.module ↥D.support
      (fun P => finiteExtensionPrincipalPartAt K L D P) K
  let f : finiteExtensionRiemannSpace K L D →ₗ[K]
      finiteExtensionPrincipalPartsSpace K L D :=
    finiteExtensionRiemannPrincipalPartsDiagonalMap K L D hD
  have hfker : f.ker =
      relativeSubmodule
        (finiteExtensionRiemannSpace K L 0)
        (finiteExtensionRiemannSpace K L D) := by
    simpa [f] using
      finiteExtensionRiemannPrincipalPartsDiagonalMap_ker K L D hD
  exact quotientLinearMapOfKerEq
    (K := K) (V := finiteExtensionRiemannSpace K L D)
    (W := finiteExtensionPrincipalPartsSpace K L D) f
    (relativeSubmodule
      (finiteExtensionRiemannSpace K L 0)
      (finiteExtensionRiemannSpace K L D))
    hfker

/-- The descended principal-parts map is injective. -/
theorem finiteExtensionRiemannPrincipalPartsQuotientMap_injective
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P) :
    Function.Injective
      (finiteExtensionRiemannPrincipalPartsQuotientMap K L D hD) := by
  let localPrincipalPartModule (P : ↥D.support) : Module K
      (finiteExtensionPrincipalPartAt K L D P) := inferInstance
  let finitePrincipalPartsModule : Module K
      (finiteExtensionPrincipalPartsSpace K L D) :=
    Pi.module ↥D.support
      (fun P => finiteExtensionPrincipalPartAt K L D P) K
  let f : finiteExtensionRiemannSpace K L D →ₗ[K]
      finiteExtensionPrincipalPartsSpace K L D :=
    finiteExtensionRiemannPrincipalPartsDiagonalMap K L D hD
  have hfker : f.ker =
      relativeSubmodule
        (finiteExtensionRiemannSpace K L 0)
        (finiteExtensionRiemannSpace K L D) := by
    simpa [f] using
      finiteExtensionRiemannPrincipalPartsDiagonalMap_ker K L D hD
  exact quotientLinearMapOfKerEq_injective
    (K := K) (V := finiteExtensionRiemannSpace K L D)
    (W := finiteExtensionPrincipalPartsSpace K L D) f
    (relativeSubmodule
      (finiteExtensionRiemannSpace K L 0)
      (finiteExtensionRiemannSpace K L D))
    hfker

/-- For an effective divisor, `L(D) / L(0)` is finite-dimensional. -/
theorem finiteExtensionRiemannSpace_quotient_zero_moduleFinite
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P) :
    Module.Finite K
      (finiteExtensionRiemannSpace K L D ⧸
        relativeSubmodule
          (finiteExtensionRiemannSpace K L 0)
          (finiteExtensionRiemannSpace K L D)) := by
  let localPrincipalPartModule (P : ↥D.support) : Module K
      (finiteExtensionPrincipalPartAt K L D P) := inferInstance
  let finitePrincipalPartsModule : Module K
      (finiteExtensionPrincipalPartsSpace K L D) :=
    Pi.module ↥D.support
      (fun P => finiteExtensionPrincipalPartAt K L D P) K
  let (P : ↥D.support) : Module.Finite K
      (finiteExtensionPrincipalPartAt K L D P) :=
    finiteExtensionPrincipalPartAt_moduleFinite K L D hD P
  let : Module.Finite K (finiteExtensionPrincipalPartsSpace K L D) :=
    Module.Finite.pi
  let f : finiteExtensionRiemannSpace K L D →ₗ[K]
      finiteExtensionPrincipalPartsSpace K L D :=
    finiteExtensionRiemannPrincipalPartsDiagonalMap K L D hD
  have hfker : f.ker =
      relativeSubmodule
        (finiteExtensionRiemannSpace K L 0)
        (finiteExtensionRiemannSpace K L D) := by
    simpa [f] using
      finiteExtensionRiemannPrincipalPartsDiagonalMap_ker K L D hD
  let q := quotientLinearMapOfKerEq
    (K := K) (V := finiteExtensionRiemannSpace K L D)
    (W := finiteExtensionPrincipalPartsSpace K L D) f
    (relativeSubmodule
      (finiteExtensionRiemannSpace K L 0)
      (finiteExtensionRiemannSpace K L D))
    hfker
  have hq : Function.Injective q :=
    quotientLinearMapOfKerEq_injective
      (K := K) (V := finiteExtensionRiemannSpace K L D)
      (W := finiteExtensionPrincipalPartsSpace K L D) f
      (relativeSubmodule
        (finiteExtensionRiemannSpace K L 0)
        (finiteExtensionRiemannSpace K L D))
      hfker
  exact Module.Finite.of_injective q hq

/-- Riemann's elementary principal-parts upper bound for an effective
exhaustive divisor. -/
theorem finiteExtensionRiemannSpace_quotient_zero_finrank_le
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P) :
    Module.finrank K
        (finiteExtensionRiemannSpace K L D ⧸
          relativeSubmodule
            (finiteExtensionRiemannSpace K L 0)
            (finiteExtensionRiemannSpace K L D)) ≤
      finiteExtensionEffectiveDivisorNatDegree K L D := by
  let localPrincipalPartModule (P : ↥D.support) : Module K
      (finiteExtensionPrincipalPartAt K L D P) := inferInstance
  let finitePrincipalPartsModule : Module K
      (finiteExtensionPrincipalPartsSpace K L D) :=
    Pi.module ↥D.support
      (fun P => finiteExtensionPrincipalPartAt K L D P) K
  let (P : ↥D.support) : Module.Finite K
      (finiteExtensionPrincipalPartAt K L D P) :=
    finiteExtensionPrincipalPartAt_moduleFinite K L D hD P
  let : Module.Finite K (finiteExtensionPrincipalPartsSpace K L D) :=
    Module.Finite.pi
  let f : finiteExtensionRiemannSpace K L D →ₗ[K]
      finiteExtensionPrincipalPartsSpace K L D :=
    finiteExtensionRiemannPrincipalPartsDiagonalMap K L D hD
  have hfker : f.ker =
      relativeSubmodule
        (finiteExtensionRiemannSpace K L 0)
        (finiteExtensionRiemannSpace K L D) := by
    simpa [f] using
      finiteExtensionRiemannPrincipalPartsDiagonalMap_ker K L D hD
  let q := quotientLinearMapOfKerEq
    (K := K) (V := finiteExtensionRiemannSpace K L D)
    (W := finiteExtensionPrincipalPartsSpace K L D) f
    (relativeSubmodule
      (finiteExtensionRiemannSpace K L 0)
      (finiteExtensionRiemannSpace K L D))
    hfker
  have hq : Function.Injective q :=
    quotientLinearMapOfKerEq_injective
      (K := K) (V := finiteExtensionRiemannSpace K L D)
      (W := finiteExtensionPrincipalPartsSpace K L D) f
      (relativeSubmodule
        (finiteExtensionRiemannSpace K L 0)
        (finiteExtensionRiemannSpace K L D))
      hfker
  calc
    Module.finrank K
        (finiteExtensionRiemannSpace K L D ⧸
          relativeSubmodule
            (finiteExtensionRiemannSpace K L 0)
            (finiteExtensionRiemannSpace K L D)) ≤
        Module.finrank K (finiteExtensionPrincipalPartsSpace K L D) :=
      q.finrank_le_finrank_of_injective hq
    _ = finiteExtensionEffectiveDivisorNatDegree K L D :=
      finiteExtensionPrincipalPartsSpace_finrank K L D hD

/-- Integer-valued form of the principal-parts upper bound. -/
theorem finiteExtensionRiemannSpace_quotient_zero_finrank_cast_le_degree
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P) :
    (Module.finrank K
        (finiteExtensionRiemannSpace K L D ⧸
          relativeSubmodule
            (finiteExtensionRiemannSpace K L 0)
            (finiteExtensionRiemannSpace K L D)) : ℤ) ≤
      finiteExtensionDivisorDegree K L D := by
  rw [← finiteExtensionEffectiveDivisorNatDegree_cast K L D hD]
  exact_mod_cast finiteExtensionRiemannSpace_quotient_zero_finrank_le
    K L D hD

/-- With exact constants, the preceding quotient is literally `L(D)` modulo
the constant functions. -/
theorem finiteExtensionRiemannSpace_mod_constants_finrank_cast_le_degree
    (D : FiniteExtensionDivisor K L) (hD : ∀ P, 0 ≤ D P)
    (hconstants : algebraicClosure K L = ⊥) :
    (Module.finrank K
        (finiteExtensionRiemannSpace K L D ⧸
          relativeSubmodule
            (LinearMap.range (Algebra.linearMap K L))
            (finiteExtensionRiemannSpace K L D)) : ℤ) ≤
      finiteExtensionDivisorDegree K L D := by
  rw [← finiteExtensionRiemannSpace_zero_eq_range K L hconstants]
  exact finiteExtensionRiemannSpace_quotient_zero_finrank_cast_le_degree
    K L D hD

end

end BGS.HasseWeil
