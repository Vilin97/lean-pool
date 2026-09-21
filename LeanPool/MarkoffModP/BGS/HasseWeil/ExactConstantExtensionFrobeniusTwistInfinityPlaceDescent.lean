/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionInfinityPlaceDegreeTower
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistFinitePlaceUnramified

/-!
# Infinity places of Frobenius-twist fields

This file proves the infinity-place counterpart of the finite-place descent
used in Frobenius-coset averaging.  The generic part first identifies rational
infinity places of an intermediate function field with the unique top places
above them.  Under unramifiedness, a top infinity place of maximal possible
degree fixed by a generator of the relative Galois group descends to a
rational infinity place.

For an exact constant extension, every top infinity-place degree is divisible
by the constant-field degree.  This is obtained from the reciprocal
normalization presentation, whose equivalence with the actual infinity-place
type is already exhaustive.
-/

open scoped Pointwise Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


section GenericInfinityDescent

variable (K M T : Type*) [Field K] [DecidableEq K]
  [DecidableEq (RatFunc K)] [Field M] [Field T]
  [Algebra (RatFunc K) M] [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M]
  [Algebra (RatFunc K) T] [FiniteDimensional (RatFunc K) T]
  [Algebra.IsSeparable (RatFunc K) T]
  [Algebra M T] [IsScalarTower (RatFunc K) M T]
  [FiniteDimensional M T] [IsGalois M T]

/-- If every top infinity-place degree is divisible by the relative field
degree, then every rational infinity place downstairs has a unique top place
above it. -/
theorem rationalInfinityPlace_fiber_card_eq_one_of_finrank_dvd_degree
    (hdegree : ∀ Q : FiniteExtensionInfinityPlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inr Q))
    (P : FiniteExtensionRationalInfinityPlace K M) :
    Fintype.card (InfinityPlaceUnderFiber K M T P.1) = 1 := by
  obtain ⟨Q, hQ⟩ := infinityPlaceUnder_surjective K M T P.1
  let Q₀ : InfinityPlaceUnderFiber K M T P.1 := ⟨Q, hQ⟩
  have hplaceDegree :=
    finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg K M T Q
  have hrelative : infinityPlaceRelativeInertiaDeg K M T Q =
      finiteExtensionPlaceDegree K T (.inr Q) := by
    rw [hQ] at hplaceDegree
    simpa [P.2] using hplaceDegree.symm
  have hm_dvd_f : Module.finrank M T ∣
      infinityPlaceRelativeInertiaDeg K M T Q := by
    rw [hrelative]
    exact hdegree Q
  have hfiber :=
    infinityPlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
      K M T P.1 Q₀
  dsimp [Q₀] at hfiber
  have hf_dvd_m : infinityPlaceRelativeInertiaDeg K M T Q ∣
      Module.finrank M T := by
    rw [← hfiber]
    exact dvd_mul_left _ _
  have hf : infinityPlaceRelativeInertiaDeg K M T Q =
      Module.finrank M T := Nat.dvd_antisymm hf_dvd_m hm_dvd_f
  have hmpos : 0 < Module.finrank M T := Module.finrank_pos
  have hproduct :
      Fintype.card (InfinityPlaceUnderFiber K M T P.1) *
          infinityPlaceRelativeRamificationIdx K M T Q = 1 := by
    apply Nat.eq_of_mul_eq_mul_right hmpos
    simpa [Nat.mul_assoc, hf] using hfiber
  exact Nat.eq_one_of_dvd_one
    ⟨infinityPlaceRelativeRamificationIdx K M T Q, hproduct.symm⟩

/-- Under the same degree-divisibility hypothesis, every relative Galois
automorphism fixes every infinity place above a rational infinity place. -/
theorem infinityPlaceGalSmul_eq_self_over_rationalInfinityPlace_of_finrank_dvd_degree
    (hdegree : ∀ Q : FiniteExtensionInfinityPlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inr Q))
    (P : FiniteExtensionRationalInfinityPlace K M)
    (Q : FiniteExtensionInfinityPlace K T)
    (hQ : infinityPlaceUnder K M T Q = P.1)
    (sigma : T ≃ₐ[M] T) :
    infinityPlaceGalSmul K M T sigma Q = Q := by
  letI := infinityIntegralClosureGalAction K M T
  letI := infinityPlaceUnderFiberGalAction K M T P.1
  have hcard :=
    rationalInfinityPlace_fiber_card_eq_one_of_finrank_dvd_degree
      K M T hdegree P
  obtain ⟨Q₀, hQ₀⟩ := Fintype.card_eq_one_iff.mp hcard
  let x : InfinityPlaceUnderFiber K M T P.1 := ⟨Q, hQ⟩
  let y : InfinityPlaceUnderFiber K M T P.1 :=
    ⟨infinityPlaceGalSmul K M T sigma Q, by
      rw [infinityPlaceUnder_infinityPlaceGalSmul, hQ]⟩
  have hxy : x = y := (hQ₀ x).trans (hQ₀ y).symm
  exact congrArg Subtype.val hxy |>.symm

/-- A rational infinity place together with its top infinity-place lift. -/
abbrev RationalInfinityPlaceLift :=
  Σ P : FiniteExtensionRationalInfinityPlace K M,
    InfinityPlaceUnderFiber K M T P.1

/-- Projection from rational infinity-place lifts is an equivalence when
every top degree is divisible by the relative degree. -/
noncomputable def rationalInfinityPlaceEquivLift
    (hdegree : ∀ Q : FiniteExtensionInfinityPlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inr Q)) :
    FiniteExtensionRationalInfinityPlace K M ≃
      RationalInfinityPlaceLift K M T := by
  let projection : RationalInfinityPlaceLift K M T →
      FiniteExtensionRationalInfinityPlace K M := fun x => x.1
  refine (Equiv.ofBijective projection ⟨?_, ?_⟩).symm
  · rintro ⟨P, Q⟩ ⟨P', Q'⟩ h
    dsimp only [projection] at h
    subst P'
    have hcard :=
      rationalInfinityPlace_fiber_card_eq_one_of_finrank_dvd_degree
        K M T hdegree P
    obtain ⟨Q₀, hQ₀⟩ := Fintype.card_eq_one_iff.mp hcard
    exact Sigma.ext rfl <| heq_of_eq <|
      (hQ₀ Q).trans (hQ₀ Q').symm
  · intro P
    obtain ⟨Q, hQ⟩ := infinityPlaceUnder_surjective K M T P.1
    exact ⟨⟨P, Q, hQ⟩, rfl⟩

/-- Every lift of a rational infinity place is fixed by every relative
Galois automorphism under the degree-divisibility hypothesis. -/
theorem rationalInfinityPlaceLift_fixed
    (hdegree : ∀ Q : FiniteExtensionInfinityPlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inr Q))
    (sigma : T ≃ₐ[M] T) (x : RationalInfinityPlaceLift K M T) :
    infinityPlaceGalSmul K M T sigma x.2.1 = x.2.1 :=
  infinityPlaceGalSmul_eq_self_over_rationalInfinityPlace_of_finrank_dvd_degree
    K M T hdegree x.1 x.2.1 x.2.2 sigma

/-- If a generator fixes a top infinity place, then generation,
unramifiedness, and maximal top degree force its restriction to have degree
one. -/
theorem infinityPlaceUnder_degree_eq_one_of_generator_fixed
    (sigma : T ≃ₐ[M] T)
    (hgen : Subgroup.zpowers sigma = ⊤)
    (Q : FiniteExtensionInfinityPlace K T)
    (hfixed : infinityPlaceGalSmul K M T sigma Q = Q)
    (hunramified : infinityPlaceRelativeRamificationIdx K M T Q = 1)
    (htopDegree : finiteExtensionPlaceDegree K T (.inr Q) =
      Module.finrank M T) :
    finiteExtensionPlaceDegree K M
      (.inr (infinityPlaceUnder K M T Q)) = 1 := by
  let P := infinityPlaceUnder K M T Q
  let Q₀ : InfinityPlaceUnderFiber K M T P := ⟨Q, rfl⟩
  letI := infinityPlaceGalAction K M T
  have hsigma : sigma ∈
      MulAction.stabilizer (T ≃ₐ[M] T) Q := by
    rw [MulAction.mem_stabilizer_iff]
    exact hfixed
  have hall (tau : T ≃ₐ[M] T) :
      infinityPlaceGalSmul K M T tau Q = Q := by
    have hle : Subgroup.zpowers sigma ≤
        MulAction.stabilizer (T ≃ₐ[M] T) Q :=
      Subgroup.zpowers_le.mpr hsigma
    have htau : tau ∈ MulAction.stabilizer (T ≃ₐ[M] T) Q := by
      apply hle
      rw [hgen]
      exact Subgroup.mem_top tau
    have hfix := MulAction.mem_stabilizer_iff.mp htau
    change infinityPlaceGalSmul K M T tau Q = Q at hfix
    exact hfix
  letI := infinityPlaceUnderFiberGalAction K M T P
  letI : MulAction.IsPretransitive (T ≃ₐ[M] T)
      (InfinityPlaceUnderFiber K M T P) :=
    infinityPlaceUnderFiberGalAction_isPretransitive K M T P
  have hcard : Fintype.card (InfinityPlaceUnderFiber K M T P) = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨Q₀, ?_⟩
    intro R
    obtain ⟨tau, htau⟩ :=
      MulAction.exists_smul_eq (T ≃ₐ[M] T) Q₀ R
    calc
      R = tau • Q₀ := htau.symm
      _ = Q₀ := by
        apply Subtype.ext
        exact hall tau
  have hfundamental :=
    infinityPlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
      K M T P Q₀
  dsimp [Q₀] at hfundamental
  have hinertia : infinityPlaceRelativeInertiaDeg K M T Q =
      Module.finrank M T := by
    simpa only [hcard, hunramified, one_mul] using hfundamental
  have htower :=
    finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg K M T Q
  rw [htopDegree, hinertia] at htower
  apply Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := M) (M := T))
  simpa only [one_mul] using htower.symm

/-- Every lift of a rational infinity place has top degree equal to the
relative field degree under the degree-divisibility hypothesis. -/
theorem rationalInfinityPlace_lift_degree_eq_finrank_of_finrank_dvd_degree
    (hdegree : ∀ Q : FiniteExtensionInfinityPlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inr Q))
    (P : FiniteExtensionRationalInfinityPlace K M)
    (Q : FiniteExtensionInfinityPlace K T)
    (hQ : infinityPlaceUnder K M T Q = P.1) :
    finiteExtensionPlaceDegree K T (.inr Q) = Module.finrank M T := by
  let Q₀ : InfinityPlaceUnderFiber K M T P.1 := ⟨Q, hQ⟩
  have htower :=
    finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg K M T Q
  have hrelative : infinityPlaceRelativeInertiaDeg K M T Q =
      finiteExtensionPlaceDegree K T (.inr Q) := by
    rw [hQ] at htower
    simpa only [P.2, one_mul] using htower.symm
  have hm_dvd_f : Module.finrank M T ∣
      infinityPlaceRelativeInertiaDeg K M T Q := by
    rw [hrelative]
    exact hdegree Q
  have hfundamental :=
    infinityPlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
      K M T P.1 Q₀
  dsimp [Q₀] at hfundamental
  have hf_dvd_m : infinityPlaceRelativeInertiaDeg K M T Q ∣
      Module.finrank M T := by
    rw [← hfundamental]
    exact dvd_mul_left _ _
  exact hrelative.symm.trans (Nat.dvd_antisymm hf_dvd_m hm_dvd_f)

/-- Rational infinity places are equivalent to generator-fixed top infinity
places of relative-degree-sized absolute degree, once the relative extension
is unramified and every top degree is divisible by the relative degree. -/
noncomputable def rationalInfinityPlaceEquivGeneratorFixedPlace
    (hdegree : ∀ Q : FiniteExtensionInfinityPlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inr Q))
    (sigma : T ≃ₐ[M] T)
    (hgen : Subgroup.zpowers sigma = ⊤)
    (hunramified : ∀ Q : FiniteExtensionInfinityPlace K T,
      infinityPlaceRelativeRamificationIdx K M T Q = 1) :
    FiniteExtensionRationalInfinityPlace K M ≃
      {Q : FiniteExtensionInfinityPlace K T //
        finiteExtensionPlaceDegree K T (.inr Q) = Module.finrank M T ∧
          infinityPlaceGalSmul K M T sigma Q = Q} := by
  let e := rationalInfinityPlaceEquivLift K M T hdegree
  refine
    { toFun := fun P => by
        let x := e P
        exact ⟨x.2.1,
          rationalInfinityPlace_lift_degree_eq_finrank_of_finrank_dvd_degree
            K M T hdegree x.1 x.2.1 x.2.2,
          rationalInfinityPlaceLift_fixed K M T hdegree sigma x⟩
      invFun := fun Q =>
        ⟨infinityPlaceUnder K M T Q.1,
          infinityPlaceUnder_degree_eq_one_of_generator_fixed K M T sigma
            hgen Q.1 Q.2.2 (hunramified Q.1) Q.2.1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro P
    apply Subtype.ext
    let x := e P
    have hx1 : x.1 = P := by
      change e.symm (e P) = P
      exact e.symm_apply_apply P
    exact x.2.2.trans (congrArg Subtype.val hx1)
  · intro Q
    apply Subtype.ext
    let P : FiniteExtensionRationalInfinityPlace K M :=
      ⟨infinityPlaceUnder K M T Q.1,
        infinityPlaceUnder_degree_eq_one_of_generator_fixed K M T sigma
          hgen Q.1 Q.2.2 (hunramified Q.1) Q.2.1⟩
    let x := e P
    have hx1 : x.1 = P := by
      change e.symm (e P) = P
      exact e.symm_apply_apply P
    let xFiber : InfinityPlaceUnderFiber K M T P.1 :=
      ⟨x.2.1, x.2.2.trans (congrArg Subtype.val hx1)⟩
    let qFiber : InfinityPlaceUnderFiber K M T P.1 := ⟨Q.1, rfl⟩
    have hcard :=
      rationalInfinityPlace_fiber_card_eq_one_of_finrank_dvd_degree
        K M T hdegree P
    obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.mp hcard
    have hxy : xFiber = qFiber := (hz xFiber).trans (hz qFiber).symm
    change x.2.1 = Q.1
    exact congrArg Subtype.val hxy

/-- Relative automorphisms over two intermediate fields induce the same
action on top infinity places when their underlying top-field maps agree. -/
theorem infinityPlaceGalSmul_eq_of_apply_eq
    (K M₁ M₂ T : Type*) [Field K] [DecidableEq K]
    [DecidableEq (RatFunc K)]
    [Field M₁] [Algebra (RatFunc K) M₁]
    [FiniteDimensional (RatFunc K) M₁]
    [Algebra.IsSeparable (RatFunc K) M₁]
    [Field M₂] [Algebra (RatFunc K) M₂]
    [FiniteDimensional (RatFunc K) M₂]
    [Algebra.IsSeparable (RatFunc K) M₂]
    [Field T] [Algebra (RatFunc K) T]
    [FiniteDimensional (RatFunc K) T]
    [Algebra.IsSeparable (RatFunc K) T]
    [Algebra M₁ T] [IsScalarTower (RatFunc K) M₁ T]
    [FiniteDimensional M₁ T] [IsGalois M₁ T]
    [Algebra M₂ T] [IsScalarTower (RatFunc K) M₂ T]
    [FiniteDimensional M₂ T] [IsGalois M₂ T]
    (g₁ : T ≃ₐ[M₁] T) (g₂ : T ≃ₐ[M₂] T)
    (happly : ∀ x : T, g₁ x = g₂ x)
    (Q : FiniteExtensionInfinityPlace K T) :
    infinityPlaceGalSmul K M₁ T g₁ Q =
      infinityPlaceGalSmul K M₂ T g₂ Q := by
  let V := RatFuncInfinityIntegers K
  let A := RatFuncInfinityIntegralClosure K T
  let A₁ := RatFuncInfinityIntegralClosure K M₁
  let A₂ := RatFuncInfinityIntegralClosure K M₂
  letI : Algebra V (RatFunc K) :=
    RingHom.toAlgebra
      (SubringClass.subtype ((RatFunc.inftyValuation K).integer))
  letI : SMul V (RatFunc K) := Algebra.toSMul
  letI : Module V (RatFunc K) := Algebra.toModule
  letI : IsFractionRing V (RatFunc K) :=
    (Valuation.integer.integers (RatFunc.inftyValuation K)).isFractionRing
  letI : Algebra V M₁ :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) M₁).comp (algebraMap V (RatFunc K)))
  letI : SMul V M₁ := Algebra.toSMul
  letI : Module V M₁ := Algebra.toModule
  letI : IsScalarTower V (RatFunc K) M₁ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra V M₂ :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) M₂).comp (algebraMap V (RatFunc K)))
  letI : SMul V M₂ := Algebra.toSMul
  letI : Module V M₂ := Algebra.toModule
  letI : IsScalarTower V (RatFunc K) M₂ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra V T :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) T).comp (algebraMap V (RatFunc K)))
  letI : SMul V T := Algebra.toSMul
  letI : Module V T := Algebra.toModule
  letI : IsScalarTower V (RatFunc K) T :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure A₁ V M₁ :=
    integralClosure.isIntegralClosure V M₁
  letI : IsScalarTower V A₁ M₁ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing A₁ M₁ :=
    IsIntegralClosure.isFractionRing_of_finite_extension V (RatFunc K) M₁ A₁
  letI : IsIntegralClosure A₂ V M₂ :=
    integralClosure.isIntegralClosure V M₂
  letI : IsScalarTower V A₂ M₂ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing A₂ M₂ :=
    IsIntegralClosure.isFractionRing_of_finite_extension V (RatFunc K) M₂ A₂
  letI : IsIntegralClosure A V T :=
    integralClosure.isIntegralClosure V T
  letI : IsScalarTower V A T :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing A T :=
    IsIntegralClosure.isFractionRing_of_finite_extension V (RatFunc K) T A
  letI : Algebra A₁ A := (infinityIntegralClosureMap K M₁ T).toAlgebra
  letI : SMul A₁ A := Algebra.toSMul
  letI : Module A₁ A := Algebra.toModule
  letI : IsScalarTower A₁ M₁ T := inferInstance
  letI : Algebra.IsIntegral V A₁ :=
    IsIntegralClosure.isIntegral_algebra V M₁
  letI : IsScalarTower V A₁ T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap (RatFunc K) T
          (algebraMap V (RatFunc K) x) =
        algebraMap M₁ T
          (algebraMap (RatFunc K) M₁
            (algebraMap V (RatFunc K) x))
    exact IsScalarTower.algebraMap_apply (RatFunc K) M₁ T _
  letI : IsScalarTower A₁ A T :=
    ⟨fun r t x => by
      simp only [Algebra.smul_def, map_mul]
      rw [show algebraMap A T (algebraMap A₁ A r) =
          algebraMap A₁ T r by rfl]
      ring⟩
  letI : IsIntegralClosure A A₁ T :=
    IsIntegralClosure.tower_top (R := V)
  letI : Algebra A₂ A := (infinityIntegralClosureMap K M₂ T).toAlgebra
  letI : SMul A₂ A := Algebra.toSMul
  letI : Module A₂ A := Algebra.toModule
  letI : IsScalarTower A₂ M₂ T := inferInstance
  letI : Algebra.IsIntegral V A₂ :=
    IsIntegralClosure.isIntegral_algebra V M₂
  letI : IsScalarTower V A₂ T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap (RatFunc K) T
          (algebraMap V (RatFunc K) x) =
        algebraMap M₂ T
          (algebraMap (RatFunc K) M₂
            (algebraMap V (RatFunc K) x))
    exact IsScalarTower.algebraMap_apply (RatFunc K) M₂ T _
  letI : IsScalarTower A₂ A T :=
    ⟨fun r t x => by
      simp only [Algebra.smul_def, map_mul]
      rw [show algebraMap A T (algebraMap A₂ A r) =
          algebraMap A₂ T r by rfl]
      ring⟩
  letI : IsIntegralClosure A A₂ T :=
    IsIntegralClosure.tower_top (R := V)
  letI : MulSemiringAction (T ≃ₐ[M₁] T) A :=
    infinityIntegralClosureGalAction K M₁ T
  letI : MulSemiringAction (T ≃ₐ[M₂] T) A :=
    infinityIntegralClosureGalAction K M₂ T
  have hsmul (a₁ : T ≃ₐ[M₁] T) (a₂ : T ≃ₐ[M₂] T)
      (ha : ∀ x : T, a₁ x = a₂ x) (x : A) : a₁ • x = a₂ • x := by
    apply Subtype.ext
    calc
      ((a₁ • x : A) : T) = a₁ (x : T) := by
        change algebraMap A T ((galRestrict A₁ M₁ T A a₁) x) =
          a₁ (algebraMap A T x)
        exact algebraMap_galRestrict_apply A₁ a₁ x
      _ = a₂ (x : T) := ha _
      _ = ((a₂ • x : A) : T) := by
        change a₂ (algebraMap A T x) =
          algebraMap A T ((galRestrict A₂ M₂ T A a₂) x)
        exact (algebraMap_galRestrict_apply A₂ a₂ x).symm
  have happly_inv (x : T) : g₁⁻¹ x = g₂⁻¹ x := by
    apply g₂.injective
    calc
      g₂ (g₁⁻¹ x) = g₁ (g₁⁻¹ x) := (happly _).symm
      _ = x := g₁.apply_symm_apply x
      _ = g₂ (g₂⁻¹ x) := (g₂.apply_symm_apply x).symm
  apply Subtype.ext
  change g₁ • Q.1 = g₂ • Q.1
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    hsmul g₁⁻¹ g₂⁻¹ happly_inv x]

end GenericInfinityDescent

variable (C N S : Type*) [Field C] [Fintype C]
  [DecidableEq C] [DecidableEq (RatFunc C)]
  [Field N] [Algebra (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Field S] [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [Finite S] [DecidableEq S] [DecidableEq (RatFunc S)]

local instance twistInfinityConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance twistInfinityConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

section ExactConstantExtensionInfinityDegree

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- Every infinity place of the exact constant extension, viewed over the
original constants `C`, has degree divisible by `[S : C]`. -/
theorem exactConstantExtensionInfinityPlace_finrank_constants_dvd_degree
    (Q :
      letI : DecidableEq C := infinityBridgeDecidableEqConstants C
      letI : DecidableEq (RatFunc C) :=
        infinityBridgeDecidableEqRatFuncConstants C
      letI : DecidableEq S := infinityBridgeDecidableEqConstants S
      letI : DecidableEq (RatFunc S) :=
        infinityBridgeDecidableEqRatFuncConstants S
      letI : Field (ExactConstantExtension C N S) :=
        exactConstantExtensionField C N S hExact
      letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
        exactConstantExtensionBaseAlgebra C (RatFunc C) N S
      FiniteExtensionInfinityPlace C (ExactConstantExtension C N S)) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    Module.finrank C S ∣ finiteExtensionPlaceDegree C
      (ExactConstantExtension C N S) (.inr Q) := by
  letI : DecidableEq C := infinityBridgeDecidableEqConstants C
  letI : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  letI : DecidableEq S := infinityBridgeDecidableEqConstants S
  letI : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra (RatFunc S) T :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : SMul (RatFunc S) T := Algebra.toSMul
  letI : Module (RatFunc S) T := Algebra.toModule
  letI : FiniteDimensional (RatFunc S) T :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc S) T :=
    isSeparable_over_extendedRatFunc C S N hExact
  let e := exactConstantExtensionPresentedInfinityPlaceEquiv
    C S N hExact
  let q := e.symm Q
  have hdegree :=
    exactConstantExtensionPresentedInfinityPlace_degree_baseChange
      C S N hExact q
  have heq : e q = Q := e.apply_symm_apply Q
  rw [heq] at hdegree
  rw [hdegree]
  exact dvd_mul_right _ _

end ExactConstantExtensionInfinityDegree

section FrobeniusTwistInfinityUnramified

/-- Powers of the ambient twist act on enlarged constants by the
corresponding powers of finite-field Frobenius. -/
private theorem exactConstantExtensionFrobeniusTwist_zpow_includeLeft_infinity
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N) (k : ℤ) (s : S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    ((exactConstantExtensionFrobeniusTwist
        C (RatFunc C) N S hExact g) ^ k)
        (Algebra.TensorProduct.includeLeft
          (R := C) (S := C) (A := S) (B := N) s) =
      Algebra.TensorProduct.includeLeft
        (R := C) (S := C) (A := S) (B := N)
        (((FiniteField.frobeniusAlgEquivOfAlgebraic C S) ^ k) s) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  change
    ((exactConstantExtensionCombinedAutHom C (RatFunc C) N S
        (FiniteField.frobeniusAlgEquivOfAlgebraic C S, g)) ^ k)
        (Algebra.TensorProduct.includeLeft
          (R := C) (S := C) (A := S) (B := N) s) = _
  rw [← map_zpow]
  simp [Algebra.TensorProduct.includeLeft_apply,
    exactConstantExtensionCombinedAutHom,
    exactConstantExtensionConstantAutHom,
    exactConstantExtensionFunctionAutHom,
    exactConstantExtensionConstantAlgEquivOverBase,
    exactConstantExtensionFunctionAlgEquivOverBase]

/-- Every infinity place of the exact constant extension is unramified over a
Frobenius-twist fixed field, provided the twist has the full
constant-extension order. -/
theorem frobeniusTwistField_infinityPlace_ramificationIdx_eq_one
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N)
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    letI : Algebra (RatFunc C) F :=
      SubalgebraClass.toAlgebra F.toSubalgebra
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    letI : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra F (ExactConstantExtension C N S) := F.toAlgebra
    letI : SMul F (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module F (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) F
        (ExactConstantExtension C N S) := inferInstance
    letI : FiniteDimensional F (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    letI : IsGalois F (ExactConstantExtension C N S) :=
      isGalois_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    ∀ Q : FiniteExtensionInfinityPlace C (ExactConstantExtension C N S),
      infinityPlaceRelativeRamificationIdx C F
        (ExactConstantExtension C N S) Q = 1 := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra F T := F.toAlgebra
  letI : SMul F T := Algebra.toSMul
  letI : Module F T := Algebra.toModule
  letI : IsScalarTower (RatFunc C) F T := inferInstance
  letI : FiniteDimensional F T :=
    finiteDimensional_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  letI : IsGalois F T :=
    isGalois_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  let V := RatFuncInfinityIntegers C
  letI : Algebra V (RatFunc C) :=
    RingHom.toAlgebra
      (SubringClass.subtype ((RatFunc.inftyValuation C).integer))
  letI : SMul V (RatFunc C) := Algebra.toSMul
  letI : Module V (RatFunc C) := Algebra.toModule
  letI : IsFractionRing V (RatFunc C) :=
    (Valuation.integer.integers (RatFunc.inftyValuation C)).isFractionRing
  letI : Algebra V T :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) T).comp (algebraMap V (RatFunc C)))
  letI : SMul V T := Algebra.toSMul
  letI : Module V T := Algebra.toModule
  letI : IsScalarTower V (RatFunc C) T :=
    IsScalarTower.of_algebraMap_eq' rfl
  let A := RatFuncInfinityIntegralClosure C T
  let AF := RatFuncInfinityIntegralClosure C F
  letI : IsIntegralClosure AF V F :=
    integralClosure.isIntegralClosure V F
  letI : IsScalarTower V AF F :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing AF F :=
    IsIntegralClosure.isFractionRing_of_finite_extension V (RatFunc C) F AF
  letI : IsIntegralClosure A V T :=
    integralClosure.isIntegralClosure V T
  letI : IsScalarTower V A T :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing A T :=
    IsIntegralClosure.isFractionRing_of_finite_extension V (RatFunc C) T A
  letI : Algebra AF A := (infinityIntegralClosureMap C F T).toAlgebra
  letI : SMul AF A := Algebra.toSMul
  letI : Module AF A := Algebra.toModule
  letI : Algebra S A :=
    exactConstantExtensionInfinityIntegralClosureConstantAlgebra C S N hExact
  letI : IsScalarTower AF F T := inferInstance
  letI : Algebra.IsIntegral V AF :=
    IsIntegralClosure.isIntegral_algebra V F
  letI : IsScalarTower V AF T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap (RatFunc C) T
          (algebraMap V (RatFunc C) x) =
        algebraMap F T
          (algebraMap (RatFunc C) F
            (algebraMap V (RatFunc C) x))
    exact IsScalarTower.algebraMap_apply (RatFunc C) F T _
  letI : IsScalarTower AF A T :=
    ⟨fun r t x => by
      simp only [Algebra.smul_def, map_mul]
      rw [show algebraMap A T (algebraMap AF A r) =
          algebraMap AF T r by rfl]
      ring⟩
  letI : IsIntegralClosure A AF T :=
    IsIntegralClosure.tower_top (R := V)
  letI : IsDedekindDomain A :=
    IsIntegralClosure.isDedekindDomain V (RatFunc C) T A
  letI : MulSemiringAction (T ≃ₐ[F] T) A :=
    infinityIntegralClosureGalAction C F T
  dsimp only
  intro Q
  rw [← infinityPlaceInertiaGroup_card_eq_ramificationIdx C F T Q]
  have hInertia : infinityPlaceInertiaGroup C F T Q = ⊥ := by
    ext tau
    constructor
    · intro htau
      rw [Subgroup.mem_bot]
      let sigma := exactConstantExtensionFrobeniusTwist
        C (RatFunc C) N S hExact g
      let H := exactConstantExtensionFrobeniusTwistSubgroup
        C (RatFunc C) N S hExact g
      let e := IntermediateField.subgroupEquivAlgEquiv H
      let h : H := e.symm tau
      have he_apply (z : H) (x : T) : e z x = z.1 x := by
        change z.1.toEquiv x = z.1 x
        rfl
      have htau_apply (x : T) : tau x = h.1 x := by
        calc
          tau x = e h x := by
            exact congrArg (fun z : T ≃ₐ[F] T => z x)
              (e.apply_symm_apply tau).symm
          _ = h.1 x := he_apply h x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
      let frob := FiniteField.frobeniusAlgEquivOfAlgebraic C S
      have hfrob_apply (s : S) : (frob ^ k) s = s := by
        let a : A := algebraMap S A s
        have haction : tau • a = algebraMap S A ((frob ^ k) s) := by
          apply Subtype.ext
          calc
            ((tau • a : A) : T) = tau (a : T) := by
              change algebraMap A T ((galRestrict AF F T A tau) a) =
                tau (algebraMap A T a)
              exact algebraMap_galRestrict_apply AF tau a
            _ = h.1 (a : T) := htau_apply (a : T)
            _ = h.1 (Algebra.TensorProduct.includeLeft
                (R := C) (S := C) (A := S) (B := N) s) := by
              rfl
            _ = (sigma ^ k) (Algebra.TensorProduct.includeLeft
                (R := C) (S := C) (A := S) (B := N) s) := by
              exact congrArg
                (fun z : T ≃ₐ[RatFunc C] T =>
                  z (Algebra.TensorProduct.includeLeft
                    (R := C) (S := C) (A := S) (B := N) s))
                hk |>.symm
            _ = Algebra.TensorProduct.includeLeft
                (R := C) (S := C) (A := S) (B := N)
                ((frob ^ k) s) := by
              exact exactConstantExtensionFrobeniusTwist_zpow_includeLeft_infinity
                C N S hExact g k s
            _ = ((algebraMap S A ((frob ^ k) s) : A) : T) := by
              rfl
        have hmem : tau • a - a ∈ Q.1 := htau a
        have hmem' : algebraMap S A ((frob ^ k) s - s) ∈ Q.1 := by
          have heq : algebraMap S A ((frob ^ k) s - s) = tau • a - a := by
            calc
              algebraMap S A ((frob ^ k) s - s) =
                  algebraMap S A ((frob ^ k) s) - algebraMap S A s :=
                map_sub (algebraMap S A) _ _
              _ = algebraMap S A ((frob ^ k) s) - a := rfl
              _ = tau • a - a := congrArg (fun z : A => z - a) haction.symm
          exact heq.symm ▸ hmem
        let J : Ideal S := Q.1.comap (algebraMap S A)
        have hmemJ : (frob ^ k) s - s ∈ J := hmem'
        have hJne : J ≠ ⊤ := by
          exact Ideal.comap_ne_top (algebraMap S A) Q.2.1.ne_top
        have hJ : J = ⊥ := (Ideal.eq_bot_or_top J).resolve_right hJne
        have hs : (frob ^ k) s - s = 0 := by
          rw [hJ] at hmemJ
          simpa only [Ideal.mem_bot] using hmemJ
        exact sub_eq_zero.mp hs
      have hFrob : frob ^ k = 1 := by
        ext s
        exact hfrob_apply s
      have hkdiv : (Module.finrank C S : ℤ) ∣ k := by
        rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic C S]
        exact orderOf_dvd_iff_zpow_eq_one.mpr hFrob
      have hsigma : sigma ^ k = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one,
          orderOf_exactConstantExtensionFrobeniusTwist
            C (RatFunc C) N S hExact g hdiv]
        exact hkdiv
      have hambient : (h.1 : T ≃ₐ[RatFunc C] T) = 1 := by
        calc
          (h.1 : T ≃ₐ[RatFunc C] T) = sigma ^ k := hk.symm
          _ = 1 := hsigma
      have hh : h = 1 := Subtype.ext hambient
      calc
        tau = e h := (e.apply_symm_apply tau).symm
        _ = e 1 := congrArg e hh
        _ = 1 := map_one e
    · intro htau
      rw [Subgroup.mem_bot] at htau
      simp [htau]
  rw [hInertia]
  exact Nat.card_unique

end FrobeniusTwistInfinityUnramified

end

end BGS.HasseWeil
