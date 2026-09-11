/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Relative norms in finite separable extensions

Mathlib's theorem `Ideal.relNorm_eq_pow_of_isMaximal` assumes that the fraction field of the
base Dedekind domain is perfect.  For function fields the needed hypothesis is instead already
available in its sharp form: the particular fraction-field extension is separable.  This file
records that variant, using the same normal-closure argument as the Mathlib theorem.
-/

@[expose] public section

open Module
open UniqueFactorizationMonoid
open scoped nonZeroDivisors

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [IsTorsionFree R S]

/-- The relative norm of a maximal ideal in a finite separable extension is the corresponding
prime below, raised to the inertia degree.  This is the separable-extension variant of
`Ideal.relNorm_eq_pow_of_isMaximal`. -/
theorem relNorm_eq_pow_of_isMaximal_of_isSeparable
    [@Algebra.IsSeparable (FractionRing R) (FractionRing S) _ _
      (FractionRing.liftAlgebra R (FractionRing S))]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    relNorm R P = p ^ p.inertiaDeg' P := by
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra R L
  let E := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl
  let T : Type _ := integralClosure S E
  let : Algebra S T := inferInstance
  let : Algebra T E := inferInstance
  let : IsScalarTower S T E := inferInstance
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R E := ((algebraMap S E).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E
  let : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).2 <| by
    rw [IsScalarTower.algebraMap_eq R S E]
    exact (algebraMap L E).injective.comp (IsFractionRing.injective S L) |>.comp
      (FaithfulSMul.algebraMap_injective R S)
  let : IsScalarTower R S L := inferInstance
  let : FaithfulSMul R L := inferInstance
  let : IsScalarTower R L E := IsScalarTower.to₁₃₄ R S L E
  let : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  let : IsScalarTower R K E := IsScalarTower.to₁₂₄ R K L E
  let : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
  let : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).2 <| by
    intro x y hxy
    apply (algebraMap L E).injective.comp (IsFractionRing.injective S L)
    exact congrArg (fun z : T => (algebraMap T E) z) hxy
  let : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).2 <| by
    rw [IsScalarTower.algebraMap_eq R S T]
    exact (FaithfulSMul.algebraMap_injective S T).comp
      (FaithfulSMul.algebraMap_injective R S)
  let : FiniteDimensional K E :=
    normalClosure.is_finiteDimensional K L (AlgebraicClosure L)
  let : Algebra.IsSeparable K E := by
    rw [← le_separableClosure_iff]
    apply normalClosure_le_iff.mpr
    intro i
    have : Algebra.IsSeparable K i.fieldRange :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i)
    exact le_separableClosure K (AlgebraicClosure L) i.fieldRange
  let : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable K L E
  let : FiniteDimensional L E := Module.Finite.right K L E
  let : IsFractionRing T E :=
    IsIntegralClosure.isFractionRing_of_finite_extension S L E T
  let : Module.Finite S T := IsIntegralClosure.finite S L E T
  let : Module.Finite R T := Module.Finite.trans S T
  let : IsDedekindDomain T := integralClosure.isDedekindDomain S L E
  let : IsGalois K E := {
    to_isSeparable := inferInstance
    to_normal := normalClosure.normal K L (AlgebraicClosure L) }
  let algT : Algebra T (FractionRing T) := inferInstance
  let : Algebra T (FractionRing T) := algT
  let : Algebra R (FractionRing T) := inferInstance
  let : Algebra S (FractionRing T) := inferInstance
  let : FaithfulSMul R (FractionRing T) := inferInstance
  let : FaithfulSMul S (FractionRing T) := inferInstance
  let : Algebra K (FractionRing T) := FractionRing.liftAlgebra R (FractionRing T)
  let : Algebra L (FractionRing T) := FractionRing.liftAlgebra S (FractionRing T)
  let : IsScalarTower R K (FractionRing T) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing T)
  let : IsScalarTower S L (FractionRing T) :=
    FractionRing.isScalarTower_liftAlgebra S (FractionRing T)
  let : IsGalois K (FractionRing T) := by
    refine IsGalois.of_equiv_equiv (F := K) (E := E)
      (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
      (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
    ext
    simpa using! IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
      (FractionRing.algEquiv T E).symm _
  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    exists_maximal_ideal_liesOver_of_isIntegral P
  let : Q.IsMaximal := hQ₁
  let : Q.LiesOver P := hQ₂
  let : Q.LiesOver p := LiesOver.trans Q P p
  have h := relNorm_eq_pow_of_isPrime_isGalois Q p
  let : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois (FractionRing R) (FractionRing S) (FractionRing T)
  rw [inertiaDeg'_eq_inertiaDeg p P]
  rwa [← relNorm_relNorm R S, relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    inertiaDeg_tower (R := R) P Q, pow_mul, pow_left_inj (inertiaDeg_pos Q S).ne'] at h

/-- Relative norm preserves the weighted sum of prime factors, with each prime upstairs weighted
by its inertia degree over the prime below. -/
theorem sum_normalizedFactors_relNorm_of_isSeparable
    [@Algebra.IsSeparable (FractionRing R) (FractionRing S) _ _
      (FractionRing.liftAlgebra R (FractionRing S))]
    (I : Ideal S) (hI : I ≠ ⊥) (w : Ideal R → ℕ) :
    ((normalizedFactors (relNorm R I)).map w).sum =
      ((normalizedFactors I).map fun P =>
        (P.under R).inertiaDeg' P * w (P.under R)).sum := by
  classical
  let : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  have aux : ∀ s : Multiset (Ideal S), (∀ P ∈ s, Prime P) →
      ((normalizedFactors (relNorm R s.prod)).map w).sum =
        (s.map fun P => (P.under R).inertiaDeg' P * w (P.under R)).sum := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty =>
        rw [Multiset.prod_zero, map_one]
        simp only [normalizedFactors_one, Multiset.map_zero, Multiset.sum_zero]
    | @cons P s ih =>
        have hP : Prime P := hs P (Multiset.mem_cons_self P s)
        have hs' : ∀ Q ∈ s, Prime Q := fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
        have hP0 : P ≠ ⊥ := hP.ne_zero
        have hs0 : s.prod ≠ ⊥ := Multiset.prod_ne_zero fun h =>
          (hs' ⊥ h).ne_zero rfl
        let p : Ideal R := P.under R
        let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP0
        let : p.IsMaximal := Ideal.IsMaximal.under R P
        let : P.LiesOver p := ⟨rfl⟩
        have hp0 : p ≠ ⊥ := by
          intro hp
          have : P.LiesOver (⊥ : Ideal R) := hp ▸ (inferInstance : P.LiesOver p)
          exact hP0 (Ideal.eq_bot_of_liesOver_bot R P)
        have hnorm : relNorm R P = p ^ p.inertiaDeg' P :=
          relNorm_eq_pow_of_isMaximal_of_isSeparable P p
        have hnormP0 : relNorm R P ≠ ⊥ := (relNorm_eq_bot_iff.not.mpr hP0)
        have hnorms0 : relNorm R s.prod ≠ ⊥ :=
          relNorm_eq_bot_iff.not.mpr hs0
        rw [Multiset.prod_cons, map_mul, normalizedFactors_mul hnormP0 hnorms0,
          Multiset.map_add, Multiset.sum_add, hnorm, normalizedFactors_pow,
          UniqueFactorizationMonoid.normalizedFactors_irreducible
            (Ideal.prime_of_isPrime hp0
              (inferInstance : p.IsMaximal).isPrime).irreducible,
          normalize_eq, Multiset.nsmul_singleton]
        simp [ih hs', p]
  let s := normalizedFactors I
  have hsprod : s.prod = I := prod_normalizedFactors_eq_self hI
  calc
    ((normalizedFactors (relNorm R I)).map w).sum =
        ((normalizedFactors (relNorm R s.prod)).map w).sum := by rw [hsprod]
    _ = (s.map fun P => (P.under R).inertiaDeg' P * w (P.under R)).sum := by
      apply aux s
      intro P hP
      exact UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    _ = ((normalizedFactors I).map fun P =>
        (P.under R).inertiaDeg' P * w (P.under R)).sum := rfl

end Ideal
