/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Fiber

/-!
# Extending derivations through local Dedekind rings

Lift derivations uniquely through formally etale maps and apply this to unramified localizations
and primes away from the different.
-/

namespace BGS.CorvajaZannier

noncomputable section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable {C S T U : Type*}
  [CommRing C] [CommRing S] [CommRing T] [CommRing U]
  [Algebra C S] [Algebra C T] [Algebra S T]
  [Algebra C U] [Algebra S U] [Algebra T U]
  [IsScalarTower C S T] [IsScalarTower C S U]
  [IsScalarTower C T U] [IsScalarTower S T U]

/-- A derivation over `C` which vanishes on `S` is an `S`-derivation. -/
def derivationToRelative
    (D : Derivation C T U)
    (hD : ∀ s : S, D (algebraMap S T s) = 0) :
    Derivation S T U where
  toLinearMap :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := by
        intro s t
        rw [show s • t = algebraMap S T s * t by
          exact Algebra.smul_def s t]
        rw [D.leibniz, hD, smul_zero, add_zero,
          IsScalarTower.algebraMap_smul T, RingHom.id_apply] }
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

omit [Algebra C S] [IsScalarTower C S T] [IsScalarTower C S U]
  [IsScalarTower C T U] in
@[simp]
theorem derivationToRelative_apply
    (D : Derivation C T U)
    (hD : ∀ s : S, D (algebraMap S T s) = 0) (t : T) :
    derivationToRelative D hD t = D t :=
  rfl

omit [Algebra C S] [IsScalarTower C S T] [IsScalarTower C S U]
  [IsScalarTower C T U] in
/-- Relative formal unramifiedness makes a `C`-derivation into a `T`-module
unique once its restriction to `S` is fixed. -/
theorem derivation_ext_of_formallyUnramified
    [Algebra.FormallyUnramified S T]
    (D₁ D₂ : Derivation C T U)
    (hD : ∀ s : S, D₁ (algebraMap S T s) = D₂ (algebraMap S T s)) :
    D₁ = D₂ := by
  let E : Derivation C T U := D₁ - D₂
  have hE : ∀ s : S, E (algebraMap S T s) = 0 := by
    intro s
    exact sub_eq_zero.mpr (hD s)
  let Erel : Derivation S T U := derivationToRelative E hE
  have hLift : Erel.liftKaehlerDifferential = 0 := by
    apply LinearMap.ext
    intro x
    rw [show x = 0 from Subsingleton.elim x 0]
    simp
  have hErel : Erel = 0 := by
    rw [← Erel.liftKaehlerDifferential_comp, hLift]
    rfl
  apply Derivation.ext
  intro t
  have := Derivation.congr_fun hErel t
  apply sub_eq_zero.mp
  simpa [Erel, E, derivationToRelative] using this

/-- Lift a `C`-derivation through a formally étale `S`-algebra. The target
may be any compatible `T`-algebra. -/
noncomputable def formallyEtaleDerivationLift
    [Algebra.FormallyEtale S T]
    (D : Derivation C S U) : Derivation C T U :=
  KaehlerDifferential.linearMapEquivDerivation C T
    ((D.liftKaehlerDifferential.liftBaseChange T).comp
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale C S T).symm.toLinearMap)

@[simp]
theorem formallyEtaleDerivationLift_algebraMap
    [Algebra.FormallyEtale S T]
    (D : Derivation C S U) (s : S) :
    formallyEtaleDerivationLift D (algebraMap S T s) = D s := by
  change (D.liftKaehlerDifferential.liftBaseChange T)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale C S T).symm
      (KaehlerDifferential.D C T (algebraMap S T s))) = D s
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

/-- The formally étale lift is the unique extension of the given derivation. -/
theorem formallyEtaleDerivationLift_unique
    [Algebra.FormallyEtale S T]
    (D : Derivation C S U) (E : Derivation C T U)
    (hE : ∀ s : S, E (algebraMap S T s) = D s) :
    E = formallyEtaleDerivationLift D := by
  apply derivation_ext_of_formallyUnramified (S := S)
    E (formallyEtaleDerivationLift D)
  intro s
  rw [hE, formallyEtaleDerivationLift_algebraMap]

/-- Extend a derivation taking values in the base ring to one taking values
in the formally étale algebra. -/
noncomputable def formallyEtaleDerivationExtension
    [Algebra.FormallyEtale S T]
    (D : Derivation C S S) : Derivation C T T :=
  formallyEtaleDerivationLift ((Algebra.linearMap S T).compDer D)

@[simp]
theorem formallyEtaleDerivationExtension_algebraMap
    [Algebra.FormallyEtale S T]
    (D : Derivation C S S) (s : S) :
    formallyEtaleDerivationExtension D (algebraMap S T s) =
      algebraMap S T (D s) := by
  simp [formallyEtaleDerivationExtension]

omit [IsScalarTower C S U] in
/-- If an ambient derivation preserves the base local ring, then it preserves
every formally étale extension ring inside the ambient algebra. -/
theorem formallyEtale_derivation_preserves
    [Algebra.FormallyEtale S T]
    (D : Derivation C S S) (E : Derivation C U U)
    (hE : ∀ s : S, E (algebraMap S U s) = algebraMap S U (D s)) :
    ∃ D' : Derivation C T T,
      (∀ s : S, D' (algebraMap S T s) = algebraMap S T (D s)) ∧
      ∀ t : T, E (algebraMap T U t) = algebraMap T U (D' t) := by
  let D' : Derivation C T T := formallyEtaleDerivationExtension D
  refine ⟨D', formallyEtaleDerivationExtension_algebraMap D, ?_⟩
  have hDer : E.compAlgebraMap T =
      (Algebra.linearMap T U).compDer D' := by
    apply derivation_ext_of_formallyUnramified (S := S)
    intro s
    change E (algebraMap T U (algebraMap S T s)) =
      algebraMap T U (D' (algebraMap S T s))
    rw [show D' = formallyEtaleDerivationExtension D from rfl,
      formallyEtaleDerivationExtension_algebraMap]
    simpa only [IsScalarTower.algebraMap_apply S T U] using hE s
  intro t
  exact Derivation.congr_fun hDer t

/-- A finite torsion-free extension of Dedekind domains is formally étale on
the local branch at every unramified prime. -/
theorem dedekindLocal_formallyEtale_of_isUnramifiedAt
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B]
    (p : Ideal A) (Q : Ideal B) [p.IsPrime] [Q.IsPrime] [Q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime Q)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime Q)]
    [Algebra.IsUnramifiedAt A Q] :
    Algebra.FormallyEtale (Localization.AtPrime p)
      (Localization.AtPrime Q) := by
  let : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.FormallyEtale A (Localization.AtPrime Q) :=
    Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat Q
  exact Algebra.FormallyEtale.of_restrictScalars
    (R := A) (A := Localization.AtPrime p) (B := Localization.AtPrime Q)

/-- Outside the different ideal, the corresponding map of Dedekind local
rings is formally étale. -/
theorem dedekindLocal_formallyEtale_of_not_dvd_different
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (p : Ideal A) (Q : Ideal B) [p.IsPrime] [Q.IsPrime] [Q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime Q)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime Q)]
    (hQ : ¬ Q ∣ differentIdeal A B) :
    Algebra.FormallyEtale (Localization.AtPrime p)
      (Localization.AtPrime Q) := by
  let : Algebra.IsUnramifiedAt A Q :=
    not_dvd_differentIdeal_iff.mp hQ
  exact dedekindLocal_formallyEtale_of_isUnramifiedAt p Q

/-- An ambient derivation preserving the base Dedekind local ring preserves
an unramified local branch of a finite torsion-free Dedekind extension. -/
theorem dedekindLocal_derivation_preserves_of_isUnramifiedAt
    {A B C U : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing U]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B]
    (p : Ideal A) (Q : Ideal B) [p.IsPrime] [Q.IsPrime] [Q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime Q)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime Q)]
    [Algebra C (Localization.AtPrime p)]
    [Algebra C (Localization.AtPrime Q)]
    [Algebra C U]
    [Algebra (Localization.AtPrime p) U]
    [Algebra (Localization.AtPrime Q) U]
    [IsScalarTower C (Localization.AtPrime p) (Localization.AtPrime Q)]
    [IsScalarTower C (Localization.AtPrime p) U]
    [IsScalarTower C (Localization.AtPrime Q) U]
    [IsScalarTower (Localization.AtPrime p) (Localization.AtPrime Q) U]
    [Algebra.IsUnramifiedAt A Q]
    (D : Derivation C (Localization.AtPrime p) (Localization.AtPrime p))
    (E : Derivation C U U)
    (hE : ∀ s : Localization.AtPrime p,
      E (algebraMap (Localization.AtPrime p) U s) =
        algebraMap (Localization.AtPrime p) U (D s)) :
    ∃ D' : Derivation C (Localization.AtPrime Q) (Localization.AtPrime Q),
      (∀ s : Localization.AtPrime p,
        D' (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q) s) =
          algebraMap (Localization.AtPrime p) (Localization.AtPrime Q) (D s)) ∧
      ∀ t : Localization.AtPrime Q,
        E (algebraMap (Localization.AtPrime Q) U t) =
          algebraMap (Localization.AtPrime Q) U (D' t) := by
  let : Algebra.FormallyEtale (Localization.AtPrime p)
      (Localization.AtPrime Q) :=
    dedekindLocal_formallyEtale_of_isUnramifiedAt p Q
  exact formallyEtale_derivation_preserves D E hE

/-- Away from the different, an ambient derivation preserving the base local
ring preserves the selected extension DVR. This is the direct local
derivation-extension statement used in the Corvaja--Zannier argument. -/
theorem dedekindLocal_derivation_preserves_of_not_dvd_different
    {A B C U : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing U]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (p : Ideal A) (Q : Ideal B) [p.IsPrime] [Q.IsPrime] [Q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime Q)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime Q)]
    [Algebra C (Localization.AtPrime p)]
    [Algebra C (Localization.AtPrime Q)]
    [Algebra C U]
    [Algebra (Localization.AtPrime p) U]
    [Algebra (Localization.AtPrime Q) U]
    [IsScalarTower C (Localization.AtPrime p) (Localization.AtPrime Q)]
    [IsScalarTower C (Localization.AtPrime p) U]
    [IsScalarTower C (Localization.AtPrime Q) U]
    [IsScalarTower (Localization.AtPrime p) (Localization.AtPrime Q) U]
    (hQ : ¬ Q ∣ differentIdeal A B)
    (D : Derivation C (Localization.AtPrime p) (Localization.AtPrime p))
    (E : Derivation C U U)
    (hE : ∀ s : Localization.AtPrime p,
      E (algebraMap (Localization.AtPrime p) U s) =
        algebraMap (Localization.AtPrime p) U (D s)) :
    ∃ D' : Derivation C (Localization.AtPrime Q) (Localization.AtPrime Q),
      (∀ s : Localization.AtPrime p,
        D' (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q) s) =
          algebraMap (Localization.AtPrime p) (Localization.AtPrime Q) (D s)) ∧
      ∀ t : Localization.AtPrime Q,
        E (algebraMap (Localization.AtPrime Q) U t) =
          algebraMap (Localization.AtPrime Q) U (D' t) := by
  let : Algebra.FormallyEtale (Localization.AtPrime p)
      (Localization.AtPrime Q) :=
    dedekindLocal_formallyEtale_of_not_dvd_different p Q hQ
  exact formallyEtale_derivation_preserves D E hE

end

end BGS.CorvajaZannier
