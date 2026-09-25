/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.NumberTheory.Padics.RingHoms
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.DenominatorValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.InverseLimitTopology
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.PadicReductionContinuous
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.QuotientTransition
/-!
# P-adic modules on finite principal-unit quotients

Finite principal-unit quotients have the expected residue-characteristic exponent.
Reduction of p-adic integers therefore supplies canonical module structures, compatible with
the transition maps.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-! ## The finite-coordinate p-adic actions -/

/-- The residue degree `f`, chosen from the finite-field identity `q = p^f`. -/
noncomputable def principalUnitResidueDegree
    (F : LocalField.{u, v} K) : ℕ+ := by
  letI := Fintype.ofFinite F.residueField
  exact Classical.choose
    (FiniteField.card F.residueField F.residueCharacteristic)

/--
Establishes the identity `F.residueCharacteristic.Prime ∧ Nat.card F.residueField =
F.residueCharacteristic ^ (principalUnitResidueDegree F : ℕ)`.
-/
theorem residueCharacteristic_prime_and_card_eq_pow_residueDegree
    (F : LocalField.{u, v} K) :
    F.residueCharacteristic.Prime ∧
      Nat.card F.residueField =
        F.residueCharacteristic ^ (principalUnitResidueDegree F : ℕ) := by
  let := Fintype.ofFinite F.residueField
  have h := Classical.choose_spec
    (FiniteField.card F.residueField F.residueCharacteristic)
  refine ⟨h.1, ?_⟩
  simpa [principalUnitResidueDegree, Nat.card_eq_fintype_card] using h.2

/-- The finite-field cardinality identity uniquely determines the residue
degree selected above. -/
theorem principalUnitResidueDegree_unique
    (F : LocalField.{u, v} K) (d : ℕ+)
    (hcard :
      Nat.card F.residueField =
        F.residueCharacteristic ^ (d : ℕ)) :
    d = principalUnitResidueDegree F := by
  have hselected :=
    residueCharacteristic_prime_and_card_eq_pow_residueDegree F
  apply Subtype.ext
  apply Nat.pow_right_injective hselected.1.two_le
  exact hcard.symm.trans hselected.2

/-- The type in `Finite (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)` is finite. -/
instance Internal.principalUnitQuotientCarrier_finite
    (F : LocalField.{u, v} K) (n : ℕ) :
    Finite (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := by
  have : Finite
      (F.valuationSubringˣ ⧸
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF) (n + 1)) :=
    higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
      F.toCompleteDVF (n + 1)
  exact Finite.of_injective
    (principalUnitQuotientCarrierToFull F.toCompleteDVF n)
    (principalUnitQuotientCarrierToFull_injective F.toCompleteDVF n)

/-- The `n`-th first-principal-unit quotient has cardinality `p^(f*n)`. -/
theorem Internal.card_principalUnitQuotientCarrier_eq_residueCharacteristic_pow
    (F : LocalField.{u, v} K) (n : ℕ) :
    Nat.card (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =
      F.residueCharacteristic ^ ((principalUnitResidueDegree F : ℕ) * n) := by
  have hcard :=
    higherPrincipalUnitGroup.card_principalUnitSubquotient_one_eq_residue_pow_of_uniformizer
      F.toCompleteDVF
      (chosenPrincipalUnitPadicUniformizer_isUniformizer F.toCompleteDVF)
      (Nat.le_add_left 1 n)
  rw [show n + 1 - 1 = n by omega] at hcard
  have hcard' :
      Nat.card (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =
        Nat.card F.residueField ^ n := by
    let e :
        Internal.principalUnitQuotientCarrier F.toCompleteDVF n ≃
          (higherPrincipalUnitGroup F.toCompleteDVF 1 ⧸
            (higherPrincipalUnitGroup F.toCompleteDVF (n + 1)).subgroupOf
              (higherPrincipalUnitGroup F.toCompleteDVF 1)) := by
      change
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration
            F.toCompleteDVF).principalUnitSubquotient 1 (n + 1) ≃
          ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
              F.toCompleteDVF).principalUnitSubgroup 1 ⧸
            ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
              F.toCompleteDVF).principalUnitSubgroup (n + 1)).subgroupOf
                ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
                  F.toCompleteDVF).principalUnitSubgroup 1))
      exact
        (AntitoneSubgroupFiltration.principalUnitSubquotientConcreteEquiv
          (higherPrincipalUnitGroup.toPrincipalUnitFiltration F.toCompleteDVF)
          1 (n + 1)).toEquiv
    let : Finite
        (higherPrincipalUnitGroup F.toCompleteDVF 1 ⧸
          (higherPrincipalUnitGroup F.toCompleteDVF (n + 1)).subgroupOf
            (higherPrincipalUnitGroup F.toCompleteDVF 1)) :=
      Finite.of_equiv
        (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)
        e
    calc
      Nat.card (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =
          Nat.card
            (higherPrincipalUnitGroup F.toCompleteDVF 1 ⧸
              (higherPrincipalUnitGroup F.toCompleteDVF (n + 1)).subgroupOf
                (higherPrincipalUnitGroup F.toCompleteDVF 1)) :=
        Nat.card_congr e
      _ = Nat.card F.residueField ^ n := by
        exact hcard
  rw [hcard',
    (residueCharacteristic_prime_and_card_eq_pow_residueDegree F).2,
    pow_mul]

/-- The type in `Finite (DiscretePrincipalUnitQuotient F.toCompleteDVF n)` is finite. -/
instance discretePrincipalUnitQuotientFinite
    (F : LocalField.{u, v} K) (n : ℕ) :
    Finite (DiscretePrincipalUnitQuotient F.toCompleteDVF n) :=
  Finite.of_injective
    (fun x : DiscretePrincipalUnitQuotient F.toCompleteDVF n => x.val)
    (DiscretePrincipalUnitQuotient.equiv F.toCompleteDVF n).injective

/-- A wrapped level quotient has the expected local-field cardinality
`p^(f*n)`. -/
theorem card_discretePrincipalUnitQuotient_eq_residueCharacteristic_pow
    (F : LocalField.{u, v} K) (n : ℕ) :
    Nat.card (DiscretePrincipalUnitQuotient F.toCompleteDVF n) =
      F.residueCharacteristic ^ ((principalUnitResidueDegree F : ℕ) * n) := by
  rw [show
    Nat.card (DiscretePrincipalUnitQuotient F.toCompleteDVF n) =
        Nat.card
          (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) by
    exact
      Nat.card_congr
        (DiscretePrincipalUnitQuotient.equiv F.toCompleteDVF n)]
  calc
    Nat.card
        (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) =
        Nat.card
          (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) :=
      Nat.card_congr Additive.toMul
    _ = F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n) :=
      Internal.card_principalUnitQuotientCarrier_eq_residueCharacteristic_pow F n

/-- Lagrange's theorem gives the exact exponent bound needed to reduce a
p-adic scalar modulo `p^(f*n)`. -/
theorem Internal.principalUnitQuotientCarrier_pow_residueCharacteristic_pow_eq_one
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : Internal.principalUnitQuotientCarrier F.toCompleteDVF n) :
    x ^ (F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n)) = 1 := by
  rw [← card_principalUnitQuotientCarrier_eq_residueCharacteristic_pow F n]
  exact pow_card_eq_one'

/--
Establishes the identity `(F.residueCharacteristic ^ ((principalUnitResidueDegree F : ℕ) * n)) • x
= 0`.
-/
theorem Internal.principalUnitQuotientCarrier_nsmul_residueCharacteristic_pow_eq_zero
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :
    (F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n)) • x = 0 := by
  change Additive.ofMul
      ((Additive.toMul x) ^ (F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n))) = Additive.ofMul 1
  rw [principalUnitQuotientCarrier_pow_residueCharacteristic_pow_eq_one]

/-- The exact exponent bound, stated on the canonical discrete wrapper. -/
theorem discretePrincipalUnitQuotient_nsmul_residueCharacteristic_pow_eq_zero
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : DiscretePrincipalUnitQuotient F.toCompleteDVF n) :
    (F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n)) • x = 0 := by
  apply (DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n).injective
  simpa only [map_nsmul, map_zero,
    DiscretePrincipalUnitQuotient.addEquiv_apply] using
    Internal.principalUnitQuotientCarrier_nsmul_residueCharacteristic_pow_eq_zero
      F n x.val

/-- The canonical `ZMod (p^(f*n))`-module on the `n`-th finite coordinate. -/
@[implicit_reducible]
noncomputable def Internal.principalUnitQuotientCarrierZModModule
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module
      (ZMod (F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n)))
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :=
  AddCommGroup.zmodModule
    (n := F.residueCharacteristic ^
      ((principalUnitResidueDegree F : ℕ) * n))
    (G := Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n))
    (principalUnitQuotientCarrier_nsmul_residueCharacteristic_pow_eq_zero F n)

/-- Restriction of scalars along `Z_p -> ZMod (p^(f*n))`. -/
noncomputable instance Internal.principalUnitQuotientCarrierPadicModule
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module ℤ_[F.residueCharacteristic]
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) := by
  letI := principalUnitQuotientCarrierZModModule F n
  exact Module.compHom _
    (PadicInt.toZModPow ((principalUnitResidueDegree F : ℕ) * n))

/--
Equips the target in `Module ℤ_[F.residueCharacteristic] (DiscretePrincipalUnitQuotient
F.toCompleteDVF n)` with the indicated module structure.
-/
noncomputable instance discretePrincipalUnitQuotientPadicModule
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module ℤ_[F.residueCharacteristic]
      (DiscretePrincipalUnitQuotient F.toCompleteDVF n) :=
  AddEquiv.module
    (β := Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n))
    ℤ_[F.residueCharacteristic]
    (DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n)

/--
Establishes the identity `DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n (a • x) = a •
DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n x`.
-/
theorem DiscretePrincipalUnitQuotient.addEquiv_map_smul
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : ℤ_[F.residueCharacteristic])
    (x : DiscretePrincipalUnitQuotient F.toCompleteDVF n) :
    DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n (a • x) =
      a • DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n x :=
  rfl

/-- The finite-coordinate scalar written explicitly through reduction of a
p-adic integer modulo `p^(f*n)`. -/
noncomputable def Internal.principalUnitQuotientCarrierPadicScalar
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :
    Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := by
  letI := principalUnitQuotientCarrierZModModule F n
  exact PadicInt.toZModPow
    ((principalUnitResidueDegree F : ℕ) * n) a • x

/-- Establishes the identity `principalUnitQuotientCarrierPadicScalar F n a x = a • x`. -/
@[simp] theorem Internal.principalUnitQuotientCarrierPadicScalar_eq_smul
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :
    principalUnitQuotientCarrierPadicScalar F n a x = a • x :=
  rfl

/-- Joint continuity of the p-adic scalar action on one finite discrete
coordinate. -/
theorem Internal.continuous_principalUnitQuotientCarrierPadicScalar
    (F : LocalField.{u, v} K) (n : ℕ) :
    letI : TopologicalSpace
        (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := ⊥
    Continuous fun z : ℤ_[F.residueCharacteristic] ×
        Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =>
      principalUnitQuotientCarrierPadicScalar F n z.1 z.2 := by
  let p := F.residueCharacteristic
  let f : ℕ := principalUnitResidueDegree F
  let : TopologicalSpace
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := ⊥
  let : DiscreteTopology
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := ⟨rfl⟩
  let : TopologicalSpace (ZMod (p ^ (f * n))) := ⊥
  let : DiscreteTopology (ZMod (p ^ (f * n))) := ⟨rfl⟩
  let : Module (ZMod (p ^ (f * n)))
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) := by
    simpa [p, f] using principalUnitQuotientCarrierZModModule F n
  have hred : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =>
      PadicInt.toZModPow (f * n) z.1 :=
    (Internal.continuous_padicIntToZModPow p (f * n)).comp continuous_fst
  have hact : Continuous fun z : ZMod (p ^ (f * n)) ×
      Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =>
      z.1 • z.2 :=
    continuous_of_discreteTopology
  change Continuous fun z : ℤ_[F.residueCharacteristic] ×
      Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =>
    PadicInt.toZModPow (f * n) z.1 • z.2
  exact hact.comp (hred.prodMk continuous_snd)

/--
The specified map is continuous: `Continuous fun z : ℤ_[F.residueCharacteristic] ×
DiscretePrincipalUnitQuotient F.toCompleteDVF n => z.1 • z.2`.
-/
theorem continuous_discretePrincipalUnitQuotientPadic_smul
    (F : LocalField.{u, v} K) (n : ℕ) :
    Continuous fun z : ℤ_[F.residueCharacteristic] ×
        DiscretePrincipalUnitQuotient F.toCompleteDVF n =>
      z.1 • z.2 := by
  let : TopologicalSpace
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) := ⊥
  let : DiscreteTopology
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) := ⟨rfl⟩
  let e : DiscretePrincipalUnitQuotient F.toCompleteDVF n ≃ₜ
      Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) :=
    { toEquiv := DiscretePrincipalUnitQuotient.equiv F.toCompleteDVF n
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  have hpair : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      DiscretePrincipalUnitQuotient F.toCompleteDVF n =>
      (z.1, e z.2) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  have h := e.continuous_symm.comp
    ((Internal.continuous_principalUnitQuotientCarrierPadicScalar F n).comp hpair)
  refine h.congr fun z => ?_
  apply e.injective
  simp only [Function.comp_apply, e.apply_symm_apply]
  change
    Internal.principalUnitQuotientCarrierPadicScalar F n z.1
        (DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n z.2) =
      DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n (z.1 • z.2)
  rw [Internal.principalUnitQuotientCarrierPadicScalar_eq_smul,
    DiscretePrincipalUnitQuotient.addEquiv_map_smul]

/-- Reduction between finite principal-unit quotients is `Z_p`-linear.  The
key point is compatibility of `toZModPow` with the cast from level `f*n` to
level `f*m`. -/
theorem Internal.principalUnitQuotientCarrierTransitionAdd_map_smul
    (F : LocalField.{u, v} K) {m n : ℕ} (hmn : m ≤ n)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :
    principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn (a • x) =
      a • principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn x := by
  let f : ℕ := principalUnitResidueDegree F
  let p : ℕ := F.residueCharacteristic
  have hlevels : f * m ≤ f * n := Nat.mul_le_mul_left f hmn
  let sourceModule : Module (ZMod (p ^ (f * n)))
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) := by
    simpa [p, f] using principalUnitQuotientCarrierZModModule F n
  let targetModule : Module (ZMod (p ^ (f * m)))
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF m)) := by
    simpa [p, f] using principalUnitQuotientCarrierZModModule F m
  let targetModuleAtN : Module (ZMod (p ^ (f * n)))
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF m)) :=
    Module.compHom _
      (ZMod.castHom (pow_dvd_pow p hlevels) (ZMod (p ^ (f * m))))
  change
    principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn
        (PadicInt.toZModPow (f * n) a • x) =
      PadicInt.toZModPow (f * m) a •
        principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn x
  calc
    principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn
        (PadicInt.toZModPow (f * n) a • x) =
        PadicInt.toZModPow (f * n) a •
          principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn x :=
      ZMod.map_smul
        (principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn)
        _ _
    _ = (PadicInt.toZModPow (f * n) a).cast •
          principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn x := rfl
    _ = PadicInt.toZModPow (f * m) a •
          principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn x := by
      rw [PadicInt.cast_toZModPow (f * m) (f * n) hlevels]

namespace DiscretePrincipalUnitQuotient

/-- Wrapped coordinate reduction is `Z_p`-linear. -/
noncomputable def transitionLinear
    (F : LocalField.{u, v} K) {m n : ℕ} (hmn : m ≤ n) :
    DiscretePrincipalUnitQuotient F.toCompleteDVF n →ₗ[
      ℤ_[F.residueCharacteristic]]
      DiscretePrincipalUnitQuotient F.toCompleteDVF m where
  toFun := transition F.toCompleteDVF hmn
  map_add' := fun x y => (transition F.toCompleteDVF hmn).map_add x y
  map_smul' a x := by
    have hx : (a • x).val = a • x.val := by
      simpa only [addEquiv_apply] using
        addEquiv_map_smul F n a x
    have hy :
        (a • transition F.toCompleteDVF hmn x).val =
          a • (transition F.toCompleteDVF hmn x).val := by
      simpa only [addEquiv_apply] using
        addEquiv_map_smul F m a (transition F.toCompleteDVF hmn x)
    apply (addEquiv F.toCompleteDVF m).injective
    simpa only [addEquiv_apply, val_transition, RingHom.id_apply, hx, hy] using
      Internal.principalUnitQuotientCarrierTransitionAdd_map_smul
        F hmn a x.val

end DiscretePrincipalUnitQuotient

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
