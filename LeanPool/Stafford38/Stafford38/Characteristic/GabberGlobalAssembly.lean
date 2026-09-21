/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.BGab001CoefficientFieldTrace
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalGabberInvolutivityInterface

/-!
# Gabber involutivity for Weyl quotients

Apply the Artinian-local commutator theorem to the localized two-block Rees
deformation at each minimal prime. Contract bracket membership, then intersect
the minimal primes. The final theorem is field-generic and has no literature
or project assumption. The opposite-ring lifts are swapped explicitly to
preserve the right-module bracket orientation.


## References and proof context

[Gab81] Ofer Gabber, *The Integrability of the Characteristic Variety*, American Journal of Mathematics 103 (1981), no. 3, 445–468.
https://doi.org/10.2307/2374101

This is the classical theorem implemented for cyclic Weyl quotients. Its exact radical-involutivity interface is proved here; see docs/literature.md and docs/proof-guide.md.
-/

namespace Stafford38.Characteristic.GabberGlobalAssembly

open Stafford38.Characteristic.BGab001CoefficientFieldTrace
open Stafford38.Characteristic.ConcreteInducedZAction
open Stafford38.Characteristic.ConcreteEquation33SourceMatrices
open Stafford38.Characteristic.ConcreteLocalizedTwoBlockSpecialFibre
open Stafford38.Characteristic.LocalizedTwoBlockQuotient
open Stafford38.Characteristic.LocalizedTwoBlockModuleExactness
open Stafford38.Characteristic.SquareZeroLocalizedExactness
open Stafford38.Characteristic.SquareZeroLocalizedRing
open Stafford38.Characteristic.SquareZeroTraceData
open Stafford38.Characteristic.RightReesArtinianAdapter
open Stafford38.CharacteristicConcreteSquareZeroTraceData
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicOrderReesTwoJet
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.WeylIteratedEquivalence
open Stafford38.EulerSurjectivity

noncomputable section
universe u

theorem quotient_power_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (q : ℕ) (hq : 0 < q) :
    IsArtinianRing (R ⧸ (IsLocalRing.maximalIdeal R) ^ q) := by
  let m := IsLocalRing.maximalIdeal R
  have hp : m ^ q ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (Ideal.pow_le_self hq.ne')
  let : Nontrivial (R ⧸ m ^ q) := Ideal.Quotient.nontrivial_iff.mpr hp
  let : IsLocalRing (R ⧸ m ^ q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (m ^ q)) Ideal.Quotient.mk_surjective
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal (R ⧸ m ^ q)).mpr
  refine ⟨q, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (m ^ q)) Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
  exact Ideal.map_quotient_self (m ^ q)

variable (k : Type u) [Field k] [CharZero k] {n : ℕ}
variable (I : RightIdeal (PresentedWeyl k n))
variable (P : Ideal (SymbolRing k n)) [P.IsPrime]

local notation "D" => filteredQuotientTwoJetTraceData k I
local notation "S" => P.primeCompl
local notation "R" => Localization S
local notation "G" => LocalizedModule S (OrderAssociatedGradedModule k I)
local notation "Wₗ" => LocalizedDeformationModule D S
local notation "C" => LocalizedTwoBlockRing D S

variable [hOre : OreLocalization.OreSet
  (OppositeDenominators (filteredQuotientTwoJetTraceData k I) P.primeCompl)]

include hOre in
theorem localized_cofactor_mem
    (q : ℕ) (hq : 0 < q)
    (hpow : IsLocalRing.maximalIdeal R ^ q ≤ Module.annihilator R G)
    [Module.Finite R G] [Nontrivial G]
    (x y z : C q)
    (hx : localizedTwoBlockSpecialization D S q x ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (localizedDoubledPower S q)))
    (hy : localizedTwoBlockSpecialization D S q y ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (localizedDoubledPower S q)))
    (hxy : x * y - y * x =
      (concreteLeftPrincipalParameterReduction k I S q).parameter * z) :
    localizedTwoBlockSpecialization D S q z ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (localizedDoubledPower S q)) := by
  let H := localizedDoubledPower S q
  let Rq := R ⧸ H
  have hH : H = (IsLocalRing.maximalIdeal R) ^ (q + q) := by
    exact (pow_add (IsLocalRing.maximalIdeal R) q q).symm
  have hproper : H ≠ ⊤ := by
    rw [hH]
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (Ideal.pow_le_self (by omega))
  let : Nontrivial Rq := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing Rq := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk H) Ideal.Quotient.mk_surjective
  let : IsArtinianRing Rq := by
    dsimp [Rq]
    rw [hH]
    exact quotient_power_artinian R (q + q) (by omega)
  let : Module Rq G := localizedDoubledPowerQuotientModule S q hpow
  let : IsScalarTower R Rq G := by
    constructor
    intro a b v
    induction b using Quotient.inductionOn' with
    | _ b => exact mul_smul a b v
  let : Module.Finite Rq G := Module.Finite.of_restrictScalars_finite R Rq G
  let : Module (C q) Wₗ := localizedTwoBlockModule D S q hpow
  let : SMul (C q) Wₗ :=
    (localizedTwoBlockModule D S q hpow).toDistribMulAction.toDistribSMul.toSMul
  let E := concreteLeftPrincipalParameterReduction k I S q
  let rho := localizedDoubledPowerModuleSpecialization D S q hpow
  have hparam : parameterAct (W := Wₗ) E.parameter = localizedCAct D S := by
    ext w
    exact localizedTwoBlock_parameter_smul D S q hpow w
  have hact : ∀ (a : C q) (w : Wₗ), rho (a • w) = E.modParameter a • rho w :=
    localizedDoubledPowerModuleSpecialization_action D S q hpow
  have hker : AddMonoidHom.ker rho = AddMonoidHom.range (parameterAct (W := Wₗ) E.parameter) := by
    rw [hparam]
    exact localizedDoubledPowerModuleSpecialization_ker D S q hpow
  have hexact : AddMonoidHom.ker (parameterAct (W := Wₗ) E.parameter) =
      AddMonoidHom.range (parameterAct (W := Wₗ) E.parameter) := by
    rw [hparam]
    exact localizedCAct_ker_eq_range D S
  have hc2 : E.parameter * E.parameter = 0 := by
    rw [← pow_two]
    change ((localizedTwoBlockIdeal D S q).ringCon.mk'
      (OreLocalization.numeratorRingHom (MulOpposite.op (orderReesTwoJetParameter (n := n) k)))) ^ 2 = 0
    exact localizedTwoBlock_parameter_sq D S q
  have hmax : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk H) =
      IsLocalRing.maximalIdeal Rq :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hmax] at hx hy ⊢
  exact artinian_local_cofactor_mem_maximalIdeal k E rho
    (localizedDoubledPowerModuleSpecialization_surjective D S q hpow)
    hact hker hexact hc2 x y z hx hy hxy

omit hOre in
theorem minimalPrime_isInvolutive
    (hP : P ∈ (Module.annihilator (SymbolRing k n)
      (OrderAssociatedGradedModule k I)).minimalPrimes) : IsInvolutive P := by
  obtain ⟨h, core⟩ := exists_concrete_localizedPreArtinianCore k I P hP
  let := h
  let : Nontrivial G := core.fibre_nontrivial
  let : IsNoetherian R G :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp core.fibre_finiteLength).1
  obtain ⟨q, hq⟩ := core.annihilatingPower
  have hpow : IsLocalRing.maximalIdeal R ^ (q + 1) ≤ Module.annihilator R G :=
    (Ideal.pow_le_pow_right (Nat.le_succ q)).trans hq
  intro f hf g hg
  obtain ⟨a, b, z, ha, hb, hab, hz⟩ :=
    RightSquareZeroTraceData.exists_lifts_commutator_factor k _ _ D f g
  let φ : (OrderReesTwoJet (n := n) k)ᵐᵒᵖ →+* C (q + 1) :=
    ((localizedTwoBlockIdeal D S (q + 1)).ringCon.mk').comp
      OreLocalization.numeratorRingHom
  let x := φ (MulOpposite.op b)
  let y := φ (MulOpposite.op a)
  let zq := φ (MulOpposite.op z)
  let H := localizedDoubledPower S (q + 1)
  have hspec (v : OrderReesTwoJet (n := n) k) :
      localizedTwoBlockSpecialization D S (q + 1) (φ (MulOpposite.op v)) =
        Ideal.Quotient.mk H (algebraMap (SymbolRing k n) R ((D).pi v)) := by
    rw [show φ (MulOpposite.op v) =
      (localizedTwoBlockIdeal D S (q + 1)).ringCon.mk'
        (OreLocalization.numeratorRingHom (MulOpposite.op v)) from rfl,
      localizedTwoBlockSpecialization_mk]
    change Ideal.Quotient.mk H (localizedOppositeSpecialization D S
      (OreLocalization.numeratorRingHom (MulOpposite.op v))) = _
    exact congrArg (Ideal.Quotient.mk H)
      (localizedOppositeSpecialization_numerator D S (MulOpposite.op v))
  have hx : localizedTwoBlockSpecialization D S (q + 1) x ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk H) := by
    rw [show x = φ (MulOpposite.op b) from rfl, hspec, hb]
    exact Ideal.mem_map_of_mem _ ((IsLocalization.AtPrime.to_map_mem_maximal_iff R P g).mpr hg)
  have hy : localizedTwoBlockSpecialization D S (q + 1) y ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk H) := by
    rw [show y = φ (MulOpposite.op a) from rfl, hspec, ha]
    exact Ideal.mem_map_of_mem _ ((IsLocalization.AtPrime.to_map_mem_maximal_iff R P f).mpr hf)
  have hop : MulOpposite.op b * MulOpposite.op a - MulOpposite.op a * MulOpposite.op b =
      MulOpposite.op (D).c * MulOpposite.op z := by
    apply MulOpposite.unop_injective
    change a * b - b * a = z * (D).c
    change a * b - b * a = (D).c * z at hab
    exact hab.trans ((D).c_center.comm z).eq
  have hxy : x * y - y * x =
      (concreteLeftPrincipalParameterReduction k I S (q + 1)).parameter * zq := by
    have hparam : (concreteLeftPrincipalParameterReduction k I S (q + 1)).parameter =
        φ (MulOpposite.op (D).c) := rfl
    rw [hparam]
    have hh := congrArg φ hop
    simpa only [map_sub, map_mul] using hh
  have hlocal := localized_cofactor_mem k I P (q + 1) (by omega) hpow x y zq hx hy hxy
  rw [show zq = φ (MulOpposite.op z) from rfl, hspec, hz,
    filteredQuotientTwoJetTraceData_bracket] at hlocal
  have hHle : H ≤ IsLocalRing.maximalIdeal R :=
    Ideal.mul_le_left.trans (Ideal.pow_le_self (by omega))
  have hneg : algebraMap (SymbolRing k n) R (-poissonBracket f g) ∈
      IsLocalRing.maximalIdeal R := by
    have hc := (Ideal.mem_comap).mpr hlocal
    rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk H)
      Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hHle] at hc
    exact hc
  exact (P.neg_mem_iff).mp ((IsLocalization.AtPrime.to_map_mem_maximal_iff R P _).mp hneg)

omit hOre in
theorem associatedGraded_radical_isInvolutive :
    IsInvolutive (Module.annihilator (SymbolRing k n)
      (OrderAssociatedGradedModule k I)).radical := by
  let J := Module.annihilator (SymbolRing k n) (OrderAssociatedGradedModule k I)
  intro f hf g hg
  rw [← J.sInf_minimalPrimes]
  apply Ideal.mem_sInf.mpr
  intro P hP
  let : P.IsPrime := hP.1.1
  have hle : J.radical ≤ P := hP.1.1.radical_le_iff.mpr hP.1.2
  exact minimalPrime_isInvolutive k I P hP f (hle hf) g (hle hg)

theorem weylAssociatedGradedRadicalInvolutivity :
    Stafford38.Characteristic.CanonicalGabberInvolutivityInterface.WeylAssociatedGradedRadicalInvolutivity.{u} := by
  intro k _ _ n I
  exact associatedGraded_radical_isInvolutive k I


end
end Stafford38.Characteristic.GabberGlobalAssembly
