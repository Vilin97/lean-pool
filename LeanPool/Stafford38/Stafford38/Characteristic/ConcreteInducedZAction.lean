/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.ConcreteEquation33SourceMatrices
public import LeanPool.Stafford38.Stafford38.Characteristic.LocalizedTwoBlockModuleExactness
public import LeanPool.Stafford38.Stafford38.Characteristic.LocalizedSpecializationActionCompatibility


/-!
# Concrete lifted source-basis action equations

This file constructs the first-order source-row matrix attached to an actual
square-zero deformation module.  The construction uses only the surjective
module specialization, its exact parameter kernel, and a basis of the special
fibre.  In particular, no scalar action on the deformation module by the
coefficient field is introduced.

The row convention is literal: entry `(i,j)` is the coefficient of the lifted
basis vector `j` in the action on lifted basis vector `i`.  This is the
transpose of Mathlib's `LinearMap.toMatrix` convention.  For the localized
two-block module the abstract construction is instantiated with the descended
quotient-ring action and the localized opposite-ring specialization.

The induced `z`-operator identity is not assumed in this file.  Its proof also
requires expanding the commutator of the two constructed action equations and
descending the resulting parameter-multiple equality through exactness.
-/

@[expose] public section

namespace Stafford38.Characteristic.ConcreteInducedZAction

open Matrix
open Stafford38.Characteristic
open Stafford38.Characteristic.ArtinianAdaptedBasisTraceAdapter
open Stafford38.Characteristic.ConcreteEquation33SourceMatrices
open Stafford38.Characteristic.LocalizedSpecializationActionCompatibility
open Stafford38.Characteristic.LocalizedTwoBlockModuleExactness
open Stafford38.Characteristic.LocalizedTwoBlockQuotient
open Stafford38.Characteristic.RightReesArtinianAdapter
open Stafford38.Characteristic.SquareZeroLocalizedExactness
open Stafford38.Characteristic.SquareZeroTraceData

noncomputable section


universe u

section AbstractSourceEquation

variable {B Abar K W V : Type u}
variable [Ring B] [CommRing Abar] [Field K]
variable [AddCommGroup W] [Module B W]
variable [AddCommGroup V] [Module K V] [Module Abar V]
variable [Algebra K Abar] [IsScalarTower K Abar V]
variable {r : ℕ}

/-- Additive action of the deformation parameter on the module. -/
def parameterAct (c : B) : W →+ W where
  toFun w := c • w
  map_zero' := smul_zero c
  map_add' x y := smul_add c x y

@[simp]
theorem parameterAct_apply (c : B) (w : W) :
    parameterAct (W := W) c w = c • w := rfl

/-- A fixed lift of every basis vector through a surjective specialization.
Calling the construction for two operators therefore uses the same lifted
basis, as required in the source calculation. -/
def liftedBasisVector
    (rho : W →+ V) (hrho : Function.Surjective rho)
    (b : Module.Basis (Fin (r + 1)) K V) (i : Fin (r + 1)) : W :=
  Classical.choose (hrho (b i))

@[simp]
theorem rho_liftedBasisVector
    (rho : W →+ V) (hrho : Function.Surjective rho)
    (b : Module.Basis (Fin (r + 1)) K V) (i : Fin (r + 1)) :
    rho (liftedBasisVector rho hrho b i) = b i :=
  Classical.choose_spec (hrho (b i))

/-- Source-row coefficients of an endomorphism.  The first index names the
input basis vector, and the second names an output coefficient. -/
def sourceActionCoefficients
    (b : Module.Basis (Fin (r + 1)) K V) (T : Module.End K V) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) Abar :=
  fun i j ↦ algebraMap K Abar (b.repr (T (b i)) j)

omit [IsScalarTower K Abar V] in
omit [Module Abar V] in
/-- The source-row coefficient matrix is the transpose of Mathlib's column
matrix, followed by coefficient-field inclusion. -/
theorem sourceActionCoefficients_eq_transpose_toMatrix_map
    (b : Module.Basis (Fin (r + 1)) K V) (T : Module.End K V) :
    sourceActionCoefficients (Abar := Abar) b T =
      (LinearMap.toMatrix b b T)ᵀ.map (algebraMap K Abar) := by
  ext i j
  simp [sourceActionCoefficients, LinearMap.toMatrix_apply, Matrix.map_apply]

/-- The row coefficients reconstruct the action on the named input vector. -/
theorem sum_sourceActionCoefficients_smul
    (b : Module.Basis (Fin (r + 1)) K V) (T : Module.End K V)
    (i : Fin (r + 1)) :
    (∑ j, sourceActionCoefficients (Abar := Abar) b T i j • b j) =
      T (b i) := by
  simp [sourceActionCoefficients]

/-- Lift the source-row coefficients entrywise through the parameter
reduction. -/
def liftedSourceActionMatrix
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (b : Module.Basis (Fin (r + 1)) K V) (T : Module.End K V) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) B :=
  liftMatrix S (sourceActionCoefficients (Abar := Abar) b T)

omit [Module Abar V] [IsScalarTower K Abar V] in
omit [IsScalarTower K Abar V] in
@[simp]
theorem liftedSourceActionMatrix_map
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (b : Module.Basis (Fin (r + 1)) K V) (T : Module.End K V) :
    (liftedSourceActionMatrix S b T).map S.modParameter =
      sourceActionCoefficients (Abar := Abar) b T :=
  liftMatrix_map S _

/-- Exact first-order source-basis action equation.

The matrix `Gamma` is constructed from the two exactness statements.  First,
the zeroth-order error is lifted through `ker rho = range(c)`.  Its chosen
preimage is expanded in the special-fibre basis; after lifting those scalar
coordinates, the remaining error again lies in `range(c)`, and multiplication
by the square-zero parameter kills it. -/
theorem exists_firstOrderSourceActionMatrix_over_coefficientField
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (rho : W →+ V) (hrho : Function.Surjective rho)
    (hrho_action : ∀ (a : B) (w : W),
      rho (a • w) = S.modParameter a • rho w)
    (hrho_ker : AddMonoidHom.ker rho =
      AddMonoidHom.range (parameterAct (W := W) S.parameter))
    (hparameter_sq : S.parameter * S.parameter = 0)
    (b : Module.Basis (Fin (r + 1)) K V) (a : B) :
    ∃ (Gamma : Matrix (Fin (r + 1)) (Fin (r + 1)) B)
      (GammaK : Matrix (Fin (r + 1)) (Fin (r + 1)) K),
      Gamma.map S.modParameter = GammaK.map (algebraMap K Abar) ∧
      ∀ i,
        a • liftedBasisVector rho hrho b i =
          (∑ j, liftedSourceActionMatrix S b
              (leftMultiplicationEnd (K := K) (V := V)
                (S.modParameter a)) i j •
              liftedBasisVector rho hrho b j) +
            S.parameter •
              (∑ j, Gamma i j • liftedBasisVector rho hrho b j) := by
  classical
  let A := liftedSourceActionMatrix S b
    (leftMultiplicationEnd (K := K) (V := V) (S.modParameter a))
  let error : Fin (r + 1) → W := fun i ↦
    a • liftedBasisVector rho hrho b i -
      ∑ j, A i j • liftedBasisVector rho hrho b j
  have herror : ∀ i, rho (error i) = 0 := by
    intro i
    rw [show rho (error i) =
        rho (a • liftedBasisVector rho hrho b i) -
          rho (∑ j, A i j • liftedBasisVector rho hrho b j) by
      simp [error]]
    rw [hrho_action, rho_liftedBasisVector]
    simp_rw [map_sum, hrho_action, rho_liftedBasisVector]
    have hAmap := liftedSourceActionMatrix_map S b
      (leftMultiplicationEnd (K := K) (V := V) (S.modParameter a))
    have hentry : ∀ i j, S.modParameter (A i j) =
        sourceActionCoefficients (Abar := Abar) b
          (leftMultiplicationEnd (K := K) (V := V)
            (S.modParameter a)) i j := by
      intro p q
      exact congrArg (fun M ↦ M p q) hAmap
    simp_rw [hentry]
    rw [sum_sourceActionCoefficients_smul]
    simp
  have herror_range : ∀ i, error i ∈
      AddMonoidHom.range (parameterAct (W := W) S.parameter) := by
    intro i
    rw [← hrho_ker]
    exact AddMonoidHom.mem_ker.mpr (herror i)
  choose u hu using herror_range
  let Gamma : Matrix (Fin (r + 1)) (Fin (r + 1)) B := fun i j ↦
    zeroPreservingLift S
      (algebraMap K Abar (b.repr (rho (u i)) j))
  have hresidual : ∀ i,
      rho (u i - ∑ j, Gamma i j • liftedBasisVector rho hrho b j) = 0 := by
    intro i
    rw [map_sub, map_sum]
    simp_rw [hrho_action, rho_liftedBasisVector]
    have hGamma : ∀ j, S.modParameter (Gamma i j) =
        algebraMap K Abar (b.repr (rho (u i)) j) := by
      intro j
      exact modParameter_zeroPreservingLift S _
    simp_rw [hGamma, IsScalarTower.algebraMap_smul]
    rw [b.sum_repr, sub_self]
  have hresidual_range : ∀ i,
      u i - ∑ j, Gamma i j • liftedBasisVector rho hrho b j ∈
        AddMonoidHom.range (parameterAct (W := W) S.parameter) := by
    intro i
    rw [← hrho_ker]
    exact AddMonoidHom.mem_ker.mpr (hresidual i)
  choose v hv using hresidual_range
  refine ⟨Gamma, (fun i j ↦ b.repr (rho (u i)) j), ?_, ?_⟩
  · ext i j
    exact modParameter_zeroPreservingLift S _
  intro i
  have hu_i : S.parameter • u i = error i := hu i
  have hv_i : S.parameter • v i =
      u i - ∑ j, Gamma i j • liftedBasisVector rho hrho b j := hv i
  have hkill : S.parameter •
      (u i - ∑ j, Gamma i j • liftedBasisVector rho hrho b j) = 0 := by
    calc
      S.parameter •
          (u i - ∑ j, Gamma i j • liftedBasisVector rho hrho b j) =
        S.parameter • (S.parameter • v i) := by rw [hv_i]
      _ = (S.parameter * S.parameter) • v i := by
        exact (mul_smul S.parameter S.parameter (v i)).symm
      _ = 0 := by rw [hparameter_sq, zero_smul]
  have hcu : S.parameter • u i =
      S.parameter •
        (∑ j, Gamma i j • liftedBasisVector rho hrho b j) := by
    rw [smul_sub] at hkill
    exact sub_eq_zero.mp hkill
  have herr : error i =
      S.parameter •
        (∑ j, Gamma i j • liftedBasisVector rho hrho b j) :=
    hu_i.symm.trans hcu
  calc
    a • liftedBasisVector rho hrho b i =
        (∑ j, A i j • liftedBasisVector rho hrho b j) + error i := by
      dsimp [error]
      abel
    _ = (∑ j, A i j • liftedBasisVector rho hrho b j) +
        S.parameter •
          (∑ j, Gamma i j • liftedBasisVector rho hrho b j) := by
      rw [herr]

/-- Compatibility form retaining only the source equation. The stronger
producer also supplies coefficient-field reductions of every correction. -/
theorem exists_firstOrderSourceActionMatrix
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (rho : W →+ V) (hrho : Function.Surjective rho)
    (hrho_action : ∀ (a : B) (w : W),
      rho (a • w) = S.modParameter a • rho w)
    (hrho_ker : AddMonoidHom.ker rho =
      AddMonoidHom.range (parameterAct (W := W) S.parameter))
    (hparameter_sq : S.parameter * S.parameter = 0)
    (b : Module.Basis (Fin (r + 1)) K V) (a : B) :
    ∃ Gamma : Matrix (Fin (r + 1)) (Fin (r + 1)) B,
      ∀ i,
        a • liftedBasisVector rho hrho b i =
          (∑ j, liftedSourceActionMatrix S b
              (leftMultiplicationEnd (K := K) (V := V)
                (S.modParameter a)) i j •
              liftedBasisVector rho hrho b j) +
            S.parameter •
              (∑ j, Gamma i j • liftedBasisVector rho hrho b j) := by
  obtain ⟨Gamma, _, _, heq⟩ :=
    exists_firstOrderSourceActionMatrix_over_coefficientField
      S rho hrho hrho_action hrho_ker hparameter_sq b a
  exact ⟨Gamma, heq⟩


end AbstractSourceEquation

section LocalizedTwoBlockProducer

variable {k R B N G : Type u}
variable [Field k] [CommRing R] [Algebra k R]
variable [Ring B] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N]
variable [SMulCommClass k Bᵐᵒᵖ N]
variable [AddCommGroup G] [Module k G] [Module R G]

variable (D : RightSquareZeroTraceData k R B N G)
variable (S : Submonoid R)
variable [OreLocalization.OreSet (OppositeDenominators D S)]
variable [IsLocalRing (Localization S)]

local notation "Wₗ" => LocalizedDeformationModule D S
local notation "A₀" => Localization S
local notation "𝔪" => IsLocalRing.maximalIdeal A₀
local notation "C₂" => LocalizedTwoBlockRing D S

/-- The doubled power acts trivially because it is contained in either one of
its two equal factors, and that factor already annihilates the module. -/
theorem localizedDoubledPower_le_annihilator
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤ Module.annihilator A₀ (LocalizedModule S G)) :
    localizedDoubledPower S q ≤
      Module.annihilator A₀ (LocalizedModule S G) := by
  exact Ideal.mul_le_left.trans hpow

/-- The canonical quotient-ring module structure on the actual localized
special fibre.  It is kept as an explicit definition because its proof
depends on the chosen annihilating power. -/
@[instance_reducible]
noncomputable def localizedDoubledPowerQuotientModule
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤ Module.annihilator A₀ (LocalizedModule S G)) :
    Module (A₀ ⧸ localizedDoubledPower S q)
      (LocalizedModule S G) := by
  apply Module.IsTorsionBySet.module
  intro w a
  exact Module.mem_annihilator.mp
    (localizedDoubledPower_le_annihilator S q hpow a.property) w

/-- The actual localized specialization, with codomain carrying the canonical
doubled-power quotient action. -/
def localizedDoubledPowerModuleSpecialization :
    Wₗ →+ LocalizedModule S G :=
  localizedSpecialization D S

omit [IsLocalRing A₀] in
theorem localizedDoubledPowerModuleSpecialization_surjective :
    Function.Surjective
      (localizedDoubledPowerModuleSpecialization D S) :=
  localizedSpecialization_surjective D S

/-- Full action compatibility after both honest quotient descents.  The left
side is the descended noncommutative two-block action; the right side is the
canonical doubled-power quotient action on the actual localized special
fibre. -/
theorem localizedDoubledPowerModuleSpecialization_action
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤ Module.annihilator A₀ (LocalizedModule S G))
    (a : C₂ q) (w : Wₗ) :
    letI : Module (A₀ ⧸ localizedDoubledPower S q)
        (LocalizedModule S G) :=
      localizedDoubledPowerQuotientModule S q hpow
    localizedDoubledPowerModuleSpecialization D S
          (localizedTwoBlockAction D S q hpow a w) =
        localizedTwoBlockSpecialization D S q a •
          localizedDoubledPowerModuleSpecialization D S w := by
  let : Module (A₀ ⧸ localizedDoubledPower S q)
      (LocalizedModule S G) :=
    localizedDoubledPowerQuotientModule S q hpow
  induction a using Quotient.inductionOn' with
  | _ z =>
    change localizedSpecialization D S (z • w) =
      Ideal.Quotient.mk (localizedDoubledPower S q)
          (SquareZeroLocalizedRing.localizedOppositeSpecialization D S z) •
        localizedSpecialization D S w
    rw [localizedSpecialization_smul]
    rfl

omit [IsLocalRing A₀] in
/-- The specialization kernel is still exactly the image of the actual
localized parameter action. -/
theorem localizedDoubledPowerModuleSpecialization_ker :
    AddMonoidHom.ker
        (localizedDoubledPowerModuleSpecialization D S) =
      AddMonoidHom.range (localizedCAct D S) :=
  localizedSpecialization_ker_eq_range D S

/-- A source-row linear combination using the actual descended two-block
action. -/
def localizedSourceLinearCombination
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤ Module.annihilator A₀ (LocalizedModule S G))
    {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (C₂ q))
    (beta : Fin (r + 1) → Wₗ) (i : Fin (r + 1)) : Wₗ :=
  ∑ j, localizedTwoBlockAction D S q hpow (M i j) (beta j)

/-- The literal source-row first-order action equation for one operator.  All
actions in this predicate are the actual localized two-block actions. -/
def LocalizedFirstOrderSourceActionEquation
    {K : Type u} [Field K]
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤ Module.annihilator A₀ (LocalizedModule S G))
    [Algebra K (A₀ ⧸ localizedDoubledPower S q)]
    [Module (A₀ ⧸ localizedDoubledPower S q) (LocalizedModule S G)]
    [Module K (LocalizedModule S G)]
    [IsScalarTower K (A₀ ⧸ localizedDoubledPower S q)
      (LocalizedModule S G)]
    {r : ℕ}
    (P : LeftPrincipalParameterReduction
      (B := C₂ q) (Abar := A₀ ⧸ localizedDoubledPower S q))
    (b : Module.Basis (Fin (r + 1)) K (LocalizedModule S G))
    (a : C₂ q)
    (Gamma : Matrix (Fin (r + 1)) (Fin (r + 1)) (C₂ q)) : Prop :=
  ∀ i,
    localizedTwoBlockAction D S q hpow a
        (liftedBasisVector
          (localizedDoubledPowerModuleSpecialization D S)
          (localizedDoubledPowerModuleSpecialization_surjective D S) b i) =
      localizedSourceLinearCombination D S q hpow
          (liftedSourceActionMatrix P b
            (leftMultiplicationEnd (K := K)
              (V := LocalizedModule S G) (P.modParameter a)))
          (liftedBasisVector
            (localizedDoubledPowerModuleSpecialization D S)
            (localizedDoubledPowerModuleSpecialization_surjective D S) b) i +
        localizedTwoBlockAction D S q hpow P.parameter
          (localizedSourceLinearCombination D S q hpow Gamma
            (liftedBasisVector
              (localizedDoubledPowerModuleSpecialization D S)
              (localizedDoubledPowerModuleSpecialization_surjective D S) b) i)

/-- The concrete first-order action-equation producer.

For an actual element of the localized two-block ring and an actual basis of
the doubled-power special fibre, this theorem constructs the source-row
matrix `Gamma` and proves the lifted basis-vector equations.  The same fixed
`liftedBasisVector` definition is used for every operator, so applying the
theorem to `x` and `y` produces `Gamma` and `Theta` on one common lifted basis.
-/
theorem exists_localizedFirstOrderSourceActionMatrix
    {K : Type u} [Field K]
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤ Module.annihilator A₀ (LocalizedModule S G))
    [Algebra K (A₀ ⧸ localizedDoubledPower S q)]
    (P : LeftPrincipalParameterReduction
      (B := C₂ q) (Abar := A₀ ⧸ localizedDoubledPower S q))
    (hPmod : P.modParameter = localizedTwoBlockSpecialization D S q)
    (hPparameter : P.parameter =
      (localizedTwoBlockIdeal D S q).ringCon.mk'
        (OreLocalization.numeratorRingHom (MulOpposite.op D.c)))
    (a : C₂ q) :
    letI : Module (A₀ ⧸ localizedDoubledPower S q)
        (LocalizedModule S G) :=
      localizedDoubledPowerQuotientModule S q hpow
    letI : Module K (LocalizedModule S G) :=
      Module.compHom _ (algebraMap K (A₀ ⧸ localizedDoubledPower S q))
    letI : IsScalarTower K (A₀ ⧸ localizedDoubledPower S q)
        (LocalizedModule S G) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    ∀ {r : ℕ} (b : Module.Basis (Fin (r + 1)) K (LocalizedModule S G)),
      ∃ Gamma : Matrix (Fin (r + 1)) (Fin (r + 1)) (C₂ q),
        ∀ i,
          localizedTwoBlockAction D S q hpow a
            (liftedBasisVector
              (localizedDoubledPowerModuleSpecialization D S)
              (localizedDoubledPowerModuleSpecialization_surjective D S) b i) =
            localizedSourceLinearCombination D S q hpow
              (liftedSourceActionMatrix P b
                (leftMultiplicationEnd (K := K)
                  (V := LocalizedModule S G)
                  (P.modParameter a)))
              (liftedBasisVector
                (localizedDoubledPowerModuleSpecialization D S)
                (localizedDoubledPowerModuleSpecialization_surjective D S) b) i +
              localizedTwoBlockAction D S q hpow P.parameter
                (localizedSourceLinearCombination D S q hpow Gamma
                  (liftedBasisVector
                  (localizedDoubledPowerModuleSpecialization D S)
                  (localizedDoubledPowerModuleSpecialization_surjective D S) b) i) := by
  let : Module (A₀ ⧸ localizedDoubledPower S q)
      (LocalizedModule S G) :=
    localizedDoubledPowerQuotientModule S q hpow
  let : Module K (LocalizedModule S G) :=
    Module.compHom _ (algebraMap K (A₀ ⧸ localizedDoubledPower S q))
  let : IsScalarTower K (A₀ ⧸ localizedDoubledPower S q)
      (LocalizedModule S G) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module (C₂ q) Wₗ := localizedTwoBlockModule D S q hpow
  intro r b
  have haction : ∀ (z : C₂ q) (w : Wₗ),
      localizedDoubledPowerModuleSpecialization D S (z • w) =
        P.modParameter z •
          localizedDoubledPowerModuleSpecialization D S w := by
    intro z w
    rw [hPmod]
    exact localizedDoubledPowerModuleSpecialization_action D S q hpow z w
  have hparameterAct :
      parameterAct (W := Wₗ) P.parameter = localizedCAct D S := by
    ext w
    change P.parameter • w = localizedCAct D S w
    rw [hPparameter]
    exact localizedTwoBlock_parameter_smul D S q hpow w
  have hker : AddMonoidHom.ker
        (localizedDoubledPowerModuleSpecialization D S) =
      AddMonoidHom.range (parameterAct (W := Wₗ) P.parameter) := by
    rw [hparameterAct]
    exact localizedDoubledPowerModuleSpecialization_ker D S
  have hsq : P.parameter * P.parameter = 0 := by
    rw [hPparameter]
    have h := localizedTwoBlock_parameter_sq D S q
    rw [pow_two] at h
    exact h
  have hresult := exists_firstOrderSourceActionMatrix P
    (localizedDoubledPowerModuleSpecialization D S)
    (localizedDoubledPowerModuleSpecialization_surjective D S)
    haction hker hsq b a
  simp only [localizedSourceLinearCombination]
  exact hresult

end LocalizedTwoBlockProducer

section ConcreteOrderReesProducer

open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotientTwoJet
open Stafford38.CharacteristicConcreteSquareZeroTraceData
open Stafford38.CharacteristicOrderReesTwoJet
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

variable (k : Type u) [Field k]
variable {n : ℕ}
variable (I : RightIdeal (PresentedWeyl k n))
variable (S : Submonoid (SymbolRing k n))

local notation "D" => filteredQuotientTwoJetTraceData k I
local notation "A₀" => Localization S
local notation "𝔪" => IsLocalRing.maximalIdeal A₀
local notation "Wₗ" => LocalizedDeformationModule D S
local notation "C₂" => LocalizedTwoBlockRing D S

variable [OreLocalization.OreSet
  (OppositeDenominators (filteredQuotientTwoJetTraceData k I) S)]
variable [IsLocalRing (Localization S)]

/-- Concrete order-Rees specialization of the action-equation producer.

There is no supplied parameter-reduction hypothesis here: the exact
left-principal reduction is the previously proved concrete two-block
specialization.  Thus the returned first-order matrix belongs to the actual
localized order-Rees two-block ring and its equation uses the actual
localized deformation module action. -/
theorem exists_concreteLocalizedFirstOrderSourceActionMatrix
    {K : Type u} [Field K]
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤ Module.annihilator A₀
      (LocalizedModule S (OrderAssociatedGradedModule k I)))
    [Algebra K (A₀ ⧸ localizedDoubledPower S q)]
    (a : C₂ q) :
    let P := concreteLeftPrincipalParameterReduction k I S q
    letI : Module (A₀ ⧸ localizedDoubledPower S q)
        (LocalizedModule S (OrderAssociatedGradedModule k I)) :=
      localizedDoubledPowerQuotientModule S q hpow
    letI : Module K
        (LocalizedModule S (OrderAssociatedGradedModule k I)) :=
      Module.compHom _ (algebraMap K (A₀ ⧸ localizedDoubledPower S q))
    letI : IsScalarTower K (A₀ ⧸ localizedDoubledPower S q)
        (LocalizedModule S (OrderAssociatedGradedModule k I)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    ∀ {r : ℕ}
      (b : Module.Basis (Fin (r + 1)) K
        (LocalizedModule S (OrderAssociatedGradedModule k I))),
      ∃ Gamma : Matrix (Fin (r + 1)) (Fin (r + 1)) (C₂ q),
        ∀ i,
          localizedTwoBlockAction D S q hpow a
            (liftedBasisVector
              (localizedDoubledPowerModuleSpecialization D S)
              (localizedDoubledPowerModuleSpecialization_surjective D S) b i) =
            localizedSourceLinearCombination D S q hpow
              (liftedSourceActionMatrix P b
                (leftMultiplicationEnd (K := K)
                  (V := LocalizedModule S
                    (OrderAssociatedGradedModule k I))
                  (P.modParameter a)))
              (liftedBasisVector
                (localizedDoubledPowerModuleSpecialization D S)
                (localizedDoubledPowerModuleSpecialization_surjective D S) b) i +
              localizedTwoBlockAction D S q hpow P.parameter
                (localizedSourceLinearCombination D S q hpow Gamma
                  (liftedBasisVector
                    (localizedDoubledPowerModuleSpecialization D S)
                    (localizedDoubledPowerModuleSpecialization_surjective D S) b) i) := by
  exact exists_localizedFirstOrderSourceActionMatrix D S q hpow
    (concreteLeftPrincipalParameterReduction k I S q) rfl rfl a

/-- Simultaneous concrete production of the source's `Gamma` and `Theta`.
Both equations use the same definitional choice of lifted basis vectors; no
second, independently chosen lift of the basis occurs. -/
theorem exists_concreteLocalizedGammaTheta
    {K : Type u} [Field K]
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤ Module.annihilator A₀
      (LocalizedModule S (OrderAssociatedGradedModule k I)))
    [Algebra K (A₀ ⧸ localizedDoubledPower S q)]
    (x y : C₂ q) :
    let P := concreteLeftPrincipalParameterReduction k I S q
    letI : Module (A₀ ⧸ localizedDoubledPower S q)
        (LocalizedModule S (OrderAssociatedGradedModule k I)) :=
      localizedDoubledPowerQuotientModule S q hpow
    letI : Module K
        (LocalizedModule S (OrderAssociatedGradedModule k I)) :=
      Module.compHom _ (algebraMap K (A₀ ⧸ localizedDoubledPower S q))
    letI : IsScalarTower K (A₀ ⧸ localizedDoubledPower S q)
        (LocalizedModule S (OrderAssociatedGradedModule k I)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    ∀ {r : ℕ}
      (b : Module.Basis (Fin (r + 1)) K
        (LocalizedModule S (OrderAssociatedGradedModule k I))),
      ∃ (Gamma Theta : Matrix (Fin (r + 1)) (Fin (r + 1)) (C₂ q)),
        LocalizedFirstOrderSourceActionEquation D S q hpow P b x Gamma ∧
        LocalizedFirstOrderSourceActionEquation D S q hpow P b y Theta := by
  dsimp only
  let P := concreteLeftPrincipalParameterReduction k I S q
  let : Module (A₀ ⧸ localizedDoubledPower S q)
      (LocalizedModule S (OrderAssociatedGradedModule k I)) :=
    localizedDoubledPowerQuotientModule S q hpow
  let : Module K
      (LocalizedModule S (OrderAssociatedGradedModule k I)) :=
    Module.compHom _ (algebraMap K (A₀ ⧸ localizedDoubledPower S q))
  let : IsScalarTower K (A₀ ⧸ localizedDoubledPower S q)
      (LocalizedModule S (OrderAssociatedGradedModule k I)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  intro r b
  obtain ⟨Gamma, hGamma⟩ :=
    (exists_concreteLocalizedFirstOrderSourceActionMatrix
      k I S q hpow x) b
  obtain ⟨Theta, hTheta⟩ :=
    (exists_concreteLocalizedFirstOrderSourceActionMatrix
      k I S q hpow y) b
  exact ⟨Gamma, Theta, hGamma, hTheta⟩


end ConcreteOrderReesProducer

end

end Stafford38.Characteristic.ConcreteInducedZAction
