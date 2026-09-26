/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.DeepPrincipalUnits
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.IntegralLattice
/-!
# First principal units in mixed characteristic

This module combines the deep free `Z_p` lattice with the finite quotient
exact sequence and packages the algebraic and topological structure of
the first principal-unit group.
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  toPrincipalUnitFiltration →
    toPrincipalUnitFiltration


noncomputable
section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero nonZeroDivisors
open Module

variable {K : Type u} [Field K]

/-! ### The finite-level exact sequence and the first principal units -/

/-- Proof-relevant output of the finite-kernel/finite-quotient PID argument. -/
structure FiniteRankTorsionProjectionData
    (R M Q : Type*) [CommRing R]
    [AddCommGroup M] [AddCommGroup Q] [Module R M] [Module R Q]
    (f : M →ₗ[R] Q) (d : ℕ) where
  /-- The middle module is finitely generated over `R`. -/
  moduleFinite : Module.Finite R M
  /-- The torsion submodule of the middle module is finite. -/
  finiteTorsion : Finite (Submodule.torsion R M)
  /-- The restriction of `f` to the torsion submodule is injective. -/
  torsionProjection_injective :
    Function.Injective (f.domRestrict (Submodule.torsion R M))
  /-- The middle module has `R`-finrank `d`. -/
  finrankMiddle : Module.finrank R M = d
  /-- The torsion-free quotient of the middle module has `R`-finrank `d`. -/
  finrankFree :
    Module.finrank R (M ⧸ Submodule.torsion R M) = d

/-- A finite quotient together with its free kernel data. -/
structure FiniteQuotientSetup
    (R M Q : Type*) [CommRing R]
    [AddCommGroup M] [AddCommGroup Q] [Module R M] [Module R Q]
    (d : ℕ) where
  /-- The linear projection from the middle module to the quotient. -/
  projection : M →ₗ[R] Q
  /-- The projection onto the quotient is surjective. -/
  projection_surjective : Function.Surjective projection
  /-- The kernel of the projection is finitely generated over `R`. -/
  kernelFinite : Module.Finite R (LinearMap.ker projection)
  /-- The kernel of the projection is free over `R`. -/
  kernelFree : Module.Free R (LinearMap.ker projection)
  /-- The kernel of the projection has `R`-finrank `d`. -/
  kernelFinrank : Module.finrank R (LinearMap.ker projection) = d
  /-- The quotient module is torsion over `R`. -/
  quotientTorsion : Module.IsTorsion R Q

/-- The projection-free form of the finite-rank/torsion output.  Keeping the
large concrete quotient map out of downstream result types substantially
reduces elaboration. -/
structure FiniteRankTorsionData
    (R M Q : Type*) [CommRing R]
    [AddCommGroup M] [AddCommGroup Q] [Module R M] [Module R Q]
    (d : ℕ) where
  /-- The middle module is finitely generated over `R`. -/
  moduleFinite : Module.Finite R M
  /-- The torsion submodule of the middle module is finite. -/
  finiteTorsion : Finite (Submodule.torsion R M)
  /-- A linear map from the torsion submodule into the quotient module. -/
  torsionProjection : Submodule.torsion R M →ₗ[R] Q
  /-- The torsion projection is injective. -/
  torsionProjection_injective : Function.Injective torsionProjection
  /-- The middle module has `R`-finrank `d`. -/
  finrankMiddle : Module.finrank R M = d
  /-- The torsion-free quotient of the middle module has `R`-finrank `d`. -/
  finrankFree :
    Module.finrank R (M ⧸ Submodule.torsion R M) = d

/-- Algebraic bookkeeping for a finite torsion quotient of a finite free
kernel.  This is the PID step used in the mixed-characteristic field-unit structure theorem: it
  proves finite
generation and rank of the middle term, and embeds its torsion into the
finite quotient. -/
theorem finite_rank_and_torsion_projection_of_surjective
    {R M Q : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    [AddCommGroup M] [AddCommGroup Q] [Module R M] [Module R Q]
    (f : M →ₗ[R] Q) (hf : Function.Surjective f)
    [Finite Q] [Module.Finite R Q]
    [Module.Finite R (LinearMap.ker f)] [Module.Free R (LinearMap.ker f)]
    (d : ℕ) (hrankKer : Module.finrank R (LinearMap.ker f) = d)
    (hQtorsion : Module.IsTorsion R Q) :
    FiniteRankTorsionProjectionData R M Q f d := by
  let N := LinearMap.ker f
  let eQuot : (M ⧸ N) ≃ₗ[R] Q :=
    LinearMap.quotKerEquivOfSurjective f hf
  let : Module.Finite R (M ⧸ N) := Module.Finite.equiv eQuot.symm
  let hM : Module.Finite R M := Module.Finite.of_submodule_quotient N
  have hquotTorsion : Module.IsTorsion R (M ⧸ N) := by
    intro x
    rcases @hQtorsion (eQuot x) with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply eQuot.injective
    calc
      eQuot (a • x) = a • eQuot x := eQuot.map_smul a x
      _ = 0 := ha
      _ = eQuot 0 := (eQuot.map_zero).symm
  have hrankQuot : Module.finrank R (M ⧸ N) = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr hquotTorsion
  have hrankM : Module.finrank R M = d := by
    have hsum := N.finrank_quotient_add_finrank
    rw [hrankQuot, zero_add] at hsum
    exact hsum.symm.trans hrankKer
  let T := Submodule.torsion R M
  let tproj : T →ₗ[R] Q := f.domRestrict T
  have htproj : Function.Injective tproj := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hzero : tproj (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hzN : (((x - y : T) : M)) ∈ N := by
      change f (((x - y : T) : M)) = 0
      exact hzero
    let zN : N := ⟨(((x - y : T) : M)), hzN⟩
    rcases (x - y).property with ⟨a, ha⟩
    have haz : (a : R) • zN = 0 := by
      apply Subtype.ext
      exact ha
    have ha_ne : (a : R) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp a.property
    have hzN_zero : zN = 0 :=
      (smul_eq_zero.mp haz).resolve_left ha_ne
    exact congrArg Subtype.val hzN_zero
  let hT : Finite T := Finite.of_injective tproj htproj
  let : Module.Finite R T := inferInstance
  have hTtorsion : Module.IsTorsion R T := by
    intro x
    rcases x.property with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha
  have hrankT : Module.finrank R T = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr hTtorsion
  let : Module.Finite R (M ⧸ T) := Module.Finite.quotient R T
  have hrankFree : Module.finrank R (M ⧸ T) = d := by
    have hsum := T.finrank_quotient_add_finrank
    rw [hrankT, add_zero] at hsum
    exact hsum.trans hrankM
  exact
    { moduleFinite := hM
      finiteTorsion := hT
      torsionProjection_injective := htproj
      finrankMiddle := hrankM
      finrankFree := hrankFree }

/-- Consume a finite quotient setup and forget the concrete quotient map
from the result type. -/
noncomputable def finiteRankTorsionDataOfSetup
    {R M Q : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    [AddCommGroup M] [AddCommGroup Q] [Module R M] [Module R Q]
    [Finite Q] [Module.Finite R Q]
    (d : ℕ) (setup : FiniteQuotientSetup R M Q d) :
    FiniteRankTorsionData R M Q d := by
  letI : Module.Finite R (LinearMap.ker setup.projection) :=
    setup.kernelFinite
  letI : Module.Free R (LinearMap.ker setup.projection) :=
    setup.kernelFree
  let core := finite_rank_and_torsion_projection_of_surjective
    setup.projection setup.projection_surjective d
      setup.kernelFinrank setup.quotientTorsion
  exact
    { moduleFinite := core.moduleFinite
      finiteTorsion := core.finiteTorsion
      torsionProjection :=
        setup.projection.domRestrict (Submodule.torsion R M)
      torsionProjection_injective := core.torsionProjection_injective
      finrankMiddle := core.finrankMiddle
      finrankFree := core.finrankFree }

/-- The proof-relevant algebraic package used to assemble the topological
classification of the first principal units. -/
structure FirstPrincipalUnitAlgebraicData
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (p d : ℕ) where
  /-- The exponent in the prime-power order `p ^ a` of the torsion subgroup. -/
  a : ℕ
  /-- The first principal-unit module is finitely generated over `R`. -/
  moduleFinite : Module.Finite R M
  /-- The torsion submodule is finite. -/
  finiteTorsion : Finite (Submodule.torsion R M)
  /-- The torsion submodule is cyclic as an additive group. -/
  cyclicTorsion : IsAddCyclic (Submodule.torsion R M)
  /-- The torsion submodule has cardinality `p ^ a`. -/
  cardTorsion :
    letI := finiteTorsion
    Nat.card (Submodule.torsion R M) = p ^ a
  /-- The torsion-free quotient has `R`-finrank `d`. -/
  finrankFree :
    Module.finrank R (M ⧸ Submodule.torsion R M) = d

/-- A finite additive group that embeds, after changing notation, into the
multiplicative group of a domain is cyclic.  Keeping the type-tag conversion at
this general boundary avoids repeating it for complicated submodule types. -/
theorem isAddCyclic_of_injective_multiplicative_map
    {A U D : Type*} [AddGroup A] [Group U]
    [CommRing D] [IsDomain D] [Finite A]
    (f : A →+ Additive U) (g : U →* D)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    IsAddCyclic A := by
  let fmul : Multiplicative A →* U :=
    AddMonoidHom.toMultiplicativeLeft f
  have hfmul : Function.Injective fmul := by
    intro x y hxy
    exact Multiplicative.toAdd.injective
      (hf (Additive.toMul.injective hxy))
  exact isCyclic_multiplicative_iff.mp
    (isCyclic_of_injective_ringHom (g.comp fmul) (hg.comp hfmul))

/-- Transfer the prime-power cardinality of a finite additive quotient across
an injective additive map. -/
theorem exists_card_eq_prime_power_of_injective_addMonoidHom
    {p : ℕ} {A B : Type*} [Fact p.Prime]
    [AddGroup A] [AddGroup B] [Finite A]
    (f : A →+ B) (hf : Function.Injective f)
    (hB : IsPGroup p (Multiplicative B)) :
    ∃ a : ℕ, Nat.card A = p ^ a := by
  let fmul : Multiplicative A →* Multiplicative B :=
    AddMonoidHom.toMultiplicative f
  have hfmul : Function.Injective fmul := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    apply hf
    simpa [fmul] using congrArg Multiplicative.toAdd hxy
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hB.of_injective fmul hfmul)
  exact ⟨a, (Nat.card_congr Multiplicative.ofAdd).trans ha⟩

/-- A finite free submodule together with its rank. -/
structure FiniteFreeSubmoduleData
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (d : ℕ) where
  /-- The submodule `N` is finitely generated over `R`. -/
  moduleFinite : Module.Finite R N
  /-- The submodule `N` is free over `R`. -/
  moduleFree : Module.Free R N
  /-- The submodule `N` has `R`-finrank `d`. -/
  finrank : Module.finrank R N = d

/-- The deep logarithmic lattice, viewed inside `U¹`, is finite free of the
field degree. -/
theorem mixed_principalUnitSuccKernelData
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let p := F.residueCharacteristic
    let R := ℤ_[p]
    let M := Additive
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (F.toCompleteDVF) 1)
    letI : MixedQPadicContext F := mixedQPadicContext F
    letI : Module R M :=
      CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
    let d := Module.finrank ℚ_[p] K
    FiniteFreeSubmoduleData R M
      (F.principalUnitSuccPadicSubmodule n) d := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let R := ℤ_[p]
  let M := Additive
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
    (F.toCompleteDVF) 1)
  let : MixedQPadicContext F := mixedQPadicContext F
  let : Module R M :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
  let d : ℕ := Module.finrank ℚ_[p] K
  let : Algebra R F.toCompleteDVF.valuationSubring :=
    F.padicIntValuationSubringAlgebra
  have hlevelSucc :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          ((F.residueCharacteristic : ℚ) - 1) < ((n + 1 : ℕ) : ℚ) :=
    lt_trans hlevel (by exact_mod_cast Nat.lt_succ_self n)
  let hr : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  let deep := Additive
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (F.toCompleteDVF) (n + 1))
  let : Module R deep := F.higherPrincipalUnitPadicModule hr
  let : Module.Finite R deep :=
    mixed_deepPrincipalUnit_moduleFinite
      v hv (n + 1) hlevelSucc
  let eDeep : deep ≃ₗ[R] (Fin d → R) :=
    mixedDeepPrincipalUnitLinearEquivPi
      v hv (n + 1) hlevelSucc
  let higher := F.principalUnitSuccPadicSubmodule n
  let eHigher : deep ≃ₗ[R] higher :=
    F.higherPrincipalUnitLinearEquivPadicSubmodule hr
  let hHigherFinite : Module.Finite R higher :=
    F.higherPrincipalUnitPadicSubmodule_moduleFinite hr inferInstance
  let : Module.Free R deep := Module.Free.of_equiv eDeep.symm
  let hHigherFree : Module.Free R higher := Module.Free.of_equiv eHigher
  have hrankDeep : Module.finrank R deep = d := by
    simpa [d] using eDeep.finrank_eq
  have hrankHigher : Module.finrank R higher = d := by
    calc
      Module.finrank R higher = Module.finrank R deep := eHigher.finrank_eq.symm
      _ = d := hrankDeep
  exact
    { moduleFinite := hHigherFinite
      moduleFree := hHigherFree
      finrank := hrankHigher }

/-- The finite quotient map in the mixed-characteristic field-unit structure theorem, with the
deep logarithmic
lattice identified as its finite free kernel. -/
noncomputable def mixedFirstPrincipalUnitFiniteQuotientSetup
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let p := F.residueCharacteristic
    let R := ℤ_[p]
    let M := Additive
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (F.toCompleteDVF) 1)
    letI : MixedQPadicContext F := mixedQPadicContext F
    letI : Module R M :=
      CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
    let d := Module.finrank ℚ_[p] K
    let q :=
      CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
        F.toCompleteDVF n
    letI : Module R q :=
      CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule F n
    FiniteQuotientSetup R M q d := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let R := ℤ_[p]
  let M := Additive
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
    (F.toCompleteDVF) 1)
  letI : MixedQPadicContext F := mixedQPadicContext F
  letI : Module R M :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
  let d : ℕ := Module.finrank ℚ_[p] K
  let higher := F.principalUnitSuccPadicSubmodule n
  let kernelData := mixed_principalUnitSuccKernelData
    v hv n hlevel
  let q :=
    CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
      F.toCompleteDVF n
  letI : Module R q :=
    CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule F n
  letI : Finite q := inferInstance
  letI : Module.Finite R q := Module.Finite.of_finite
  let projection : M →ₗ[R] q := F.principalUnitQuotientProjectionLinear n
  let U :=
    toPrincipalUnitFiltration
    F.toCompleteDVF
  let quotientKernel := (U.principalUnitSubgroup (n + 1)).subgroupOf
    (U.principalUnitSubgroup 1)
  have hsur : Function.Surjective projection := by
    intro y
    obtain ⟨x, hx⟩ :=
      QuotientGroup.mk'_surjective quotientKernel (Additive.toMul y.val)
    refine ⟨Additive.ofMul x, ?_⟩
    apply (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv
      F.toCompleteDVF n).injective
    apply Additive.toMul.injective
    exact hx
  let N := LinearMap.ker projection
  have hN : N = higher :=
    F.principalUnitQuotientProjectionLinear_ker n
  letI hNFinite : Module.Finite R N := by
    rw [hN]
    exact kernelData.moduleFinite
  letI hNFree : Module.Free R N := by
    rw [hN]
    exact kernelData.moduleFree
  have hrankN : Module.finrank R N = d := by
    rw [hN]
    exact kernelData.finrank
  have hqTorsion : Module.IsTorsion R q := by
    intro x
    exact F.discretePrincipalUnitQuotient_moduleIsTorsion n (x := x)
  exact
    { projection := projection
      projection_surjective := hsur
      kernelFinite := hNFinite
      kernelFree := hNFree
      kernelFinrank := hrankN
      quotientTorsion := hqTorsion }

/-- Finite torsion in a module on principal units is cyclic, since it embeds in the field. -/
private theorem isAddCyclic_principalUnit_torsion
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K) (R : Type*) [CommRing R]
    [Module R (Additive (CompleteDVF.higherPrincipalUnitGroup F 1))]
    [Finite (Submodule.torsion R (Additive (CompleteDVF.higherPrincipalUnitGroup F 1)))] :
    IsAddCyclic (Submodule.torsion R (Additive (CompleteDVF.higherPrincipalUnitGroup F 1))) := by
  let U1 := CompleteDVF.higherPrincipalUnitGroup F 1
  let T := Submodule.torsion R (Additive U1)
  let valuationUnitsToFieldUnits := CompleteDVF.valuationSubringUnitsToFieldUnits F
  let principalToField : U1 →* K :=
    (Units.coeHom K).comp (valuationUnitsToFieldUnits.comp U1.subtype)
  have hvaluationUnitsToFieldUnits : Function.Injective valuationUnitsToFieldUnits := by
    intro x y hxy
    apply Units.ext
    apply Subtype.ext
    have hxy' := congrArg (fun z : Kˣ => (z : K)) hxy
    simpa [valuationUnitsToFieldUnits] using hxy'
  have hprincipalToField : Function.Injective principalToField :=
    Units.val_injective.comp (hvaluationUnitsToFieldUnits.comp Subtype.val_injective)
  exact isAddCyclic_of_injective_multiplicative_map (A := T) (U := U1)
    T.subtype.toAddMonoidHom principalToField T.subtype_injective hprincipalToField

/-- Algebraic data for the first principal units in the mixed-characteristic field-unit
structure theorem.
The deep logarithmic lattice supplies the free kernel; the finite-level
principal-unit quotient detects all torsion. -/
noncomputable def chosenMixedFirstPrincipalUnitAlgebraicData
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let p := F.residueCharacteristic
    let R := ℤ_[p]
    let M := Additive
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (F.toCompleteDVF) 1)
    letI : MixedQPadicContext F := mixedQPadicContext F
    letI : Module R M :=
      CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
    let d := Module.finrank ℚ_[p] K
    FirstPrincipalUnitAlgebraicData R M p d := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let R := ℤ_[p]
  let M := Additive
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
    (F.toCompleteDVF) 1)
  letI : MixedQPadicContext F := mixedQPadicContext F
  letI : Module R M :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
  let d : ℕ := Module.finrank ℚ_[p] K
  let q :=
    CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
      F.toCompleteDVF n
  letI : Module R q :=
    CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule F n
  letI : Finite q := inferInstance
  letI : Module.Finite R q := Module.Finite.of_finite
  let setup :=
    mixedFirstPrincipalUnitFiniteQuotientSetup
      v hv n hlevel
  let exactData : FiniteRankTorsionData R M q d :=
    finiteRankTorsionDataOfSetup d setup
  letI : Module.Finite R M := exactData.moduleFinite
  let T := Submodule.torsion R M
  letI hTAddCommGroup : AddCommGroup T := Submodule.addCommGroup T
  letI hTAddGroup : AddGroup T := hTAddCommGroup.toAddGroup
  letI hTModule : Module R T := Submodule.module T
  letI : Finite T := exactData.finiteTorsion
  letI hqAddGroup : AddGroup q := inferInstance
  let tproj : T →ₗ[R] q := exactData.torsionProjection
  have hqP : IsPGroup p (Multiplicative q) :=
    F.discretePrincipalUnitQuotient_isPGroup n
  let hcardExists :=
    exists_card_eq_prime_power_of_injective_addMonoidHom
      tproj.toAddMonoidHom exactData.torsionProjection_injective hqP
  let a : ℕ := Classical.choose hcardExists
  have hcard : Nat.card T = p ^ a :=
    Classical.choose_spec hcardExists
  refine
    { a := a
      moduleFinite := exactData.moduleFinite
      finiteTorsion := exactData.finiteTorsion
      cyclicTorsion := by
        exact isAddCyclic_principalUnit_torsion F.toCompleteDVF R
      cardTorsion := hcard
      finrankFree := exactData.finrankFree }

/-- The mixed-characteristic field-unit structure theorem, principal-unit factor in its literal
algebraic and
topological form.  The finite torsion is a cyclic `p`-group and the free
factor has rank `[K : Q_p]`. -/
noncomputable def mixedFirstPrincipalUnitStructure
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    Σ a : ℕ,
      Multiplicative
          (ZMod (F.residueCharacteristic ^ a) ×
            (Fin d → ℤ_[F.residueCharacteristic])) ≃ₜ*
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (F.toCompleteDVF) 1 := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let R := ℤ_[p]
  let M := Additive
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
    (F.toCompleteDVF) 1)
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d : ℕ := Module.finrank ℚ_[p] K
  let T := Submodule.torsion R M
  letI : AddCommGroup T := Submodule.addCommGroup T
  letI : Module R T := Submodule.module T
  let data :=
    chosenMixedFirstPrincipalUnitAlgebraicData
      v hv n hlevel
  letI : Module.Finite R M := data.moduleFinite
  letI : Finite T := data.finiteTorsion
  letI : ContinuousAdd M :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicContinuousAddOfWithZeroValuation v
  letI : ContinuousSMul R M :=
    continuousSMul_padicInt_firstPrincipalUnit_ofWithZeroValuation v
  letI : CompactSpace M := Module.Finite.compactSpace R M
  letI : T2Space M :=
    T2Space.of_injective_continuous Additive.toMul.injective continuous_toMul
  let eAdd :=
    CompleteDVF.higherPrincipalUnitGroup.chosenPadicModuleContinuousAddEquivZModProdFinPi
      p M data.a d data.cyclicTorsion data.cardTorsion data.finrankFree
  exact ⟨data.a, continuousMulEquivOfAdditiveTarget eAdd⟩

/-- The mixed-characteristic field-unit structure theorem, principal-unit factor with the
logarithmic depth
chosen internally.  Thus the statement retains only the hypotheses attached
to the local field and a normalized valuation. -/
noncomputable def chosenMixedFirstPrincipalUnitStructureOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    Σ a : ℕ,
      Multiplicative
          (ZMod (F.residueCharacteristic ^ a) ×
            (Fin d → ℤ_[F.residueCharacteristic])) ≃ₜ*
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          (F.toCompleteDVF) 1 := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hex := exists_nat_gt
    ((ramificationIndexOfWithZeroValuation v : ℚ) /
      ((F.residueCharacteristic : ℚ) - 1))
  let n : ℕ := Classical.choose hex
  have hn := Classical.choose_spec hex
  exact mixedFirstPrincipalUnitStructure
    v hv n (by simpa [F] using hn)

end LocalField
end LocalFieldTheory.DiscreteValuationField
