/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.Instances
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.H0
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.HMinusOne
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Trivial
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Quotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Cohomology
/-!
# Finite-support decompositions of actual ideles

For a finite set `S` of finite places, this file identifies the actual
subgroup `I_K^S` with the product of all archimedean local groups, the
full multiplicative groups at places in `S`, and the local unit groups
away from `S`.  The construction is componentwise and uses the genuine
restricted-product membership condition.

For a finite family of base places in a Galois extension, it also
assembles the local tensor-algebra decomposition and proves its
equivariance for the full Galois action.  Finally, the concrete
unramified local class-field theorem is transported through Shapiro to
show that every unramified induced integer-unit block has trivial
`H⁰` and `H⁻¹`.
-/

open scoped NumberField RestrictedProduct ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- The finite local factors occurring in `I_F^S`: arbitrary local
elements on `S`, and integral local units away from `S`. -/
abbrev FiniteSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S},
      (v.1.adicCompletion F)ˣ) ×
    (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (v.1.adicCompletionIntegers F).units)

/-- The complete product model for `I_F^S`, including every
archimedean component. -/
abbrev IdeleSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  InfiniteIdeleGroup F × FiniteSPlaceFactors (F := F) S

/-- Assemble prescribed local factors into a finite idele.  Restricted
product membership follows because the only possibly nonintegral
components lie in the finite set `S`. -/
noncomputable def finiteIdeleOfSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : FiniteSPlaceFactors (F := F) S) :
    FiniteIdeleGroup F := by
  classical
  let f : ∀ v : HeightOneSpectrum (𝓞 F),
      (v.adicCompletion F)ˣ :=
    fun v ↦ if hv : v ∈ S then
      x.1 ⟨v, hv⟩
    else
      (x.2 ⟨v, hv⟩ :
        (v.adicCompletion F)ˣ)
  refine ⟨f, S.eventually_cofinite_notMem.mono ?_⟩
  intro v hv
  simp only [f, dite_eq_right hv]
  exact (x.2 ⟨v, hv⟩).2

@[simp]
theorem finiteIdeleOfSPlaceFactors_apply_mem
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : FiniteSPlaceFactors (F := F) S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) :
    finiteIdeleOfSPlaceFactors S x v = x.1 ⟨v, hv⟩ := by
  simp [finiteIdeleOfSPlaceFactors, hv]

@[simp]
theorem finiteIdeleOfSPlaceFactors_apply_notMem
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : FiniteSPlaceFactors (F := F) S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    finiteIdeleOfSPlaceFactors S x v =
      (x.2 ⟨v, hv⟩ : (v.adicCompletion F)ˣ) := by
  simp [finiteIdeleOfSPlaceFactors, hv]

/-- The finite part of the actual `S`-idele group is exactly the
displayed product of local multiplicative groups and local unit groups. -/
noncomputable def finiteSupportedAtEquivSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    FiniteIdeleGroup.supportedAt (K := F) (S : Set _) ≃*
      FiniteSPlaceFactors (F := F) S where
  toFun a :=
    ⟨fun v ↦ a.1 v.1,
      fun v ↦ ⟨a.1 v.1, a.2 v.1 v.2⟩⟩
  invFun x :=
    ⟨finiteIdeleOfSPlaceFactors S x, by
      intro v hv
      rw [finiteIdeleOfSPlaceFactors_apply_notMem S x v hv]
      exact (x.2 ⟨v, hv⟩).2⟩
  left_inv a := by
    apply Subtype.ext
    ext v
    by_cases hv : v ∈ S
    · simp [finiteIdeleOfSPlaceFactors_apply_mem, hv]
    · simp [finiteIdeleOfSPlaceFactors_apply_notMem, hv]
  right_inv x := by
    apply Prod.ext
    · funext v
      exact finiteIdeleOfSPlaceFactors_apply_mem S x v.1 v.2
    · funext v
      apply Subtype.ext
      exact finiteIdeleOfSPlaceFactors_apply_notMem S x v.1 v.2
  map_mul' a b := by
    apply Prod.ext
    · funext v
      rfl
    · funext v
      apply Subtype.ext
      rfl

/-- The actual finite-support decomposition:

`I_F^S ≃ I_{F,∞} × (∏_{v∈S} F_vˣ) ×
  (∏_{v∉S} O_vˣ)`.
-/
noncomputable def ideleSupportedAtEquivInfiniteProd
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IdeleGroup.supportedAt (K := F) (S : Set _) ≃*
      InfiniteIdeleGroup F ×
        FiniteIdeleGroup.supportedAt (K := F) (S : Set _) where
  toFun a := ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The actual `S`-idele group identified with its complete family of
archimedean, unrestricted finite, and integral finite local factors. -/
noncomputable def ideleSupportedAtEquivSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IdeleGroup.supportedAt (K := F) (S : Set _) ≃*
      IdeleSPlaceFactors (F := F) S :=
  (ideleSupportedAtEquivInfiniteProd S).trans
    ((MulEquiv.refl (InfiniteIdeleGroup F)).prodCongr
      (finiteSupportedAtEquivSPlaceFactors S))

@[simp]
theorem ideleSupportedAtEquivSPlaceFactors_infinite
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : IdeleGroup.supportedAt (K := F) (S : Set _)) :
    (ideleSupportedAtEquivSPlaceFactors S a).1 = a.1.1 :=
  rfl

@[simp]
theorem ideleSupportedAtEquivSPlaceFactors_inside
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : IdeleGroup.supportedAt (K := F) (S : Set _))
    (v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S}) :
    (ideleSupportedAtEquivSPlaceFactors S a).2.1 v =
      a.1.2 v.1 :=
  rfl

@[simp]
theorem ideleSupportedAtEquivSPlaceFactors_outside_coe
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : IdeleGroup.supportedAt (K := F) (S : Set _))
    (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    ((ideleSupportedAtEquivSPlaceFactors S a).2.2 v :
        (v.1.adicCompletion F)ˣ) =
      a.1.2 v.1 :=
  rfl

section FiniteTensorFamily

universe uK uL uι

variable {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual scalar-extended local tensor factors over a family of
base places. -/
abbrev LocalTensorFamily {ι : Type uι}
    (d : ι → LocalPlaceDatum K L) :=
  ∀ i, (LocalTensorAlgebra (L := L) (d i).base)ˣ

/-- The componentwise natural Galois action on a family of local tensor
factors. -/
@[reducible]
noncomputable def localTensorFamilyAction {ι : Type uι}
    (d : ι → LocalPlaceDatum K L) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (LocalTensorFamily d) := by
  letI : ∀ i, MulDistribMulAction (L ≃ₐ[K] L)
      (LocalTensorAlgebra (L := L) (d i).base)ˣ :=
    fun i ↦ localTensorUnitsAction (d i).base
  exact piMulDistribMulAction (L ≃ₐ[K] L)
    (fun i ↦ (LocalTensorAlgebra (L := L) (d i).base)ˣ)

/-- The componentwise induced-module action on a local block family. -/
@[reducible]
noncomputable def localBlockFamilyAction {ι : Type uι}
    (d : ι → LocalPlaceDatum K L) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (LocalBlockFamily d) := by
  letI : ∀ i, MulDistribMulAction
      (absoluteValueDecompositionGroup K (d i).extension.1)
      (LocalizedCompletion
        (d i).base (d i).extension)ˣ :=
    fun i ↦ decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension
  letI : ∀ i, MulDistribMulAction (L ≃ₐ[K] L)
      (LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension) :=
    fun i ↦ inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K (d i).extension.1)
  exact piMulDistribMulAction (L ≃ₐ[K] L)
    (fun i ↦ LocalPlaceBlock
      (d i).base (d i).base_isNontrivial
      (d i).extension)

/-- The componentwise local tensor equivalence realizes a finite (or arbitrary) family of
actual local tensor unit groups as the corresponding family of induced
local blocks. -/
noncomputable def localTensorFamilyEquivLocalBlockFamily
    {ι : Type uι} (d : ι → LocalPlaceDatum K L) :
    LocalTensorFamily d ≃* LocalBlockFamily d := by
  letI : ∀ i, MulDistribMulAction
      (absoluteValueDecompositionGroup K (d i).extension.1)
      (LocalizedCompletion
        (d i).base (d i).extension)ˣ :=
    fun i ↦ decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension
  letI hK : ∀ i,
      Algebra K (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.extensionCompletionAlgebra
      (K := K) (d i).extension.1
  letI : ∀ i, SMul K (d i).extension.1.Completion :=
    fun i ↦ (hK i).toSMul
  letI : ∀ i, Algebra (d i).base.Completion
      (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.completionAlgebra
      (d i).base (d i).extension.1 (d i).extension.2
  exact MulEquiv.piCongrRight fun i ↦
    localTensorUnitsEquivLocalPlaceBlock
      (d i).base (d i).base_isNontrivial
      (d i).extension

/-- The family realization is equivariant for the full Galois action,
not merely componentwise multiplicative. -/
theorem localTensorFamilyEquivLocalBlockFamily_smul
    {ι : Type uι} (d : ι → LocalPlaceDatum K L)
    (τ : L ≃ₐ[K] L) (z : LocalTensorFamily d) :
    localTensorFamilyEquivLocalBlockFamily d
        ((localTensorFamilyAction d).smul τ z) =
      (localBlockFamilyAction d).smul τ
        (localTensorFamilyEquivLocalBlockFamily d z) := by
  funext i
  let _ :=
    decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) (d i).extension.1
  let _ : SMul K (d i).extension.1.Completion :=
    hK.toSMul
  let _ :=
    AbsoluteValue.completionAlgebra
      (d i).base (d i).extension.1
      (d i).extension.2
  let _ : ∀ w' : AbsoluteValueExtension (d i).base L,
      Algebra (d i).base.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra
      (d i).base w'.1 w'.2
  let _ :=
    localTensorUnitsAction (K := K) (L := L)
      (d i).base
  let _ : MulDistribMulAction (L ≃ₐ[K] L)
      (LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension) :=
    inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K (d i).extension.1)
  change
    localTensorUnitsEquivLocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension (τ • z i) =
      τ •
        localTensorUnitsEquivLocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension (z i)
  exact localTensorUnitsEquivLocalPlaceBlock_smul
    (d i).base (d i).base_isNontrivial
    (d i).extension τ (z i)

/-- Equivariance of the inverse family realization.  This is often the
convenient direction when local induced blocks have already been
constructed. -/
theorem localTensorFamilyEquivLocalBlockFamily_symm_smul
    {ι : Type uι} (d : ι → LocalPlaceDatum K L)
    (τ : L ≃ₐ[K] L) (z : LocalBlockFamily d) :
    (localTensorFamilyEquivLocalBlockFamily d).symm
        ((localBlockFamilyAction d).smul τ z) =
      (localTensorFamilyAction d).smul τ
        ((localTensorFamilyEquivLocalBlockFamily d).symm z) := by
  apply (localTensorFamilyEquivLocalBlockFamily d).injective
  rw [localTensorFamilyEquivLocalBlockFamily_smul]
  simp

end FiniteTensorFamily

section UnramifiedLocalUnits

/-- Outside the ramified support, the local integer-unit factor has
trivial low-degree Tate cohomology.  This generator-explicit form is the
one needed after restricting a global cyclic generator to a decomposition
group. -/
theorem unramifiedLocalIntegerUnitsHerbrand_subsingleton
    (k ell : Type)
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [ValuativeRel ell] [UniformSpace ell]
    [IsUniformAddGroup ell]
    [IsNonarchimedeanLocalField ell]
    [Valuation.HasExtension
      (ValuativeRel.valuation k) (ValuativeRel.valuation ell)]
    [IsIntegralClosure 𝒪[ell] 𝒪[k] ell]
    [Module.Finite 𝒪[k] 𝒪[ell]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      k ell]
    (g : Gal(ell / k))
    (hg : ∀ σ : Gal(ell / k),
      σ ∈ Subgroup.zpowers g) :
    letI :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
        k ell
    Subsingleton
        (HerbrandH0 (Gal(ell / k)) 𝒪[ell]ˣ) ∧
      Subsingleton
        (HerbrandHMinusOne
          (Gal(ell / k)) 𝒪[ell]ˣ g) := by
  exact
    (unramified_units_tateCohomology_and_norm_surjective_for_generator
      k ell g hg).1

/-- Canonical Frobenius form of the same outside-`S` vanishing. -/
theorem unramifiedLocalIntegerUnitsHerbrand_subsingleton_frobenius
    (k ell : Type)
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [ValuativeRel ell] [UniformSpace ell]
    [IsUniformAddGroup ell]
    [IsNonarchimedeanLocalField ell]
    [Valuation.HasExtension
      (ValuativeRel.valuation k) (ValuativeRel.valuation ell)]
    [IsIntegralClosure 𝒪[ell] 𝒪[k] ell]
    [Module.Finite 𝒪[k] 𝒪[ell]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      k ell] :
    let φ := arithmeticFrobeniusOfUnramifiedValuation k ell
    letI :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
        k ell
    Subsingleton
        (HerbrandH0 (Gal(ell / k)) 𝒪[ell]ˣ) ∧
      Subsingleton
        (HerbrandHMinusOne
          (Gal(ell / k)) 𝒪[ell]ˣ φ) := by
  exact
    (unramified_units_tateCohomology_and_norm_surjective
      k ell).1

section InducedOutsideSBlock

universe uG

variable {G : Type uG} [Group G] [Fintype G]

/-- Shapiro plus change of group identifies an induced unramified
integer-unit block with its actual local Galois cohomology in degree
zero. -/
noncomputable def unramifiedInducedIntegerUnitsHerbrandH0Equiv
    (H : Subgroup G)
    (k ell : Type)
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell]
    [ValuativeRel ell]
    [MulDistribMulAction (Gal(ell / k)) 𝒪[ell]ˣ]
    (e : H ≃* Gal(ell / k))
    (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    letI : MulDistribMulAction H 𝒪[ell]ˣ :=
      MulDistribMulAction.compHom 𝒪[ell]ˣ e.toMonoidHom
    letI : Fintype H := Fintype.ofFinite H
    HerbrandH0 G (InducedModule (B := 𝒪[ell]ˣ) H) ≃*
      HerbrandH0 (Gal(ell / k)) 𝒪[ell]ˣ := by
  letI : MulDistribMulAction H 𝒪[ell]ˣ :=
    MulDistribMulAction.compHom 𝒪[ell]ˣ e.toMonoidHom
  letI : Fintype H := Fintype.ofFinite H
  exact
    (inducedHerbrandH0EquivOfFiniteCyclic H σ hσ).trans
      (herbrandH0CompMulEquiv (A := 𝒪[ell]ˣ) e)

/-- The corresponding Shapiro and change-of-group equivalence in degree
minus one. -/
noncomputable def unramifiedInducedIntegerUnitsHerbrandHMinusOneEquiv
    (H : Subgroup G)
    (k ell : Type)
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell]
    [ValuativeRel ell]
    [MulDistribMulAction (Gal(ell / k)) 𝒪[ell]ˣ]
    (e : H ≃* Gal(ell / k))
    (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    letI : MulDistribMulAction H 𝒪[ell]ˣ :=
      MulDistribMulAction.compHom 𝒪[ell]ˣ e.toMonoidHom
    letI : Fintype H := Fintype.ofFinite H
    HerbrandHMinusOne G
        (InducedModule (B := 𝒪[ell]ˣ) H) σ ≃*
      HerbrandHMinusOne (Gal(ell / k)) 𝒪[ell]ˣ
        (e (subgroupGeneratorOfGenerator H σ hσ)) := by
  letI : MulDistribMulAction H 𝒪[ell]ˣ :=
    MulDistribMulAction.compHom 𝒪[ell]ˣ e.toMonoidHom
  letI : Fintype H := Fintype.ofFinite H
  exact
    (inducedHerbrandHMinusOneEquivOfFiniteCyclic
      H σ hσ).trans
      (herbrandHMinusOneCompMulEquiv
        (A := 𝒪[ell]ˣ) e
        (subgroupGeneratorOfGenerator H σ hσ))

/-- An unramified outside-`S` induced unit block contributes neither
degree-zero nor degree-minus-one Tate cohomology. -/
theorem unramifiedInducedIntegerUnitsHerbrand_subsingleton
    (H : Subgroup G)
    (k ell : Type)
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [ValuativeRel ell] [UniformSpace ell]
    [IsUniformAddGroup ell]
    [IsNonarchimedeanLocalField ell]
    [Valuation.HasExtension
      (ValuativeRel.valuation k) (ValuativeRel.valuation ell)]
    [IsIntegralClosure 𝒪[ell] 𝒪[k] ell]
    [Module.Finite 𝒪[k] 𝒪[ell]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      k ell]
    (e : H ≃* Gal(ell / k))
    (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    letI : MulDistribMulAction (Gal(ell / k)) 𝒪[ell]ˣ :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
        k ell
    letI : MulDistribMulAction H 𝒪[ell]ˣ :=
      MulDistribMulAction.compHom 𝒪[ell]ˣ e.toMonoidHom
    letI : Fintype H := Fintype.ofFinite H
    Subsingleton
        (HerbrandH0 G
          (InducedModule (B := 𝒪[ell]ˣ) H)) ∧
      Subsingleton
        (HerbrandHMinusOne G
          (InducedModule (B := 𝒪[ell]ˣ) H) σ) := by
  let _ : MulDistribMulAction (Gal(ell / k)) 𝒪[ell]ˣ :=
    galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
      k ell
  let _ : MulDistribMulAction H 𝒪[ell]ˣ :=
    MulDistribMulAction.compHom 𝒪[ell]ˣ e.toMonoidHom
  let _ : Fintype H := Fintype.ofFinite H
  let δ := subgroupGeneratorOfGenerator H σ hσ
  have hδ : ∀ τ : Gal(ell / k),
      τ ∈ Subgroup.zpowers (e δ) := by
    intro τ
    have hmem :
        e.symm τ ∈ Subgroup.zpowers δ :=
      subgroupGeneratorOfGenerator_generates H σ hσ (e.symm τ)
    have himage :
        e (e.symm τ) ∈
          (Subgroup.zpowers δ).map e.toMonoidHom :=
      ⟨e.symm τ, hmem, rfl⟩
    rw [MonoidHom.map_zpowers] at himage
    simpa using himage
  have hlocal :=
    unramifiedLocalIntegerUnitsHerbrand_subsingleton
      k ell (e δ) hδ
  constructor
  · let E :=
      unramifiedInducedIntegerUnitsHerbrandH0Equiv
        H k ell e σ hσ
    exact
      ⟨fun x y ↦ E.injective
        (by exact @Subsingleton.elim _ hlocal.1 (E x) (E y))⟩
  · let E :=
      unramifiedInducedIntegerUnitsHerbrandHMinusOneEquiv
        H k ell e σ hσ
    exact
      ⟨fun x y ↦ E.injective
        (by exact @Subsingleton.elim _ hlocal.2 (E x) (E y))⟩

end InducedOutsideSBlock

end UnramifiedLocalUnits
