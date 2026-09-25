/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Definitions

/-!
# Simplicity of the tensor unit

In the setting of Deligne's theorem — an abelian ℂ-linear rigid
monoidal category whose unit endomorphisms are exactly the scalars —
the tensor unit is a simple object.  This is Proposition 1.17 of
Deligne–Milne, *Tannakian categories*.

The argument follows Deligne–Milne.  Given a nonzero subobject
`i : U ⟶ 𝟙`, write `V` for the cokernel of `i` and `D : 𝟙 ⟶ 𝟙 ⊗ Uᘁ`
for the mate of `i` under the duality adjunction, and set
`W := ker D`.  Exactness of the tensor product in each variable
(rigidity provides two-sided adjoints to whiskering) yields
`V ⊗ U = 0`, `U ⊗ V = 0` and `W ⊗ U = 0`, from which the composite
`W ⟶ 𝟙 ⟶ V` is an isomorphism.  The resulting splitting of `𝟙 ↠ V`
produces an idempotent unit endomorphism, and `End (𝟙) = ℂ` has no
idempotents besides `0` and `1`: the value `1` would force `i = 0`,
so the idempotent vanishes, `V = 0`, and `i` is an isomorphism.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

/-! ## Scalars on the unit

Consequences of `HasScalarUnit` alone: the identity of the unit is
nonzero, and the only idempotent endomorphisms of the unit are `0`
and the identity. -/

section UnitScalars

variable {A : Type u}

/-- Under `HasScalarUnit`, the identity of the unit is nonzero. -/
theorem id_unit_ne_zero
    [Category.{v} A] [Preadditive A] [Linear ℂ A] [MonoidalCategory A]
    (hu : HasScalarUnit A) : 𝟙 (𝟙_ A) ≠ 0 := by
  intro h
  have h1 : ((1 : ℂ) • 𝟙 (𝟙_ A) : 𝟙_ A ⟶ 𝟙_ A) = (0 : ℂ) • 𝟙 (𝟙_ A) := by
    rw [one_smul, zero_smul, h]
  exact one_ne_zero (hu.injective h1)

/-- Under `HasScalarUnit`, the only idempotent endomorphisms of the
unit are `0` and the identity: composition of scalar endomorphisms
is multiplication in ℂ, and a field has no other idempotents. -/
theorem HasScalarUnit.idempotent_eq_zero_or_id
    [Category.{v} A] [Preadditive A] [Linear ℂ A] [MonoidalCategory A]
    (hu : HasScalarUnit A)
    {e : 𝟙_ A ⟶ 𝟙_ A} (he : e ≫ e = e) : e = 0 ∨ e = 𝟙 (𝟙_ A) := by
  obtain ⟨c, hc⟩ := hu.surjective e
  replace hc : c • 𝟙 (𝟙_ A) = e := hc
  have h1 : ((c * c) • 𝟙 (𝟙_ A) : 𝟙_ A ⟶ 𝟙_ A) = c • 𝟙 (𝟙_ A) := by
    calc ((c * c) • 𝟙 (𝟙_ A) : 𝟙_ A ⟶ 𝟙_ A)
        = (c • 𝟙 (𝟙_ A)) ≫ (c • 𝟙 (𝟙_ A)) := by
          simp [Linear.comp_smul, smul_smul]
      _ = e ≫ e := by rw [hc]
      _ = e := he
      _ = c • 𝟙 (𝟙_ A) := hc.symm
  have hcc : c * c = c := hu.injective h1
  have hcases : c = 0 ∨ c = 1 := by
    rcases mul_eq_zero.mp
        (show c * (c - 1) = 0 by rw [mul_sub, mul_one, hcc, sub_self])
      with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hcases with h | h
  · exact Or.inl (by rw [← hc, h, zero_smul])
  · exact Or.inr (by rw [← hc, h, one_smul])

end UnitScalars

/-! ## Exactness of whiskering

In a rigid category each whiskering functor has adjoints on both
sides, so it preserves monomorphisms, epimorphisms and kernels. -/

section Whiskering

variable {A : Type u}

/-- Whiskering on the left preserves monomorphisms. -/
private theorem tensorLeft_preservesMono
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    (X : A) :
    (tensorLeft X).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_adjunction (tensorLeftAdjunction X (Xᘁ))

/-- Whiskering on the left preserves epimorphisms. -/
private theorem tensorLeft_preservesEpi
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    (X : A) :
    (tensorLeft X).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_adjunction (tensorLeftAdjunction (ᘁX) X)

/-- Whiskering on the right preserves monomorphisms. -/
private theorem tensorRight_preservesMono
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    (X : A) :
    (tensorRight X).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_adjunction (tensorRightAdjunction (ᘁX) X)

/-- Whiskering on the right preserves epimorphisms. -/
private theorem tensorRight_preservesEpi
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    (X : A) :
    (tensorRight X).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_adjunction (tensorRightAdjunction X (Xᘁ))

/-- Whiskering on the left preserves limits, in particular kernels. -/
private theorem tensorLeft_preservesLimits
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    (X : A) :
    PreservesLimitsOfSize.{0, 0} (tensorLeft X) :=
  (tensorLeftAdjunction X (Xᘁ)).rightAdjoint_preservesLimits

end Whiskering

/-! ## The mate of a subobject of the unit

For a monomorphism `i : U ⟶ 𝟙` the mate `D : 𝟙 ⟶ 𝟙 ⊗ Uᘁ` under the
duality adjunction detects which maps into the unit are annihilated
by tensoring with `U`: if `x ≫ D = 0` then `x ▷ U = 0`. -/

section Mate

variable {A : Type u}

/-- A monomorphism that vanishes has a zero source. -/
private theorem isZero_of_mono_eq_zero [Category.{v} A] [Preadditive A]
    {X Y : A} (f : X ⟶ Y) [Mono f]
    (h : f = 0) : IsZero X := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono f, h, comp_zero, zero_comp]

/-- The duality correspondence sends zero to zero. -/
private theorem tensorRightHomEquiv_zero
    [Category.{v} A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A]
    (X Y Y' Z : A)
    [ExactPairing Y Y'] : tensorRightHomEquiv X Y Y' Z 0 = 0 := by
  simp [tensorRightHomEquiv]

/-- The inverse duality correspondence sends zero to zero. -/
private theorem tensorRightHomEquiv_symm_zero
    [Category.{v} A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A]
    (X Y Y' Z : A)
    [ExactPairing Y Y'] : (tensorRightHomEquiv X Y Y' Z).symm 0 = 0 := by
  simp [tensorRightHomEquiv]

/-- The mate `𝟙 ⟶ 𝟙 ⊗ Uᘁ` of a subobject inclusion `i : U ⟶ 𝟙`
under the duality adjunction for `U`. -/
private noncomputable def unitMate
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    {U : A} (i : U ⟶ 𝟙_ A) :
    𝟙_ A ⟶ 𝟙_ A ⊗ Uᘁ :=
  tensorRightHomEquiv (𝟙_ A) U (Uᘁ) (𝟙_ A) ((λ_ U).hom ≫ i)

/-- Maps into the unit annihilated by the mate are annihilated by
tensoring with the subobject. -/
private theorem whiskerRight_eq_zero_of_comp_unitMate
    [Category.{v} A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [RigidCategory A]
    {U X : A}
    (i : U ⟶ 𝟙_ A) [Mono i] (x : X ⟶ 𝟙_ A)
    (hx : x ≫ unitMate i = 0) : x ▷ U = 0 := by
  have h1 : (tensorRightHomEquiv X U (Uᘁ) (𝟙_ A)).symm (x ≫ unitMate i)
      = x ▷ U ≫ (λ_ U).hom ≫ i := by
    rw [tensorRightHomEquiv_symm_naturality, unitMate,
      Equiv.symm_apply_apply]
  rw [hx, tensorRightHomEquiv_symm_zero] at h1
  have h2 : x ▷ U ≫ (λ_ U).hom = 0 := by
    rw [← cancel_mono i, Category.assoc, ← h1, zero_comp]
  rw [← cancel_mono (λ_ U).hom, h2, zero_comp]

end Mate

/-! ## Vanishing tensor products

For a subobject `i : U ⟶ 𝟙` with cokernel `V`, both `V ⊗ U` and
`U ⊗ V` vanish: the composite of the whiskered epimorphism and the
whiskered monomorphism through them is `i ≫ π = 0`.  The kernel `W`
of the mate also satisfies `W ⊗ U = 0`, by construction of the
mate. -/

section Vanishing

variable {A : Type u}

/-- `V ⊗ U = 0` for the cokernel `V` of a subobject `U` of the
unit. -/
private theorem isZero_coker_tensor
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [RigidCategory A]
    {U : A} (i : U ⟶ 𝟙_ A) [Mono i] :
    IsZero (cokernel i ⊗ U) := by
  have := tensorLeft_preservesMono (A := A) (cokernel i)
  have := tensorRight_preservesEpi (A := A) U
  have : Mono (cokernel i ◁ i) :=
    Functor.map_mono (tensorLeft (cokernel i)) i
  have : Epi (cokernel.π i ▷ U) :=
    Functor.map_epi (tensorRight U) (cokernel.π i)
  have hcomp : cokernel.π i ▷ U ≫ cokernel i ◁ i = 0 := by
    rw [← whisker_exchange]
    simp [unitors_inv_equal]
  exact isZero_of_mono_eq_zero _ (zero_of_epi_comp _ hcomp)

/-- `U ⊗ V = 0` for the cokernel `V` of a subobject `U` of the
unit. -/
private theorem isZero_tensor_coker
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [RigidCategory A]
    {U : A} (i : U ⟶ 𝟙_ A) [Mono i] :
    IsZero (U ⊗ cokernel i) := by
  have := tensorRight_preservesMono (A := A) (cokernel i)
  have := tensorLeft_preservesEpi (A := A) U
  have : Mono (i ▷ cokernel i) :=
    Functor.map_mono (tensorRight (cokernel i)) i
  have : Epi (U ◁ cokernel.π i) :=
    Functor.map_epi (tensorLeft U) (cokernel.π i)
  have hcomp : U ◁ cokernel.π i ≫ i ▷ cokernel i = 0 := by
    rw [whisker_exchange]
    simp [unitors_equal]
  exact isZero_of_mono_eq_zero _ (zero_of_epi_comp _ hcomp)

/-- `W ⊗ U = 0` for the kernel `W` of the mate of `i : U ⟶ 𝟙`. -/
private theorem isZero_kernelMate_tensor
    [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [RigidCategory A]
    {U : A} (i : U ⟶ 𝟙_ A)
    [Mono i] : IsZero (kernel (unitMate i) ⊗ U) := by
  have := tensorRight_preservesMono (A := A) U
  have : Mono (kernel.ι (unitMate i) ▷ U) :=
    Functor.map_mono (tensorRight U) (kernel.ι (unitMate i))
  exact isZero_of_mono_eq_zero _
    (whiskerRight_eq_zero_of_comp_unitMate i _ (kernel.condition _))

end Vanishing

/-! ## The kernel of the mate maps onto the cokernel

Whiskering the mate by the cokernel `V` kills it, because the mate
factors through `i` and `V ⊗ U = 0`.  Since whiskering preserves
kernels, `V ◁ kernel.ι` is then the kernel of a zero map, hence an
isomorphism `V ⊗ W ≅ V ⊗ 𝟙`. -/

section KernelMate

variable {A : Type u}

/-- Whiskering the mate of `i` by the cokernel of `i` gives zero. -/
private theorem whiskerLeft_unitMate_zero
    [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [RigidCategory A]
    {U : A} (i : U ⟶ 𝟙_ A)
    [Mono i] : cokernel i ◁ unitMate i = 0 := by
  have hz : cokernel i ◁ i = 0 :=
    (isZero_coker_tensor i).eq_zero_of_src _
  have h1 := tensorRightHomEquiv_tensor (Y := U) (unitMate i)
    (𝟙 (cokernel i))
  have h2 : (tensorRightHomEquiv (𝟙_ A) U (Uᘁ) (𝟙_ A)).symm (unitMate i)
      = (λ_ U).hom ≫ i := by
    rw [unitMate, Equiv.symm_apply_apply]
  rw [h2] at h1
  have h3 : (α_ (cokernel i) (𝟙_ A) U).hom
      ≫ (𝟙 (cokernel i) ⊗ₘ ((λ_ U).hom ≫ i)) = 0 := by
    simp [hz]
  rw [h3] at h1
  have h4 : (𝟙 (cokernel i) ⊗ₘ unitMate i)
      ≫ (α_ (cokernel i) (𝟙_ A) (Uᘁ)).inv = 0 := by
    have h5 := congrArg
      (tensorRightHomEquiv (cokernel i ⊗ 𝟙_ A) U (Uᘁ)
        (cokernel i ⊗ 𝟙_ A)) h1
    rwa [Equiv.apply_symm_apply, tensorRightHomEquiv_zero] at h5
  rw [← cancel_mono (α_ (cokernel i) (𝟙_ A) (Uᘁ)).inv, zero_comp,
    ← MonoidalCategory.id_tensorHom]
  exact h4

/-- The cokernel-whiskered kernel inclusion of the mate is an
isomorphism `V ⊗ W ≅ V ⊗ 𝟙`. -/
private theorem isIso_whiskerLeft_kernelMate
    [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [RigidCategory A]
    {U : A} (i : U ⟶ 𝟙_ A)
    [Mono i] : IsIso (cokernel i ◁ kernel.ι (unitMate i)) := by
  have : PreservesLimitsOfSize.{0, 0} (tensorLeft (cokernel i)) :=
    tensorLeft_preservesLimits (cokernel i)
  have hlim := isLimitForkMapOfIsLimit' (tensorLeft (cokernel i))
    (kernel.condition (unitMate i)) (kernelIsKernel (unitMate i))
  have hzero : (tensorLeft (cokernel i)).map (unitMate i) = 0 :=
    whiskerLeft_unitMate_zero i
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hlim
    (𝟙 ((tensorLeft (cokernel i)).obj (𝟙_ A)))
    (by rw [hzero, comp_zero])
  simp only [Fork.ι_ofι] at hl
  have : IsSplitEpi
      ((tensorLeft (cokernel i)).map (kernel.ι (unitMate i))) :=
    IsSplitEpi.mk' ⟨l, hl⟩
  have := tensorLeft_preservesMono (A := A) (cokernel i)
  have : Mono ((tensorLeft (cokernel i)).map (kernel.ι (unitMate i))) :=
    Functor.map_mono _ _
  exact isIso_of_mono_of_epi
    ((tensorLeft (cokernel i)).map (kernel.ι (unitMate i)))

end KernelMate

/-! ## Subobjects of `U` killed by `⊗ U`

A subobject `T` of `U` with `T ⊗ U = 0` is zero: `T ⊗ V` vanishes
because `U ⊗ V` does, and whiskering the exact sequence
`U ⟶ 𝟙 ⟶ V` by `T` exhibits `T ≅ T ⊗ 𝟙` as an extension of the two
vanishing ends. -/

section Subobjects

variable {A : Type u}

/-- A subobject of `U` annihilated by tensoring with `U` is zero. -/
private theorem isZero_of_sub_of_tensor_isZero
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [RigidCategory A]
    {U T : A}
    (i : U ⟶ 𝟙_ A) [Mono i] (t : T ⟶ U) (ht : Mono t)
    (hT : IsZero (T ⊗ U)) : IsZero T := by
  have := ht
  have := tensorRight_preservesMono (A := A) (cokernel i)
  have : Mono (t ▷ cokernel i) :=
    Functor.map_mono (tensorRight (cokernel i)) t
  have hTV : IsZero (T ⊗ cokernel i) :=
    IsZero.of_mono (t ▷ cokernel i) (isZero_tensor_coker i)
  have : PreservesLimitsOfSize.{0, 0} (tensorLeft T) :=
    tensorLeft_preservesLimits T
  have hbase : IsLimit (KernelFork.ofι i (cokernel.condition i)) :=
    Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π i) (cokernel.condition i))
      (cokernelIsCokernel i)
  have hlim := isLimitForkMapOfIsLimit' (tensorLeft T)
    (cokernel.condition i) hbase
  have : Mono (T ◁ cokernel.π i) :=
    Preadditive.mono_of_isZero_kernel' _ hlim hT
  have := tensorLeft_preservesEpi (A := A) T
  have : Epi (T ◁ cokernel.π i) :=
    Functor.map_epi (tensorLeft T) (cokernel.π i)
  have : IsIso (T ◁ cokernel.π i) := isIso_of_mono_of_epi _
  have h1 : IsZero (T ⊗ 𝟙_ A) :=
    hTV.of_iso (asIso (T ◁ cokernel.π i))
  exact h1.of_iso (ρ_ T).symm

end Subobjects

/-! ## The theorem -/

section Main

/-- **The tensor unit is simple** in the setting of Deligne's
theorem: in an abelian ℂ-linear rigid monoidal category whose unit
endomorphisms are exactly the scalars, `𝟙_ A` is a simple object.
This is Proposition 1.17 of Deligne–Milne, *Tannakian categories*. -/
theorem simple_unit_of_hasScalarUnit
    {A : Type u} [Category.{v} A] [Abelian A] [Linear ℂ A]
    [MonoidalCategory A] [MonoidalPreadditive A]
    [RigidCategory A] (hu : HasScalarUnit A) :
    Simple (𝟙_ A) := by
  constructor
  intro U i hi
  have := hi
  constructor
  · -- an isomorphism into the unit is nonzero
    intro hIso h0
    have := hIso
    have hU : IsZero (𝟙_ A) :=
      (isZero_of_mono_eq_zero i h0).of_iso (asIso i).symm
    exact id_unit_ne_zero hu (hU.eq_zero_of_src _)
  · -- a nonzero subobject of the unit is everything
    intro hne
    -- `W ⟶ 𝟙 ⟶ V` is epi: it factors as
    -- `λ⁻¹ ≫ (π ▷ W ≫ V ◁ ι) ≫ ρ` with `V ◁ ι` invertible
    have : IsIso (cokernel i ◁ kernel.ι (unitMate i)) :=
      isIso_whiskerLeft_kernelMate i
    have := tensorRight_preservesEpi (A := A) (kernel (unitMate i))
    have : Epi (cokernel.π i ▷ kernel (unitMate i)) :=
      Functor.map_epi (tensorRight (kernel (unitMate i)))
        (cokernel.π i)
    have hfact : kernel.ι (unitMate i) ≫ cokernel.π i
        = (λ_ (kernel (unitMate i))).inv
          ≫ (cokernel.π i ▷ kernel (unitMate i)
            ≫ cokernel i ◁ kernel.ι (unitMate i))
          ≫ (ρ_ (cokernel i)).hom := by
      rw [← whisker_exchange]
      simp [unitors_inv_equal]
    have : Epi (kernel.ι (unitMate i) ≫ cokernel.π i) := by
      rw [hfact]; infer_instance
    -- `W ⟶ 𝟙 ⟶ V` is mono: its kernel lies in both `U` and `W`,
    -- so it is killed by `⊗ U`, hence zero
    have hbase : IsLimit (KernelFork.ofι i (cokernel.condition i)) :=
      Abelian.monoIsKernelOfCokernel
        (CokernelCofork.ofπ (cokernel.π i) (cokernel.condition i))
        (cokernelIsCokernel i)
    obtain ⟨j, hj⟩ := KernelFork.IsLimit.lift' hbase
      (kernel.ι (kernel.ι (unitMate i) ≫ cokernel.π i)
        ≫ kernel.ι (unitMate i))
      (by rw [Category.assoc]; exact kernel.condition _)
    simp only [Fork.ι_ofι] at hj
    have : Mono (j ≫ i) := by rw [hj]; exact mono_comp _ _
    have := tensorRight_preservesMono (A := A) U
    have : Mono
        (kernel.ι (kernel.ι (unitMate i) ≫ cokernel.π i) ▷ U) :=
      Functor.map_mono (tensorRight U) _
    have hKU : IsZero
        (kernel (kernel.ι (unitMate i) ≫ cokernel.π i) ⊗ U) :=
      isZero_of_mono_eq_zero
        (kernel.ι (kernel.ι (unitMate i) ≫ cokernel.π i) ▷ U)
        ((isZero_kernelMate_tensor i).eq_zero_of_tgt _)
    have hK : IsZero (kernel (kernel.ι (unitMate i) ≫ cokernel.π i)) :=
      isZero_of_sub_of_tensor_isZero i j (mono_of_mono j i) hKU
    have : Mono (kernel.ι (unitMate i) ≫ cokernel.π i) :=
      Abelian.mono_of_kernel_ι_eq_zero _ (hK.eq_zero_of_src _)
    have : IsIso (kernel.ι (unitMate i) ≫ cokernel.π i) :=
      isIso_of_mono_of_epi _
    -- the resulting splitting of `𝟙 ↠ V` is an idempotent scalar
    set σ : cokernel i ⟶ 𝟙_ A :=
      inv (kernel.ι (unitMate i) ≫ cokernel.π i)
        ≫ kernel.ι (unitMate i)
    have hσq : σ ≫ cokernel.π i = 𝟙 (cokernel i) := by
      rw [Category.assoc, IsIso.inv_hom_id]
    have hidem : (cokernel.π i ≫ σ) ≫ (cokernel.π i ≫ σ)
        = cokernel.π i ≫ σ := by
      rw [Category.assoc, ← Category.assoc σ, hσq, Category.id_comp]
    rcases hu.idempotent_eq_zero_or_id hidem with h0 | h1
    · -- idempotent zero: the cokernel vanishes and `i` is epi
      have hq0 : cokernel.π i = 0 := by
        have h2 : (cokernel.π i ≫ σ) ≫ cokernel.π i = cokernel.π i := by
          rw [Category.assoc, hσq, Category.comp_id]
        rw [h0, zero_comp] at h2
        exact h2.symm
      have : Epi i := Abelian.epi_of_cokernel_π_eq_zero i hq0
      exact isIso_of_mono_of_epi i
    · -- idempotent one: `i` would vanish, contradiction
      refine absurd ?_ hne
      have h2 : i ≫ cokernel.π i ≫ σ = i := by
        rw [h1, Category.comp_id]
      rw [← h2, ← Category.assoc, cokernel.condition, zero_comp]

end Main

end RS
