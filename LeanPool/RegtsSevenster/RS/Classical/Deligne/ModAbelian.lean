/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.WhiskerAdditive
import LeanPool.RegtsSevenster.RS.Classical.Deligne.BaseChangeBiprod

/-!
# Modules over a monoid object form an abelian category

Mathlib's `CategoryTheory.Mod D A` carries no additive structure.
This file supplies it, for `A` a monoid object in a monoidally
preadditive category `D`, and upgrades it to an abelian structure
when `D` is abelian and tensoring on the left is right exact.

Everything is computed in `D` and transported along the forgetful
functor:

* hom-groups are the subgroups of `D`'s hom-groups cut out by the
  intertwining condition — closed under addition because `A ◁ −` is
  additive;
* the zero module is the zero object of `D` with the zero action,
  and the biproduct of `RS.modBiprod` exhibits binary biproducts;
* the kernel of a module map is the kernel of its underlying
  morphism, with the action restricted by the universal property of
  the kernel: no exactness hypothesis is needed, since the
  restricted action is produced by `kernel.lift`;
* the cokernel is the cokernel of the underlying morphism, with the
  action descended along `A ◁ cokernel.π`; here right exactness of
  `Z ◁ −` is what makes the descent possible, and the module laws
  are checked after cancelling the epimorphisms `𝟙_ D ◁ cokernel.π`
  and `(A ⊗ A) ◁ cokernel.π`;
* a module map is a monomorphism exactly when its underlying
  morphism is, and likewise for epimorphisms, so normality in `D`
  transports: the route to `CategoryTheory.Abelian` is the
  normality route, as for super modules in
  `RS/Classical/Deligne/SuperModAbelian.lean`.

The second half of the file is independent of module theory: in any
abelian category, a subobject of a finite direct sum of simple
objects is the direct sum of a sublist of them, and dually for
quotients.  The engine is `RS.idxSum`, the direct sum of a list of
indices into a family of objects, and the two theorems
`RS.exists_sublist_iso_of_mono`/`RS.exists_sublist_iso_of_epi` are
proved by induction on the list from the two splitting lemmas
`RS.isoBiprodOfRetraction`/`RS.isoBiprodOfSection`: at each step
the intersection with the leading summand is a subobject of a
simple object, hence zero or the whole of it, and in either case
the inclusion of the kernel is split.  The specialisations to a
`Fin n`-indexed biproduct
(`RS.exists_sublist_iso_biproduct_of_mono` and its epimorphism
companion) and to a sum of copies of two simple objects
(`RS.exists_mixSum_iso_of_mono` and its companion) follow.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits ZeroObject
open scoped MonObj

universe v u w

/-! ## The additive structure on module maps -/

section Preadd

variable {D : Type u}

/-- The zero morphism of carriers intertwines the actions. -/
theorem zero_lin [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A} :
    actLeft A M.X ≫ (0 : M.X ⟶ N.X)
      = A ◁ (0 : M.X ⟶ N.X) ≫ actLeft A N.X := by
  rw [Limits.comp_zero, MonoidalPreadditive.whiskerLeft_zero,
    Limits.zero_comp]

/-- A sum of module maps intertwines the actions. -/
theorem add_lin [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A}
    (f g : M ⟶ N) :
    actLeft A M.X ≫ (f.hom + g.hom)
      = A ◁ (f.hom + g.hom) ≫ actLeft A N.X := by
  rw [Preadditive.comp_add, actLeft_natural A M.X N.X f.hom,
    actLeft_natural A M.X N.X g.hom,
    MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp]

/-- The negative of a module map intertwines the actions. -/
theorem neg_lin [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A}
    (f : M ⟶ N) :
    actLeft A M.X ≫ (-f.hom)
      = A ◁ (-f.hom) ≫ actLeft A N.X := by
  rw [Preadditive.comp_neg, actLeft_natural A M.X N.X f.hom,
    whiskerLeft_neg, Preadditive.neg_comp]

/-- The sum of two module maps. -/
def homAdd [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A}
    (f g : M ⟶ N) : M ⟶ N :=
  Mod.Hom.mk' (f.hom + g.hom) (by exact add_lin f g)

/-- The zero module map. -/
def homZero [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A} :
    M ⟶ N :=
  Mod.Hom.mk' 0 (by exact zero_lin)

/-- The negative of a module map. -/
def homNeg [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A}
    (f : M ⟶ N) : M ⟶ N :=
  Mod.Hom.mk' (-f.hom) (by exact neg_lin f)

instance instAddHomMod [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A} :
    Add (M ⟶ N) := ⟨homAdd⟩

instance instZeroHomMod [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A} :
    Zero (M ⟶ N) := ⟨homZero⟩

instance instNegHomMod [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A} :
    Neg (M ⟶ N) := ⟨homNeg⟩

/-- The hom-groups of the category of modules. -/
instance instAddCommGroupHomMod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A} :
    AddCommGroup (M ⟶ N) where
  add_assoc _ _ _ := Mod.hom_ext _ _ (add_assoc _ _ _)
  zero_add _ := Mod.hom_ext _ _ (zero_add _)
  add_zero _ := Mod.hom_ext _ _ (add_zero _)
  neg_add_cancel _ := Mod.hom_ext _ _ (neg_add_cancel _)
  add_comm _ _ := Mod.hom_ext _ _ (add_comm _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- **Modules over a monoid object are preadditive**, with
hom-groups the intertwining subgroups of the ambient hom-groups. -/
instance instPreadditiveMod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] : Preadditive (Mod D A) where
  homGroup _ _ := instAddCommGroupHomMod
  add_comp _ _ _ _ _ _ :=
    Mod.hom_ext _ _ (Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ :=
    Mod.hom_ext _ _ (Preadditive.comp_add _ _ _ _ _ _)

@[simp] theorem mod_add_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A}
    (f g : M ⟶ N) :
    (f + g).hom = f.hom + g.hom := rfl

@[simp] theorem mod_zero_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A} :
    (0 : M ⟶ N).hom = 0 := rfl

@[simp] theorem mod_neg_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] {M : Mod D A} {N : Mod D A}
    (f : M ⟶ N) : (-f).hom = -f.hom := rfl

/-- **The forgetful functor is additive.** -/
instance instForgetAdditive
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] {A : D} [MonObj A] :
    (Mod.forget (D := D) A).Additive where
  map_add := rfl

/-- **The forgetful functor is faithful.** -/
instance instForgetFaithful
    [Category.{v} D] [MonoidalCategory D] {A : D} [MonObj A] :
    (Mod.forget (D := D) A).Faithful where
  map_injective h := Mod.hom_ext _ _ h

/-- A module map whose underlying morphism is a monomorphism is a
monomorphism. -/
theorem mono_of_mono_hom
    [Category.{v} D] [MonoidalCategory D] {A : D} [MonObj A] {M : Mod D A}
    {N : Mod D A}
    (f : M ⟶ N) (h : Mono f.hom) : Mono f :=
  ⟨fun _ _ huv => Mod.hom_ext _ _
    ((cancel_mono f.hom).1 (congrArg Mod.Hom.hom huv))⟩

/-- A module map whose underlying morphism is an epimorphism is an
epimorphism. -/
theorem epi_of_epi_hom
    [Category.{v} D] [MonoidalCategory D] {A : D} [MonObj A] {M : Mod D A}
    {N : Mod D A}
    (f : M ⟶ N) (h : Epi f.hom) : Epi f :=
  ⟨fun _ _ huv => Mod.hom_ext _ _
    ((cancel_epi f.hom).1 (congrArg Mod.Hom.hom huv))⟩

end Preadd

/-! ## The zero module -/

section Zero

variable {D : Type u}

/-- The zero object of `D` is a module, with the zero action. -/
@[implicit_reducible]
noncomputable def zeroModObj
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] [HasZeroObject D]
    (A : D) [MonObj A] : ModObj A (0 : D) where
  smul := 0
  one_smul := (isZero_zero D).eq_of_tgt _ _
  mul_smul := (isZero_zero D).eq_of_tgt _ _

/-- **The zero module.** -/
noncomputable def zeroMod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] [HasZeroObject D]
    (A : D) [MonObj A] : Mod D A :=
  letI := zeroModObj A
  ⟨0⟩

/-- The zero module is a zero object. -/
theorem isZero_zeroMod [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasZeroObject D] (A : D) [MonObj A] :
    IsZero (zeroMod A) := by
  rw [IsZero.iff_id_eq_zero]
  refine Mod.hom_ext _ _ ?_
  exact (isZero_zero D).eq_of_tgt _ _

/-- **Modules over a monoid object have a zero object.** -/
instance instHasZeroObjectMod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasZeroObject D] (A : D) [MonObj A] :
    HasZeroObject (Mod D A) :=
  ⟨⟨zeroMod A, isZero_zeroMod A⟩⟩

end Zero

/-! ## Binary biproducts -/

section Biprod

variable {D : Type u}

/-- The binary bicone carried by the biproduct of two modules. -/
noncomputable def modBinaryBicone
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) : BinaryBicone M N where
  pt := modBiprod A M N
  fst := modBiprodFst A M N
  snd := modBiprodSnd A M N
  inl := modBiprodInl A M N
  inr := modBiprodInr A M N
  inl_fst := Mod.hom_ext _ _ (by simp)
  inl_snd := Mod.hom_ext _ _ (by simp)
  inr_fst := Mod.hom_ext _ _ (by simp)
  inr_snd := Mod.hom_ext _ _ (by simp)

/-- The bicone of the module biproduct is total. -/
theorem modBinaryBicone_total
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) :
    (modBinaryBicone A M N).fst ≫ (modBinaryBicone A M N).inl
        + (modBinaryBicone A M N).snd ≫ (modBinaryBicone A M N).inr
      = 𝟙 (modBinaryBicone A M N).pt := by
  refine Mod.hom_ext _ _ ?_
  change biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr
    = 𝟙 (M.X ⊞ N.X)
  exact biprod.total

/-- **The bicone of the module biproduct is a bilimit.** -/
noncomputable def modBinaryBiconeIsBilimit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) :
    (modBinaryBicone A M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (modBinaryBicone_total A M N)

end Biprod

section BiprodInst

variable {D : Type u}

/-- **Modules over a monoid object have binary biproducts.** -/
instance instHasBinaryBiproductsMod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A] :
    HasBinaryBiproducts (Mod D A) :=
  ⟨fun M N => HasBinaryBiproduct.mk
    ⟨modBinaryBicone A M N, modBinaryBiconeIsBilimit A M N⟩⟩

end BiprodInst

/-! ## Finite biproducts -/

section FinBiprod

variable {D : Type u}

/-- The componentwise action on a finite biproduct of carriers. -/
noncomputable def modBiproductAct
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasFiniteBiproducts D] (A : D) [MonObj A] {K : Type} [Fintype K]
    (M : K → Mod D A) :
    A ⊗ (⨁ fun j => (M j).X) ⟶ ⨁ fun j => (M j).X :=
  biproduct.lift fun j =>
    A ◁ biproduct.π (fun j => (M j).X) j ≫ actLeft A (M j).X

@[reassoc (attr := simp)]
theorem modBiproductAct_π [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasFiniteBiproducts D] (A : D) [MonObj A] {K : Type} [Fintype K]
    (M : K → Mod D A)
    (j : K) :
    modBiproductAct A M ≫ biproduct.π (fun j => (M j).X) j
      = A ◁ biproduct.π (fun j => (M j).X) j ≫ actLeft A (M j).X :=
  biproduct.lift_π _ _

/-- Unitality of the componentwise action. -/
theorem modBiproductAct_one
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasFiniteBiproducts D] (A : D) [MonObj A] {K : Type} [Fintype K]
    (M : K → Mod D A) :
    η[A] ▷ (⨁ fun j => (M j).X) ≫ modBiproductAct A M
      = (λ_ (⨁ fun j => (M j).X)).hom := by
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Category.assoc, modBiproductAct_π, ← Category.assoc,
    ← whisker_exchange, Category.assoc, one_actLeft,
    leftUnitor_naturality]

/-- Associativity of the componentwise action. -/
theorem modBiproductAct_mul
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasFiniteBiproducts D] (A : D) [MonObj A] {K : Type} [Fintype K]
    (M : K → Mod D A) :
    μ[A] ▷ (⨁ fun j => (M j).X) ≫ modBiproductAct A M
      = (α_ A A (⨁ fun j => (M j).X)).hom
          ≫ A ◁ modBiproductAct A M ≫ modBiproductAct A M := by
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Category.assoc, modBiproductAct_π, ← Category.assoc,
    ← whisker_exchange, Category.assoc, mul_actLeft, Category.assoc,
    Category.assoc, modBiproductAct_π,
    ← MonoidalCategory.whiskerLeft_comp_assoc, modBiproductAct_π,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    associator_naturality_right_assoc]

/-- The module structure on a finite biproduct of carriers. -/
@[implicit_reducible]
noncomputable def modBiproductModObj
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasFiniteBiproducts D] (A : D) [MonObj A] {K : Type} [Fintype K]
    (M : K → Mod D A) :
    ModObj A (⨁ fun j => (M j).X) where
  smul := modBiproductAct A M
  one_smul := modBiproductAct_one A M
  mul_smul := modBiproductAct_mul A M

/-- **The finite biproduct of modules**, bundled. -/
noncomputable def modBiproduct
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasFiniteBiproducts D] (A : D) [MonObj A] {K : Type} [Fintype K]
    (M : K → Mod D A) : Mod D A :=
  letI := modBiproductModObj A M
  ⟨⨁ fun j => (M j).X⟩

/-- The projections of the biproduct are module maps. -/
noncomputable def modBiproductπ
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasFiniteBiproducts D] (A : D) [MonObj A] {K : Type} [Fintype K]
    (M : K → Mod D A)
    (j : K) : modBiproduct A M ⟶ M j :=
  Mod.Hom.mk' (biproduct.π (fun j => (M j).X) j)
    (by exact modBiproductAct_π A M j)

/-- The injections intertwine the actions. -/
theorem modBiproductAct_ι [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] (A : D) [MonObj A]
    {K : Type} [Fintype K] (M : K → Mod D A)
    (j : K) :
    actLeft A (M j).X ≫ biproduct.ι (fun j => (M j).X) j
      = A ◁ biproduct.ι (fun j => (M j).X) j
          ≫ modBiproductAct A M := by
  refine biproduct.hom_ext _ _ fun j' => ?_
  by_cases h : j = j'
  · subst h
    rw [Category.assoc, biproduct.ι_π_self, Category.comp_id,
      Category.assoc, modBiproductAct_π,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biproduct.ι_π_self, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  · rw [Category.assoc, biproduct.ι_π_ne _ h, Limits.comp_zero,
      Category.assoc, modBiproductAct_π,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biproduct.ι_π_ne _ h, MonoidalPreadditive.whiskerLeft_zero,
      Limits.zero_comp]

/-- The injections of the biproduct are module maps. -/
noncomputable def modBiproductInj
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] (A : D) [MonObj A]
    {K : Type} [Fintype K] (M : K → Mod D A)
    (j : K) : M j ⟶ modBiproduct A M :=
  Mod.Hom.mk' (biproduct.ι (fun j => (M j).X) j)
    (by exact modBiproductAct_ι A M j)

/-- The bicone carried by the finite biproduct of modules. -/
noncomputable def modBicone
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] (A : D) [MonObj A]
    {K : Type} [Fintype K] (M : K → Mod D A) : Bicone M :=
  Bicone.mk (modBiproduct A M) (modBiproductπ A M)
    (modBiproductInj A M)
    (fun j j' => by
      by_cases h : j = j'
      · subst h
        rw [dite_eq_left rfl]
        refine Mod.hom_ext _ _ ?_
        change biproduct.ι (fun j => (M j).X) j
          ≫ biproduct.π (fun j => (M j).X) j = _
        rw [biproduct.ι_π_self]
        exact (Mod.id_hom' (M j)).symm
      · rw [dite_eq_right h]
        refine Mod.hom_ext _ _ ?_
        change biproduct.ι (fun j => (M j).X) j
          ≫ biproduct.π (fun j => (M j).X) j' = _
        rw [biproduct.ι_π_ne _ h]
        rfl)

/-- Taking the underlying morphism of a module map is additive. -/
def modHomAddHom [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (A : D) [MonObj A]
    (P Q : Mod D A) : (P ⟶ Q) →+ (P.X ⟶ Q.X) where
  toFun f := f.hom
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The bicone of the finite biproduct of modules is total. -/
theorem modBicone_total [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] (A : D) [MonObj A]
    {K : Type} [Fintype K] (M : K → Mod D A) :
    ∑ j, Bicone.π (modBicone A M) j ≫ Bicone.ι (modBicone A M) j
      = 𝟙 (Bicone.pt (modBicone A M)) := by
  refine Mod.hom_ext _ _ ?_
  refine Eq.trans (map_sum (modHomAddHom A (modBiproduct A M)
    (modBiproduct A M)) _ Finset.univ) ?_
  exact biproduct.total

/-- **Modules over a monoid object have finite biproducts**,
computed in the ambient category. -/
instance instHasFiniteBiproductsMod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] (A : D) [MonObj A] :
    HasFiniteBiproducts (Mod D A) where
  out _ :=
    { has_biproduct := fun M => HasBiproduct.mk
        { bicone := modBicone A M
          isBilimit := isBilimitOfTotal _ (modBicone_total A M) } }

end FinBiprod

/-! ## Finite products -/

section FinProd

variable {D : Type u}

/-- **Modules over a monoid object have finite products.** -/
instance instHasFiniteProductsMod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteProducts D] (A : D) [MonObj A] :
    HasFiniteProducts (Mod D A) :=
  haveI : HasFiniteBiproducts D :=
    HasFiniteBiproducts.of_hasFiniteProducts
  haveI : HasFiniteBiproducts (Mod D A) := instHasFiniteBiproductsMod A
  inferInstance

end FinProd

/-! ## Kernels -/

section Kernels

variable {D : Type u}

/-- The action carried by the kernel lands in the kernel. -/
theorem kerAct_aux [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) :
    (A ◁ kernel.ι f.hom ≫ actLeft A M.X) ≫ f.hom = 0 := by
  rw [Category.assoc, actLeft_natural A M.X N.X f.hom,
    ← MonoidalCategory.whiskerLeft_comp_assoc, kernel.condition,
    MonoidalPreadditive.whiskerLeft_zero, Limits.zero_comp]

/-- **The action on the kernel** of the underlying morphism. -/
noncomputable def kerAct [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) : A ⊗ kernel f.hom ⟶ kernel f.hom :=
  kernel.lift f.hom (A ◁ kernel.ι f.hom ≫ actLeft A M.X)
    (kerAct_aux A f)

@[reassoc (attr := simp)]
theorem kerAct_ι [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) :
    kerAct A f ≫ kernel.ι f.hom
      = A ◁ kernel.ι f.hom ≫ actLeft A M.X :=
  kernel.lift_ι _ _ _

/-- Unitality of the action on the kernel. -/
theorem kerAct_one [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) :
    η[A] ▷ kernel f.hom ≫ kerAct A f
      = (λ_ (kernel f.hom)).hom := by
  refine (cancel_mono (kernel.ι f.hom)).1 ?_
  rw [Category.assoc, kerAct_ι, ← Category.assoc, ← whisker_exchange,
    Category.assoc, one_actLeft, leftUnitor_naturality]

/-- Associativity of the action on the kernel. -/
theorem kerAct_mul [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) :
    μ[A] ▷ kernel f.hom ≫ kerAct A f
      = (α_ A A (kernel f.hom)).hom ≫ A ◁ kerAct A f ≫ kerAct A f := by
  refine (cancel_mono (kernel.ι f.hom)).1 ?_
  rw [Category.assoc, kerAct_ι, ← Category.assoc, ← whisker_exchange,
    Category.assoc, mul_actLeft, Category.assoc, Category.assoc,
    kerAct_ι, ← MonoidalCategory.whiskerLeft_comp_assoc, kerAct_ι,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    associator_naturality_right_assoc]

/-- The module structure on the kernel of the underlying
morphism. -/
@[implicit_reducible]
noncomputable def kerModObj
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) : ModObj A (kernel f.hom) where
  smul := kerAct A f
  one_smul := kerAct_one A f
  mul_smul := kerAct_mul A f

/-- **The kernel of a module map**, bundled. -/
noncomputable def kerMod [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) : Mod D A :=
  letI := kerModObj A f
  ⟨kernel f.hom⟩

/-- The inclusion of the kernel of a module map. -/
noncomputable def kerIncl [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) : kerMod A f ⟶ M :=
  Mod.Hom.mk' (kernel.ι f.hom) (by exact kerAct_ι A f)

@[simp] theorem kerIncl_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) : (kerIncl A f).hom = kernel.ι f.hom :=
  rfl

/-- The inclusion of the kernel is annihilated by the map. -/
theorem kerIncl_comp [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) : kerIncl A f ≫ f = 0 :=
  Mod.hom_ext _ _ (kernel.condition f.hom)

/-- The inclusion of the kernel is a monomorphism. -/
theorem mono_kerIncl [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) : Mono (kerIncl A f) :=
  mono_of_mono_hom _ (by
    change Mono (kernel.ι f.hom)
    infer_instance)

/-- The lift of a module map annihilated by `f` through the
inclusion of the kernel. -/
noncomputable def kerLift [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N)
    {W : Mod D A} (k : W ⟶ M)
    (hk : k ≫ f = 0) : W ⟶ kerMod A f :=
  Mod.Hom.mk'
    (kernel.lift f.hom k.hom (by simpa using congrArg Mod.Hom.hom hk))
    (by
      change actLeft A W.X ≫ kernel.lift f.hom k.hom (by simpa using congrArg Mod.Hom.hom hk)
        = A ◁ kernel.lift f.hom k.hom (by simpa using congrArg Mod.Hom.hom hk) ≫ kerAct A f
      refine (cancel_mono (kernel.ι f.hom)).1 ?_
      rw [Category.assoc, kernel.lift_ι, Category.assoc, kerAct_ι,
        ← MonoidalCategory.whiskerLeft_comp_assoc, kernel.lift_ι,
        actLeft_natural A W.X M.X k.hom]
      all_goals simpa using congrArg Mod.Hom.hom hk)

/-- The lift through the kernel recovers the given map. -/
theorem kerLift_comp [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N)
    {W : Mod D A} (k : W ⟶ M) (hk : k ≫ f = 0) :
    kerLift A f k hk ≫ kerIncl A f = k :=
  Mod.hom_ext _ _ (kernel.lift_ι _ _ _)

/-- The kernel fork of a module map. -/
noncomputable def kernelForkMod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) : KernelFork f :=
  KernelFork.ofι (kerIncl A f) (kerIncl_comp A f)

/-- **The kernel fork of a module map is limiting.** -/
noncomputable def kernelForkModIsLimit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] {M : Mod D A}
    {N : Mod D A} (f : M ⟶ N) : IsLimit (kernelForkMod A f) :=
  haveI := mono_kerIncl A f
  KernelFork.IsLimit.ofι' (kerIncl A f) (kerIncl_comp A f)
    fun k hk => ⟨kerLift A f k hk, kerLift_comp A f k hk⟩

end Kernels

section KernelsInst

variable {D : Type u}

/-- **Modules over a monoid object have kernels**, computed in the
ambient category. -/
instance instHasKernelsMod [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasKernels D] (A : D) [MonObj A] :
    HasKernels (Mod D A) where
  has_limit g := HasLimit.mk
    { cone := kernelForkMod A g
      isLimit := kernelForkModIsLimit A g }

end KernelsInst

/-! ## Cokernels -/

section Cokernels

variable {D : Type u}

/-- Whiskering a cokernel projection leaves an epimorphism. -/
theorem epi_whiskerLeft_cokernelπ
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Z : D) {X Y : D} (g : X ⟶ Y) :
    Epi (Z ◁ cokernel.π g) :=
  epi_of_isColimit_cofork
    (isColimitOfHasCokernelOfPreservesColimit (tensorLeft Z) g)

/-- **Descent along a whiskered cokernel projection.** -/
noncomputable def whiskerCokernelDesc
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Z : D) {X Y W : D} (g : X ⟶ Y)
    (k : Z ⊗ Y ⟶ W) (hk : Z ◁ g ≫ k = 0) : Z ⊗ cokernel g ⟶ W :=
  (isColimitOfHasCokernelOfPreservesColimit (tensorLeft Z) g).desc
    (CokernelCofork.ofπ k (by exact hk))

@[reassoc (attr := simp)]
theorem whiskerCokernel_π_desc
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Z : D) {X Y W : D} (g : X ⟶ Y)
    (k : Z ⊗ Y ⟶ W) (hk : Z ◁ g ≫ k = 0) :
    Z ◁ cokernel.π g ≫ whiskerCokernelDesc Z g k hk = k := by
  exact Cofork.IsColimit.π_desc
    (isColimitOfHasCokernelOfPreservesColimit (tensorLeft Z) g)

/-- The descended action is well defined. -/
theorem cokerAct_aux
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] [HasCokernels D]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    A ◁ f.hom ≫ actLeft A N.X ≫ cokernel.π f.hom = 0 := by
  rw [← Category.assoc, ← actLeft_natural A M.X N.X f.hom,
    Category.assoc, cokernel.condition, Limits.comp_zero]

/-- **The action on the cokernel** of the underlying morphism. -/
noncomputable def cokerAct [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    A ⊗ cokernel f.hom ⟶ cokernel f.hom :=
  whiskerCokernelDesc A f.hom (actLeft A N.X ≫ cokernel.π f.hom)
    (cokerAct_aux A f)

@[reassoc (attr := simp)]
theorem π_cokerAct [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    A ◁ cokernel.π f.hom ≫ cokerAct A f
      = actLeft A N.X ≫ cokernel.π f.hom :=
  whiskerCokernel_π_desc _ _ _ _

/-- Unitality of the action on the cokernel. -/
theorem cokerAct_one [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    η[A] ▷ cokernel f.hom ≫ cokerAct A f
      = (λ_ (cokernel f.hom)).hom := by
  have := epi_whiskerLeft_cokernelπ (𝟙_ D) f.hom
  refine (cancel_epi ((𝟙_ D) ◁ cokernel.π f.hom)).1 ?_
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    π_cokerAct, ← Category.assoc, one_actLeft, leftUnitor_naturality]

/-- Associativity of the action on the cokernel. -/
theorem cokerAct_mul [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    μ[A] ▷ cokernel f.hom ≫ cokerAct A f
      = (α_ A A (cokernel f.hom)).hom
          ≫ A ◁ cokerAct A f ≫ cokerAct A f := by
  have := epi_whiskerLeft_cokernelπ (A ⊗ A) f.hom
  refine (cancel_epi ((A ⊗ A) ◁ cokernel.π f.hom)).1 ?_
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    π_cokerAct, ← Category.assoc, mul_actLeft, Category.assoc,
    Category.assoc, associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, π_cokerAct,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, π_cokerAct]

/-- The module structure on the cokernel of the underlying
morphism. -/
@[implicit_reducible]
noncomputable def cokerModObj
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    ModObj A (cokernel f.hom) where
  smul := cokerAct A f
  one_smul := cokerAct_one A f
  mul_smul := cokerAct_mul A f

/-- **The cokernel of a module map**, bundled. -/
noncomputable def cokerMod [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) : Mod D A :=
  letI := cokerModObj A f
  ⟨cokernel f.hom⟩

/-- The projection onto the cokernel of a module map. -/
noncomputable def cokerProj
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    N ⟶ cokerMod A f :=
  Mod.Hom.mk' (cokernel.π f.hom) (by exact (π_cokerAct A f).symm)

@[simp] theorem cokerProj_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    (cokerProj A f).hom = cokernel.π f.hom := rfl

/-- The projection onto the cokernel annihilates the map. -/
theorem comp_cokerProj [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    f ≫ cokerProj A f = 0 :=
  Mod.hom_ext _ _ (cokernel.condition f.hom)

/-- The projection onto the cokernel is an epimorphism. -/
theorem epi_cokerProj [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    Epi (cokerProj A f) :=
  epi_of_epi_hom _ (by
    change Epi (cokernel.π f.hom)
    infer_instance)

/-- The descent of a module map annihilating `f` through the
projection onto the cokernel. -/
noncomputable def cokerDesc
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N)
    {W : Mod D A} (k : N ⟶ W)
    (hk : f ≫ k = 0) : cokerMod A f ⟶ W :=
  Mod.Hom.mk'
    (cokernel.desc f.hom k.hom (by simpa using congrArg Mod.Hom.hom hk))
    (by
      change cokerAct A f ≫ cokernel.desc f.hom k.hom (by simpa using congrArg Mod.Hom.hom hk)
        = A ◁ cokernel.desc f.hom k.hom (by simpa using congrArg Mod.Hom.hom hk) ≫ actLeft A W.X
      have := epi_whiskerLeft_cokernelπ A f.hom
      refine (cancel_epi (A ◁ cokernel.π f.hom)).1 ?_
      rw [← Category.assoc, π_cokerAct, Category.assoc,
        cokernel.π_desc, ← MonoidalCategory.whiskerLeft_comp_assoc,
        cokernel.π_desc, actLeft_natural A N.X W.X k.hom]
      all_goals simpa using congrArg Mod.Hom.hom hk)

/-- The descent through the cokernel recovers the given map. -/
theorem cokerProj_desc [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N)
    {W : Mod D A} (k : N ⟶ W) (hk : f ≫ k = 0) :
    cokerProj A f ≫ cokerDesc A f k hk = k :=
  Mod.hom_ext _ _ (cokernel.π_desc _ _ _)

/-- The cokernel cofork of a module map. -/
noncomputable def cokernelCoforkMod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    CokernelCofork f :=
  CokernelCofork.ofπ (cokerProj A f) (comp_cokerProj A f)

/-- **The cokernel cofork of a module map is colimiting.** -/
noncomputable def cokernelCoforkModIsColimit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (f : M ⟶ N) :
    IsColimit (cokernelCoforkMod A f) :=
  haveI := epi_cokerProj A f
  CokernelCofork.IsColimit.ofπ' (cokerProj A f) (comp_cokerProj A f)
    fun k hk => ⟨cokerDesc A f k hk, cokerProj_desc A f k hk⟩

end Cokernels

section CokernelsInst

variable {D : Type u}

/-- **Modules over a monoid object have cokernels**, computed in
the ambient category. -/
instance instHasCokernelsMod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasCokernels D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] : HasCokernels (Mod D A) where
  has_colimit g := HasColimit.mk
    { cocone := cokernelCoforkMod A g
      isColimit := cokernelCoforkModIsColimit A g }

end CokernelsInst

/-! ## The monomorphism and epimorphism bridges -/

section MonoBridge

variable {D : Type u}

/-- **A module map is a monomorphism exactly when its underlying
morphism is.** -/
theorem mono_iff_hom [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] (A : D) [MonObj A] {M : Mod D A} {N : Mod D A}
    (f : M ⟶ N) : Mono f ↔ Mono f.hom := by
  refine ⟨fun hf => ?_, mono_of_mono_hom f⟩
  have h0 : kerIncl A f = 0 := by
    refine (cancel_mono f).1 ?_
    rw [kerIncl_comp, Limits.zero_comp]
  have hi : kernel.ι f.hom = 0 := congrArg Mod.Hom.hom h0
  rw [Preadditive.mono_iff_cancel_zero]
  intro R w hw
  rw [← kernel.lift_ι f.hom w hw, hi, Limits.comp_zero]

/-- **Whiskering preserves epimorphisms**: an epimorphism of an
abelian category is the cokernel of its kernel, and tensoring on
the left preserves that cokernel. -/
theorem epi_whiskerLeft [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [∀ Z : D,
    PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Z : D) {X Y : D} (e : X ⟶ Y) [Epi e] : Epi (Z ◁ e) := by
  have h := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel e)
  exact epi_of_isColimit_cofork
    (isColimitMapCoconeCoforkEquiv (tensorLeft Z) _
      (isColimitOfPreserves (tensorLeft Z) h))

end MonoBridge

section EpiBridge

variable {D : Type u}

/-- **A module map is an epimorphism exactly when its underlying
morphism is.** -/
theorem epi_iff_hom [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A}
    (f : M ⟶ N) : Epi f ↔ Epi f.hom := by
  refine ⟨fun hf => ?_, epi_of_epi_hom f⟩
  have h0 : cokerProj A f = 0 := by
    refine (cancel_epi f).1 ?_
    rw [comp_cokerProj, Limits.comp_zero]
  have hp : cokernel.π f.hom = 0 := congrArg Mod.Hom.hom h0
  rw [Preadditive.epi_iff_cancel_zero]
  intro R w hw
  rw [← cokernel.π_desc f.hom w hw, hp, Limits.zero_comp]

end EpiBridge

/-! ## Normality and abelianness -/

section Normal

variable {D : Type u}

/-- A module map annihilated by the projection onto the cokernel is
annihilated by the underlying cokernel projection. -/
theorem monoLift_aux [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    {W : Mod D A} (k : W ⟶ N)
    (hk : k ≫ cokerProj A φ = 0) : k.hom ≫ cokernel.π φ.hom = 0 :=
  congrArg Mod.Hom.hom hk

/-- The underlying factorisation through a monomorphic module
map. -/
noncomputable def monoLiftHom [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    [Mono φ.hom] {W : Mod D A} (k : W ⟶ N)
    (hk : k ≫ cokerProj A φ = 0) : W.X ⟶ M.X :=
  (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel φ.hom)).lift
    (KernelFork.ofι k.hom (monoLift_aux A φ k hk))

@[reassoc]
theorem monoLiftHom_comp [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    [Mono φ.hom] {W : Mod D A} (k : W ⟶ N)
    (hk : k ≫ cokerProj A φ = 0) :
    monoLiftHom A φ k hk ≫ φ.hom = k.hom := by
  exact Fork.IsLimit.lift_ι _

/-- The underlying factorisation intertwines the actions. -/
theorem monoLiftHom_lin [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    [Mono φ.hom] {W : Mod D A} (k : W ⟶ N)
    (hk : k ≫ cokerProj A φ = 0) :
    actLeft A W.X ≫ monoLiftHom A φ k hk
      = A ◁ monoLiftHom A φ k hk ≫ actLeft A M.X := by
  refine (cancel_mono φ.hom).1 ?_
  rw [Category.assoc, monoLiftHom_comp, Category.assoc,
    actLeft_natural A M.X N.X φ.hom,
    ← MonoidalCategory.whiskerLeft_comp_assoc, monoLiftHom_comp,
    actLeft_natural A W.X N.X k.hom]

/-- The factorisation through a monomorphism of a module map
annihilated by the projection onto its cokernel. -/
noncomputable def monoLift [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    [Mono φ.hom] {W : Mod D A} (k : W ⟶ N)
    (hk : k ≫ cokerProj A φ = 0) : W ⟶ M :=
  Mod.Hom.mk' (monoLiftHom A φ k hk)
    (by exact monoLiftHom_lin A φ k hk)

/-- The factorisation through a monomorphism recovers the given
map. -/
theorem monoLift_comp [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    [Mono φ.hom] {W : Mod D A} (k : W ⟶ N)
    (hk : k ≫ cokerProj A φ = 0) : monoLift A φ k hk ≫ φ = k :=
  Mod.hom_ext _ _ (monoLiftHom_comp A φ k hk)

/-- **A module map with monomorphic underlying morphism is the
kernel of its cokernel.** -/
@[implicit_reducible]
noncomputable def normalMonoOfMonoHom
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    [Mono φ.hom] : NormalMono φ where
  Z := cokerMod A φ
  g := cokerProj A φ
  w := comp_cokerProj A φ
  isLimit :=
    haveI : Mono φ := mono_of_mono_hom φ inferInstance
    KernelFork.IsLimit.ofι' φ (comp_cokerProj A φ)
      fun k hk => ⟨monoLift A φ k hk, monoLift_comp A φ k hk⟩

/-- A module map annihilating the inclusion of the kernel is
annihilated by the underlying kernel inclusion. -/
theorem epiDesc_aux [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] (A : D) [MonObj A] {M : Mod D A} {N : Mod D A}
    (φ : M ⟶ N)
    {W : Mod D A} (k : M ⟶ W)
    (hk : kerIncl A φ ≫ k = 0) : kernel.ι φ.hom ≫ k.hom = 0 :=
  congrArg Mod.Hom.hom hk

/-- The underlying factorisation through an epimorphic module
map. -/
noncomputable def epiDescHom [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] (A : D) [MonObj A] {M : Mod D A} {N : Mod D A}
    (φ : M ⟶ N)
    [Epi φ.hom] {W : Mod D A} (k : M ⟶ W)
    (hk : kerIncl A φ ≫ k = 0) : N.X ⟶ W.X :=
  (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel φ.hom)).desc
    (CokernelCofork.ofπ k.hom (epiDesc_aux A φ k hk))

/-- The underlying factorisation recovers the given map. -/
@[reassoc]
theorem comp_epiDescHom [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] (A : D) [MonObj A] {M : Mod D A} {N : Mod D A}
    (φ : M ⟶ N)
    [Epi φ.hom] {W : Mod D A} (k : M ⟶ W)
    (hk : kerIncl A φ ≫ k = 0) :
    φ.hom ≫ epiDescHom A φ k hk = k.hom := by
  exact Cofork.IsColimit.π_desc
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel φ.hom))

/-- The underlying factorisation intertwines the actions. -/
theorem epiDescHom_lin [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    [Epi φ.hom] {W : Mod D A} (k : M ⟶ W)
    (hk : kerIncl A φ ≫ k = 0) :
    actLeft A N.X ≫ epiDescHom A φ k hk
      = A ◁ epiDescHom A φ k hk ≫ actLeft A W.X := by
  have := epi_whiskerLeft A (e := φ.hom)
  refine (cancel_epi (A ◁ φ.hom)).1 ?_
  rw [← Category.assoc, ← actLeft_natural A M.X N.X φ.hom,
    Category.assoc, comp_epiDescHom,
    ← MonoidalCategory.whiskerLeft_comp_assoc, comp_epiDescHom,
    actLeft_natural A M.X W.X k.hom]

/-- The factorisation through an epimorphism of a module map
annihilating the inclusion of its kernel. -/
noncomputable def epiDesc [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    [Epi φ.hom] {W : Mod D A} (k : M ⟶ W)
    (hk : kerIncl A φ ≫ k = 0) : N ⟶ W :=
  Mod.Hom.mk' (epiDescHom A φ k hk)
    (by exact epiDescHom_lin A φ k hk)

/-- The factorisation through an epimorphism recovers the given
map. -/
theorem comp_epiDesc [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    [Epi φ.hom] {W : Mod D A} (k : M ⟶ W)
    (hk : kerIncl A φ ≫ k = 0) : φ ≫ epiDesc A φ k hk = k :=
  Mod.hom_ext _ _ (comp_epiDescHom A φ k hk)

/-- **A module map with epimorphic underlying morphism is the
cokernel of its kernel.** -/
@[implicit_reducible]
noncomputable def normalEpiOfEpiHom
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {N : Mod D A} (φ : M ⟶ N)
    [Epi φ.hom] : NormalEpi φ where
  W := kerMod A φ
  g := kerIncl A φ
  w := kerIncl_comp A φ
  isColimit :=
    haveI : Epi φ := epi_of_epi_hom φ inferInstance
    CokernelCofork.IsColimit.ofπ' φ (kerIncl_comp A φ)
      fun k hk => ⟨epiDesc A φ k hk, comp_epiDesc A φ k hk⟩

end Normal

section AbelianMod

variable {D : Type u}

/-- **Every monomorphism of modules is a kernel.** -/
instance instIsNormalMonoCategoryMod
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] :
    IsNormalMonoCategory (Mod D A) where
  normalMonoOfMono φ hφ :=
    haveI : Mono φ.hom := (mono_iff_hom A φ).1 hφ
    ⟨normalMonoOfMonoHom A φ⟩

/-- **Every epimorphism of modules is a cokernel.** -/
instance instIsNormalEpiCategoryMod
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] :
    IsNormalEpiCategory (Mod D A) where
  normalEpiOfEpi φ hφ :=
    haveI : Epi φ.hom := (epi_iff_hom A φ).1 hφ
    ⟨normalEpiOfEpiHom A φ⟩

/-- **Modules over a monoid object in an abelian monoidally
preadditive category with right-exact tensor form an abelian
category.** -/
noncomputable instance instAbelianMod
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] : Abelian (Mod D A) where
  normalMonoOfMono φ hφ :=
    haveI : Mono φ.hom := (mono_iff_hom A φ).1 hφ
    ⟨normalMonoOfMonoHom A φ⟩
  normalEpiOfEpi φ hφ :=
    haveI : Epi φ.hom := (epi_iff_hom A φ).1 hφ
    ⟨normalEpiOfEpiHom A φ⟩

/-- **The forgetful functor preserves monomorphisms.** -/
instance instForgetPreservesMono
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] (A : D) [MonObj A] :
    (Mod.forget (D := D) A).PreservesMonomorphisms where
  preserves φ hφ := (mono_iff_hom A φ).1 hφ

/-- **The forgetful functor reflects monomorphisms.** -/
instance instForgetReflectsMono
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] (A : D) [MonObj A] :
    (Mod.forget (D := D) A).ReflectsMonomorphisms where
  reflects φ hφ := (mono_iff_hom A φ).2 hφ

/-- **The forgetful functor preserves epimorphisms.** -/
instance instForgetPreservesEpi
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] :
    (Mod.forget (D := D) A).PreservesEpimorphisms where
  preserves φ hφ := (epi_iff_hom A φ).1 hφ

/-- **The forgetful functor reflects epimorphisms.** -/
instance instForgetReflectsEpi [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] :
    (Mod.forget (D := D) A).ReflectsEpimorphisms where
  reflects φ hφ := (epi_iff_hom A φ).2 hφ

end AbelianMod

/-! ## Splitting off a retraction or a section -/

section Split

variable {E : Type u}

/-- The section of the cokernel projection determined by a
retraction. -/
noncomputable def retractionSection
    [Category.{v} E] [Abelian E] {K : E} {N : E} (k : K ⟶ N) (r : N ⟶ K)
    (hr : k ≫ r = 𝟙 K) : cokernel k ⟶ N :=
  cokernel.desc k (𝟙 N - r ≫ k) (by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hr,
      Category.id_comp, sub_self])

@[reassoc]
theorem π_retractionSection
    [Category.{v} E] [Abelian E] {K : E} {N : E} (k : K ⟶ N) (r : N ⟶ K)
    (hr : k ≫ r = 𝟙 K) :
    cokernel.π k ≫ retractionSection k r hr = 𝟙 N - r ≫ k :=
  cokernel.π_desc _ _ _

/-- The section is a section of the cokernel projection. -/
theorem retractionSection_π
    [Category.{v} E] [Abelian E] {K : E} {N : E} (k : K ⟶ N) (r : N ⟶ K)
    (hr : k ≫ r = 𝟙 K) :
    retractionSection k r hr ≫ cokernel.π k = 𝟙 (cokernel k) := by
  refine (cancel_epi (cokernel.π k)).1 ?_
  rw [← Category.assoc, π_retractionSection, Preadditive.sub_comp,
    Category.id_comp, Category.assoc, cokernel.condition,
    Limits.comp_zero, sub_zero, Category.comp_id]

/-- The section is annihilated by the retraction. -/
theorem retractionSection_comp
    [Category.{v} E] [Abelian E] {K : E} {N : E} (k : K ⟶ N) (r : N ⟶ K)
    (hr : k ≫ r = 𝟙 K) :
    retractionSection k r hr ≫ r = 0 := by
  refine (cancel_epi (cokernel.π k)).1 ?_
  rw [← Category.assoc, π_retractionSection, Preadditive.sub_comp,
    Category.id_comp, Category.assoc, hr, Category.comp_id, sub_self,
    Limits.comp_zero]

/-- The bicone exhibiting the ambient object as the biproduct of a
split monomorphism and its cokernel. -/
noncomputable def retractionBicone
    [Category.{v} E] [Abelian E] {K : E} {N : E} (k : K ⟶ N) (r : N ⟶ K)
    (hr : k ≫ r = 𝟙 K) : BinaryBicone K (cokernel k) where
  pt := N
  fst := r
  snd := cokernel.π k
  inl := k
  inr := retractionSection k r hr
  inl_fst := hr
  inl_snd := cokernel.condition k
  inr_fst := retractionSection_comp k r hr
  inr_snd := retractionSection_π k r hr

/-- The bicone determined by a retraction is total. -/
theorem retractionBicone_total
    [Category.{v} E] [Abelian E] {K : E} {N : E} (k : K ⟶ N) (r : N ⟶ K)
    (hr : k ≫ r = 𝟙 K) :
    (retractionBicone k r hr).fst ≫ (retractionBicone k r hr).inl
        + (retractionBicone k r hr).snd
            ≫ (retractionBicone k r hr).inr
      = 𝟙 (retractionBicone k r hr).pt := by
  change r ≫ k + cokernel.π k ≫ retractionSection k r hr = 𝟙 N
  rw [π_retractionSection]
  abel

/-- **A retraction splits off the cokernel**: if `k : K ⟶ N` has a
retraction then `N` is the biproduct of `K` and the cokernel of
`k`. -/
noncomputable def isoBiprodOfRetraction
    [Category.{v} E] [Abelian E] {K : E} {N : E} (k : K ⟶ N) (r : N ⟶ K)
    (hr : k ≫ r = 𝟙 K) : N ≅ K ⊞ cokernel k :=
  biprod.uniqueUpToIso K (cokernel k)
    (isBinaryBilimitOfTotal (retractionBicone k r hr)
      (retractionBicone_total k r hr))

end Split

section CoSplit

variable {E : Type u}

/-- The retraction of the kernel inclusion determined by a
section. -/
noncomputable def sectionRetraction
    [Category.{v} E] [Abelian E] {C : E} {N : E} (c : N ⟶ C) (s : C ⟶ N)
    (hs : s ≫ c = 𝟙 C) : N ⟶ kernel c :=
  kernel.lift c (𝟙 N - c ≫ s) (by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hs,
      Category.comp_id, sub_self])

@[reassoc]
theorem sectionRetraction_ι
    [Category.{v} E] [Abelian E] {C : E} {N : E} (c : N ⟶ C) (s : C ⟶ N)
    (hs : s ≫ c = 𝟙 C) :
    sectionRetraction c s hs ≫ kernel.ι c = 𝟙 N - c ≫ s :=
  kernel.lift_ι _ _ _

/-- The retraction is a retraction of the kernel inclusion. -/
theorem ι_sectionRetraction
    [Category.{v} E] [Abelian E] {C : E} {N : E} (c : N ⟶ C) (s : C ⟶ N)
    (hs : s ≫ c = 𝟙 C) :
    kernel.ι c ≫ sectionRetraction c s hs = 𝟙 (kernel c) := by
  refine (cancel_mono (kernel.ι c)).1 ?_
  rw [Category.assoc, sectionRetraction_ι, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc, kernel.condition,
    Limits.zero_comp, sub_zero, Category.id_comp]

/-- The section is annihilated by the retraction. -/
theorem comp_sectionRetraction
    [Category.{v} E] [Abelian E] {C : E} {N : E} (c : N ⟶ C) (s : C ⟶ N)
    (hs : s ≫ c = 𝟙 C) :
    s ≫ sectionRetraction c s hs = 0 := by
  refine (cancel_mono (kernel.ι c)).1 ?_
  rw [Category.assoc, sectionRetraction_ι, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc, hs, Category.id_comp,
    sub_self, Limits.zero_comp]

/-- The bicone exhibiting the ambient object as the biproduct of the
kernel of a split epimorphism and its target. -/
noncomputable def sectionBicone
    [Category.{v} E] [Abelian E] {C : E} {N : E} (c : N ⟶ C) (s : C ⟶ N)
    (hs : s ≫ c = 𝟙 C) : BinaryBicone (kernel c) C where
  pt := N
  fst := sectionRetraction c s hs
  snd := c
  inl := kernel.ι c
  inr := s
  inl_fst := ι_sectionRetraction c s hs
  inl_snd := kernel.condition c
  inr_fst := comp_sectionRetraction c s hs
  inr_snd := hs

/-- The bicone determined by a section is total. -/
theorem sectionBicone_total
    [Category.{v} E] [Abelian E] {C : E} {N : E} (c : N ⟶ C) (s : C ⟶ N)
    (hs : s ≫ c = 𝟙 C) :
    (sectionBicone c s hs).fst ≫ (sectionBicone c s hs).inl
        + (sectionBicone c s hs).snd ≫ (sectionBicone c s hs).inr
      = 𝟙 (sectionBicone c s hs).pt := by
  change sectionRetraction c s hs ≫ kernel.ι c + c ≫ s = 𝟙 N
  rw [sectionRetraction_ι]
  abel

/-- **A section splits off the kernel**: if `c : N ⟶ C` has a
section then `N` is the biproduct of the kernel of `c` and `C`. -/
noncomputable def isoBiprodOfSection
    [Category.{v} E] [Abelian E] {C : E} {N : E} (c : N ⟶ C) (s : C ⟶ N)
    (hs : s ≫ c = 𝟙 C) : N ≅ kernel c ⊞ C :=
  biprod.uniqueUpToIso (kernel c) C
    (isBinaryBilimitOfTotal (sectionBicone c s hs)
      (sectionBicone_total c s hs))

end CoSplit

/-! ## Subobjects and quotients of a finite sum of simples -/

section SimpleSum

variable {E : Type u}

/-- **The inductive step for subobjects**: a subobject of `X ⊞ T`
with `X` simple is either a subobject of `T`, or the sum of `X`
with one. -/
theorem exists_subobject_of_mono_biprod [Category.{v} E] [Abelian E]
    {X T N : E} [Simple X]
    (f : N ⟶ (X ⊞ T)) [Mono f] :
    ∃ (C : E) (m : C ⟶ T), Mono m ∧
      (Nonempty (N ≅ C) ∨ Nonempty (N ≅ (X ⊞ C))) := by
  have hfac : kernel.ι (f ≫ biprod.snd) ≫ f
      = (kernel.ι (f ≫ biprod.snd) ≫ f ≫ biprod.fst)
          ≫ biprod.inl := by
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [Category.assoc]
  have : Mono (kernel.ι (f ≫ biprod.snd) ≫ f) := mono_comp _ _
  have : Mono (kernel.ι (f ≫ biprod.snd) ≫ f ≫ biprod.fst) :=
    mono_of_mono_fac hfac.symm
  refine ⟨Abelian.coimage (f ≫ biprod.snd),
    Abelian.factorThruCoimage (f ≫ biprod.snd), inferInstance, ?_⟩
  by_cases hu : kernel.ι (f ≫ biprod.snd) ≫ f ≫ biprod.fst = 0
  · have hk0 : kernel.ι (f ≫ biprod.snd) = 0 := by
      refine zero_of_comp_mono f ?_
      rw [hfac, hu, Limits.zero_comp]
    have hKz : IsZero (kernel (f ≫ biprod.snd)) := by
      rw [IsZero.iff_id_eq_zero]
      refine (cancel_mono (kernel.ι (f ≫ biprod.snd))).1 ?_
      rw [Category.id_comp, hk0, Limits.zero_comp]
    have hr : kernel.ι (f ≫ biprod.snd)
        ≫ (0 : N ⟶ kernel (f ≫ biprod.snd))
        = 𝟙 (kernel (f ≫ biprod.snd)) := hKz.eq_of_tgt _ _
    exact Or.inl ⟨isoBiprodOfRetraction _ 0 hr
      ≪≫ (isoZeroBiprod hKz).symm⟩
  · have : IsIso (kernel.ι (f ≫ biprod.snd) ≫ f ≫ biprod.fst) :=
      isIso_of_mono_of_nonzero hu
    have hr : kernel.ι (f ≫ biprod.snd)
        ≫ ((f ≫ biprod.fst)
          ≫ inv (kernel.ι (f ≫ biprod.snd) ≫ f ≫ biprod.fst))
        = 𝟙 (kernel (f ≫ biprod.snd)) := by
      rw [← Category.assoc]
      exact IsIso.hom_inv_id _
    exact Or.inr ⟨isoBiprodOfRetraction _ _ hr
      ≪≫ biprod.mapIso
        (asIso (kernel.ι (f ≫ biprod.snd) ≫ f ≫ biprod.fst))
        (Iso.refl _)⟩

/-- **The inductive step for quotients**: a quotient of `X ⊞ T`
with `X` simple is either a quotient of `T`, or the sum of `X`
with one. -/
theorem exists_quotient_of_epi_biprod [Category.{v} E] [Abelian E]
    {X T N : E} [Simple X]
    (f : (X ⊞ T) ⟶ N) [Epi f] :
    ∃ (C : E) (m : T ⟶ C), Epi m ∧
      (Nonempty (N ≅ C) ∨ Nonempty (N ≅ (X ⊞ C))) := by
  have hg : biprod.inr ≫ f ≫ cokernel.π (biprod.inr ≫ f) = 0 := by
    rw [← Category.assoc]
    exact cokernel.condition _
  have hfac : f ≫ cokernel.π (biprod.inr ≫ f)
      = biprod.fst
          ≫ (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f)) := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [hg]
  have : Epi (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f)) := by
    have h1 : Epi (f ≫ cokernel.π (biprod.inr ≫ f)) := epi_comp _ _
    rw [hfac] at h1
    exact epi_of_epi (biprod.fst : (X ⊞ T) ⟶ X)
      (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f))
  refine ⟨Abelian.image (biprod.inr ≫ f),
    Abelian.factorThruImage (biprod.inr ≫ f), inferInstance, ?_⟩
  by_cases hu : biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f) = 0
  · have hc0 : cokernel.π (biprod.inr ≫ f) = 0 := by
      refine zero_of_epi_comp f ?_
      rw [hfac, hu, Limits.comp_zero]
    have hCz : IsZero (cokernel (biprod.inr ≫ f)) := by
      rw [IsZero.iff_id_eq_zero]
      refine (cancel_epi (cokernel.π (biprod.inr ≫ f))).1 ?_
      rw [Category.comp_id, hc0, Limits.comp_zero]
    have hs : (0 : cokernel (biprod.inr ≫ f) ⟶ N)
        ≫ cokernel.π (biprod.inr ≫ f)
        = 𝟙 (cokernel (biprod.inr ≫ f)) := hCz.eq_of_src _ _
    exact Or.inl ⟨isoBiprodOfSection _ 0 hs
      ≪≫ (isoBiprodZero hCz).symm⟩
  · have : IsIso (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f)) :=
      isIso_of_epi_of_nonzero hu
    have hs : (inv (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f))
          ≫ (biprod.inl ≫ f))
        ≫ cokernel.π (biprod.inr ≫ f)
        = 𝟙 (cokernel (biprod.inr ≫ f)) := by
      rw [Category.assoc, Category.assoc]
      exact IsIso.inv_hom_id _
    exact Or.inr ⟨isoBiprodOfSection _ _ hs
      ≪≫ biprod.mapIso (Iso.refl _)
          (asIso (biprod.inl ≫ f
            ≫ cokernel.π (biprod.inr ≫ f))).symm
      ≪≫ biprod.braiding _ _⟩

/-- **The direct sum of a list of indices**, formed by iterated
binary biproducts from a family of objects. -/
noncomputable def idxSum [Category.{v} E] [Abelian E]
    {J : Type w} (S : J → E) : List J → E
  | [] => 0
  | i :: L => S i ⊞ idxSum S L

@[simp] theorem idxSum_nil [Category.{v} E] [Abelian E]
    {J : Type w} (S : J → E) :
    idxSum S [] = 0 := rfl

@[simp] theorem idxSum_cons [Category.{v} E] [Abelian E]
    {J : Type w} (S : J → E) (i : J)
    (L : List J) : idxSum S (i :: L) = (S i ⊞ idxSum S L) := rfl

/-- **A subobject of a finite direct sum of simple objects is the
direct sum of a sublist of them.** -/
theorem exists_sublist_iso_of_mono [Category.{v} E] [Abelian E]
    {J : Type w} (S : J → E) :
    ∀ (L : List J), (∀ j ∈ L, Simple (S j)) →
      ∀ {N : E} (f : N ⟶ idxSum S L), Mono f →
        ∃ L' : List J, L'.Sublist L ∧ Nonempty (N ≅ idxSum S L') := by
  intro L
  induction L with
  | nil =>
      intro _ N f hf
      have := hf
      refine ⟨[], List.Sublist.refl _, ⟨?_⟩⟩
      have h0 : IsZero N := by
        rw [IsZero.iff_id_eq_zero]
        refine (cancel_mono f).1 ?_
        exact (isZero_zero E).eq_of_tgt _ _
      exact h0.iso (isZero_zero E)
  | cons i L₀ ih =>
      intro hS N f hf
      have : Simple (S i) := hS i (List.mem_cons_self ..)
      have : Mono (show N ⟶ (S i ⊞ idxSum S L₀) from f) := hf
      obtain ⟨C, m, hm, hcase⟩ :=
        exists_subobject_of_mono_biprod (X := S i)
          (T := idxSum S L₀) (N := N) f
      obtain ⟨L', hL', ⟨e⟩⟩ :=
        ih (fun j hj => hS j (List.mem_cons_of_mem i hj)) m hm
      rcases hcase with h | h
      · obtain ⟨eN⟩ := h
        exact ⟨L', hL'.cons i, ⟨eN ≪≫ e⟩⟩
      · obtain ⟨eN⟩ := h
        exact ⟨i :: L', hL'.cons_cons i,
          ⟨eN ≪≫ biprod.mapIso (Iso.refl (S i)) e⟩⟩

/-- **A quotient of a finite direct sum of simple objects is the
direct sum of a sublist of them.** -/
theorem exists_sublist_iso_of_epi [Category.{v} E] [Abelian E]
    {J : Type w} (S : J → E) :
    ∀ (L : List J), (∀ j ∈ L, Simple (S j)) →
      ∀ {N : E} (f : idxSum S L ⟶ N), Epi f →
        ∃ L' : List J, L'.Sublist L ∧ Nonempty (N ≅ idxSum S L') := by
  intro L
  induction L with
  | nil =>
      intro _ N f hf
      have := hf
      refine ⟨[], List.Sublist.refl _, ⟨?_⟩⟩
      have h0 : IsZero N := by
        rw [IsZero.iff_id_eq_zero]
        refine (cancel_epi f).1 ?_
        exact (isZero_zero E).eq_of_src _ _
      exact h0.iso (isZero_zero E)
  | cons i L₀ ih =>
      intro hS N f hf
      have : Simple (S i) := hS i (List.mem_cons_self ..)
      have : Epi (show (S i ⊞ idxSum S L₀) ⟶ N from f) := hf
      obtain ⟨C, m, hm, hcase⟩ :=
        exists_quotient_of_epi_biprod (X := S i)
          (T := idxSum S L₀) (N := N) f
      obtain ⟨L', hL', ⟨e⟩⟩ :=
        ih (fun j hj => hS j (List.mem_cons_of_mem i hj)) m hm
      rcases hcase with h | h
      · obtain ⟨eN⟩ := h
        exact ⟨L', hL'.cons i, ⟨eN ≪≫ e⟩⟩
      · obtain ⟨eN⟩ := h
        exact ⟨i :: L', hL'.cons_cons i,
          ⟨eN ≪≫ biprod.mapIso (Iso.refl (S i)) e⟩⟩

/-! ## Sums of copies of two simple objects -/

/-- The direct sum of `p` copies of `X` and `q` copies of `Y`. -/
noncomputable def mixSum [Category.{v} E] [Abelian E]
    (X Y : E) (p q : ℕ) : E :=
  idxSum (id : E → E) (List.replicate p X ++ List.replicate q Y)

/-- Every entry of a mixed replicate list is one of the two given
objects. -/
theorem simple_of_mem_mix [Category.{v} E] [Abelian E]
    (X Y : E) [Simple X] [Simple Y] (p q : ℕ) :
    ∀ Z ∈ List.replicate p X ++ List.replicate q Y, Simple (id Z) := by
  intro Z hZ
  rcases List.mem_append.1 hZ with h | h
  · rw [List.eq_of_mem_replicate h]
    exact inferInstanceAs (Simple X)
  · rw [List.eq_of_mem_replicate h]
    exact inferInstanceAs (Simple Y)

/-- **A subobject of a sum of `p` copies of a simple object and `q`
copies of another is a sum of `p' ≤ p` copies of the first and
`q' ≤ q` copies of the second.** -/
theorem exists_mixSum_iso_of_mono [Category.{v} E] [Abelian E]
    (X Y : E) [Simple X] [Simple Y]
    (p q : ℕ) {N : E} (f : N ⟶ mixSum X Y p q) (hf : Mono f) :
    ∃ p' q' : ℕ, p' ≤ p ∧ q' ≤ q ∧
      Nonempty (N ≅ mixSum X Y p' q') := by
  obtain ⟨L, hL, e⟩ := exists_sublist_iso_of_mono (id : E → E)
    (List.replicate p X ++ List.replicate q Y)
    (simple_of_mem_mix X Y p q) f hf
  obtain ⟨L₁, L₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.1 hL
  obtain ⟨p', hp', rfl⟩ := List.sublist_replicate_iff.1 h₁
  obtain ⟨q', hq', rfl⟩ := List.sublist_replicate_iff.1 h₂
  exact ⟨p', q', hp', hq', e⟩

/-- **A quotient of a sum of `p` copies of a simple object and `q`
copies of another is a sum of `p' ≤ p` copies of the first and
`q' ≤ q` copies of the second.** -/
theorem exists_mixSum_iso_of_epi [Category.{v} E] [Abelian E]
    (X Y : E) [Simple X] [Simple Y]
    (p q : ℕ) {N : E} (f : mixSum X Y p q ⟶ N) (hf : Epi f) :
    ∃ p' q' : ℕ, p' ≤ p ∧ q' ≤ q ∧
      Nonempty (N ≅ mixSum X Y p' q') := by
  obtain ⟨L, hL, e⟩ := exists_sublist_iso_of_epi (id : E → E)
    (List.replicate p X ++ List.replicate q Y)
    (simple_of_mem_mix X Y p q) f hf
  obtain ⟨L₁, L₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.1 hL
  obtain ⟨p', hp', rfl⟩ := List.sublist_replicate_iff.1 h₁
  obtain ⟨q', hq', rfl⟩ := List.sublist_replicate_iff.1 h₂
  exact ⟨p', q', hp', hq', e⟩

end SimpleSum

/-! ## Biproducts indexed by `Fin n` -/

section FinIndexed

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {E : Type u}

/-- The bicone splitting off the zeroth summand of a biproduct
indexed by `Fin (n + 1)`. -/
noncomputable def finSuccBicone [Category.{v} E] [Abelian E]
    {n : ℕ} (S : Fin (n + 1) → E) :
    BinaryBicone (S 0) (⨁ fun i : Fin n => S i.succ) where
  pt := ⨁ S
  fst := biproduct.π S 0
  snd := biproduct.lift fun i : Fin n => biproduct.π S i.succ
  inl := biproduct.ι S 0
  inr := biproduct.desc fun i : Fin n => biproduct.ι S i.succ
  inl_fst := biproduct.ι_π_self S 0
  inl_snd := by
    refine biproduct.hom_ext _ _ fun j => ?_
    rw [Category.assoc, biproduct.lift_π, Limits.zero_comp,
      biproduct.ι_π_ne S (Fin.succ_ne_zero j).symm]
  inr_fst := by
    refine biproduct.hom_ext' _ _ fun i => ?_
    rw [← Category.assoc, biproduct.ι_desc, Limits.comp_zero,
      biproduct.ι_π_ne S (Fin.succ_ne_zero i)]
  inr_snd := by
    refine biproduct.hom_ext' _ _ fun i => ?_
    refine biproduct.hom_ext _ _ fun j => ?_
    rw [Category.assoc, Category.assoc, biproduct.lift_π,
      ← Category.assoc, biproduct.ι_desc, Category.comp_id]
    by_cases h : i = j
    · subst h
      rw [biproduct.ι_π_self, biproduct.ι_π_self]
    · rw [biproduct.ι_π_ne _ h, biproduct.ι_π_ne S
        (fun hc => h (Fin.succ_injective n hc))]

/-- **A biproduct indexed by `Fin (n + 1)` splits off its zeroth
summand.** -/
noncomputable def biproductFinSuccIso [Category.{v} E] [Abelian E]
    {n : ℕ} (S : Fin (n + 1) → E) :
    (⨁ S) ≅ (S 0 ⊞ ⨁ fun i : Fin n => S i.succ) :=
  biprod.uniqueUpToIso _ _
    (isBinaryBilimitOfTotal (finSuccBicone S) (by
      change biproduct.π S 0 ≫ biproduct.ι S 0
          + biproduct.lift (fun i : Fin n => biproduct.π S i.succ)
              ≫ (biproduct.desc fun i : Fin n =>
                  biproduct.ι S i.succ)
        = 𝟙 (⨁ S)
      rw [biproduct.lift_desc]
      exact (Fin.sum_univ_succ
          (fun j => biproduct.π S j ≫ biproduct.ι S j)).symm.trans
        biproduct.total))

/-- Reindexing a list sum along a map of indices. -/
theorem idxSum_map [Category.{v} E] [Abelian E]
    {J K : Type w} (S : K → E) (g : J → K)
    (L : List J) : idxSum S (L.map g) = idxSum (S ∘ g) L := by
  induction L with
  | nil => rfl
  | cons i L ih => rw [List.map_cons, idxSum_cons, ih]; rfl

/-- **A biproduct indexed by `Fin n` is the sum over the list of
its indices.** -/
theorem nonempty_biproduct_iso_idxSum
    [Category.{v} E] [Abelian E] : ∀ (n : ℕ) (S : Fin n → E),
    Nonempty ((⨁ S) ≅ idxSum S (List.finRange n))
  | 0, S => by
      rw [List.finRange_zero]
      have h : IsZero (⨁ S) := by
        rw [IsZero.iff_id_eq_zero, ← biproduct.total]
        simp
      exact ⟨h.iso (isZero_zero E)⟩
  | n + 1, S => by
      obtain ⟨e⟩ :=
        nonempty_biproduct_iso_idxSum n fun i : Fin n => S i.succ
      rw [List.finRange_succ, idxSum_cons, idxSum_map]
      exact ⟨biproductFinSuccIso S ≪≫ biprod.mapIso (Iso.refl _) e⟩

/-- **A subobject of a finite biproduct of simple objects is the
sum over a sublist of the indices.** -/
theorem exists_sublist_iso_biproduct_of_mono [Category.{v} E] [Abelian E]
    {n : ℕ} (S : Fin n → E)
    (hS : ∀ i, Simple (S i)) {N : E} (f : N ⟶ ⨁ S) (hf : Mono f) :
    ∃ L : List (Fin n), L.Sublist (List.finRange n) ∧
      Nonempty (N ≅ idxSum S L) := by
  obtain ⟨e⟩ := nonempty_biproduct_iso_idxSum n S
  have := hf
  exact exists_sublist_iso_of_mono S (List.finRange n)
    (fun j _ => hS j) (f ≫ e.hom) inferInstance

end FinIndexed

end RS
