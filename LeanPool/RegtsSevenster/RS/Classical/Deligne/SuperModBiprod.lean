/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModHom

/-!
# Biproducts of super modules

Super modules over a fixed super-commutative ℂ-algebra carry a zero
object and binary biproducts, and both are computed componentwise:
the zero module is trivial in each degree, and the biproduct of two
super modules is the product of the even components together with
the product of the odd components, acted on blockwise.

Nothing here needs the graded axioms in any essential way.  Each of
the ten axioms of `RS.SuperCommAlgebra.Mod` is a pointwise identity,
so it holds in a product as soon as it holds in each factor, and the
four structure morphisms are the four ℂ-linear structure maps of a
product of modules taken in each degree at once.

Since the category is preadditive, the bicone assembled from those
four morphisms is a bilimit as soon as it satisfies the total
identity `fst ≫ inl + snd ≫ inr = 𝟙`, which in each degree is the
componentwise statement `(p.1, 0) + (0, p.2) = p`.  Finite
biproducts then follow formally from the zero object and the binary
ones.
-/

@[expose] public section

namespace RS

open CategoryTheory Limits

universe u u' w w'

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u'}}

/-! ## Componentwise action blocks -/

section Componentwise

variable {A E₁ E₂ F₁ F₂ : Type*}

/-- **The componentwise action block**: a pair of bilinear action
blocks acting on the two factors of a product separately.  The four
action blocks of a biproduct of super modules are the four instances
of this construction. -/
def prodAct [AddCommGroup A] [Module ℂ A] [AddCommGroup E₁] [Module ℂ E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [AddCommGroup F₁] [Module ℂ F₁]
    [AddCommGroup F₂] [Module ℂ F₂]
    (f : A →ₗ[ℂ] E₁ →ₗ[ℂ] F₁) (g : A →ₗ[ℂ] E₂ →ₗ[ℂ] F₂) :
    A →ₗ[ℂ] (E₁ × E₂) →ₗ[ℂ] F₁ × F₂ :=
  LinearMap.mk₂ ℂ (fun a p => (f a p.1, g a p.2))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)

@[simp]
theorem prodAct_apply
    [AddCommGroup A] [Module ℂ A] [AddCommGroup E₁] [Module ℂ E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [AddCommGroup F₁] [Module ℂ F₁]
    [AddCommGroup F₂] [Module ℂ F₂]
    (f : A →ₗ[ℂ] E₁ →ₗ[ℂ] F₁)
    (g : A →ₗ[ℂ] E₂ →ₗ[ℂ] F₂) (a : A) (p : E₁ × E₂) :
    prodAct f g a p = (f a p.1, g a p.2) := rfl

/-- The total identity for a product of ℂ-modules, in the form in
which each degree of the biproduct of super modules needs it. -/
theorem inl_fst_add_inr_snd
    [AddCommGroup E₁] [Module ℂ E₁] [AddCommGroup E₂] [Module ℂ E₂]
    (p : E₁ × E₂) :
    LinearMap.inl ℂ E₁ E₂ (LinearMap.fst ℂ E₁ E₂ p)
      + LinearMap.inr ℂ E₁ E₂ (LinearMap.snd ℂ E₁ E₂ p) = p := by
  simp

end Componentwise

/-! ## The zero module -/

/-- **The zero super module**: both components trivial, all four
actions zero. -/
def zeroMod (S : SuperCommAlgebra.{u, u'}) : Mod.{u, u', w, w'} S
    where
  even := PUnit
  odd := PUnit
  actEE := 0
  actEO := 0
  actOE := 0
  actOO := 0
  one_act_e _ := rfl
  one_act_o _ := rfl
  assoc_eee _ _ _ := rfl
  assoc_eeo _ _ _ := rfl
  assoc_eoe _ _ _ := rfl
  assoc_eoo _ _ _ := rfl
  assoc_oee _ _ _ := rfl
  assoc_oeo _ _ _ := rfl
  assoc_ooe _ _ _ := rfl
  assoc_ooo _ _ _ := rfl

/-- The zero super module is a zero object. -/
theorem isZero_zeroMod (S : SuperCommAlgebra.{u, u'}) :
    IsZero (zeroMod.{u, u', w, w'} S) :=
  (IsZero.iff_id_eq_zero _).2 (Hom.ext rfl rfl)

/-- **Super modules have a zero object.** -/
instance hasZeroObject :
    HasZeroObject (Mod.{u, u', w, w'} S) :=
  (isZero_zeroMod S).hasZeroObject

/-! ## The binary biproduct -/

/-- **The biproduct of two super modules**: the product of the even
components, the product of the odd components, and the four action
blocks taken componentwise. -/
def biprod (M N : Mod.{u, u', w, w'} S) : Mod.{u, u', w, w'} S
    where
  even := M.even × N.even
  odd := M.odd × N.odd
  actEE := prodAct M.actEE N.actEE
  actEO := prodAct M.actEO N.actEO
  actOE := prodAct M.actOE N.actOE
  actOO := prodAct M.actOO N.actOO
  one_act_e m := Prod.ext (M.one_act_e m.1) (N.one_act_e m.2)
  one_act_o m := Prod.ext (M.one_act_o m.1) (N.one_act_o m.2)
  assoc_eee x y m :=
    Prod.ext (M.assoc_eee x y m.1) (N.assoc_eee x y m.2)
  assoc_eeo x y m :=
    Prod.ext (M.assoc_eeo x y m.1) (N.assoc_eeo x y m.2)
  assoc_eoe x uu m :=
    Prod.ext (M.assoc_eoe x uu m.1) (N.assoc_eoe x uu m.2)
  assoc_eoo x uu m :=
    Prod.ext (M.assoc_eoo x uu m.1) (N.assoc_eoo x uu m.2)
  assoc_oee uu x m :=
    Prod.ext (M.assoc_oee uu x m.1) (N.assoc_oee uu x m.2)
  assoc_oeo uu x m :=
    Prod.ext (M.assoc_oeo uu x m.1) (N.assoc_oeo uu x m.2)
  assoc_ooe uu v m :=
    Prod.ext (M.assoc_ooe uu v m.1) (N.assoc_ooe uu v m.2)
  assoc_ooo uu v m :=
    Prod.ext (M.assoc_ooo uu v m.1) (N.assoc_ooo uu v m.2)

/-! ## The four structure morphisms -/

/-- The injection of the first summand into the biproduct. -/
def biprodInl (M N : S.Mod) : M ⟶ M.biprod N where
  evenMap := LinearMap.inl ℂ M.even N.even
  oddMap := LinearMap.inl ℂ M.odd N.odd
  map_actEE _ _ := Prod.ext rfl (map_zero _).symm
  map_actEO _ _ := Prod.ext rfl (map_zero _).symm
  map_actOE _ _ := Prod.ext rfl (map_zero _).symm
  map_actOO _ _ := Prod.ext rfl (map_zero _).symm

/-- The injection of the second summand into the biproduct. -/
def biprodInr (M N : S.Mod) : N ⟶ M.biprod N where
  evenMap := LinearMap.inr ℂ M.even N.even
  oddMap := LinearMap.inr ℂ M.odd N.odd
  map_actEE _ _ := Prod.ext (map_zero _).symm rfl
  map_actEO _ _ := Prod.ext (map_zero _).symm rfl
  map_actOE _ _ := Prod.ext (map_zero _).symm rfl
  map_actOO _ _ := Prod.ext (map_zero _).symm rfl

/-- The projection of the biproduct onto the first summand. -/
def biprodFst (M N : S.Mod) : M.biprod N ⟶ M where
  evenMap := LinearMap.fst ℂ M.even N.even
  oddMap := LinearMap.fst ℂ M.odd N.odd
  map_actEE _ _ := rfl
  map_actEO _ _ := rfl
  map_actOE _ _ := rfl
  map_actOO _ _ := rfl

/-- The projection of the biproduct onto the second summand. -/
def biprodSnd (M N : S.Mod) : M.biprod N ⟶ N where
  evenMap := LinearMap.snd ℂ M.even N.even
  oddMap := LinearMap.snd ℂ M.odd N.odd
  map_actEE _ _ := rfl
  map_actEO _ _ := rfl
  map_actOE _ _ := rfl
  map_actOO _ _ := rfl

@[simp] theorem comp_evenMap {M N P : S.Mod} (f : M ⟶ N)
    (g : N ⟶ P) : (f ≫ g).evenMap = g.evenMap.comp f.evenMap := rfl

@[simp] theorem comp_oddMap {M N P : S.Mod} (f : M ⟶ N)
    (g : N ⟶ P) : (f ≫ g).oddMap = g.oddMap.comp f.oddMap := rfl

@[simp] theorem id_evenMap (M : S.Mod) :
    Hom.evenMap (𝟙 M) = LinearMap.id := rfl

@[simp] theorem id_oddMap (M : S.Mod) :
    Hom.oddMap (𝟙 M) = LinearMap.id := rfl

/-! ## The bicone identities -/

@[simp] theorem biprodInl_fst (M N : S.Mod) :
    biprodInl M N ≫ biprodFst M N = 𝟙 M :=
  Hom.ext (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)

@[simp] theorem biprodInl_snd (M N : S.Mod) :
    biprodInl M N ≫ biprodSnd M N = 0 :=
  Hom.ext (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)

@[simp] theorem biprodInr_fst (M N : S.Mod) :
    biprodInr M N ≫ biprodFst M N = 0 :=
  Hom.ext (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)

@[simp] theorem biprodInr_snd (M N : S.Mod) :
    biprodInr M N ≫ biprodSnd M N = 𝟙 N :=
  Hom.ext (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)

/-- **The total identity**: the two projections followed by the two
injections recover the identity of the biproduct. -/
theorem biprodTotal (M N : S.Mod) :
    biprodFst M N ≫ biprodInl M N
        + biprodSnd M N ≫ biprodInr M N = 𝟙 (M.biprod N) :=
  Hom.ext (LinearMap.ext fun p => inl_fst_add_inr_snd p)
    (LinearMap.ext fun p => inl_fst_add_inr_snd p)

/-! ## Binary and finite biproducts -/

/-- The binary bicone of two super modules, with vertex their
biproduct. -/
def biprodBicone (M N : S.Mod) : BinaryBicone M N where
  pt := M.biprod N
  fst := biprodFst M N
  snd := biprodSnd M N
  inl := biprodInl M N
  inr := biprodInr M N
  inl_fst := biprodInl_fst M N
  inl_snd := biprodInl_snd M N
  inr_fst := biprodInr_fst M N
  inr_snd := biprodInr_snd M N

/-- **The biproduct bicone is a bilimit**: it is simultaneously a
product cone and a coproduct cocone. -/
def biprodBiconeIsBilimit (M N : S.Mod) :
    (biprodBicone M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (biprodTotal M N)

/-- **Super modules have binary biproducts.** -/
instance hasBinaryBiproducts :
    HasBinaryBiproducts (Mod.{u, u', w, w'} S) where
  has_binary_biproduct M N :=
    HasBinaryBiproduct.mk
      { bicone := biprodBicone M N
        isBilimit := biprodBiconeIsBilimit M N }

/-- **Super modules have finite biproducts.** -/
instance hasFiniteBiproducts :
    HasFiniteBiproducts (Mod.{u, u', w, w'} S) :=
  have : HasFiniteProducts (Mod.{u, u', w, w'} S) :=
    hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

end SuperCommAlgebra.Mod

end RS
