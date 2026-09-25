/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreAdditive
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModAdjoint

/-!
# The fibre functor is faithful

A free module on an object that becomes a mixed sum is generated,
as a module, by finitely many morphisms out of the unit and out of
the odd line.  So a morphism killed by the fibre functor is killed
after base change; and if the unit of the algebra is a monomorphism
that is enough to kill the morphism itself.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

section

variable {D : Type u}

/-- The retract family of a free module on a mixed object,
transported along an isomorphism. -/
private noncomputable def mixSec
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R]
    {V : D} {p q : ℕ}
    (e : freeMod R V ≅ freeMod R (L.mix p q))
    (i : Fin p ⊕ Fin q) :
    freeMod R (Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) i) ⟶
      freeMod R V :=
  freeModMap R (biproduct.ι (fun k : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) k) i) ≫ e.inv

private noncomputable def mixRet
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R]
    {V : D} {p q : ℕ}
    (e : freeMod R V ≅ freeMod R (L.mix p q))
    (i : Fin p ⊕ Fin q) :
    freeMod R V ⟶
      freeMod R (Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) i) :=
  e.hom ≫ freeModMap R (biproduct.π (fun k : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) k) i)

private theorem mixTotal
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (R : D) [MonObj R]
    {V : D} {p q : ℕ}
    (e : freeMod R V ≅ freeMod R (L.mix p q)) :
    ∑ i : Fin p ⊕ Fin q,
        (mixRet L R e i).hom ≫ (mixSec L R e i).hom =
      𝟙 (freeMod R V).X := by
  classical
  have h : ∀ i : Fin p ⊕ Fin q,
      (mixRet L R e i).hom ≫ (mixSec L R e i).hom =
        e.hom.hom ≫
          ((freeModMap R (biproduct.π (fun k : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) k) i)).hom ≫
            (freeModMap R (biproduct.ι (fun k : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) k) i)).hom) ≫
          e.inv.hom := by
    intro i
    change (e.hom.hom ≫
        (freeModMap R (biproduct.π (fun k : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) k) i)).hom) ≫
        ((freeModMap R (biproduct.ι (fun k : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) k) i)).hom ≫
          e.inv.hom) = _
    repeat' erw [Category.assoc]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => h i) ?_
  erw [← Preadditive.comp_sum, ← Preadditive.sum_comp]
  refine Eq.trans (whisker_eq _ (eq_whisker
    (freeModMap_biproduct_total R (fun k : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) k)) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.id_comp _)) ?_
  exact congrArg Mod.Hom.hom e.hom_inv_id

/-- **A morphism killed by the fibre functor is killed by base
change.** -/
theorem whiskerLeft_eq_zero_of_fibre
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] [IsCommMonObj R]
    {V W : D} (fm : V ⟶ W)
    {p q : ℕ} (e : freeMod R V ≅ freeMod R (L.mix p q))
    (h : (fibreFun L R).map fm = 0) : R ◁ fm = 0 := by
  classical
  refine hom_eq_zero_of_generators R (mixSec L R e) (mixRet L R e)
    (mixTotal L R e) (freeModMap R fm) ?_
  rintro (j | j)
  · have hz : (((λ_ (𝟙_ D)).inv ≫ (η[R] ▷ (𝟙_ D)) ≫
        (mixSec L R e (Sum.inl j)).hom) ≫
          (freeModMap R fm).hom) = 0 := by
      change ((fibreFun L R).map fm).evenMap
        ((λ_ (𝟙_ D)).inv ≫ (η[R] ▷ (𝟙_ D)) ≫
          (mixSec L R e (Sum.inl j)).hom) = 0
      rw [h]
      rfl
    refine Eq.trans ?_ hz
    exact (Eq.trans (Category.assoc _ _ _)
      (whisker_eq _ (Category.assoc _ _ _))).symm
  · have hz : (((λ_ L.obj).inv ≫ (η[R] ▷ L.obj) ≫
        (mixSec L R e (Sum.inr j)).hom) ≫
          (freeModMap R fm).hom) = 0 := by
      change ((fibreFun L R).map fm).oddMap
        ((λ_ L.obj).inv ≫ (η[R] ▷ L.obj) ≫
          (mixSec L R e (Sum.inr j)).hom) = 0
      rw [h]
      rfl
    refine Eq.trans ?_ hz
    exact (Eq.trans (Category.assoc _ _ _)
      (whisker_eq _ (Category.assoc _ _ _))).symm

/-- **Base change is faithful when the unit is a
monomorphism.** -/
theorem eq_zero_of_whiskerLeft
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] (R : D) [MonObj R]
    [∀ Z : D, (tensorRight Z).PreservesMonomorphisms]
    (hη : Mono η[R]) {V W : D}
    (fm : V ⟶ W) (h : R ◁ fm = 0) : fm = 0 := by
  have := hη
  have : Mono (η[R] ▷ W) :=
    (tensorRight W).map_mono η[R]
  have h1 : fm ≫ ((λ_ W).inv ≫ (η[R] ▷ W)) = 0 := by
    have h2 : (λ_ V).inv ≫ (η[R] ▷ V) ≫ (R ◁ fm) = 0 := by
      rw [h, Limits.comp_zero, Limits.comp_zero]
    rw [← whisker_exchange, ← Category.assoc,
      ← leftUnitor_inv_naturality, Category.assoc] at h2
    exact h2
  have : Mono ((λ_ W).inv ≫ (η[R] ▷ W)) := mono_comp _ _
  exact (cancel_mono ((λ_ W).inv ≫ (η[R] ▷ W))).mp
    (h1.trans (Limits.zero_comp).symm)

/-- **The fibre functor is faithful** on the objects that become
mixed sums. -/
theorem fibreFun_map_eq_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] [IsCommMonObj R]
    [∀ Z : D, (tensorRight Z).PreservesMonomorphisms]
    (hη : Mono η[R]) {V W : D}
    (fm : V ⟶ W) {p q : ℕ}
    (e : freeMod R V ≅ freeMod R (L.mix p q))
    (h : (fibreFun L R).map fm = 0) : fm = 0 :=
  eq_zero_of_whiskerLeft R hη fm
    (whiskerLeft_eq_zero_of_fibre L R fm e h)

end

end RS
