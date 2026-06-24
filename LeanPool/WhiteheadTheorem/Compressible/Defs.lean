/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.Exponential
import LeanPool.WhiteheadTheorem.Shapes.Maps
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# LeanPool.WhiteheadTheorem.Compressible.Defs

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Compressible.Defs`.
-/


open CategoryTheory unitInterval

namespace TopCat

variable {A' A X' X : TopCat.{u}}
variable {f : A' ⟶ A} {ι : A' ⟶ X'} {i : A ⟶ X} {F : X' ⟶ X}

/-- A commutative square
```
A' -----f----→ A
|              |
ι              i
|              |
↓              ↓
X' -----F----→ X
```
in `TopCat` is said to have a lift, up to relative homotopy, if
there exists a map ` l : X' ⟶ A ` and a homotopy ` H : I × X' ⟶ X ` from `F` to `l ≫ i`,
such that `ι ≫ l = f` and `∀ t, ι ≫ H(t, ·) = f ≫ i`.

(Note: If `i` is injective, then `ι ≫ l = f` is implied by `ι ≫ H(1, ·) = f ≫ i`,
since `H(1, ·) = l ≫ i`.)

See `TopCat.LiftStructUpToRelHomotopy.curriedMk` for a more convenient constructor.
-/
structure LiftStructUpToRelHomotopy (sq : CommSq f ι i F) where
  /-- The lift -/
  l : X' ⟶ A
  /-- The upper left triangle commutes. -/
  fac_left : ι ≫ l = f
  /-- The lower right triangle commutes up to relative homotopy. -/
  H : ContinuousMap.HomotopicRel F.hom (l ≫ i).hom (Set.range ι)
  -- H : ContinuousMap.HomotopicWith F.hom (l ≫ i).hom fun h ↦ h ∘ ⇑ι = ⇑(f ≫ i)


namespace LiftStructUpToRelHomotopy

variable {sq : CommSq f ι i F} (l : LiftStructUpToRelHomotopy sq)

/-- `curriedH` -/
noncomputable def curriedH : X' ⟶ TopCat.of C(I, X) :=
  ofHom l.H.some.toContinuousMap.argSwap.curry

lemma curriedH_apply_zero :
    l.curriedH ≫ PathSpace.eval₀ X = F := by
  unfold curriedH PathSpace.eval₀
  simp_all only [ContinuousMap.argSwap, hom_comp, ContinuousMap.coe_mk]
  ext x_1 : 1
  simp_all only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply,
    ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.apply_zero]

lemma curriedH_apply_zero' :
    ∀ x, l.curriedH.hom.uncurry.argSwap.toFun (0, x) = F.hom x := by
  intro x
  simp only [ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
    ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
    Function.uncurry_apply_pair]
  change (l.curriedH ≫ PathSpace.eval₀ _) x = _
  congr 2
  exact l.curriedH_apply_zero

lemma curriedH_apply_one :
    l.curriedH ≫ PathSpace.eval₁ X = l.l ≫ i := by
  unfold curriedH PathSpace.eval₁
  simp only [ContinuousMap.argSwap, hom_comp, ContinuousMap.coe_mk]
  ext x : 1
  simp_all only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply,
    ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.apply_one]

lemma curriedH_apply_one' :
    ∀ x, l.curriedH.hom.uncurry.argSwap.toFun (1, x) = (l.l ≫ i).hom x := by
  intro x
  simp only [ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
    ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
    Function.uncurry_apply_pair, hom_comp]
  change (l.curriedH ≫ PathSpace.eval₁ _) x = (l.l ≫ i) x
  congr 2
  exact l.curriedH_apply_one

lemma curriedH_prop :
    ∀ t, ι ≫ l.curriedH ≫ PathSpace.evalAt X t = ι ≫ F := by
  intro t
  unfold curriedH PathSpace.evalAt
  ext a
  simp only [ContinuousMap.argSwap, hom_comp, ContinuousMap.coe_mk, hom_ofHom,
    ContinuousMap.comp_assoc, ContinuousMap.comp_apply, ContinuousMap.curry_apply,
    ContinuousMap.prodSwap_apply, ContinuousMap.Homotopy.coe_toContinuousMap,
    ContinuousMap.HomotopyWith.coe_toHomotopy]
  have := l.H.some.prop t (ι a) (Set.mem_range_self a)
  simp_all only [hom_comp, ContinuousMap.Homotopy.curry_apply,
    ContinuousMap.HomotopyWith.coe_toHomotopy]

lemma curriedH_prop' :
    ∀ t, ∀ x ∈ Set.range ι, l.curriedH.hom.uncurry.argSwap (t, x) = F.hom x := by
  intro t x hx
  replace hx := Set.mem_range.mp hx
  obtain ⟨a, ha⟩ := hx
  subst ha
  simp only [ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.comp_apply,
    ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair]
  change (ι ≫ l.curriedH ≫ PathSpace.evalAt _ t) _ = (ι ≫ F) _
  congr 2
  exact l.curriedH_prop t

/-- `curriedMk` -/
def curriedMk
    (l : X' ⟶ A)
    (fac_left : ι ≫ l = f)
    (curriedH : X' ⟶ TopCat.of C(I, X))
    (curriedH_apply_zero : curriedH ≫ PathSpace.eval₀ X = F)
    (curriedH_apply_one : curriedH ≫ PathSpace.eval₁ X = l ≫ i)
    (curriedH_prop : ∀ t, ι ≫ curriedH ≫ PathSpace.evalAt X t = ι ≫ F) :
    LiftStructUpToRelHomotopy sq where
  l := l
  fac_left := fac_left
  H := Nonempty.intro
    { toContinuousMap := curriedH.hom.uncurry.argSwap
      map_zero_left x := by
        simp only [ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
          ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
          Function.uncurry_apply_pair]
        change (curriedH ≫ PathSpace.eval₀ _) x = _
        congr 2  -- curriedH_apply_zero
      map_one_left x := by
        simp only [ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
          ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
          Function.uncurry_apply_pair, hom_comp]
        change (curriedH ≫ PathSpace.eval₁ _) x = (l ≫ i) x
        congr 2  -- curriedH_apply_one
      prop' t x hx := by
        replace hx := Set.mem_range.mp hx
        obtain ⟨a, ha⟩ := hx
        subst ha
        change (ι ≫ curriedH ≫ PathSpace.evalAt _ t) _ = (ι ≫ F) _
        congr 2
        exact curriedH_prop t }

end LiftStructUpToRelHomotopy



/-- `HasLiftUpToRelHomotopy` -/
structure HasLiftUpToRelHomotopy (sq : CommSq f ι i F) : Prop where
  hasLift : Nonempty <| LiftStructUpToRelHomotopy sq

/-- A map `i : A ⟶ X` is called compressible with respect to ` ι : A' ⟶ X' `
if every commutative square
```
A' -----f----→ A
|              |
ι              i
|              |
↓              ↓
X' -----F----→ X
```
has a lift, up to relative homotopy.
-/
structure IsCompressible (ι : A' ⟶ X') (i : A ⟶ X) : Prop where
  sq_hasLift : ∀ {F : X' ⟶ X} {f : A' ⟶ A} (sq : CommSq f ι i F), HasLiftUpToRelHomotopy sq

end TopCat
