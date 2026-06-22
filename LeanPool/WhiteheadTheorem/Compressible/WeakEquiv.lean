/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.Compressible.Disk
import LeanPool.WhiteheadTheorem.Compressible.CWComplex

/-!
This file proves that if `B` and `Y` are CW-complexes
and `f : B ⟶ Y` is a weak homotopy equivalence,
then the induced map $f_* : [X, B] → [X, Y]$ is bijective for all CW-complexes `X`.

## TODO
`TopCat.LiftStructUpToRelHomotopy.curriedH_prop` is not used,
hence the definition `TopCat.LiftStructUpToRelHomotopy` can be weakened (?)

## References
* T. tom Dieck, *Algebraic topology*. Theorem 8.4.3.
-/


universe u

variable {B Y : TopCat.{u}} {f : B ⟶ Y}


namespace TopCat

/-- If `f : B ⟶ Y` is a weak homotopy equivalence and $(X, A)$ is a relative CW-complex,
then the inclusion map `MapCyl.domIncl φ` from `B` to the mapping cylinder of `φ`
is compressible w.r.t. the inclusion map `A ⟶ X` from the $(-1)$-skeleton to `X`. -/
theorem _root_.TopCat.IsCompressible.relCWComplex_of_isWeakHomotopyEquiv
    (hf : IsWeakHomotopyEquiv f.hom) (X : RelCWComplex) :
    IsCompressible (X.skIncl 0) (MapCyl.domIncl f) := by
  apply IsCompressible.relCWComplex_of_diskBoundaryIncl
  exact fun n ↦ disk.isCompressible_mapCyl_domIncl_of_isWeakHomotopyEquiv n f hf

end TopCat


namespace IsWeakHomotopyEquiv

open TopCat CategoryTheory unitInterval

/-- if `B` and `Y` are CW-complexes and `f : B ⟶ Y` is a weak homotopy equivalence,
then the induced map $f_* : [X, B] → [X, Y]$ is surjective for all CW-complexes `X`.
```
∅ -----z----→ B
|             |
|       MapCyl.domIncl f
|             |
↓             ↓
X -----G----→ MapCyl f
```
-/
theorem CWComplex_induced_map_surjective
    (hf : IsWeakHomotopyEquiv f.hom) (X : CWComplex) (g : X.toTopCat ⟶ Y) :
    ∃ g' : X.toTopCat ⟶ B, (g' ≫ f).hom.Homotopic g.hom := by
  have com := IsCompressible.relCWComplex_of_isWeakHomotopyEquiv hf X.toRelCWComplex
  let z : X.sk 0 ⟶ B :=
    letI := X.isEmpty_sk_zero; ofHom ⟨fun x ↦ isEmptyElim x, continuous_of_discreteTopology⟩
  let G : X.toTopCat ⟶ MapCyl f := g ≫ MapCyl.codIncl f
  have sq : CommSq z (X.skIncl 0) (MapCyl.domIncl f) G :=
    ⟨by ext x; have := X.isEmpty_sk_zero; exact isEmptyElim x⟩
  let l := com.sq_hasLift sq |>.hasLift.some
  use l.l
  exact ContinuousMap.Homotopic.symm <| Nonempty.intro <|
    { toContinuousMap :=
        ((ContinuousMap.Homotopy.refl (MapCyl.retr f).hom).comp
          l.H.some.toHomotopy).toContinuousMap
      map_zero_left x := by
        change ((ContinuousMap.Homotopy.refl (MapCyl.retr f).hom).comp
          l.H.some.toHomotopy) (0, x) = g.hom x
        rw [ContinuousMap.Homotopy.comp_apply]
        simp only [ContinuousMap.Homotopy.apply_zero]
        change (g ≫ MapCyl.codIncl f ≫ MapCyl.retr f).hom x = g.hom x
        congr 2
        rw [MapCyl.codIncl_retr_eq_id, Category.comp_id]
      map_one_left x := by
        change ((ContinuousMap.Homotopy.refl (MapCyl.retr f).hom).comp
          l.H.some.toHomotopy) (1, x) = (l.l ≫ f).hom x
        rw [ContinuousMap.Homotopy.comp_apply]
        simp only [ContinuousMap.Homotopy.apply_one]
        change (l.l ≫ MapCyl.domIncl f ≫ MapCyl.retr f).hom x = (l.l ≫ f).hom x
        congr 3
        exact MapCyl.domIncl_retr_eq f }

/-- if `B` and `Y` are CW-complexes and `f : B ⟶ Y` is a weak homotopy equivalence,
then the induced map $f_* : [X, B] → [X, Y]$ is injective for all CW-complexes `X`.
```
{0, 1} × X ------- G₀₁ -------→ B
   |                            |
   |                     MapCyl.domIncl f
X.zeroOneProdInclIProd          |
   ↓                            ↓
I × X ------------ G ------→ MapCyl f
```
-/
theorem CWComplex_induced_map_injective
    (hf : IsWeakHomotopyEquiv f.hom) (X : CWComplex) (g₀ g₁ : X.toTopCat ⟶ B)
    (hg : (g₀ ≫ f).hom.Homotopic (g₁ ≫ f).hom) :
    g₀.hom.Homotopic g₁.hom := by
  replace hg :
      (g₀ ≫ MapCyl.domIncl f ≫ MapCyl.retr f ≫ MapCyl.codIncl f).hom.Homotopic
      (g₁ ≫ MapCyl.domIncl f ≫ MapCyl.retr f ≫ MapCyl.codIncl f).hom := by
    rw [MapCyl.domIncl_retr_eq_assoc]
    exact (ContinuousMap.Homotopic.refl (MapCyl.codIncl f).hom).comp hg
  have hg₀ :
      (g₀ ≫ MapCyl.domIncl f ≫ MapCyl.retr f ≫ MapCyl.codIncl f).hom.Homotopic
      (g₀ ≫ MapCyl.domIncl f).hom :=
    (MapCyl.homotopyEquivBase f).left_inv.comp
      (ContinuousMap.Homotopic.refl (g₀ ≫ MapCyl.domIncl f).hom)
  have hg₁ :
      (g₁ ≫ MapCyl.domIncl f ≫ MapCyl.retr f ≫ MapCyl.codIncl f).hom.Homotopic
      (g₁ ≫ MapCyl.domIncl f).hom :=
    (MapCyl.homotopyEquivBase f).left_inv.comp
      (ContinuousMap.Homotopic.refl (g₁ ≫ MapCyl.domIncl f).hom)
  replace hg := hg₀.symm.trans hg |>.trans hg₁
  let G : TopCat.of (I × X.toTopCat) ⟶ MapCyl f := ofHom hg.some.toContinuousMap
  let G₀₁ : TopCat.of (({0, 1} : Set ℝ) × X.toTopCat) ⟶ B := ofHom
    { toFun x := if x.fst.val = 0 then g₀.hom x.snd else g₁.hom x.snd
      continuous_toFun := by
        have : (fun x : TopCat.of (({0, 1} : Set ℝ) × X.toTopCat) ↦
                  if x.fst.val = 0 then g₀.hom x.snd else g₁.hom x.snd) =
            (fun x ↦ if x.fst.val ≤ 1 / 2 then g₀.hom x.snd else g₁.hom x.snd) := by
          ext ⟨⟨tval, tprop⟩, x⟩
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at tprop
          cases tprop with
          | inl h0 => subst h0; simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
          | inr h1 => subst h1; simp only [one_ne_zero, one_div, (by norm_num : ¬((1 : ℝ) ≤ 2⁻¹))]
        rw [this]
        refine Continuous.if_le
          ((Hom.hom g₀).continuous.comp continuous_snd)
          ((Hom.hom g₁).continuous.comp continuous_snd)
          (continuous_subtype_val.comp continuous_fst) continuous_const ?_
        intro x hx
        simp_all only [Category.assoc, TopCat.hom_comp, ContinuousMap.comp_assoc, hom_ofHom,
          one_div]
        obtain ⟨⟨val, property⟩, snd⟩ := x
        subst hx
        dsimp only
        simp_all only [Set.mem_insert_iff, inv_eq_zero, OfNat.ofNat_ne_zero,
          Set.mem_singleton_iff, inv_eq_one, OfNat.ofNat_ne_one, or_self] }
  have sq : CommSq G₀₁ X.zeroOneProdInclIProd (MapCyl.domIncl f) G := ⟨by
    ext ⟨⟨tval, tprop⟩, x⟩
    unfold G₀₁ G
    simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_assoc, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, Limits.colimit.cocone_x, ContinuousMap.prodMap_apply,
      ContinuousMap.coe_id, Prod.map_apply, id_eq]
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at tprop
    cases tprop with
    | inl h0 =>
        subst h0; simp only [↓reduceIte, Set.Icc.mk_zero]
        change _ = (Nonempty.some hg).toContinuousMap (0, x)
        rw [ContinuousMap.Homotopy.coe_toContinuousMap, hg.some.apply_zero x]
        rfl
    | inr h1 =>
        subst h1; simp only [one_ne_zero, ↓reduceIte, Set.Icc.mk_one]
        change _ = (Nonempty.some hg).toContinuousMap (1, x)
        rw [ContinuousMap.Homotopy.coe_toContinuousMap, hg.some.apply_one x]
        rfl ⟩
  have com := IsCompressible.of_arrow_iso_left (CWComplex.IProd.arrowIso X) <|
    IsCompressible.relCWComplex_of_isWeakHomotopyEquiv hf X.IProd
  let l := com.sq_hasLift sq |>.hasLift.some
  exact Nonempty.intro <|
    { toContinuousMap := l.l.hom
      map_zero_left x := by
        have zero_mem : 0 ∈ ({0, 1} : Set ℝ) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, zero_ne_one, or_false]
        change (X.zeroOneProdInclIProd  ≫ l.l) (⟨0, zero_mem⟩, x) = g₀ x
        rw [l.fac_left]
        unfold G₀₁
        simp only [hom_ofHom, ContinuousMap.coe_mk, ↓reduceIte]
      map_one_left x := by
        have one_mem : 1 ∈ ({0, 1} : Set ℝ) := by
          simp only [Set.mem_insert_iff, one_ne_zero, Set.mem_singleton_iff, or_true]
        change (X.zeroOneProdInclIProd  ≫ l.l) (⟨1, one_mem⟩, x) = g₁ x
        rw [l.fac_left]
        unfold G₀₁
        simp only [hom_ofHom, ContinuousMap.coe_mk, one_ne_zero, ↓reduceIte] }

end IsWeakHomotopyEquiv
