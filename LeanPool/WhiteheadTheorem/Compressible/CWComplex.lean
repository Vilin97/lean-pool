/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.CWComplex.IProd.Iso
import LeanPool.WhiteheadTheorem.HEP.Cofibration
import LeanPool.WhiteheadTheorem.Compressible.Defs

/-!
This file proves that if a map is compressible with respect to
`TopCat.diskBoundaryIncl n : ∂𝔻 n ⟶ 𝔻 n`
(inclusion from the boundary of a disk to the disk),
then it is compressible with respect to the inclusion map
from the `-1`-skeleton of any relative CW-complex to the relative CW-complex.
This is the theorem `IsCompressible.relCWComplex_of_diskBoundaryIncl`.

Some proofs are similar to the ones in `Mathlib.CategoryTheory.LiftingProperties.Limits`
-/


open CategoryTheory unitInterval

universe u


namespace TopCat

/-- Suppose `j` is compressible w.r.t. `i1`, and `i2` is an isomorphism,
then `j` is compressible w.r.t. `i1 ≫ i2`.-/
lemma IsCompressible.of_comp_iso_left
    {A B Z X Y : TopCat.{u}} {i1 : A ⟶ X} {i2 : X ⟶ Z} {j : B ⟶ Y}
    (hcom1 : IsCompressible i1 j) [IsIso i2] :
    IsCompressible (i1 ≫ i2) j where
  sq_hasLift := fun {F f} sq ↦ by
    have sq1 : CommSq f i1 j (i2 ≫ F) := ⟨by rw [sq.w, Category.assoc]⟩
    let l1 := hcom1.sq_hasLift sq1 |>.hasLift.some
    let L : Z ⟶ B := inv i2 ≫ l1.l
    let H : Z ⟶ TopCat.of C(I, Y) := inv i2 ≫ l1.curriedH
    refine ⟨Nonempty.intro <| LiftStructUpToRelHomotopy.curriedMk L ?_ H ?_ ?_ fun t ↦ ?_⟩
    · rw [Category.assoc, IsIso.hom_inv_id_assoc, l1.fac_left]
    · rw [Category.assoc, l1.curriedH_apply_zero, IsIso.inv_hom_id_assoc]
    · rw [Category.assoc, l1.curriedH_apply_one]; rfl
    · have := l1.curriedH_prop t
      simp_all only [Category.assoc, IsIso.hom_inv_id_assoc, l1, H]

/-- Suppose `i1` is an isomorphism and `j` is compressible w.r.t. `i2`,
then `j` is compressible w.r.t. `i1 ≫ i2`.-/
lemma IsCompressible.of_iso_comp_left
    {A B Z X Y : TopCat.{u}} {i1 : A ⟶ X} {i2 : X ⟶ Z} {j : B ⟶ Y}
    [IsIso i1] (hcom2 : IsCompressible i2 j) :
    IsCompressible (i1 ≫ i2) j where
  sq_hasLift := fun {F f} sq ↦ by
    have sq2 : CommSq (inv i1 ≫ f) i2 j F :=
      ⟨by rw [Category.assoc, sq.w, Category.assoc, IsIso.inv_hom_id_assoc]⟩
    let l2 := hcom2.sq_hasLift sq2 |>.hasLift.some
    let L : Z ⟶ B := l2.l
    let H : Z ⟶ TopCat.of C(I, Y) := l2.curriedH
    refine ⟨Nonempty.intro <| LiftStructUpToRelHomotopy.curriedMk L ?_ H ?_ ?_ fun t ↦ ?_⟩
    . rw [Category.assoc, l2.fac_left, IsIso.hom_inv_id_assoc]
    . rw [l2.curriedH_apply_zero]
    . rw [l2.curriedH_apply_one]
    . rw [Category.assoc, l2.curriedH_prop t, Category.assoc]

/-- Suppose `j` is compressible w.r.t. `i`,
and `i` is isomorphic to `i'` in the arrow category,
then `j` is compressible w.r.t. `i'`.-/
lemma IsCompressible.of_arrow_iso_left
    {A X A' X' B Y : TopCat.{u}} {i : A ⟶ X} {i' : A' ⟶ X'} {j : B ⟶ Y}
    (e : Arrow.mk i ≅ Arrow.mk i') (hcom : IsCompressible i j) :
    IsCompressible i' j := by
  rw [Arrow.iso_w' e]
  exact IsCompressible.of_iso_comp_left <| IsCompressible.of_comp_iso_left hcom

/--
If `j` is compressible w.r.t. `i`, then it is also compressible w.r.t. `∐ i`.
```
∐ A -----f----→ B
 |              |
∐ i             j
 |              |
 ↓              ↓
∐ X -----F----→ Y
```
TODO: This lemma can be generalized to the case where
each component function of `∐ A ⟶ ∐ X` can be different.
-/
lemma IsCompressible.coprod {A B X Y : TopCat.{u}} {i : A ⟶ X} {j : B ⟶ Y}
    (hcom : IsCompressible i j) (cells : Type u) :
    IsCompressible (Limits.Sigma.map fun (_ : cells) ↦ i) j where
  sq_hasLift := fun {F f} sq ↦ by
    have sq' c : CommSq
        (Limits.Sigma.ι (fun _ ↦ A) c ≫ f) i j
        (Limits.Sigma.ι (fun _ ↦ X) c ≫ F) :=
      ⟨by simp only [Category.assoc, sq.w, Limits.ι_colimMap_assoc, Discrete.functor_obj_eq_as,
            Discrete.natTrans_app] ⟩
    let l c := hcom.sq_hasLift (sq' c) |>.hasLift.some
    let L := Limits.Sigma.desc fun c ↦ (l c).l
    let h c := (l c).H.some.toContinuousMap.argSwap.curry
    let H := Limits.Sigma.desc fun c ↦ ofHom (h c)
    refine ⟨Nonempty.intro <| LiftStructUpToRelHomotopy.curriedMk L ?_ H ?_ ?_ fun t ↦ ?_⟩
    · apply Limits.Sigma.hom_ext
      intro c
      have := (l c).fac_left
      simp_all only [Limits.colimit.map_desc, Limits.colimit.ι_desc, Limits.Cocones.precompose_obj_pt,
        Limits.Cofan.mk_pt, Limits.Cocones.precompose_obj_ι, NatTrans.comp_app, Discrete.functor_obj_eq_as,
        Functor.const_obj_obj, Discrete.natTrans_app, Limits.Cofan.mk_ι_app, l, L]
    · apply Limits.Sigma.hom_ext
      intro c
      ext x
      -- have := (l c).H.some.apply_zero x
      simp_all only [hom_comp, ContinuousMap.comp_apply, ContinuousMap.HomotopyWith.apply_zero,
        ContinuousMap.argSwap, ContinuousMap.coe_mk, Limits.colimit.ι_desc_assoc, Discrete.functor_obj_eq_as,
        Limits.Cofan.mk_pt, Limits.Cofan.mk_ι_app, hom_ofHom, ContinuousMap.curry_apply,
        ContinuousMap.prodSwap_apply, ContinuousMap.Homotopy.coe_toContinuousMap,
        ContinuousMap.Homotopy.apply_zero, l, L, H, h]
    · apply Limits.Sigma.hom_ext
      intro c
      ext x
      simp_all only [ContinuousMap.argSwap, hom_comp, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        Limits.colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Limits.Cofan.mk_pt, Limits.Cofan.mk_ι_app,
        hom_ofHom, ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply,
        ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.apply_one, l, L, H, h]
    · apply Limits.Sigma.hom_ext
      intro c
      ext a
      have := (l c).H.some.prop t (i a) (Set.mem_range_self a)
      simp_all only [hom_comp, ContinuousMap.comp_apply, ContinuousMap.Homotopy.curry_apply,
        ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.argSwap, ContinuousMap.coe_mk,
        Limits.colimit.map_desc_assoc, Limits.Cofan.mk_pt, Limits.colimit.ι_desc_assoc, Discrete.functor_obj_eq_as,
        Limits.Cocones.precompose_obj_pt, Limits.Cocones.precompose_obj_ι, NatTrans.comp_app, Functor.const_obj_obj,
        Discrete.natTrans_app, Limits.Cofan.mk_ι_app, Category.assoc, hom_ofHom, ContinuousMap.comp_assoc,
        ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply, ContinuousMap.Homotopy.coe_toContinuousMap,
        Limits.ι_colimMap_assoc, l, h, L, H]

/--
Suppose the left square in the diagram below is a pushout square.
If `j` is compressible w.r.t. `ι`, then it is also compressible w.r.t. `i`.
```
A' -----φ----→ A -----f----→ B
 |             |             |
 ι             i             j
 |             |             |
 ↓             ↓             ↓
X' -----Φ----→ X -----F----→ Y
```
-/
lemma IsCompressible.pushout {A' A B X' X Y : TopCat.{u}}
    {ι : A' ⟶ X'} {i : A ⟶ X} {j : B ⟶ Y}
    {φ : A' ⟶ A} {Φ : X' ⟶ X} (po : IsPushout φ ι i Φ)
    (com : IsCompressible ι j) : IsCompressible i j where
  sq_hasLift := fun {F f} sq ↦ by
    have sq' : CommSq (φ ≫ f) ι j (Φ ≫ F) := ⟨by rw [Category.assoc, sq.w, po.w_assoc] ⟩
    let l' := com.sq_hasLift sq' |>.hasLift.some
    let l   : X  ⟶ B          := po.desc f l'.l l'.fac_left.symm
    let H'  : X' ⟶ of C(I, Y) := l'.curriedH
    let H'' : A  ⟶ of C(I, Y) := PathSpace.homToConstPaths (i ≫ F)
    let G   : X  ⟶ of C(I, Y) := po.desc H'' H' <| by
      unfold H'' H'
      ext a' t
      simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.curry_apply,
        ContinuousMap.coe_mk]
      change (φ ≫ i ≫ F) _ = _
      rw [po.w_assoc]
      have := l'.curriedH_prop' t (ι a') (Set.mem_range_self a')
      simp only [ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.comp_apply,
        ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair,
        hom_comp] at this
      convert this.symm
    refine ⟨Nonempty.intro <| LiftStructUpToRelHomotopy.curriedMk l ?_ G ?_ ?_ fun t ↦ ?_⟩
    · apply po.inl_desc
    · apply po.hom_ext
      · rw [po.inl_desc_assoc]; rfl
      · rw [po.inr_desc_assoc, l'.curriedH_apply_zero]
    · apply po.hom_ext
      · rw [po.inl_desc_assoc, po.inl_desc_assoc, sq.w]; rfl
      · rw [po.inr_desc_assoc, l'.curriedH_apply_one, po.inr_desc_assoc]
    · simp only [po.inl_desc_assoc, G, H'', H', l']; rfl


namespace IsCompressible.relCWComplex

/--
```
 X.sk n ---------------------→ B
   |              f            |
   |                           j
   |                           |
   ↓                     F     ↓
X.sk (n + 1) ----→ X --------→ Y
```
-/
private structure FStruct
    (X : RelCWComplex.{u}) {B Y : TopCat.{u}} (j : B ⟶ Y) (n : ℕ) where
  /-- $f_n$ -/
  f : X.sk n ⟶ B
  /-- $F_n$ -/
  F : X.toTopCat ⟶ Y
  /-- The maps $f_n$ and $F_n$ agree on `X.sk n` -/
  sq : CommSq f (X.skInclSucc n) j (X.skIncl (n + 1) ≫ F)
  /-- The structure containing the lift `l.l : X.sk (n + 1)  ⟶ B`, i.e., the next `f` -/
  l : LiftStructUpToRelHomotopy sq
  /-- The commutative square for constructing the homotopy from $F_n$ to $F_{n+1}$ -/
  hep_sq : CommSq l.curriedH (X.skIncl (n + 1)) (PathSpace.eval₀ Y) F
  /-- The structure containing the homotopy `hep_l.l` from $F_n$ to $F_{n+1}$ -/
  hep_l : hep_sq.LiftStruct

variable {X : RelCWComplex.{u}} {B Y : TopCat.{u}} {j : B ⟶ Y}
  (jcom_sk : ∀ n, IsCompressible (X.skInclSucc n) j)
  {F₀ : X.toTopCat ⟶ Y} {f₀ : X.sk 0 ⟶ B}
  (sq : CommSq f₀ (X.skIncl 0) j F₀)

private noncomputable def F : ∀ n : ℕ, FStruct X j n
  | 0 => by
      let sq' : CommSq f₀ (X.skInclSucc 0) j (X.skIncl 1 ≫ F₀) :=
        ⟨by
          rw [sq.w, ← Category.assoc]
          congr 1
          apply Eq.symm
          exact Limits.colimit.w (Functor.ofSequence fun n ↦ (X.attachCells n).incl) <|
            homOfLE (by omega : 0 ≤ 1) ⟩
      let l' := jcom_sk 0 |>.sq_hasLift sq' |>.hasLift.some
      have hep_sq : CommSq l'.curriedH (X.skIncl 1) (PathSpace.eval₀ Y) F₀ :=
        ⟨l'.curriedH_apply_zero⟩
      exact
        { f := f₀
          F := F₀
          sq := sq'
          l := l'
          hep_sq := hep_sq
          hep_l := X.skIncl_isCofibration 1 |>.hasCurriedHEP Y
            |>.hasLift |>.sq_hasLift hep_sq |>.exists_lift.some }
  | n + 1 => by
      let f' := (F n).l.l
      let F' := (F n).hep_l.l ≫ PathSpace.eval₁ Y
      let sq' : CommSq f' (X.skInclSucc (n + 1)) j (X.skIncl (n + 1 + 1) ≫ F') :=
        ⟨by
          rw [← (F n).l.curriedH_apply_one, ← Category.assoc, ← Category.assoc]
          congr 1
          rw [X.skInclSucc_skIncl_eq, (F n).hep_l.fac_left] ⟩
      let l' := jcom_sk (n + 1) |>.sq_hasLift sq' |>.hasLift.some
      have hep_sq : CommSq l'.curriedH (X.skIncl (n + 1 + 1)) (PathSpace.eval₀ Y) F' :=
        ⟨l'.curriedH_apply_zero⟩
      exact
        { f := f'
          F := F'
          sq := sq'
          l := l'
          hep_sq := hep_sq
          hep_l := X.skIncl_isCofibration (n + 1 + 1) |>.hasCurriedHEP Y
            |>.hasLift |>.sq_hasLift hep_sq |>.exists_lift.some }

/-- Invoke this definition with `m = 0` and `step = n` to get the homotopy `C(I × (X.sk n), Y)`
which is the concatenation of `(n + 1)` homotopies,
where the first one is defined on the interval `[0, 1/2]`, the second on `[1/2, 3/4]`,
the third on `[3/4, 7/8]`, ..., the `n`-th on `[1 - 1/2^(n-1), 1 - 1/2^n]`.
The `(n + 1)`-th homotopy defined on `t ∈ [1 - 1/2^n, 1]` is constant (independent of `t`).

Note: invoking this definition with `step = 0` gives the last homotopy
in the chain of `(n + 1)` homotopies. -/
private noncomputable def H (n m step : ℕ) (hstep : m + step = n) :
    ContinuousMap.Homotopy
      (X.skIncl n ≫ (F jcom_sk sq m).F).hom
      (X.skIncl n ≫ (F jcom_sk sq n).F).hom :=
  match step with
  | 0 =>
      { toContinuousMap := ContinuousMap.Homotopy.refl (X.skIncl n ≫ (F jcom_sk sq n).F).hom
        map_zero_left x := by subst hstep; rfl
        map_one_left x := by subst hstep; rfl }
      -- hstep ▸ ContinuousMap.Homotopy.refl (X.skIncl n ≫ (F jcom_sk sq n).F).hom
      -- ContinuousMap.Homotopy.refl ((F n).f ≫ j).hom
  | step + 1 => by
      let Hlow : ContinuousMap.Homotopy
          (X.skIncl n ≫ (F jcom_sk sq m).F).hom
          (X.skIncl n ≫ (F jcom_sk sq (m + 1)).F).hom :=
        { toContinuousMap := (X.skIncl n ≫ (F jcom_sk sq m).hep_l.l).hom.uncurry.argSwap
          map_zero_left x := by
            change (X.skIncl n ≫ (F ..).hep_l.l ≫ PathSpace.eval₀ _).hom x = _
            rw [(F ..).hep_l.fac_right]
          map_one_left x := rfl }
      let Hhigh : ContinuousMap.Homotopy
          (X.skIncl n ≫ (F jcom_sk sq (m + 1)).F).hom
          (X.skIncl n ≫ (F jcom_sk sq n).F).hom :=
        H n (m + 1) step (by rw [← hstep, add_comm step 1, add_assoc])
      exact Hlow.trans Hhigh  -- `Hlow` on `[0, 1/2]`

private lemma H_skInclSucc (n m step : ℕ) (hstep : m + step = n) :
    ∀ x t,
      (H jcom_sk sq (n + 1) m (step + 1) (by omega)).toFun (t, (X.skInclSucc n).hom x) =
      (H jcom_sk sq n m step hstep).toFun (t, x) :=
  let F := TopCat.IsCompressible.relCWComplex.F jcom_sk sq
  match step with
  | 0 => by
      rw [Nat.add_zero] at hstep
      subst hstep
      intro x t
      simp only [hom_comp, H, ContinuousMap.argSwap, ContinuousMap.coe_mk,
        ContinuousMap.toFun_eq_coe, ContinuousMap.Homotopy.coe_toContinuousMap,
        ContinuousMap.coe_coe, ContinuousMap.Homotopy.refl_apply, ContinuousMap.comp_apply]
      simp only [ContinuousMap.Homotopy.trans_apply, one_div]
      by_cases ht : t.val ≤ 2⁻¹
      all_goals simp only [ht, ↓reduceDIte, hom_comp, ContinuousMap.comp_apply]
      · change (X.skInclSucc m ≫ ((X.skIncl (m + 1)) ≫ (F m).hep_l.l) ≫
            PathSpace.evalAt _ _).hom x = (X.skIncl m ≫ (F m).F).hom x
        congr 2
        rw [(F m).hep_l.fac_left, (F m).l.curriedH_prop]
        rw [← X.skInclSucc_skIncl_eq m, Category.assoc]
      · change (X.skInclSucc m ≫ (X.skIncl (m + 1)) ≫ (F (m + 1)).F).hom _ =
          (X.skIncl m ≫ (F m).F).hom _
        congr 2
        rw [← X.skInclSucc_skIncl_eq m, Category.assoc, ← (F m).l.curriedH_prop 1]
        congr 1
        rw [(by rfl : (F (m + 1)).F = (F m).hep_l.l ≫ PathSpace.evalAt _ 1)]
        rw [← Category.assoc, (F m).hep_l.fac_left]
  | step + 1 => by
      intro x t
      unfold H
      simp only [hom_comp, ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
        ContinuousMap.Homotopy.coe_toContinuousMap]
      simp only [ContinuousMap.Homotopy.trans_apply, one_div]
      by_cases ht : t.val ≤ 2⁻¹
      all_goals simp only [ht, ↓reduceDIte]
      · change ((X.skInclSucc n ≫ (X.skIncl (n + 1)) ≫ (F m).hep_l.l).hom x) _ =
          ((X.skIncl n ≫ (F m).hep_l.l).hom x) _
        congr 3
        rw [← Category.assoc, X.skInclSucc_skIncl_eq]
      · apply H_skInclSucc n (m + 1) step (by omega)

end IsCompressible.relCWComplex


/--
Suppose `X` is a relative CW-complex and `j : B ⟶ Y` is a continuous map.
If `j` is `n`-compressible for every natural number `n`,
then it is compressible w.r.t. the inclusion map from
the $(-1)$-skeleton of `X` to `X`, i.e., any map from the pair
`(X, X.sk 0)` to `(Y, B)` is homotopic relative to `X.sk 0` to a map into `B`.
```
X.sk 0 --- f₀ ---→ B
  |                |
  i                j
  |                |
  ↓                ↓
  X ----- F₀ ----→ Y
```
-/
theorem IsCompressible.relCWComplex_of_diskBoundaryIncl
    (X : RelCWComplex.{u}) {B Y : TopCat.{u}} (j : B ⟶ Y)
    (jcom : ∀ n, IsCompressible (diskBoundaryIncl n) j) :
    IsCompressible (X.skIncl 0) j where
  sq_hasLift := fun {F₀ f₀} sq ↦ by
    have jcom_sk n : IsCompressible (X.skInclSucc n) j := by
      apply IsCompressible.of_comp_iso_left
      apply IsCompressible.pushout (X.attachCells n).pushout_isPushout
      apply IsCompressible.coprod
      exact jcom n
    let F := IsCompressible.relCWComplex.F jcom_sk sq
    let H n := IsCompressible.relCWComplex.H jcom_sk sq n 0 n (by omega)
    let ccL : Limits.Cocone (Functor.ofSequence X.skInclSucc) :=
      { pt := B
        ι := NatTrans.ofSequence (fun n ↦ (F n).f)
          (fun n ↦ by
            simp only [Functor.ofSequence_obj, Functor.const_obj_obj, homOfLE_leOfHom,
              Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map, Category.comp_id]
            exact (F n).l.fac_left ) }
    let L : X.toTopCat ⟶ B :=
      Limits.colimit.desc (Functor.ofSequence X.skInclSucc) ccL
    let ccH : Limits.Cocone (Functor.ofSequence X.skInclSucc) :=
      { pt := TopCat.of C(I, Y)
        ι := NatTrans.ofSequence (fun n ↦ ofHom (H n).toContinuousMap.argSwap.curry)
          (fun n ↦ by
            simp only [Functor.ofSequence_obj, Functor.const_obj_obj, homOfLE_leOfHom,
              Functor.ofSequence_map_homOfLE_succ, ContinuousMap.argSwap, hom_comp,
              ContinuousMap.coe_mk, Functor.const_obj_map, Category.comp_id]
            ext x t
            simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.curry_apply,
              ContinuousMap.prodSwap_apply, ContinuousMap.Homotopy.coe_toContinuousMap]
            apply IsCompressible.relCWComplex.H_skInclSucc ) }
    let H' : X.toTopCat ⟶ TopCat.of C(I, Y) :=
      Limits.colimit.desc (Functor.ofSequence X.skInclSucc) ccH
    refine ⟨Nonempty.intro <| LiftStructUpToRelHomotopy.curriedMk L ?_ H' ?_ ?_ fun t ↦ ?_⟩
    · apply Limits.colimit.ι_desc
    any_goals
      apply Limits.colimit.hom_ext
      intro n
      rw [← Category.assoc, Limits.colimit.ι_desc]
      unfold ccH
      simp only [Functor.ofSequence_obj, ContinuousMap.argSwap, hom_comp, ContinuousMap.coe_mk,
        Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map, id_eq, hom_ofHom,
        ContinuousMap.comp_apply, ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply,
        ContinuousMap.Homotopy.coe_toContinuousMap, eq_mpr_eq_cast, NatTrans.ofSequence_app]
    · change _ = X.skIncl n ≫ _
      ext x
      simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply,
        ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.apply_zero]
      rfl
    · rw [← Category.assoc, Limits.colimit.ι_desc]
      unfold ccL
      simp only [Functor.ofSequence_obj, Functor.const_obj_obj, homOfLE_leOfHom,
        Functor.const_obj_map, id_eq, eq_mpr_eq_cast, NatTrans.ofSequence_app]
      ext x
      simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply,
        ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.apply_one]
      change (X.skIncl n ≫ (F n).F).hom _ = ((F n).f ≫ j).hom _
      congr 2
      rw [(F n).sq.w, ← Category.assoc, X.skInclSucc_skIncl_eq]
    · nth_rw 1 [RelCWComplex.skIncl]
      rw [← Category.assoc, Limits.colimit.ι_desc]
      unfold ccH
      simp only [ContinuousMap.argSwap, hom_comp, ContinuousMap.coe_mk, Functor.ofSequence_obj,
        Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map, id_eq, hom_ofHom,
        ContinuousMap.comp_apply, ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply,
        ContinuousMap.Homotopy.coe_toContinuousMap, eq_mpr_eq_cast, NatTrans.ofSequence_app]
      ext x
      simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply,
        ContinuousMap.Homotopy.coe_toContinuousMap]
      rfl

end TopCat
