/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.Defs
import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Defs
import LeanPool.WhiteheadTheorem.HEP.Cube
import LeanPool.WhiteheadTheorem.HEP.Cofibration
import LeanPool.WhiteheadTheorem.HomotopyGroup.InducedMaps
-- import Mathlib.CategoryTheory.Category.Pointed
-- import WhiteheadTheorem.HEP.Retract
-- import Mathlib.CategoryTheory.LiftingProperties.Adjunction


open scoped unitInterval Topology Topology.Homotopy TopCat CategoryTheory

universe u

variable {n : ℕ}
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ x₂ : X}

namespace GenLoop

/-- A level homotopy along a path `p` is a continuous function `H : I × (I^ Fin n) → X`
such that `H ⟨t, y⟩ = p t` for all `y ∈ ∂I^n`.
Note: cannot extend `HomotopyWith` because it would require intermediate maps satisfy
a predicate that does not depend on `t`. -/
structure LevelHomotopy (f₀ : Ω^ (Fin n) X x₀) (f₁ : Ω^ (Fin n) X x₁) (p : Path x₀ x₁)
    extends ContinuousMap.Homotopy f₀.val f₁.val where
  prop' : ∀ t, ∀ y ∈ ∂I^n, toFun ⟨t, y⟩ = p t


namespace LevelHomotopy

variable {f₀ g₀ : Ω^ (Fin n) X x₀} {f₁ : Ω^ (Fin n) X x₁} {f₂ : Ω^ (Fin n) X x₂}
variable {p : Path x₀ x₁} {q : Path x₁ x₂}

/-- A level homotopy along the constant path -/
noncomputable def refl_of_GenLoop_homotopic (H : GenLoop.Homotopic f₀ g₀) :
    LevelHomotopy f₀ g₀ (Path.refl _) where
  toHomotopy := H.some.toHomotopy
  prop' t y hy := by
    simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.Homotopy.coe_toContinuousMap,
      ContinuousMap.HomotopyWith.coe_toHomotopy, Path.refl_apply]
    have := H.some.prop' t y hy
    simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.Homotopy.coe_toContinuousMap,
      ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.coe_mk] at this
    rw [this, f₀.property y hy]

/-- The reverse of a level homotopy along `p`,
as a level homotopy along the reversed path `p.symm` -/
def symm (L : LevelHomotopy f₀ f₁ p) : LevelHomotopy f₁ f₀ p.symm where
  toHomotopy := L.toHomotopy.symm
  prop' t y hy := L.prop' (σ t) y hy

/-- The concatenation of two level homotopies -/
noncomputable def trans (K : LevelHomotopy f₀ f₁ p) (L : LevelHomotopy f₁ f₂ q) :
    LevelHomotopy f₀ f₂ (p.trans q) where
  toHomotopy := K.toHomotopy.trans L.toHomotopy
  prop' t y hy := by
    simp only [ContinuousMap.Homotopy.trans, one_div, ContinuousMap.toFun_eq_coe,
      ContinuousMap.coe_mk, Path.trans, Path.coe_mk_mk, Function.comp_apply]
    by_cases ht : t ≤ (2⁻¹ : ℝ)
    all_goals simp only [ht, ↓reduceIte,
      ContinuousMap.Homotopy.extend, ContinuousMap.coe_IccExtend, Path.extend]
    · have t_mem : 2 * t.val ∈ I := ⟨by linarith only [t.property.left], by linarith only [ht]⟩
      simp only [Set.IccExtend_of_mem _ _ t_mem, ContinuousMap.Homotopy.curry_apply,
        ContinuousMap.coe_mk]
      exact K.prop' ⟨2 * t, t_mem⟩ y hy
    · have t_mem : 2 * t.val - 1 ∈ I := ⟨by linarith only [ht], by linarith only [t.property.right]⟩
      simp only [Set.IccExtend_of_mem _ _ t_mem, ContinuousMap.Homotopy.curry_apply,
        ContinuousMap.coe_mk]
      exact L.prop' ⟨2 * t - 1, t_mem⟩ y hy

/-- A level homotopy whose intermediate maps are constant `GenLoop`s -/
def const_loops : LevelHomotopy (@const (Fin n) _ _ _) const p where
  toContinuousMap := ⟨fun ⟨t, y⟩ ↦ p t, by fun_prop⟩
  map_zero_left y := by simp only [Path.source, const, ContinuousMap.const_apply]
  map_one_left y := by simp only [Path.target, const, ContinuousMap.const_apply]
  prop' t y hy := rfl

/-- Given a level homotopy from `f₀` to `f₁`,
produce a level homotopy from `g ∘ f₀` to `g ∘ f₁`. -/
def map (g : C(X, Y)) (L : LevelHomotopy f₀ f₁ p) :
    LevelHomotopy (GenLoop.inducedMap n x₀ g f₀) (GenLoop.inducedMap n x₁ g f₁)
      (p.map g.continuous) where
  toHomotopy := (ContinuousMap.Homotopy.refl g).comp L.toHomotopy
  prop' t y hy := by
    simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.Homotopy.coe_toContinuousMap, Path.map_coe,
      Function.comp_apply]
    change ((ContinuousMap.Homotopy.refl g).comp L.toHomotopy) (t, y) = _
    simp only [ContinuousMap.Homotopy.comp_apply, ContinuousMap.Homotopy.refl_apply]
    congr 1
    exact L.prop' t y hy

end LevelHomotopy



/-- If `f` and `g` are `GenLoop`s at `x₀` such that there is a `LevelHomotopy` from `f` to `g`
along a null-homotopic loop `p`, then `f` and `g` are homotopic as `GenLoop`s
(i.e., homotopic rel `∂I^n`). -/
theorem homotopic_of_levelHomotopy_along_null_loop {f g : Ω^ (Fin n) X x₀}
    {p : Ω X x₀} (H : LevelHomotopy f g p) (pnull : Path.Homotopic p (Path.refl _)) :
    GenLoop.Homotopic f g := by
  let Fb : C((𝕀 n) × I, X) :=  -- bottom `fun ⟨⟨y⟩, t⟩ ↦ H.toFun ⟨t, y⟩`
    H.toContinuousMap.comp <|
    ((ContinuousMap.id _).prodMap ⟨ULift.down, continuous_uliftDown⟩).comp ContinuousMap.prodSwap
  let Fs : C(((∂𝕀 n) × I) × I, X) := ⟨fun ⟨⟨⟨y⟩, t⟩, s⟩ ↦ pnull.some ⟨s, t⟩, by fun_prop⟩ -- sides
  have : Fb ∘ ((TopCat.cubeBoundaryIncl n).hom.prodMap (ContinuousMap.id I)) =
      Fs ∘ fun x ↦ (x, 0) := by
    funext ⟨y, t⟩
    simp only [ContinuousMap.coe_comp, ContinuousMap.Homotopy.coe_toContinuousMap,
      Function.comp_apply, ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
      ContinuousMap.coe_mk, Fb, Fs]
    change H.toFun (t, ((TopCat.cubeBoundaryIncl n).hom y).down) = (Nonempty.some pnull) (0, t)
    rw [H.prop' t ((TopCat.cubeBoundaryIncl n).hom y).down y.down.property]
    rw [pnull.some.apply_zero _]
    rfl
  obtain ⟨F, ⟨hFb, hFs⟩⟩ := TopCat.cubeBoundaryIncl_prod_unitInterval_hasHEP n X Fb Fs this
  have Fyts_eq_x₀ (y : ∂I^n) (t s : I) (hts : (t = 0 ∨ t = 1) ∨ s = 1) :
      F ((⟨y.val⟩, t), s) = x₀ := by
    have := congrFun hFs ((⟨y⟩, t), s)
    dsimp [TopCat.cubeBoundaryIncl] at this
    change _ = F ((⟨y.val⟩, t), s) at this
    rw [← this]
    dsimp only [Path.coe_toContinuousMap, ContinuousMap.coe_mk, Fs, Fb]
    obtain ht | hs := hts
    · have := pnull.some.prop' s t ht
      simp only [Path.coe_toContinuousMap, ContinuousMap.toFun_eq_coe,
        ContinuousMap.Homotopy.coe_toContinuousMap,
        ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.coe_mk] at this
      rw [this]
      cases ht with
      | inl ht0 => rw [ht0, p.source]
      | inr ht1 => rw [ht1, p.target]
    · rw [hs]
      simp only [ContinuousMap.HomotopyWith.apply_one, Path.coe_toContinuousMap, Path.refl_apply,
        ]
  let Fyts (t s : I) (hts : (t = 0 ∨ t = 1) ∨ s = 1) : Ω^ (Fin n) X x₀ :=
    ⟨⟨fun y ↦ F ((⟨y⟩, t), s), by fun_prop⟩, fun y hy ↦ Fyts_eq_x₀ ⟨y, hy⟩ t s hts⟩
  let Fy01 := Fyts 0 1 (Or.inr rfl)
  let Fy11 := Fyts 1 1 (Or.inr rfl)
  have f_Fy01 : GenLoop.Homotopic f Fy01 := Nonempty.intro
    { toFun := fun ⟨s, y⟩ ↦ Fyts 0 s (Or.inl <| Or.inl rfl) y
      continuous_toFun := by
        change Continuous fun (sy : I × (I^Fin n)) ↦ F ((⟨sy.2⟩, 0), sy.1)
        fun_prop
      map_zero_left y := by
        change F (({ down := y }, 0), 0) = f y
        have h_fb := congrFun hFb (⟨y⟩, 0)
        simp only [Function.comp_apply] at h_fb
        change Fb (⟨y⟩, 0) = F (({ down := y }, 0), 0) at h_fb
        rw [← h_fb]
        change H.toContinuousMap (0, y) = f y
        exact H.apply_zero y
      map_one_left y := by dsimp [Fyts, Fy01]
      prop' s y hy := by
        change F (({ down := y }, 0), s) = f y
        rw [show (f y : X) = x₀ from f.property y hy]
        exact Fyts_eq_x₀ ⟨y, hy⟩ _ _ (Or.inl <| Or.inl rfl) }
  have Fy01_Fy11 : GenLoop.Homotopic Fy01 Fy11 := Nonempty.intro
    { toFun := fun ⟨t, y⟩ ↦ Fyts t 1 (Or.inr rfl) y
      continuous_toFun := by
        change Continuous fun (ty : I × (I^Fin n)) ↦ F ((⟨ty.2⟩, ty.1), 1)
        fun_prop
      map_zero_left y := by
        change F (({ down := y }, 0), 1) = (Fy01 : C(I^Fin n, X)) y
        rfl
      map_one_left y := by
        change F (({ down := y }, 1), 1) = (Fy11 : C(I^Fin n, X)) y
        rfl
      prop' t y hy := by
        change F (({ down := y }, t), 1) = (Fy01 : C(I^Fin n, X)) y
        change F (({ down := y }, t), 1) = F (({ down := y }, 0), 1)
        rw [Fyts_eq_x₀ ⟨y, hy⟩ _ _ (Or.inr rfl),
          ← Fyts_eq_x₀ ⟨y, hy⟩ 0 1 (Or.inr rfl)] }
  have g_Fy11 : GenLoop.Homotopic g Fy11 := Nonempty.intro
    { toFun := fun ⟨s, y⟩ ↦ Fyts 1 s (Or.inl <| Or.inr rfl) y
      continuous_toFun := by
        change Continuous fun (sy : I × (I^Fin n)) ↦ F ((⟨sy.2⟩, 1), sy.1)
        fun_prop
      map_zero_left y := by
        change F (({ down := y }, 1), 0) = g y
        have h_fb := congrFun hFb (⟨y⟩, 1)
        simp only [Function.comp_apply] at h_fb
        change Fb (⟨y⟩, 1) = F (({ down := y }, 1), 0) at h_fb
        rw [← h_fb]
        change H.toContinuousMap (1, y) = g y
        exact H.apply_one y
      map_one_left y := by dsimp [Fyts, Fy11]
      prop' t y hy := by
        change F (({ down := y }, 1), t) = g y
        rw [show (g y : X) = x₀ from g.property y hy]
        exact Fyts_eq_x₀ ⟨y, hy⟩ _ _ (Or.inl <| Or.inr rfl) }
  exact f_Fy01.trans Fy01_Fy11 |>.trans g_Fy11.symm

/-- Suppose `f`, `g` and `h` are `GenLoop`s,
`K` is a level homotopy from `f` to `g` along a path `p`, and
`L` is a level homotopy from `f` to `h` along a path `q`.
If `p` and `q` are homotopic as paths (i.e., rel endpoints),
then `g` and `h` are homotopic as `GenLoop`s (i.e., rel `∂I^n`). -/
theorem homotopic_of_levelHomotopy_along_homotopic_paths
    {f : Ω^ (Fin n) X x₀} {g h : Ω^ (Fin n) X x₁} {p q : Path x₀ x₁}
    (K : LevelHomotopy f g p) (L : LevelHomotopy f h q) (pq : Path.Homotopic p q) :
    GenLoop.Homotopic g h := by
  apply homotopic_of_levelHomotopy_along_null_loop (K.symm.trans L)
  have pq_pp : (p.symm.trans q).Homotopic (p.symm.trans p) :=
    (Path.Homotopic.refl p.symm).hcomp pq.symm
  have pp_0 : (p.symm.trans p).Homotopic (Path.refl _) :=
    Nonempty.intro (Path.Homotopy.reflSymmTrans p).symm
  exact pq_pp.trans pp_0


/-- `ChangeBasePt` -/
structure ChangeBasePt (f₀ : Ω^ (Fin n) X x₀) (p : Path x₀ x₁) where
  /-- `res` -/
  res : Ω^ (Fin n) X x₁
  /-- `levelHomotopy` -/
  levelHomotopy : LevelHomotopy f₀ res p

namespace ChangeBasePt

/-- `get` -/
noncomputable def get
    (f₀ : Ω^ (Fin n) X x₀) (p : Path x₀ x₁) : ChangeBasePt f₀ p := by
  let f₀' : C(𝕀 n, X) := (f₀.val).comp ⟨ULift.down, continuous_uliftDown⟩
  let h : C((∂𝕀 n) × I, X) := ⟨fun ⟨_, t⟩ ↦ p t, by fun_prop⟩
  have hep := TopCat.cubeBoundaryIncl_hasHEP n X f₀' h
  have : f₀' ∘ (TopCat.cubeBoundaryIncl n).hom = h ∘ fun x ↦ (x, 0) := by
    funext ⟨y, hy⟩
    simp only [Function.comp_apply, ContinuousMap.coe_mk, Path.source, h]
    exact f₀.property y hy
  let H' := Classical.choose (hep this)
  have H'_spec := Classical.choose_spec (hep this)
  constructor
  case res => exact
    ⟨ ⟨fun y ↦ H' ⟨⟨y⟩, 1⟩, by fun_prop⟩,  -- include to the top face, then apply `H'`
      fun y hy ↦ by  -- f₁ is a `GenLoop`
        change H' ⟨(TopCat.cubeBoundaryIncl n) ⟨y, hy⟩, 1⟩ = _
        have := congr_fun H'_spec.right ⟨⟨y, hy⟩, 1⟩
        dsimp only [Function.comp_apply, Prod.map_apply, id_eq, h] at this
        rw [← this, ContinuousMap.coe_mk, Path.target] ⟩
  case levelHomotopy => exact
    { toContinuousMap := H'.comp <| ContinuousMap.prodSwap.comp <|
          ContinuousMap.prodMap (ContinuousMap.id _) ⟨ULift.up, continuous_uliftUp⟩
      map_zero_left y := by
        dsimp
        exact (congr_fun H'_spec.left ⟨y⟩).symm
      map_one_left y := by simp
      prop' t y hy := by
        dsimp
        change H' ⟨(TopCat.cubeBoundaryIncl n).hom ⟨y, hy⟩, t⟩ = _
        have := congr_fun H'_spec.right ⟨⟨y, hy⟩, t⟩
        dsimp only [Function.comp_apply, Prod.map_apply, id_eq] at this
        rw [← this]
        dsimp only [ContinuousMap.coe_mk, h] }

end ChangeBasePt

/-- `«term(_#_)»` -/
scoped[Topology.Homotopy] notation "(" p " # " f₀ ")" =>
  GenLoop.ChangeBasePt.res (GenLoop.ChangeBasePt.get f₀ p)
/-- `«term(_#~_)»` -/
scoped[Topology.Homotopy] notation "(" p " #~ " f₀ ")" =>
  GenLoop.ChangeBasePt.levelHomotopy (GenLoop.ChangeBasePt.get f₀ p)

namespace ChangeBasePt

/-- If `p` and `q` are homotopic paths (rel endpoints), then `p# = q#`
in the sense that `(p # f)` and `(q # f)` are homotopic `GenLoop`s for all `f`.
See also `HomotopyGroup.changeBasePt.eq_of_path_homotopic`. -/
lemma homotopic_of_path_homotopic {f₀ : Ω^ (Fin n) X x₀}
    {p q : Path x₀ x₁} (pq : Path.Homotopic p q) :
    GenLoop.Homotopic (p # f₀) (q # f₀) :=
  homotopic_of_levelHomotopy_along_homotopic_paths (p #~ f₀) (q #~ f₀) pq

/-- `p#` sends (the homotopy class of) the const loop at `x₀` to
(the homotopy class of) the const loop at `x₁`. -/
lemma apply_const {p : Path x₀ x₁} :
    GenLoop.Homotopic (p # const) <| @const (Fin n) _ _ _ :=
  homotopic_of_levelHomotopy_along_homotopic_paths
    (p #~ const) GenLoop.LevelHomotopy.const_loops (Path.Homotopic.refl p)

/-- Changing base point along the constant path `Path.refl _` does nothing. -/
lemma along_const {f : Ω^ (Fin n) X x₀} :
    GenLoop.Homotopic f (Path.refl _ # f) :=
  Nonempty.intro
    { toHomotopy := (Path.refl _ #~ f).toHomotopy
      prop' t y hy := by
        change (_ #~ _).toFun _ = _
        rw [(Path.refl _ #~ f).prop' t y hy, f.property y hy]
        rfl }

/-- Changing base point along a null-homotopic loop `p` does nothing. -/
lemma along_null_path {f : Ω^ (Fin n) X x₀}
    {p : Ω X x₀} (pnull : Path.Homotopic p (Path.refl _)) :
    GenLoop.Homotopic f (p # f) :=
  along_const.trans <| homotopic_of_path_homotopic pnull.symm

/-- `(q # (p # f)) ≈ (p.trans q # f)` -/
lemma trans {p : Path x₀ x₁} {q : Path x₁ x₂} {f : Ω^ (Fin n) X x₀} :
    GenLoop.Homotopic (q # (p # f)) (p.trans q # f) :=
  homotopic_of_levelHomotopy_along_homotopic_paths
    (GenLoop.LevelHomotopy.trans (p #~ f) (q #~ (p # f))) (p.trans q #~ f) (Path.Homotopic.refl _)

/-- `(q # (p # f)) ≈ (r # f)` if `r ≈ p.trans q`. -/
lemma trans' {p : Path x₀ x₁} {q : Path x₁ x₂} {r : Path x₀ x₂} {f : Ω^ (Fin n) X x₀}
    (r_pq : Path.Homotopic r (p.trans q)) :
    GenLoop.Homotopic (q # (p # f)) (r # f) :=
  trans.trans <| homotopic_of_path_homotopic r_pq.symm

end ChangeBasePt

/-- `ChangeBasePt` commutes with the induced map, up to homotopy:
```
Ω^ (Fin n) X x₀  ------ f* ---->  Ω^ (Fin n) Y (f x₀)
      |                                    |
      p#                                (f ∘ p)#
      |                                    |
      v                                    v
Ω^ (Fin n) X x₁  ------ f* ---->  Ω^ (Fin n) Y (f x₁)
```
See also `HomotopyGroup.map_changeBasePt_eq_changeBasePt_map`.
-/
lemma map_changeBasePt_homotopic_changeBasePt_map
    {p : Path x₀ x₁} {α : Ω^ (Fin n) X x₀} (f : C(X, Y)) :
    GenLoop.Homotopic (GenLoop.inducedMap n x₁ f (p # α))
      (p.map f.continuous # GenLoop.inducedMap n x₀ f α) :=
  homotopic_of_levelHomotopy_along_homotopic_paths (GenLoop.LevelHomotopy.map f (p #~ α))
    (_ #~ _) (Path.Homotopic.refl _)

end GenLoop



/-- Transport an element of `π_ n X (p 0)` along the path `p`. -/
noncomputable def HomotopyGroup.changeBasePt (n : ℕ) (p : Path x₀ x₁) :
    π_ n X x₀ → π_ n X x₁ := by
  apply Quotient.map fun f₀ ↦ (p # f₀)
  intro f₀ g₀ eq₀
  let Hf := (p #~ f₀)
  let Hg := (p #~ g₀)
  let L := GenLoop.LevelHomotopy.refl_of_GenLoop_homotopic eq₀
  apply GenLoop.homotopic_of_levelHomotopy_along_homotopic_paths Hf (L.trans Hg)
  exact Nonempty.intro <| (Path.Homotopy.reflTrans _).symm

/-- `changeBasePt` -/
noncomputable def FundamentalGroupoid.changeBasePt (n : ℕ) : FundamentalGroupoid X ⥤ Pointed where
  obj x₀ := Pointed.of (default : π_ n X x₀.as)
  map {x₀ x₁} p :=
    { toFun := HomotopyGroup.changeBasePt n (Quotient.out p)
      map_point := Quotient.sound GenLoop.ChangeBasePt.apply_const }
  map_id x₀ := by
    congr 1
    ext f
    rw [id_eq]
    change HomotopyGroup.changeBasePt n ⟦Path.refl x₀.as⟧.out _ = _
    rw [← Quotient.out_eq f]
    unfold HomotopyGroup.changeBasePt
    rw [Quotient.map_mk]
    apply Eq.symm
    apply Quotient.eq_iff_equiv.mpr
    apply GenLoop.ChangeBasePt.along_null_path  -- the key
    change (Path.Homotopic.setoid _ _) _ _
    apply Quotient.mk_out
  map_comp {x₀ x₁ x₂} p q := by
    congr 1
    ext f
    dsimp only [Function.comp_apply]
    rw [← Quotient.out_eq f]
    unfold HomotopyGroup.changeBasePt
    iterate 3 (rw [Quotient.map_mk])
    apply Eq.symm
    apply Quotient.eq_iff_equiv.mpr
    apply GenLoop.ChangeBasePt.trans'  -- the key
    change (Path.Homotopic.Quotient.trans _ _).out.Homotopic _
    conv_lhs => pattern p; rw [← Quotient.out_eq p]
    conv_lhs => pattern q; rw [← Quotient.out_eq q]
    have hpq : Path.Homotopic.Quotient.trans (⟦Quotient.out p⟧ : Path.Homotopic.Quotient _ _)
        ⟦Quotient.out q⟧ = ⟦(Quotient.out p).trans (Quotient.out q)⟧ :=
      (Path.Homotopic.Quotient.mk_trans _ _).symm
    rw [hpq]
    change (Path.Homotopic.setoid _ _) _ _
    apply Quotient.mk_out

instance FundamentalGroupoid.isIso_changeBasePt_map
    {x₀ x₁ : FundamentalGroupoid X} (p : x₀ ⟶ x₁) :
    CategoryTheory.IsIso ((FundamentalGroupoid.changeBasePt n).map p) := by
  -- have : CategoryTheory.IsIso p := by infer_instance  -- CategoryTheory.IsIso.of_groupoid
  infer_instance



namespace HomotopyGroup

open CategoryTheory
open scoped ContinuousMap  -- notation `≃ₕ`

/-- If `p` and `q` are homotopic paths (rel endpoints), then `p#` and `q#` are equal
as maps from `π_ n X x₀` to `π_ n X x₁`.
See also `GenLoop.ChangeBasePt.homotopic_of_path_homotopic`. -/
lemma changeBasePt_eq_of_path_homotopic
    {p q : Path x₀ x₁} (pq : Path.Homotopic p q) :
    HomotopyGroup.changeBasePt n p = HomotopyGroup.changeBasePt n q := by
  ext f
  rw [← Quotient.out_eq f]
  apply Quotient.sound
  exact GenLoop.ChangeBasePt.homotopic_of_path_homotopic pq

/-- Change of base point along the path `p`,
as a morphism $F(·, x₀)_{#} : π_n(X, f(x₀)) → π_n(Y, g(x₀))$ in the category `Pointed` -/
noncomputable abbrev pointedHomOfPath (n : ℕ) (p : Path x₀ x₁) :
    Pointed.of (default : π_ n X x₀) ⟶ Pointed.of (default : π_ n X x₁) where
  toFun := changeBasePt n p
  map_point := Quotient.sound GenLoop.ChangeBasePt.apply_const

instance isIso_pointedHomOfPath (n : ℕ) (p : Path x₀ x₁) :
    IsIso (pointedHomOfPath n p) := by
  have : (FundamentalGroupoid.changeBasePt n).map ⟦p⟧ = (pointedHomOfPath n p) := by
    unfold FundamentalGroupoid.changeBasePt pointedHomOfPath
    dsimp
    congr 1
    apply HomotopyGroup.changeBasePt_eq_of_path_homotopic
    change (Path.Homotopic.setoid _ _) _ _
    apply Quotient.mk_out
  rw [← this]
  exact FundamentalGroupoid.isIso_changeBasePt_map ⟦p⟧

lemma bijective_changeBasePt (n : ℕ) (p : Path x₀ x₁) :
    Function.Bijective (changeBasePt n p) := by
  rw [(by rfl : changeBasePt n p = ConcreteCategory.hom (pointedHomOfPath n p))]
  apply (Pointed.isIso_iff_bijective _).mp
  apply isIso_pointedHomOfPath

/-- `ChangeBasePt` commutes with the induced map:
```
π_ n X x₀  ------ f* ---->  π_ n Y (f x₀)
    |                            |
    p#                        (f ∘ p)#
    |                            |
    v                            v
π_ n X x₁  ------ f* ---->  π_ n Y (f x₁)
```
See also `GenLoop.map_changeBasePt_homotopic_changeBasePt_map`. -/
lemma pointedHomOfPath_inducedPointedHom_eq_inducedPointedHom_pointedHomOfPath
    (n : ℕ) (p : Path x₀ x₁) (f : C(X, Y)) :
    pointedHomOfPath n p ≫ inducedPointedHom n x₁ f =
    inducedPointedHom n x₀ f ≫ pointedHomOfPath n (p.map f.continuous) := by
  ext α
  rw [← Quotient.out_eq α]
  apply Quotient.sound
  exact GenLoop.map_changeBasePt_homotopic_changeBasePt_map f

lemma inducedPointedHom_eq_of_path
    (n : ℕ) (p : Path x₀ x₁) (f : C(X, Y)) :
    inducedPointedHom n x₀ f = pointedHomOfPath n p ≫ inducedPointedHom n x₁ f ≫
      inv (pointedHomOfPath n (p.map f.continuous)) := by
  rw [← Category.assoc, pointedHomOfPath_inducedPointedHom_eq_inducedPointedHom_pointedHomOfPath]
  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem inducedPointedHom_comp_pointedHomOfHomotopy_eq
    (n : ℕ) (x₀ : X) {f g : C(X, X)} (F : f.Homotopy g) :
    inducedPointedHom n x₀ f ≫ pointedHomOfPath n (F.evalAt x₀) =
    inducedPointedHom n x₀ g := by
  ext α
  dsimp only at α
  dsimp only [inducedPointedHom, pointedHomOfPath, functorToPointed]
  change changeBasePt n (F.evalAt x₀) ((functorToType n).map (PointedTopCat.ofHom f x₀) α) =
    (functorToType n).map (PointedTopCat.ofHom g x₀) α
  simp only [functorToType, CategoryTheory.Under.mk_right]
  rw [← Quotient.out_eq α]
  apply Quotient.sound
  simp only [GenLoop.inducedMap', CategoryTheory.Under.mk_right, CategoryTheory.Under.homMk_right,
    TopCat.hom_ofHom]
  generalize_proofs fα_mem gα_mem
  let fα : Ω^ (Fin n) X (f x₀) := ⟨f.comp α.out, fα_mem⟩
  let gα : Ω^ (Fin n) X (g x₀) := ⟨g.comp α.out, gα_mem⟩
  have L : GenLoop.LevelHomotopy fα gα (F.evalAt x₀) :=  -- (t, y) ↦ F(t, α(y))
    { toContinuousMap := F.toContinuousMap.comp <| (ContinuousMap.id _).prodMap α.out
      map_zero_left y := by simp [fα]
      map_one_left y := by simp [gα]
      prop' t y hy := by
        simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply,
          ContinuousMap.prodMap_apply, ContinuousMap.coe_id, GenLoop.coe_coe, Prod.map_apply,
          id_eq, ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.evalAt,
          Path.coe_mk', ContinuousMap.coe_mk]
        rw [show ((Quotient.out α) y : X) = x₀ from α.out.prop y hy] }
  apply GenLoop.homotopic_of_levelHomotopy_along_homotopic_paths (F.evalAt x₀ #~ fα) L
  exact Path.Homotopic.refl _

lemma injective_toFun_surjective_invFun_of_homotopyEquiv (n : ℕ) (x₀ : X) (E : X ≃ₕ Y) :
    Function.Injective (inducedPointedHom n x₀ E.toFun).toFun ∧
    Function.Surjective (inducedPointedHom n (E.toFun x₀) E.invFun).toFun := by
  have gf_ch_eq_id := inducedPointedHom_comp_pointedHomOfHomotopy_eq n x₀ E.left_inv.some
  have bgf : Function.Bijective (inducedPointedHom n x₀ (E.invFun.comp E.toFun)) := by
    apply (Pointed.isIso_iff_bijective _).mp
    have iso_gf : IsIso (inducedPointedHom n x₀ (E.invFun.comp E.toFun)) :=
      IsIso.of_isIso_fac_right gf_ch_eq_id  -- using `isIso_inducedPointedHom_id`
    infer_instance  -- using `iso_gf` and `CategoryTheory.hom_isIso`
  have : (inducedPointedHom n x₀ (E.invFun.comp E.toFun)).toFun =
      (inducedPointedHom n _ E.invFun).toFun ∘ (inducedPointedHom n _ E.toFun).toFun := by
    rw [inducedPointedHom_comp n x₀ E.toFun E.invFun]
    simp only [ContinuousMap.comp_apply, ContinuousMap.HomotopyEquiv.coe_invFun,
      Pointed.Hom.comp_toFun']
  replace bgf : Function.Bijective <|
      (inducedPointedHom n _ E.invFun).toFun ∘ (inducedPointedHom n x₀ E.toFun).toFun := by
    rw [← this]
    exact bgf
  exact ⟨Function.Injective.of_comp bgf.injective, Function.Surjective.of_comp bgf.surjective⟩

theorem isIso_inducedPointedHom_of_isHomotopyEquiv (n : ℕ) (x₀ : X) (f : C(X, Y))
    (hf : IsHomotopyEquiv f) : IsIso (inducedPointedHom n x₀ f) := by
  obtain ⟨E, Ef⟩ := hf
  -- have : f = E.toFun := Ef.symm
  -- let g := E.invFun
  have inj_f : Function.Injective (inducedPointedHom n x₀ f).toFun := by
    rw [← Ef]
    exact (injective_toFun_surjective_invFun_of_homotopyEquiv n x₀ E).left
  have surj_f : Function.Surjective (inducedPointedHom n x₀ f).toFun := by
    -- In general, `g (f x₀) ≠ x₀`, hence `inducedPointedHom_eq_of_path` is necessary.
    rw [← Ef]
    have surj := injective_toFun_surjective_invFun_of_homotopyEquiv n
        (E.symm.invFun x₀) E.symm |>.right
    rw [(by rfl : E.symm.invFun = E.toFun)] at surj
    rw [show E.symm.toFun (E.toFun x₀) = (E.invFun.comp E.toFun) x₀ from rfl] at surj
    rw [inducedPointedHom_eq_of_path n (E.left_inv.some.evalAt x₀) E.toFun] at surj
    have {A B C D : Type u} {f : A → B} {g : B → C} {h : C → D}
        (shgf : Function.Surjective (h ∘ g ∘ f))
        (bh : Function.Bijective h) (bf : Function.Bijective f) : Function.Surjective g :=
      Function.Surjective.of_comp <| (Function.Surjective.of_comp_iff' bh (g ∘ f)).mp shgf
    refine this surj ?_ ?_
    · apply (Pointed.isIso_iff_bijective _).mp
      infer_instance
    · apply bijective_changeBasePt
  exact (Pointed.isIso_iff_bijective _).mpr ⟨inj_f, surj_f⟩

theorem isIso_inducedPointedHom'_of_isHomotopyEquiv
    (n : ℕ) {X Y : TopCat.{u}} (x₀ : X) (f : X ⟶ Y)
    (hf : IsHomotopyEquiv f.hom) : IsIso (inducedPointedHom' n x₀ f) := by
  rw [inducedPointedHom'_eq_inducedPointedHom]
  apply isIso_inducedPointedHom_of_isHomotopyEquiv
  exact hf

theorem isIso_inducedPointedHom'_of_isHomeomorph
    (n : ℕ) {X Y : TopCat.{u}} (x₀ : X) (f : X ⟶ Y)
    (hf : IsHomeomorph f.hom) : IsIso (inducedPointedHom' n x₀ f) := by
  let eq := Homeomorph.toHomotopyEquiv (hf.homeomorph)
  apply isIso_inducedPointedHom_of_isHomotopyEquiv
  rw [(by rfl : f.hom' = eq.toFun)]
  use eq

end HomotopyGroup
