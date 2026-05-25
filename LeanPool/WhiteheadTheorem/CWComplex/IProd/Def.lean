/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

-- import WhiteheadTheorem.Shapes.Cube
import LeanPool.WhiteheadTheorem.CWComplex.Basic
import LeanPool.WhiteheadTheorem.Auxiliary
import LeanPool.WhiteheadTheorem.Exponential
import LeanPool.WhiteheadTheorem.Shapes.DiskHomeoCube
import LeanPool.WhiteheadTheorem.Shapes.CubeBoundaryMap
import LeanPool.WhiteheadTheorem.Shapes.Maps
import LeanPool.WhiteheadTheorem.Shapes.Pushout
import Mathlib.CategoryTheory.Comma.Arrow

/-!
For every CW-complex `X`, this file constructs a relative CW-complex `X.IProd`
homeomorphic to `I × X`, where `I` is the unit interval.
The $(-1)$-skeleton of `X.IProd` is homeomorphic to `{0, 1} × X`.
-/


open CategoryTheory unitInterval TopCat
-- open scoped Topology Topology.Homotopy  -- `∂I^1` and `I^ Fin 1`


universe u

variable (X : CWComplex.{u})


noncomputable section

namespace CWComplex

/-- The inclusion map from `{0, 1} × X` to `I × X` -/
abbrev zeroOneProdInclIProd :
    TopCat.of (zeroOne × X.toTopCat) ⟶ TopCat.of (I × X.toTopCat) :=
  ofHom <| unitInterval.zeroOneIncl.prodMap (ContinuousMap.id _)

namespace IProd

abbrev l (n : ℕ) := ofHom <| (ContinuousMap.id zeroOne).prodMap (X.skIncl n).hom
abbrev r (n : ℕ) := ofHom <| zeroOneIncl.prodMap <| ContinuousMap.id <| X.sk n
abbrev xskl (n : ℕ) := Limits.Sigma.desc (X.attachCells n).attachMaps
abbrev xskr (n : ℕ) := Limits.Sigma.map fun (_ : (X.attachCells n).cells) ↦ diskBoundaryIncl n

/--
```
                    l X n
{0, 1} × (X.sk n) ------→ {0, 1} × X
       |                       |
r X n  |             pushout   |
       ↓                       ↓
     I × (X.sk n) ----→ X.IProd.sk (n + 1)
```
`X.IProd.sk 0 = {0, 1} × X ≅ X.IProd.sk 1`
-/
noncomputable def sk (n : ℕ) : TopCat.{u} :=
  match n with
  | 0 => TopCat.of (zeroOne × X.toTopCat)
  | n + 1 => Limits.pushout (IProd.l X n) (IProd.r X n)

def skZeroIsoSkOne : CWComplex.IProd.sk X 0 ≅ CWComplex.IProd.sk X 1 :=
  have : IsIso <| ofHom <| zeroOneIncl.prodMap <| ContinuousMap.id <| X.sk 0 := by
    have := X.isEmpty_sk_zero
    infer_instance  -- TopCat.isIso_of_isEmpty
  haveI : IsIso (r X 0) := this
  haveI : IsIso (Limits.pushout.inl (l X 0) (r X 0)) :=
    Limits.pushout_inl_iso_of_right_iso _ _
  asIso <| Limits.pushout.inl (l X 0) (r X 0)  -- Limits.pushout_inl_iso_of_right_iso

end IProd


def cubeInclToSk {n : ℕ} (α : (X.attachCells n).cells) : 𝕀 n ⟶ X.sk (n + 1) :=
  (diskPair.homeoCubePairULift n).inv.right ≫
  Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr .. ≫ (X.attachCells n).isoPushout.inv

def cubeIncl {n : ℕ} (α : (X.attachCells n).cells) : 𝕀 n ⟶ X :=
  X.cubeInclToSk α ≫ X.skIncl (n + 1)

def cubeAtt {n : ℕ} (α : (X.attachCells n).cells) : ∂𝕀 n ⟶ X.sk n :=
  (diskPair.homeoCubePairULift n).inv.left ≫ (X.attachCells n).attachMaps α


namespace IProd

def cubeAttBotOrTop {n : ℕ} (α : (X.attachCells n).cells) (t : zeroOne) :
    𝕀 n ⟶ IProd.sk X (n + 1) :=  -- bottom face of `∂𝕀 (n + 1)`
  X.cubeIncl α ≫
  ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩ ≫  -- X ⟶ {0, 1} × X
  Limits.pushout.inl ..

def cubeAttSides {n : ℕ} (α : (X.attachCells n).cells) :
    TopCat.of (I × ∂𝕀 n) ⟶ IProd.sk X (n + 1) :=  -- sides of `∂𝕀 (n + 1)`
  ofHom ((ContinuousMap.id I).prodMap (X.cubeAtt α).hom) ≫  -- of (I × ∂𝕀 n) ⟶ of (I × (X.sk n))
  Limits.pushout.inr ..

lemma cubeAtt_compatible {n : ℕ} (α : (X.attachCells n).cells) (t : zeroOne) :
    ∀ (y : ∂𝕀 n), (IProd.cubeAttBotOrTop X α t) ((cubeBoundaryIncl n) y) =
      (IProd.cubeAttSides X α) ⟨zeroOneIncl t, y⟩ := fun y ↦ by
  let iX : X.toTopCat ⟶ TopCat.of (zeroOne × X.toTopCat) := ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩
  let isk : X.sk n ⟶ TopCat.of (zeroOne × (X.sk n)) := ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩
  change ((diskPair.homeoCubePairULift n).inv.left ≫ diskBoundaryIncl n ≫
      Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr .. ≫
      (X.attachCells n).isoPushout.inv ≫ X.skIncl _ ≫ iX ≫ Limits.pushout.inl .. ) y =
    ((diskPair.homeoCubePairULift n).inv.left ≫ (X.attachCells n).attachMaps α ≫
      isk ≫ r X n ≫ Limits.pushout.inr .. ) y
  have h := (X.attachCells n).w_cell α
  unfold RelCWComplex.AttachGeneralizedCells.pushout_inr at h
  unfold RelCWComplex.AttachGeneralizedCells.pushout_inl at h
  -- `reassoc_of% h` doesn't pattern-match the original; use a direct `have` then rewrite.
  have h' : Arrow.Hom.left (diskPair.homeoCubePairULift n).inv ≫ diskBoundaryIncl n ≫
      Limits.Sigma.ι (fun x ↦ 𝔻 n) α ≫
        Limits.pushout.inr (Limits.Sigma.desc (X.attachCells n).attachMaps)
          (Limits.Sigma.map fun x ↦ diskBoundaryIncl n) ≫
        (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫ iX ≫
          Limits.pushout.inl (l X n) (r X n) =
      Arrow.Hom.left (diskPair.homeoCubePairULift n).inv ≫ (X.attachCells n).attachMaps α ≫
        Limits.pushout.inl (Limits.Sigma.desc (X.attachCells n).attachMaps)
          (Limits.Sigma.map fun x ↦ diskBoundaryIncl n) ≫
        (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫ iX ≫
          Limits.pushout.inl (l X n) (r X n) := by
    have hr := h =≫ (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫ iX ≫
      Limits.pushout.inl (l X n) (r X n)
    have hr2 := Arrow.Hom.left (diskPair.homeoCubePairULift n).inv ≫= hr
    simp only [Category.assoc] at hr2 ⊢
    exact hr2
  rw [h']
  congr 4
  -- TODO: refactor
  -- have : X.skIncl n ≫ iX = isk ≫ l X n := rfl
  -- have : X.skIncl n =
  --   (X.attachCells n).pushout_inl ≫ (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) := sorry
  have : (X.attachCells n).pushout_inl ≫ (X.attachCells n).isoPushout.inv ≫
      X.skIncl (n + 1) ≫ iX = isk ≫ l X n := by
    ext x
    · simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
        Limits.colimit.cocone_x, ContinuousMap.comp_assoc, isk, iX]
    · simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
        Limits.colimit.cocone_x, ContinuousMap.comp_assoc, isk, iX]
      change (X.skInclSucc _ ≫ X.skIncl _) x = (X.skIncl _) x
      rw [X.skInclSucc_skIncl_eq]
  change (_ ≫ _ ≫ _ ≫ iX) ≫ _ = _
  rw [this, Category.assoc, Limits.pushout.condition]

def attachMaps {n : ℕ} (α : (X.attachCells n).cells) : ∂𝔻 (n + 1) ⟶ IProd.sk X (n + 1) :=
  (diskPair.homeoCubePairULift (n + 1)).hom.left ≫
    cubeBoundary.mapOfBotTopSides
      (IProd.cubeAttBotOrTop X α) (IProd.cubeAttSides X α) (IProd.cubeAtt_compatible X α)

/-- Note:
Each $n$-cell of `X` corresponds to an $(n + 1)$-cell of `X.IProd`.
The latter cell is attached to `IProd.sk X (n + 1)`, which is of dimension $n$.
`X.IProd` has no `0`-cells. -/
def sigmaDisksInclToSk (n : ℕ) :
    (∐ fun (_ : (X.attachCells n).cells) ↦ 𝔻 (n + 1)) ⟶ IProd.sk X (n + 1 + 1) :=
  (Limits.Sigma.desc
    fun α ↦ (diskPair.homeoCubePairULift _).hom.right ≫ cubeSplitAtLast.hom ≫
      ofHom ((ContinuousMap.id I).prodMap (X.cubeInclToSk α).hom) )
  ≫ Limits.pushout.inr ..

def skInclSucc (n : ℕ) : IProd.sk X (n + 1) ⟶ IProd.sk X (n + 1 + 1) :=
  let il : TopCat.of (zeroOne × X.toTopCat) ⟶ IProd.sk X (n + 1 + 1) := Limits.pushout.inl ..
  let ir : TopCat.of (I × X.sk n) ⟶ IProd.sk X (n + 1 + 1) :=
    ofHom ((ContinuousMap.id I).prodMap (X.skInclSucc _).hom) ≫ Limits.pushout.inr ..
  Limits.pushout.desc il ir <| by
    ext ⟨t, x⟩
    simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
      ContinuousMap.coe_id, Prod.map_apply, id_eq, ContinuousMap.coe_mk]
    change _ = (r X (n + 1) ≫ Limits.pushout.inr ..) ⟨t, X.skInclSucc _ x⟩
    have : il ⟨t, (X.skIncl n) x⟩ =
        (l X (n + 1) ≫ Limits.pushout.inl ..) ⟨t, X.skInclSucc _ x⟩ := by
      simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
        ContinuousMap.coe_id, Prod.map_apply, id_eq, il]
      congr 2
      rw [← X.skInclSucc_skIncl_eq]; rfl
    rw [this, Limits.pushout.condition]

@[reassoc]
lemma inl_skInclSucc {n : ℕ} :
    Limits.pushout.inl (l X n) (r X n) ≫ IProd.skInclSucc X n =
    Limits.pushout.inl (l X (n + 1)) (r X (n + 1)) := by
  unfold IProd.skInclSucc
  exact Limits.pushout.inl_desc _ _ _

@[reassoc]
lemma inr_skInclSucc {n : ℕ} :
    Limits.pushout.inr (l X n) (r X n) ≫ IProd.skInclSucc X n =
    ofHom ((ContinuousMap.id I).prodMap (X.skInclSucc _).hom) ≫
      Limits.pushout.inr (l X (n + 1)) (r X (n + 1)) := by
  unfold IProd.skInclSucc
  exact Limits.pushout.inr_desc _ _ _

/--
```
∐ ∂𝔻 (n + 1) -----------→ IProd.sk X (n + 1)
    |                             |
    |                             |
    ↓                             ↓
∐ 𝔻 (n + 1) ------------→ IProd.sk X (n + 1 + 1)
```
-/
def commSqSkSk (n : ℕ) :
    CommSq
      (Limits.Sigma.desc (IProd.attachMaps X))
      (Limits.Sigma.map fun _ ↦ diskBoundaryIncl (n + 1))
      (IProd.skInclSucc X n)
      (IProd.sigmaDisksInclToSk X n) :=
  ⟨by
    let iX t : X.toTopCat ⟶ TopCat.of (zeroOne × X.toTopCat) := ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩
    let isk t : X.sk (n + 1) ⟶ TopCat.of (zeroOne × (X.sk _)) := ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩
    have cv := cubeBoundary.botTopSidesCover_cover.{u} n
    have cl := cubeBoundary.botTopSidesCover_closed.{u} n
    ext α x
    simp only [Limits.colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Limits.Cofan.mk_pt,
      Limits.Cofan.mk_ι_app, TopCat.hom_comp, ContinuousMap.comp_apply, Limits.ι_colimMap_assoc,
      Discrete.natTrans_app, ContinuousMap.comp_assoc]
    -- `attribute [reassoc] Limits.Sigma.ι_desc` or `rw [reassoc_of% Limits.Sigma.ι_desc]`
    change _ = ((Limits.Sigma.ι (fun _ ↦ 𝔻 (n + 1)) α ≫ Limits.Sigma.desc _) ≫ _) _
    rw [Limits.Sigma.ι_desc]
    change ((diskPair.homeoCubePairULift (n + 1)).hom.left ≫
        cubeBoundary.mapOfBotTopSides _ _ (IProd.cubeAtt_compatible X α) ≫
        skInclSucc X n ) x =
      ((diskPair.homeoCubePairULift (n + 1)).hom.left ≫
        (cubeBoundaryIncl (n + 1)) ≫ cubeSplitAtLast.hom ≫
        ofHom ((ContinuousMap.id I).prodMap (X.cubeInclToSk α).hom) ≫ Limits.pushout.inr .. ) x
    congr 3
    ext y
    obtain ⟨k, hk⟩ := cubeBoundary.botTopSidesCover_cover _ y
    fin_cases k
    all_goals
      change (skInclSucc X n) (ContinuousMap.liftCoverClosed _ _ _ cv cl _) = _
      rw [ContinuousMap.liftCoverClosed_coe' _ _ _ _ _ _ hk]
      obtain ⟨⟨y, hy⟩⟩ := y
      change _ = Limits.pushout.inr (l X (n + 1)) (r X (n + 1))
        ⟨(Cube.splitAtLast y).fst, X.cubeInclToSk α ⟨(Cube.splitAtLast y).snd⟩⟩
    iterate 2  -- bottom and top of the $(n + 1)$-cube
      -- change (skInclSucc X n) ((cubeAttBotOrTop X α) 0 ⟨(Cube.splitAtLast y).snd⟩) = _
      -- have : X.skIncl (n + 1) ≫ iX 0 = isk 0 ≫ l X (n + 1) := rfl
      change (X.cubeInclToSk α ≫ isk _ ≫ l X (n + 1) ≫
          Limits.pushout.inl .. ≫ skInclSucc X n ) ⟨(Cube.splitAtLast y).snd⟩ = _
      rw [skInclSucc, Limits.pushout.inl_desc, Limits.pushout.condition]
      rw [Cube.splitAtLast_fst_eq, hk]; rfl
    · -- sides of the $(n + 1)$-cube
      change (Limits.pushout.inr .. ≫ skInclSucc X n)
        ⟨(Cube.splitAtLast y).fst, X.cubeAtt α ⟨(Cube.splitAtLast y).snd, _⟩⟩ = _
      rw [skInclSucc, Limits.pushout.inr_desc]
      change (ofHom ((ContinuousMap.id I).prodMap (Hom.hom (X.skInclSucc n))) ≫
          Limits.pushout.inr ..)
        ⟨(Cube.splitAtLast y).fst,
          X.cubeAtt α ⟨(Cube.splitAtLast y).snd, _⟩ ⟩ = _
      simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
        ContinuousMap.coe_id, Prod.map_apply, id_eq]
      congr 2
      change (X.cubeAtt α ≫ X.skInclSucc n) _ = _
      unfold CWComplex.cubeAtt CWComplex.cubeInclToSk
      rw [Category.assoc]
      change _ = ((diskPair.homeoCubePairULift n).inv.left ≫ diskBoundaryIncl _ ≫
          Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr .. ≫
            (X.attachCells n).isoPushout.inv )
          ⟨⟨(Cube.splitAtLast y).2, cubeBoundary.splitAtLast_snd_mem_boundary_of_mem_sides hk⟩⟩
      congr 3
      unfold RelCWComplex.skInclSucc RelCWComplex.AttachCells.incl
      change (_ ≫ _) ≫ (X.attachCells n).isoPushout.inv =
        (_ ≫ _ ≫ _) ≫ (X.attachCells n).isoPushout.inv
      congr 1
      rw [(X.attachCells n).attachMaps_apply_eq_ι_desc, Category.assoc]
      rw [Limits.pushout.condition, (X.attachCells n).w_sigma_cells_assoc] ⟩


namespace pushoutSkSk
/-!
Now verify that `commSqSkSk` is a pushout square.
-/

variable (n : ℕ) (Z : Limits.PushoutCocone
  (Limits.Sigma.desc (IProd.attachMaps X))
  (Limits.Sigma.map fun _ ↦ diskBoundaryIncl (n + 1)) )

abbrev l' : X.sk n ⟶ TopCat.of C(I, Z.pt) :=
  ofHom (Limits.pushout.inr (l X n) (r X n) ≫ Z.inl).hom.argSwap.curry
abbrev r' : (∐ fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) ⟶ TopCat.of C(I, Z.pt) :=
  Limits.Sigma.desc fun α ↦
    let Zinr' : TopCat.of (I × (𝕀 n)) ⟶ Z.pt :=
      TopCat.cubeSplitAtLast.inv ≫ (diskPair.homeoCubePairULift _).inv.right ≫
      Limits.Sigma.ι (fun _ ↦ 𝔻 _) α ≫ Z.inr
    (diskPair.homeoCubePairULift n).hom.right ≫ ofHom (ContinuousMap.curry Zinr'.hom.argSwap)

/--
The following square commutes.
```
  ∐ ∂𝔻 n --------→ X.sk n
     |     xskl       |
xskr |                | l'
     ↓      r'        ↓
  ∐ 𝔻 n ---------→ C(I, Z)
```
-/
lemma w' : xskl X n ≫ l' X n Z = xskr X n ≫ r' X n Z := by
  ext α : 1
  simp only [Limits.colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Limits.Cofan.mk_pt,
    Limits.Cofan.mk_ι_app, Limits.ι_colimMap_assoc, Discrete.natTrans_app, xskl, xskr]
  change _ = _ ≫ Limits.Sigma.ι _ α ≫ r' ..
  ext x t
  unfold l' r'
  simp only [ContinuousMap.argSwap, TopCat.hom_comp, ContinuousMap.coe_mk,
    ContinuousMap.comp_assoc, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.curry_apply,
    ContinuousMap.prodSwap_apply, Arrow.mk_right, cubeSplitAtLast, Limits.colimit.ι_desc,
    Limits.Cofan.mk_pt, Limits.Cofan.mk_ι_app]
  let xt_cube : ∂𝕀 (n + 1) :=
    TopCat.cubeBoundary.castSucc t <| (diskPair.homeoCubePairULift n).hom.left x
  let xt : ∂𝔻 (n + 1) := (diskPair.homeoCubePairULift _).inv.left xt_cube
  have : (Limits.pushout.inr (l X n) (r X n)) ⟨t, (X.attachCells n).attachMaps α x⟩ =
      (Limits.Sigma.ι (fun _ ↦ ∂𝔻 (n + 1)) α ≫
        Limits.Sigma.desc (IProd.attachMaps X)) xt := by
    unfold IProd.attachMaps xt
    simp only [Arrow.mk_left, Limits.colimit.ι_desc, Limits.Cofan.mk_pt, Limits.Cofan.mk_ι_app,
      TopCat.hom_comp, ContinuousMap.comp_apply]
    change _ = (cubeBoundary.mapOfBotTopSides _ _ _)
      (((diskPair.homeoCubePairULift _).inv.left ≫ (diskPair.homeoCubePairULift _).hom.left) _)
    simp only [Arrow.mk_left, Arrow.inv_hom_id_left, TopCat.hom_id, ContinuousMap.id_apply]
    have : xt_cube ∈ cubeBoundary.botTopSidesCover _ 2 := cubeBoundary.castSucc_mem_sides ..
    simp only [cubeBoundary.mapOfBotTopSides, hom_ofHom]
    rw [ContinuousMap.liftCoverClosed_coe' _ _ _ _ _ xt_cube this]
    change _ = (cubeAttSides X α) ⟨_, _⟩
    simp only [↓cubeSplitAtLast_inv_down_eq, Arrow.mk_left, Homeomorph.apply_symm_apply]
    change _ = (Limits.pushout.inr (l X n) (r X n)) _
    congr 2
    simp only [cubeAtt, Arrow.mk_left, TopCat.hom_comp, ContinuousMap.comp_apply]
    congr 1
    change x =
      ((diskPair.homeoCubePairULift n).hom.left ≫ (diskPair.homeoCubePairULift n).inv.left) x
    simp only [Arrow.mk_left, Arrow.hom_inv_id_left, TopCat.hom_id, ContinuousMap.id_apply]
  rw [this]
  change (_ ≫ Limits.Sigma.desc (attachMaps X) ≫ Z.inl) _ = _
  rw [Z.condition]
  simp only [Limits.ι_colimMap_assoc, Discrete.functor_obj_eq_as, Discrete.natTrans_app,
    TopCat.hom_comp, ContinuousMap.comp_assoc, ContinuousMap.comp_apply]; rfl

abbrev d' : X.sk (n + 1) ⟶ TopCat.of C(I, Z.pt) :=
    (X.attachCells n).isoPushout.hom ≫ Limits.pushout.desc (l' ..) (r' ..) (w' ..)
abbrev l'' : TopCat.of (zeroOne × X.toTopCat) ⟶ Z.pt := Limits.pushout.inl (l X n) (r X n) ≫ Z.inl
abbrev r'' : TopCat.of (I × (X.sk (n + 1))) ⟶ Z.pt := ofHom (d' ..).hom.uncurry.argSwap

/--
The following square commutes.
```
                       l X (n+1)
{0, 1} × (X.sk (n + 1)) ------→ {0, 1} × X
           |                       |
r X (n+1)  |                       | l''
           ↓                r''    ↓
     I × (X.sk (n + 1)) ---------→ Z
```
-/
lemma w'' : l X (n + 1) ≫ l'' X n Z = r X (n + 1) ≫ r'' X n Z := by
  unfold l r l'' r''
  ext ⟨t, x⟩
  simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_assoc, ContinuousMap.comp_apply,
    ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
    ContinuousMap.argSwap, ContinuousMap.coe_mk, ofHom_comp, ContinuousMap.prodSwap_apply,
      ContinuousMap.uncurry_apply, Function.uncurry_apply_pair]
  obtain ht | ht := zeroOne.eq_zero_or_eq_one t
  all_goals  -- bottom or top
    change _ = (d' ..) x (zeroOneIncl t)
    let eₜ := PathSpace.evalAt Z.pt (zeroOneIncl t)
    change _ = ((X.attachCells n).isoPushout.hom ≫
      Limits.pushout.desc (l' ..) (r' ..) (w' ..) ≫ eₜ) x
    have w'ₜ : xskl X n ≫ (l' .. ≫ eₜ) = xskr X n ≫ (r' .. ≫ eₜ) := by
      simp only [← Category.assoc, xskl, xskr, w']
    have : Limits.pushout.desc (l' ..) (r' ..) (w' ..) ≫ eₜ =
        Limits.pushout.desc (l' .. ≫ eₜ) (r' .. ≫ eₜ) w'ₜ := by
      apply Limits.pushout.hom_ext
      all_goals simp only [Limits.colimit.ι_desc_assoc, Limits.span_left, Limits.span_right,
        id_eq, Limits.PushoutCocone.mk_pt, Limits.PushoutCocone.mk_ι_app, Limits.colimit.ι_desc]
    rw [this]
    change _ = (Limits.pushout.desc (l' .. ≫ eₜ) (r' .. ≫ eₜ) w'ₜ)
      ((X.attachCells n).isoPushout.hom x)
    -- TODO: use `Limits.pushout.hom_ext` instead of `TopCat.eq_inl_or_eq_inr_of_mem_pushout`
    obtain ⟨x', hx'⟩ | ⟨y, hy⟩ := TopCat.eq_inl_or_eq_inr_of_mem_pushout (xskl X n) (xskr X n) <|
      (X.attachCells n).isoPushout.hom x
    · rw [hx']
      change _ = (Limits.pushout.inl (xskl X n) (xskr X n) ≫ _) x'
      rw [Limits.pushout.inl_desc]
      unfold l' eₜ
      simp only [ContinuousMap.argSwap, TopCat.hom_comp, ContinuousMap.coe_mk,
        ContinuousMap.comp_assoc, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.curry_apply,
        ContinuousMap.prodSwap_apply]
      congr 1
      replace hx' := congrArg (X.attachCells n).isoPushout.inv hx'
      rw [Iso.hom_inv_id_apply] at hx'
      rw [hx']
      change _ = (r X n ≫ Limits.pushout.inr (l X n) (r X n)) ⟨t, x'⟩
      rw [← Limits.pushout.condition]
      simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply,
        ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq]
      rw [← X.skInclSucc_skIncl_eq n]; rfl
    · rw [hy]
      change _ = (Limits.pushout.inr (xskl X n) (xskr X n) ≫ _) y
      rw [Limits.pushout.inr_desc]
      replace hy := congrArg (X.attachCells n).isoPushout.inv hy
      rw [Iso.hom_inv_id_apply] at hy
      rw [hy]
      change (Limits.pushout.inr (xskl X n) (xskr X n) ≫
        (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫
        ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩ ≫ Limits.pushout.inl (l X n) (r X n) ≫ Z.inl) y = _
      congr 2
      refine Limits.Sigma.hom_ext _ _ fun α ↦ ?_
      change _ = (Limits.Sigma.ι (fun x ↦ 𝔻 n) α ≫ r' ..) ≫ eₜ
      unfold r' eₜ
      rw [Limits.Sigma.ι_desc]
      have : Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr (xskl X n) (xskr X n) ≫
          (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫
          ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩ ≫ Limits.pushout.inl (l X n) (r X n) =
          (diskPair.homeoCubePairULift n).hom.right ≫ cubeBoundary.cubeInclToBotOrTop t ≫
          (diskPair.homeoCubePairULift (n + 1)).inv.left ≫ Limits.Sigma.ι (fun _ ↦ ∂𝔻 (n + 1)) α ≫
          Limits.Sigma.desc (IProd.attachMaps X) := by
        unfold IProd.attachMaps
        rw [Limits.Sigma.ι_desc, Arrow.inv_hom_id_left_assoc]
        rw [cubeBoundary.cubeInclToBotOrTop_mapOfBotTopSides _ _ _ t]
        unfold IProd.cubeAttBotOrTop cubeIncl cubeInclToSk
        simp only [Limits.colimit.cocone_x, Arrow.mk_right, Category.assoc,
          Arrow.hom_inv_id_right_assoc]
      change (Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr (xskl X n) (xskr X n) ≫
        (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫
        ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩ ≫ Limits.pushout.inl (l X n) (r X n)) ≫ Z.inl = _
      rw [this]; repeat rw [Category.assoc]
      rw [Z.condition]
      ext y
      simp only [Arrow.mk_right, Arrow.mk_left, Limits.ι_colimMap_assoc,
        Discrete.functor_obj_eq_as, Discrete.natTrans_app, Arrow.w_mk_right_assoc, Arrow.mk_hom,
        TopCat.hom_comp, ContinuousMap.comp_assoc, ContinuousMap.comp_apply,
        ContinuousMap.argSwap, cubeSplitAtLast, hom_ofHom, ContinuousMap.coe_mk,
        ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply]; rfl

/--
Given a commutative square
```
∐ ∂𝔻 (n + 1) ------→ IProd.sk X (n + 1)
    |                     |
    |                     |
    ↓                     ↓
∐ 𝔻 (n + 1) ------------→ Z
```
return the descending map `IProd.sk X (n + 1 + 1) ⟶ Z` out of the pushout cocone.
-/
abbrev desc : IProd.sk X (n + 1 + 1) ⟶ Z.pt :=
  Limits.pushout.desc (l'' X n Z) (r'' X n Z) (w'' X n Z)

def cocone (n : ℕ) :
    Limits.PushoutCocone
      (Limits.Sigma.desc (IProd.attachMaps X))
      (Limits.Sigma.map fun _ ↦ diskBoundaryIncl (n + 1)) :=
  Limits.PushoutCocone.mk
    (IProd.skInclSucc X n) (IProd.sigmaDisksInclToSk X n) (IProd.commSqSkSk X n).w

lemma cocone_inl (n : ℕ) (Z : Limits.PushoutCocone _ _) :
    (cocone X n).inl ≫ desc X n Z = Z.inl := by
  simp only [cocone, Limits.PushoutCocone.mk_pt, Limits.PushoutCocone.mk_ι_app]
  apply Limits.pushout.hom_ext
  · rw [desc, inl_skInclSucc_assoc, Limits.pushout.inl_desc]
  · rw [desc, inr_skInclSucc_assoc, Limits.pushout.inr_desc]
    ext ⟨t, x⟩
    unfold r'' RelCWComplex.skInclSucc RelCWComplex.AttachCells.incl
    simp only [TopCat.hom_comp, ContinuousMap.argSwap, ContinuousMap.coe_mk, ofHom_comp, hom_ofHom,
      ContinuousMap.comp_assoc, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
      ContinuousMap.coe_id, ContinuousMap.coe_comp, Prod.map_apply, id_eq, Function.comp_apply,
      ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair,
      Iso.inv_hom_id_apply]
    change (Limits.pushout.inl (xskl X n) (xskr X n) ≫
      (Limits.pushout.desc (l' ..) (r' ..) (w' ..)) ) x t = _
    rw [Limits.pushout.inl_desc]; rfl

lemma cocone_inr (n : ℕ) (Z : Limits.PushoutCocone _ _) :
    (cocone X n).inr ≫ desc X n Z = Z.inr := by
  simp only [cocone, Limits.PushoutCocone.mk_pt, Limits.PushoutCocone.mk_ι_app]
  rw [sigmaDisksInclToSk, desc, Category.assoc, Limits.pushout.inr_desc]
  refine Limits.Sigma.hom_ext _ _ fun α ↦ ?_
  rw [← Category.assoc, Limits.Sigma.ι_desc]
  apply CategoryTheory.eq_of_comp_right_iso_eq (diskPair.homeoCubePairULift (n + 1)).inv.right
  simp only [Category.assoc, Arrow.inv_hom_id_right_assoc]
  apply CategoryTheory.eq_of_comp_right_iso_eq cubeSplitAtLast.inv
  change (cubeSplitAtLast.inv ≫ cubeSplitAtLast.hom) ≫ ofHom _ ≫ r'' .. = _
  rw [Iso.inv_hom_id, Category.id_comp]
  ext ⟨t, y⟩
  unfold r''
  simp only [ContinuousMap.argSwap, TopCat.hom_comp, ContinuousMap.coe_mk, ofHom_comp, hom_ofHom,
    ContinuousMap.comp_assoc, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
    ContinuousMap.coe_id, Prod.map_apply, id_eq, ContinuousMap.prodSwap_apply,
    ContinuousMap.uncurry_apply, Function.uncurry_apply_pair, Arrow.mk_right]
  change (X.cubeInclToSk α ≫ (X.attachCells n).isoPushout.hom ≫
    Limits.pushout.desc (l' ..) (r' ..) (w' ..)) y t = _
  unfold CWComplex.cubeInclToSk
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Limits.pushout.inr_desc]
  unfold r'
  rw [Limits.Sigma.ι_desc]
  simp only [Arrow.mk_right, ContinuousMap.argSwap, cubeSplitAtLast,
    Limits.PushoutCocone.ι_app_right, TopCat.hom_comp, ContinuousMap.comp_assoc, hom_ofHom,
    ContinuousMap.coe_mk, Arrow.inv_hom_id_right_assoc, ContinuousMap.curry_apply,
    ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply]

end pushoutSkSk  -- namespace

open pushoutSkSk in
def pushoutSkSk (n : ℕ) :
    IsPushout
      (Limits.Sigma.desc (IProd.attachMaps X))
      (Limits.Sigma.map fun _ ↦ diskBoundaryIncl (n + 1))
      (IProd.skInclSucc X n)
      (IProd.sigmaDisksInclToSk X n) := by
  refine IsPushout.of_isColimit (?_ : Limits.IsColimit (cocone X n))
  apply Limits.PushoutCocone.isColimitAux'
  intro Z
  use desc X n Z
  refine ⟨cocone_inl X n Z, cocone_inr X n Z, ?_⟩
  intro d hdl hdr
  change sk X (n + 1 + 1) ⟶ Z.pt at d
  apply Limits.pushout.hom_ext
  · rw [Limits.pushout.inl_desc, ← inl_skInclSucc, Category.assoc]
    rw [(by rfl : skInclSucc X n = (cocone X n).inl), hdl]
  · rw [Limits.pushout.inr_desc]
    -- The goal is to prove the equality of two maps from `I × (X.sk (n + 1)))` to `Z.pt`.
    -- Now reduce this to the equality of two maps from `X.sk (n + 1)` to `C(I, Z.pt)`.
    apply TopCat.hom_eq_of_argSwap_curry_eq
    apply ContinuousMap.eq_of_topCat_ofHom
    apply eq_of_comp_right_iso_eq (X.attachCells n).isoPushout.inv
    unfold pushoutSkSk.r'' pushoutSkSk.d'
    simp only [ContinuousMap.argSwap, TopCat.hom_comp, ContinuousMap.coe_mk,
      ContinuousMap.comp_assoc, ofHom_comp, hom_ofHom]
    apply Limits.pushout.hom_ext
    · ext x t
      simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_assoc, ContinuousMap.comp_apply,
        ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
        Function.uncurry_apply_pair, Iso.inv_hom_id_apply]
      change _ = (Limits.pushout.inl (xskl X n) (xskr X n) ≫
        Limits.pushout.desc (l' ..) (r' ..) (w' ..)) x t
      rw [Limits.pushout.inl_desc, l']
      simp only [ContinuousMap.argSwap, Limits.PushoutCocone.ι_app_left, TopCat.hom_comp,
        ContinuousMap.coe_mk, ContinuousMap.comp_assoc, hom_ofHom, ContinuousMap.curry_apply,
        ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply]
      change d ( (Limits.pushout.inr (l ..) (r ..)) (t, (X.skInclSucc n) x) ) = _
      change ((ofHom ((ContinuousMap.id I).prodMap (X.skInclSucc _).hom) ≫
        Limits.pushout.inr (l X (n + 1)) (r X (n + 1))) ≫ d) ⟨t, x⟩ = _
      rw [← inr_skInclSucc, Category.assoc]
      rw [(by rfl : skInclSucc X n = (cocone X n).inl), hdl]
      rfl
    · ext α x t
      simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_assoc, ContinuousMap.comp_apply,
        ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
        Function.uncurry_apply_pair, Iso.inv_hom_id_apply]
      change _ = (Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr (xskl X n) (xskr X n) ≫
        Limits.pushout.desc (l' ..) (r' ..) (w' ..)) x t
      rw [Limits.pushout.inr_desc, r']
      simp only [Arrow.mk_right, ContinuousMap.argSwap, Limits.PushoutCocone.ι_app_right,
        TopCat.hom_comp, ContinuousMap.comp_assoc, hom_ofHom, ContinuousMap.coe_mk,
        Limits.colimit.ι_desc, Limits.Cofan.mk_pt, Limits.Cofan.mk_ι_app, ContinuousMap.comp_apply,
        ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply]
      rw [← hdr, (by rfl : (cocone X n).inr = IProd.sigmaDisksInclToSk X n)]
      change d ((Limits.pushout.inr (l X (n + 1)) (r X (n + 1)))
        ⟨t, (Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr (xskl X n) (xskr X n) ≫
          (X.attachCells n).isoPushout.inv) x⟩ ) =
        d ((cubeSplitAtLast.inv ≫ (diskPair.homeoCubePairULift (n + 1)).inv.right ≫
          Limits.Sigma.ι (fun _ ↦ 𝔻 (n + 1)) α ≫ IProd.sigmaDisksInclToSk X n )
            ⟨t, (diskPair.homeoCubePairULift n).hom.right x⟩)
      congr 1
      unfold IProd.sigmaDisksInclToSk
      change _ = (_ ≫ _ ≫ (Limits.Sigma.ι (fun _ ↦ 𝔻 (n + 1)) α ≫ Limits.Sigma.desc _) ≫ _) _
      rw [Limits.Sigma.ι_desc]
      simp only [TopCat.hom_comp, ContinuousMap.comp_assoc, ContinuousMap.comp_apply,
        Arrow.mk_right, Category.assoc, Arrow.inv_hom_id_right_assoc, Iso.inv_hom_id_assoc,
        hom_ofHom, ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq]
      congr 2
      change (Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr (xskl X n) (xskr X n) ≫
        (X.attachCells n).isoPushout.inv) x =
        ((diskPair.homeoCubePairULift n).hom.right ≫ X.cubeInclToSk α) x
      congr 2
      unfold CWComplex.cubeInclToSk
      simp only [Arrow.mk_right, Arrow.hom_inv_id_right_assoc]

end IProd


def IProd : RelCWComplex where
  sk := IProd.sk X
  attachCells n :=
    match n with
    | 0 =>
      { cells := PEmpty
        attachMaps := isEmptyElim
        isoPushout :=  -- TopCat.isIso_of_isEmpty, TopCat.isEmpty_sigmaObj_of_isEmpty_dom
          (IProd.skZeroIsoSkOne X).symm.trans <| asIso <| Limits.pushout.inl
            (Limits.Sigma.desc fun a ↦ isEmptyElim a)
            (Limits.Sigma.map fun _ ↦ diskBoundaryIncl 0) }
    | n + 1 =>
      { cells := (X.attachCells n).cells
        attachMaps := IProd.attachMaps X
        isoPushout := (IProd.pushoutSkSk X n).isoPushout }

end CWComplex

end  -- noncomputable section
