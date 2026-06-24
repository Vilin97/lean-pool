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



namespace CWComplex

/-- The inclusion map from `{0, 1} × X` to `I × X` -/
noncomputable abbrev zeroOneProdInclIProd :
    TopCat.of (zeroOne × X.toTopCat) ⟶ TopCat.of (I × X.toTopCat) :=
  ofHom <| unitInterval.zeroOneIncl.prodMap (ContinuousMap.id _)

namespace IProd

/-- `l` -/
noncomputable abbrev l (n : ℕ) := ofHom <| (ContinuousMap.id zeroOne).prodMap (X.skIncl n).hom
/-- `r` -/
abbrev r (n : ℕ) := ofHom <| zeroOneIncl.prodMap <| ContinuousMap.id <| X.sk n
/-- `xskl` -/
noncomputable abbrev xskl (n : ℕ) := Limits.Sigma.desc (X.attachCells n).attachMaps
/-- `xskr` -/
noncomputable abbrev xskr (n : ℕ) :=
  Limits.Sigma.map fun (_ : (X.attachCells n).cells) ↦ diskBoundaryIncl n

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

/-- `skZeroIsoSkOne` -/
noncomputable def skZeroIsoSkOne : CWComplex.IProd.sk X 0 ≅ CWComplex.IProd.sk X 1 :=
  have : IsIso <| ofHom <| zeroOneIncl.prodMap <| ContinuousMap.id <| X.sk 0 := by
    have := X.isEmpty_sk_zero
    infer_instance  -- TopCat.isIso_of_isEmpty
  haveI : IsIso (r X 0) := this
  @asIso _ _ _ _ (Limits.pushout.inl (l X 0) (r X 0))
    (Limits.pushout_inl_iso_of_right_iso _ _)

end IProd


/-- `cubeInclToSk` -/
noncomputable def cubeInclToSk {n : ℕ} (α : (X.attachCells n).cells) : 𝕀 n ⟶ X.sk (n + 1) :=
  (diskPair.homeoCubePairULift n).inv.right ≫
  Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr .. ≫ (X.attachCells n).isoPushout.inv

/-- `cubeIncl` -/
noncomputable def cubeIncl {n : ℕ} (α : (X.attachCells n).cells) : 𝕀 n ⟶ X :=
  X.cubeInclToSk α ≫ X.skIncl (n + 1)

/-- `cubeAtt` -/
noncomputable def cubeAtt {n : ℕ} (α : (X.attachCells n).cells) : ∂𝕀 n ⟶ X.sk n :=
  (diskPair.homeoCubePairULift n).inv.left ≫ (X.attachCells n).attachMaps α


namespace IProd

/-- `cubeAttBotOrTop` -/
noncomputable def cubeAttBotOrTop {n : ℕ} (α : (X.attachCells n).cells) (t : zeroOne) :
    𝕀 n ⟶ IProd.sk X (n + 1) :=  -- bottom face of `∂𝕀 (n + 1)`
  X.cubeIncl α ≫
  ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩ ≫  -- X ⟶ {0, 1} × X
  Limits.pushout.inl ..

/-- `cubeAttSides` -/
noncomputable def cubeAttSides {n : ℕ} (α : (X.attachCells n).cells) :
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
  unfold RelCWComplex.AttachGeneralizedCells.pushoutInr at h
  unfold RelCWComplex.AttachGeneralizedCells.pushoutInl at h
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
  have : (X.attachCells n).pushoutInl ≫ (X.attachCells n).isoPushout.inv ≫
      X.skIncl (n + 1) ≫ iX = isk ≫ l X n := by
    ext x
    · simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
        Limits.colimit.cocone_x, ContinuousMap.comp_assoc, isk, iX]
      rfl
    · simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
        Limits.colimit.cocone_x, ContinuousMap.comp_assoc, isk, iX]
      change (X.skInclSucc _ ≫ X.skIncl _) x = (X.skIncl _) x
      rw [X.skInclSucc_skIncl_eq]
  change (_ ≫ _ ≫ _ ≫ iX) ≫ _ = _
  rw [this, Category.assoc, Limits.pushout.condition]

/-- `attachMaps` -/
noncomputable def attachMaps {n : ℕ} (α : (X.attachCells n).cells) :
    ∂𝔻 (n + 1) ⟶ IProd.sk X (n + 1) :=
  (diskPair.homeoCubePairULift (n + 1)).hom.left ≫
    cubeBoundary.mapOfBotTopSides
      (IProd.cubeAttBotOrTop X α) (IProd.cubeAttSides X α) (IProd.cubeAtt_compatible X α)

/-- Note:
Each $n$-cell of `X` corresponds to an $(n + 1)$-cell of `X.IProd`.
The latter cell is attached to `IProd.sk X (n + 1)`, which is of dimension $n$.
`X.IProd` has no `0`-cells. -/
noncomputable def sigmaDisksInclToSk (n : ℕ) :
    (∐ fun (_ : (X.attachCells n).cells) ↦ 𝔻 (n + 1)) ⟶ IProd.sk X (n + 1 + 1) :=
  (Limits.Sigma.desc
    fun α ↦ (diskPair.homeoCubePairULift _).hom.right ≫ cubeSplitAtLast.hom ≫
      ofHom ((ContinuousMap.id I).prodMap (X.cubeInclToSk α).hom) )
  ≫ Limits.pushout.inr ..

/-- `skInclSucc` -/
noncomputable def skInclSucc (n : ℕ) : IProd.sk X (n + 1) ⟶ IProd.sk X (n + 1 + 1) :=
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
lemma commSqSkSk (n : ℕ) :
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
    -- The underlying morphism equality follows from the universal property of the coproduct.
    apply Limits.Sigma.hom_ext
    intro α
    simp only [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc,
      ]
    -- Now we need to show `attachMaps α ≫ skInclSucc X n = diskBoundaryIncl (n+1) ≫
    -- Sigma.ι _ α ≫ sigmaDisksInclToSk X n`.
    unfold IProd.attachMaps IProd.sigmaDisksInclToSk
    rw [Limits.Sigma.ι_desc_assoc]
    -- Use `Arrow.Hom.w` to move `diskBoundaryIncl` past `right`.
    have hw : diskBoundaryIncl (n + 1) ≫ (diskPair.homeoCubePairULift (n + 1)).hom.right =
        (diskPair.homeoCubePairULift (n + 1)).hom.left ≫ cubeBoundaryIncl (n + 1) :=
      ((diskPair.homeoCubePairULift (n + 1)).hom.w).symm
    simp only [← Category.assoc]
    rw [hw]
    -- Both sides start with `(diskPair.homeoCubePairULift (n + 1)).hom.left`. Reassociate.
    simp only [Category.assoc]
    -- Apply hom_ext directly to reduce to pointwise equality.
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x'
    set y := ((diskPair.homeoCubePairULift (n + 1)).hom.left : ∂𝔻 (n + 1) ⟶ _) x' with hy_def
    change (cubeBoundary.mapOfBotTopSides _ _ (IProd.cubeAtt_compatible X α) ≫ skInclSucc X n) y =
      (cubeBoundaryIncl (n + 1) ≫
        cubeSplitAtLast.hom ≫ ofHom ((ContinuousMap.id ↑I).prodMap (Hom.hom (X.cubeInclToSk α))) ≫
        Limits.pushout.inr (l X (n + 1)) (r X (n + 1))) y
    clear_value y; clear hy_def x'
    obtain ⟨k, hk⟩ := cubeBoundary.botTopSidesCover_cover _ y
    fin_cases k
    all_goals
      change (skInclSucc X n) (ContinuousMap.liftCoverClosed _ _ _ cv cl _) = _
      rw [ContinuousMap.liftCoverClosed_coe' _ _ _ _ _ _ hk]
      obtain ⟨⟨y, hy⟩⟩ := y
      change _ = Limits.pushout.inr (l X (n + 1)) (r X (n + 1))
        ⟨(Cube.splitAtLast y).fst, X.cubeInclToSk α ⟨(Cube.splitAtLast y).snd⟩⟩
    iterate 2  -- bottom and top of the $(n + 1)$-cube
      change (X.cubeInclToSk α ≫ isk _ ≫ l X (n + 1) ≫
          Limits.pushout.inl .. ≫ skInclSucc X n ) ⟨(Cube.splitAtLast y).snd⟩ = _
      rw [skInclSucc, Limits.pushout.inl_desc]
      change ((X.cubeInclToSk α ≫ isk _) ≫
          (l X (n + 1) ≫ Limits.pushout.inl (l X (n + 1)) (r X (n + 1))))
            ⟨(Cube.splitAtLast y).snd⟩ = _
      rw [Limits.pushout.condition]
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
      -- Use `w_cell'` which says
      -- `f ≫ Sigma.ι α ≫ pushout.inr = Sigma.ι α ≫ Sigma.desc ≫ pushout.inl`.
      have hwc := (X.attachCells n).w_cell' α
      unfold RelCWComplex.AttachGeneralizedCells.pushoutInl
        RelCWComplex.AttachGeneralizedCells.pushoutInr at hwc
      rw [(X.attachCells n).attachMaps_apply_eq_ι_desc]
      exact (Category.assoc _ _ _).trans hwc.symm ⟩


namespace pushoutSkSk
/-!
Now verify that `commSqSkSk` is a pushout square.
-/

variable (n : ℕ) (Z : Limits.PushoutCocone
  (Limits.Sigma.desc (IProd.attachMaps X))
  (Limits.Sigma.map fun _ ↦ diskBoundaryIncl (n + 1)))

/-- `l'` -/
noncomputable abbrev l' : X.sk n ⟶ TopCat.of C(I, Z.pt) :=
  ofHom (Limits.pushout.inr (l X n) (r X n) ≫ Z.inl).hom.argSwap.curry
/-- `r'` -/
noncomputable abbrev r' : (∐ fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) ⟶ TopCat.of C(I, Z.pt) :=
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
  apply Limits.Sigma.hom_ext
  intro α
  unfold IProd.xskl IProd.xskr
  rw [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc]
  change _ = diskBoundaryIncl n ≫ Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ r' ..
  ext x t
  unfold l' r'
  simp only [ContinuousMap.argSwap, TopCat.hom_comp, ContinuousMap.coe_mk,
    ContinuousMap.comp_assoc, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.curry_apply,
    ContinuousMap.prodSwap_apply, cubeSplitAtLast,
    ]
  let xt_cube : ∂𝕀 (n + 1) :=
    TopCat.cubeBoundary.castSucc t <| (diskPair.homeoCubePairULift n).hom.left x
  let xt : ∂𝔻 (n + 1) := (diskPair.homeoCubePairULift _).inv.left xt_cube
  have : (Limits.pushout.inr (l X n) (r X n)) ⟨t, (X.attachCells n).attachMaps α x⟩ =
      (Limits.Sigma.ι (fun _ ↦ ∂𝔻 (n + 1)) α ≫
        Limits.Sigma.desc (IProd.attachMaps X)) xt := by
    unfold IProd.attachMaps xt
    rw [Limits.Sigma.ι_desc]
    change _ = ((diskPair.homeoCubePairULift _).inv.left ≫
      (diskPair.homeoCubePairULift _).hom.left ≫
      cubeBoundary.mapOfBotTopSides (cubeAttBotOrTop X α) (cubeAttSides X α)
        (cubeAtt_compatible X α)) xt_cube
    rw [Arrow.inv_hom_id_left_assoc]
    have : xt_cube ∈ cubeBoundary.botTopSidesCover _ 2 := cubeBoundary.castSucc_mem_sides ..
    unfold cubeBoundary.mapOfBotTopSides
    change _ = (ContinuousMap.liftCoverClosed (cubeBoundary.botTopSidesCover n)
      (cubeBoundary.mapVecOfBotTopSides (cubeAttBotOrTop X α) (cubeAttSides X α))
      (cubeBoundary.mapVecOfBotTopSides_compatible _ _ (cubeAtt_compatible X α))
      (cubeBoundary.botTopSidesCover_cover n)
      (cubeBoundary.botTopSidesCover_closed n)) xt_cube
    rw [ContinuousMap.liftCoverClosed_coe' _ _ _ _ _ xt_cube this]
    change _ = (cubeAttSides X α) ⟨_, _⟩
    simp only [↓cubeSplitAtLast_inv_down_eq, Homeomorph.apply_symm_apply]
    change _ = (Limits.pushout.inr (l X n) (r X n)) _
    congr 2
    simp only [cubeAtt, TopCat.hom_comp, ContinuousMap.comp_apply]
    congr 1
    change x =
      ((diskPair.homeoCubePairULift n).hom.left ≫ (diskPair.homeoCubePairULift n).inv.left) x
    rw [Arrow.hom_inv_id_left]; rfl
  rw [this]
  change (_ ≫ Limits.Sigma.desc (attachMaps X) ≫ Z.inl) _ = _
  rw [Z.condition]
  -- LHS becomes (Sigma.ι α ≫ Sigma.map _ ≫ Z.inr) xt; RHS uses Sigma.desc of r'.
  change (Limits.Sigma.ι (fun _ ↦ ∂𝔻 (n + 1)) α ≫
      (Limits.Sigma.map fun _ ↦ diskBoundaryIncl (n + 1)) ≫ Z.inr) xt =
    (Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ r' X n Z) (diskBoundaryIncl n x) t
  rw [Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc]
  rfl

/-- `d'` -/
noncomputable abbrev d' : X.sk (n + 1) ⟶ TopCat.of C(I, Z.pt) :=
    (X.attachCells n).isoPushout.hom ≫ Limits.pushout.desc (l' ..) (r' ..) (w' ..)
/-- `l''` -/
noncomputable abbrev l'' : TopCat.of (zeroOne × X.toTopCat) ⟶ Z.pt :=
  Limits.pushout.inl (l X n) (r X n) ≫ Z.inl
/-- `r''` -/
noncomputable abbrev r'' : TopCat.of (I × (X.sk (n + 1))) ⟶ Z.pt :=
  ofHom (d' ..).hom.uncurry.argSwap

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
      · rw [← Category.assoc, Limits.pushout.inl_desc, Limits.pushout.inl_desc]
      · rw [← Category.assoc, Limits.pushout.inr_desc, Limits.pushout.inr_desc]
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
        -- Reduce RHS: `Sigma.ι α ≫ Sigma.desc (attachMaps X) = attachMaps X α`,
        -- then `inv.left ≫ hom.left ≫ map = map` via `Arrow.inv_hom_id_left`.
        have hRHS : (diskPair.homeoCubePairULift n).hom.right ≫
            cubeBoundary.cubeInclToBotOrTop t ≫
            (diskPair.homeoCubePairULift (n + 1)).inv.left ≫
            Limits.Sigma.ι (fun _ ↦ ∂𝔻 (n + 1)) α ≫ Limits.Sigma.desc (IProd.attachMaps X) =
            (diskPair.homeoCubePairULift n).hom.right ≫
            cubeBoundary.cubeInclToBotOrTop t ≫
            cubeBoundary.mapOfBotTopSides (IProd.cubeAttBotOrTop X α) (IProd.cubeAttSides X α)
              (IProd.cubeAtt_compatible X α) := by
          congr 1
          congr 1
          -- LHS: inv.left ≫ Sigma.ι α ≫ Sigma.desc (attachMaps X)
          -- = inv.left ≫ attachMaps X α
          -- = inv.left ≫ hom.left ≫ mapOfBotTopSides
          -- = mapOfBotTopSides
          calc (diskPair.homeoCubePairULift (n + 1)).inv.left ≫
              Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ ∂𝔻 (n + 1)) α ≫
              Limits.Sigma.desc (IProd.attachMaps X)
              = (diskPair.homeoCubePairULift (n + 1)).inv.left ≫
                IProd.attachMaps X α := by
                congr 1
                exact Limits.Sigma.ι_desc _ α
            _ = cubeBoundary.mapOfBotTopSides (IProd.cubeAttBotOrTop X α) (IProd.cubeAttSides X α)
                  (IProd.cubeAtt_compatible X α) := by
                unfold IProd.attachMaps
                exact Arrow.inv_hom_id_left_assoc _ _
        rw [hRHS]
        -- Now reduce `cubeInclToBotOrTop t ≫ mapOfBotTopSides ... = cubeAttBotOrTop X α t`.
        have hCIB : cubeBoundary.cubeInclToBotOrTop t ≫
            cubeBoundary.mapOfBotTopSides (IProd.cubeAttBotOrTop X α) (IProd.cubeAttSides X α)
              (IProd.cubeAtt_compatible X α) =
            IProd.cubeAttBotOrTop X α t :=
          cubeBoundary.cubeInclToBotOrTop_mapOfBotTopSides _ _ _ t
        rw [show (diskPair.homeoCubePairULift n).hom.right ≫
            cubeBoundary.cubeInclToBotOrTop t ≫
            cubeBoundary.mapOfBotTopSides (IProd.cubeAttBotOrTop X α) (IProd.cubeAttSides X α)
              (IProd.cubeAtt_compatible X α) =
            (diskPair.homeoCubePairULift n).hom.right ≫ IProd.cubeAttBotOrTop X α t from by
          congr 1]
        -- Unfold cubeAttBotOrTop α t and use `hom.right ≫ inv.right = 𝟙 _`.
        unfold IProd.cubeAttBotOrTop cubeIncl cubeInclToSk
        -- Express the LHS to match the unfolded RHS.
        have hCubeId : (diskPair.homeoCubePairULift n).hom.right ≫
            (diskPair.homeoCubePairULift n).inv.right ≫
            Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
            Limits.pushout.inr (Limits.Sigma.desc (X.attachCells n).attachMaps)
              (Limits.Sigma.map fun _ ↦ diskBoundaryIncl n) ≫
            (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫
            ofHom ⟨fun x ↦ (t, x), by fun_prop⟩ =
            Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
            Limits.pushout.inr (Limits.Sigma.desc (X.attachCells n).attachMaps)
              (Limits.Sigma.map fun _ ↦ diskBoundaryIncl n) ≫
            (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫
            ofHom ⟨fun x ↦ (t, x), by fun_prop⟩ :=
          Arrow.hom_inv_id_right_assoc _ _
        change Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
            Limits.pushout.inr (xskl X n) (xskr X n) ≫
            (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫
            ofHom ⟨fun x ↦ (t, x), by fun_prop⟩ ≫ Limits.pushout.inl (l X n) (r X n) =
            ((diskPair.homeoCubePairULift n).hom.right ≫
              (diskPair.homeoCubePairULift n).inv.right ≫
              Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
              Limits.pushout.inr (Limits.Sigma.desc (X.attachCells n).attachMaps)
                (Limits.Sigma.map fun _ ↦ diskBoundaryIncl n) ≫
              (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫
              ofHom ⟨fun x ↦ (t, x), by fun_prop⟩) ≫ Limits.pushout.inl (l X n) (r X n)
        rw [hCubeId]
        -- After collapsing hom.right ≫ inv.right, both sides match up to associativity
        -- and the definitional equalities `xskl = Sigma.desc ..` and `xskr = Sigma.map ..`.
        rfl
      change (Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr (xskl X n) (xskr X n) ≫
        (X.attachCells n).isoPushout.inv ≫ X.skIncl (n + 1) ≫
        ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩ ≫ Limits.pushout.inl (l X n) (r X n)) ≫ Z.inl = _
      rw [this]
      -- The LHS is now `(... ≫ Sigma.desc (attachMaps X)) ≫ Z.inl`. Re-associate so we
      -- can apply `Z.condition : Sigma.desc (attachMaps X) ≫ Z.inl = Sigma.map _ ≫ Z.inr`.
      change (diskPair.homeoCubePairULift n).hom.right ≫ cubeBoundary.cubeInclToBotOrTop t ≫
          (diskPair.homeoCubePairULift (n + 1)).inv.left ≫
          Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ ∂𝔻 (n + 1)) α ≫
          (Limits.Sigma.desc (IProd.attachMaps X) ≫ Z.inl) = _
      rw [Z.condition]
      -- After Z.condition, LHS has `Sigma.ι α ≫ Sigma.map _ ≫ Z.inr`. Bridge via Sigma.ι_map.
      have hLHS : (diskPair.homeoCubePairULift n).hom.right ≫ cubeBoundary.cubeInclToBotOrTop t ≫
          (diskPair.homeoCubePairULift (n + 1)).inv.left ≫
          Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ ∂𝔻 (n + 1)) α ≫
          (Limits.Sigma.map fun _ ↦ diskBoundaryIncl (n + 1)) ≫ Z.inr =
          (diskPair.homeoCubePairULift n).hom.right ≫ cubeBoundary.cubeInclToBotOrTop t ≫
          (diskPair.homeoCubePairULift (n + 1)).inv.left ≫
          diskBoundaryIncl (n + 1) ≫
          Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 (n + 1)) α ≫ Z.inr := by
        congr 1
        congr 1
        congr 1
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        exact Limits.Sigma.ι_map _ _
      rw [hLHS]
      ext y
      simp only [TopCat.hom_comp, ContinuousMap.argSwap, cubeSplitAtLast,
        ContinuousMap.coe_mk]; rfl

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
noncomputable abbrev desc : IProd.sk X (n + 1 + 1) ⟶ Z.pt :=
  Limits.pushout.desc (l'' X n Z) (r'' X n Z) (w'' X n Z)

/-- `cocone` -/
noncomputable def cocone (n : ℕ) :
    Limits.PushoutCocone
      (Limits.Sigma.desc (IProd.attachMaps X))
      (Limits.Sigma.map fun _ ↦ diskBoundaryIncl (n + 1)) :=
  Limits.PushoutCocone.mk
    (IProd.skInclSucc X n) (IProd.sigmaDisksInclToSk X n) (IProd.commSqSkSk X n).w

lemma coconeInl (n : ℕ) (Z : Limits.PushoutCocone _ _) :
    (cocone X n).inl ≫ desc X n Z = Z.inl := by
  simp only [cocone, Limits.PushoutCocone.mk_ι_app]
  apply Limits.pushout.hom_ext
  · change Limits.pushout.inl (l X n) (r X n) ≫ _ ≫ _ = _
    unfold desc
    have hstep := congrArg
      (fun q => q ≫ Limits.pushout.desc (l'' X n Z) (r'' X n Z) (w'' X n Z))
      (inl_skInclSucc (X := X) (n := n))
    exact hstep.trans (Limits.pushout.inl_desc (l'' X n Z) (r'' X n Z) (w'' X n Z))
  · change Limits.pushout.inr (l X n) (r X n) ≫ _ ≫ _ = _
    unfold desc
    have hstep := congrArg
      (fun q => q ≫ Limits.pushout.desc (l'' X n Z) (r'' X n Z) (w'' X n Z))
      (inr_skInclSucc (X := X) (n := n))
    refine (Category.assoc _ _ _).symm.trans ?_
    refine hstep.trans ?_
    change ofHom ((ContinuousMap.id ↑I).prodMap (Hom.hom (X.skInclSucc n))) ≫
        Limits.pushout.inr (l X (n + 1)) (r X (n + 1)) ≫
          Limits.pushout.desc (l'' X n Z) (r'' X n Z) (w'' X n Z) = _
    rw [Limits.pushout.inr_desc]
    ext ⟨t, x⟩
    unfold r''
    simp only [TopCat.hom_comp, ContinuousMap.argSwap, ContinuousMap.coe_mk, ofHom_comp, hom_ofHom,
      ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
      ContinuousMap.coe_id, Prod.map_apply, id_eq,
      ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair]
    have hSk : (Hom.hom (X.attachCells n).isoPushout.hom) ((Hom.hom (X.skInclSucc n)) x) =
        (Hom.hom (Limits.pushout.inl (xskl X n) (xskr X n))) x := by
      change (X.skInclSucc n ≫ (X.attachCells n).isoPushout.hom).hom x =
        (Limits.pushout.inl (xskl X n) (xskr X n)).hom x
      congr 1
      unfold RelCWComplex.skInclSucc RelCWComplex.AttachCells.incl
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hSk]
    change ((Limits.pushout.inl (xskl X n) (xskr X n) ≫
      Limits.pushout.desc (l' ..) (r' ..) (w' ..)).hom x) t = _
    rw [Limits.pushout.inl_desc]
    unfold l'
    simp only [TopCat.hom_comp, ContinuousMap.argSwap, ContinuousMap.coe_mk,
      ContinuousMap.comp_apply, ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply, hom_ofHom]

lemma coconeInr (n : ℕ) (Z : Limits.PushoutCocone _ _) :
    (cocone X n).inr ≫ desc X n Z = Z.inr := by
  simp only [cocone, Limits.PushoutCocone.mk_ι_app]
  unfold sigmaDisksInclToSk desc
  change (Limits.Sigma.desc fun α ↦
      Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).hom ≫
        cubeSplitAtLast.hom ≫ ofHom ((ContinuousMap.id ↑I).prodMap (Hom.hom (X.cubeInclToSk α)))) ≫
    (Limits.pushout.inr (l X (n + 1)) (r X (n + 1)) ≫
      Limits.pushout.desc (l'' X n Z) (r'' X n Z) (w'' X n Z)) = Z.inr
  rw [Limits.pushout.inr_desc]
  refine Limits.Sigma.hom_ext _ _ fun α ↦ ?_
  rw [← Category.assoc, Limits.Sigma.ι_desc]
  apply CategoryTheory.eq_of_comp_right_iso_eq (diskPair.homeoCubePairULift (n + 1)).inv.right
  simp only [Category.assoc, Arrow.inv_hom_id_right_assoc]
  apply CategoryTheory.eq_of_comp_right_iso_eq cubeSplitAtLast.inv
  change (cubeSplitAtLast.inv ≫ cubeSplitAtLast.hom) ≫ ofHom _ ≫ r'' .. = _
  rw [Iso.inv_hom_id, Category.id_comp]
  -- Now we need to show that two morphisms `I × 𝕀 n ⟶ Z.pt` agree.
  -- The LHS is `ofHom (id I).prodMap (X.cubeInclToSk α).hom ≫ r''`.
  -- The RHS is `cubeSplitAtLast.inv ≫ (diskPair.homeoCubePairULift (n+1)).inv.right ≫
  --   Limits.Sigma.ι ... α ≫ Z.inr`.
  -- We reduce by computing
  -- `cubeInclToSk α ≫ isoPushout.hom = Sigma.ι α ≫ pushout.inr (xskl, xskr)`.
  have hcube : X.cubeInclToSk α ≫ (X.attachCells n).isoPushout.hom =
      (diskPair.homeoCubePairULift n).inv.right ≫ Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫
        Limits.pushout.inr (xskl X n) (xskr X n) := by
    unfold CWComplex.cubeInclToSk xskl xskr
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  -- Compute `Sigma.ι α ≫ r' = (diskPair.homeoCubePairULift n).hom.right ≫ ofHom (curry ...)`.
  have hι : Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫ r' X n Z = _ :=
    Limits.Sigma.ι_desc _ α
  ext ⟨t, y⟩
  unfold r''
  simp only [ContinuousMap.argSwap, TopCat.hom_comp, ContinuousMap.coe_mk, ofHom_comp, hom_ofHom,
    ContinuousMap.comp_assoc, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
    ContinuousMap.coe_id, Prod.map_apply, id_eq, ContinuousMap.prodSwap_apply,
    ContinuousMap.uncurry_apply, Function.uncurry_apply_pair]
  -- LHS: `d' (cubeInclToSk α y) t`. By hcube, `isoPushout.hom (cubeInclToSk α y)`
  --      equals
  --      `pushout.inr (xskl X n) (xskr X n)
  --        (Sigma.ι α ((diskPair.homeoCubePairULift n).inv.right y))`.
  -- Use hcube ≫ pushout.desc = ... ≫ r' (i.e. inline the pushout.inr_desc step).
  have hcomp : X.cubeInclToSk α ≫ (X.attachCells n).isoPushout.hom ≫
      Limits.pushout.desc (l' X n Z) (r' X n Z) (w' X n Z) =
      (diskPair.homeoCubePairULift n).inv.right ≫
        Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫ r' X n Z := by
    rw [← Category.assoc, hcube]
    change Arrow.Hom.right (diskPair.homeoCubePairULift n).inv ≫
        Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
          Limits.pushout.inr (xskl X n) (xskr X n) ≫
            Limits.pushout.desc (l' X n Z) (r' X n Z) (w' X n Z) = _
    rw [Limits.pushout.inr_desc]
  change (X.cubeInclToSk α ≫ (X.attachCells n).isoPushout.hom ≫
    Limits.pushout.desc (l' ..) (r' ..) (w' ..)) y t = _
  rw [hcomp]
  -- Inline hι by replacing `r' X n Z` directly in the LHS using a calc-style equation.
  have hfinal : ((diskPair.homeoCubePairULift n).inv.right ≫
        Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫ r' X n Z) =
      (diskPair.homeoCubePairULift n).inv.right ≫
        ((diskPair.homeoCubePairULift n).hom.right ≫ ofHom (ContinuousMap.curry
          (TopCat.cubeSplitAtLast.inv ≫ (diskPair.homeoCubePairULift _).inv.right ≫
            Limits.Sigma.ι (fun _ ↦ 𝔻 _) α ≫ Z.inr).hom.argSwap)) := by
    apply congrArg
    exact hι
  rw [hfinal]
  -- After hfinal substitution, the LHS has `right .inv ≫ right .hom = id`.
  -- Use `inv_hom_id_right_assoc`.
  simp only [Arrow.inv_hom_id_right_assoc]
  simp only [ContinuousMap.argSwap, cubeSplitAtLast, TopCat.hom_comp,
    ContinuousMap.comp_assoc]
  rfl

end pushoutSkSk  -- namespace

open pushoutSkSk in
/-- `pushoutSkSk` -/
lemma pushoutSkSk (n : ℕ) :
    IsPushout
      (Limits.Sigma.desc (IProd.attachMaps X))
      (Limits.Sigma.map fun _ ↦ diskBoundaryIncl (n + 1))
      (IProd.skInclSucc X n)
      (IProd.sigmaDisksInclToSk X n) := by
  refine IsPushout.of_isColimit (?_ : Limits.IsColimit (cocone X n))
  apply Limits.PushoutCocone.isColimitAux'
  intro Z; use desc X n Z
  refine ⟨coconeInl X n Z, coconeInr X n Z, ?_⟩
  intro d hdl hdr; change sk X (n + 1 + 1) ⟶ Z.pt at d
  apply Limits.pushout.hom_ext
  · rw [Limits.pushout.inl_desc]
    have hreassoc : Limits.pushout.inl (l X n) (r X n) ≫ skInclSucc X n ≫ d =
        Limits.pushout.inl (l X (n + 1)) (r X (n + 1)) ≫ d :=
      inl_skInclSucc_assoc X d
    rw [← hreassoc]
    change Limits.pushout.inl (l X n) (r X n) ≫ (cocone X n).inl ≫ d = _
    have : Limits.pushout.inl (l X n) (r X n) ≫ (cocone X n).inl ≫ d =
        Limits.pushout.inl (l X n) (r X n) ≫ Z.inl :=
      congrArg (Limits.pushout.inl (l X n) (r X n) ≫ ·) hdl
    rw [this]
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
      simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_assoc,
        ContinuousMap.comp_apply, ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply,
        ContinuousMap.uncurry_apply, Function.uncurry_apply_pair, Iso.inv_hom_id_apply]
      change _ = (Limits.pushout.inl (xskl X n) (xskr X n) ≫
        Limits.pushout.desc (l' ..) (r' ..) (w' ..)) x t
      rw [Limits.pushout.inl_desc, l']
      simp only [ContinuousMap.argSwap, Limits.PushoutCocone.ι_app_left,
        TopCat.hom_comp, ContinuousMap.coe_mk, ContinuousMap.comp_assoc, hom_ofHom,
        ContinuousMap.curry_apply, ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply]
      change d ( (Limits.pushout.inr (l ..) (r ..)) (t, (X.skInclSucc n) x) ) = _
      change ((ofHom ((ContinuousMap.id I).prodMap (X.skInclSucc _).hom) ≫
        Limits.pushout.inr (l X (n + 1)) (r X (n + 1))) ≫ d) ⟨t, x⟩ = _
      have hreassoc : Limits.pushout.inr (l X n) (r X n) ≫ skInclSucc X n ≫ d =
          (ofHom ((ContinuousMap.id I).prodMap (X.skInclSucc _).hom) ≫
            Limits.pushout.inr (l X (n + 1)) (r X (n + 1))) ≫ d := by
        rw [inr_skInclSucc_assoc]
        rfl
      rw [← hreassoc]
      change (Limits.pushout.inr (l X n) (r X n) ≫ (cocone X n).inl ≫ d) ⟨t, x⟩ = _
      have : Limits.pushout.inr (l X n) (r X n) ≫ (cocone X n).inl ≫ d =
          Limits.pushout.inr (l X n) (r X n) ≫ Z.inl :=
        congrArg (Limits.pushout.inr (l X n) (r X n) ≫ ·) hdl
      rw [this]; rfl
    · ext α x t
      simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_assoc, ContinuousMap.comp_apply,
        ContinuousMap.curry_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
        Function.uncurry_apply_pair, Iso.inv_hom_id_apply]
      change _ = (Limits.Sigma.ι (fun _ ↦ 𝔻 n) α ≫ Limits.pushout.inr (xskl X n) (xskr X n) ≫
        Limits.pushout.desc (l' ..) (r' ..) (w' ..)) x t
      rw [Limits.pushout.inr_desc, r']
      simp only [ContinuousMap.argSwap, Limits.PushoutCocone.ι_app_right, TopCat.hom_comp,
        ContinuousMap.comp_assoc, ContinuousMap.coe_mk, ContinuousMap.comp_apply]
      rw [← hdr, (by rfl : (cocone X n).inr = IProd.sigmaDisksInclToSk X n)]
      -- Combine nested `Hom.hom` applications into a single composition.
      simp only [← TopCat.comp_app]
      -- Reduce the RHS `(Sigma.desc f).hom (Sigma.ι α x) t` via `Sigma.ι_desc` at morphism level.
      have hsi : Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
          (Limits.Sigma.desc fun α ↦
              Arrow.Hom.right (diskPair.homeoCubePairULift n).hom ≫
                ofHom ((Hom.hom (sigmaDisksInclToSk X n ≫ d)).comp
                  ((Hom.hom (Limits.Sigma.ι (fun _ ↦ 𝔻 (n + 1)) α)).comp
                    ((Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).inv)).comp
                      ((Hom.hom cubeSplitAtLast.inv).comp ContinuousMap.prodSwap)))).curry) =
          Arrow.Hom.right (diskPair.homeoCubePairULift n).hom ≫
              ofHom ((Hom.hom (sigmaDisksInclToSk X n ≫ d)).comp
                ((Hom.hom (Limits.Sigma.ι (fun _ ↦ 𝔻 (n + 1)) α)).comp
                  ((Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).inv)).comp
                    ((Hom.hom cubeSplitAtLast.inv).comp ContinuousMap.prodSwap)))).curry :=
        Limits.Sigma.ι_desc _ α
      -- Provide the morphism-level identity for the LHS.
      have hci : (Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
            Limits.pushout.inr (Limits.Sigma.desc (X.attachCells n).attachMaps)
              (Limits.Sigma.map fun _ ↦ diskBoundaryIncl n)) ≫
          (X.attachCells n).isoPushout.inv =
          (diskPair.homeoCubePairULift n).hom.right ≫ X.cubeInclToSk α := by
        have hiso : (diskPair.homeoCubePairULift n).hom.right ≫
            (diskPair.homeoCubePairULift n).inv.right = 𝟙 _ :=
          Arrow.hom_inv_id_right ..
        have hrhs : (diskPair.homeoCubePairULift n).hom.right ≫ X.cubeInclToSk α =
            ((diskPair.homeoCubePairULift n).hom.right ≫
                (diskPair.homeoCubePairULift n).inv.right) ≫
              Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
                Limits.pushout.inr (Limits.Sigma.desc (X.attachCells n).attachMaps)
                  (Limits.Sigma.map fun _ ↦ diskBoundaryIncl n) ≫
                  (X.attachCells n).isoPushout.inv := by
          unfold CWComplex.cubeInclToSk
          change ((diskPair.homeoCubePairULift n).hom.right ≫
              (diskPair.homeoCubePairULift n).inv.right) ≫
            Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
              Limits.pushout.inr (Limits.Sigma.desc (X.attachCells n).attachMaps)
                (Limits.Sigma.map fun _ ↦ diskBoundaryIncl n) ≫
                (X.attachCells n).isoPushout.inv = _
          rw [hiso, Category.id_comp]
        rw [hrhs, hiso, Category.id_comp]
        rfl
      -- Rewrite both LHS and RHS to use `cubeInclToSk` as the common factor.
      change (Hom.hom d) ((Hom.hom (Limits.pushout.inr (l X (n + 1)) (r X (n + 1))))
          (t, ((Hom.hom ((Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
            Limits.pushout.inr (Limits.Sigma.desc (X.attachCells n).attachMaps)
              (Limits.Sigma.map fun _ ↦ diskBoundaryIncl n)) ≫
              (X.attachCells n).isoPushout.inv)) x))) =
        ((Hom.hom (Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 n) α ≫
          (Limits.Sigma.desc fun α ↦
              Arrow.Hom.right (diskPair.homeoCubePairULift n).hom ≫
                ofHom ((Hom.hom (sigmaDisksInclToSk X n ≫ d)).comp
                  ((Hom.hom (Limits.Sigma.ι (fun _ ↦ 𝔻 (n + 1)) α)).comp
                    ((Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).inv)).comp
                      ((Hom.hom cubeSplitAtLast.inv).comp ContinuousMap.prodSwap)))).curry))) x) t
      rw [hci, hsi]
      -- Now both sides express the same map evaluated; reduce by unfolding `sigmaDisksInclToSk`.
      simp only []
      unfold IProd.sigmaDisksInclToSk
      simp only [TopCat.hom_comp]
      have hsidisks : Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 (n + 1)) α ≫
          (Limits.Sigma.desc fun α ↦
            Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).hom ≫
              cubeSplitAtLast.hom ≫
                ofHom ((ContinuousMap.id ↑I).prodMap (Hom.hom (X.cubeInclToSk α)))) =
          Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).hom ≫
            cubeSplitAtLast.hom ≫
              ofHom ((ContinuousMap.id ↑I).prodMap (Hom.hom (X.cubeInclToSk α))) :=
        Limits.Sigma.ι_desc _ α
      -- Evaluate the curried form on the RHS manually so the result matches the LHS.
      change (Hom.hom d) ((Hom.hom (Limits.pushout.inr (l X (n + 1)) (r X (n + 1))))
          (t, (Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift n).hom ≫
            X.cubeInclToSk α)) x)) =
        (Hom.hom d) ((Hom.hom (Limits.pushout.inr (l X (n + 1)) (r X (n + 1))))
          ((Hom.hom (Limits.Sigma.desc fun α ↦
              Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).hom ≫
                cubeSplitAtLast.hom ≫
                ofHom ((ContinuousMap.id ↑I).prodMap (Hom.hom (X.cubeInclToSk α)))))
            ((Hom.hom (Limits.Sigma.ι (fun _ ↦ 𝔻 (n + 1)) α))
              ((Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).inv))
                ((Hom.hom TopCat.cubeSplitAtLast.inv)
                  (ContinuousMap.prodSwap
                    ((Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift n).hom)) x, t)))))))
      -- Apply hsidisks pointwise via `congr` to evaluate the inner Sigma.desc ∘ Sigma.ι α.
      congr 2
      have hsi_pt :
        ∀ z, (Hom.hom (Limits.Sigma.desc fun α ↦
            Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).hom ≫
              cubeSplitAtLast.hom ≫
              ofHom ((ContinuousMap.id ↑I).prodMap (Hom.hom (X.cubeInclToSk α)))))
            ((Hom.hom (Limits.Sigma.ι (fun (_ : (X.attachCells n).cells) ↦ 𝔻 (n + 1)) α)) z) =
            (Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).hom ≫
              cubeSplitAtLast.hom ≫
              ofHom ((ContinuousMap.id ↑I).prodMap (Hom.hom (X.cubeInclToSk α))))) z := by
        intro z
        have h₂ : (Hom.hom (Limits.Sigma.ι (fun _ ↦ 𝔻 (n + 1)) α ≫ Limits.Sigma.desc fun α ↦
            Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).hom ≫
              cubeSplitAtLast.hom ≫
              ofHom ((ContinuousMap.id ↑I).prodMap (Hom.hom (X.cubeInclToSk α))))) z =
            (Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).hom ≫
              cubeSplitAtLast.hom ≫
              ofHom ((ContinuousMap.id ↑I).prodMap (Hom.hom (X.cubeInclToSk α))))) z := by
          rw [hsidisks]; rfl
        exact h₂
      rw [hsi_pt]
      -- Evaluate the remaining chain.
      simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply,
        ContinuousMap.prodMap_apply, ContinuousMap.coe_id, ContinuousMap.prodSwap_apply,
        TopCat.cubeSplitAtLast]
      -- Reduce hom.right ∘ inv.right = id pointwise via congrArg over morphism equation.
      have hhi : ∀ z : ↑(Arrow.mk (cubeBoundaryIncl (n + 1))).right,
          (Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).hom))
            ((Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift (n + 1)).inv)) z) = z := by
        intro z
        have h : (diskPair.homeoCubePairULift (n + 1)).inv.right ≫
            (diskPair.homeoCubePairULift (n + 1)).hom.right = 𝟙 _ := Arrow.inv_hom_id_right _
        exact congrArg (fun (f : (Arrow.mk (cubeBoundaryIncl (n + 1))).right ⟶
              (Arrow.mk (cubeBoundaryIncl (n + 1))).right) => (Hom.hom f) z) h
      rw [hhi]
      -- Express hom.right x via its ULift representation.
      have hxy : (Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift n).hom)) x =
          ⟨((Hom.hom (Arrow.Hom.right (diskPair.homeoCubePairULift n).hom)) x).down⟩ := rfl
      rw [hxy]
      -- Unwrap `hom_ofHom`, evaluate the lambda's `match`,
      -- then apply `Homeomorph.apply_symm_apply`.
      change _ = Prod.map id (Hom.hom (X.cubeInclToSk α))
          ((Cube.splitAtLast (Cube.splitAtLast.symm
              ⟨t, ((Hom.hom (Arrow.Hom.right
                (diskPair.homeoCubePairULift n).hom)) x).down⟩)).1,
            ⟨(Cube.splitAtLast (Cube.splitAtLast.symm
              ⟨t, ((Hom.hom (Arrow.Hom.right
                (diskPair.homeoCubePairULift n).hom)) x).down⟩)).2⟩)
      rw [Homeomorph.apply_symm_apply]; rfl

end IProd


/-- `IProd` -/
noncomputable def IProd : RelCWComplex where
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
