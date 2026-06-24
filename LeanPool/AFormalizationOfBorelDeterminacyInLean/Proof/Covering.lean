/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.GaleStewart
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.BuildLevelwise

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Covering

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame
open CategoryTheory
open Descriptive Tree Stream'.Discrete

noncomputable section «Section1»
variable {k m n : ℕ} {p : Player}
namespace Covering
/-- a tree that is pruned and nonempty as required for determinacy -/
def PTrees := Σ' (T : Trees), IsPruned T.2 ∧ [] ∈ T.2
@[simp] lemma pTrees_isPruned (T : PTrees) : IsPruned T.1.2 := T.2.1
@[simp] lemma pTrees_ne (T : PTrees) : [] ∈ T.1.2 := T.2.2
end Covering
namespace ResStrategy
variable {T : Covering.PTrees} (S : ResStrategy T.1 p k)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def chooseSucc : ResStrategy T.1 p m :=
  fun x hp _ ↦ if h' : x.val.length ≤ k then S x hp h' else Classical.choice (T.2.1 x)
@[simp] lemma res_chooseSucc (h : k ≤ m) : S.chooseSucc.res h = S := by
  ext _ _ hl; simp [chooseSucc, res, hl]
lemma res_surjective (h : m ≤ k) : (res h (T := T.1) (p := p)).Surjective :=
  fun S ↦ ⟨_, S.res_chooseSucc h⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def chooseSystem : StrategySystem T.1 p where
  str k := S.chooseSucc
  con k := by ext x; simp [chooseSucc, res]
lemma chooseSystem_self : S.chooseSystem.str k = S := by ext _ _ hl; simp [chooseSucc, hl]
lemma str_surjective : (fun (S : StrategySystem T.1 p) ↦ S.str k).Surjective :=
  fun S ↦ ⟨_, S.chooseSystem_self⟩
end ResStrategy
namespace Covering
/-- Auxiliary declaration for the Borel determinacy formalization. -/
structure PTreesS where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  tree : PTrees
/-- a map of strategies whose output on the first k levels only depends on
  the input on the first k levels -/
@[ext] structure LvlStratHom (T U : PTreesS) where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  toFun : ∀ p k, ResStrategy T.tree.1 p k → ResStrategy U.tree.1 p k
  con : ∀ p {k m} (h : m ≤ k) S, (toFun p k S).res h = toFun p m (S.res h)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def LvlStratHom.id (T : PTreesS) : LvlStratHom T T where
  toFun p k := _root_.id
  con := by simp
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def LvlStratHom.comp {T U V : PTreesS} (g : LvlStratHom U V) (f : LvlStratHom T U) :
  LvlStratHom T V where
  toFun p k := g.toFun p k ∘ f.toFun p k
  con := by simp [g.con, f.con]
instance : Category PTreesS where
  Hom := LvlStratHom
  id := LvlStratHom.id
  comp f g := LvlStratHom.comp g f
@[simp] lemma LvlStratHom.id_toFun (T : PTreesS) :
  LvlStratHom.toFun (𝟙 T) p k = _root_.id := rfl
@[simp] lemma LvlStratHom.comp_toFun {T U V : PTreesS} (f : T ⟶ U) (g : U ⟶ V) :
  LvlStratHom.toFun (f ≫ g) p k = LvlStratHom.toFun g p k ∘ LvlStratHom.toFun f p k := rfl
@[ext] lemma LvlStratHom.ext' {T U : PTreesS} {f g : T ⟶ U} (h : f.toFun = g.toFun) : f = g :=
  LvlStratHom.ext h
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def LvlStratHom.system (p : Player) : PTreesS ⥤ Type where
  obj T := StrategySystem T.tree.1 p
  map {T U} f := TypeCat.ofHom fun S : StrategySystem T.tree.1 p ↦ ({
    str := fun k ↦ f.toFun p k (S.str k),
    con := by simp [f.con]
  } : StrategySystem U.tree.1 p)
  map_id _ := rfl
  map_comp _ _ := rfl
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev LvlStratHom.systemToObj {T : PTreesS} (S : StrategySystem T.tree.1 p) :
    (LvlStratHom.system p).obj T :=
  cast (by dsimp [LvlStratHom.system] :
    StrategySystem T.tree.1 p = (LvlStratHom.system p).obj T) S
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev LvlStratHom.systemOfObj {T : PTreesS} (S : (LvlStratHom.system p).obj T) :
    StrategySystem T.tree.1 p :=
  cast (by dsimp [LvlStratHom.system] :
    (LvlStratHom.system p).obj T = StrategySystem T.tree.1 p) S
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def LvlStratHom.global (p : Player) : PTreesS ⥤ Type where
  obj T := Strategy T.tree.1.2 p
  map {T U} f := TypeCat.ofHom fun S : Strategy T.tree.1.2 p ↦
    strategyEquivSystem.symm
      (LvlStratHom.systemOfObj
        (ConcreteCategory.hom ((system p).map f)
          (LvlStratHom.systemToObj (strategyEquivSystem S))))
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro S
    apply strategyEquivSystem.injective
    simp [LvlStratHom.systemToObj, LvlStratHom.systemOfObj]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev LvlStratHom.globalToObj {T : PTreesS} (S : Strategy T.tree.1.2 p) :
    (LvlStratHom.global p).obj T :=
  cast (by dsimp [LvlStratHom.global] :
    Strategy T.tree.1.2 p = (LvlStratHom.global p).obj T) S
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev LvlStratHom.globalOfObj {T : PTreesS} (S : (LvlStratHom.global p).obj T) :
    Strategy T.tree.1.2 p :=
  cast (by dsimp [LvlStratHom.global] :
    (LvlStratHom.global p).obj T = Strategy T.tree.1.2 p) S

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def bodyLiftExists {T U : PTrees} (toHom : T.1 ⟶ U.1) (str : PTreesS.mk T ⟶ PTreesS.mk U) :=
  ∀ {p : Player} {S : Strategy T.1.2 p}
  (y : body (LvlStratHom.globalOfObj
    (ConcreteCategory.hom ((LvlStratHom.global p).map str)
      (LvlStratHom.globalToObj S))).pre.subtree),
  ∃ x : body S.pre.subtree,
    (Tree.bodyFunctor.map toHom ⟨x, body_mono S.pre.subtree_sub x.prop⟩).val
    = y.val
lemma bodyLiftExists_iff_system
  {T U : PTrees} (toHom : T.1 ⟶ U.1) (str : PTreesS.mk T ⟶ PTreesS.mk U) :
  bodyLiftExists toHom str ↔ ∀ {p : Player} {S : StrategySystem T.1 p}
  (y : bodySystem.obj U.1),
  consistent y (LvlStratHom.systemOfObj
    (ConcreteCategory.hom ((LvlStratHom.system p).map str)
      (LvlStratHom.systemToObj S))) →
  ∃ x : bodySystem.obj T.1, consistent x S ∧ bodySystem.map toHom x = y := by
  constructor <;> intro h p S y
  · intro yc; obtain ⟨S, rfl⟩ := strategyEquivSystem.surjective S
    rw [← bodyEquivSystem_strat'] at yc; obtain ⟨x, hx⟩ := h ⟨_, yc⟩
    use bodyEquivSystem.hom.app _ ⟨x.val, body_mono S.pre.subtree_sub x.prop⟩
    constructor
    · exact (bodyEquivSystem_strat _).mp x.prop
    apply ((isIso_iff_bijective (bodyEquivSystem.inv.app _)).mp inferInstance).1
    rw [← naturality_apply_types, Iso.hom_inv_id_app_apply]
    exact Subtype.ext hx
  · let y' : Tree.bodyFunctor.obj U.1 := ⟨y.val, body_mono (PreStrategy.subtree_sub _) y.prop⟩
    obtain ⟨x, ⟨hxc, hxe⟩⟩ := h
      (bodyEquivSystem.hom.app _ y') <| (bodyEquivSystem_strat _).mp y.prop
    have hmem : (bodyEquivSystem.inv.app T.1 x).val ∈ body S.pre.subtree := by
      simpa [LvlStratHom.globalToObj] using
        (bodyEquivSystem_strat' (T := T.1) (S := strategyEquivSystem S)).mpr hxc
    use ⟨(bodyEquivSystem.inv.app T.1 x).val, hmem⟩
    have hmap : (bodyFunctor.map toHom) (bodyEquivSystem.inv.app T.1 x) = y' := by
      apply ((isIso_iff_bijective (bodyEquivSystem.hom.app U.1)).mp inferInstance).1
      rw [naturality_apply_types]
      have hpoint : (bodyEquivSystem.hom.app T.1) ((bodyEquivSystem.inv.app T.1) x) = x := by
        change ((bodyEquivSystem.inv.app T.1 ≫ bodyEquivSystem.hom.app T.1) x) = x
        rw [← NatTrans.comp_app, bodyEquivSystem.inv_hom_id]
        rfl
      rwa [hpoint]
    simpa [y'] using congrArg Subtype.val hmap

end Covering
/-- a covering used in the proof of Borel determinacy, given by a length preserving map of nodes
and a map of strategies and satisfying a lifting condition on plays consistent with the
strategy -/
@[ext (flat := false)] structure Covering (T U : Covering.PTrees) where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  toHom : T.1 ⟶ U.1
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  str : Covering.PTreesS.mk T ⟶ Covering.PTreesS.mk U
  h_body : Covering.bodyLiftExists toHom str
namespace Covering
instance : Category PTrees where
  Hom := Covering
  id T := ⟨𝟙 T.1, LvlStratHom.id _, fun {p} {S} y ↦ ⟨y, by
    exact congrArg Subtype.val
      (bodyFunctor.map_id_apply T.1 ⟨y.val, body_mono S.pre.subtree_sub y.prop⟩)⟩⟩
  comp f g := ⟨f.toHom ≫ g.toHom, f.str ≫ g.str, fun {p} {S} x ↦ by as_aux_lemma =>
    obtain ⟨y, hy⟩ := g.h_body (S :=
      LvlStratHom.globalOfObj
        (ConcreteCategory.hom ((LvlStratHom.global p).map f.str)
          (LvlStratHom.globalToObj S))) (cast (by simp) x)
    obtain ⟨z, hz⟩ := f.h_body y
    use z
    have hy' :
        ((ConcreteCategory.hom (bodyFunctor.map g.toHom))
          ⟨↑y, body_mono (PreStrategy.subtree_sub _) y.prop⟩).val = x.val := by
      simpa using hy
    rw [← hy']
    have hybody :
        (bodyFunctor.map f.toHom) ⟨↑z, body_mono S.pre.subtree_sub z.prop⟩ =
          ⟨↑y, body_mono (PreStrategy.subtree_sub _) y.prop⟩ :=
      Subtype.ext hz
    rw [← hybody]
    rw [Functor.map_comp_apply]⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def PTreeForget : PTrees ⥤ Trees where
  obj T := T.1
  map f := f.toHom
@[simp, simp_lengths] lemma id_covering_toHom (T : PTrees) :
  Covering.toHom (𝟙 T) = 𝟙 _ := rfl
@[simp] lemma id_covering_str (T : PTrees) :
  Covering.str (𝟙 T) = 𝟙 _ := rfl
@[simp, simp_lengths] lemma comp_covering_toHom {T U V : PTrees} (f : T ⟶ U) (g : U ⟶ V) :
  (f ≫ g).toHom = f.toHom ≫ g.toHom := rfl
@[simp] lemma comp_covering_str {T U V : PTrees} (f : T ⟶ U) (g : U ⟶ V) :
  (f ≫ g).str = f.str ≫ g.str := rfl
lemma comp_covering_str_apply (S T U : PTrees) (f : S ⟶ T) (g : T ⟶ U) A :
  (f ≫ g).str.toFun p k A = g.str.toFun p k (f.str.toFun p k A) := by dsimp
@[ext] lemma ext' {T U : PTrees} {f g : T ⟶ U} (h1 : f.toHom = g.toHom)
  (h2 : f.str = g.str) : f = g := Covering.ext h1 h2

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Fixing k {T U : PTrees} (f : T ⟶ U) :=
  ∃ _ : Tree.Fixing k f.toHom, ∀ p, f.str.toFun p k = ResStrategy.fromMap f.toHom
@[simp] lemma fixing_id k T : Fixing k (𝟙 T) := by
  use (by synthFixing); intros; ext; simp
lemma fixing_comp k {T U V : PTrees} (f : T ⟶ U) (g : U ⟶ V)
  (hf : Fixing k f) (hg : Fixing k g) : Fixing k (f ≫ g) := by
  have _ := hf.1; have _ := hg.1
  use (by simp_rw [comp_covering_toHom]; infer_instance)
  intros; ext; simp [hf.2, hg.2]
lemma fixing_snd_mon {k m} (hm : k ≤ m) {T U : PTrees} (f : T ⟶ U)
  (h : Fixing m f) (p : Player) :
  f.str.toFun p k = ResStrategy.fromMap (f := f.toHom) (h := h.1.mon hm) := by
  ext S'; obtain ⟨S', rfl⟩ := ResStrategy.res_surjective hm S'
  have hs := by simpa using congr_arg (ResStrategy.res hm) (congr_fun (h.2 p) S')
  rw [← hs, f.str.con]
lemma fixing_mon {S T} (f : S ⟶ T) (h : Fixing k f) (hn : n ≤ k) :
  Fixing n f := ⟨h.1.mon hn, fun _ ↦ fixing_snd_mon hn _ h _⟩

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Games := Σ' (A : Type*) (G : Game A), IsPruned G.tree ∧ [] ∈ G.tree
@[simp] lemma games_isPruned (G : Games) : IsPruned G.2.1.tree := G.2.2.1
@[simp] lemma games_ne (G : Games) : [] ∈ G.2.1.tree := G.2.2.2
instance (G : Games) : TopologicalSpace G.1 := ⊥
instance (G : Games) : DiscreteTopology G.1 where eq_bot := rfl
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev Games.tree (G : Games) : PTrees := ⟨⟨G.1, G.2.1.tree⟩, G.2.2⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext] structure Games.Covering (G' : Games) (G : Games) extends
  GaleStewartGame.Covering G'.tree G.tree where
  hpre : (Tree.bodyFunctor.map toHom)⁻¹' (G.2.1.payoff) = G'.2.1.payoff
lemma covering_hpre_pl {G' G} (f : Games.Covering G' G) (p : Player) :
  (Tree.bodyFunctor.map f.toHom)⁻¹' (p.payoff G.2.1) = p.payoff G'.2.1 := by
  cases p
  · simpa using f.hpre
  · exact congrArg (fun s => sᶜ) f.hpre
lemma covering_winning {G' G} (f : Games.Covering G' G) {p : Player}
  {S : Strategy G'.tree.1.2 p} (h : S.pre.IsWinning) :
  (LvlStratHom.globalOfObj
    (ConcreteCategory.hom ((LvlStratHom.global p).map f.str)
      (LvlStratHom.globalToObj S))).pre.IsWinning := by
  intro y hy; obtain ⟨x, rfl⟩ := f.h_body ⟨y, hy⟩
  obtain ⟨xg, hxg, hxval⟩ := h x.prop
  have hxg' : ⟨x.val, body_mono S.pre.subtree_sub x.prop⟩ ∈ p.payoff G'.2.1 := by
    rwa [← (Subtype.ext hxval : xg = ⟨x.val, body_mono S.pre.subtree_sub x.prop⟩)]
  have hxpre :
      (Tree.bodyFunctor.map f.toHom) ⟨x.val, body_mono S.pre.subtree_sub x.prop⟩ ∈
        p.payoff G.2.1 := by
    change ⟨x.val, body_mono S.pre.subtree_sub x.prop⟩ ∈
      (Tree.bodyFunctor.map f.toHom)⁻¹' p.payoff G.2.1
    rwa [covering_hpre_pl f p]
  exact ⟨(Tree.bodyFunctor.map f.toHom) ⟨x.val, body_mono S.pre.subtree_sub x.prop⟩,
    hxpre, rfl⟩

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Games.IsUnravelable G := ∀ k, ∃ (G' : Games) (f : Games.Covering G' G),
  Fixing k f.toCovering ∧ IsClopen G'.2.1.payoff
lemma Games.IsUnravelable.isDetermined {G : Games} (h : G.IsUnravelable) :
  G.2.1.IsDetermined :=
  let ⟨_, f, _, h⟩ := h 0
  let ⟨p, s, hw⟩ := Game.gale_stewart h.1 (games_isPruned _)
  ⟨p, ⟨LvlStratHom.globalOfObj
    (ConcreteCategory.hom ((LvlStratHom.global p).map f.str)
      (LvlStratHom.globalToObj s)), covering_winning f hw⟩⟩

end Covering
end «Section1»
end GaleStewartGame
