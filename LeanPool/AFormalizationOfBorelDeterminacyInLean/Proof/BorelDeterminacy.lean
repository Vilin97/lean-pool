/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.One.Strat
public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.CoveringLim
public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.InvLimitNat
public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.TreeLift
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.Strat

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.BorelDeterminacy

Auxiliary declarations for the Borel determinacy formalization.
-/

@[expose] public section


namespace GaleStewartGame
open Descriptive Tree Covering Stream'.Discrete
open MeasureTheory CategoryTheory
noncomputable section «Section1»

namespace BorelDet
variable {A : Type} {G : Game A} {k : ℕ} (hyp : Hyp G k)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev Gh : Games := ⟨A, G, hyp.pruned, hyp.nonempty⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev G'h : Games :=
  ⟨A' (hyp := hyp), G' (hyp := hyp), gameTree_isPruned (hyp := hyp),
    gameTree_ne (hyp := hyp)⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def treeCov : (G'h hyp).tree ⟶ (Gh hyp).tree where
  toHom := π (hyp := hyp)
  str := {
    toFun := by rintro (_ | _) <;> [apply Zero.stratMap; apply One.stratMap]
    con := by rintro (_ | _) _ _ _ _ <;> rfl
  }
  h_body := by
    rintro (_ | _)
    · apply Zero.body_stratMap
    · apply One.body_stratMap
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def gameCov : Games.GameCovering (G'h hyp) (Gh hyp) where
  toCovering := treeCov hyp
  hpre := game_payoff hyp
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
lemma main_lemma {G : Games} (hC : IsClosed G.2.1.payoff) : G.IsUnravelable :=
  fun k ↦ ⟨G'h (k := k) ⟨hC, G.2.2.1, G.2.2.2⟩, gameCov _, by
    unfold gameCov treeCov
    let hyp' : Hyp G.2.1 k := ⟨hC, G.2.2.1, G.2.2.2⟩
    refine ⟨(treeHom_fixing (hyp := hyp')).mon (by omega), ?_⟩
    intro p
    cases p
    · funext R x hp hl
      apply ExtensionsAt.ext_valT'
      have hshort : x.val.length ≤ 2 * k := le_trans hl (by omega)
      conv => simp [Zero.stratMap, hshort, ResStrategy.fromMap, ResStrategy.res, π]
      rfl
    · funext R x hp hl
      apply ExtensionsAt.ext_valT'
      have hshort : x.val.length ≤ 2 * k := le_trans hl (by omega)
      conv => simp [One.stratMap, hshort, ResStrategy.fromMap, ResStrategy.res, π]
      rfl, payoff_clopen⟩
end BorelDet
namespace BorelDet'

variable (T : PTrees) (W : Set (body T.1.2)) {n : ℕ}
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def extendToGame : Games where
  fst := T.1.1
  snd := {
    fst := {
      tree := T.1.2
      payoff := W
    }
    snd := T.2
  }

/-- a slight strengthening of Martin's notion of unravelable games to facilitate Borel induction -/
def UniversallyUnravelable :=
  ∀ ⦃T'⦄ (f : T' ⟶ T), (extendToGame T' <| (bodyFunctor.map f.toHom)⁻¹' W).IsUnravelable
lemma unravelable_complement (h : UniversallyUnravelable T W) :
  UniversallyUnravelable T Wᶜ := by
  intro _ f n; obtain ⟨G, f, ht, hc⟩ := h f n
  use extendToGame G.tree G.2.1.payoffᶜ
  use { toCovering := f.toCovering, hpre := (by
    rw [← f.hpre]
    ext x
    rfl) }, ht
  exact hc.compl
lemma closed_unravelable (h : IsClosed W) : UniversallyUnravelable T W := by
  intro T' f; apply BorelDet.main_lemma
  exact h.preimage (LenHom.bodyMap_continuous f.toHom)
lemma open_unravelable (h : IsOpen W) : UniversallyUnravelable T W := by
  rw [← compl_compl W]; apply unravelable_complement; apply closed_unravelable
  exact isClosed_compl_iff.mpr h
lemma unravelable_preimage {T' T : PTrees} (f : T' ⟶ T) W (h : UniversallyUnravelable T W) :
  UniversallyUnravelable T' ((bodyFunctor.map f.toHom)⁻¹' W) := by
  intro _ g
  convert h (g ≫ f) using 2
  ext x
  simp only [comp_covering_toHom, CategoryTheory.Functor.map_comp]
  rfl

/-- Auxiliary declaration for the Borel determinacy formalization. -/
structure PartiallyUnravelled (n : ℕ) where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  carrier : PTrees
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  sets : ℕ → PSigma (UniversallyUnravelable carrier)
  unrav : ∀ m < n, IsOpen (sets m).1
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def PartiallyUnravelled.continue (G : PartiallyUnravelled n) (k : ℕ) :
  Σ' (G' : PartiallyUnravelled (n + 1)) (f : G'.carrier ⟶ G.carrier),
  Covering.Fixing (k + n) f ∧
  ∀ n, (G'.sets n).1 = (bodyFunctor.map f.toHom)⁻¹' (G.sets n).1 := by
  apply Classical.choice
  have ⟨car, ⟨f, ⟨hf, h⟩⟩⟩ := (G.sets n).2 (𝟙 G.carrier) (k + n)
  constructor
  use {
    carrier := car.tree
    sets := fun n ↦ ⟨(bodyFunctor.map f.toHom)⁻¹' (G.sets n).1,
      unravelable_preimage _ _ (G.sets n).2⟩
    unrav := by
      intro m hm; rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
      · exact (G.unrav m hm).preimage (LenHom.bodyMap_continuous f.toHom)
      · have hf := f.hpre
        have hfpre : (bodyFunctor.map f.toHom)⁻¹' (G.sets m).1 = car.2.1.payoff := by
          rw [← hf]
          ext x
          simp only [extendToGame, id_covering_toHom,
            CategoryTheory.Functor.map_id]
          rfl
        change IsOpen ((bodyFunctor.map f.toHom)⁻¹' (G.sets m).1)
        rw [hfpre]
        exact h.isOpen
  }, f.toCovering, hf, fun _ ↦ rfl
variable (G : PartiallyUnravelled 0) (k : ℕ)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def unravelNth : ∀ n, PartiallyUnravelled n
  | 0 => G
  | n + 1 => ((unravelNth n).continue k).1
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def unravelFunctor : ℕᵒᵖ ⥤ PTrees :=
  natFreeCat.symm ⟨fun n ↦ (unravelNth G k n).carrier,
    fun n ↦ ((unravelNth G k n).continue k).2.1⟩
lemma unravelFunctor_succ n :
  (unravelFunctor G k).map (homOfLE (Nat.le_succ n)).op
    = ((unravelNth G k n).continue k).2.1 := by
  change (natFreeCat (unravelFunctor G k)).2 _ = _
  simp [unravelFunctor]
  rfl
lemma unravelFunctor_fixing n :
  Covering.Fixing (k + n) ((unravelFunctor G k).map (homOfLE (Nat.le_succ n)).op) := by
  rw [unravelFunctor_succ]
  exact ((unravelNth G k n).continue k).2.2.1
lemma unravelFunctor_preimage m n :
  (Tree.bodyFunctor.map
    ((unravelFunctor G k).map (homOfLE (by simp : 0 ≤ n)).op).toHom)⁻¹' (G.sets m).1
  = ((unravelNth G k n).sets m).1 := by
  induction n with
  | zero =>
    ext x
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, id_covering_toHom]
    change x ∈ (G.sets m).1 ↔ x ∈ (G.sets m).1
    rfl
  | succ n ih =>
    have hcomp : (homOfLE (by simp : 0 ≤ n + 1)).op
      = (homOfLE (Nat.le_succ n)).op ≫ (homOfLE (by simp : 0 ≤ n)).op :=
      by apply Subsingleton.elim
    rw [hcomp, CategoryTheory.Functor.map_comp]
    simp_rw [unravelFunctor_succ]
    let fc := ((unravelNth G k n).continue k).2.1
    let gc := (unravelFunctor G k).map (homOfLE (by simp : 0 ≤ n)).op
    change (ConcreteCategory.hom (bodyFunctor.map (fc.toHom ≫ gc.toHom))) ⁻¹'
      (G.sets m).1 = _
    erw [bodyFunctor.map_comp]
    change (ConcreteCategory.hom (bodyFunctor.map fc.toHom)) ⁻¹'
      ((ConcreteCategory.hom (bodyFunctor.map gc.toHom)) ⁻¹' (G.sets m).1) = _
    erw [ih]
    exact (((unravelNth G k n).continue k).2.2.2 m).symm
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def unravelLim : Limits.Cone (unravelFunctor G k) :=
  limCone (unravelFunctor_fixing G k)
lemma unravelLim_fixing : Covering.Fixing k ((unravelLim G k).π.app ⟨0⟩) :=
  limCone_fixing (unravelFunctor_fixing G k) 0

/-- the σ-algebra of universally unravelable sets -/
@[reducible]
def unravelableAsMeasurable : MeasurableSpace (Tree.body T.1.2) where
  MeasurableSet' := UniversallyUnravelable T
  measurableSet_empty := open_unravelable T ∅ isOpen_empty
  measurableSet_compl := unravelable_complement T
  measurableSet_iUnion := by
    intro W hW T' f k
    let G0: PartiallyUnravelled 0 := {
      carrier := T'
      sets := fun n ↦ ⟨(Tree.bodyFunctor.map f.toHom)⁻¹' (W n), unravelable_preimage _ _ (hW n)⟩
      unrav := by simp
    }
    let F := unravelFunctor G0 k
    let G := (unravelLim G0 k).pt; let π := (unravelLim G0 k).π
    have hO : IsOpen ((Tree.bodyFunctor.map (π.app ⟨0⟩).toHom)⁻¹'
      ((Tree.bodyFunctor.map f.toHom)⁻¹' (⋃i, W i))) := by
      erw [Set.preimage_iUnion]
      apply isOpen_iUnion
      intro n
      change IsOpen ((ConcreteCategory.hom (bodyFunctor.map (π.app ⟨0⟩).toHom)) ⁻¹'
        ((ConcreteCategory.hom (bodyFunctor.map f.toHom)) ⁻¹' W n))
      have hnat : π.app ⟨0⟩ = π.app ⟨n + 1⟩ ≫ F.map (homOfLE (by omega)).op := by
        rw [← CategoryTheory.Category.id_comp (π.app ⟨0⟩)]
        exact π.naturality (homOfLE (by omega : 0 ≤ n + 1)).op
      rw [hnat, comp_covering_toHom]
      change IsOpen
        ((ConcreteCategory.hom (bodyFunctor.map
          ((π.app ⟨n + 1⟩).toHom ≫ (F.map (homOfLE (by omega : 0 ≤ n + 1)).op).toHom)))⁻¹'
        ((Tree.bodyFunctor.map f.toHom)⁻¹' W n))
      rw [bodyFunctor.map_comp]
      let a := bodyFunctor.map (π.app ⟨n + 1⟩).toHom
      let b := bodyFunctor.map (F.map (homOfLE (by omega : 0 ≤ n + 1)).op).toHom
      change IsOpen ((ConcreteCategory.hom a)⁻¹'
        ((ConcreteCategory.hom b)⁻¹' ((Tree.bodyFunctor.map f.toHom)⁻¹' W n)))
      have hinner : (ConcreteCategory.hom b)⁻¹' ((Tree.bodyFunctor.map f.toHom)⁻¹' W n) =
          ((unravelNth G0 k (n + 1)).sets n).1 :=
        unravelFunctor_preimage G0 k n (n + 1)
      rw [hinner]
      exact ((unravelNth G0 k (n + 1)).unrav n (by omega)).preimage
        (Tree.LenHom.bodyMap_continuous _)
    obtain ⟨G', g, hgT, _⟩ := open_unravelable _ _ hO (𝟙 _) k
    let gc : G'.tree ⟶ G := g.toCovering
    use G', {
      toCovering := gc ≫ π.app ⟨0⟩
      hpre := by
        rw [← g.hpre]
        let Gcone :=
          ((Functor.const ℕᵒᵖ).obj (unravelLim G0 k).pt).obj (Opposite.op 0)
        have hcompMap : bodyFunctor.map (gc ≫ π.app ⟨0⟩).toHom =
            bodyFunctor.map gc.toHom ≫ bodyFunctor.map (π.app ⟨0⟩).toHom := by
          change bodyFunctor.map (gc.toHom ≫ (π.app ⟨0⟩).toHom) = _
          exact bodyFunctor.map_comp gc.toHom (π.app ⟨0⟩).toHom
        have hidMap : bodyFunctor.map ((𝟙 Gcone : Gcone ⟶ Gcone).toHom) = 𝟙 _ := by
          change bodyFunctor.map (𝟙 Gcone.1) = _
          exact bodyFunctor.map_id Gcone.1
        simp only [extendToGame]
        erw [hcompMap]
        conv => rhs; arg 2; rw [hidMap]
        rfl
    }, fixing_comp k gc _ hgT <| unravelLim_fixing G0 k

lemma borel_unravelable : borel _ ≤ unravelableAsMeasurable T :=
  MeasurableSpace.generateFrom_le <| open_unravelable T
end BorelDet'

/-- Borel games are determined -/
lemma Games.borel_determinacy (G : Games.{0}) (h : MeasurableSet[borel _] G.2.1.payoff) :
  G.2.1.IsDetermined := by
  let Gid := BorelDet'.extendToGame G.tree
    ((ConcreteCategory.hom (bodyFunctor.map ((𝟙 G.tree : G.tree ⟶ G.tree).toHom)))⁻¹'
      G.2.1.payoff)
  have hgame : Gid.2.1 = G.2.1 := by
    have hmapId : bodyFunctor.map ((𝟙 G.tree : G.tree ⟶ G.tree).toHom) = 𝟙 _ := by
      change bodyFunctor.map (𝟙 G.tree.1) = _
      exact bodyFunctor.map_id G.tree.1
    change (BorelDet'.extendToGame G.tree
      ((ConcreteCategory.hom (bodyFunctor.map ((𝟙 G.tree : G.tree ⟶ G.tree).toHom)))⁻¹'
        G.2.1.payoff)).2.1 = G.2.1
    rw [hmapId]
    rfl
  rw [← hgame]
  change Gid.2.1.IsDetermined
  simpa [Gid] using (BorelDet'.borel_unravelable G.tree _ h (𝟙 G.tree)).isDetermined
theorem borel_determinacy {A : Type} {G : Game A}
  (hB : MeasurableSet[borel _] G.payoff) (hP : Tree.IsPruned G.tree) : G.IsDetermined := by
  by_cases h : [] ∈ G.tree
  · exact Games.borel_determinacy ⟨A, G, hP, h⟩ hB
  · rw [G.empty_of_tree (by simpa)]
    exact ⟨Player.zero, PreStrategy.existsWinning_empty⟩

end «Section1»
end GaleStewartGame
