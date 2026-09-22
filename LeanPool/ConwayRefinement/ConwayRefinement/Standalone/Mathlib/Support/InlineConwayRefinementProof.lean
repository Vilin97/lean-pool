/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/

module
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.InlineConwayRefinement
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.InlineSurreal
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.ConwayRefinement
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.ConwayRefinementConsequences
public import LeanPool.ConwayRefinement.CombinatorialGames.Game.Functor
import Mathlib.Tactic.Linarith
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.ConwayRefinementProof

/-! # Inline Conway Refinement Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.InlineConwayRefinement

universe u

abbrev SupportGame := ConwayRefinement.Standalone.InlineSurreal.IGame

noncomputable def Game.toSupport : Game.{u} → SupportGame.{u}
  | .mk Left Right left right =>
      ConwayRefinement.Standalone.InlineSurreal.ofSets
        (ConwayRefinement.Standalone.InlineSurreal.Player.cases
          (Set.range fun i : Left ↦ Game.toSupport (left i))
          (Set.range fun i : Right ↦ Game.toSupport (right i))) trivial

@[expose] noncomputable def Game.fromSupport (x : SupportGame.{u}) : Game.{u} :=
  ConwayRefinement.Standalone.InlineSurreal.IGame.ofSetsRecOn x fun s t _ _ hs ht ↦
    .mk (Shrink s) (Shrink t)
      (fun i ↦
        let z := (equivShrink s).symm i
        hs z.1 z.2)
      (fun i ↦
        let z := (equivShrink t).symm i
        ht z.1 z.2)

theorem Game.fromSupport_ofSets (s t : Set SupportGame.{u}) [Small.{u} s] [Small.{u} t] :
    Game.fromSupport
        (ConwayRefinement.Standalone.InlineSurreal.ofSets
          (ConwayRefinement.Standalone.InlineSurreal.Player.cases s t) trivial) =
      .mk (Shrink s) (Shrink t)
        (fun i ↦ Game.fromSupport ((equivShrink s).symm i).1)
        (fun i ↦ Game.fromSupport ((equivShrink t).symm i).1) := by
  rw [Game.fromSupport,
    ConwayRefinement.Standalone.InlineSurreal.IGame.ofSetsRecOn_ofSets]
  simp only [Game.fromSupport]

theorem Game.toSupport_fromSupport (x : SupportGame.{u}) :
    Game.toSupport (Game.fromSupport x) = x := by
  induction x using ConwayRefinement.Standalone.InlineSurreal.IGame.ofSetsRecOn with
  | ofSets s t ihs iht =>
      simp only [Game.fromSupport,
        ConwayRefinement.Standalone.InlineSurreal.IGame.ofSetsRecOn_ofSets, Game.toSupport]
      apply ConwayRefinement.Standalone.InlineSurreal.IGame.ext
      intro p
      simp only [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets]
      cases p
      · ext z
        constructor
        · rintro ⟨i, rfl⟩
          let y := (equivShrink s).symm i
          change Game.toSupport (Game.fromSupport y.1) ∈ s
          rw [ihs y.1 y.2]
          exact y.2
        · intro hz
          let i := equivShrink s ⟨z, hz⟩
          refine ⟨i, ?_⟩
          simpa only [i, Equiv.symm_apply_apply, Game.fromSupport] using ihs z hz
      · ext z
        constructor
        · rintro ⟨i, rfl⟩
          let y := (equivShrink t).symm i
          change Game.toSupport (Game.fromSupport y.1) ∈ t
          rw [iht y.1 y.2]
          exact y.2
        · intro hz
          let i := equivShrink t ⟨z, hz⟩
          refine ⟨i, ?_⟩
          simpa only [i, Equiv.symm_apply_apply, Game.fromSupport] using iht z hz

theorem Game.toSupport_neg (x : Game.{u}) :
    Game.toSupport (Game.neg x) = -Game.toSupport x := by
  induction x with
  | mk Left Right left right ihLeft ihRight =>
      rw [Game.neg_mk]
      simp only [Game.toSupport]
      rw [ConwayRefinement.Standalone.InlineSurreal.IGame.neg_ofSets]
      apply ConwayRefinement.Standalone.InlineSurreal.IGame.ext
      intro p
      simp only [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets]
      cases p
      · calc
          Set.range (fun i ↦ Game.toSupport (Game.neg (right i))) =
              Set.range (fun i ↦ -Game.toSupport (right i)) := by
                congr 1
                funext i
                exact ihRight i
          _ = -Set.range (fun i ↦ Game.toSupport (right i)) := by
                rw [← Set.image_neg_eq_neg]
                exact Set.range_comp' _ _
      · calc
          Set.range (fun i ↦ Game.toSupport (Game.neg (left i))) =
              Set.range (fun i ↦ -Game.toSupport (left i)) := by
                congr 1
                funext i
                exact ihLeft i
          _ = -Set.range (fun i ↦ Game.toSupport (left i)) := by
                rw [← Set.image_neg_eq_neg]
                exact Set.range_comp' _ _

theorem Game.toSupport_le (x y : Game.{u}) :
    Game.Le x y ↔ Game.toSupport x ≤ Game.toSupport y := by
  induction x, y using Sym2.GameAdd.recursion Game.move_wf with
  | _ x y ih =>
      cases x with
      | mk Lx Rx lx rx =>
        cases y with
        | mk Ly Ry ly ry =>
          rw [Game.le_mk]
          rw [ConwayRefinement.Standalone.InlineSurreal.IGame.le_iff_forall_lf]
          simp only [Game.toSupport,
            ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets, Set.forall_mem_range]
          constructor
          · rintro ⟨hLeft, hRight⟩
            constructor
            · intro i h
              exact hLeft i ((ih _ _ (Sym2.GameAdd.snd_fst (Game.Move.left i))).mpr h)
            · intro j h
              exact hRight j ((ih _ _ (Sym2.GameAdd.fst_snd (Game.Move.right j))).mpr h)
          · rintro ⟨hLeft, hRight⟩
            constructor
            · intro i h
              exact hLeft i ((ih _ _ (Sym2.GameAdd.snd_fst (Game.Move.left i))).mp h)
            · intro j h
              exact hRight j ((ih _ _ (Sym2.GameAdd.fst_snd (Game.Move.right j))).mp h)

theorem Game.Numeric.toSupport {x : Game.{u}} (h : Game.Numeric x) :
    ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric (Game.toSupport x) := by
  induction h with
  | mk hOrder hLeft hRight ihLeft ihRight =>
      rw [ConwayRefinement.Standalone.InlineSurreal.IGame.numeric_def]
      simp only [Game.toSupport,
        ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets, Set.forall_mem_range]
      constructor
      · intro i j
        obtain ⟨hij, hji⟩ := Game.less_iff _ _ |>.mp (hOrder i j)
        rw [lt_iff_le_not_ge]
        exact ⟨Game.toSupport_le _ _ |>.mp hij,
          fun h ↦ hji (Game.toSupport_le _ _ |>.mpr h)⟩
      · intro p
        cases p
        · intro y hy
          obtain ⟨i, rfl⟩ := hy
          exact ihLeft i
        · intro y hy
          obtain ⟨j, rfl⟩ := hy
          exact ihRight j

theorem Game.Numeric.fromSupport {x : SupportGame.{u}}
    (h : ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric x) :
    Game.Numeric (Game.fromSupport x) := by
  revert h
  induction x using ConwayRefinement.Standalone.InlineSurreal.IGame.ofSetsRecOn with
  | ofSets s t ihLeft ihRight =>
      intro h
      have hdef := ConwayRefinement.Standalone.InlineSurreal.IGame.numeric_def.mp h
      simp only [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets] at hdef
      rw [Game.fromSupport_ofSets]
      apply Game.Numeric.mk
      · intro i j
        let a := (equivShrink s).symm i
        let b := (equivShrink t).symm j
        have hab : a.1 < b.1 := hdef.1 a.1 a.2 b.1 b.2
        obtain ⟨hab, hba⟩ := lt_iff_le_not_ge.mp hab
        apply Game.less_iff _ _ |>.mpr
        constructor
        · apply Game.toSupport_le _ _ |>.mpr
          simpa only [Game.toSupport_fromSupport] using hab
        · intro hrev
          apply hba
          have := Game.toSupport_le _ _ |>.mp hrev
          simpa only [Game.toSupport_fromSupport] using this
      · intro i
        let a := (equivShrink s).symm i
        exact ihLeft a.1 a.2
          (hdef.2 ConwayRefinement.Standalone.InlineSurreal.Player.left a.1 a.2)
      · intro j
        let b := (equivShrink t).symm j
        exact ihRight b.1 b.2
          (hdef.2 ConwayRefinement.Standalone.InlineSurreal.Player.right b.1 b.2)

theorem Game.toSupport_add (x y : Game.{u}) :
    Game.toSupport (Game.add x y) = Game.toSupport x + Game.toSupport y := by
  induction x, y using Game.pairRec with
  | _ x y ih =>
      cases x with
      | mk Lx Rx lx rx =>
        cases y with
        | mk Ly Ry ly ry =>
          rw [Game.add_mk]
          simp only [Game.toSupport]
          rw [ConwayRefinement.Standalone.InlineSurreal.IGame.ofSets_add_ofSets]
          apply ConwayRefinement.Standalone.InlineSurreal.IGame.ext
          intro p
          simp only [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets]
          cases p
          · ext z
            simp only [Set.mem_range, Set.mem_union, Set.mem_image]
            constructor
            · rintro ⟨i | j, rfl⟩
              · left
                refine ⟨Game.toSupport (lx i), ⟨i, rfl⟩, ?_⟩
                exact (ih (lx i) (.mk Ly Ry ly ry)
                  (Prod.Lex.left _ _ (Game.Move.left i))).symm
              · right
                refine ⟨Game.toSupport (ly j), ⟨j, rfl⟩, ?_⟩
                exact (ih (.mk Lx Rx lx rx) (ly j)
                  (Prod.Lex.right _ (Game.Move.left j))).symm
            · rintro (⟨_, ⟨i, rfl⟩, rfl⟩ | ⟨_, ⟨j, rfl⟩, rfl⟩)
              · exact ⟨Sum.inl i, ih _ _ (Prod.Lex.left _ _ (Game.Move.left i))⟩
              · exact ⟨Sum.inr j, ih _ _ (Prod.Lex.right _ (Game.Move.left j))⟩
          · ext z
            simp only [Set.mem_range, Set.mem_union, Set.mem_image]
            constructor
            · rintro ⟨i | j, rfl⟩
              · left
                refine ⟨Game.toSupport (rx i), ⟨i, rfl⟩, ?_⟩
                exact (ih (rx i) (.mk Ly Ry ly ry)
                  (Prod.Lex.left _ _ (Game.Move.right i))).symm
              · right
                refine ⟨Game.toSupport (ry j), ⟨j, rfl⟩, ?_⟩
                exact (ih (.mk Lx Rx lx rx) (ry j)
                  (Prod.Lex.right _ (Game.Move.right j))).symm
            · rintro (⟨_, ⟨i, rfl⟩, rfl⟩ | ⟨_, ⟨j, rfl⟩, rfl⟩)
              · exact ⟨Sum.inl i, ih _ _ (Prod.Lex.left _ _ (Game.Move.right i))⟩
              · exact ⟨Sum.inr j, ih _ _ (Prod.Lex.right _ (Game.Move.right j))⟩

theorem Game.toSupport_mul (x y : Game.{u}) :
    Game.toSupport (Game.mul x y) = Game.toSupport x * Game.toSupport y := by
  induction x, y using Game.pairRec with
  | _ x y ih =>
      cases x with
      | mk Lx Rx lx rx =>
        cases y with
        | mk Ly Ry ly ry =>
          let x := Game.mk Lx Rx lx rx
          let y := Game.mk Ly Ry ly ry
          have option_eq (a b : Game) (ha : Game.Move a x) (hb : Game.Move b y) :
              Game.toSupport
                  (Game.add (Game.add (Game.mul a y) (Game.mul x b))
                    (Game.neg (Game.mul a b))) =
                ConwayRefinement.Standalone.InlineSurreal.IGame.mulOption
                  (Game.toSupport x) (Game.toSupport y)
                  (Game.toSupport a) (Game.toSupport b) := by
            rw [Game.toSupport_add, Game.toSupport_add, Game.toSupport_neg,
              ih a y (Prod.Lex.left y y ha), ih x b (Prod.Lex.right x hb),
              ih a b (Prod.Lex.left b y ha)]
            rfl
          rw [Game.mul_mk]
          simp only [Game.toSupport]
          rw [ConwayRefinement.Standalone.InlineSurreal.IGame.mul_eq]
          apply ConwayRefinement.Standalone.InlineSurreal.IGame.ext
          intro p
          simp only [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets]
          cases p
          · ext z
            simp only [Set.mem_range, Set.mem_image, Set.mem_union, Set.mem_prod]
            constructor
            · rintro ⟨ij | ij, rfl⟩
              · refine ⟨(Game.toSupport (lx ij.1), Game.toSupport (ly ij.2)), ?_, ?_⟩
                · left
                  exact ⟨⟨ij.1, rfl⟩, ⟨ij.2, rfl⟩⟩
                · exact (option_eq _ _ (Game.Move.left ij.1) (Game.Move.left ij.2)).symm
              · refine ⟨(Game.toSupport (rx ij.1), Game.toSupport (ry ij.2)), ?_, ?_⟩
                · right
                  exact ⟨⟨ij.1, rfl⟩, ⟨ij.2, rfl⟩⟩
                · exact (option_eq _ _ (Game.Move.right ij.1) (Game.Move.right ij.2)).symm
            · rintro ⟨⟨a, b⟩, (⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ | ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩), rfl⟩
              · exact ⟨Sum.inl (i, j),
                  option_eq _ _ (Game.Move.left i) (Game.Move.left j)⟩
              · exact ⟨Sum.inr (i, j),
                  option_eq _ _ (Game.Move.right i) (Game.Move.right j)⟩
          · ext z
            simp only [Set.mem_range, Set.mem_image, Set.mem_union, Set.mem_prod]
            constructor
            · rintro ⟨ij | ij, rfl⟩
              · refine ⟨(Game.toSupport (lx ij.1), Game.toSupport (ry ij.2)), ?_, ?_⟩
                · left
                  exact ⟨⟨ij.1, rfl⟩, ⟨ij.2, rfl⟩⟩
                · exact (option_eq _ _ (Game.Move.left ij.1) (Game.Move.right ij.2)).symm
              · refine ⟨(Game.toSupport (rx ij.1), Game.toSupport (ly ij.2)), ?_, ?_⟩
                · right
                  exact ⟨⟨ij.1, rfl⟩, ⟨ij.2, rfl⟩⟩
                · exact (option_eq _ _ (Game.Move.right ij.1) (Game.Move.left ij.2)).symm
            · rintro ⟨⟨a, b⟩, (⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ | ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩), rfl⟩
              · exact ⟨Sum.inl (i, j),
                  option_eq _ _ (Game.Move.left i) (Game.Move.right j)⟩
              · exact ⟨Sum.inr (i, j),
                  option_eq _ _ (Game.Move.right i) (Game.Move.left j)⟩

noncomputable def Surreal.toSupport (x : Surreal.{u}) :
    ConwayRefinement.Standalone.InlineSurreal.Surreal.{u} :=
  @ConwayRefinement.Standalone.InlineSurreal.Surreal.mk _ x.numeric.toSupport

theorem Surreal.toSupport_eq (x : Surreal.{u}) :
    x.toSupport = @ConwayRefinement.Standalone.InlineSurreal.Surreal.mk _ x.numeric.toSupport :=
  (rfl)

noncomputable def Surreal.fromSupport
    (x : ConwayRefinement.Standalone.InlineSurreal.Surreal.{u}) : Surreal.{u} :=
  ⟨Game.fromSupport x.out, Game.Numeric.fromSupport inferInstance⟩

theorem Surreal.fromSupport_game
    (x : ConwayRefinement.Standalone.InlineSurreal.Surreal.{u}) :
    (Surreal.fromSupport x).game = Game.fromSupport x.out := (rfl)

theorem Surreal.toSupport_fromSupport
    (x : ConwayRefinement.Standalone.InlineSurreal.Surreal.{u}) :
    (Surreal.fromSupport x).toSupport = x := by
  letI : ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric
      (Game.toSupport (Surreal.fromSupport x).game) :=
    (Surreal.fromSupport x).numeric.toSupport
  rw [Surreal.toSupport_eq]
  calc
    ConwayRefinement.Standalone.InlineSurreal.Surreal.mk
        (Game.toSupport (Surreal.fromSupport x).game) =
        ConwayRefinement.Standalone.InlineSurreal.Surreal.mk x.out := by
      apply ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_eq
      have heq : Game.toSupport (Surreal.fromSupport x).game = x.out :=
        congrArg Game.toSupport (Surreal.fromSupport_game x) |>.trans
          (Game.toSupport_fromSupport x.out)
      rw [heq]
    _ = x := ConwayRefinement.Standalone.InlineSurreal.Surreal.out_eq x

theorem Surreal.gameEquivalent_iff_toSupport_eq (x y : Surreal.{u}) :
    Game.Equivalent x.game y.game ↔ x.toSupport = y.toSupport := by
  letI : ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric (Game.toSupport x.game) :=
    x.numeric.toSupport
  letI : ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric (Game.toSupport y.game) :=
    y.numeric.toSupport
  rw [Surreal.toSupport_eq, Surreal.toSupport_eq,
    ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_eq_mk, Game.equivalent_iff]
  change (Game.Le x.game y.game ∧ Game.Le y.game x.game) ↔
    (Game.toSupport x.game ≤ Game.toSupport y.game ∧
      Game.toSupport y.game ≤ Game.toSupport x.game)
  rw [Game.toSupport_le, Game.toSupport_le]

/-- The actual quotient of the numeric representatives displayed in the headline file. -/
def Surreal.QuotientModel : Type (u + 1) :=
  Quotient
    { r := fun x y : Surreal.{u} ↦ Game.Equivalent x.game y.game
      iseqv := ⟨
        fun x ↦ Surreal.gameEquivalent_iff_toSupport_eq x x |>.mpr rfl,
        fun h ↦ Surreal.gameEquivalent_iff_toSupport_eq _ _ |>.mpr
          (Surreal.gameEquivalent_iff_toSupport_eq _ _ |>.mp h).symm,
        fun hxy hyz ↦ Surreal.gameEquivalent_iff_toSupport_eq _ _ |>.mpr
          ((Surreal.gameEquivalent_iff_toSupport_eq _ _ |>.mp hxy).trans
            (Surreal.gameEquivalent_iff_toSupport_eq _ _ |>.mp hyz))⟩ }

noncomputable def Surreal.QuotientModel.toSupport : Surreal.QuotientModel.{u} →
    ConwayRefinement.Standalone.InlineSurreal.Surreal.{u} :=
  Quotient.lift Surreal.toSupport fun _ _ h ↦
    Surreal.gameEquivalent_iff_toSupport_eq _ _ |>.mp h

universe v

theorem Surreal.QuotientModel.toSupport_bijective :
    Function.Bijective Surreal.QuotientModel.toSupport.{v} := by
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂ x y ?_ hxy
    intro x y h
    apply Quotient.sound
    exact Surreal.gameEquivalent_iff_toSupport_eq x y |>.mpr h
  · intro (x : ConwayRefinement.Standalone.InlineSurreal.Surreal.{v})
    exact ⟨Quotient.mk _ (Surreal.fromSupport x), Surreal.toSupport_fromSupport x⟩

/-- The quotient of the headline's numeric games is equivalent to the fully developed inlined
surreal numbers. -/
noncomputable def Surreal.quotientEquivSupport : Surreal.QuotientModel.{v} ≃
    ConwayRefinement.Standalone.InlineSurreal.Surreal.{v} :=
  Equiv.ofBijective Surreal.QuotientModel.toSupport.{v}
    Surreal.QuotientModel.toSupport_bijective

namespace SupportBridge

def playerToSupport : _root_.Player → ConwayRefinement.Standalone.InlineSurreal.Player
  | .left => .left
  | .right => .right

noncomputable def toCG (x : SupportGame.{u}) : _root_.IGame.{u} :=
  ConwayRefinement.Standalone.InlineSurreal.IGame.ofSetsRecOn x fun s t _ _ hs ht ↦
    !{Set.range fun y : s ↦ hs y.1 y.2 | Set.range fun y : t ↦ ht y.1 y.2}

noncomputable def fromCG (x : _root_.IGame.{u}) : SupportGame.{u} :=
  _root_.IGame.ofSetsRecOn x fun s t _ _ hs ht ↦
    ConwayRefinement.Standalone.InlineSurreal.ofSets
      (ConwayRefinement.Standalone.InlineSurreal.Player.cases
        (Set.range fun y : s ↦ hs y.1 y.2)
        (Set.range fun y : t ↦ ht y.1 y.2)) trivial

theorem fromCG_toCG (x : SupportGame.{u}) : fromCG (toCG x) = x := by
  induction x using ConwayRefinement.Standalone.InlineSurreal.IGame.ofSetsRecOn with
  | ofSets s t ihs iht =>
      rw [toCG, ConwayRefinement.Standalone.InlineSurreal.IGame.ofSetsRecOn_ofSets,
        fromCG, _root_.IGame.ofSetsRecOn_ofSets]
      apply ConwayRefinement.Standalone.InlineSurreal.IGame.ext
      intro p
      cases p
      · rw [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets,
          ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets]
        ext z
        constructor
        · rintro ⟨y, rfl⟩
          obtain ⟨x, hx⟩ := y.2
          change fromCG y.1 ∈ s
          have hxy : fromCG y.1 = x.1 :=
            (congrArg fromCG hx).symm.trans (ihs x.1 x.2)
          rw [hxy]
          exact x.2
        · intro hz
          refine ⟨⟨toCG z, ⟨⟨z, hz⟩, rfl⟩⟩, ?_⟩
          exact ihs z hz
      · rw [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets,
          ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets]
        ext z
        constructor
        · rintro ⟨y, rfl⟩
          obtain ⟨x, hx⟩ := y.2
          change fromCG y.1 ∈ t
          have hxy : fromCG y.1 = x.1 :=
            (congrArg fromCG hx).symm.trans (iht x.1 x.2)
          rw [hxy]
          exact x.2
        · intro hz
          refine ⟨⟨toCG z, ⟨⟨z, hz⟩, rfl⟩⟩, ?_⟩
          exact iht z hz

theorem toCG_fromCG (x : _root_.IGame.{u}) : toCG (fromCG x) = x := by
  induction x using _root_.IGame.ofSetsRecOn with
  | ofSets s t ihs iht =>
      rw [fromCG, _root_.IGame.ofSetsRecOn_ofSets,
        toCG, ConwayRefinement.Standalone.InlineSurreal.IGame.ofSetsRecOn_ofSets]
      apply _root_.IGame.ext
      intro p
      cases p
      · rw [_root_.IGame.moves_ofSets, _root_.IGame.moves_ofSets]
        ext z
        constructor
        · rintro ⟨y, rfl⟩
          obtain ⟨x, hx⟩ := y.2
          change toCG y.1 ∈ s
          have hxy : toCG y.1 = x.1 :=
            (congrArg toCG hx).symm.trans (ihs x.1 x.2)
          rw [hxy]
          exact x.2
        · intro hz
          refine ⟨⟨fromCG z, ⟨⟨z, hz⟩, rfl⟩⟩, ?_⟩
          exact ihs z hz
      · rw [_root_.IGame.moves_ofSets, _root_.IGame.moves_ofSets]
        ext z
        constructor
        · rintro ⟨y, rfl⟩
          obtain ⟨x, hx⟩ := y.2
          change toCG y.1 ∈ t
          have hxy : toCG y.1 = x.1 :=
            (congrArg toCG hx).symm.trans (iht x.1 x.2)
          rw [hxy]
          exact x.2
        · intro hz
          refine ⟨⟨fromCG z, ⟨⟨z, hz⟩, rfl⟩⟩, ?_⟩
          exact iht z hz

theorem moves_toCG (p : _root_.Player) (x : SupportGame.{u}) :
    (toCG x).moves p = toCG '' x.moves (playerToSupport p) := by
  induction x using ConwayRefinement.Standalone.InlineSurreal.IGame.ofSetsRecOn with
  | ofSets s t _ _ =>
      cases p <;> simp [toCG, playerToSupport, Set.ext_iff]

theorem toCG_le (x y : SupportGame.{u}) : x ≤ y ↔ toCG x ≤ toCG y := by
  induction x, y using Sym2.GameAdd.recursion
    ConwayRefinement.Standalone.InlineSurreal.IGame.subposition_wf with
  | _ x y ih =>
      rw [ConwayRefinement.Standalone.InlineSurreal.IGame.le_iff_forall_lf,
        _root_.IGame.le_iff_forall_lf, moves_toCG, moves_toCG]
      simp only [playerToSupport, Set.forall_mem_image]
      constructor
      · rintro ⟨hLeft, hRight⟩
        constructor
        · intro z hz h
          exact hLeft z hz ((ih _ _ (Sym2.GameAdd.snd_fst
            (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves hz))).mpr h)
        · intro z hz h
          exact hRight z hz ((ih _ _ (Sym2.GameAdd.fst_snd
            (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves hz))).mpr h)
      · rintro ⟨hLeft, hRight⟩
        constructor
        · intro z hz h
          exact hLeft hz ((ih _ _ (Sym2.GameAdd.snd_fst
            (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves hz))).mp h)
        · intro z hz h
          exact hRight hz ((ih _ _ (Sym2.GameAdd.fst_snd
            (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves hz))).mp h)

theorem playerToSupport_neg (p : _root_.Player) : playerToSupport (-p) = -playerToSupport p := by
  cases p <;> rfl

theorem playerToSupport_mul (p q : _root_.Player) :
    playerToSupport (p * q) = playerToSupport p * playerToSupport q := by
  cases p <;> cases q <;> rfl

theorem toCG_neg (x : SupportGame.{u}) : toCG (-x) = -toCG x := by
  induction x using ConwayRefinement.Standalone.InlineSurreal.IGame.moveRecOn with
  | ind x ih =>
      apply _root_.IGame.ext
      intro p
      rw [moves_toCG, ConwayRefinement.Standalone.InlineSurreal.IGame.moves_neg,
        _root_.IGame.moves_neg, moves_toCG, playerToSupport_neg]
      rw [← Set.image_neg_eq_neg, ← Set.image_neg_eq_neg]
      ext z
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨toCG y, ⟨y, hy, rfl⟩, (ih _ y hy).symm⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨-y, ⟨y, hy, rfl⟩, ih _ y hy⟩

theorem toCG_add (x y : SupportGame.{u}) : toCG (x + y) = toCG x + toCG y := by
  induction x, y using Sym2.GameAdd.recursion
    ConwayRefinement.Standalone.InlineSurreal.IGame.subposition_wf with
  | _ x y ih =>
      apply _root_.IGame.ext
      intro p
      rw [moves_toCG, ConwayRefinement.Standalone.InlineSurreal.IGame.moves_add,
        _root_.IGame.moves_add, moves_toCG, moves_toCG]
      ext z
      simp only [Set.mem_image, Set.mem_union]
      constructor
      · rintro ⟨_, (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩), rfl⟩
        · left
          refine ⟨toCG a, ⟨a, ha, rfl⟩, ?_⟩
          exact (ih _ _ (Sym2.GameAdd.fst
            (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves ha))).symm
        · right
          refine ⟨toCG b, ⟨b, hb, rfl⟩, ?_⟩
          exact (ih _ _ (Sym2.GameAdd.snd
            (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves hb))).symm
      · rintro (⟨_, ⟨a, ha, rfl⟩, rfl⟩ | ⟨_, ⟨b, hb, rfl⟩, rfl⟩)
        · exact ⟨a + y, Or.inl ⟨a, ha, rfl⟩,
            ih _ _ (Sym2.GameAdd.fst
              (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves ha))⟩
        · exact ⟨x + b, Or.inr ⟨b, hb, rfl⟩,
            ih _ _ (Sym2.GameAdd.snd
              (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves hb))⟩

theorem toCG_zero : toCG (0 : SupportGame.{u}) = 0 := by
  apply _root_.IGame.ext
  intro p
  rw [moves_toCG, ConwayRefinement.Standalone.InlineSurreal.IGame.moves_zero,
    _root_.IGame.moves_zero]
  simp

theorem toCG_one : toCG (1 : SupportGame.{u}) = 1 := by
  apply _root_.IGame.ext
  intro p
  rw [moves_toCG]
  cases p <;>
    simp [ConwayRefinement.Standalone.InlineSurreal.IGame.one_def, _root_.IGame.one_def,
      playerToSupport, toCG_zero]

theorem toCG_mul (x y : SupportGame.{u}) : toCG (x * y) = toCG x * toCG y := by
  have option_eq {a b : SupportGame.{u}}
      (ha : ∃ q, a ∈ ConwayRefinement.Standalone.InlineSurreal.IGame.moves q x)
      (hb : ∃ q, b ∈ ConwayRefinement.Standalone.InlineSurreal.IGame.moves q y) :
      toCG (ConwayRefinement.Standalone.InlineSurreal.IGame.mulOption x y a b) =
        _root_.IGame.mulOption (toCG x) (toCG y) (toCG a) (toCG b) := by
    rw [ConwayRefinement.Standalone.InlineSurreal.IGame.mulOption, _root_.IGame.mulOption,
      sub_eq_add_neg, sub_eq_add_neg, toCG_add, toCG_add, toCG_neg,
      toCG_mul a y, toCG_mul x b, toCG_mul a b]
  apply _root_.IGame.ext
  intro p
  rw [moves_toCG, ConwayRefinement.Standalone.InlineSurreal.IGame.moves_mul,
    _root_.IGame.moves_mul, moves_toCG, moves_toCG, moves_toCG, moves_toCG,
    playerToSupport_neg]
  ext z
  simp only [Set.mem_image, Set.mem_union, Set.mem_prod]
  constructor
  · rintro ⟨w, ⟨⟨a, b⟩, (⟨ha, hb⟩ | ⟨ha, hb⟩), hmul⟩, hw⟩
    · refine ⟨(toCG a, toCG b), Or.inl ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, ?_⟩
      calc
        _root_.IGame.mulOption (toCG x) (toCG y) (toCG a) (toCG b) =
            toCG (ConwayRefinement.Standalone.InlineSurreal.IGame.mulOption x y a b) :=
          (option_eq ⟨_, ha⟩ ⟨_, hb⟩).symm
        _ = toCG w := congrArg toCG hmul
        _ = z := hw
    · refine ⟨(toCG a, toCG b), Or.inr ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, ?_⟩
      calc
        _root_.IGame.mulOption (toCG x) (toCG y) (toCG a) (toCG b) =
            toCG (ConwayRefinement.Standalone.InlineSurreal.IGame.mulOption x y a b) :=
          (option_eq ⟨_, ha⟩ ⟨_, hb⟩).symm
        _ = toCG w := congrArg toCG hmul
        _ = z := hw
  · rintro ⟨⟨qa, qb⟩,
      (⟨⟨a, ha, hqa⟩, ⟨b, hb, hqb⟩⟩ | ⟨⟨a, ha, hqa⟩, ⟨b, hb, hqb⟩⟩), hmul⟩
    · refine ⟨ConwayRefinement.Standalone.InlineSurreal.IGame.mulOption x y a b,
        ⟨(a, b), Or.inl ⟨ha, hb⟩, rfl⟩, ?_⟩
      calc
        toCG (ConwayRefinement.Standalone.InlineSurreal.IGame.mulOption x y a b) =
            _root_.IGame.mulOption (toCG x) (toCG y) (toCG a) (toCG b) :=
          option_eq ⟨_, ha⟩ ⟨_, hb⟩
        _ = _root_.IGame.mulOption (toCG x) (toCG y) qa qb := by rw [hqa, hqb]
        _ = z := hmul
    · refine ⟨ConwayRefinement.Standalone.InlineSurreal.IGame.mulOption x y a b,
        ⟨(a, b), Or.inr ⟨ha, hb⟩, rfl⟩, ?_⟩
      calc
        toCG (ConwayRefinement.Standalone.InlineSurreal.IGame.mulOption x y a b) =
            _root_.IGame.mulOption (toCG x) (toCG y) (toCG a) (toCG b) :=
          option_eq ⟨_, ha⟩ ⟨_, hb⟩
        _ = _root_.IGame.mulOption (toCG x) (toCG y) qa qb := by rw [hqa, hqb]
        _ = z := hmul
termination_by (x, y)
decreasing_by
  · obtain ⟨q, hq⟩ := ha
    exact Prod.Lex.left _ _
      (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves hq)
  · obtain ⟨q, hq⟩ := hb
    exact Prod.Lex.right _
      (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves hq)
  · obtain ⟨q, hq⟩ := ha
    exact Prod.Lex.left _ _
      (ConwayRefinement.Standalone.InlineSurreal.IGame.Subposition.of_mem_moves hq)


theorem toCG_numeric {x : SupportGame.{u}}
    (h : ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric x) :
    _root_.IGame.Numeric (toCG x) := by
  induction h with
  | mk hOrder hMoves ih =>
      rw [_root_.IGame.numeric_def]
      constructor
      · intro y hy z hz
        rw [moves_toCG] at hy hz
        obtain ⟨y, hy, rfl⟩ := hy
        obtain ⟨z, hz, rfl⟩ := hz
        rw [lt_iff_le_not_ge, ← toCG_le, ← toCG_le]
        exact hOrder y hy z hz
      · intro p y hy
        rw [moves_toCG] at hy
        obtain ⟨y, hy, rfl⟩ := hy
        exact ih (playerToSupport p) y hy

theorem fromCG_numeric {x : _root_.IGame.{u}} (h : _root_.IGame.Numeric x) :
    ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric (fromCG x) := by
  revert h
  induction x using _root_.IGame.moveRecOn with
  | ind x ih =>
      intro h
      have hdef := _root_.IGame.numeric_def.mp h
      rw [ConwayRefinement.Standalone.InlineSurreal.IGame.numeric_def]
      constructor
      · intro y hy z hz
        have hy' : toCG y ∈ x.moves _root_.Player.left := by
          rw [← toCG_fromCG x, moves_toCG]
          exact ⟨y, by simpa only [playerToSupport] using hy, rfl⟩
        have hz' : toCG z ∈ x.moves _root_.Player.right := by
          rw [← toCG_fromCG x, moves_toCG]
          exact ⟨z, by simpa only [playerToSupport] using hz, rfl⟩
        have hyz := hdef.1 (toCG y) hy' (toCG z) hz'
        rw [lt_iff_le_not_ge, ← toCG_le, ← toCG_le] at hyz
        exact hyz
      · intro p y hy
        cases p
        · have hy' : toCG y ∈ x.moves _root_.Player.left := by
            rw [← toCG_fromCG x, moves_toCG]
            exact ⟨y, by simpa only [playerToSupport] using hy, rfl⟩
          simpa only [fromCG_toCG] using
            ih _ (toCG y) hy' (hdef.2 _ (toCG y) hy')
        · have hy' : toCG y ∈ x.moves _root_.Player.right := by
            rw [← toCG_fromCG x, moves_toCG]
            exact ⟨y, by simpa only [playerToSupport] using hy, rfl⟩
          simpa only [fromCG_toCG] using
            ih _ (toCG y) hy' (hdef.2 _ (toCG y) hy')

end SupportBridge

namespace SupportBridge

abbrev SupportSurreal := ConwayRefinement.Standalone.InlineSurreal.Surreal
abbrev SupportQuotientGame := ConwayRefinement.Standalone.InlineSurreal.Game

noncomputable def gameToCG (x : SupportQuotientGame.{u}) : _root_.Game.{u} :=
  _root_.Game.mk (toCG x.out)

noncomputable def surrealToCG (x : SupportSurreal.{u}) : _root_.Surreal.{u} :=
  @_root_.Surreal.mk (toCG x.out) (toCG_numeric inferInstance)

noncomputable def surrealFromCG (x : _root_.Surreal.{u}) : SupportSurreal.{u} :=
  @ConwayRefinement.Standalone.InlineSurreal.Surreal.mk (fromCG x.out)
    (fromCG_numeric inferInstance)

theorem toCG_equiv (x y : SupportGame.{u}) :
    (x ≤ y ∧ y ≤ x) ↔ (toCG x ≤ toCG y ∧ toCG y ≤ toCG x) := by
  rw [toCG_le, toCG_le]

theorem gameToCG_mk (x : SupportGame.{u}) :
    gameToCG (ConwayRefinement.Standalone.InlineSurreal.Game.mk x) = _root_.Game.mk (toCG x) := by
  rw [gameToCG, _root_.Game.mk_eq_mk]
  apply toCG_equiv _ _ |>.mp
  exact ConwayRefinement.Standalone.InlineSurreal.Game.mk_out_equiv x

theorem gameToCG_singletonCut (l r : SupportQuotientGame.{u}) :
    gameToCG !{{l} | {r}} = !{{gameToCG l} | {gameToCG r}} := by
  rw [gameToCG]
  apply _root_.Game.mk_eq
  let sraw : SupportGame.{u} :=
    ConwayRefinement.Standalone.InlineSurreal.OfSets.ofSets
      (ConwayRefinement.Standalone.InlineSurreal.Player.cases {l.out} {r.out}) trivial
  have hout :
      toCG (ConwayRefinement.Standalone.InlineSurreal.Game.out !{{l} | {r}}) ≤ toCG sraw ∧
        toCG sraw ≤ toCG (ConwayRefinement.Standalone.InlineSurreal.Game.out !{{l} | {r}}) := by
    apply toCG_equiv _ _ |>.mp
    have hs := ConwayRefinement.Standalone.InlineSurreal.Game.mk_out_equiv sraw
    change (ConwayRefinement.Standalone.InlineSurreal.Game.mk sraw).out ≤ sraw ∧
      sraw ≤ (ConwayRefinement.Standalone.InlineSurreal.Game.mk sraw).out at hs
    have hcut : ConwayRefinement.Standalone.InlineSurreal.Game.mk sraw = !{{l} | {r}} := by
      simpa only [sraw, Set.image_singleton,
        ConwayRefinement.Standalone.InlineSurreal.Game.out_eq] using
        ConwayRefinement.Standalone.InlineSurreal.Game.mk_ofSets ({l.out} : Set SupportGame.{u})
          ({r.out} : Set SupportGame.{u})
    rw [← hcut]
    exact hs
  have hraw :
      toCG sraw = !{{toCG l.out} | {toCG r.out}} := by
    apply _root_.IGame.ext
    intro p
    rw [moves_toCG]
    cases p <;> simp [sraw, playerToSupport]
  have htarget :
      toCG sraw ≤ !{fun p ↦ _root_.Game.out ''
          _root_.Player.cases {gameToCG l} {gameToCG r} p} ∧
        !{fun p ↦ _root_.Game.out ''
          _root_.Player.cases {gameToCG l} {gameToCG r} p} ≤ toCG sraw := by
    rw [hraw]
    apply _root_.IGame.equiv_of_exists <;>
      simp only [_root_.IGame.moves_ofSets, Set.mem_singleton_iff,
        _root_.Player.apply_cases, Set.mem_image]
    · intro a ha
      subst a
      exact ⟨(gameToCG l).out, ⟨gameToCG l, rfl, rfl⟩,
        (_root_.Game.mk_out_equiv (toCG l.out)).symm⟩
    · intro a ha
      subst a
      exact ⟨(gameToCG r).out, ⟨gameToCG r, rfl, rfl⟩,
        (_root_.Game.mk_out_equiv (toCG r.out)).symm⟩
    · intro b hb
      obtain ⟨l', hl', rfl⟩ := hb
      subst l'
      exact ⟨toCG l.out, rfl, (_root_.Game.mk_out_equiv (toCG l.out)).symm⟩
    · intro b hb
      obtain ⟨r', hr', rfl⟩ := hb
      subst r'
      exact ⟨toCG r.out, rfl, (_root_.Game.mk_out_equiv (toCG r.out)).symm⟩
  exact ⟨hout.1.trans htarget.1, htarget.2.trans hout.2⟩

theorem surrealToCG_mk (x : SupportGame.{u})
    [ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric x] :
    surrealToCG (ConwayRefinement.Standalone.InlineSurreal.Surreal.mk x) =
      @_root_.Surreal.mk (toCG x) (toCG_numeric inferInstance) := by
  letI := toCG_numeric (x := x) (inferInstance)
  letI := toCG_numeric
    (x := (ConwayRefinement.Standalone.InlineSurreal.Surreal.mk x).out) (inferInstance)
  rw [surrealToCG, _root_.Surreal.mk_eq_mk]
  apply toCG_equiv _ _ |>.mp
  exact ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_out_equiv x

theorem toGame_surrealToCG (x : SupportSurreal.{u}) :
    _root_.Surreal.toGame (surrealToCG x) =
      gameToCG (ConwayRefinement.Standalone.InlineSurreal.Surreal.toGame x) := by
  induction x using ConwayRefinement.Standalone.InlineSurreal.Surreal.ind with
  | mk x =>
      letI : _root_.IGame.Numeric (toCG x) := toCG_numeric (by infer_instance)
      rw [surrealToCG_mk, _root_.Surreal.toGame_mk,
        ConwayRefinement.Standalone.InlineSurreal.Surreal.toGame_mk, gameToCG_mk]

theorem surrealFromCG_mk (x : _root_.IGame.{u}) [x.Numeric] :
    surrealFromCG (_root_.Surreal.mk x) =
      @ConwayRefinement.Standalone.InlineSurreal.Surreal.mk (fromCG x)
        (fromCG_numeric inferInstance) := by
  letI := fromCG_numeric (x := x) (inferInstance)
  letI := fromCG_numeric (x := (_root_.Surreal.mk x).out) (inferInstance)
  rw [surrealFromCG, ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_eq_mk]
  apply toCG_equiv _ _ |>.mpr
  rw [toCG_fromCG]
  obtain ⟨h₁, h₂⟩ := _root_.Surreal.mk_out_equiv x
  constructor
  · exact h₁.trans_eq (toCG_fromCG x).symm
  · exact (toCG_fromCG x).le.trans h₂

theorem surrealToCG_fromCG (x : _root_.Surreal.{u}) :
    surrealToCG (surrealFromCG x) = x := by
  induction x using _root_.Surreal.ind with
  | mk x =>
      letI := fromCG_numeric (x := x) (inferInstance)
      letI := toCG_numeric (x := fromCG x) (inferInstance)
      rw [surrealFromCG_mk, surrealToCG_mk]
      rw [_root_.Surreal.mk_eq_mk]
      change toCG (fromCG x) ≤ x ∧ x ≤ toCG (fromCG x)
      rw [toCG_fromCG]
      exact ⟨le_rfl, le_rfl⟩

theorem surrealFromCG_toCG (x : SupportSurreal.{u}) :
    surrealFromCG (surrealToCG x) = x := by
  induction x using ConwayRefinement.Standalone.InlineSurreal.Surreal.ind with
  | mk x =>
      letI := toCG_numeric (x := x) (inferInstance)
      letI := fromCG_numeric (x := toCG x) (inferInstance)
      rw [surrealToCG_mk, surrealFromCG_mk]
      rw [ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_eq_mk]
      apply toCG_equiv _ _ |>.mpr
      rw [toCG_fromCG]
      exact ⟨le_rfl, le_rfl⟩

/-- The fully developed Mathlib-only copy and CombinatorialGames define equivalent surreal
numbers. -/
noncomputable def surrealEquivCG : SupportSurreal.{u} ≃ _root_.Surreal.{u} where
  toFun := surrealToCG
  invFun := surrealFromCG
  left_inv := surrealFromCG_toCG
  right_inv := surrealToCG_fromCG

theorem surrealToCG_zero : surrealToCG (0 : SupportSurreal.{u}) = 0 := by
  letI : _root_.IGame.Numeric (toCG (0 : SupportGame.{u})) :=
    toCG_numeric (by infer_instance)
  rw [← ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_zero, surrealToCG_mk,
    ← _root_.Surreal.mk_zero, _root_.Surreal.mk_eq_mk]
  change toCG 0 ≤ 0 ∧ 0 ≤ toCG 0
  rw [toCG_zero]
  exact ⟨le_rfl, le_rfl⟩

theorem surrealToCG_one : surrealToCG (1 : SupportSurreal.{u}) = 1 := by
  letI : _root_.IGame.Numeric (toCG (1 : SupportGame.{u})) :=
    toCG_numeric (by infer_instance)
  rw [← ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_one, surrealToCG_mk,
    ← _root_.Surreal.mk_one, _root_.Surreal.mk_eq_mk]
  change toCG 1 ≤ 1 ∧ 1 ≤ toCG 1
  rw [toCG_one]
  exact ⟨le_rfl, le_rfl⟩

theorem surrealToCG_neg (x : SupportSurreal.{u}) : surrealToCG (-x) = -surrealToCG x := by
  induction x using ConwayRefinement.Standalone.InlineSurreal.Surreal.ind with
  | mk x =>
      letI : _root_.IGame.Numeric (toCG x) := toCG_numeric (by infer_instance)
      letI : _root_.IGame.Numeric (toCG (-x)) := toCG_numeric (by infer_instance)
      rw [← ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_neg, surrealToCG_mk,
        surrealToCG_mk, ← _root_.Surreal.mk_neg, _root_.Surreal.mk_eq_mk]
      change toCG (-x) ≤ -toCG x ∧ -toCG x ≤ toCG (-x)
      rw [toCG_neg]
      exact ⟨le_rfl, le_rfl⟩

theorem surrealToCG_add (x y : SupportSurreal.{u}) :
    surrealToCG (x + y) = surrealToCG x + surrealToCG y := by
  induction x using ConwayRefinement.Standalone.InlineSurreal.Surreal.ind with
  | mk x =>
      induction y using ConwayRefinement.Standalone.InlineSurreal.Surreal.ind with
      | mk y =>
          letI : _root_.IGame.Numeric (toCG x) := toCG_numeric (by infer_instance)
          letI : _root_.IGame.Numeric (toCG y) := toCG_numeric (by infer_instance)
          letI : _root_.IGame.Numeric (toCG (x + y)) := toCG_numeric (by infer_instance)
          rw [← ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_add, surrealToCG_mk,
            surrealToCG_mk, surrealToCG_mk, ← _root_.Surreal.mk_add,
            _root_.Surreal.mk_eq_mk]
          change toCG (x + y) ≤ toCG x + toCG y ∧ toCG x + toCG y ≤ toCG (x + y)
          rw [toCG_add]
          exact ⟨le_rfl, le_rfl⟩

theorem surrealToCG_mul (x y : SupportSurreal.{u}) :
    surrealToCG (x * y) = surrealToCG x * surrealToCG y := by
  induction x using ConwayRefinement.Standalone.InlineSurreal.Surreal.ind with
  | mk x =>
      induction y using ConwayRefinement.Standalone.InlineSurreal.Surreal.ind with
      | mk y =>
          letI : _root_.IGame.Numeric (toCG x) := toCG_numeric (by infer_instance)
          letI : _root_.IGame.Numeric (toCG y) := toCG_numeric (by infer_instance)
          letI : _root_.IGame.Numeric (toCG (x * y)) := toCG_numeric (by infer_instance)
          rw [← ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_mul, surrealToCG_mk,
            surrealToCG_mk, surrealToCG_mk, ← _root_.Surreal.mk_mul,
            _root_.Surreal.mk_eq_mk]
          change toCG (x * y) ≤ toCG x * toCG y ∧ toCG x * toCG y ≤ toCG (x * y)
          rw [toCG_mul]
          exact ⟨le_rfl, le_rfl⟩

theorem surrealToCG_singletonIntegerCut (x : SupportSurreal.{u}) :
    surrealToCG (ConwayRefinement.Standalone.InlineSurreal.Surreal.singletonIntegerCut x) =
      !{{surrealToCG x - 1} | {surrealToCG x + 1}}' (by
        simp only [Set.mem_singleton_iff]
        rintro _ rfl _ rfl
        simp [sub_eq_add_neg]) := by
  rw [ConwayRefinement.Standalone.InlineSurreal.Surreal.singletonIntegerCut]
  rw [← _root_.Surreal.toGame_inj, toGame_surrealToCG,
    ConwayRefinement.Standalone.InlineSurreal.Surreal.toGame_ofSets]
  simp only [Set.image_singleton]
  rw [gameToCG_singletonCut, _root_.Surreal.toGame_ofSets]
  simp only [Set.image_singleton]
  congr 2
  · congr 1
    rw [← toGame_surrealToCG, sub_eq_add_neg, surrealToCG_add, surrealToCG_neg,
      surrealToCG_one]
    rw [sub_eq_add_neg]
  · congr 1
    rw [← toGame_surrealToCG, surrealToCG_add, surrealToCG_one]

theorem isConwayOmnificInteger_iff (x : SupportSurreal.{u}) :
    ConwayRefinement.Standalone.InlineSurreal.Surreal.IsConwayOmnificInteger x ↔
      ConwayRefinement.Standalone.Oz.IsConwayOmnificInteger (surrealToCG x) := by
  rw [ConwayRefinement.Standalone.InlineSurreal.Surreal.IsConwayOmnificInteger,
    ConwayRefinement.Standalone.Oz.isConwayOmnificInteger_iff]
  constructor
  · intro hx
    calc
      surrealToCG x =
          surrealToCG (ConwayRefinement.Standalone.InlineSurreal.Surreal.singletonIntegerCut x) :=
        congrArg surrealToCG hx
      _ = !{{surrealToCG x - 1} | {surrealToCG x + 1}}' _ :=
        surrealToCG_singletonIntegerCut x
  · intro hx
    apply surrealEquivCG.injective
    calc
      surrealToCG x = !{{surrealToCG x - 1} | {surrealToCG x + 1}}' _ := hx
      _ = surrealToCG (ConwayRefinement.Standalone.InlineSurreal.Surreal.singletonIntegerCut x) :=
        (surrealToCG_singletonIntegerCut x).symm

end SupportBridge

/-- The quotient of the completely visible inline representatives is exactly the surreal-number
type supplied by CombinatorialGames. -/
noncomputable def Surreal.quotientEquivCombinatorialGames :
    Surreal.QuotientModel.{u} ≃ _root_.Surreal.{u} :=
  Surreal.quotientEquivSupport.trans SupportBridge.surrealEquivCG

end ConwayRefinement.Standalone.InlineConwayRefinement
namespace ConwayRefinement.Standalone.InlineConwayRefinement.SupportBridge

universe u

theorem supportConway :
    ConwayRefinement.Standalone.InlineSurreal.Surreal.ConwayConjecture.{u} := by
  intro a b c d ha hb hc hd habcd
  have ha' := (isConwayOmnificInteger_iff a).mp ha
  have hb' := (isConwayOmnificInteger_iff b).mp hb
  have hc' := (isConwayOmnificInteger_iff c).mp hc
  have hd' := (isConwayOmnificInteger_iff d).mp hd
  have habcd' : surrealToCG a * surrealToCG b = surrealToCG c * surrealToCG d := by
    rw [← surrealToCG_mul, ← surrealToCG_mul, habcd]
  obtain ⟨e, f, g, h, he, hf, hg, hh, hae, hbg, hce, hdf⟩ :=
    ConwayRefinement.Standalone.Oz.conwayConjecture_iff.mp
      ConwayRefinement.Standalone.Oz.ConwayConjecture.proof
      (surrealToCG a) (surrealToCG b) (surrealToCG c) (surrealToCG d)
      ha' hb' hc' hd' habcd'
  refine ⟨surrealFromCG e, surrealFromCG f, surrealFromCG g, surrealFromCG h,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (isConwayOmnificInteger_iff _).mpr
    simpa only [surrealToCG_fromCG] using he
  · apply (isConwayOmnificInteger_iff _).mpr
    simpa only [surrealToCG_fromCG] using hf
  · apply (isConwayOmnificInteger_iff _).mpr
    simpa only [surrealToCG_fromCG] using hg
  · apply (isConwayOmnificInteger_iff _).mpr
    simpa only [surrealToCG_fromCG] using hh
  · apply surrealEquivCG.injective
    change surrealToCG a = surrealToCG (surrealFromCG e * surrealFromCG f)
    rw [surrealToCG_mul, surrealToCG_fromCG, surrealToCG_fromCG]
    exact hae
  · apply surrealEquivCG.injective
    change surrealToCG b = surrealToCG (surrealFromCG g * surrealFromCG h)
    rw [surrealToCG_mul, surrealToCG_fromCG, surrealToCG_fromCG]
    exact hbg
  · apply surrealEquivCG.injective
    change surrealToCG c = surrealToCG (surrealFromCG e * surrealFromCG g)
    rw [surrealToCG_mul, surrealToCG_fromCG, surrealToCG_fromCG]
    exact hce
  · apply surrealEquivCG.injective
    change surrealToCG d = surrealToCG (surrealFromCG f * surrealFromCG h)
    rw [surrealToCG_mul, surrealToCG_fromCG, surrealToCG_fromCG]
    exact hdf

end ConwayRefinement.Standalone.InlineConwayRefinement.SupportBridge

namespace ConwayRefinement.Standalone.InlineConwayRefinement

universe u

theorem Game.equivalent_iff_toSupport (x y : Game.{u}) :
    Game.Equivalent x y ↔
      (Game.toSupport x ≤ Game.toSupport y ∧ Game.toSupport y ≤ Game.toSupport x) := by
  rw [Game.equivalent_iff]
  rw [Game.toSupport_le, Game.toSupport_le]

theorem Surreal.productsEqual_iff_toSupport (a b c d : Surreal.{u}) :
    Game.Equivalent (Game.mul a.game b.game) (Game.mul c.game d.game) ↔
      a.toSupport * b.toSupport = c.toSupport * d.toSupport := by
  letI := a.numeric.toSupport
  letI := b.numeric.toSupport
  letI := c.numeric.toSupport
  letI := d.numeric.toSupport
  rw [Game.equivalent_iff_toSupport, Game.toSupport_mul, Game.toSupport_mul]
  simp only [Surreal.toSupport_eq]
  rw [← ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_mul,
    ← ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_mul]
  rw [ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_eq_mk]
  rfl

theorem Surreal.equalsProduct_iff_toSupport (a e f : Surreal.{u}) :
    Game.Equivalent a.game (Game.mul e.game f.game) ↔
      a.toSupport = e.toSupport * f.toSupport := by
  letI := a.numeric.toSupport
  letI := e.numeric.toSupport
  letI := f.numeric.toSupport
  rw [Game.equivalent_iff_toSupport, Game.toSupport_mul]
  simp only [Surreal.toSupport_eq]
  rw [← ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_mul]
  rw [ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_eq_mk]
  rfl

theorem Game.toSupport_mk {Left Right : Type u}
    (left : Left → Game.{u}) (right : Right → Game.{u}) :
    Game.toSupport (.mk Left Right left right) =
      ConwayRefinement.Standalone.InlineSurreal.ofSets
        (ConwayRefinement.Standalone.InlineSurreal.Player.cases
          (Set.range fun i : Left ↦ Game.toSupport (left i))
          (Set.range fun i : Right ↦ Game.toSupport (right i))) trivial := (rfl)

theorem Game.toSupport_zero : Game.toSupport (Game.zero : Game.{u}) =
    (0 : ConwayRefinement.Standalone.InlineSurreal.IGame.{u}) := by
  rw [Game.zero_eq, Game.toSupport_mk]
  apply ConwayRefinement.Standalone.InlineSurreal.IGame.ext
  intro p
  cases p
  · rw [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets,
      ConwayRefinement.Standalone.InlineSurreal.IGame.moves_zero]
    ext z
    constructor
    · rintro ⟨i, _⟩
      exact nomatch i.down
    · simp
  · rw [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets,
      ConwayRefinement.Standalone.InlineSurreal.IGame.moves_zero]
    ext z
    constructor
    · rintro ⟨i, _⟩
      exact nomatch i.down
    · simp

theorem Game.toSupport_one : Game.toSupport (Game.one : Game.{u}) =
    (1 : ConwayRefinement.Standalone.InlineSurreal.IGame.{u}) := by
  rw [Game.one_eq, Game.toSupport_mk]
  apply ConwayRefinement.Standalone.InlineSurreal.IGame.ext
  intro p
  cases p
  · rw [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets]
    rw [ConwayRefinement.Standalone.InlineSurreal.IGame.one_def,
      ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets]
    ext z
    constructor
    · rintro ⟨_, rfl⟩
      exact Game.toSupport_zero
    · intro hz
      have hz' : z = 0 := by simpa using hz
      subst z
      exact ⟨PUnit.unit, Game.toSupport_zero⟩
  · rw [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets,
      ConwayRefinement.Standalone.InlineSurreal.IGame.one_def,
      ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets]
    ext z
    constructor
    · rintro ⟨i, _⟩
      exact nomatch i.down
    · simp

theorem Game.toSupport_singletonIntegerCut_numeric (x : Surreal.{u}) :
    ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric
      (Game.toSupport (Surreal.singletonIntegerCut x.game)) := by
  letI := x.numeric.toSupport
  rw [Surreal.singletonIntegerCut_eq]
  rw [Game.toSupport_mk]
  rw [ConwayRefinement.Standalone.InlineSurreal.IGame.numeric_def]
  simp only [ConwayRefinement.Standalone.InlineSurreal.IGame.moves_ofSets,
    Set.forall_mem_range]
  constructor
  · intro _ _
    change ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport
        (ConwayRefinement.Standalone.InlineConwayRefinement.Game.add x.game
          (ConwayRefinement.Standalone.InlineConwayRefinement.Game.neg
            ConwayRefinement.Standalone.InlineConwayRefinement.Game.one)) <
      ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport
        (ConwayRefinement.Standalone.InlineConwayRefinement.Game.add x.game
          ConwayRefinement.Standalone.InlineConwayRefinement.Game.one)
    rw [ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport_add x.game
        (ConwayRefinement.Standalone.InlineConwayRefinement.Game.neg
          (show Game.{u} from ConwayRefinement.Standalone.InlineConwayRefinement.Game.one)),
      ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport_add x.game
        (show Game.{u} from ConwayRefinement.Standalone.InlineConwayRefinement.Game.one),
      ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport_neg
        (show Game.{u} from ConwayRefinement.Standalone.InlineConwayRefinement.Game.one)]
    rw [Game.toSupport_one]
    apply ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_lt_mk.mp
    simp only [ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_add,
      ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_neg,
      ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_one]
    linarith
  · intro p y hy
    cases p
    · obtain ⟨_, rfl⟩ := hy
      change ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric
        (ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport
          (ConwayRefinement.Standalone.InlineConwayRefinement.Game.add x.game
            (ConwayRefinement.Standalone.InlineConwayRefinement.Game.neg
              ConwayRefinement.Standalone.InlineConwayRefinement.Game.one)))
      rw [ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport_add x.game
          (ConwayRefinement.Standalone.InlineConwayRefinement.Game.neg
            (show Game.{u} from ConwayRefinement.Standalone.InlineConwayRefinement.Game.one)),
        ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport_neg
          (show Game.{u} from ConwayRefinement.Standalone.InlineConwayRefinement.Game.one)]
      rw [Game.toSupport_one]
      infer_instance
    · obtain ⟨_, rfl⟩ := hy
      change ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric
        (ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport
          (ConwayRefinement.Standalone.InlineConwayRefinement.Game.add x.game
            ConwayRefinement.Standalone.InlineConwayRefinement.Game.one))
      rw [ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport_add x.game
        (show Game.{u} from ConwayRefinement.Standalone.InlineConwayRefinement.Game.one)]
      rw [Game.toSupport_one]
      infer_instance

theorem Surreal.toSupport_sub_one (x : Surreal.{u}) :
    @ConwayRefinement.Standalone.InlineSurreal.Surreal.mk
        (Game.toSupport (Game.add x.game (Game.neg Game.one))) (by
          letI := x.numeric.toSupport
          rw [Game.toSupport_add, Game.toSupport_neg, Game.toSupport_one]
          infer_instance) = x.toSupport - 1 := by
  letI := x.numeric.toSupport
  simp only [Game.toSupport_add, Game.toSupport_neg, Game.toSupport_one]
  simpa only [ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_neg,
    ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_one, Surreal.toSupport_eq,
    sub_eq_add_neg] using
      (ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_add
        (Game.toSupport x.game) (-1 : ConwayRefinement.Standalone.InlineSurreal.IGame.{u}))

theorem Surreal.toSupport_add_one (x : Surreal.{u}) :
    @ConwayRefinement.Standalone.InlineSurreal.Surreal.mk
        (Game.toSupport (Game.add x.game Game.one)) (by
          letI := x.numeric.toSupport
          rw [Game.toSupport_add, Game.toSupport_one]
          infer_instance) = x.toSupport + 1 := by
  letI := x.numeric.toSupport
  simp only [Game.toSupport_add, Game.toSupport_one]
  simpa only [ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_one,
    Surreal.toSupport_eq] using
      (ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_add
        (Game.toSupport x.game) (1 : ConwayRefinement.Standalone.InlineSurreal.IGame.{u}))

theorem Surreal.toSupport_singletonIntegerCut (x : Surreal.{u}) :
    @ConwayRefinement.Standalone.InlineSurreal.Surreal.mk
        (Game.toSupport (Surreal.singletonIntegerCut x.game))
        (Game.toSupport_singletonIntegerCut_numeric x) =
      ConwayRefinement.Standalone.InlineSurreal.Surreal.singletonIntegerCut x.toSupport := by
  simp only [Surreal.singletonIntegerCut_eq, Game.toSupport_mk]
  rw [ConwayRefinement.Standalone.InlineSurreal.Surreal.singletonIntegerCut]
  rw [ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_ofSets]
  congr 2
  · ext z
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, ⟨_, rfl⟩⟩, rfl⟩
      exact Surreal.toSupport_sub_one x
    · rintro rfl
      refine ⟨⟨Game.toSupport (Game.add x.game (Game.neg Game.one)),
        ⟨PUnit.unit, rfl⟩⟩, ?_⟩
      exact Surreal.toSupport_sub_one x
  · ext z
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, ⟨_, rfl⟩⟩, rfl⟩
      exact Surreal.toSupport_add_one x
    · rintro rfl
      refine ⟨⟨Game.toSupport (Game.add x.game Game.one),
        ⟨PUnit.unit, rfl⟩⟩, ?_⟩
      exact Surreal.toSupport_add_one x

theorem Surreal.isConwayOmnificInteger_iff_toSupport (x : Surreal.{u}) :
    IsConwayOmnificInteger x ↔
      ConwayRefinement.Standalone.InlineSurreal.Surreal.IsConwayOmnificInteger x.toSupport := by
  letI := x.numeric.toSupport
  letI := Game.toSupport_singletonIntegerCut_numeric x
  rw [Surreal.isConwayOmnificInteger_iff,
    ConwayRefinement.Standalone.InlineSurreal.Surreal.IsConwayOmnificInteger]
  constructor
  · intro hx
    have hraw := Game.equivalent_iff_toSupport _ _ |>.mp hx
    have hmk : x.toSupport =
        @ConwayRefinement.Standalone.InlineSurreal.Surreal.mk
          (Game.toSupport (Surreal.singletonIntegerCut x.game)) inferInstance := by
      rw [Surreal.toSupport_eq,
        ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_eq_mk]
      exact hraw
    exact hmk.trans (Surreal.toSupport_singletonIntegerCut x)
  · intro hx
    apply Game.equivalent_iff_toSupport _ _ |>.mpr
    apply ConwayRefinement.Standalone.InlineSurreal.Surreal.mk_eq_mk.mp
    rw [← Surreal.toSupport_eq]
    exact hx.trans (Surreal.toSupport_singletonIntegerCut x).symm

theorem Surreal.conwayRefinementProof : Surreal.ConwayConjecture.{u} := by
  intro a b c d ha hb hc hd habcd
  have ha' := (Surreal.isConwayOmnificInteger_iff_toSupport a).mp ha
  have hb' := (Surreal.isConwayOmnificInteger_iff_toSupport b).mp hb
  have hc' := (Surreal.isConwayOmnificInteger_iff_toSupport c).mp hc
  have hd' := (Surreal.isConwayOmnificInteger_iff_toSupport d).mp hd
  have habcd' := (Surreal.productsEqual_iff_toSupport a b c d).mp habcd
  obtain ⟨e, f, g, h, he, hf, hg, hh, hae, hbg, hce, hdf⟩ :=
    SupportBridge.supportConway a.toSupport b.toSupport c.toSupport d.toSupport
      ha' hb' hc' hd' habcd'
  refine ⟨Surreal.fromSupport e, Surreal.fromSupport f,
    Surreal.fromSupport g, Surreal.fromSupport h,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (Surreal.isConwayOmnificInteger_iff_toSupport _).mpr
    simpa only [Surreal.toSupport_fromSupport] using he
  · apply (Surreal.isConwayOmnificInteger_iff_toSupport _).mpr
    simpa only [Surreal.toSupport_fromSupport] using hf
  · apply (Surreal.isConwayOmnificInteger_iff_toSupport _).mpr
    simpa only [Surreal.toSupport_fromSupport] using hg
  · apply (Surreal.isConwayOmnificInteger_iff_toSupport _).mpr
    simpa only [Surreal.toSupport_fromSupport] using hh
  · apply (Surreal.equalsProduct_iff_toSupport _ _ _).mpr
    simpa only [Surreal.toSupport_fromSupport] using hae
  · apply (Surreal.equalsProduct_iff_toSupport _ _ _).mpr
    simpa only [Surreal.toSupport_fromSupport] using hbg
  · apply (Surreal.equalsProduct_iff_toSupport _ _ _).mpr
    simpa only [Surreal.toSupport_fromSupport] using hce
  · apply (Surreal.equalsProduct_iff_toSupport _ _ _).mpr
    simpa only [Surreal.toSupport_fromSupport] using hdf

end ConwayRefinement.Standalone.InlineConwayRefinement
