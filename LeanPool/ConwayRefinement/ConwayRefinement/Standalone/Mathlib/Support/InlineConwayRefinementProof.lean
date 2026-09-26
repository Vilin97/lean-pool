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

/-- The shared CombinatorialGames representation used by the proof bridge. -/
abbrev SupportGame := _root_.IGame

/-- Recursively convert an indexed Conway game to the auxiliary representation by its option
sets. -/
noncomputable def Game.toSupport : Game.{u} → SupportGame.{u}
  | .mk Left Right left right =>
      _root_.OfSets.ofSets
        (_root_.Player.cases
          (Set.range fun i : Left ↦ Game.toSupport (left i))
          (Set.range fun i : Right ↦ Game.toSupport (right i))) trivial

/-- Convert an auxiliary game to an indexed Conway game by shrinking its left and right option
sets. -/
@[expose] noncomputable def Game.fromSupport (x : SupportGame.{u}) : Game.{u} :=
  _root_.IGame.ofSetsRecOn x fun s t _ _ hs ht ↦
    .mk (Shrink s) (Shrink t)
      (fun i ↦
        let z := (equivShrink s).symm i
        hs z.1 z.2)
      (fun i ↦
        let z := (equivShrink t).symm i
        ht z.1 z.2)

theorem Game.fromSupport_ofSets (s t : Set SupportGame.{u}) [Small.{u} s] [Small.{u} t] :
    Game.fromSupport
        (_root_.OfSets.ofSets
          (_root_.Player.cases s t) trivial) =
      .mk (Shrink s) (Shrink t)
        (fun i ↦ Game.fromSupport ((equivShrink s).symm i).1)
        (fun i ↦ Game.fromSupport ((equivShrink t).symm i).1) := by
  rw [Game.fromSupport,
    _root_.IGame.ofSetsRecOn_ofSets]
  simp only [Game.fromSupport]

theorem Game.toSupport_fromSupport (x : SupportGame.{u}) :
    Game.toSupport (Game.fromSupport x) = x := by
  induction x using _root_.IGame.ofSetsRecOn with
  | ofSets s t ihs iht =>
      simp only [Game.fromSupport,
        _root_.IGame.ofSetsRecOn_ofSets, Game.toSupport]
      apply _root_.IGame.ext
      intro p
      simp only [_root_.IGame.moves_ofSets]
      cases p
      · ext z
        constructor
        · rintro ⟨i, rfl⟩
          let y := (equivShrink s).symm i
          change Game.toSupport (Game.fromSupport y.1) ∈ s
          simpa only [ihs y.1 y.2] using y.2
        · intro hz
          let i := equivShrink s ⟨z, hz⟩
          refine ⟨i, ?_⟩
          simpa only [i, Equiv.symm_apply_apply, Game.fromSupport] using ihs z hz
      · ext z
        constructor
        · rintro ⟨i, rfl⟩
          let y := (equivShrink t).symm i
          change Game.toSupport (Game.fromSupport y.1) ∈ t
          simpa only [iht y.1 y.2] using y.2
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
      rw [_root_.IGame.neg_ofSets]
      apply _root_.IGame.ext
      intro p
      simp only [_root_.IGame.moves_ofSets]
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
          rw [_root_.IGame.le_iff_forall_lf]
          simp only [Game.toSupport,
            _root_.IGame.moves_ofSets, Set.forall_mem_range]
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
    _root_.IGame.Numeric (Game.toSupport x) := by
  induction h with
  | mk hOrder hLeft hRight ihLeft ihRight =>
      rw [_root_.IGame.numeric_def]
      simp only [Game.toSupport,
        _root_.IGame.moves_ofSets, Set.forall_mem_range]
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
    (h : _root_.IGame.Numeric x) :
    Game.Numeric (Game.fromSupport x) := by
  revert h
  induction x using _root_.IGame.ofSetsRecOn with
  | ofSets s t ihLeft ihRight =>
      intro h
      have hdef := _root_.IGame.numeric_def.mp h
      simp only [_root_.IGame.moves_ofSets] at hdef
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
          (hdef.2 _root_.Player.left a.1 a.2)
      · intro j
        let b := (equivShrink t).symm j
        exact ihRight b.1 b.2
          (hdef.2 _root_.Player.right b.1 b.2)

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
          rw [_root_.IGame.ofSets_add_ofSets]
          apply _root_.IGame.ext
          intro p
          simp only [_root_.IGame.moves_ofSets]
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
                _root_.IGame.mulOption
                  (Game.toSupport x) (Game.toSupport y)
                  (Game.toSupport a) (Game.toSupport b) := by
            rw [Game.toSupport_add, Game.toSupport_add, Game.toSupport_neg,
              ih a y (Prod.Lex.left y y ha), ih x b (Prod.Lex.right x hb),
              ih a b (Prod.Lex.left b y ha)]
            rfl
          rw [Game.mul_mk]
          simp only [Game.toSupport]
          rw [_root_.IGame.mul_eq]
          apply _root_.IGame.ext
          intro p
          simp only [_root_.IGame.moves_ofSets]
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

/-- Map a numeric indexed-game representative to its surreal value in the auxiliary model. -/
noncomputable def Surreal.toSupport (x : Surreal.{u}) :
    _root_.Surreal.{u} :=
  @_root_.Surreal.mk _ x.numeric.toSupport

theorem Surreal.toSupport_eq (x : Surreal.{u}) :
    x.toSupport = @_root_.Surreal.mk _ x.numeric.toSupport :=
  (rfl)

/-- Choose a numeric indexed-game representative of a surreal number in the auxiliary model. -/
noncomputable def Surreal.fromSupport
    (x : _root_.Surreal.{u}) : Surreal.{u} :=
  ⟨Game.fromSupport x.out, Game.Numeric.fromSupport inferInstance⟩

theorem Surreal.fromSupport_game
    (x : _root_.Surreal.{u}) :
    (Surreal.fromSupport x).game = Game.fromSupport x.out := (rfl)

theorem Surreal.toSupport_fromSupport
    (x : _root_.Surreal.{u}) :
    (Surreal.fromSupport x).toSupport = x := by
  let : _root_.IGame.Numeric
      (Game.toSupport (Surreal.fromSupport x).game) :=
    (Surreal.fromSupport x).numeric.toSupport
  rw [Surreal.toSupport_eq]
  calc
    _root_.Surreal.mk
        (Game.toSupport (Surreal.fromSupport x).game) =
        _root_.Surreal.mk x.out := by
      apply _root_.Surreal.mk_eq
      have heq : Game.toSupport (Surreal.fromSupport x).game = x.out :=
        congrArg Game.toSupport (Surreal.fromSupport_game x) |>.trans
          (Game.toSupport_fromSupport x.out)
      rw [heq]
    _ = x := _root_.Surreal.out_eq x

theorem Surreal.gameEquivalent_iff_toSupport_eq (x y : Surreal.{u}) :
    Game.Equivalent x.game y.game ↔ x.toSupport = y.toSupport := by
  let : _root_.IGame.Numeric (Game.toSupport x.game) :=
    x.numeric.toSupport
  let : _root_.IGame.Numeric (Game.toSupport y.game) :=
    y.numeric.toSupport
  rw [Surreal.toSupport_eq, Surreal.toSupport_eq,
    _root_.Surreal.mk_eq_mk, Game.equivalent_iff]
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

/-- The map from indexed games modulo numeric equivalence to the auxiliary surreal model. -/
noncomputable def Surreal.QuotientModel.toSupport : Surreal.QuotientModel.{u} →
    _root_.Surreal.{u} :=
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
  · intro (x : _root_.Surreal.{v})
    exact ⟨Quotient.mk _ (Surreal.fromSupport x), Surreal.toSupport_fromSupport x⟩

/-- The quotient of the headline's numeric games is equivalent to the fully developed inlined
surreal numbers. -/
noncomputable def Surreal.quotientEquivSupport : Surreal.QuotientModel.{v} ≃
    _root_.Surreal.{v} :=
  Equiv.ofBijective Surreal.QuotientModel.toSupport.{v}
    Surreal.QuotientModel.toSupport_bijective

/-- The quotient of the completely visible inline representatives is exactly the surreal-number
type supplied by CombinatorialGames. -/
noncomputable def Surreal.quotientEquivCombinatorialGames :
    Surreal.QuotientModel.{u} ≃ _root_.Surreal.{u} :=
  Surreal.quotientEquivSupport

end ConwayRefinement.Standalone.InlineConwayRefinement
namespace ConwayRefinement.Standalone.InlineConwayRefinement.SupportBridge

universe u

theorem supportConway :
    ConwayRefinement.Standalone.InlineSurreal.Surreal.ConwayConjecture.{u} :=
  ConwayRefinement.Standalone.Oz.ConwayConjecture.proof

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
  let := a.numeric.toSupport
  let := b.numeric.toSupport
  let := c.numeric.toSupport
  let := d.numeric.toSupport
  rw [Game.equivalent_iff_toSupport, Game.toSupport_mul, Game.toSupport_mul]
  simp only [Surreal.toSupport_eq]
  rw [← _root_.Surreal.mk_mul,
    ← _root_.Surreal.mk_mul]
  rw [_root_.Surreal.mk_eq_mk]
  rfl

theorem Surreal.equalsProduct_iff_toSupport (a e f : Surreal.{u}) :
    Game.Equivalent a.game (Game.mul e.game f.game) ↔
      a.toSupport = e.toSupport * f.toSupport := by
  let := a.numeric.toSupport
  let := e.numeric.toSupport
  let := f.numeric.toSupport
  rw [Game.equivalent_iff_toSupport, Game.toSupport_mul]
  simp only [Surreal.toSupport_eq]
  rw [← _root_.Surreal.mk_mul]
  rw [_root_.Surreal.mk_eq_mk]
  rfl

theorem Game.toSupport_mk {Left Right : Type u}
    (left : Left → Game.{u}) (right : Right → Game.{u}) :
    Game.toSupport (.mk Left Right left right) =
      _root_.OfSets.ofSets
        (_root_.Player.cases
          (Set.range fun i : Left ↦ Game.toSupport (left i))
          (Set.range fun i : Right ↦ Game.toSupport (right i))) trivial := (rfl)

theorem Game.toSupport_zero : Game.toSupport (Game.zero : Game.{u}) =
    (0 : _root_.IGame.{u}) := by
  rw [Game.zero_eq, Game.toSupport_mk]
  apply _root_.IGame.ext
  intro p
  cases p
  · rw [_root_.IGame.moves_ofSets,
      _root_.IGame.moves_zero]
    ext z
    constructor
    · rintro ⟨i, _⟩
      exact nomatch i.down
    · simp
  · rw [_root_.IGame.moves_ofSets,
      _root_.IGame.moves_zero]
    ext z
    constructor
    · rintro ⟨i, _⟩
      exact nomatch i.down
    · simp

theorem Game.toSupport_one : Game.toSupport (Game.one : Game.{u}) =
    (1 : _root_.IGame.{u}) := by
  rw [Game.one_eq, Game.toSupport_mk]
  apply _root_.IGame.ext
  intro p
  cases p
  · rw [_root_.IGame.moves_ofSets]
    rw [_root_.IGame.one_def,
      _root_.IGame.moves_ofSets]
    ext z
    constructor
    · rintro ⟨_, rfl⟩
      exact Game.toSupport_zero
    · intro hz
      have hz' : z = 0 := by simpa using hz
      subst z
      exact ⟨PUnit.unit, Game.toSupport_zero⟩
  · rw [_root_.IGame.moves_ofSets,
      _root_.IGame.one_def,
      _root_.IGame.moves_ofSets]
    ext z
    constructor
    · rintro ⟨i, _⟩
      exact nomatch i.down
    · simp

theorem Game.toSupport_singletonIntegerCut_numeric (x : Surreal.{u}) :
    _root_.IGame.Numeric
      (Game.toSupport (Surreal.singletonIntegerCut x.game)) := by
  let := x.numeric.toSupport
  rw [Surreal.singletonIntegerCut_eq]
  rw [Game.toSupport_mk]
  rw [_root_.IGame.numeric_def]
  simp only [_root_.IGame.moves_ofSets,
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
    apply _root_.Surreal.mk_lt_mk.mp
    simp only [_root_.Surreal.mk_add,
      _root_.Surreal.mk_neg,
      _root_.Surreal.mk_one]
    linarith
  · intro p y hy
    cases p
    · obtain ⟨_, rfl⟩ := hy
      change _root_.IGame.Numeric
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
      change _root_.IGame.Numeric
        (ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport
          (ConwayRefinement.Standalone.InlineConwayRefinement.Game.add x.game
            ConwayRefinement.Standalone.InlineConwayRefinement.Game.one))
      rw [ConwayRefinement.Standalone.InlineConwayRefinement.Game.toSupport_add x.game
        (show Game.{u} from ConwayRefinement.Standalone.InlineConwayRefinement.Game.one)]
      rw [Game.toSupport_one]
      infer_instance

theorem Surreal.toSupport_sub_one (x : Surreal.{u}) :
    @_root_.Surreal.mk
        (Game.toSupport (Game.add x.game (Game.neg Game.one))) (by
          let := x.numeric.toSupport
          rw [Game.toSupport_add, Game.toSupport_neg, Game.toSupport_one]
          infer_instance) = x.toSupport - 1 := by
  let := x.numeric.toSupport
  simp only [Game.toSupport_add, Game.toSupport_neg, Game.toSupport_one]
  simpa only [_root_.Surreal.mk_neg,
    _root_.Surreal.mk_one, Surreal.toSupport_eq,
    sub_eq_add_neg] using
      (_root_.Surreal.mk_add
        (Game.toSupport x.game) (-1 : _root_.IGame.{u}))

theorem Surreal.toSupport_add_one (x : Surreal.{u}) :
    @_root_.Surreal.mk
        (Game.toSupport (Game.add x.game Game.one)) (by
          let := x.numeric.toSupport
          rw [Game.toSupport_add, Game.toSupport_one]
          infer_instance) = x.toSupport + 1 := by
  let := x.numeric.toSupport
  simp only [Game.toSupport_add, Game.toSupport_one]
  simpa only [_root_.Surreal.mk_one,
    Surreal.toSupport_eq] using
      (_root_.Surreal.mk_add
        (Game.toSupport x.game) (1 : _root_.IGame.{u}))

theorem Surreal.toSupport_singletonIntegerCut (x : Surreal.{u}) :
    @_root_.Surreal.mk
        (Game.toSupport (Surreal.singletonIntegerCut x.game))
        (Game.toSupport_singletonIntegerCut_numeric x) =
      ConwayRefinement.Standalone.InlineSurreal.Surreal.singletonIntegerCut x.toSupport := by
  simp only [Surreal.singletonIntegerCut_eq, Game.toSupport_mk]
  rw [ConwayRefinement.Standalone.InlineSurreal.Surreal.singletonIntegerCut]
  rw [_root_.Surreal.mk_ofSets]
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
  let := x.numeric.toSupport
  let := Game.toSupport_singletonIntegerCut_numeric x
  rw [Surreal.isConwayOmnificInteger_iff,
    ConwayRefinement.Standalone.InlineSurreal.Surreal.IsConwayOmnificInteger]
  constructor
  · intro hx
    have hraw := Game.equivalent_iff_toSupport _ _ |>.mp hx
    have hmk : x.toSupport =
        @_root_.Surreal.mk
          (Game.toSupport (Surreal.singletonIntegerCut x.game)) inferInstance := by
      rw [Surreal.toSupport_eq,
        _root_.Surreal.mk_eq_mk]
      exact hraw
    exact hmk.trans (Surreal.toSupport_singletonIntegerCut x)
  · intro hx
    apply Game.equivalent_iff_toSupport _ _ |>.mpr
    apply _root_.Surreal.mk_eq_mk.mp
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
