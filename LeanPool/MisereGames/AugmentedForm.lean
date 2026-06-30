/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Form
public import LeanPool.MisereGames.GameForm
public import LeanPool.MisereGames.Form.Misere.Outcome

/-!
Misere combinatorial games.
-/

namespace MisereGames

public noncomputable section

universe u

/-!
# Augmented Form

This module defines `AugmentedForm`: these are Siegel's *augmented forms*,
which apart from ordinary options may also have tombstones, as defined in
[Siegel, Definition 5.1 on p. 212][siegel:GeneralDeadendingUniverse:2025].

The main result is `AugmentedForm.instForm`.

## References

* [A. N. Siegel, *On the general dead-ending universe of partizan
games*][siegel:GeneralDeadendingUniverse:2025]
-/

/--
Like `GameFunctor`, but each position may contain Left and/or Right tombstones.
-/
private def AugmentedFunctor (α : Type (u + 1)) : Type (u + 1) :=
  {s : Player → Set α // ∀ p, Small.{u} (s p)} × (Player → Prop)

namespace AugmentedFunctor

@[ext] private theorem ext {α : Type (u + 1)} {x y : AugmentedFunctor α} :
    x.1 = y.1 → x.2 = y.2 → x = y := by
  intro h1 h2
  apply Prod.ext
  · exact h1
  · exact h2

private instance {α : Type (u + 1)} (x : AugmentedFunctor α) (p : Player) :
    Small.{u} (x.1.1 p) := x.1.2 p

private instance : Functor AugmentedFunctor where
  map f s := ⟨⟨(f '' s.1.1 ·), fun _ => inferInstance⟩, s.2⟩

private theorem map_def {α β} (f : α → β) (s : AugmentedFunctor α) :
    f <$> s = ⟨⟨(f '' s.1.1 ·), fun _ => inferInstance⟩, s.2⟩ :=
  rfl

private instance : QPF AugmentedFunctor where
  P := ⟨(Player → Type u) × (Player → Prop), fun ⟨x, _⟩ ↦ Σ p, PLift (x p)⟩
  abs x := ⟨⟨fun p ↦ Set.range (x.2 ∘ .mk p ∘ PLift.up), fun _ ↦ inferInstance⟩, x.1.2⟩
  repr x := ⟨⟨fun p ↦ Shrink (x.1.1 p), x.2⟩, Sigma.rec (fun _ y ↦ ((equivShrink _).symm y.1).1)⟩
  abs_repr x := by
    cases x with | mk s b =>
    refine AugmentedFunctor.ext ?_ rfl
    apply Subtype.ext; funext p; ext y; constructor
    · rintro ⟨x, hx⟩; exact hx ▸ ((equivShrink ↑(s.1 p)).symm x).2
    · intro hy; exact ⟨equivShrink ↑(s.1 p) ⟨y, hy⟩,
        congrArg Subtype.val ((equivShrink ↑(s.1 p)).left_inv ⟨y, hy⟩)⟩
  abs_map f := by
    intro ⟨⟨x, b⟩, g⟩
    ext
    · simp [PFunctor.map, map_def]
    · simp [PFunctor.map, map_def]

end AugmentedFunctor

/--
Like `GameForm`, but each position may contain Left and/or Right tombstones.
-/
def AugmentedForm : Type (u + 1) :=
  QPF.Fix AugmentedFunctor

namespace AugmentedForm

open Form

private def moves' (p : Player) (x : AugmentedForm.{u}) : Set AugmentedForm.{u} :=
  x.dest.1.1 p

@[no_expose] instance : Moves AugmentedForm where
  moves := moves'
  isOption'_wf := by
    refine ⟨fun x ↦ ?_⟩
    apply QPF.Fix.ind
    unfold Moves.IsOption' moves'
    rintro _ ⟨⟨st, hst⟩, rfl⟩
    constructor
    rintro y hy
    rw [QPF.Fix.dest_mk, Set.mem_iUnion] at hy
    obtain ⟨_, ⟨_, h⟩, _, rfl⟩ := hy
    exact h

/--
Check if a given `Player` has a tombstone.
-/
def hasTombstone (p : Player) (x : AugmentedForm) : Prop :=
  x.dest.2 p

/--
Construct an `AugmentedForm` from available options and tombstones.
-/
def ofSetsWithTombs (st : Player → Set AugmentedForm) (tomb : Player → Prop)
    [Small.{u} (st .left)] [Small.{u} (st .right)] : AugmentedForm :=
  QPF.Fix.mk ⟨⟨st, fun
    | .left => (inferInstance : Small.{u} (st .left))
    | .right => (inferInstance : Small.{u} (st .right))⟩, tomb⟩

instance : OfSets AugmentedForm fun _ ↦ True where
  ofSets st _ := ofSetsWithTombs st (fun _ => False)

private theorem moves_ofSets' (p) (st :
    Player → Set AugmentedForm) [Small.{u} (st .left)] [Small.{u} (st .right)] :
    moves p !{st} = st p := by
  dsimp [ofSets, ofSetsWithTombs, moves]; rw [moves', QPF.Fix.dest_mk]

@[simp]
theorem moves_ofSetsWithTombs (p) (st : Player → Set AugmentedForm) (tomb : Player → Prop)
    [Small.{u} (st .left)] [Small.{u} (st .right)] :
    moves p (ofSetsWithTombs st tomb) = st p := by
  dsimp [ofSetsWithTombs, moves]; rw [moves', QPF.Fix.dest_mk]

@[simp]
theorem hasTombstone_ofSets
    (st : Player → Set AugmentedForm) [Small.{u} (st .left)] [Small.{u} (st .right)]
    (p : Player) : ¬!{st}.hasTombstone p := by
  dsimp [ofSets, ofSetsWithTombs]
  rw [hasTombstone, QPF.Fix.dest_mk]
  cases p <;> simp only [not_false_eq_true]

@[simp]
theorem hasTombstone_ofSetsWithTombs (p : Player) (st : Player → Set AugmentedForm)
    [Small.{u} (st .left)] [Small.{u} (st .right)] (tomb : Player → Prop)
    : (ofSetsWithTombs st tomb).hasTombstone p = tomb p := by
  simp only [hasTombstone, ofSetsWithTombs, QPF.Fix.dest_mk]

instance (p : Player) (x : AugmentedForm.{u}) : Small.{u} (moves p x) := x.dest.1.2 p

@[simp]
theorem ofSets_moves_tombs (x : AugmentedForm) :
    ofSetsWithTombs (fun p => moves p x) (fun p => x.hasTombstone p) = x := by
  simp only [ofSetsWithTombs, moves, moves', hasTombstone]
  unfold AugmentedForm at x
  have h1 : (fun x_1 ↦
        match x_1 with
        | Player.left => x.dest.2 Player.left
        | Player.right => x.dest.2 Player.right) = x.dest.2 := by
       funext p
       cases p <;> rfl
  simp only [Subtype.coe_eta, Prod.mk.eta, QPF.Fix.mk_dest]

/--
Two `AugmentedForm`s are equal if they have the same options and tombstones.
-/
@[ext]
theorem ext {x y : AugmentedForm.{u}}
    (h_moves : ∀ p, moves p x = moves p y)
    (h_tomb : ∀ p, x.hasTombstone p ↔ y.hasTombstone p)
    : x = y := by
  rw [← ofSets_moves_tombs x, ← ofSets_moves_tombs y]
  simp_rw [funext h_moves, h_tomb]

/--
This is Conway induction.
-/
@[elab_as_elim]
def moveRecOn {motive : AugmentedForm → Sort*} (x)
    (mk : Π x, (Π p, Π y ∈ moves p x, motive y) → motive x) : motive x :=
  mk x (fun p y _ ↦ moveRecOn y mk)
  termination_by x
  decreasing_by form_wf

theorem moveRecOn_eq {motive : AugmentedForm → Sort*} (x)
    (mk : Π x, (Π p, Π y ∈ moves p x, motive y) → motive x) :
    moveRecOn x mk = mk x (fun _ y _ ↦ moveRecOn y mk) := by
  rw [moveRecOn]

open scoped Classical in
private noncomputable def EndLike (p : Player) (g : AugmentedForm) : Prop :=
  g.hasTombstone p ∨ (Form.IsEnd p g)

private noncomputable def add' (x y : AugmentedForm) : AugmentedForm :=
  ofSetsWithTombs
    (fun p => (Set.range fun z : moves p x => add' z y) ∪ (Set.range fun z : moves p y => add' x z))
    (fun p => (x.hasTombstone p ∧ EndLike p y) ∨ (y.hasTombstone p ∧ EndLike p x))
  termination_by (x, y)
  decreasing_by form_wf

@[no_expose] noncomputable instance : Add AugmentedForm where
  add := add'

/--
Convert a `GameForm` to an `AugmentedForm` with no tombstones.
-/
def ofGameForm (g : GameForm) : AugmentedForm :=
  ofSetsWithTombs
    (fun p => Set.range (fun gp : moves p g => ofGameForm gp))
    (fun _ => False)
    termination_by g
    decreasing_by form_wf

instance : Coe GameForm AugmentedForm where
  coe := ofGameForm

/--
An `AugmentedForm` is `TombstoneFree` if no player has a tombstone and all
options are `TombstoneFree`.
-/
def TombstoneFree (g : AugmentedForm) : Prop :=
  (∀ p, ¬g.hasTombstone p) ∧ ∀ p, ∀ h ∈ moves p g, TombstoneFree h
  termination_by g
  decreasing_by form_wf

theorem TombstoneFree.not_hasTombstone {g : AugmentedForm} (h1 : TombstoneFree g) :
  ∀ p, ¬g.hasTombstone p := by
  unfold TombstoneFree at h1
  exact h1.left

theorem TombstoneFree.moves {g : AugmentedForm} (h1 : TombstoneFree g) :
  ∀ p, ∀ h ∈ moves p g, TombstoneFree h := by
  unfold TombstoneFree at h1
  exact h1.right

theorem ofSetsWithTombs_ff_TombstoneFree
    {st : Player → Set AugmentedForm} [Small.{u} (st .left)] [Small.{u} (st .right)]
    (h1 : ∀ p, ∀ gp ∈ st p,
      TombstoneFree gp) : TombstoneFree (ofSetsWithTombs st (fun _ => False)) := by
  unfold TombstoneFree
  constructor
  · simp only [hasTombstone_ofSetsWithTombs, forall_const, not_false_eq_true]
  · intro p gp h2
    refine h1 p gp ?_
    rw [moves_ofSetsWithTombs] at h2
    exact h2

/--
Convert a `TombstoneFree` `AugmentedForm` to a `GameForm` by 'forgetting' about
the missing tombstones.
-/
def toGameForm (g : AugmentedForm) (h : TombstoneFree g) : GameForm :=
  !{Set.range (fun gl : moves .left g => toGameForm gl (h.moves .left gl gl.property)) |
    Set.range (fun gr : moves .right g => toGameForm gr (h.moves .right gr gr.property))}
termination_by g
decreasing_by form_wf

theorem ofGameForm_tombstoneFree (g : GameForm) : TombstoneFree (ofGameForm g) := by
  induction g using GameForm.moveRecOn with
  | mk g ih =>
    unfold ofGameForm
    apply ofSetsWithTombs_ff_TombstoneFree
    intro p gp ⟨h3, h4⟩
    rw [<-h4]
    exact ih p h3 (Subtype.coe_prop h3)

@[simp]
theorem not_hasTombstone_ofGameForm (g : GameForm) (p : Player)
    : ¬hasTombstone p (ofGameForm g) :=
  (ofGameForm_tombstoneFree g).not_hasTombstone p

theorem ofSetsWithTombs_eq
    {as : Player → Set AugmentedForm} [Small.{u} (as .left)] [Small.{u} (as .right)]
    {bs : Player → Set AugmentedForm} [Small.{u} (bs .left)] [Small.{u} (bs .right)]
    {tombL tombR : Player → Prop}
    (h1 : ofSetsWithTombs as tombL = ofSetsWithTombs bs tombR) : as = bs := by
  have ⟨h2, _⟩ := AugmentedForm.ext_iff.mp h1
  simp only [moves_ofSetsWithTombs] at h2
  exact funext_iff.mpr h2

private theorem ofGameForm_Injective' {x y : GameForm} (h1 : ofGameForm x = ofGameForm y)
    : x = y := by
  ext p g
  have h3 := (fun p => congrArg (moves p) h1) p
  unfold ofGameForm at h3
  simp only [moves_ofSetsWithTombs, Set.range_eq_iff, Set.mem_range, Subtype.exists, exists_prop,
             Subtype.forall, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h3
  obtain ⟨h3, h4⟩ := h3
  constructor <;> intro h5
  · obtain ⟨yp, h6, h7⟩ := h3 g h5
    rw [ofGameForm_Injective' h7.symm]
    exact h6
  · obtain ⟨xp, h6, h7⟩ := h4 g h5
    rw [(ofGameForm_Injective' h7).symm]
    exact h6
termination_by (x, y)
decreasing_by form_wf

theorem ofGameForm_Injective : Function.Injective ofGameForm := by
  intro _ _ h1
  exact ofGameForm_Injective' h1

theorem ofGameForm_moves_mem_iff {g gp : GameForm} {p : Player}
    : (ofGameForm gp ∈ moves p (ofGameForm g)) ↔ (gp ∈ moves p g) := by
  constructor <;> intro h1
  · rw [ofGameForm, moves_ofSetsWithTombs] at h1
    simp only [Set.mem_range, Subtype.exists, exists_prop] at h1
    obtain ⟨gpp, h1, h2⟩ := h1
    rwa [ofGameForm_Injective h2] at h1
  · unfold ofGameForm
    rw [moves_ofSetsWithTombs, Set.mem_range, <-ofGameForm, SetCoe.exists]
    use gp, h1

theorem toGameForm_moves_mem' {g gp : AugmentedForm} {p : Player} (h1 : gp ∈ moves p g)
    (h2 : TombstoneFree g)
    : (toGameForm gp (TombstoneFree.moves h2 p gp h1) ∈ moves p (toGameForm g h2)) := by
  unfold toGameForm
  cases p
  all_goals
  · simp only [leftMoves_ofSets, rightMoves_ofSets, Set.mem_range, Subtype.exists]
    use gp, h1
    rw [toGameForm]

@[simp]
theorem toGameForm_ofGameForm (g : GameForm) :
  toGameForm (ofGameForm g) (ofGameForm_tombstoneFree g) = g := by
  ext p gp
  constructor <;> intro h1
  · unfold ofGameForm toGameForm at h1
    simp only [moves_ofSets, Player.cases] at h1
    cases p
    all_goals
    · simp only [Set.mem_range, Subtype.exists, moves_ofSetsWithTombs, exists_prop] at h1
      obtain ⟨g2, ⟨g3, ⟨h2, h3⟩⟩, h4⟩ := h1
      simp only [<-h3, <-h4, toGameForm_ofGameForm g3]
      exact h2
  · unfold ofGameForm toGameForm
    simp only [moves_ofSets, Player.cases]
    cases p
    all_goals
    · simp only [Set.mem_range, Subtype.exists, moves_ofSetsWithTombs, exists_prop]
      use (ofGameForm gp)
      exact Exists.intro (by use gp) (toGameForm_ofGameForm gp)
termination_by g
decreasing_by form_wf

@[simp]
theorem ofGameForm_toGameForm (g : AugmentedForm) (h1 : TombstoneFree g) :
  ofGameForm (toGameForm g h1) = g := by
  unfold ofGameForm
  ext p x
  · simp only [moves_ofSetsWithTombs, Set.mem_range, Subtype.exists, exists_prop]
    constructor <;> intro h2
    · unfold toGameForm ofGameForm at h2
      simp only [moves_ofSets, Player.cases] at h2
      cases p
      all_goals
      · simp only [Set.mem_range, Subtype.exists] at h2
        obtain ⟨gg, ⟨gl, h3, h4⟩, h5⟩ := h2
        rw [<-h5, <-ofGameForm, <-h4, ofGameForm_toGameForm gl (TombstoneFree.moves h1 _ gl h3)]
        exact h3
    · use toGameForm x (TombstoneFree.moves h1 p x h2)
      constructor
      · exact toGameForm_moves_mem' h2 h1
      · exact ofGameForm_toGameForm x (TombstoneFree.moves h1 p x h2)
  · simp only [hasTombstone_ofSetsWithTombs, h1, TombstoneFree.not_hasTombstone]
termination_by g
decreasing_by form_wf

private theorem add_eq (x y : AugmentedForm) : x + y =
    ofSetsWithTombs
      (Player.cases
        ((· + y) '' moves .left x ∪ (x + ·) '' moves .left y)
        ((· + y) '' moves .right x ∪ (x + ·) '' moves .right y))
      (Player.cases
        ((x.hasTombstone .left ∧ EndLike .left y) ∨ (y.hasTombstone .left ∧ EndLike .left x))
        ((x.hasTombstone .right ∧ EndLike .right y) ∨
          (y.hasTombstone .right ∧ EndLike .right x))) := by
  change add' _ _ = _
  rw [add']
  congr 1
  all_goals
  · ext p
    cases p <;> simp [HAdd.hAdd, Add.add]

private theorem add_eq' (x y : AugmentedForm) : x + y =
    ofSetsWithTombs
      (fun p => (· + y) '' moves p x ∪ (x + ·) '' moves p y)
      (fun p => (x.hasTombstone p ∧ EndLike p y) ∨ (y.hasTombstone p ∧ EndLike p x)) := by
  rw [add_eq]
  congr 1
  all_goals
  · ext p
    cases p <;> rfl

private theorem hasTombstone_add' {x y : AugmentedForm} {p : Player} :
    (x + y).hasTombstone p ↔
      ((x.hasTombstone p ∧ EndLike p y) ∨ (y.hasTombstone p ∧ EndLike p x)) := by
  rw [add_eq]
  cases p <;> simp only [hasTombstone_ofSetsWithTombs]

@[simp]
private theorem moves_add' (p : Player) (x y : AugmentedForm) :
    moves p (x + y) = (· + y) '' moves p x ∪ (x + ·) '' moves p y := by
  rw [add_eq', moves_ofSetsWithTombs]

private theorem add_comm' (x y : AugmentedForm) : x + y = y + x := by
  ext
  · simp only [moves_add', Set.mem_union, Set.mem_image, or_comm]
    congr! 3 <;>
    · refine and_congr_right_iff.2 fun h ↦ ?_
      rw [add_comm']
  · simp only [hasTombstone_add', or_comm]
termination_by (x, y)
decreasing_by form_wf

lemma hasTombstone_add_assoc (x y z : AugmentedForm) (p : Player) :
    hasTombstone p (x + y + z) ↔ hasTombstone p (x + (y + z)) := by
  simp only [hasTombstone_add']
  unfold EndLike
  by_cases h1 : hasTombstone p x
  <;> by_cases h2 : hasTombstone p y
  <;> by_cases h3 : hasTombstone p z
  <;> simp only [h1, h2, h3, hasTombstone_add', And.comm, EndLike, and_self, and_true,
                 false_and, false_or, iff_or_self, or_false, or_iff_left_iff_imp, or_self,
                 or_self_left, true_and, true_or, isEnd_def]
  <;> by_cases h4 : moves p x = ∅
  <;> by_cases h5 : moves p y = ∅
  <;> by_cases h6 : moves p z = ∅
  <;> simp [h4, h5, h6]

private theorem add_assoc' (x y z : AugmentedForm) : x + y + z = x + (y + z) := by
  ext1
  · simp only [moves_add', Set.image_union, Set.image_image, Set.union_assoc]
    refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_) <;>
    · ext
      congr! 2
      rw [add_assoc']
  · exact hasTombstone_add_assoc x y z _
termination_by (x, y, z)
decreasing_by form_wf

theorem ofGameForm_exists_preimage {a : AugmentedForm} (h1 : TombstoneFree a)
    : ∃g, ofGameForm g = a := by
  unfold ofGameForm
  use !{fun p => Set.range (fun ap :
      moves p a => toGameForm ap (h1.moves p ap (Subtype.coe_prop ap)))}
  rw [AugmentedForm.ext_iff]
  simp only [moves_ofSetsWithTombs]
  constructor
  · intro p
    refine Eq.symm (Set.ext ?_)
    intro al
    constructor <;> intro h2
    · simp only [Set.mem_range, Subtype.exists, moves_ofSets, exists_prop]
      use (toGameForm al (TombstoneFree.moves h1 p al h2))
      simp only [ofGameForm_toGameForm, and_true]
      use al, h2
    · simp only [Set.mem_range, Subtype.exists, moves_ofSets, exists_prop] at h2
      obtain ⟨g1, ⟨g2, h6, h7⟩, h5⟩ := h2
      simp only [<-h5, <-h7, ofGameForm_toGameForm, h6]
  · simp only [h1, hasTombstone_ofSetsWithTombs, TombstoneFree.not_hasTombstone, implies_true]

theorem mem_moves_ofGameForm {g : GameForm} {ap : AugmentedForm} {p : Player}
    (h1 : ap ∈ moves p (ofGameForm g)) : ∃ gp ∈ moves p g, ofGameForm gp = ap := by
  have h2 : TombstoneFree (ofGameForm g) := by exact ofGameForm_tombstoneFree g
  have h3 : TombstoneFree ap := TombstoneFree.moves h2 p ap h1
  obtain ⟨gp, h3⟩ := ofGameForm_exists_preimage h3
  use gp
  refine And.intro ?_ h3
  rw [<-h3] at h1
  exact ofGameForm_moves_mem_iff.mp h1

theorem ofGameForm_add (g h : GameForm) : ofGameForm (g + h) = ofGameForm g + ofGameForm h := by
  rw [add_eq']
  simp only [not_hasTombstone_ofGameForm, false_and, or_self]
  rw [GameForm.add_eq']
  rw [ofGameForm]
  refine ext ?_ (by simp only [hasTombstone_ofSetsWithTombs, implies_true])
  intro p
  simp only [moves_ofSetsWithTombs, Set.range_eq_iff, Set.mem_union, Set.mem_image, Subtype.forall,
             moves_ofSets, Subtype.exists, exists_prop]
  constructor
  · intro ghp h3
    apply Or.elim h3 <;> intro ⟨x, h3, h4⟩ <;> rw [<-h4]
    · apply Or.inl
      use ofGameForm x
      exact And.intro (ofGameForm_moves_mem_iff.mpr h3) (ofGameForm_add x h).symm
    · apply Or.inr
      use ofGameForm x
      exact And.intro (ofGameForm_moves_mem_iff.mpr h3) (ofGameForm_add g x).symm
  · intro ghp h3
    apply Or.elim h3
      <;> intro ⟨_, h3, h4⟩
      <;> obtain ⟨x, h5, h6⟩ := mem_moves_ofGameForm h3
      <;> rw [<-h4]
    · use (x + h)
      constructor
      · apply Or.inl
        use x
      · rw [<-h6]
        exact ofGameForm_add x h
    · use (g + x)
      constructor
      · apply Or.inr
        use x
      · rw [<-h6]
        exact ofGameForm_add g x
termination_by (g, h)
decreasing_by form_wf

private def neg' (x : AugmentedForm) : AugmentedForm :=
  ofSetsWithTombs
    (fun p => (Set.range fun xp : moves (-p) x => neg' xp))
    (fun p => hasTombstone (-p) x)
termination_by x
decreasing_by form_wf

@[no_expose] instance : Neg AugmentedForm where
  neg := neg'

theorem neg_eq (x : AugmentedForm)
    : (-x) = ofSetsWithTombs
               (fun p => (Set.range fun xp : moves (-p) x => -xp))
               (fun p => hasTombstone (-p) x) := by
  simp only [Neg.neg, Player.cases]
  rw [neg']
  congr

private theorem neg_eq' (x : AugmentedForm)
    : (-x) = ofSetsWithTombs
               (fun p => (Set.range fun xp : moves (-p) x => neg' xp))
               (fun p => hasTombstone (-p) x) := by
  simp only [Neg.neg, Player.cases]
  rw [neg']
  congr

private theorem neg'_eq (x : AugmentedForm) : (-x) = neg' x := by rfl

private theorem neg_neg' (x : AugmentedForm) : -(-x) = x := by
  simp only [neg_eq', hasTombstone_ofSetsWithTombs, neg_neg]
  rw [<-ofSets_moves_tombs x]
  congr
  funext p
  ext xp
  simp only [Set.mem_range, Subtype.exists, ofSets_moves_tombs, moves_ofSetsWithTombs,
             exists_prop, exists_exists_and_eq_and]
  constructor <;> intro h1
  · obtain ⟨yp, h1, h2⟩ := h1
    have h3 : neg' (neg' yp) = -(-yp) := rfl
    rw [<-h2, h3, neg_neg' yp]
    rw [neg_neg] at h1
    exact h1
  · use xp
    rw [neg_neg p]
    apply And.intro h1
    have h3 : neg' (neg' xp) = -(-xp) := rfl
    rw [h3, neg_neg' xp]
termination_by x
decreasing_by form_wf

instance : InvolutiveNeg AugmentedForm where
  neg_neg := private neg_neg'

private theorem moves_neg' (p : Player) (x : AugmentedForm) :
    moves p (-x) = -moves (-p) x := by
  rw [neg_eq, moves_ofSetsWithTombs]
  ext y
  simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_neg]
  apply Iff.intro <;> intro h1
  · obtain ⟨a, h1, h2⟩ := h1
    rwa [<-h2, neg_neg]
  · use -y, h1
    rw [neg_neg]

private theorem hasTombstone_neg' (x : AugmentedForm) (p : Player)
    : hasTombstone p (-x) ↔ hasTombstone (-p) x := by
  rw [neg_eq, hasTombstone_ofSetsWithTombs]

private theorem EndLike_neg' (x : AugmentedForm) (p : Player)
    : EndLike p (-x) ↔ EndLike (-p) x := by
  rw [neg_eq]
  simp [EndLike, isEnd_def]

private theorem neg_add' (x y : AugmentedForm) : -(x + y) = -x + -y := by
  ext
  · simp only [moves_neg', moves_add', Set.union_neg, Set.mem_union, Set.mem_neg, Set.mem_image,
      Set.exists_neg_mem]
    congr! 3 <;>
    · refine and_congr_right_iff.2 fun _ ↦ ?_
      rw [← neg_inj, neg_add', neg_neg]
  · simp [hasTombstone_neg', EndLike_neg', hasTombstone_add']
termination_by (x, y)
decreasing_by form_wf

instance : AddCommSemigroup AugmentedForm where
  add_assoc := private add_assoc'
  add_comm := private add_comm'

theorem not_hasTombstone_zero' (p : Player) : ¬(!{fun _ => ∅} : AugmentedForm).hasTombstone p := by
  exact hasTombstone_ofSets (fun x ↦ ∅) p

theorem add_eq_zero_iff {x y : AugmentedForm}
    : x + y = !{fun _ => ∅} ↔ x = !{fun _ => ∅} ∧ y = !{fun _ => ∅} := by
  constructor
    <;> simp [AugmentedForm.ext_iff, EndLike, isEnd_def, hasTombstone_add', moves_ofSets']
    <;> tauto

private lemma hasTombstone_add_zero' (g : AugmentedForm) (p : Player)
    : (g + !{fun _ => ∅}).hasTombstone p ↔ g.hasTombstone p := by
  simp [hasTombstone_add', EndLike, isEnd_def, moves_ofSets']

private lemma add_zero' (x : AugmentedForm) : x + !{fun _ ↦ ∅} = x := by
  refine moveRecOn x ?_
  intro x ih
  ext
  · aesop (add simp [moves_ofSets'])
  · exact hasTombstone_add_zero' x _

noncomputable instance : Form AugmentedForm where
  moves_neg' := by
    intro p x
    simp only [neg_eq']
    simp only [←neg'_eq, ←Set.neg_range, Subtype.range_coe_subtype, Set.setOf_mem_eq,
               moves_ofSetsWithTombs]
  moves_add' := private moves_add'
  moves_small' := instSmallElemMoves
  IsEndLike p g := g.hasTombstone p ∨ (Form.IsEnd p g)
  isEndLike_ofEnd' _ _ h1 := by
    rw [<-isEnd_def] at h1
    exact Or.inr h1
  isEndLike_add_iff' p x y := by
    simp only [EndLike, hasTombstone_add', isEnd_def, moves_add',
               Set.union_empty_iff, Set.image_eq_empty]
    tauto
  isEndLike_neg_iff_neg' p g := by
    apply or_congr (hasTombstone_neg' g p)
    constructor <;> cases p
    all_goals
    · intro h1
      simp only [moves_neg', Player.neg_left, Player.neg_right, Set.neg_eq_empty, isEnd_def] at h1 ⊢
      exact h1
  moves_ofSets' := private moves_ofSets'
  add_zero' := private add_zero'
  add_eq_zero_iff' _ _ := private add_eq_zero_iff
  ofSets_inj'' := by
    intro st1 st2 _ _ _ _
    apply Iff.intro <;> intro h1
    · exact ofSetsWithTombs_eq h1
    · simp [h1]
  neg_ofSets'' s t _ _ := by
    simp only [neg_eq', hasTombstone_ofSets]
    ext p x
    · cases p
      · simp only [moves_ofSetsWithTombs, Player.neg_left, Set.mem_range, Subtype.exists,
          moves_ofSets', Player.cases, exists_prop, Set.mem_neg]
        apply Iff.intro
        · intro ⟨y, h1, h2⟩
          rwa [<-h2, <-neg'_eq, neg_neg]
        · intro h1
          use -x, h1
          rw [<-neg'_eq, neg_neg]
      · simp only [moves_ofSetsWithTombs, Player.neg_right, Set.mem_range, Subtype.exists,
          moves_ofSets', Player.cases, exists_prop, Set.mem_neg]
        apply Iff.intro
        · intro ⟨y, h1, h2⟩
          rwa [<-h2, <-neg'_eq, neg_neg]
        · intro h1
          use -x, h1
          rw [<-neg'_eq, neg_neg]
    · simp
  neg_add' := private neg_add'
  smallElemMoves' := instSmallElemMoves
  ofSets_isEndLike_iff' p s t _ _ := by
    apply Iff.intro <;> intro h1
    · simp only [hasTombstone_ofSets, false_or] at h1
      rwa [isEnd_def] at h1
    · rw [isEnd_def]
      exact Or.inr h1
  ofSets_add_ofSets'' s1 t1 s2 t2 _ _ _ _ := by
    dsimp [ofSets]
    rw [add_eq']
    ext p x
    · simp only [moves_ofSetsWithTombs]
      aesop
    · simp
  ofSets_moves_of_not_isEndLike' := @fun g _ _ hg => by
    ext p
    · simp [moves_ofSets']
    · simp only [hasTombstone_ofSets, false_iff]
      exact fun h => hg p (Or.inl h)

lemma IsEndLike_iff {g : AugmentedForm} {p : Player} :
    IsEndLike p g ↔ (g.hasTombstone p ∨ (Form.IsEnd p g)) := by rfl

-- We make no use of `AugmentedForm`'s definition from a `QPF` after this
-- point.

attribute [irreducible] AugmentedForm

theorem ofGameForm_zero : ofGameForm (0 : GameForm) = (0 : AugmentedForm) := by
  rw [zero_def, zero_def, ofGameForm]
  ext p x <;> simp

/--
The coercion from `GameForm` to `AugmentedForm` is an additive monoid
homomorphism.
-/
def ofGameFormHom : GameForm →+ AugmentedForm where
  toFun := ofGameForm
  map_zero' := ofGameForm_zero
  map_add' := ofGameForm_add

theorem ofGameFormHom_injective : Function.Injective ofGameFormHom := by
  intro g h eq
  exact ofGameForm_Injective eq

theorem hasTombstone_neg_iff {g : AugmentedForm} {p : Player}
    : hasTombstone p (-g) ↔ hasTombstone (-p) g := by
  rw [neg_eq']
  exact Eq.to_iff rfl

@[simp]
theorem hasTombstone_add {x y : AugmentedForm} {p : Player} :
    (x + y).hasTombstone p ↔
      ((x.hasTombstone p ∧ IsEndLike p y) ∨ (y.hasTombstone p ∧ IsEndLike p x)) := by
  exact hasTombstone_add'

lemma not_isEndLike_iff {g : AugmentedForm} {p : Player}
    : ¬IsEndLike p g ↔ ¬hasTombstone p g ∧ ¬IsEnd p g := by
  simp only [IsEndLike_iff, not_or]

@[simp]
theorem isEndLike_ofGameForm_iff_isEnd {g : GameForm} {p : Player} :
    IsEndLike p (ofGameForm g) ↔ Form.IsEnd p g := by
  constructor <;> intro h1
  · unfold ofGameForm at h1
    apply Or.elim h1 <;> intro h1
    · simp only [hasTombstone_ofSetsWithTombs] at h1
    · simp only [moves_ofSetsWithTombs, Set.range_eq_empty_iff, Set.isEmpty_coe_sort,
      isEnd_def] at h1
      rw [isEnd_def]
      exact h1
  · unfold ofGameForm
    apply Or.inr
    rw [isEnd_def, moves_ofSetsWithTombs]
    simp only [Set.range_eq_empty_iff, Set.isEmpty_coe_sort]
    rw [<-isEnd_def]
    exact h1

theorem mem_ofGameForm_exists_mem {g : GameForm} {gp : AugmentedForm} {p : Player}
  (h1 : AugmentedForm.TombstoneFree gp)
  (h2 : gp ∈ Form.moves p (AugmentedForm.ofGameForm g))
    : ∃ gp', gp' ∈ Form.moves p g ∧ AugmentedForm.ofGameForm gp' = gp := by
  have ⟨gp', h4⟩ := AugmentedForm.ofGameForm_exists_preimage h1
  rw [<-h4] at h2
  have h5 := AugmentedForm.ofGameForm_moves_mem_iff.mp h2
  use gp'

end AugmentedForm

end

end MisereGames
