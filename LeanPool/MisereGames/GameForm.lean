/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Alfie Davies, contributors
-/
module

public import LeanPool.MisereGames.Mathlib.Small
public import LeanPool.MisereGames.OfSets
public import LeanPool.MisereGames.Form
public import Mathlib.Algebra.Group.Pointwise.Set.Small
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.QPF.Univariate.Basic
public import Mathlib.Logic.Small.Defs
public import Mathlib.Logic.Small.Set

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

open Form

@[expose] public noncomputable section

/-- The polynomial functor describing Left and Right option sets. -/
def GameFunctor (α : Type (u + 1)) : Type (u + 1) :=
  {s : Player → Set α // ∀ p, Small.{u} (s p)}

namespace GameFunctor

@[ext]
theorem ext {α : Type (u + 1)} {x y : GameFunctor α} : x.1 = y.1 → x = y := Subtype.ext

instance {α : Type (u + 1)} (x : GameFunctor α) (p : Player) : Small.{u} (x.1 p) := x.2 p

instance : Functor GameFunctor where
  map f s := ⟨(f '' s.1 ·), fun _ => by infer_instance⟩

theorem map_def {α β} (f : α → β) (s : GameFunctor α) :
    f <$> s = ⟨(f '' s.1 ·), fun _ => by infer_instance⟩ :=
  rfl

instance : QPF GameFunctor where
  P := ⟨Player → Type u, fun x ↦ Σ p, PLift (x p)⟩
  abs x := ⟨fun p ↦ Set.range (x.2 ∘ .mk p ∘ PLift.up), fun _ ↦ by infer_instance⟩
  repr x := ⟨fun p ↦ Shrink (x.1 p), Sigma.rec (fun _ y ↦ ((equivShrink _).symm y.1).1)⟩
  abs_repr x := by
    cases x with | mk s hs =>
    apply Subtype.ext
    funext p; ext z; constructor
    · rintro ⟨y, rfl⟩; exact ((equivShrink ↑(s p)).symm y).2
    · intro hz
      exact ⟨equivShrink ↑(s p) ⟨z, hz⟩,
        congrArg Subtype.val ((equivShrink ↑(s p)).left_inv ⟨z, hz⟩)⟩
  abs_map f := by intro ⟨x, f⟩; ext; simp [PFunctor.map, map_def]

end GameFunctor

/-- The canonical type of combinatorial game forms. -/
def GameForm : Type (u + 1) :=
  QPF.Fix GameFunctor

namespace GameForm

/--
Construct a `GameForm` from its Left and Right options.
-/
instance : OfSets GameForm fun _ ↦ True where
  ofSets (st : Player → Set GameForm) _ := QPF.Fix.mk ⟨st, fun
    | .left => (inferInstance : Small.{u} (st .left))
    | .right => (inferInstance : Small.{u} (st .right))⟩

/--
The set of options of the game.
-/
private def moves' (p : Player) (x : GameForm.{u}) : Set GameForm.{u} := x.dest.1 p

@[no_expose]
instance : Moves GameForm where
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
The set of Left options of the game.
-/
scoped notation:max x:max "ᴸ" => moves Player.left x

/--
The set of Right options of the game.
-/
scoped notation:max x:max "ᴿ" => moves Player.right x

instance instSmallElemMoves (p : Player) (x : GameForm.{u}) : Small.{u} (moves p x) := x.dest.2 p

private theorem moves_ofSets (p) (st :
    Player → Set GameForm) [Small.{u} (st .left)] [Small.{u} (st .right)] :
    moves p !{st} = st p := by
  dsimp [ofSets]; ext; simp only [moves, moves', QPF.Fix.dest_mk]

@[simp]
theorem ofSets_moves (x : GameForm) : !{fun p => moves p x} = x := x.mk_dest

private theorem leftMoves_ofSets (s t : Set GameForm) [Small.{u} s] [Small.{u} t] : !{s | t}ᴸ = s :=
  moves_ofSets ..

private theorem rightMoves_ofSets (s t : Set GameForm) [Small.{u} s] [Small.{u} t] :
    !{s | t}ᴿ = t :=
  moves_ofSets ..

@[simp]
theorem ofSets_leftMoves_rightMoves (x : GameForm) : !{xᴸ | xᴿ} = x := by
  convert x.ofSets_moves with p
  cases p <;> rfl

/--
Two `GameForm`s are equal when their option sets are.
-/
@[ext]
theorem ext {x y : GameForm.{u}} (h : ∀ p, moves p x = moves p y) :
    x = y := by
  rw [← ofSets_moves x, ← ofSets_moves y]
  simp_rw [funext h]

private theorem ofSets_inj' {st₁ st₂ : Player → Set GameForm}
    [Small (st₁ .left)] [Small (st₁ .right)] [Small (st₂ .left)] [Small (st₂ .right)] :
    !{st₁} = !{st₂} ↔ st₁ = st₂ := by
  simp_rw [GameForm.ext_iff, moves_ofSets, funext_iff]

theorem ofSets_inj {s₁ s₂ t₁ t₂ : Set GameForm} [Small s₁] [Small s₂] [Small t₁] [Small t₂] :
    !{s₁ | t₁} = !{s₂ | t₂} ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp only [ofSets_inj', Player.cases_inj]

instance (x : GameForm.{u}) : Small.{u} {y // IsOption y x} :=
  inferInstanceAs (Small (⋃ p, moves p x))

instance (x : GameForm.{u}) : Small.{u} {y // Subposition y x} :=
  small_transGen' _ x

-- We make no use of `GameForm`'s definition from a `QPF` after this point.
attribute [irreducible] GameForm

/--
**Conway induction**: build data for a game by recursively building it on its
Left and Right sets. This rarely needs to be used explicitly, as the
termination checker will handle it.

See `ofSetsRecOn` for an alternate form.
-/
@[elab_as_elim]
def moveRecOn {motive : GameForm → Sort*} (x)
    (mk : Π x, (Π p, Π y ∈ moves p x, motive y) → motive x) : motive x :=
  mk x (fun p y _ ↦ moveRecOn y mk)
termination_by x
decreasing_by form_wf

theorem moveRecOn_eq {motive : GameForm → Sort*} (x)
    (mk : Π x, (Π p, Π y ∈ moves p x, motive y) → motive x) :
    moveRecOn x mk = mk x (fun _ y _ ↦ moveRecOn y mk) := by
  rw [moveRecOn]

/--
**Conway induction**: build data for a game by recursively building it on its
Left and Right sets. This rarely needs to be used explicitly, as the
termination checker will handle it.

See `moveRecOn` for an alternate form.
-/
@[elab_as_elim]
def ofSetsRecOn {motive : GameForm.{u} → Sort*} (x)
    (mk : Π (s t : Set GameForm) [Small s] [Small t],
      (Π x ∈ s, motive x) → (Π x ∈ t, motive x) → motive !{s | t}) :
    motive x :=
  cast (by simp) <| moveRecOn (motive := fun x ↦ motive !{xᴸ | xᴿ}) x
    fun x IH ↦ mk _ _
      (fun y hy ↦ cast (by simp) (IH .left y hy)) (fun y hy ↦ cast (by simp) (IH .right y hy))

@[simp]
theorem ofSetsRecOn_ofSets {motive : GameForm.{u} → Sort*}
    (s t : Set GameForm) [Small.{u} s] [Small.{u} t]
    (mk : Π (s t : Set GameForm) [Small s] [Small t],
      (Π x ∈ s, motive x) → (Π x ∈ t, motive x) → motive !{s | t}) :
    ofSetsRecOn !{s | t} mk = mk _ _ (fun y _ ↦ ofSetsRecOn y mk) (fun y _ ↦ ofSetsRecOn y mk) := by
  rw [ofSetsRecOn, cast_eq_iff_heq, moveRecOn_eq]
  congr
  any_goals simp only [moves_ofSets, Player.cases, heq_eq_eq]
  all_goals
    refine Function.hfunext rfl fun x _ h ↦ ?_
    cases h
    refine Function.hfunext ?_ fun _ _ _ ↦ ?_
    · simp [moves_ofSets]
    · rw [ofSetsRecOn, cast_heq_iff_heq, heq_cast_iff_heq]

private def neg' (x : GameForm) : GameForm :=
  !{Set.range fun y : xᴿ ↦ neg' y.1 | Set.range fun y : xᴸ ↦ neg' y.1}
termination_by x
decreasing_by form_wf

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
The *conjugate* of a game is defined by `-!{s | t} = !{-t | -s}`. In the
literature, one would see
$$
  \overline{G}=\form<\overline{G^\mathcal{R}}>[\overline{G^\mathcal{L}}].
$$
In this repository, the conjugate is often referred to as the 'negative', even
though it is *not* necessarily an additive inverse.
-/
@[no_expose]
instance : Neg GameForm where
  neg := neg'

private theorem neg_ofSets'' (s t : Set GameForm) [Small s] [Small t] :
    -!{s | t} = !{Neg.neg '' t | Neg.neg '' s} := by
  change neg' _ = _
  rw [neg']
  simp [Neg.neg, Set.ext_iff, moves_ofSets, ofSets_inj']

instance : InvolutiveNeg GameForm where
  neg_neg x := by
    refine ofSetsRecOn x ?_
    aesop (add simp [neg_ofSets'', ofSets_inj'])

private theorem neg_ofSets (s t : Set GameForm) [Small s] [Small t] : -!{s | t} = !{-t | -s} := by
  simp_rw [neg_ofSets'', Set.image_neg_eq_neg]

theorem neg_ofSets' (st : Player → Set GameForm) [Small (st .left)] [Small (st .right)] :
    -!{st} = !{fun p ↦ -st (-p)} := by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases fun _ ↦ -_, neg_ofSets]
  rfl

private theorem neg_ofSets_const (s : Set GameForm) [Small s] :
    -!{fun _ ↦ s} = !{fun _ ↦ -s} := by
  simp only [neg_ofSets']

theorem neg_eq (x : GameForm) : -x = !{-xᴿ | -xᴸ} := by
  rw [← neg_ofSets, ofSets_leftMoves_rightMoves]

theorem neg_eq' (x : GameForm) : -x = !{fun p ↦ -moves (-p) x} := by
  rw [neg_eq, ofSets_eq_ofSets_cases (fun _ ↦ -_)]; rfl

private theorem moves_neg' (p : Player) (x : GameForm) :
    moves p (-x) = -moves (-p) x := by
  rw [neg_eq', moves_ofSets]

/-!
### Addition and subtraction
-/

-- The recursive `add'` definition builds both players' option sets and needs
-- extra heartbeats for the termination proof after unfolding `ofSets`.
private def add' (x y : GameForm) : GameForm :=
  !{(Set.range fun z : moves .left x ↦ add' z y) ∪ (Set.range fun z : moves .left y ↦ add' x z) |
    (Set.range fun z : moves .right x ↦ add' z y) ∪ (Set.range fun z : moves .right y ↦ add' x z)}
termination_by (x, y)
decreasing_by form_wf

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
The sum of `x = !{s₁ | t₁}` and `y = !{s₂ | t₂}` is `!{s₁ + y, x + s₂ | t₁ + y,
x + t₂}`. In the literature, one would see
$$
  G+H=\form<G^\mathcal{L}+H,G+H^\mathcal{L}>[G^\mathcal{R}+H,G+H^\mathcal{R}].
$$
-/
@[no_expose]
instance : Add GameForm where
  add := add'

theorem add_eq (x y : GameForm) : x + y =
    !{(· + y) '' xᴸ ∪ (x + ·) '' yᴸ | (· + y) '' xᴿ ∪ (x + ·) '' yᴿ} := by
  change add' _ _ = _
  rw [add']
  simp [HAdd.hAdd, Add.add, Set.ext_iff, ofSets_inj']

theorem add_eq' (x y : GameForm) : x + y =
    !{fun p ↦ (· + y) '' moves p x ∪ (x + ·) '' moves p y} := by
  rw [add_eq, ofSets_eq_ofSets_cases (fun _ ↦ _ ∪ _)]

theorem ofSets_add_ofSets
    (s₁ t₁ s₂ t₂ : Set GameForm) [Small s₁] [Small t₁] [Small s₂] [Small t₂] :
    !{s₁ | t₁} + !{s₂ | t₂} =
      !{(· + !{s₂ | t₂}) '' s₁ ∪ (!{s₁ | t₁} + ·) '' s₂ |
        (· + !{s₂ | t₂}) '' t₁ ∪ (!{s₁ | t₁} + ·) '' t₂} := by
  rw [add_eq]
  simp only [moves_ofSets, Player.cases]

theorem ofSets_add_ofSets' (st₁ st₂ : Player → Set GameForm)
    [Small (st₁ .left)] [Small (st₂ .left)] [Small (st₁ .right)] [Small (st₂ .right)] :
    !{st₁} + !{st₂} =
      !{fun p ↦ (· + !{st₂}) '' st₁ p ∪ (!{st₁} + ·) '' st₂ p} := by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases st₂, ofSets_eq_ofSets_cases (fun _ ↦ _ ∪ _),
    ofSets_add_ofSets]

private theorem moves_add' (p : Player) (x y : GameForm) :
    moves p (x + y) = (· + y) '' moves p x ∪ (x + ·) '' moves p y := by
  rw [add_eq', moves_ofSets]

theorem isOption_neg {x y : GameForm} : IsOption x (-y) ↔ IsOption (-x) y := by
  simp only [moves_neg', IsOption.iff_mem_union, Player.neg_left, Player.neg_right,
             Set.union_comm, Set.mem_union, Set.mem_neg]

@[simp]
theorem isOption_neg_neg {x y : GameForm} : IsOption (-x) (-y) ↔ IsOption x y := by
  rw [isOption_neg, neg_neg]

theorem forall_moves_neg {P : GameForm → Prop} {p : Player} {x : GameForm} :
    (∀ y ∈ moves p (-x), P y) ↔ (∀ y ∈ moves (-p) x, P (-y)) := by
  simp only [moves_neg', Set.mem_neg, Set.forall_neg_mem]

theorem IsOption.add_left {x y z : GameForm} (h : IsOption x y) : IsOption (z + x) (z + y) := by
  aesop (add simp [moves_add'])

theorem IsOption.add_right {x y z : GameForm} (h : IsOption x y) : IsOption (x + z) (y + z) := by
  aesop (add simp [moves_add'])

private theorem add_comm' (x y : GameForm) : x + y = y + x := by
  ext
  simp only [moves_add', Set.mem_union, Set.mem_image, or_comm]
  congr! 3 <;>
  · refine and_congr_right_iff.2 fun h ↦ ?_
    rw [add_comm']
termination_by (x, y)
decreasing_by form_wf

private theorem add_assoc' (x y z : GameForm) : x + y + z = x + (y + z) := by
  ext1
  simp only [moves_add', Set.image_union, Set.image_image, Set.union_assoc]
  refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_) <;>
  · ext
    congr! 2
    rw [add_assoc']
termination_by (x, y, z)
decreasing_by form_wf

private theorem neg_add' (x y : GameForm) : -(x + y) = -x + -y := by
  ext
  simp only [moves_neg', moves_add', Set.union_neg, Set.mem_union, Set.mem_neg, Set.mem_image,
             Set.exists_neg_mem]
  congr! 3 <;>
  · refine and_congr_right_iff.2 fun _ ↦ ?_
    rw [← neg_inj, neg_add', neg_neg]
termination_by (x, y)
decreasing_by form_wf

instance : AddCommSemigroup GameForm where
  add_assoc := private add_assoc'
  add_comm := private add_comm'

instance : Form GameForm where
  moves_neg' := private moves_neg'
  moves_add' := private moves_add'
  moves_small' := instSmallElemMoves
  IsEndLike p x := moves p x = ∅
  isEndLike_ofEnd' _ _ h1 := h1
  isEndLike_add_iff' p x y := by simp [moves_add']
  isEndLike_neg_iff_neg' p g := by
    constructor <;> cases p
    all_goals
    · intro h1
      simp only [moves_neg', Player.neg_left, Player.neg_right, Set.neg_eq_empty] at h1 ⊢
      exact h1
  moves_ofSets' := private moves_ofSets
  add_zero' x := by
    refine moveRecOn x ?_
    intro y h1
    simp only [Player.forall] at h1
    ext p z
    have moves_zero' : moves p (!{fun x ↦ ∅} : GameForm) = ∅ := by cases p <;> simp [moves_ofSets]
    rw [moves_add', moves_zero', Set.image_empty, Set.union_empty, Set.mem_image]
    cases p
    all_goals
    · apply Iff.intro
      · intro ⟨w, left, right⟩
        subst right
        simp_all only
      · intro a
        use z, a
        simp_all only
  add_eq_zero_iff' x y := by
    constructor <;> simp_all [GameForm.ext_iff, moves_add', moves_ofSets]
  ofSets_inj'' := private ofSets_inj'
  neg_ofSets'' := private neg_ofSets
  neg_add' := private neg_add'
  smallElemMoves' := instSmallElemMoves
  ofSets_isEndLike_iff' p s t _ _ := Eq.congr_right rfl
  ofSets_add_ofSets'' := ofSets_add_ofSets
  ofSets_moves_of_not_isEndLike' := @fun g _ _ _ => ofSets_moves g

@[simp]
theorem isEndLike_iff_isEnd {g : GameForm} {p : Player} : IsEndLike p g ↔ IsEnd p g := by
  simp only [IsEndLike, isEnd_def]

theorem leftEnd_rightEnd_eq_zero {g : GameForm} (h1 : IsEnd .left g) (h2 : IsEnd .right g) :
    g = 0 := by
  rw [isEnd_def] at h1 h2
  rw [zero_def]
  ext p
  cases p
  · simp only [moves_ofSets, Set.mem_empty_iff_false, iff_false] at ⊢ h1
    simp only [h1, Set.mem_empty_iff_false, not_false_eq_true]
  · simp only [moves_ofSets] at ⊢ h2
    rw [h2]

theorem both_ends_eq_zero {g : GameForm} {p : Player} (h1 : IsEnd p g) (h2 : IsEnd (-p) g) :
    g = 0 := by
  cases p
  · exact leftEnd_rightEnd_eq_zero h1 h2
  · exact leftEnd_rightEnd_eq_zero h2 h1

theorem ne_zero_not_end {g : GameForm} (h1 : g ≠ 0) : ∃ p, ¬IsEnd p g := by
  apply not_forall.mp
  intro h2
  exact h1 (leftEnd_rightEnd_eq_zero (h2 .left) (h2 .right))

@[simp]
theorem zero_not_both_end {g : GameForm} {p : Player} (h1 : g ≠ 0) (h2 : IsEnd p g) :
    ¬IsEnd (-p) g :=
  fun h3 => h1 (both_ends_eq_zero h2 h3)

theorem isOption_zero_add_iff {g h : GameForm} :
    IsOption 0 (g + h) ↔ (IsOption 0 g ∧ h = 0) ∨ (IsOption 0 h ∧ g = 0) := by
  constructor
  · intro h1
    simp only [isOption_iff_mem_union, moves_add, Set.mem_union,
               Set.mem_image, add_eq_zero_iff, ↓existsAndEq, true_and, exists_eq_right_right] at h1
    simp only [isOption_iff_mem_union, Set.mem_union]
    apply Or.elim3 h1
    · intro h2
      apply Or.elim h2
      · intro ⟨gl, h0⟩
        exact Or.inl ⟨Or.inl gl, h0⟩
      · intro ⟨hl, g0⟩
        exact Or.inr ⟨Or.inl hl, g0⟩
    · intro ⟨gr, h0⟩
      exact Or.inl ⟨Or.inr gr, h0⟩
    · intro ⟨hr, g0⟩
      exact Or.inr ⟨Or.inr hr, g0⟩
  · rintro (⟨h_isOption_zero_g, h_h_zero⟩ | ⟨h_isOption_zero_h, h_g_zero⟩)
    · rwa [h_h_zero, add_zero]
    · rwa [h_g_zero, zero_add]

end GameForm

end

end MisereGames
