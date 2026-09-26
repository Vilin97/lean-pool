/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Logic.Relation
public import Mathlib.Order.CompleteLattice.Basic

public import LeanPool.PDL.Syntax
public import LeanPool.PDL.General.ListFinset

/-! # Semantics (Section 2.2) -/

public section

namespace PDL

/-! ## Models and Truth -/

/-- Kripke Models, also known as Labelled Transition Systems -/
structure KripkeModel (W : Type) : Type where
  /-- The truth assignment for atomic propositions at each world. -/
  val : W → Nat → Prop
  /-- The accessibility relation for each atomic program. -/
  Rel : Nat → W → W → Prop

/-- The syntactic measure used to define formula evaluation and program relations mutually. -/
@[simp]
def complexityOfQuery {W : Type} :
    PSum (Σ' (_ : KripkeModel W) (_ : W), Formula)
         (Σ' (_ : KripkeModel W) (_ : Program) (_ : W), W) → ℕ
  | PSum.inl val => lengthOfFormula val.snd.snd
  | PSum.inr val => lengthOfProgram val.snd.fst

mutual
  /-- Truth of a PDL formula at a world in a Kripke model. -/
  @[expose, simp] def evaluate {W : Type} : KripkeModel W → W → Formula → Prop
    | _, _, ⊥ => False
    | M, w, ·c => M.val w c
    | M, w, ~φ => Not (evaluate M w φ)
    | M, w, φ⋀ψ => evaluate M w φ ∧ evaluate M w ψ
    | M, w, ⌈α⌉ φ => ∀ v : W, relate M α w v → evaluate M v φ
  /-- The binary relation denoted by a PDL program in a Kripke model. -/
  @[expose, simp] def relate {W : Type} : KripkeModel W → Program → W → W → Prop
    | M, ·c, w, v => M.Rel c w v
    | M, α;'β, w, v => ∃ y, relate M α w y ∧ relate M β y v
    | M, α⋓β, w, v => relate M α w v ∨ relate M β w v
    | M, ∗α, w, v => Relation.ReflTransGen (relate M α) w v
    | M, ?'φ, w, v => w = v ∧ evaluate M w φ
end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.
end PDL

namespace PDL

theorem evalDis {W M f g} {w : W} : evaluate M w (f⋁g) ↔ evaluate M w f ∨ evaluate M w g :=
  by
  simp
  tauto

/-- Evaluate a formula at a pointed Kripke model. -/
@[expose, simp] def evaluatePoint {W : Type} : KripkeModel W × W → Formula → Prop
  | (M, w), ϕ => evaluate M w ϕ

/-- Validity of a formula at every world of every Kripke model. -/
def tautology (φ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, evaluate M w φ

/-- Falsity of a formula at every world of every Kripke model. -/
def contradiction (φ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, ¬evaluate M w φ

/-! ## Satisfiability -/

-- MB: Definition 5, page 9
/-- Types equipped with a notion of semantic satisfiability. -/
class HasSat (α : Type) where
  /-- Existence of a semantic model for an object. -/
  satisfiable : α → Prop
open HasSat
@[simp]
instance formHasSat : HasSat Formula :=
  HasSat.mk fun ϕ => ∃ (W : _) (M : KripkeModel W) (w : _), evaluate M w ϕ
@[simp]
instance setHasSat : HasSat (Finset Formula) :=
  HasSat.mk fun X => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ ∈ X, evaluate M w φ
@[simp]
instance listHasSat : HasSat (List Formula) :=
  HasSat.mk fun X => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ ∈ X, evaluate M w φ

/-- Satisfiability of a list only depends on which formulas are in it. -/
lemma sat_congr_of_mem_iff {L L' : List Formula} (h : ∀ f, f ∈ L ↔ f ∈ L') :
    satisfiable L ↔ satisfiable L' := by
  constructor <;> rintro ⟨W, M, w, hw⟩ <;> exact ⟨W, M, w, fun f hf => hw f (by simp_all)⟩

/-! ## Semantic implication and vDash notation -/

/-- Semantic consequence between finite sets of formulas. -/
def semImpliesSets (X : Finset Formula) (Y : Finset Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w),
    (∀ φ ∈ X, evaluate M w φ) → ∀ ψ ∈ Y, evaluate M w ψ

/-- Semantic consequence between lists of formulas. -/
@[expose] def semImpliesLists (X : List Formula) (Y : List Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w),
    (∀ φ ∈ X, evaluate M w φ) → ∀ ψ ∈ Y, evaluate M w ψ

/-- Agreement of two formulas at every pointed Kripke model. -/
@[expose] def semEquiv (φ ψ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, evaluate M w φ ↔ evaluate M w ψ

/-- Agreement of two program relations in every Kripke model. -/
def relEquiv (α β : Program) :=
  ∀ (W : Type) (M : KripkeModel W) v w, relate M α v w ↔ relate M β v w

theorem notsatisfnotThenTaut : ∀ φ, ¬ satisfiable (~φ) → tautology φ :=
  by
  intro phi
  unfold satisfiable
  unfold tautology
  simp

theorem subsetSat {M : KripkeModel W} {w : W} {X Y : List Formula} :
    (∀ φ ∈ X, evaluate M w φ) → Y ⊆ X → ∀ φ ∈ Y, evaluate M w φ :=
  by aesop

theorem semEquiv.refl : Std.Refl semEquiv := by
  constructor
  tauto

theorem semEquiv.symm : Std.Symm semEquiv := by
  constructor
  intro φ1 φ2 hyp W M w
  specialize hyp W M w
  tauto

theorem semEquiv.trans : IsTrans Formula semEquiv := by
  constructor
  intro _ _ _ hyp1 hyp2 W M w
  specialize hyp1 W M w
  specialize hyp2 W M w
  tauto

theorem relEquiv.refl : Std.Refl relEquiv := by
  constructor
  tauto

theorem relEquiv.symm : Std.Symm relEquiv := by
  constructor
  intro α1 α2 hyp W M w v
  specialize hyp W M w v
  tauto

theorem relEquiv.trans : IsTrans Program relEquiv := by
  constructor
  intro _ _ _ hyp1 hyp2 W M w v
  specialize hyp1 W M w v
  specialize hyp2 W M w v
  tauto

/-- An overloaded semantic satisfaction or consequence relation. -/
class vDash (α : Type) (β : Type) where
  /-- The semantic relation for the two specified types. -/
  SemImplies : α → β → Prop

open vDash

instance modelCanSemImplyForm {W : Type} : vDash (KripkeModel W × W) Formula :=
  vDash.mk (@evaluatePoint W)
@[simp]
instance modelCanSemImplyList {W : Type} : vDash (KripkeModel W × W) (List Formula) :=
  vDash.mk (fun ⟨M,w⟩ fs => ∀ f ∈ fs, @evaluate W M w f)
instance modelCanSemImplyAnyFormula {W : Type} : vDash (KripkeModel W × W) AnyFormula :=
  ⟨fun (M,w) ξ => match ξ with
    | (AnyFormula.normal φ) => evaluate M w φ
    | .loaded χ => evaluate M w χ.unload⟩
instance modelCanSemImplyAnyNegFormula {W : Type} : vDash (KripkeModel W × W) AnyNegFormula :=
  vDash.mk (fun ⟨M,w⟩ ⟨ξ⟩ => ¬ SemImplies (M, w) ξ)
instance setCanSemImplySet : vDash (List Formula) (List Formula) := vDash.mk semImpliesLists
instance setCanSemImplyForm : vDash (List Formula) Formula :=
  vDash.mk fun X ψ => semImpliesLists X [ψ]
instance formCanSemImplySet : vDash Formula (List Formula) :=
  vDash.mk fun φ X => semImpliesLists [φ] X
instance formCanSemImplyForm : vDash Formula Formula :=
  vDash.mk fun φ ψ => semImpliesLists [φ] [ψ]

/-- Semantic satisfaction or consequence. -/
scoped infixl:40 " ⊨ " => SemImplies

/-- Semantic equivalence of formulas. -/
scoped infixl:40 " ≡ " => semEquiv

/-- Semantic equivalence of program relations. -/
scoped infixl:40 " ≡ᵣ " => relEquiv

/-- Failure of semantic satisfaction or consequence. -/
scoped infixl:40 " ⊭ " => fun a b => ¬a⊨b

@[simp]
theorem singletonSat_iff_sat : ∀ φ, satisfiable ({φ} : Finset Formula) ↔ satisfiable φ :=
  by
  intro phi
  simp [satisfiable]

@[simp]
theorem vDashSingleton_iff_vDash_formula {M : KripkeModel W} {w : W} :
    ∀ φ, (M, w) ⊨ ([φ] : List Formula) ↔ evaluate M w φ :=
  by
  intro phi
  simp [SemImplies]

-- useful lemmas to connect different ⊨ cases
theorem forms_to_lists {φ ψ : Formula} : φ⊨ψ → ([φ] : List Formula)⊨([ψ] : List Formula) :=
  by
  intro impTaut W M w lhs ψ psi_in_psi
  specialize impTaut W M w
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at psi_in_psi lhs
  rw [psi_in_psi]
  -- needed even though no ψ_1 in goal here?!
  apply impTaut
  · rw [←vDashSingleton_iff_vDash_formula φ] at lhs
    tauto
  · aesop

/-- The Local Deduction Theorem. -/
theorem deduction (X : List Formula) (ψ φ : Formula) :
    X ++ [ψ] ⊨ φ ↔ (X ⊨ ψ ↣ φ) := by
  constructor
  · intro Xφ_then_ψ W M w w_X
    aesop
  · intro X_ W M w w_X
    specialize X_ W M w
    aesop

theorem notSat_iff_semImplies (X : List Formula) (φ : Formula) :
    ¬ satisfiable (X ∪ [~φ]) ↔ X ⊨ ([φ] : List Formula) := by
  constructor
  · simp only [satisfiable, not_exists, not_forall, exists_prop]
    intro nSat W M w satX
    specialize nSat W M w
    rcases nSat with ⟨φ, phi_in, not_phi⟩
    aesop
  · intro X_φ
    by_contra hyp
    simp only [satisfiable] at hyp
    rcases hyp with ⟨W, M, w, w_⟩
    specialize X_φ W M w
    cases X
    · simp_all
    · have := w_ (~φ)
      simp at *
      simp_all

theorem equivSat (φ ψ : Formula) {M : KripkeModel W} {w : W} :
    φ ≡ ψ → (M, w) ⊨ φ → (M, w) ⊨ ψ :=
  by
    intro φ_eq_ψ evalφ
    have : evaluate M w φ := by tauto
    rw [φ_eq_ψ] at this
    tauto

theorem equiv_iff (φ ψ : Formula) (φ_eq_ψ : φ ≡ ψ) :
    ∀ {W} {M : KripkeModel W} {w : W},
    (M, w) ⊨ φ ↔ (M, w) ⊨ ψ :=
  by
    intro W M w
    constructor
    · intro
      have : evaluate M w φ := by tauto
      rw [φ_eq_ψ] at this
      tauto
    · intro
      have : evaluate M w ψ := by tauto
      rw [← φ_eq_ψ] at this
      tauto

theorem tautImp_iff_comboNotUnsat {φ ψ : Formula} :
    tautology (φ ↣ ψ) ↔ ¬ satisfiable ([φ, ~ψ]) :=
  by
  simp [tautology, satisfiable, evaluate]

theorem relate_steps_append {as bs} : ∀ x z, relate M (Program.steps (as ++ bs)) x z  ↔
  ∃ y, relate M (Program.steps as) x y ∧ relate M (Program.steps bs) y z :=
  by
  induction as
  · simp
  case cons a as IH =>
    intro x z
    constructor
    · intro lhs
      simp only [List.cons_append, Program.steps.eq_2, relate, Program.steps] at *
      rcases lhs with ⟨y, x_a_y, y_asbs_z⟩
      rw [IH] at y_asbs_z
      rcases y_asbs_z with ⟨y', y_as_ys', ys'_bs_z⟩
      use y'
      constructor
      · use y
      · exact ys'_bs_z
    · intro rhs
      simp only [Program.steps, relate, List.cons_append] at *
      rcases rhs with ⟨y, ⟨y', x_a_y', y'_as_y⟩, bla⟩
      use y'
      rw [IH y' z]
      tauto

theorem rel_steps_last {as} : ∀ v w,
  relate M (Program.steps (as ++ [a])) v w ↔
    ∃ mid, relate M (Program.steps as) v mid ∧ relate M a mid w :=
  by
  induction as
  case nil =>
    simp at *
  case cons a2 as IH =>
    intro s t
    simp only [List.cons_append, Program.steps.eq_2, relate, Program.steps] at *
    constructor
    · intro lhs
      rcases lhs with ⟨next, s_a2_next, next_asa_t⟩
      rw [IH] at next_asa_t
      tauto
    · intro rhs
      rcases rhs with ⟨m,⟨y,yP,yP2⟩,mP⟩
      use y
      rw [IH]
      tauto

/-- Relational composition of a list of programs, with equality for the empty list. -/
@[expose] def relateSeq {W} (M : KripkeModel W) (δ : List Program) (w v : W) : Prop :=
  match δ with
  | [] => w = v
  | (α::as) => ∃ u, relate M α w u ∧ relateSeq M as u v

@[simp]
theorem relateSeq_nil {M : KripkeModel W} {w v : W} :
    relateSeq M [] w v ↔ w = v := by
  simp [relateSeq]

@[simp]
theorem relateSeq_singleton {M : KripkeModel W} {α : Program} {w v : W} :
    relateSeq M [α] w v ↔ relate M α w v := by
  simp [relateSeq]

theorem relateSeq_cons {M : KripkeModel W} {d : Program} {δ : List Program} {w v : W} :
    relateSeq M (d :: δ) w v ↔ ∃ u, relate M d w u ∧ relateSeq M δ u v := iff_of_eq rfl

theorem relateSeq_append {M : KripkeModel W} {l1 l2 : List Program} {w v : W} :
    relateSeq M (l1 ++ l2) w v ↔ ∃ u, relateSeq M l1 w u ∧ relateSeq M l2 u v := by
  induction l1 generalizing w v
  · simp [relateSeq]
  case cons l l1 IH =>
    simp [relateSeq]
    aesop

lemma relate_steps_iff_relateSeq (M : KripkeModel W) (δ : List Program) (w v : W) :
    relate M (Program.steps δ) w v ↔ relateSeq M δ w v := by
  induction δ generalizing w v <;> simp_all [relateSeq]

theorem relateSeq_iff_exists_Vector (M : KripkeModel W) (δ : List Program) (w v : W) :
  relateSeq M δ w v ↔
   ∃ (ws : List.Vector W (δ.length).succ),
      w = ws.head ∧ v = ws.last ∧ ∀ i, relate M (δ.get i) (ws.get i.castSucc) (ws.get i.succ)
    := by
  induction δ generalizing w
  · simp only [relateSeq_nil, List.length_nil, Nat.succ_eq_add_one, Nat.reduceAdd,
    List.get_eq_getElem, IsEmpty.forall_iff, and_true]
    constructor <;> intro h
    · use ⟨[w], by simp⟩
      aesop
    · rcases h with ⟨⟨ws, ws_len_eq_1⟩ , w_def, v_def⟩
      rw [List.length_eq_one_iff] at ws_len_eq_1
      rcases ws_len_eq_1 with ⟨x, ws_def⟩
      aesop
  case cons d δ IH =>
    simp only [relateSeq_cons, List.length_cons, Nat.succ_eq_add_one, List.get_eq_getElem]
    constructor <;> intro h
    · rcases h with ⟨u, w_u, u_v⟩
      rw [IH] at u_v
      clear IH
      rcases u_v with ⟨ws, u_def, v_def, claim⟩
      refine ⟨w ::ᵥ ws, ?_, ?_, ?_⟩
      · simp
      · rw [v_def]
        have := @List.Vector.tail_last_eq_last _ _ (w ::ᵥ ws)
        grind
      · apply Fin.cases
        · simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
            Fin.castSucc_zero, Fin.succ_zero_eq_one]
          convert w_u
          · subst u_def
            simp [List.Vector.get]
          · rcases ws with ⟨ws, ws_len⟩
            have := List.exists_of_length_succ _ ws_len
            aesop
        · aesop
    · rcases h with ⟨wws, w_def, v_def, claim⟩
      let u := wws[1]
      use wws[1]
      constructor
      · have := claim 0
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero, Fin.castSucc_zero,
          List.Vector.get_zero, Fin.succ_zero_eq_one] at this
        convert this
        rfl
      · specialize IH u
        rw [IH]
        clear IH
        refine ⟨wws.tail, ?_ , ?_ , ?_ ⟩
        · unfold u
          rcases wws with ⟨wws, wws_len⟩
          rcases List.exists_of_length_succ _ wws_len with ⟨x, t, wws_def⟩
          subst wws_def
          have := List.exists_of_length_succ t
            (by simp at wws_len; assumption : t.length = δ.length + 1)
          rcases this with ⟨y, tt, t_def⟩
          subst t_def
          aesop
        · rw [v_def]
          -- copied from previous case
          rcases wws with ⟨wws, wws_len⟩
          rcases List.exists_of_length_succ _ wws_len with ⟨x, t, wws_def⟩
          subst wws_def
          have := List.exists_of_length_succ t
            (by simp at wws_len; assumption : t.length = δ.length + 1)
          rcases this with ⟨y, tt, t_def⟩
          subst t_def
          aesop
        · intro i
          specialize claim i.succ
          aesop

/-- Relating along `Program.unions L` means relating along one of the programs in `L`. -/
lemma relate_unions {W} {M : KripkeModel W} : ∀ (L : List Program) (v u : W),
    relate M (Program.unions L) v u ↔ ∃ a ∈ L, relate M a v u
  | [], v, u => by simp [Program.unions, relate, evaluate]
  | [a], v, u => by simp [Program.unions]
  | a :: b :: L, v, u => by
      simp only [Program.unions, relate, relate_unions (b :: L) v u, List.mem_cons]
      constructor
      · rintro (h | ⟨c, hc, h⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨c, Or.inr hc, h⟩
      · rintro ⟨c, rfl | hc, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, hc, h⟩

theorem evalBoxes (δ : List Program) φ :
    evaluate M w (⌈⌈δ⌉⌉φ) ↔ (∀ v, relateSeq M δ w v → evaluate M v φ) := by
  induction δ generalizing w
  · simp [relateSeq]
  case cons α δ IH =>
    simp only [Formula.boxes_cons]
    constructor
    · intro lhs v v_αδ_w
      simp only [evaluate, relateSeq] at *
      rcases v_αδ_w with ⟨u, w_α_u, u_δ_v⟩
      specialize @IH u
      refine IH.1 ?_ v u_δ_v
      simp_all only [true_iff]
    · intro rhs u w_α_u
      apply IH.2
      intro v u_δ_v
      apply rhs
      simp only [relateSeq]
      use u

@[simp]
theorem evaluate_unload_box {af} :
    evaluate M w (⌊α⌋af).unload ↔ ∀ v, relate M α w v → (M,v) ⊨ af := by
  cases af <;> simp_all [SemImplies]

theorem truthImply_then_satImply (X Y : List Formula) : X ⊨ Y → satisfiable X → satisfiable Y :=
  by
  intro X_Y satX
  rcases satX with ⟨W,M,w,v_X⟩
  specialize X_Y W M w v_X
  use W, M, w

/-- Semantic induction rule for the Kleene star operator. -/
theorem stepToStar : φ ⊨ (⌈α⌉φ) ⋀ ψ  →  φ ⊨ (⌈∗α⌉ψ) := by
  intro hyp W M w w_φ
  specialize hyp W M
  have : ∀ v, relate M (∗α) w v → evaluate M v φ := by
    intro v w_sta_v
    simp_all only [List.mem_singleton, forall_eq, evaluate, relate]
    induction w_sta_v
    case refl =>
      simp_all
    case tail s t _ s_α_t s_φ =>
      exact (hyp s s_φ).1 t s_α_t
  simp_all

theorem SemImplyAnyNegFormula_loadBoxes_iff {M : KripkeModel W} {ξ : AnyFormula} :
    (M, w) ⊨ ~''(ξ.loadBoxes δ) ↔ ∃ v, relateSeq M δ w v ∧ (M, v) ⊨ ~''ξ := by
  induction δ generalizing w
  · simp
  case cons d δ IH =>
    unfold modelCanSemImplyAnyNegFormula at IH
    simp only at IH
    unfold SemImplies modelCanSemImplyAnyNegFormula modelCanSemImplyAnyFormula
    simp only [AnyFormula.loadBoxes_cons, evaluate_unload_box, not_forall]
    constructor
    · rintro ⟨u, w_u, u_⟩
      rw [IH] at u_
      rcases u_ with ⟨z, u_z, z_⟩
      use z
      simp only [relateSeq_cons]
      constructor
      · use u
      · exact z_
    · rintro ⟨v, w_v, v_⟩
      simp only [relateSeq_cons] at w_v
      rcases w_v with ⟨u, w_u, u_v⟩
      refine ⟨u, w_u, ?_⟩
      rw [IH]
      use v
      tauto

end PDL
