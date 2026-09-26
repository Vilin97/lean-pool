/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.DepRewrite

public import LeanPool.PDL.Tableau

/-! # Navigating through tableaux with PathIn

To define relations between nodes in a tableau we need to represent the whole
tableau and point to a specific node inside it. This is the `PathIn` type.
Its values say "go to this child, then to this child, ... stop here."
-/

public section

namespace PDL

/-- A path in a tableau. Three constructors for the empty path, a local step or a pdl step.
The `loc` and `pdl` steps correspond to two out of three constructors of `Tableau`.
A `PathIn` only goes downwards, it cannot use `LoadedPathRepeat`s. -/
inductive PathIn : ∀ {Hist X}, Tableau Hist X → Type
| nil : PathIn _
| loc {nrep nbas lt next Y} (Y_in : Y ∈ endNodesOf lt) (tail : PathIn (next Y Y_in))
    : PathIn (Tableau.loc nrep nbas lt next)
| pdl {nrep bas} {r : PdlRule X Y} {next} (tail : PathIn next)
    : PathIn (Tableau.pdl nrep bas r next)
deriving DecidableEq

/-- The tableau reached by a path, together with its history and root sequent. -/
@[implicit_reducible]
@[expose] def tabAt {Hist X} {tab : Tableau Hist X} : PathIn tab → Σ H X, Tableau H X
| .nil => ⟨_,_,tab⟩
| .loc _ tail => tabAt tail
| .pdl tail => tabAt tail

/-- Transporting a path along an equation about `tabAt` does not change `tabAt`.
Compare `PathIn.tabAt_cast` which is about an equation between two tableaux. -/
lemma tabAt_cast_gen {Hist X} {tab : Tableau Hist X} (s : PathIn tab) (w : Σ H X, Tableau H X)
    (h : tabAt s = w) (q : PathIn w.2.2) : tabAt (h ▸ q) = tabAt q := by
  cases h; rfl

/-- Append a path in the reached tableau to an initial path. -/
def PathIn.append {Hist X} {tab : Tableau Hist X} (p : PathIn tab) (q : PathIn (tabAt p).2.2) :
  PathIn tab := match p with
  | .nil => q
  | .loc Y_in tail => .loc Y_in (PathIn.append tail q)
  | .pdl tail => .pdl (PathIn.append tail q)

/-- Whether the tableau reached by a path is a loaded-path-repeat leaf. -/
@[expose]
def PathIn.isLrep {Hist X} {tab : Tableau Hist X} (p : PathIn tab) : Prop := (tabAt p).2.2.isLrep

instance instDecdidablePathInisLrep {Hist X} {tab : Tableau Hist X} (p : PathIn tab) : Decidable
  p.isLrep := by
  rcases h : tabAt p with ⟨H, X, _|_|_⟩
  all_goals
    simp_all only [PathIn.isLrep]; rw [h]; simp only [Tableau.isLrep]
  · apply isFalse; simp
  · apply isFalse; simp
  · apply isTrue; simp

@[simp]
theorem append_eq_iff_eq {Hist X} {tab : Tableau Hist X} (s : PathIn tab) p q : s.append p =
  s.append q ↔ p = q := by
  induction s
  case nil => exact Iff.rfl
  case loc IH => simp only [PathIn.append, PathIn.loc.injEq, heq_eq_eq, true_and]; exact IH _ _
  case pdl IH => simp only [PathIn.append, PathIn.pdl.injEq]; exact IH _ _

@[simp]
theorem PathIn.eq_append_iff_other_eq_nil {Hist X} {tab : Tableau Hist X} (p : PathIn tab) (q :
  PathIn (tabAt p).2.2) :
    p = p.append q ↔ q = nil := by
  induction p
  case nil => exact eq_comm
  case loc IH => simp only [PathIn.append, PathIn.loc.injEq, heq_eq_eq, true_and]; exact IH _
  case pdl IH => simp only [PathIn.append, PathIn.pdl.injEq]; exact IH _

theorem PathIn.nil_eq_append_iff_both_eq_nil {Hist X} {tab : Tableau Hist X} (p : PathIn tab) (q :
  PathIn (tabAt p).2.2) :
    .nil = p.append q ↔ p = .nil ∧ q = .nil := by
  constructor
  · intro nil_eq
    cases p
    · simp_all
    case loc IH =>
      simp [append] at nil_eq
    case pdl IH =>
      simp [append] at nil_eq
  · rintro ⟨p_def, q_def⟩
    subst_eqs
    simp

@[simp]
theorem tabAt_append {Hist X} {tab : Tableau Hist X} (p : PathIn tab) (q : PathIn (tabAt p).2.2) :
    tabAt (p.append q) = tabAt q := by
  induction p
  case nil => rfl
  case loc IH => exact IH _
  case pdl IH => exact IH _

@[simp]
theorem tabAt_nil {Hist} {tab : Tableau Hist X} : tabAt (.nil : PathIn tab) = ⟨_, _, tab⟩ := by
  simp [tabAt, tabAt]

@[simp]
theorem tabAt_loc {Hist X Y} {nrep : ¬ flprep Hist X} {nbas : ¬ X.basic}
    {lt : LocalTableau X} {next : ∀ Y ∈ endNodesOf lt, Tableau (X :: Hist) Y}
    {Y_in : Y ∈ endNodesOf lt} {tail : PathIn (next Y Y_in)} :
    tabAt (.loc Y_in tail : PathIn (.loc nrep nbas lt next)) = tabAt tail := by simp [tabAt]

@[simp]
theorem tabAt_pdl {Hist X Y} {nrep : ¬ flprep Hist X} {bas : X.basic} {r : PdlRule X Y}
    {next : Tableau (X :: Hist) Y} {tail : PathIn next} :
    tabAt (.pdl tail : PathIn (.pdl nrep bas r next)) = tabAt tail := by simp [tabAt]

/-- Given a path to node `t`, this is its label Λ(t). -/
@[expose] def nodeAt {H X} {tab : (Tableau H X)} (p : PathIn tab) : Sequent := (tabAt p).2.1

@[simp]
theorem nodeAt_nil {Hist} {tab : Tableau Hist X} : nodeAt (.nil : PathIn tab) = X := by
  simp [nodeAt, tabAt]

@[simp]
theorem nodeAt_loc {Hist X Y} {nrep : ¬ flprep Hist X} {nbas : ¬ X.basic}
    {lt : LocalTableau X} {next : ∀ Y ∈ endNodesOf lt, Tableau (X :: Hist) Y}
    {Y_in : Y ∈ endNodesOf lt} {tail : PathIn (next Y Y_in)} :
  nodeAt (.loc Y_in tail : PathIn (.loc nrep nbas lt next)) = nodeAt tail := by simp [nodeAt, tabAt]

@[simp]
theorem nodeAt_pdl {Hist X Y} {nrep : ¬ flprep Hist X} {bas : X.basic} {r : PdlRule X Y}
    {next : Tableau (X :: Hist) Y} {tail : PathIn next} :
  nodeAt (.pdl tail : PathIn (.pdl nrep bas r next)) = nodeAt tail := by simp [nodeAt, tabAt]

@[simp]
theorem nodeAt_append {Hist X} {tab : Tableau Hist X} (p : PathIn tab) (q : PathIn (tabAt p).2.2) :
    nodeAt (p.append q) = nodeAt q := by
  unfold nodeAt
  rw [tabAt_append p q]

/-- The root sequent of the tableau containing a path. -/
@[simp]
def PathIn.head {Hist} {tab : Tableau Hist X} (_ : PathIn tab) : Sequent := X

/-- The sequent reached at the end of a path. -/
@[simp]
def PathIn.last {Hist X} {tab : Tableau Hist X} (t : PathIn tab) : Sequent := (tabAt t).2.1

/-- The length of a path is the number of actual steps. -/
@[simp, implicit_reducible]
@[expose] def PathIn.length {Hist X} {tab : Tableau Hist X} : (t : PathIn tab) → ℕ
| .nil => 0
| .pdl tail => tail.length + 1
| .loc _ tail => tail.length + 1

theorem append_length {Hist X} {tab : Tableau Hist X} {p : PathIn tab} q : (p.append q).length =
  p.length + q.length := by
  induction p <;> simp only [PathIn.append, PathIn.length]
  case nil => exact (Nat.zero_add _).symm
  case loc _ _ _ _ _ _ _ _ tail IH =>
    have h : (tail.append q).length = tail.length + q.length := IH q
    omega
  case pdl _ _ _ _ _ _ _ tail IH =>
    have h : (tail.append q).length = tail.length + q.length := IH q
    omega

/-! ## Edge Relation -/

/-- Relation `s ⋖_ t` says `t` is a child of `s`. Two cases, both defined via `append`. -/
@[expose] def edge {Hist X} {tab : Tableau Hist X} (s t : PathIn tab) : Prop :=
  ( ∃ Hist X nrep nbas lt next Y,
    ∃ (Y_in : Y ∈ endNodesOf lt)
      (h : tabAt s = ⟨Hist, X, (Tableau.loc nrep nbas lt next : Tableau _ X)⟩),
      t = s.append (h ▸ PathIn.loc Y_in .nil) )
  ∨
  ( ∃ Hist X nrep bas Y r,
    ∃ (next : Tableau (X :: Hist) Y)
      (h : tabAt s = ⟨Hist, X, Tableau.pdl nrep bas r next⟩),
      t = s.append (h ▸ PathIn.pdl .nil) )

/-- Notation ⋖_ for `edge` (because ⋖ is taken in Mathlib). -/
scoped notation s:arg " ⋖_ " t:arg => edge s t

/-- Appending a one-step `loc` path is also a ⋖_ child.
When using this, this may be helpful:
`convert this; rw [← heq_iff_eq, heq_eqRec_iff_heq, eqRec_heq_iff_heq]`.
-/
theorem edge_append_loc_nil {sX sHist nrep nbas} {X} {Hist} {tab : Tableau X Hist} (s : PathIn tab)
    {lt : LocalTableau sX} (next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (sX :: sHist) Y)
    {Y : Sequent} (Y_in : Y ∈ endNodesOf lt)
    (tabAt_s_def : tabAt s = ⟨sHist, sX, Tableau.loc nrep nbas lt next⟩) :
    edge s (s.append (tabAt_s_def ▸ PathIn.loc Y_in .nil)) := by
  unfold edge
  left
  use sHist, sX, nrep, nbas, lt, next, (by assumption), Y_in
  constructor
  · rw [append_eq_iff_eq, ← heq_iff_eq, heq_eqRec_iff, eqRec_heq_iff]
  · rw [← tabAt_s_def]

/-- Appending a one-step `pdl` path is also a ⋖_ child. -/
@[simp]
theorem edge_append_pdl_nil {Hist : History} {X : Sequent} {tab : Tableau Hist X} {s : PathIn tab}
    {nrep : ¬flprep (tabAt s).fst (tabAt s).snd.fst} {bas : (tabAt s).snd.fst.basic} {Y : Sequent}
    {r : PdlRule (tabAt s).snd.fst Y} {next : Tableau ((tabAt s).snd.fst :: (tabAt s).fst) Y}
    (h : (tabAt s).2.2 = Tableau.pdl nrep bas r next) :
    edge s (s.append (h ▸ PathIn.pdl .nil)) := by
  simp only [edge, append_eq_iff_eq]
  right
  use (tabAt s).1, (tabAt s).2.1, nrep, bas, (by assumption), r, next
  constructor
  · rw [← heq_iff_eq, heq_eqRec_iff, eqRec_heq_iff]
  · rw [← h]

/-- Variant of `edge_append_pdl_nil` where the assumption is about all of `tabAt s`,
analogous to `edge_append_loc_nil`. -/
theorem edge_append_pdl_nil' {X Hist} {tab : Tableau X Hist} (s : PathIn tab)
    {sHist sX sY nrep bas} {r : PdlRule sX sY} (next : Tableau (sX :: sHist) sY)
    (tabAt_s_def : tabAt s = ⟨sHist, sX, Tableau.pdl nrep bas r next⟩) :
    edge s (s.append (tabAt_s_def ▸ PathIn.pdl .nil)) := by
  unfold edge
  right
  use sHist, sX, nrep, bas, sY, r, next, (by assumption)

-- QUESTION: Does it actually have an effect to mark this with simp?
-- FIXME: implicit `tail` argument?
@[simp]
theorem nil_edge_loc_nil {X Y : Sequent} {Hist : List Sequent} {nrep nbas}
    {lt : LocalTableau X} {Y_in : Y ∈ endNodesOf lt}
    {next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: Hist) Y}
    : (.nil : PathIn (.loc nrep nbas lt next)) ⋖_ (.loc Y_in .nil) := by
  left
  use Hist, X, nrep, nbas, lt, next, Y, Y_in, rfl
  simp_all
  rfl

-- same question and note as above
@[simp]
theorem nil_edge_pdl_nil {Hist} {X} {nrep} {bas} {Y} {r : PdlRule X Y}
    {next : Tableau (X :: Hist) Y}
    : (.nil : PathIn (.pdl nrep bas r next)) ⋖_ (.pdl .nil) := by
  right
  use Hist, X, nrep, bas, Y, r, next
  simp_all
  rfl

@[simp]
theorem loc_edge_loc_iff_edge {Y X} {lt : LocalTableau X} {Y_in : Y ∈ endNodesOf lt} {tail}
    {next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: tail) Y} {nrep nbas}
    {t s : PathIn (next Y Y_in)}
    : (.loc Y_in t : PathIn (.loc nrep nbas lt next)) ⋖_ (.loc Y_in s) ↔ (t ⋖_ s) := by
  constructor
  · rintro ( ⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def, p_def⟩
           | ⟨Hist, X, nrep, bas, Y, r, next, tab_def, p_def⟩ )
    · left
      use Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def
      simp only [PathIn.append, PathIn.loc.injEq, heq_eq_eq, true_and] at p_def
      exact p_def
    · right
      use Hist, X, nrep, bas, Y, r, next, tab_def
      simp only [PathIn.append, PathIn.loc.injEq, heq_eq_eq, true_and] at p_def
      exact p_def
  · intro t_s
    rcases t_s with ( ⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def, p_def⟩
                    | ⟨Hist, X, nrep, bas, Y, r, next, tab_def, p_def⟩ )
    · left
      use Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def
      simp only [] at p_def
      rw [p_def]
      rfl
    · right
      use Hist, X, nrep, bas, Y, r, next, tab_def
      simp only [] at p_def
      rw [p_def]
      rfl

@[simp]
theorem pdl_edge_pdl_iff_edge {X Y} {r : PdlRule X Y} {tail : List Sequent}
    {next : Tableau (X :: tail) Y} {nrep bas} {t s : PathIn next}
    : (.pdl t : PathIn (.pdl nrep bas r next)) ⋖_ (.pdl s) ↔ t ⋖_ s := by
  -- exact same proof as `loc_edge_loc_iff_edge`;-)
  constructor
  · rintro ( ⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def, p_def⟩
           | ⟨Hist, X, nrep, bas, Y, r, next, tab_def, p_def⟩ )
    · left
      use Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def
      simp only [PathIn.append, PathIn.pdl.injEq] at p_def
      exact p_def
    · right
      use Hist, X, nrep, bas, Y, r, next, tab_def
      simp only [PathIn.append, PathIn.pdl.injEq] at p_def
      exact p_def
  · intro t_s
    rcases t_s with ( ⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def, p_def⟩
                    | ⟨Hist, X, nrep, bas, Y, r, next, tab_def, p_def⟩ )
    · left
      use Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def
      simp only [] at p_def
      rw [p_def]
      rfl
    · right
      use Hist, X, nrep, bas, Y, r, next, tab_def
      simp only [] at p_def
      rw [p_def]
      rfl

/-- The root has no parent. Note this holds even when Hist ≠ []. -/
theorem not_edge_nil {Hist} (tab : Tableau Hist X) (t : PathIn tab) : ¬ edge t .nil := by
  intro t_nil
  rcases t_nil with ( ⟨Hist, Z, nrep, nbas, lt, next, Y, Y_in, tabAt_s_def, t_def⟩
                    | ⟨Hist, Z, nrep, bas, Y, r, next, tabAt_s_def, t_def⟩ )
  all_goals
    rw [PathIn.nil_eq_append_iff_both_eq_nil] at t_def
    rcases t_def with ⟨t_nil, loc_eq_nil⟩
    subst t_nil
    rw [tabAt_nil] at tabAt_s_def
    rw [Sigma.mk.inj_iff] at tabAt_s_def
    rcases tabAt_s_def with ⟨nil_eq_Hist, hyp⟩
    subst nil_eq_Hist
    rw [heq_eq_eq, Sigma.mk.inj_iff] at hyp
    rcases hyp with ⟨X_eq_Z, hyp⟩
    subst X_eq_Z
    rw [heq_eq_eq] at hyp
    subst hyp
    simp_all

theorem nodeAt_loc_nil {H : List Sequent} {lt : LocalTableau X} {nrep nbas}
    (next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: H) Y) (Y_in : Y ∈ endNodesOf lt) :
    nodeAt (@PathIn.loc H X nrep nbas lt next Y Y_in .nil) = Y := by
  simp [nodeAt, tabAt]

theorem nodeAt_pdl_nil {X : Sequent} {Hist : History} {Y : Sequent} {nrep : ¬flprep Hist X}
    {bas : X.basic} (child : Tableau (X :: Hist) Y) (r : PdlRule X Y) :
    nodeAt (@PathIn.pdl Hist X Y nrep bas r child .nil) = Y := by
  simp [nodeAt, tabAt]

/-- Any `⋖_` step is given by an end node of a local tableau or by a PDL rule. -/
lemma nodeAt_of_edge {Hist X} {tab : Tableau Hist X} {s t : PathIn tab} (h : s ⋖_ t) :
    (∃ lt : LocalTableau (nodeAt s), nodeAt t ∈ endNodesOf lt)
    ∨ Nonempty (PdlRule (nodeAt s) (nodeAt t)) := by
  rcases h with ⟨Hist', X', nrep, nbas, lt, next, Y, Y_in, tab_def, rfl⟩
              | ⟨Hist', X', nrep, bas, Y, r, next, tab_def, rfl⟩
  · left
    have hs : nodeAt s = X' := by unfold nodeAt; rw [tab_def]
    have ht : nodeAt (s.append (tab_def ▸ PathIn.loc Y_in .nil)) = Y := by
      rw [nodeAt_append]
      unfold nodeAt
      rw [tabAt_cast_gen s _ tab_def (PathIn.loc Y_in .nil)]
      simp [tabAt]
    rw [hs, ht]
    exact ⟨lt, Y_in⟩
  · right
    have hs : nodeAt s = X' := by unfold nodeAt; rw [tab_def]
    have ht : nodeAt (s.append (tab_def ▸ PathIn.pdl .nil)) = Y := by
      rw [nodeAt_append]
      unfold nodeAt
      rw [tabAt_cast_gen s _ tab_def (PathIn.pdl .nil)]
      simp [tabAt]
    rw [hs, ht]
    exact ⟨r⟩

/-- The length of `edge`-related paths differs by one. -/
theorem length_succ_eq_length_of_edge {Hist X} {tab : Tableau Hist X} {s t : PathIn tab} : s ⋖_ t
  → s.length + 1 = t.length := by
  intro s_t
  rcases s_t with ( ⟨Hist', Z', nrep, nbas, lt', next', Y', Y'_in, tabAt_s_def, t_def⟩
                  | ⟨Hist', Z', nrep, bas, Y', r', next', tabAt_s_def, t_def⟩ )
  · subst t_def
    rw [append_length, add_right_inj]
    have : 1 = (.loc Y'_in .nil : PathIn (Tableau.loc nrep nbas lt' next')).length := by simp
    convert this
    · simp_all only [PathIn.length, zero_add]
    · rw [tabAt_s_def]
    · rw [tabAt_s_def]
    · subst_eqs; simp_all only [heq_eq_eq, eqRec_heq_iff]
  · subst t_def
    rw [append_length, add_right_inj]
    have : 1 = (.pdl .nil : PathIn (Tableau.pdl nrep bas r' next')).length := by simp
    convert this
    · simp_all only [PathIn.length, zero_add]
    · rw [tabAt_s_def]
    · rw [tabAt_s_def]
    · subst_eqs; simp_all only [heq_eq_eq, eqRec_heq_iff]

theorem edge_then_length_lt {Hist X} {tab : Tableau Hist X} {s t : PathIn tab} (s_t : s ⋖_ t) :
  s.length < t.length := by
  have := length_succ_eq_length_of_edge s_t
  linarith

/-- Map tableau edges to strict increases in path length. -/
def edgeNatLTRelHom {Hist X tab} : RelHom (@edge Hist X tab) Nat.lt :=
  ⟨PathIn.length, edge_then_length_lt⟩

/-- The `⋖_` relation in a tableau is well-founded.
Proven by lifting the relation to the length of histories.
That length goes up with `⋖_`, so because `<` is wellfounded on `Nat`
also `⋖_` is well-founded via `RelHomClass.wellFounded`. -/
theorem edge.wellFounded {Hist : History} {X : Sequent} {tab : Tableau Hist X} : WellFounded
    (@edge Hist X tab) := by
  apply @RelHomClass.wellFounded _ Nat (@edge Hist X tab) Nat.lt _ _ _ edgeNatLTRelHom
  exact instWellFoundedLTNat

instance edge.isAsymm {Hist : History} {X : Sequent} {tab : Tableau Hist X} : @Std.Asymm
    (PathIn tab) edge :=
  edge.wellFounded.asymm

theorem edge_is_strict_ordering {Hist X} {tab : Tableau Hist X} {s t : PathIn tab} : s ⋖_ t → s ≠
  t := by
  intro s_t set
  have := edge_then_length_lt s_t
  simp_all

/-- Enumerate the immediate children of a tableau path. -/
def PathIn.children {Hist X} {tab : Tableau Hist X} (p : PathIn tab) : Finset {q : PathIn tab // p
  ⋖_ q} :=
  match h : tabAt p with
  | ⟨_, _, .loc _ _ lt _⟩ =>
      (endNodesOf lt).attach.image (fun ⟨_,Y_in⟩ => ⟨_, edge_append_loc_nil _ _ Y_in h⟩ )
  | ⟨_, _, .pdl _ _ _ next⟩ =>
      { ⟨_, edge_append_pdl_nil' _ next h⟩ }
  | ⟨_, _, .lrep _⟩ => {}

lemma PathIn.children_spec : p ⋖_ q ↔ q ∈ p.children.image Subtype.val := by
  constructor
  · rintro (⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, h, rfl⟩
            | ⟨Hist, X, nrep, bas, Y, r, next, h, rfl⟩)
      <;> (unfold PathIn.children; split)
      <;> (rename_i heq; rw [h] at heq)
    all_goals
      first
        -- The cases where the shape of `tabAt p` does not match `h` are contradictory:
        | (obtain ⟨rfl, hh⟩ := Sigma.mk.injEq .. ▸ heq
           obtain ⟨rfl, -⟩ := hh
           done)
        -- The `loc` case:
        | (cases heq
           simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
             Subtype.mk.injEq, exists_and_left, exists_prop, exists_eq_right_right,
             append_eq_iff_eq]
           exact ⟨⟨Y, Y_in, rfl⟩, edge_append_loc_nil p next Y_in h⟩)
        -- The `pdl` case:
        | (cases heq
           simp)
  · intro hq
    simp only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hq
    obtain ⟨p_q, _⟩ := hq
    exact p_q

instance instDecidableEdge {H X} {tab : Tableau H X} (p q : PathIn tab) :
    Decidable (p ⋖_ q) :=
  decidable_of_iff _ PathIn.children_spec.symm

/-- An induction principle for `PathIn` with a base case at the root of the tableau and
an induction step using the `edge` relation `⋖_`.

QUESTIONS:
- Do we need to add any of these attributes? @[induction_eliminator, elab_as_elim]
- Should it be a def or a theorem? (`motive` to `Prop` or to `Sort u`?)
-/
theorem PathIn.init_inductionOn {Hist X} {tab : Tableau Hist X} t {motive : PathIn tab → Prop}
    (root : motive .nil)
    (step : (t : PathIn tab) → motive t → ∀ {s}, (t_s : t ⋖_ s) → motive s)
    : motive t := by
  induction tab -- works only if motive goes to Prop!
  case loc Hist X nrep nbas lt next IH =>
    cases t
    · assumption
    case loc Y nbas nrep Y_in rest =>
      specialize @IH Y Y_in rest (motive ∘ .loc Y_in)
      simp only [Function.comp_apply] at IH
      apply IH <;> clear IH
      case root =>
        exact step nil root nil_edge_loc_nil
      case step =>
        intro t motive_t s t_edge_s
        apply @step (.loc Y_in t) motive_t (.loc Y_in s)
        rw [loc_edge_loc_iff_edge]
        exact t_edge_s
  case pdl Hist Y X nrep bas r next IH =>
    cases t
    · assumption
    case pdl rest =>
      specialize @IH rest (motive ∘ .pdl)
      simp only [Function.comp_apply] at IH
      apply IH <;> clear IH
      case root =>
        exact step nil root nil_edge_pdl_nil
      case step =>
        intro t motive_t s t_edge_s
        apply @step (.pdl t) motive_t (.pdl s)
        rw [pdl_edge_pdl_iff_edge]
        exact t_edge_s
  case lrep =>
    cases t -- path at rep must be nil
    exact root

/-! ## Transitive Closure of the Edge Relation -/

/-- Enable "<" notation for transitive closure of ⋖_. -/
instance {Hist X} {tab : Tableau Hist X} : LT (PathIn tab) := ⟨Relation.TransGen edge⟩

/-- Enable "≤" notation for reflexive transitive closure of ⋖_ -/
instance {Hist X} {tab : Tableau Hist X} : LE (PathIn tab) := ⟨Relation.ReflTransGen edge⟩

/-- The "<" in a tableau is antisymmetric. -/
instance edge.TransGen_isAsymm {Hist : History} {X : Sequent} {tab : Tableau Hist X} : @Std.Asymm
    (PathIn tab) (Relation.TransGen edge) :=
  (WellFounded.transGen wellFounded).asymm

theorem not_path_nil {Hist X} {tab : Tableau Hist X} {a : PathIn tab} : ¬(a < PathIn.nil) := by
  intro con
  cases con <;> simp_all [not_edge_nil]

theorem path_is_strict_ordering {Hist X} {tab : Tableau Hist X} {s t : PathIn tab} : s < t → s ≠ t
  := by
  intro s_t seqt
  induction s_t
  case single set =>
    absurd seqt
    exact edge_is_strict_ordering set
  case tail k t s_k k_t ih =>
    apply edge.TransGen_isAsymm.1 s k s_k
    rw [seqt]
    apply Relation.TransGen.single k_t

theorem PathIn.nil_le_anything : PathIn.nil ≤ t := by
  induction t using PathIn.init_inductionOn
  case root =>
    exact Relation.ReflTransGen.refl
  case step nil_le_s u s_edge_u =>
    apply Relation.ReflTransGen.tail nil_le_s s_edge_u

theorem PathIn.loc_le_loc_of_le {Hist : History} {X : Sequent} {nrep : ¬flprep Hist X}
    {nbas : ¬X.basic}
    {lt : LocalTableau X} {next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: Hist) Y}
      {Y : Sequent}
    {Z_in : Y ∈ endNodesOf lt} {t1 t2 : PathIn (next Y Z_in)} (h : t1 ≤ t2) :
  @loc Hist X nrep nbas lt next Y Z_in t1 ≤ @loc Hist X nrep nbas lt next Y Z_in t2 := by
  induction h
  · exact Relation.ReflTransGen.refl
  case tail s t _ s_t IH =>
    apply Relation.ReflTransGen.tail IH
    simp only [loc_edge_loc_iff_edge]
    exact s_t

theorem PathIn.pdl_le_pdl_of_le {Hist : History} {X Y : Sequent} {nrep : ¬flprep Hist X}
    {bas : X.basic}
    {r : PdlRule X Y} {Z_in : Tableau (X :: Hist) Y} {t1 t2 : PathIn Z_in} (h : t1 ≤ t2) :
  @pdl Hist X Y nrep bas r Z_in t1 ≤ @pdl Hist X Y nrep bas r Z_in t2 := by
  induction h
  · exact Relation.ReflTransGen.refl
  case tail s t _ s_t IH =>
    apply Relation.ReflTransGen.tail IH
    simp only [pdl_edge_pdl_iff_edge]
    exact s_t

/-! ## Path cast and append lemmas

Lemmas developed for `tabToIntAt`.
-/

@[simp]
lemma PathIn.cast_nil {Hist : History} {X : Sequent} {tab tab2 : Tableau Hist X} (h : tab = tab2) :
    (h ▸ (.nil : PathIn tab)) = (.nil : PathIn tab2) := by grind

lemma PathIn.tabAt_cast_nil {Hist : History} {X : Sequent} {tab tab2 : Tableau Hist X}
    (h : tab = tab2) :
    tabAt (h ▸ (PathIn.nil : PathIn tab)) = tabAt (.nil : PathIn tab2) := by
  convert @tabAt_nil; simp_all

lemma PathIn.tabAt_cast_loc {H : History} {X : Sequent} {nrep : ¬flprep H X} {nbas : ¬X.basic}
    {lt : LocalTableau X} {nexts : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: H) Y}
    {tab2 : Tableau H X} {Y : Sequent} {Y_in : Y ∈ endNodesOf lt}
      (h : (Tableau.loc nrep nbas lt nexts) = tab2)
    (tail : PathIn (nexts Y Y_in)) :
    tabAt (h ▸ (PathIn.loc Y_in tail)) = tabAt tail := by
  convert tabAt_loc <;> simp_all

lemma PathIn.tabAt_cast_pdl {H : History} {X : Sequent} {nrep : ¬flprep H X} {bas : X.basic}
    {Y : Sequent}
    {r : PdlRule X Y} {next : Tableau (X :: H) Y} {tab2 : Tableau H X} {tail : PathIn next}
    (h : Tableau.pdl nrep bas r next = tab2) :
    tabAt (h ▸ PathIn.pdl tail) = tabAt tail := by
  convert @tabAt_pdl _ _ _ nrep bas r next tail <;> simp_all

@[simp]
lemma PathIn.tabAt_cast {Hist : History} {X : Sequent} {tab tab2 : Tableau Hist X} (p : PathIn tab)
    (h : tab = tab2) :
    tabAt (h ▸ p) = tabAt p := by
  cases h
  rfl

/-- (p ++ q) ++ r = p ++ (q ++ r) -/
lemma PathIn.append_append {Hist} {tab : Tableau Hist X}
    (p : PathIn tab) (q : PathIn (tabAt p).2.2) (r : PathIn (tabAt (p.append q)).2.2)
    : (p.append q).append r = p.append (q.append (tabAt_append p q ▸ r)) := by
  induction p
  case nil => rfl
  case loc _ _ _ _ _ _ _ Y_in tail IH => exact congrArg (PathIn.loc Y_in) (IH q r)
  case pdl _ _ _ _ _ _ _ tail IH => exact congrArg PathIn.pdl (IH q r)

@[simp]
lemma PathIn.loc_append {X Hist} {nflprep : ¬ flprep Hist X} {nbas : ¬X.basic} {lt : LocalTableau X}
    {nexts : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: Hist) Y}
    {Y : Sequent} {Y_in : Y ∈ endNodesOf lt} {tail : PathIn _}
    (h : PathIn (nexts Y Y_in) = PathIn (tabAt (PathIn.loc Y_in .nil)).snd.snd)
    : (PathIn.loc Y_in .nil : PathIn (Tableau.loc nflprep nbas lt nexts)).append tail
    = PathIn.loc Y_in (h ▸ tail) := by
  simp [append]

@[simp]
lemma PathIn.pdl_append {Hist X Y} {next : Tableau (X :: Hist) Y} {nflprep : ¬ flprep Hist X}
    {bas : X.basic} {r : PdlRule X Y} {tail : PathIn (tabAt PathIn.nil.pdl).snd.snd}
    (h : PathIn next = PathIn (tabAt nil.pdl).snd.snd)
    : (PathIn.pdl .nil : PathIn (Tableau.pdl nflprep bas r next)).append tail
    = PathIn.pdl (h ▸ tail) := by
  simp [append]

/-- Used for `tabToIntAt`. -/
lemma PathIn.lt_append_non_nil {Hist X pHist pX tabNew} {tab : Tableau Hist X}
  (p : PathIn tab) (h : tabAt p = ⟨pHist, ⟨pX, tabNew⟩⟩) (q : PathIn tabNew)
  : q ≠ .nil → p < p.append (h ▸ q) := by
  cases q
  case nil => simp
  case loc Y nbas lt Y_in nflprep nexts tail =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const]
    have p_loc : p ⋖_ (p.append (h ▸ PathIn.loc Y_in .nil)) := edge_append_loc_nil _ _ _ h
    apply Relation.TransGen.head' p_loc
    by_cases tail_nil : tail = .nil
    · subst_eqs
      exact Relation.ReflTransGen.refl
    · apply Relation.TransGen.to_reflTransGen
      change (_ : PathIn tab) < _
      have IH := @PathIn.lt_append_non_nil Hist X _ _ (nexts Y Y_in) tab
      convert IH ?_ ?_ tail tail_nil using 1
      · rw [PathIn.append_append, append_eq_iff_eq]
        simp only []
        have := @PathIn.loc_append _ _ nflprep nbas lt nexts Y Y_in tail rfl
        convert this <;> try rw [h]
        · simp_all
        · grind
      · simp only [tabAt_append]
        rw! [h]
        simp
  case pdl Y bas r nflprep next tail =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const]
    have p_pdl : p ⋖_ (p.append (h ▸ nil.pdl)) := by
      have := @edge_append_pdl_nil Hist X tab p
      rw! (castMode := .all) [h] at this
      simp only [Tableau.pdl.injEq, forall_and_index] at this
      exact @this nflprep bas Y r next rfl (by simp) (by simp)
    apply Relation.TransGen.head' p_pdl
    by_cases tail_nil : tail = .nil
    · subst_eqs
      exact Relation.ReflTransGen.refl
    · apply Relation.TransGen.to_reflTransGen
      change (_ : PathIn tab) < _
      have IH := @PathIn.lt_append_non_nil _ _ _ _ next tab
      convert IH ?_ ?_ tail tail_nil using 1
      · rw [PathIn.append_append, append_eq_iff_eq]
        simp only []
        have := @PathIn.pdl_append _ _ _ next nflprep bas r tail rfl
        convert this <;> try rw [h]
        · simp_all
        · grind
      · simp only [tabAt_append]
        rw! [h]
        simp
termination_by
  tabNew.size
decreasing_by
  · subst_eqs
    apply Tableau.size_next_lt_of_loc rfl
  · subst_eqs
    apply Tableau.size_next_lt_of_pdl rfl

/-! ## From Path to History -/

/-- Convert a path to a History.
Does not include the last node.
The history of `.nil` is `[]` because this will not go into `Hist`. -/
@[implicit_reducible]
@[expose] def PathIn.toHistory {Hist} {tab : Tableau Hist X} : (t : PathIn tab) → History
| .nil => []
| .pdl tail => tail.toHistory ++ [X]
| .loc _ tail => tail.toHistory ++ [X]

/-- Convert a path to a list of nodes. Reverse of the history and does include the last node.
The list of `.nil` is `[X]`. -/
def PathIn.toList {Hist} {tab : Tableau Hist X} : (t : PathIn tab) → List Sequent
| .nil => [X]
| .pdl tail => X :: tail.toList
| .loc _ tail => X :: tail.toList

/-- A path gives the same list of nodes as the history of its last node. -/
theorem PathIn.toHistory_eq_Hist {Hist} {tab : Tableau Hist X} (t : PathIn tab) :
    t.toHistory ++ Hist = (tabAt t).1 := by
  induction tab
  all_goals
    cases t <;> simp_all [tabAt, PathIn.toHistory]

-- TODO generalise [] to Hist with + Hist.length ??
theorem tabAt_fst_length_eq_toHistory_length {tab : Tableau [] X} (s : PathIn tab) :
    (tabAt s).fst.length = s.toHistory.length := by
  have := PathIn.toHistory_eq_Hist s
  rw [← this]
  simp

@[simp]
theorem PathIn.loc_length_eq {X Y Hist} {nrep nbas} {lt : LocalTableau X}
    {next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: Hist) Y}
    Y_in (tail : PathIn (next Y Y_in))
    : (loc Y_in tail : PathIn (.loc nrep nbas lt next)).toHistory.length
      = tail.toHistory.length + 1 := by
  simp [PathIn.toHistory]

@[simp]
theorem PathIn.pdl_length_eq {X Y Hist} {nrep bas} {next : Tableau (X :: Hist) Y} {r}
    (tail : PathIn next)
    : (pdl tail : PathIn (.pdl nrep bas r next)).toHistory.length = tail.toHistory.length + 1 := by
  simp [PathIn.toHistory]

/-- Prefix of a path, taking only the first `k` steps. -/
def PathIn.prefix {Hist} {tab : Tableau Hist X} : (t : PathIn tab) → (k : Fin (t.length + 1)) →
  PathIn tab
| .nil, _ => .nil
| .pdl tail, k => Fin.cases (.nil) (fun j => .pdl (tail.prefix j)) k
| .loc Y_in tail, k => Fin.cases (.nil) (fun j => .loc Y_in (tail.prefix j)) k

/-- The list of a prefix of a path is the same as the prefix of the list of the path. -/
theorem PathIn.prefix_toList_eq_toList_take {Hist} {tab : Tableau Hist X}
    (t : PathIn tab) (k : Fin (t.length + 1))
    : (t.prefix k).toList = (t.toList).take (k + 1) := by
  induction tab
  case loc rest Y lt next IH =>
    cases t
    case nil =>
      simp [PathIn.toList, PathIn.prefix]
    case loc Z Z_in tail =>
      simp only [«prefix», length, toList, List.take_succ_cons]
      induction k using Fin.inductionOn
      case zero => rfl
      case succ => simp_all [PathIn.toList]
  case pdl =>
    cases t
    case nil =>
      simp_all [PathIn.toList, PathIn.prefix]
    case pdl rest Y Z r tab IH tail =>
      simp only [«prefix», length, toList, List.take_succ_cons]
      induction k using Fin.inductionOn
      case zero => rfl
      case succ => simp_all [PathIn.toList]
  case lrep =>
    cases t
    simp_all [PathIn.toList, PathIn.prefix]

/-! ## Path Rewinding -/

/-- Rewinding a path, removing the last `k` steps. Cannot go into Hist.
Used to go to the `companion` of a repeat. Returns `.nil` when `k` is the length of the whole path.
We use +1 in the type because `rewind 0` is always possible, even with history `[]`.
Defined using Fin.lastCases.

Hint: when proving stuff about `rewind k`, avoid induction on k, because rewind does not decrease k.
-/
@[expose]
def PathIn.rewind {Hist : History} {X : Sequent} {tab : Tableau Hist X} : (t : PathIn tab) →
    (k : Fin (t.toHistory.length + 1)) → PathIn tab
| .nil, _ => .nil
| .loc Y_in tail, k => Fin.lastCases (.nil)
    (PathIn.loc Y_in ∘ tail.rewind ∘ Fin.cast (loc_length_eq Y_in tail)) k
| .pdl tail, k => Fin.lastCases (.nil)
    (PathIn.pdl ∘ tail.rewind ∘ Fin.cast (pdl_length_eq tail)) k

/-- Rewinding 0 steps does nothing. -/
theorem PathIn.rewind_zero {Hist} {tab : Tableau Hist X} {p : PathIn tab} : p.rewind 0 = p := by
  induction p <;> simp only [rewind]
  case loc Hist0 X0 nrep nbas lt next Y Y_in tail IH =>
    -- TODO
    -- The rest here would be nice as a lemma, a variant of `Fin.lastCases_castSucc`
    -- and maybe it could be called `Fin.lastCases_castSucc_of_ne_last`.
    have : 0 ≠ Fin.last (.loc Y_in tail : PathIn (.loc nrep nbas lt next)).toHistory.length := by
      simp_all
    rw [← Fin.exists_castSucc_eq] at this
    rcases this with ⟨k,kdef⟩
    simp only [← kdef, Fin.lastCases_castSucc, Function.comp_apply, loc.injEq, heq_eq_eq, true_and]
    convert IH
    cases k
    simp_all
  case pdl Y Z X0 nrep bas r next tail IH =>
    have : 0 ≠ Fin.last (.pdl tail : PathIn (.pdl nrep bas r next)).toHistory.length := by
      simp_all
    rw [← Fin.exists_castSucc_eq] at this
    rcases this with ⟨k,kdef⟩
    simp only [← kdef, Fin.lastCases_castSucc, Function.comp_apply, pdl.injEq]
    convert IH
    cases k
    simp_all

theorem PathIn.rewind_le {Hist X} {tab : Tableau Hist X} (t : PathIn tab) (k : Fin
  (t.toHistory.length + 1)) : t.rewind k ≤ t := by
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases t <;> simp only [rewind]
    case nil =>
      exact Relation.ReflTransGen.refl
    case loc Z nbas nrep Z_in tail =>
      specialize IH Z Z_in tail
      cases k using Fin.lastCases
      case last =>
        rw [Fin.lastCases_last]
        exact PathIn.nil_le_anything
      case cast j =>
        simp only [Fin.lastCases_castSucc, Function.comp_apply]
        apply PathIn.loc_le_loc_of_le
        apply IH
  case pdl =>
    cases t <;> simp only [rewind]
    case nil =>
      exact Relation.ReflTransGen.refl
    case pdl rest Y Z r tab IH bas nrep tail =>
      specialize IH tail
      cases k using Fin.lastCases
      case last =>
        rw [Fin.lastCases_last]
        exact PathIn.nil_le_anything
      case cast j =>
        simp only [Fin.lastCases_castSucc, Function.comp_apply]
        apply PathIn.pdl_le_pdl_of_le
        apply IH
  case lrep =>
    cases t
    simp only [rewind]
    exact Relation.ReflTransGen.refl

/-- If we rewind by `k > 0` steps then the length goes down. -/
theorem PathIn.rewind_length_lt_length_of_gt_zero {Hist X} {tab : Tableau Hist X}
    (t : PathIn tab) (k : Fin (t.toHistory.length + 1)) (k_gt_zero : k > 0)
    : (t.rewind k).length < t.length := by
  induction t
  · exfalso
    rcases k with ⟨k, k_prop⟩
    simp only [toHistory, List.length_nil, zero_add, Nat.lt_one_iff] at k_prop
    subst k_prop
    simp_all
  case loc H Z Y ltX next Y_in tail IH =>
      cases k using Fin.lastCases
      · simp [PathIn.toHistory, PathIn.rewind] at *
      case cast j =>
        specialize IH ⟨j, by rcases j with ⟨j,j_lt⟩; rw [loc_length_eq] at j_lt; simp_all⟩ k_gt_zero
        simp only [rewind, Fin.lastCases_castSucc, Function.comp_apply, length,
          add_lt_add_iff_right]
        convert IH <;> simp [Fin.heq_ext_iff _]
  case pdl Z Y H next r tail IH =>
    cases k using Fin.lastCases
    · simp [PathIn.toHistory, PathIn.rewind] at *
    case cast j =>
      specialize IH ⟨j, by rcases j with ⟨j,j_lt⟩; rw [pdl_length_eq] at j_lt; simp_all⟩ k_gt_zero
      simp only [rewind, Fin.lastCases_castSucc, Function.comp_apply, length, add_lt_add_iff_right]
      convert IH <;> simp [Fin.heq_ext_iff _]

theorem PathIn.rewind_lt_of_gt_zero {Hist X} {tab : Tableau Hist X}
    (t : PathIn tab) (k : Fin (t.toHistory.length + 1)) (k_gt_zero : k > 0) :
    (t.rewind k) < t := by
  have h : t.rewind k ≤ t := PathIn.rewind_le t k
  apply Relation.TransGen_of_ReflTransGen h
  intro con
  have length_lt : (t.rewind k).length < t.length :=
    PathIn.rewind_length_lt_length_of_gt_zero t k k_gt_zero
  have length_eq : (t.rewind k).length = t.length := by simp [con]
  simp_all

/-- The node we get from rewinding `k` steps is element `k+1` in the history. -/
theorem PathIn.nodeAt_rewind_eq_toHistory_get {Hist} {tab : Tableau Hist X}
    (t : PathIn tab) (k : Fin (t.toHistory.length + 1))
    : nodeAt (t.rewind k) = (nodeAt t :: t.toHistory).get k := by
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases t
    case nil =>
      simp [PathIn.toHistory, PathIn.rewind]
    case loc Z nbas nrep Z_in tail =>
      cases k using Fin.lastCases
      · simp [PathIn.toHistory, PathIn.rewind] at *
      case cast j =>
        specialize IH Z Z_in tail
        simp_all only [List.get_eq_getElem, List.length_cons, rewind, toHistory,
          Fin.lastCases_castSucc, Function.comp_apply, nodeAt_loc, Fin.val_cast, Fin.val_castSucc]
        rcases j with ⟨j,j_lt⟩
        rw [loc_length_eq] at j_lt
        have := @List.getElem_append _ (nodeAt tail :: tail.toHistory) [Y] j ?_
        · simp only [List.cons_append, List.length_cons, List.getElem_singleton] at this
          simp_all only [dite_true]
        · simp only [List.cons_append, List.length_cons, List.length_append]
          exact Nat.lt_add_right 1 j_lt
  case pdl =>
    cases t
    case nil =>
      simp_all [PathIn.toHistory, PathIn.rewind]
    case pdl rest Z Y _ _ r tab IH bas nrep tail =>
      cases k using Fin.lastCases
      · simp [PathIn.toHistory, PathIn.rewind] at *
      case cast j =>
        specialize IH tail
        simp_all only [List.get_eq_getElem, List.length_cons, rewind, toHistory,
          Fin.lastCases_castSucc, Function.comp_apply, nodeAt_pdl, Fin.val_cast, Fin.val_castSucc]
        rcases j with ⟨j,j_lt⟩
        rw [pdl_length_eq] at j_lt
        have := @List.getElem_append _ (nodeAt tail :: tail.toHistory) [Z] j ?_
        · simp only [List.cons_append, List.length_cons, List.getElem_singleton] at this
          simp_all only [dite_true]
        · simp only [List.cons_append, List.length_cons, List.length_append]
          exact Nat.lt_add_right 1 j_lt
  case lrep =>
    cases t
    simp_all [PathIn.toHistory, PathIn.rewind]

theorem nil_iff_length_zero {Hist X} {tab : Tableau Hist X} {a : PathIn tab} :
    a = PathIn.nil ↔ a.toHistory = [] := by
  constructor
  · intro a_nil
    subst a_nil
    simp [PathIn.toHistory]
  · cases a <;> simp [PathIn.toHistory]

lemma PathIn.loc_injective {Hist X nrep nbas lt next Y Y_in ta tb} :
    @PathIn.loc Hist X nrep nbas lt next Y Y_in ta = PathIn.loc Y_in tb → ta = tb := by
  simp

lemma PathIn.pdl_injective {Hist X Y nrep bas next} r ta tb :
    @PathIn.pdl Hist X Y nrep bas r next ta = PathIn.pdl tb → ta = tb := by
  simp

theorem edge_is_irreflexive {Hist X} {tab : Tableau Hist X} {a : PathIn tab} : ¬(a ⋖_ a) := by
  intro con
  have := edge_then_length_lt con
  simp_all

theorem path_then_length_lt {Hist X} {tab : Tableau Hist X} {s t : PathIn tab} (s_t : s < t) :
  s.length < t.length := by
  induction s_t
  case single set => exact edge_then_length_lt set
  case tail h ih => have := edge_then_length_lt h
                    linarith

theorem path_is_irreflexive {Hist X} {tab : Tableau Hist X} {a : PathIn tab} : ¬(Relation.TransGen
  edge a a) := by
  intro con
  have := path_then_length_lt con
  simp_all

theorem rewind_order_reversing {Hist X} {tab : Tableau Hist X} {t : PathIn tab} {k k' : Fin
  (List.length t.toHistory + 1)}
    (h : k < k') : t.rewind k' ≤ t.rewind k := by -- We have to put ≤ to deal with nil.
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases t <;> simp only [PathIn.rewind]
    case nil =>
      exact Relation.ReflTransGen.refl
    case loc Z nbas nrep Z_in tail =>
      cases k using Fin.lastCases
      case last =>
        cases k' using Fin.lastCases
        case last =>
          rw [Fin.lastCases_last]
          exact PathIn.nil_le_anything
        case cast j' =>
          absurd h
          have ⟨j'_val, j'_pf⟩ := j'
          simp only [Fin.last, PathIn.loc_length_eq, Fin.castSucc_mk, Fin.mk_lt_mk, not_lt,
            ge_iff_le]
          simp only [PathIn.toHistory, List.length_append, List.length_cons, List.length_nil,
            zero_add] at j'_pf
          exact Nat.le_of_lt j'_pf
      case cast j =>
        cases k' using Fin.lastCases
        case last =>
          rw [Fin.lastCases_last]
          exact PathIn.nil_le_anything
        case cast j' =>
          simp only [Fin.lastCases_castSucc, Function.comp_apply]
          apply PathIn.loc_le_loc_of_le
          apply IH
          · simp_all
  case pdl => -- almost the same as `loc`, maybe change to `all_goals`?
    cases t <;> simp only [PathIn.rewind]
    case nil =>
      exact Relation.ReflTransGen.refl
    case pdl rest Y Z r tab IH bas nrep tail =>
      cases k using Fin.lastCases
      case last =>
        cases k' using Fin.lastCases
        case last =>
          rw [Fin.lastCases_last]
          exact PathIn.nil_le_anything
        case cast j' =>
          simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last]
          absurd h
          have ⟨j'_val, j'_pf⟩ := j'
          simp only [Fin.last, PathIn.pdl_length_eq, Fin.castSucc_mk, Fin.mk_lt_mk, not_lt,
            ge_iff_le]
          simp only [PathIn.toHistory, List.length_append, List.length_cons, List.length_nil,
            zero_add] at j'_pf
          exact Nat.le_of_lt j'_pf
      case cast j =>
        cases k' using Fin.lastCases
        case last =>
          rw [Fin.lastCases_last]
          exact PathIn.nil_le_anything
        case cast j' =>
          simp only [Fin.lastCases_castSucc, Function.comp_apply]
          apply PathIn.pdl_le_pdl_of_le
          apply IH
          · simp_all
  case lrep =>
    cases t
    simp only [PathIn.rewind]
    exact Relation.ReflTransGen.refl

theorem PathIn.loc_lt_loc_of_lt {Hist X Y nrep nbas lt next Z_in} {t1 t2} (h : t1 < t2) :
    @loc Hist X Y nrep nbas lt next Z_in t1 < @ loc Hist X Y nrep nbas lt next Z_in t2 :=
  Relation.TransGen_of_ReflTransGen (PathIn.loc_le_loc_of_le (Relation.TransGen.to_reflTransGen h))
  <| by
  simp_all only [ne_eq, loc.injEq, heq_eq_eq, true_and]
  intro con
  subst con
  exact path_is_irreflexive h

theorem PathIn.pdl_lt_pdl_of_lt {Hist X Y nrep bas r Z_in} {t1 t2} (h : t1 < t2) :
    @pdl Hist X Y nrep bas r Z_in t1 < @pdl Hist X Y nrep bas r Z_in t2 :=
  Relation.TransGen_of_ReflTransGen (PathIn.pdl_le_pdl_of_le (Relation.TransGen.to_reflTransGen h))
  <| by
  simp_all only [ne_eq, pdl.injEq]
  intro con
  subst con
  exact path_is_irreflexive h

-- needs a better name
theorem one_is_one_helper {h : k > 0} :
    (1 : ℕ) = (1 : Fin (k + 1)).1 := by
  simp only [Fin.coe_ofNat_eq_mod]
  induction k
  case zero => simp_all
  case succ n ih => simp

theorem rewind_of_edge_is_eq {Hist X} {tab : Tableau Hist X} {a b : PathIn tab} (a_b : a ⋖_ b) :
  b.rewind 1 = a := by
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases b <;> simp_all only [PathIn.rewind]
    case nil => simp_all [not_edge_nil]
    case loc Z nbas' nrep' Z_in tail =>
      cases a
      case nil =>
        have t_nil : tail = PathIn.nil := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, tabAt_def, p_def⟩
                          | ⟨_, _, _, _, _, _, _, tabAt_def, p_def⟩ )
          · simp only [PathIn.append] at p_def
            apply PathIn.loc_injective
            rw [p_def]
            unfold tabAt at tabAt_def
            aesop
          · exfalso
            unfold tabAt at tabAt_def
            aesop
        subst t_nil
        rfl
      case loc X nbas'' nrep'' X_in tail' =>
        have Z_X : Z = X := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, _, p_def⟩ | ⟨_, _, _, _, _, _, _, _, p_def⟩ )
          all_goals
          simp only [PathIn.append, PathIn.loc.injEq] at p_def
          exact p_def.1
        have Z_in_X_in : HEq Z_in X_in := by simp_all
        subst Z_X Z_in_X_in
        simp only [loc_edge_loc_iff_edge] at a_b
        specialize IH Z Z_in a_b
        have hyp' : List.length (tail.toHistory) + 1 ≠ 1 := by
          have t_ne_nil : tail ≠ PathIn.nil := by
            intro con
            subst con
            exact not_edge_nil _ _ a_b
          simp only [ne_eq, Nat.add_eq_right, List.length_eq_zero_iff]
          by_contra con
          have t_nil := nil_iff_length_zero.2 con
          simp_all
        have hyp : (1 : Fin ((PathIn.loc Z_in tail
              : PathIn (Tableau.loc nrep' nbas' lt next)).toHistory.length + 1))
            ≠ Fin.last _ := by
          simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
        rw [← Fin.exists_castSucc_eq] at hyp
        rcases hyp with ⟨k,kdef⟩
        simp only [← kdef, Fin.lastCases_castSucc, Function.comp_apply, PathIn.loc.injEq,
          heq_eq_eq, true_and]
        rw [← IH]
        convert rfl
        simp only [ne_eq, Nat.add_eq_right, List.length_eq_zero_iff, Fin.ext_iff,
          Fin.val_castSucc, Fin.coe_ofNat_eq_mod, PathIn.loc_length_eq, Nat.one_mod, Fin.val_cast]
            at *
        rw [kdef, @Nat.one_mod_eq_one]
        aesop
  case pdl rest Y X nrep bas r tab IH =>
    cases b <;> simp_all only [PathIn.rewind]
    case nil => simp_all [not_edge_nil]
    case pdl Z bas' nrep' tail =>
      cases a
      case nil =>
        have t_nil : tail = PathIn.nil := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, tabAt_def, p_def⟩
                          | ⟨_, _, _, _, _, _, _, tabAt_def, p_def⟩ )
          · exfalso
            unfold tabAt at tabAt_def
            aesop
          · simp only [PathIn.append] at p_def
            apply PathIn.pdl_injective
            rw [p_def]
            unfold tabAt at tabAt_def
            aesop
        subst t_nil
        rfl
      case pdl bas'' nrep'' tail' =>
        simp only [pdl_edge_pdl_iff_edge] at a_b
        specialize IH a_b
        have hyp' : List.length (tail.toHistory) + 1 ≠ 1 := by
          have t_ne_nil : tail ≠ PathIn.nil := by
            intro con
            subst con
            exact not_edge_nil _ _ a_b
          simp only [ne_eq, Nat.add_eq_right, List.length_eq_zero_iff]
          by_contra con
          have t_nil := nil_iff_length_zero.2 con
          simp_all
        have hyp : (1 : Fin ((PathIn.pdl tail
              : PathIn (Tableau.pdl nrep' bas' r tab)).toHistory.length + 1))
            ≠ Fin.last _ := by
          simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
        rw [← Fin.exists_castSucc_eq] at hyp
        rcases hyp with ⟨k,kdef⟩
        simp only [← kdef, Fin.lastCases_castSucc, Function.comp_apply, PathIn.pdl.injEq]
        rw [← IH]
        convert rfl
        simp only [ne_eq, Nat.add_eq_right, List.length_eq_zero_iff, Fin.ext_iff,
          Fin.val_castSucc, Fin.coe_ofNat_eq_mod, PathIn.pdl_length_eq, Nat.one_mod, Fin.val_cast]
            at *
        rw [kdef, @Nat.one_mod_eq_one]
        aesop
  case lrep => cases b; simp [not_edge_nil] at a_b

theorem rewind_order_reversing_if_not_nil {Hist X} {tab : Tableau Hist X} {t : PathIn tab}
    {k k' : Fin (List.length t.toHistory + 1)} (h : k < k') (h' : t ≠ PathIn.nil) :
    t.rewind k' < t.rewind k := by
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases t <;> simp only [PathIn.rewind]
    case nil =>
      simp_all
    case loc Z nbas nrep Z_in tail =>
      cases k using Fin.lastCases
      case last =>
        cases k' using Fin.lastCases
        case last =>
          absurd h
          simp
        case cast j' =>
          absurd h
          have ⟨j'_val, j'_pf⟩ := j'
          simp only [Fin.last, PathIn.loc_length_eq, Fin.castSucc_mk, Fin.mk_lt_mk, not_lt,
            ge_iff_le]
          simp only [PathIn.toHistory, List.length_append, List.length_cons, List.length_nil,
            zero_add] at j'_pf
          exact Nat.le_of_lt j'_pf
      case cast j =>
        cases k' using Fin.lastCases
        case last =>
          simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last]
          apply Relation.TransGen_of_ReflTransGen (PathIn.nil_le_anything)
          simp
        case cast j' =>
          have ⟨j'_val, j'_pf⟩ := j'
          have ⟨j_val, j_pf⟩ := j
          simp only [Fin.lastCases_castSucc, Function.comp_apply]
          apply PathIn.loc_lt_loc_of_lt
          apply IH
          · simp_all
          · intro con
            subst con
            simp [PathIn.toHistory] at j_pf
            simp [PathIn.toHistory] at j'_pf
            simp_all
  case pdl  => -- almost the same as `loc`, maybe change to `all_goals`?
    cases t <;> simp only [PathIn.rewind]
    case nil =>
      simp_all
    case pdl rest Y Z r tab IH bas nrep tail =>
      cases k using Fin.lastCases
      case last =>
        cases k' using Fin.lastCases
        case last =>
          absurd h
          simp
        case cast j' =>
          absurd h
          have ⟨j'_val, j'_pf⟩ := j'
          simp only [Fin.last, PathIn.pdl_length_eq, Fin.castSucc_mk, Fin.mk_lt_mk, not_lt,
            ge_iff_le]
          simp only [PathIn.toHistory, List.length_append, List.length_cons, List.length_nil,
            zero_add] at j'_pf
          exact Nat.le_of_lt j'_pf
      case cast j =>
        cases k' using Fin.lastCases
        case last =>
          simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last]
          apply Relation.TransGen_of_ReflTransGen (PathIn.nil_le_anything)
          simp
        case cast j' =>
          have ⟨j'_val, j'_pf⟩ := j'
          have ⟨j_val, j_pf⟩ := j
          simp only [Fin.lastCases_castSucc, Function.comp_apply]
          apply PathIn.pdl_lt_pdl_of_lt
          apply IH
          · simp_all
          · intro con
            subst con
            simp [PathIn.toHistory] at j_pf
            simp [PathIn.toHistory] at j'_pf
            simp_all
  case lrep =>
    cases t
    simp only [PathIn.rewind]
    simp_all

theorem rewind_is_inj {Hist X} {tab : Tableau Hist X} {t : PathIn tab} {k k'} (h1 : t.rewind k =
  t.rewind k') : k = k' := by
  cases eq_or_ne t PathIn.nil
  case inl t_eq_nil =>
    subst t_eq_nil
    have ⟨k_val, k_pf⟩ := k
    have ⟨k'_val, k'_pf⟩ := k'
    simp [PathIn.toHistory] at k_pf
    simp [PathIn.toHistory] at k'_pf
    simp_all
  case inr t_ne_nil =>
    apply Fin.le_antisymm
    all_goals
    by_contra hyp
    simp only [not_le] at hyp
    have := rewind_order_reversing_if_not_nil hyp t_ne_nil
    simp_all only [ne_eq]
    exact path_is_irreflexive this

theorem one_is_one_rewind_helper {Hist X} {tab : Tableau Hist X} {b : PathIn tab} {k : Fin
  (List.length b.toHistory + 1)}
    (h : (b.rewind k) ⋖_ b) : k = (1 : Fin (List.length b.toHistory + 1)) := by
  have := rewind_of_edge_is_eq h
  exact Eq.symm (rewind_is_inj this)

lemma edge_leftInjective {Hist} {tab : Tableau Hist X} (a b c : PathIn tab) :
    a ⋖_ c → b ⋖_ c → a = b := by
  intro a_c b_c
  apply rewind_of_edge_is_eq at a_c
  apply rewind_of_edge_is_eq at b_c
  simp_all

lemma edge_revEuclideanHelper {Hist X} {tab : Tableau Hist X} (a b c : PathIn tab) : a ⋖_ c → b <
  c → b ≤ a := by
  intro a_c b_c
  cases b_c
  case single b_c =>
    have a_eq_c := edge_leftInjective a b c a_c b_c
    simp_all only [ge_iff_le]
    exact Relation.ReflTransGen.refl
  case tail d b_d d_c =>
    have a_eq_d := edge_leftInjective a d c a_c d_c
    rw [a_eq_d]
    exact Relation.TransGen.to_reflTransGen b_d

lemma path_revEuclidean {Hist X} {tab : Tableau Hist X} (a b c : PathIn tab) :
    a < c → b < c → (a < b ∨ b < a ∨ b = a) := by
  intro a_lt_c b_lt_c
  induction a_lt_c
  case single c a_ed_b =>
    have b_le_a := edge_revEuclideanHelper a b c a_ed_b b_lt_c
    cases eq_or_ne b a
    case inl b_eq_a => exact Or.inr (Or.inr b_eq_a)
    case inr b_ne_a => exact Or.inr (Or.inl (Relation.TransGen_of_ReflTransGen b_le_a b_ne_a))
  case tail d c a_d d_c ih =>
    have b_le_d : b ≤ d := edge_revEuclideanHelper d b c d_c b_lt_c
    cases eq_or_ne b d
    case inl b_eq_d =>
      rw [←b_eq_d] at a_d
      exact Or.inl a_d
    case inr b_ne_d => exact ih (Relation.TransGen_of_ReflTransGen b_le_d b_ne_d)

lemma path_revEuclidean' {Hist X} {tab : Tableau Hist X} (a b c : PathIn tab) :
    a < c → b < c → (a ≤ b ∨ b ≤ a) := by
  intro a_c b_c
  rcases (path_revEuclidean a b c a_c b_c) with a_b | b_a | a_eq_b
  case inl => exact Or.inl (Relation.TransGen.to_reflTransGen a_b)
  case inr =>
    have a_a : a ≤ a := by exact Relation.ReflTransGen.refl
    left
    simp_all
  case inr.inl => exact Or.inr (Relation.TransGen.to_reflTransGen b_a)

theorem edge_inc_length_by_one {Hist X} {tab : Tableau Hist X} {a b : PathIn tab} (a_b : edge a b) :
    List.length a.toHistory + 1 + 1 = List.length b.toHistory + 1 := by
  have a_is_b_re_1 := rewind_of_edge_is_eq a_b
  subst a_is_b_re_1
  induction b
  case nil => simp [not_edge_nil] at a_b
  case loc Hist X nrep nbas lt next Y Y_in tail IH =>
    by_cases tail = PathIn.nil
    case pos tail_eq_nil =>
      subst tail_eq_nil
      rfl
    case neg tail_ne_nil =>
      have helper : (1 : Fin ((PathIn.loc Y_in tail
            : PathIn (Tableau.loc nrep nbas lt next)).toHistory.length + 1))
          ≠ Fin.last _ := by
        have hyp : ¬ (1 = (List.length tail.toHistory + 1)) := by
          simp only [Nat.right_eq_add, List.length_eq_zero_iff]
          intro con
          have := nil_iff_length_zero.2 con
          simp_all
        intro con
        simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
      simp only [Nat.add_right_cancel_iff, PathIn.rewind, PathIn.loc_length_eq] at *
      -- similar to something above, should be same lemma?
      rw [← Fin.exists_castSucc_eq] at helper
      rcases helper with ⟨k, kdef⟩
      rw [← kdef] at a_b
      simp only [Fin.lastCases_castSucc, Function.comp_apply, loc_edge_loc_iff_edge] at a_b
      have := one_is_one_rewind_helper a_b
      simp_all [← kdef]
  case pdl Hist X Y nrep bas r next tail IH => -- exactly the same as loc case
    by_cases tail = PathIn.nil
    case pos tail_eq_nil =>
      subst tail_eq_nil
      rfl
    case neg tail_ne_nil =>
      have helper : (1 : Fin ((PathIn.pdl tail
            : PathIn (Tableau.pdl nrep bas r next)).toHistory.length + 1))
          ≠ Fin.last _ := by
        have hyp : ¬ (1 = (List.length tail.toHistory + 1)) := by
          simp only [Nat.right_eq_add, List.length_eq_zero_iff]
          intro con
          have := nil_iff_length_zero.2 con
          simp_all
        intro con
        simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
      simp only [Nat.add_right_cancel_iff, PathIn.rewind, PathIn.pdl_length_eq] at *
      -- similar to something above, should be same lemma?
      rw [← Fin.exists_castSucc_eq] at helper
      rcases helper with ⟨k, kdef⟩
      rw [← kdef] at a_b
      simp only [Fin.lastCases_castSucc, Function.comp_apply, pdl_edge_pdl_iff_edge] at a_b
      have := one_is_one_rewind_helper a_b
      simp_all [← kdef]

theorem rewind_helper {Hist X} {tab : Tableau Hist X} {a b : PathIn tab} {k : Fin (List.length
  a.toHistory + 1)} (a_b : a ⋖_ b) :
    b.rewind (Fin.cast (edge_inc_length_by_one a_b) (k.succ)) = a.rewind k := by
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases b
    case nil => simp [not_edge_nil] at a_b
    case loc Z nbas' nrep' Z_in tail =>
      cases a
      case nil =>
        have t_nil : tail = PathIn.nil := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, tabAt_def, p_def⟩
                        | ⟨_, _, _, _, _, _, _, tabAt_def, p_def⟩ )
          · simp only [PathIn.append] at p_def
            apply PathIn.loc_injective
            rw [p_def]
            unfold tabAt at tabAt_def
            aesop
          · exfalso
            unfold tabAt at tabAt_def
            aesop
        subst t_nil
        simp_all [PathIn.rewind, Fin.lastCases, PathIn.toHistory]
        have ⟨k_val, k_pf⟩ := k
        simp [PathIn.toHistory] at k_pf
        simp_all
        rfl
      case loc X nbas'' nrep'' X_in tail' =>
        have Z_X : Z = X := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, _, p_def⟩ | ⟨_, _, _, _, _, _, _, _, p_def⟩ )
          all_goals
          simp only [PathIn.append, PathIn.loc.injEq] at p_def
          exact p_def.1
        have Z_in_X_in : HEq Z_in X_in := by simp_all
        subst Z_X
        subst Z_in_X_in
        have t'_t : tail' ⋖_ tail := by simp_all
        simp only [PathIn.rewind]
        cases k using Fin.lastCases
        case last => simp
        case cast i =>
          -- TODO same lemma?
          have h : (Fin.cast (Nat.succ.inj (edge_inc_length_by_one a_b)) i.castSucc).succ
                  ≠ Fin.last (List.length (PathIn.loc Z_in tail).toHistory) := by
            intro con
            have ⟨i_val, i_pf⟩ := i
            simp_all [Fin.last]
            simp [PathIn.toHistory] at i_pf
            have := edge_inc_length_by_one t'_t
            linarith
          rw [← Fin.exists_castSucc_eq] at h
          rcases h with ⟨k, kdef⟩
          simp only [Fin.cast_succ_eq, ← kdef, Fin.lastCases_castSucc, Function.comp_apply,
            PathIn.loc.injEq, heq_eq_eq, true_and]
          have := @IH Z Z_in tail' tail (Fin.cast (PathIn.loc_length_eq Z_in tail') i) t'_t
          rcases k with ⟨k, k_lt⟩
          convert this
          simp only [Fin.cast_succ_eq, Fin.cast_cast, Fin.castSucc_mk, PathIn.loc_length_eq,
            Nat.add_right_cancel_iff, Fin.val_succ, Fin.val_cast] at *
          cases kdef
          simp
  case pdl rest Y X nrep bas r tab IH =>
    cases b
    case nil => simp [not_edge_nil] at a_b
    case pdl Z bas' nrep' tail =>
      cases a
      case nil =>
        have t_nil : tail = PathIn.nil := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, tabAt_def, p_def⟩
                        | ⟨_, _, _, _, _, _, _, tabAt_def, p_def⟩ )
          · exfalso
            unfold tabAt at tabAt_def
            aesop
          · simp only [PathIn.append] at p_def
            apply PathIn.pdl_injective
            rw [p_def]
            unfold tabAt at tabAt_def
            aesop
        subst t_nil
        simp_all [PathIn.rewind, PathIn.toHistory]
        have ⟨k_val, k_pf⟩ := k
        simp [PathIn.toHistory] at k_pf
        simp_all
        rfl
      case pdl bas'' nrep'' tail' =>
        have t'_t : tail' ⋖_ tail := by simp_all
        simp only [PathIn.rewind]
        cases k using Fin.lastCases
        case last => simp
        case cast i =>
          -- TODO same lemma?
          have h : (Fin.cast (Nat.succ.inj (edge_inc_length_by_one a_b)) i.castSucc).succ
                  ≠ Fin.last (List.length (PathIn.pdl tail).toHistory) := by
            intro con
            have ⟨i_val, i_pf⟩ := i
            simp_all [Fin.last]
            simp [PathIn.toHistory] at i_pf
            have := edge_inc_length_by_one t'_t
            linarith
          rw [← Fin.exists_castSucc_eq] at h
          rcases h with ⟨k, kdef⟩
          simp only [Fin.cast_succ_eq, ← kdef, Fin.lastCases_castSucc, Function.comp_apply,
            PathIn.pdl.injEq]
          have := @IH tail' tail (Fin.cast (PathIn.pdl_length_eq tail') i) t'_t
          rcases k with ⟨k, k_lt⟩
          convert this
          simp only [Fin.cast_succ_eq, Fin.cast_cast, Fin.castSucc_mk, PathIn.pdl_length_eq,
            Nat.add_right_cancel_iff, Fin.val_succ, Fin.val_cast] at *
          cases kdef
          simp
  case lrep => cases b; simp [not_edge_nil] at a_b

-- unique existence?
theorem exists_rewind_of_le {Hist X} {tab : Tableau Hist X} {a b : PathIn tab} (h : a ≤ b) : ∃ k,
  b.rewind k = a := by
  induction h
  case refl =>
    use 0
    exact PathIn.rewind_zero
  case tail c b a_c c_b ih =>
    have ⟨k, c_re_k_is_a⟩ := ih
    use (Fin.cast (edge_inc_length_by_one c_b) (k.succ))
    have := (@rewind_helper _ _ _ c b k c_b)
    rw [c_re_k_is_a] at this
    exact this

theorem exists_rewinds_middle {Hist X} {tab : Tableau Hist X} {a b c : PathIn tab} (h : a ≤ b) (h'
  : b ≤ c) :
    ∃ k k', c.rewind k = a ∧ c.rewind k' = b ∧ k' ≤ k := by
  have ⟨k, c_re_k_is_a⟩ := exists_rewind_of_le (Relation.ReflTransGen.trans h h')
  have ⟨k', c_re_k'_is_b⟩ := exists_rewind_of_le h'
  use k
  use k'
  have k_lt_k' : k' ≤ k := by
    cases eq_or_ne c PathIn.nil
    case inl c_eq_nil =>
      subst c_eq_nil
      have hk : (k : ℕ) = 0 := by
        have := k.isLt
        simp only [PathIn.toHistory, List.length_nil, Nat.zero_add] at this
        omega
      have hk' : (k' : ℕ) = 0 := by
        have := k'.isLt
        simp only [PathIn.toHistory, List.length_nil, Nat.zero_add] at this
        omega
      simp [Fin.le_def]
    case inr c_ne_nil =>
    by_contra k_lt_k
    apply not_le.1 at k_lt_k
    have this := rewind_order_reversing_if_not_nil k_lt_k c_ne_nil
    simp_all only [ne_eq]
    apply edge.TransGen_isAsymm.1 a b ?_ this
    apply Relation.TransGen_of_ReflTransGen h
    intro con
    simp_all only
    exact path_is_irreflexive this
  simp_all

/-! ## Finiteness and Wellfoundedness -/

-- Why not in Mathlib?
-- See https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Union.20BigOperator/near/470044981
/-- The union of a finite family of finsets. -/
@[simp]
def _root_.Finset.pdlJoin [DecidableEq α] (M : Finset (Finset α)) : Finset α := M.sup id

/-- Enumerate every path in a tableau. -/
def allPaths {Hist} : (tab : Tableau Hist X) → Finset (PathIn tab)
| .loc _ _ lt next => { .nil } ∪
    (endNodesOf lt).attach.sup
      (fun Y => (allPaths (next Y.1 Y.2)).image (fun p => PathIn.loc Y.2 p))
| .pdl _ _ _ next => {.nil} ∪ (allPaths next).image (fun p => PathIn.pdl p)
| .lrep _ => { .nil }

theorem allPaths_loc_cases {Hist X} {nrep : ¬ flprep Hist X} {nbas : ¬ X.basic}
    {lt : LocalTableau X} {next : ∀ Y ∈ endNodesOf lt, Tableau (X :: Hist) Y}
    (s : PathIn (.loc nrep nbas lt next)) :
    s ∈ allPaths (.loc nrep nbas lt next) ↔
        s = PathIn.nil
      ∨ ∃ (Y : Sequent) (Y_in : Y ∈ endNodesOf lt) (t :  PathIn (next Y Y_in)),
          t ∈ allPaths (next Y Y_in) ∧
          s = PathIn.loc Y_in t := by
  constructor <;> intro hyp
  · unfold allPaths at hyp
    aesop
  · unfold allPaths
    aesop

theorem PathIn.elem_allPaths {Hist X} {tab : Tableau Hist X} (p : PathIn tab) :
    p ∈ allPaths tab := by
  induction tab
  case loc Hist X lt nexts IH =>
    induction p using init_inductionOn
    case root =>
      simp_all [allPaths]
    case step t _ s t_s =>
      rw [allPaths_loc_cases]
      cases s
      · tauto
      case loc nrep nbas Y Y_in tail =>
        right
        simp_all
  case pdl nrep bas r next =>
    cases p <;> simp_all [allPaths]
  case lrep lpr =>
    cases p
    simp_all [allPaths]

/-- A Tableau is finite.
Should be useful to get *converse* well-foundedness of `edge` -/
instance PathIn.instFintype {Hist} {tab : Tableau Hist X} : Fintype (PathIn tab) := by
  refine ⟨(allPaths tab), fun p => elem_allPaths _⟩

-- mathlib?
theorem Finite.wellfounded_of_irrefl_TC {α : Type} [Finite α] (r : α → α → Prop)
    (h : Std.Irrefl (Relation.TransGen r)) : WellFounded r :=
  let wf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen r)
  ⟨fun a => acc_transGen_iff.mp <| wf.apply a⟩

lemma nodeAt_mem_History_of_edge : p ⋖_ q → nodeAt p ∈ (tabAt q).1 := by
  rintro ( ⟨Hist, XX, nrep, nbas, lt, next, Y, Y_in, tab_def, q_def⟩
         | ⟨Hist, XX, nrep, bas, Y, r, next, tab_def, q_def⟩ )
  <;> induction p <;> (simp at tab_def; try aesop)

lemma mem_History_of_edge : p ⋖_ q → x ∈ (tabAt p).1 → x ∈ (tabAt q).1 := by
  intro hedge hmemp
  rcases hedge with ( ⟨Hist, XX, nrep, nbas, lt, next, Y, Y_in, tab_def, q_def⟩
                    | ⟨Hist, XX, nrep, bas, Y, r, next, tab_def, q_def⟩ )
  <;> induction p <;> (simp at tab_def; try aesop)

lemma mem_History_append : X ∈ (tabAt p).1 → X ∈ (tabAt (p.append q)).1 := by
  intro h
  induction q using PathIn.init_inductionOn <;> simp_all only [tabAt_append, tabAt_nil, Sigma.eta]
  apply mem_History_of_edge <;> assumption

lemma edge_TransGen_then_mem_History :
    Relation.TransGen edge p q → nodeAt p ∈ (tabAt q).1 := by
  intro h
  induction h with
  | single h => apply (nodeAt_mem_History_of_edge h)
  | tail t h ih =>
    rcases h with ⟨_, _, _, _, _, _, _, _, _, p_def⟩ | ⟨_, _, _, _, _, _, _, _, p_def⟩
    <;> subst p_def <;> apply (mem_History_append ih)

/-! ## Wellfoundedness of `flip edge`

The lemmas and instances here are used for `tabToIntAt`. -/

lemma PathIn.length_lt_tab_size {H X} (tab : Tableau H X) (p : PathIn tab) :
    p.length < tab.size := by
  induction tab
  case loc Hist X nflprep nbas lt next IH =>
    cases p
    · simp [Tableau.size]
    case loc Y nbas_ nflprep_ Y_in tail =>
      simp only [length, add_comm, Tableau.size, add_lt_add_iff_left]
      specialize IH Y Y_in tail
      refine lt_of_lt_of_le IH ?_
      exact Finset.single_le_sum (f := fun x : {x // x ∈ endNodesOf lt} => (next x.1 x.2).size)
        (fun _ _ => Nat.zero_le _) (Finset.mem_attach _ ⟨Y, Y_in⟩)
  case pdl Hist X Y nflprerp bas r next IH =>
    cases p
    · simp [Tableau.size]
    case pdl nrep bas tail =>
      simp only [length, Tableau.size]
      specialize IH tail
      grind
  · cases p
    simp [Tableau.size]

/-- The `flip edge` relation in a tableau is well-founded. -/
theorem flipEdge.wellFounded {H X} {tab : Tableau H X} :
    WellFounded (flip (@edge _ _ tab)) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  by_contra hChain
  simp only [not_isEmpty_iff, nonempty_subtype] at hChain
  rcases hChain with ⟨f, all_rel⟩
  have all_lt : ∀ (n : ℕ), (f n).length < tab.size :=
    fun n => @PathIn.length_lt_tab_size H X tab (f n)
  have increasing : ∀ (n : ℕ), (f n).length < (f (n + 1)).length :=
    fun n => edge_then_length_lt (all_rel n)
  have : ∀ n, (f (n + 1)).length > n := by
    intro n
    induction n <;> grind
  absurd this tab.size
  grind

/-- Induction principle going from the leaves (= childless nodes) to the root.
Suppose whenever the `motive` holds at all children then it holds at the parent.
Then it holds at all nodes. -/
theorem PathIn.edge_upwards_inductionOn {Hist X} {tab : Tableau Hist X}
    {motive : PathIn tab → Prop}
    (up : ∀ {u}, (∀ {s}, (u_s : u ⋖_ s) → motive s) → motive u)
    (t : PathIn tab)
    : motive t := by
  -- Doing `induction tab` as in `init_inductionOn` is not what we want here.
  apply WellFounded.induction flipEdge.wellFounded t
  intro t IH
  rcases tabT_def : (tabAt t) with ⟨H,X,tabT⟩
  cases tabT
  case loc => exact up fun {s} t_s => IH s t_s
  case pdl => exact up fun {s} t_s => IH s t_s
  case lrep =>
    apply up
    rintro s t_s
    rcases t_s with ⟨_, _, _, _, _, _, _, _, tabAt_t_eq, _⟩
                  | ⟨_, _, _, _, _, _, _, tabAt_t_eq, _⟩
    · rw [tabT_def] at tabAt_t_eq
      cases tabAt_t_eq
    · rw [tabT_def] at tabAt_t_eq
      cases tabAt_t_eq

-- not in mathlib already?
lemma Relation.TransGen_flip_iff {r : α → α → Prop} :
    Relation.TransGen (flip r) s t ↔ Relation.TransGen r t s := by
  constructor
  all_goals
    intro t_s
    induction t_s
    case single t s_t =>
      exact _root_.Relation.TransGen.single s_t
    case tail b c _ c_b b_s =>
      try simp only [flip] at c_b
      exact _root_.Relation.TransGen.trans (_root_.Relation.TransGen.single c_b) b_s

/-- Strong induction from the leaves (= childless nodes) to the root.
Suppose whenever the `motive` holds at all successors then it holds at the parent.
Then it holds at all nodes. -/
theorem PathIn.strong_upwards_inductionOn {Hist X} {tab : Tableau Hist X}
    {motive : PathIn tab → Prop}
    (ups : ∀ {u}, (∀ {s}, (u_s : u < s) → motive s) → motive u)
    (t0 : PathIn tab)
    : motive t0 := by
  have := @WellFounded.transGen _ _ (@flipEdge.wellFounded _ _ tab)
  apply WellFounded.induction this t0
  intro t IH
  rcases tabT_def : (tabAt t) with ⟨H,X,tabT⟩
  cases tabT
  case loc => exact ups fun {s} t_s => IH s (by rw [Relation.TransGen_flip_iff]; exact t_s)
  case pdl => exact ups fun {s} t_s => IH s (by rw [Relation.TransGen_flip_iff]; exact t_s)
  case lrep lpr =>
    apply ups
    rintro s t_s
    cases t_s
    case single t_s => -- easy case, like in non-strong induction
      rcases t_s with ⟨_, _, _, _, _, _, _, _, tabAt_t_eq, _⟩
                    | ⟨_, _, _, _, _, _, _, tabAt_t_eq, _⟩
      · rw [tabT_def] at tabAt_t_eq
        cases tabAt_t_eq
      · rw [tabT_def] at tabAt_t_eq
        cases tabAt_t_eq
    case tail b c t__b b_c =>
      apply IH
      rw [Relation.TransGen_flip_iff]
      exact Relation.TransGen.trans t__b (Relation.TransGen.single b_c)

end PDL
