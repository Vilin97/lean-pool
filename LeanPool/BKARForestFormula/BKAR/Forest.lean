/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Quotient
public import Mathlib.Data.Sym.Sym2

/-! # Forests on a finite vertex set

Combinatorial foundation for the BKAR forest interpolation formula (see
`BKAR.Formula`).  Defines `Edge V`, the off-diagonal unordered pairs of a
finite vertex type `V` (edges of the complete graph on `V`); simple paths
along an edge set; the acyclicity predicate `IsAcyclicEdgeSet`; the
acyclicity API `AcyclicEdgeSetData` (component relation, canonical simple
paths, path uniqueness); the index type `ForestIndex V` of acyclic edge
sets, over which the final forest sum ranges; and the working type
`Forest V`, an acyclic edge set packaged with its path API and the one-edge
extension characterization.
-/

@[expose] public section

namespace BKAR

/-- Edges of the complete graph on `V`, represented as off-diagonal unordered pairs. -/
abbrev Edge (V : Type*) : Type _ :=
  { e : Sym2 V // ¬ e.IsDiag }

noncomputable instance instFintypeEdge {V : Type*} [Fintype V] :
    Fintype (Edge V) :=
  Fintype.ofFinite (Edge V)

namespace Edge

variable {V} [DecidableEq V]

/-- The edge with endpoints `i` and `j`. -/
def mk (i j : V) (hij : i ≠ j) : Edge V :=
  ⟨Sym2.mk i j, by
    intro hdiag
    exact hij ((Sym2.mk_isDiag_iff).mp hdiag)⟩

omit [DecidableEq V] in
@[simp]
theorem mk_val (i j : V) (hij : i ≠ j) :
    (mk i j hij : Edge V).val = Sym2.mk i j :=
  rfl

omit [DecidableEq V] in
theorem not_isDiag (e : Edge V) : ¬ e.val.IsDiag :=
  e.property

/-- `e.Between i j` says that `e` is the unordered pair `{i, j}`. -/
def Between (e : Edge V) (i j : V) : Prop :=
  e.val = Sym2.mk i j

omit [DecidableEq V] in
theorem mk_between (i j : V) (hij : i ≠ j) : (mk i j hij).Between i j :=
  rfl

omit [DecidableEq V] in
theorem mk_comm (i j : V) (hij : i ≠ j) :
    mk i j hij = mk j i hij.symm := by
  apply Subtype.ext
  exact Sym2.eq_swap

/-- A fixed first endpoint of an unordered edge. -/
noncomputable def left (e : Edge V) : V :=
  e.val.out.1

/-- A fixed second endpoint of an unordered edge. -/
noncomputable def right (e : Edge V) : V :=
  e.val.out.2

omit [DecidableEq V] in
theorem mk_left_right_eq (e : Edge V) :
    Sym2.mk e.left e.right = e.val := by
  change Sym2.mk e.val.out.1 e.val.out.2 = e.val
  exact e.val.out_eq

omit [DecidableEq V] in
theorem between_left_right (e : Edge V) : e.Between e.left e.right := by
  classical
  exact
    (e.mk_left_right_eq).symm

omit [DecidableEq V] in
theorem left_ne_right (e : Edge V) : e.left ≠ e.right := by
  classical
  intro h
  exact e.property (by
    rw [← e.mk_left_right_eq]
    exact (Sym2.mk_isDiag_iff).mpr h)

omit [DecidableEq V] in
theorem not_between_self (e : Edge V) (i : V) :
    ¬ e.Between i i := by
  intro h
  exact e.property (by
    rw [Between] at h
    rw [h]
    exact (Sym2.mk_isDiag_iff).mpr rfl)

omit [DecidableEq V] in
theorem Between.symm {e : Edge V} {i j : V} (h : e.Between i j) :
    e.Between j i := by
  classical
  rw [Between] at h ⊢
  rw [h]
  exact Sym2.eq_swap

end Edge

namespace EdgePath

variable {V} [DecidableEq V]

/-- A list of edges forms an oriented walk from `i` to `j` inside `S`. -/
inductive IsPath (S : Finset (Edge V)) :
    List (Edge V) → V → V → Prop
  | nil (i : V) : IsPath S [] i i
  | cons {i j k : V} {e : Edge V} {γ : List (Edge V)} :
      e ∈ S → e.Between i j → IsPath S γ j k →
        IsPath S (e :: γ) i k

/-- A graph-level simple path: an edge walk with no repeated edges. -/
def IsSimplePath (S : Finset (Edge V))
    (γ : List (Edge V)) (i j : V) : Prop :=
  IsPath S γ i j ∧ γ.Nodup

namespace IsPath

omit [DecidableEq V] in
theorem mono {S T : Finset (Edge V)} (hsub : S ⊆ T) :
    ∀ {γ : List (Edge V)} {i j : V},
      IsPath S γ i j → IsPath T γ i j
  | [], _i, _j, h => by
      cases h
      exact IsPath.nil _
  | _e :: _γ, _i, _j, h => by
      cases h with
      | cons he hbetween htail =>
          exact IsPath.cons (hsub he) hbetween (mono hsub htail)

omit [DecidableEq V] in
theorem mono_of_forall_mem {S T : Finset (Edge V)} :
    ∀ {γ : List (Edge V)} {i j : V},
      IsPath S γ i j →
      (∀ e ∈ γ, e ∈ T) →
        IsPath T γ i j
  | [], _i, _j, hpath, _hmem => by
      cases hpath
      exact IsPath.nil _
  | e :: γ, _i, _j, hpath, hmem => by
      cases hpath with
      | cons _he hbetween htail =>
          exact IsPath.cons
            (hmem e (by simp))
            hbetween
            (mono_of_forall_mem htail
              (fun e' he' => hmem e' (by simp [he'])))

omit [DecidableEq V] in
theorem edge_mem {S : Finset (Edge V)} :
    ∀ {γ : List (Edge V)} {i j : V},
      IsPath S γ i j → ∀ e ∈ γ, e ∈ S
  | [], _i, _j, hpath, e, he => by
      cases hpath
      cases he
  | e₀ :: γ, _i, _j, hpath, e, he => by
      cases hpath with
      | cons he₀ _hbetween htail =>
          rw [List.mem_cons] at he
          exact he.elim (fun heq => heq ▸ he₀)
            (fun htail_mem => edge_mem htail e htail_mem)

omit [DecidableEq V] in
theorem append {S : Finset (Edge V)} :
    ∀ {γ₁ γ₂ : List (Edge V)} {i j k : V},
      IsPath S γ₁ i j → IsPath S γ₂ j k →
        IsPath S (γ₁ ++ γ₂) i k
  | [], _γ₂, _i, _j, _k, hnil, htail => by
      cases hnil
      exact htail
  | _e :: _γ, _γ₂, _i, _j, _k, hcons, htail₂ => by
      cases hcons with
      | cons he hbetween htail₁ =>
          exact IsPath.cons he hbetween (append htail₁ htail₂)

omit [DecidableEq V] in
theorem reverse {S : Finset (Edge V)} :
    ∀ {γ : List (Edge V)} {i j : V},
      IsPath S γ i j → IsPath S γ.reverse j i
  | [], _i, _j, hnil => by
      cases hnil
      exact IsPath.nil _
  | _e :: _γ, _i, _k, hcons => by
      cases hcons with
      | cons he hbetween htail =>
          simpa using
            append (reverse htail)
              (IsPath.cons he hbetween.symm (IsPath.nil _))

end IsPath

namespace IsSimplePath

omit [DecidableEq V] in
theorem mono {S T : Finset (Edge V)} (hsub : S ⊆ T)
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j) :
    IsSimplePath T γ i j :=
  ⟨h.1.mono hsub, h.2⟩

omit [DecidableEq V] in
theorem mono_of_forall_mem {S T : Finset (Edge V)}
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j)
    (hmem : ∀ e ∈ γ, e ∈ T) :
    IsSimplePath T γ i j :=
  ⟨h.1.mono_of_forall_mem hmem, h.2⟩

omit [DecidableEq V] in
theorem edge_mem {S : Finset (Edge V)}
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j) :
    ∀ e ∈ γ, e ∈ S :=
  h.1.edge_mem

omit [DecidableEq V] in
theorem reverse {S : Finset (Edge V)}
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j) :
    IsSimplePath S γ.reverse j i :=
  ⟨h.1.reverse, List.nodup_reverse.mpr h.2⟩

end IsSimplePath

omit [DecidableEq V] in
theorem isSimplePath_empty_iff {γ : List (Edge V)} {i j : V} :
    IsSimplePath (∅ : Finset (Edge V)) γ i j ↔ γ = [] ∧ i = j := by
  constructor
  · intro h
    cases h.1 with
    | nil i =>
        exact ⟨rfl, rfl⟩
    | cons he _hbetween _htail =>
        exact False.elim (Finset.notMem_empty _ he)
  · intro h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨IsPath.nil i, List.nodup_nil⟩

omit [DecidableEq V] in
open Classical in
theorem isPath_singleton_tail_nil {e₀ : Edge V} :
    ∀ {γ : List (Edge V)} {i j : V},
      IsSimplePath ({e₀} : Finset (Edge V)) γ i j →
      γ = [] ∨ γ = [e₀]
  | [], _i, _j, _h => Or.inl rfl
  | e :: γ, _i, _j, h => by
      cases h.1 with
      | cons he _hbetween htail =>
          have heq : e = e₀ := Finset.mem_singleton.mp he
          cases γ with
          | nil =>
              exact Or.inr (by simp [heq])
          | cons e' γ' =>
              have he'_mem : e' ∈ ({e₀} : Finset (Edge V)) :=
                htail.edge_mem e' (by simp)
              have heq' : e' = e₀ := Finset.mem_singleton.mp he'_mem
              have hnot : e ∉ e' :: γ' :=
                (List.nodup_cons.mp h.2).1
              exact False.elim (hnot (by simp [heq, heq']))

omit [DecidableEq V] in
theorem isSimplePath_singleton_iff {e₀ : Edge V}
    {γ : List (Edge V)} {i j : V} :
    IsSimplePath ({e₀} : Finset (Edge V)) γ i j ↔
      (γ = [] ∧ i = j) ∨ (γ = [e₀] ∧ e₀.Between i j) := by
  classical
  constructor
  · intro h
    rcases isPath_singleton_tail_nil h with hnil | hsingle
    · subst γ
      cases h.1
      exact Or.inl ⟨rfl, rfl⟩
    · subst γ
      cases h.1 with
      | cons he hbetween htail =>
          cases htail
          have heq : _ = e₀ := Finset.mem_singleton.mp he
          exact Or.inr ⟨rfl, heq ▸ hbetween⟩
  · intro h
    rcases h with hnil | hsingle
    · rcases hnil with ⟨rfl, rfl⟩
      exact ⟨IsPath.nil i, List.nodup_nil⟩
    · rcases hsingle with ⟨rfl, hbetween⟩
      exact
        ⟨IsPath.cons (Finset.mem_singleton_self e₀) hbetween
          (IsPath.nil j), by simp⟩

end EdgePath

/--
Data carried by an acyclic edge set.

The primitive representation is intentionally thin: later files consume the component
relation, the canonical simple path, and path uniqueness, so these are the API exposed
by the acyclicity certificate.
-/
structure AcyclicEdgeSetData {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Edge V)) where
  /-- The relation of belonging to the same connected component. -/
  inSameComponent : V → V → Prop
  /-- The predicate that an edge list is a simple path between the given vertices. -/
  isSimplePath : List (Edge V) → V → V → Prop
  /-- The canonical simple path between vertices in the same component. -/
  pathIn : (i j : V) → inSameComponent i j → List (Edge V)
  pathIn_isSimple :
    ∀ {i j : V} (h : inSameComponent i j), isSimplePath (pathIn i j h) i j
  isSimplePath_iff :
    ∀ {i j : V} {γ : List (Edge V)},
      isSimplePath γ i j ↔ EdgePath.IsSimplePath S γ i j
  sameComponent_of_simplePath :
    ∀ {i j : V} {γ : List (Edge V)}, isSimplePath γ i j → inSameComponent i j
  path_unique :
    ∀ {i j : V} {γ₁ γ₂ : List (Edge V)},
      isSimplePath γ₁ i j → isSimplePath γ₂ i j → γ₁ = γ₂
  path_edges_mem :
    ∀ {i j : V} {γ : List (Edge V)}, isSimplePath γ i j → ∀ e ∈ γ, e ∈ S
  edge_isSimplePath :
    ∀ {e : Edge V}, e ∈ S → isSimplePath [e] e.left e.right

/-- A custom acyclicity predicate for finite edge sets. -/
def IsAcyclicEdgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Edge V)) : Prop :=
  Nonempty (AcyclicEdgeSetData S)

namespace IsAcyclicEdgeSet

variable {V} [Fintype V] [DecidableEq V]

/-- Acyclicity is inherited by finite edge subsets. -/
theorem mono {S T : Finset (Edge V)}
    (hS : IsAcyclicEdgeSet S) (hsub : T ⊆ S) :
    IsAcyclicEdgeSet T := by
  classical
  rcases hS with ⟨data⟩
  refine ⟨{
    inSameComponent := fun i j =>
      ∃ γ : List (Edge V), data.isSimplePath γ i j ∧
        ∀ e ∈ γ, e ∈ T
    isSimplePath := fun γ i j =>
      data.isSimplePath γ i j ∧ ∀ e ∈ γ, e ∈ T
    pathIn := fun _ _ h => Classical.choose h
    pathIn_isSimple := ?_
    isSimplePath_iff := ?_
    sameComponent_of_simplePath := ?_
    path_unique := ?_
    path_edges_mem := ?_
    edge_isSimplePath := ?_ }⟩
  · intro i j h
    exact Classical.choose_spec h
  · intro i j γ
    constructor
    · intro hγ
      exact
        (data.isSimplePath_iff.mp hγ.1).mono_of_forall_mem hγ.2
    · intro hγ
      constructor
      · exact data.isSimplePath_iff.mpr (hγ.mono hsub)
      · exact hγ.edge_mem
  · intro i j γ hγ
    exact ⟨γ, hγ⟩
  · intro i j γ₁ γ₂ hγ₁ hγ₂
    exact data.path_unique hγ₁.1 hγ₂.1
  · intro i j γ hγ e he
    exact hγ.2 e he
  · intro e he
    constructor
    · exact data.edge_isSimplePath (hsub he)
    · intro x hx
      rw [List.mem_singleton] at hx
      exact hx ▸ he

end IsAcyclicEdgeSet

namespace AcyclicEdgeSetData

variable {V} [Fintype V] [DecidableEq V]

theorem inSameComponent_iff_exists_isSimplePath
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {i j : V} :
    data.inSameComponent i j ↔
      ∃ γ : List (Edge V), EdgePath.IsSimplePath S γ i j := by
  constructor
  · intro h
    exact ⟨data.pathIn i j h,
      data.isSimplePath_iff.mp (data.pathIn_isSimple h)⟩
  · rintro ⟨γ, hγ⟩
    exact data.sameComponent_of_simplePath
      (data.isSimplePath_iff.mpr hγ)

theorem inSameComponent_refl
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    (i : V) :
    data.inSameComponent i i := by
  rw [data.inSameComponent_iff_exists_isSimplePath]
  exact ⟨[], ⟨EdgePath.IsPath.nil i, List.nodup_nil⟩⟩

theorem inSameComponent_symm
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {i j : V} (h : data.inSameComponent i j) :
    data.inSameComponent j i := by
  rw [data.inSameComponent_iff_exists_isSimplePath] at h ⊢
  rcases h with ⟨γ, hγ⟩
  exact ⟨γ.reverse, hγ.reverse⟩

/--
Adding an absent edge whose endpoints are already connected cannot preserve
acyclicity: the old component path and the new singleton edge would be two
distinct simple paths.
-/
theorem not_isAcyclicEdgeSet_insert_of_inSameComponent
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {e : Edge V} (heS : e ∉ S)
    (hcomp : data.inSameComponent e.left e.right) :
    ¬ IsAcyclicEdgeSet (insert e S) := by
  rintro ⟨insertData⟩
  let γ := data.pathIn e.left e.right hcomp
  have hγData : data.isSimplePath γ e.left e.right :=
    data.pathIn_isSimple hcomp
  have hγGraphS : EdgePath.IsSimplePath S γ e.left e.right :=
    data.isSimplePath_iff.mp hγData
  have hγGraphInsert : EdgePath.IsSimplePath (insert e S) γ e.left e.right :=
    hγGraphS.mono (by
      intro e' he'
      exact Finset.mem_insert_of_mem he')
  have hγInsert : insertData.isSimplePath γ e.left e.right :=
    insertData.isSimplePath_iff.mpr hγGraphInsert
  have hsingle : insertData.isSimplePath [e] e.left e.right :=
    insertData.edge_isSimplePath (Finset.mem_insert_self e S)
  have heq : γ = [e] :=
    insertData.path_unique hγInsert hsingle
  have he_mem_γ : e ∈ γ := by
    rw [heq]
    simp
  have he_mem_S : e ∈ S :=
    hγGraphS.edge_mem e he_mem_γ
  exact heS he_mem_S

end AcyclicEdgeSetData

/-- The finite edge-set index over which the final BKAR forest sum ranges. -/
structure ForestIndex (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The finite acyclic edge set indexing a forest summand. -/
  edges : Finset (Edge V)
  acyclic : IsAcyclicEdgeSet edges

namespace ForestIndex

variable {V} [Fintype V] [DecidableEq V]

noncomputable instance instFintype : Fintype (ForestIndex V) := by
  classical
  letI : DecidablePred (fun S : Finset (Edge V) => IsAcyclicEdgeSet S) :=
    fun _ => Classical.propDecidable _
  let e :
      ForestIndex V ≃ {S : Finset (Edge V) // IsAcyclicEdgeSet S} := {
    toFun := fun F => ⟨F.edges, F.acyclic⟩
    invFun := fun S => ⟨S.val, S.property⟩
    left_inv := by
      intro F
      cases F
      rfl
    right_inv := by
      intro S
      cases S
      rfl }
  exact Fintype.ofEquiv {S : Finset (Edge V) // IsAcyclicEdgeSet S} e.symm

noncomputable instance instDecidableEq : DecidableEq (ForestIndex V) :=
  Classical.decEq _

@[ext]
theorem ext {I J : ForestIndex V} (h : I.edges = J.edges) : I = J := by
  cases I
  cases J
  cases h
  rfl

end ForestIndex

/-- A forest is a finite edge set with the path API needed for BKAR interpolation. -/
structure Forest (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The finite edge set of the forest. -/
  edges : Finset (Edge V)
  /-- The component and unique-path data witnessing acyclicity of the edge set. -/
  acyclic : AcyclicEdgeSetData edges
  acyclic_insert_iff' :
    ∀ {i j : V} (hij : i ≠ j), Edge.mk i j hij ∉ edges →
      (IsAcyclicEdgeSet (insert (Edge.mk i j hij) edges) ↔
        ¬ acyclic.inSameComponent i j)

namespace Forest

variable {V} [Fintype V] [DecidableEq V]

/-- Acyclicity data for the empty edge set. -/
def emptyAcyclicEdgeSetData :
    AcyclicEdgeSetData (∅ : Finset (Edge V)) where
  inSameComponent := fun i j => i = j
  isSimplePath := fun γ i j => γ = [] ∧ i = j
  pathIn := fun _ _ _ => []
  pathIn_isSimple := by
    intro i j h
    exact ⟨rfl, h⟩
  isSimplePath_iff := by
    intro i j γ
    constructor
    · intro h
      exact EdgePath.isSimplePath_empty_iff.mpr h
    · intro h
      exact EdgePath.isSimplePath_empty_iff.mp h
  sameComponent_of_simplePath := by
    intro i j γ hγ
    exact hγ.2
  path_unique := by
    intro i j γ₁ γ₂ hγ₁ hγ₂
    rw [hγ₁.1, hγ₂.1]
  path_edges_mem := by
    intro i j γ hγ e he
    rw [hγ.1] at he
    cases he
  edge_isSimplePath := by
    intro e he
    exact False.elim (Finset.notMem_empty e he)

/-- Acyclicity data for a singleton edge set. -/
def singletonAcyclicEdgeSetData (e₀ : Edge V) :
    AcyclicEdgeSetData ({e₀} : Finset (Edge V)) where
  inSameComponent := fun i j => i = j ∨ e₀.Between i j
  isSimplePath := fun γ i j =>
    (γ = [] ∧ i = j) ∨ (γ = [e₀] ∧ e₀.Between i j)
  pathIn := fun i j h =>
    if i = j then [] else [e₀]
  pathIn_isSimple := by
    intro i j h
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      exact Or.inl ⟨rfl, hij⟩
    · rw [ite_eq_right hij]
      apply Or.inr
      constructor
      · rfl
      · exact h.elim (fun heq => False.elim (hij heq)) id
  isSimplePath_iff := by
    intro i j γ
    constructor
    · intro h
      exact EdgePath.isSimplePath_singleton_iff.mpr h
    · intro h
      exact EdgePath.isSimplePath_singleton_iff.mp h
  sameComponent_of_simplePath := by
    intro i j γ hγ
    exact hγ.elim (fun hnil => Or.inl hnil.2) (fun hedge => Or.inr hedge.2)
  path_unique := by
    intro i j γ₁ γ₂ hγ₁ hγ₂
    cases hγ₁ with
    | inl hnil₁ =>
        cases hγ₂ with
        | inl hnil₂ =>
            rw [hnil₁.1, hnil₂.1]
        | inr hedge₂ =>
            have hbetween : e₀.Between j j := by
              rw [hnil₁.2] at hedge₂
              exact hedge₂.2
            exact False.elim (e₀.not_between_self j hbetween)
    | inr hedge₁ =>
        cases hγ₂ with
        | inl hnil₂ =>
            have hbetween : e₀.Between j j := by
              rw [hnil₂.2] at hedge₁
              exact hedge₁.2
            exact False.elim (e₀.not_between_self j hbetween)
        | inr hedge₂ =>
            rw [hedge₁.1, hedge₂.1]
  path_edges_mem := by
    intro i j γ hγ e he
    cases hγ with
    | inl hnil =>
        rw [hnil.1] at he
        cases he
    | inr hedge =>
        rw [hedge.1] at he
        rw [List.mem_singleton] at he
        rw [he]
        exact Finset.mem_singleton_self e₀
  edge_isSimplePath := by
    intro e he
    have heq : e = e₀ := Finset.mem_singleton.mp he
    rw [heq]
    exact Or.inr ⟨rfl, e₀.between_left_right⟩

/-- The empty forest, with equality as its component relation. -/
def empty (V : Type*) [Fintype V] [DecidableEq V] : Forest V where
  edges := ∅
  acyclic := emptyAcyclicEdgeSetData
  acyclic_insert_iff' := by
    intro i j hij he
    constructor
    · intro _ hcomp
      exact hij hcomp
    · intro _
      change IsAcyclicEdgeSet ({Edge.mk i j hij} : Finset (Edge V))
      exact ⟨singletonAcyclicEdgeSetData (Edge.mk i j hij)⟩

theorem empty_edges (V : Type*) [Fintype V] [DecidableEq V] :
    (empty V).edges = ∅ :=
  rfl

theorem isAcyclicEdgeSet (F : Forest V) : IsAcyclicEdgeSet F.edges :=
  ⟨F.acyclic⟩

/-- Forget the path data of a `Forest` representative, retaining only its finite edge-set index. -/
def support (F : Forest V) : ForestIndex V where
  edges := F.edges
  acyclic := F.isAcyclicEdgeSet

theorem support_edges (F : Forest V) :
    F.support.edges = F.edges :=
  rfl

theorem empty_support :
    (empty V).support = ⟨∅, ⟨emptyAcyclicEdgeSetData⟩⟩ := by
  rfl

/-- The component relation of a forest. -/
def inSameComponent (F : Forest V) (i j : V) : Prop :=
  F.acyclic.inSameComponent i j

theorem empty_inSameComponent_iff {i j : V} :
    (empty V).inSameComponent i j ↔ i = j :=
  Iff.rfl

noncomputable instance instDecidableInSameComponent (F : Forest V) (i j : V) :
    Decidable (F.inSameComponent i j) :=
  Classical.propDecidable _

/-- The canonical path between vertices known to be in the same component. -/
def pathInF (F : Forest V) (i j : V) (h : F.inSameComponent i j) :
    List (Edge V) :=
  F.acyclic.pathIn i j h

end Forest

/-- Simple paths in a forest, as exposed by its acyclicity certificate. -/
def IsSimplePath {V : Type*} [Fintype V] [DecidableEq V]
    (F : Forest V) (γ : List (Edge V)) (i j : V) : Prop :=
  F.acyclic.isSimplePath γ i j

namespace Forest

variable {V} [Fintype V] [DecidableEq V]

theorem pathInF_isSimple (F : Forest V) {i j : V}
    (h : F.inSameComponent i j) :
    IsSimplePath F (F.pathInF i j h) i j :=
  F.acyclic.pathIn_isSimple h

theorem inSameComponent_of_isSimplePath (F : Forest V) {i j : V}
    {γ : List (Edge V)} (hγ : IsSimplePath F γ i j) :
    F.inSameComponent i j :=
  F.acyclic.sameComponent_of_simplePath hγ

theorem edge_mem_of_isSimplePath (F : Forest V) {i j : V}
    {γ : List (Edge V)} (hγ : IsSimplePath F γ i j) :
    ∀ e ∈ γ, e ∈ F.edges :=
  F.acyclic.path_edges_mem hγ

theorem edge_isSimplePath (F : Forest V) {e : Edge V} (he : e ∈ F.edges) :
    IsSimplePath F [e] e.left e.right :=
  F.acyclic.edge_isSimplePath he

theorem edge_inSameComponent (F : Forest V) {e : Edge V} (he : e ∈ F.edges) :
    F.inSameComponent e.left e.right :=
  F.inSameComponent_of_isSimplePath (F.edge_isSimplePath he)

/-- Lemma A1: the simple path in a forest is unique. -/
theorem pathInF_unique (F : Forest V) {i j : V}
    (h : F.inSameComponent i j) (γ : List (Edge V))
    (hγ : IsSimplePath F γ i j) :
    γ = F.pathInF i j h :=
  F.acyclic.path_unique hγ (F.pathInF_isSimple h)

theorem pathInF_eq_singleton_of_edge_mem (F : Forest V) {e : Edge V}
    (he : e ∈ F.edges) :
    F.pathInF e.left e.right (F.edge_inSameComponent he) = [e] :=
  (F.pathInF_unique (F.edge_inSameComponent he) [e] (F.edge_isSimplePath he)).symm

/-- Simple paths are invariant under replacing the `Forest` representative data by another
forest with the same underlying edge set. -/
theorem isSimplePath_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    {γ : List (Edge V)} {i j : V}
    (hγ : IsSimplePath F γ i j) :
    IsSimplePath G γ i j := by
  rw [IsSimplePath]
  rw [G.acyclic.isSimplePath_iff]
  rw [← hedges]
  exact F.acyclic.isSimplePath_iff.mp hγ

/-- The component relation is invariant under changing only the auxiliary path data. -/
theorem inSameComponent_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    {i j : V} (h : F.inSameComponent i j) :
    G.inSameComponent i j :=
  G.inSameComponent_of_isSimplePath
    (F.isSimplePath_of_edges_eq G hedges (F.pathInF_isSimple h))

theorem inSameComponent_iff_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    {i j : V} :
    F.inSameComponent i j ↔ G.inSameComponent i j :=
  ⟨F.inSameComponent_of_edges_eq G hedges,
    G.inSameComponent_of_edges_eq F hedges.symm⟩

/--
Canonical paths are invariant under changing only the `Forest` representative data, once
the underlying edge set is fixed.
-/
theorem pathInF_eq_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    {i j : V} (hF : F.inSameComponent i j)
    (hG : G.inSameComponent i j) :
    F.pathInF i j hF = G.pathInF i j hG := by
  symm
  exact F.pathInF_unique hF (G.pathInF i j hG)
    (G.isSimplePath_of_edges_eq F hedges.symm (G.pathInF_isSimple hG))

/-- Lemma A2: adding an absent edge preserves acyclicity exactly across components. -/
theorem acyclic_insert_iff (F : Forest V) {i j : V} (hij : i ≠ j)
    (he : Edge.mk i j hij ∉ F.edges) :
    IsAcyclicEdgeSet (insert (Edge.mk i j hij) F.edges) ↔
      ¬ F.inSameComponent i j :=
  show IsAcyclicEdgeSet (insert (Edge.mk i j hij) F.edges) ↔
      ¬ F.acyclic.inSameComponent i j from
    F.acyclic_insert_iff' (i := i) (j := j) hij he

/--
Certificate that `F'` is obtained from `F` by adding one edge and that the canonical
paths behave as expected under this extension.
-/
structure EdgeExtension (F F' : Forest V) (e₀ : Edge V) where
  new_not_mem : e₀ ∉ F.edges
  edges_eq : F'.edges = insert e₀ F.edges
  old_component :
    ∀ {i j : V}, F.inSameComponent i j → F'.inSameComponent i j
  old_path :
    ∀ {i j : V} (h : F.inSameComponent i j),
      F'.pathInF i j (old_component h) = F.pathInF i j h
  new_path_uses :
    ∀ {i j : V} (_ : ¬ F.inSameComponent i j)
      (hF' : F'.inSameComponent i j), e₀ ∈ F'.pathInF i j hF'

namespace EdgeExtension

variable {F F' : Forest V} {e₀ e : Edge V}

theorem new_mem (h : EdgeExtension F F' e₀) : e₀ ∈ F'.edges := by
  rw [h.edges_eq]
  exact Finset.mem_insert_self e₀ F.edges

theorem old_mem (h : EdgeExtension F F' e₀) (he : e ∈ F.edges) :
    e ∈ F'.edges := by
  rw [h.edges_eq]
  exact Finset.mem_insert_of_mem he

theorem mem_old_of_mem_of_ne (h : EdgeExtension F F' e₀)
    (he : e ∈ F'.edges) (hne : e ≠ e₀) : e ∈ F.edges := by
  have hmem : e ∈ insert e₀ F.edges := by
    rw [← h.edges_eq]
    exact he
  rw [Finset.mem_insert] at hmem
  exact hmem.elim (fun heq => False.elim (hne heq)) id

end EdgeExtension

end Forest

namespace ForestIndex

variable {V} [Fintype V] [DecidableEq V]

/-- The finite forest index consisting of one edge. -/
def singleton (e : Edge V) : ForestIndex V where
  edges := {e}
  acyclic := ⟨Forest.singletonAcyclicEdgeSetData e⟩

theorem singleton_edges (e : Edge V) :
    (singleton e : ForestIndex V).edges = {e} :=
  rfl

end ForestIndex

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
