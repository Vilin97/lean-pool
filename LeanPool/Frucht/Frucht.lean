/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Tactic.NormNum
import LeanPool.Frucht.SetTheory
import LeanPool.Frucht.Graphs

/-!
# Frucht's theorem, choice-free

Assembles the canonical pointed graphs and Cayley colored graphs into the main
results: a strong form of Frucht's theorem that every group is isomorphic to the
automorphism group of a simple graph, derived from the axiom of choice and, more
finely, from foundation and the `FAFA₂` set-theoretic rigidity hypothesis.
-/

noncomputable section
universe u v

open Function Relation Cardinal

@[classical] def top (x : Type u) := castMem (trcl_singleton_contains_self (x := x))

@[classical] def canonicalGraph (α : Type u) : PointedGraph (trcl {α}) where
  p := top α
  r := fun x y => (y : Type u) ∈ (x : Type u)

@[classical] def FAFA₂On (M : Set (Type u)) :=
  ∀ α ∈ M, ∀ β ∈ M, canonicalGraph α ≃· canonicalGraph β → α = β

namespace canonicalGraph

open PointedGraph

variable {x y : Type u} (f : canonicalGraph x ≃· canonicalGraph y) (a b : trcl {x})

@[classical] lemma p_eq : (canonicalGraph x).p = top x := rfl

@[classical] lemma reachable_iff :
    ReflTransGen (canonicalGraph x).r a b ↔ ↑b ∈ trcl {↑a} := by
  rw [mem_trcl_singleton_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · apply ReflTransGen.swap
    refine ReflTransGen.lift _ ?_ h
    simp [canonicalGraph]
  · replace h := h.swap
    refine ReflTransGen.liftInjective elements_inj ?_ ?_ h
    · simp [canonicalGraph]
    · simpa only [← mem_def, swap] using fun _ _ => trcl_singleton_trans_of_mem

@[classical] def isoInduce (hy : y ∈ trcl {x}) :
    canonicalGraph y ≃· (canonicalGraph x).induce (castMem hy) where
  toFun := fun z => ⟨
    castMem (trcl_singleton_trans (elements_mem z) hy),
    by simpa [reachable_iff] using elements_mem _
  ⟩
  invFun := fun ⟨z, hz⟩ => by
    simp only [reachable_iff, elements_cast] at hz
    exact castMem hz
  map_point' := by simp +instances [induce, p_eq, top]
  left_inv := by simp [LeftInverse]
  right_inv := by simp [RightInverse, LeftInverse]
  map_rel_iff' := by simp +instances [induce, canonicalGraph]

@[classical] def isoInduceElement : canonicalGraph ↑a ≃· (canonicalGraph x).induce a := by
  convert isoInduce (elements_mem a) <;> simp

@[classical] def move (a : x) : y := by
  let a' := moveSub sub_trcl_singleton a
  have : ↑(f a') ∈ y := by
    suffices (canonicalGraph y).r (top y) (f a') by
      simpa [canonicalGraph, top] using this
    rw [← p_eq, ← f.map_point, f.map_rel_iff, p_eq]
    simp [canonicalGraph, top, a', moveSub, elements_mem]
  exact castMem this

@[classical] def moveIso (a : x) : canonicalGraph ↑a ≃· canonicalGraph ↑(move f a) :=
  let a' := moveSub sub_trcl_singleton a
  calc
    _ ≃· canonicalGraph ↑a' := by
      convert PointedGraphIso.refl (G := canonicalGraph ↑a)
      · simp [a']
      · congr 1; simp [a']
    _ ≃· (canonicalGraph x).induce a' := by
      convert isoInduce (elements_mem _) <;> simp
    _ ≃· (canonicalGraph y).induce (f a') := by
      apply induceIso
    _ ≃· canonicalGraph ↑(f a') := by
      convert isoInduce (elements_mem _) |>.symm <;> simp
    _ ≃· _ := by
      convert PointedGraphIso.refl (G := canonicalGraph ↑(f a'))
      · simp [move, a']
      · congr 1; simp [move, a']

@[classical] lemma is_rigid
    {M : Set (Type u)} (hfafa : FAFA₂On M) (htrans : TransitiveClass M) (hx : x ∈ M) :
    (canonicalGraph x).Rigid := by
  refine @Unique.instSubsingleton _ ⟨⟨.refl⟩, ?_⟩
  intro f
  ext a
  change f a = a
  have := calc
    _ ≃· _ := isoInduceElement a
    _ ≃· _ := induceIso f a
    _ ≃· _ := isoInduceElement (f a) |>.symm
  exact (elements_inj <| hfafa
    _ (mem_transitive htrans hx (elements_mem a))
    _ (mem_transitive htrans hx (elements_mem (f a))) this) |>.symm

end canonicalGraph

open canonicalGraph in
@[classical] theorem fafa₂_on_wf : FAFA₂On WF := by
  intro x hx y hy f
  clear hy
  induction hx generalizing y with
  | @intro x hx ih =>
    ext z
    refine ⟨fun hz => ?_, fun hz => ?_⟩
    · have := ih _ hz _ (elements_cast _ ▸ moveIso f (castMem hz))
      exact this ▸ elements_mem _
    · have := ih _ (elements_mem _) _ (moveIso f.symm (castMem hz)).symm
      simp only [elements_cast] at this
      exact this ▸ elements_mem _

@[classical] class HasEnoughPointedGraph (α : Type u) where
  S : Set (Sigma PointedGraph.{u})
  equiv : α ≃ S
  all_rigid : S ⊆ {G | G.2.Rigid}
  not_isomorphic : S.Pairwise fun G H => IsEmpty (G.2 ≃· H.2)

@[classical, reducible] def instHasEnoughPointedGraph
    {M : Set (Type u)} (hfafa : FAFA₂On M) (htrans : TransitiveClass M) {α} (hα : α ∈ M) :
    HasEnoughPointedGraph α := by
  let f (x : α) := Sigma.mk _ (canonicalGraph (x : Type u))
  refine ⟨_, Equiv.ofInjective' f ?_, ?_, ?_⟩
  · intro x y eq
    simp only [Sigma.mk.injEq, f] at eq
    let φ {α : Type u} (G : PointedGraph α) : Type u := G.p
    have : φ (canonicalGraph x) = φ (canonicalGraph y) := by
      congr 1 <;> simp [eq]
    simp only [canonicalGraph, top, elements_cast, φ] at this
    exact elements_inj this
  · intro G hG
    obtain ⟨x, hx⟩ := hG
    rw [← hx]
    exact canonicalGraph.is_rigid hfafa htrans (htrans _ hα _ (elements_mem _))
  · refine fun x hx y hy ne => ⟨fun iso => ?_⟩
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    rw [← hx', ← hy'] at iso
    absurd ne
    suffices x' = y' by ext1 <;> rw [← hx', ← hy', this]
    refine elements_inj (hfafa _ ?_ _ ?_ iso)
    · refine htrans _ hα _ (elements_mem _)
    · refine htrans _ hα _ (elements_mem _)

@[classical, reducible] def instHasEnoughPointedGraphFromEquiv
    {α β} [A : HasEnoughPointedGraph α] (f : α ≃ β) : HasEnoughPointedGraph β where
  S := A.S
  equiv := f.symm.trans A.equiv
  all_rigid := A.all_rigid
  not_isomorphic := A.not_isomorphic

@[classical] class HasEnoughRCPG (α : Type u) where
  S : Set (Sigma RCPG.{u})
  equiv : α ≃ S
  nontrivial : ∀ G ∈ S, Nontrivial G.1
  not_isomorphic : S.Pairwise fun G H => IsEmpty (G.2 ≃p H.2)

namespace RCPG

open SimpleGraph

variable (m n : ℕ) [NeZero m] [NeZero n]

@[classical] def path : RCPG (Fin n) :=
  { pathGraph n with
    p := 0
    is_rigid' := @Unique.instSubsingleton _
      ⟨⟨⟨.refl, rfl⟩⟩, fun | ⟨f, hf⟩ => Subtype.val_inj.mp (pathGraph_rigid f hf)⟩
    is_connected := by
      obtain ⟨m, ⟨_⟩⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
      exact pathGraph_connected _ }

@[classical] lemma path_not_isomorphic (ne : m ≠ n) : IsEmpty (path m ≃p path n) :=
  ⟨fun e => ne (Fin.equiv_iff_eq.mp ⟨e.toEquiv⟩)⟩

instance : HasEnoughRCPG Bool where
  S := _
  equiv := Equiv.ofInjective'
    (fun | false => ⟨_, path 2⟩ | true => ⟨_, path 3⟩)
    (by simpa using fun h => absurd (Fin.equiv_iff_eq.mp ⟨Equiv.cast h⟩) (by simp))
  nontrivial := by
    simp only [Bool.range_eq, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq]
    constructor <;> infer_instance
  not_isomorphic := by simp [Set.Pairwise, path_not_isomorphic]

end RCPG

namespace HasEnoughRCPG

variable {C} [HasEnoughRCPG C] (u v : C)

@[classical] def type : Type u := (equiv u).1.1
@[classical] def rcpgOfColor : RCPG (type u) := (equiv u).1.2
@[classical] def graph : SimpleGraph (type u) := (rcpgOfColor u).toSimpleGraph
@[classical] def point : type u := (rcpgOfColor u).p
@[classical] lemma graph_connected : (graph u).Connected := (rcpgOfColor u).is_connected
@[classical] instance : Nontrivial (type u) := nontrivial (equiv u).1 (equiv u).2

variable {u v}

@[classical] lemma color_eq_of_iso (f : rcpgOfColor u ≃p rcpgOfColor v) : u = v := by
  by_contra ne
  exact not_isomorphic (equiv u).2 (equiv v).2
    (Subtype.val_inj.not.mpr (equiv.injective.ne ne)) |>.false f

end HasEnoughRCPG

open HasEnoughRCPG

namespace ColoredGraph

variable {α : Type u} {C : Type v} [HasEnoughRCPG C] (G : ColoredGraph α C)

@[classical] inductive RCPGPoints : Type _
  | o (x : α)
  | a (x y : α)
  | b (x y : α)
  | c (x y : α) (u : type (G x y))
  | l (x y : α) (u : type (G x y))

section ImplicitArgument

variable {G} (q : RCPGPoints G)

namespace RCPGPoints

@[classical] abbrev p (x y : α) := c x y (point (G x y))
@[classical] instance instNontrivial [ne : Nonempty α] : Nontrivial G.RCPGPoints := by
  obtain ⟨x⟩ := ne
  refine ⟨a x x, .b x x, by simp⟩

@[classical] def Is_o := ∃ x, o x = q
@[classical] def Is_a := ∃ x y, a x y = q
@[classical] def Is_b := ∃ x y, b x y = q
@[classical] def Is_c := ∃ x y u, c x y u = q
@[classical] def Is_l := ∃ x y u, l x y u = q
@[classical] def Is_p := ∃ x y, p x y = q

end RCPGPoints

@[classical] inductive RCPGRelation : G.RCPGPoints → G.RCPGPoints → Prop
  | roa (x y) : RCPGRelation (.o x) (.a x y)
  | rao (x y) : RCPGRelation (.a x y) (.o x)
  | rab (x y) : RCPGRelation (.a x y) (.b x y)
  | rba (x y) : RCPGRelation (.b x y) (.a x y)
  | rap (x y) : RCPGRelation (.a x y) (.p x y)
  | rpa (x y) : RCPGRelation (.p x y) (.a x y)
  | rpo (x y) : RCPGRelation (.p x y) (.o y)
  | rop (x y) : RCPGRelation (.o y) (.p x y)
  | rcl (x y u) : RCPGRelation (.c x y u) (.l x y u)
  | rlc (x y u) : RCPGRelation (.l x y u) (.c x y u)
  | rcc (x y u v) (hzw : (graph (G x y)).Adj u v) : RCPGRelation (.c x y u) (.c x y v)

end ImplicitArgument

@[classical] def elimColor : SimpleGraph G.RCPGPoints where
  Adj := RCPGRelation
  symm := by
    intro x y r
    cases r <;> constructor
    rename_i x y a b hab
    exact hab.symm
  loopless := by
    refine ⟨fun x hx => ?_⟩
    cases hx
    rename_i x y a ha
    exact (graph (G _ _)).loopless.irrefl _ ha

end ColoredGraph

namespace ColoredGraphIso

open ColoredGraph

variable {α β C} [HasEnoughRCPG C] {G : ColoredGraph α C} {H : ColoredGraph β C} (f : G ≃c H)

@[classical] def toElimColorMap : G.RCPGPoints → H.RCPGPoints
  | .o x => .o (f x)
  | .a x y => .a (f x) (f y)
  | .b x y => .b (f x) (f y)
  | .c x y u => .c (f x) (f y) (congr_arg type f.map_color ▸ u)
  | .l x y u => .l (f x) (f y) (congr_arg type f.map_color ▸ u)

@[classical] def toElimColorEquiv : G.RCPGPoints ≃ H.RCPGPoints where
  toFun := toElimColorMap f
  invFun := toElimColorMap f.symm
  left_inv := by rintro ⟨_⟩ <;> simp [toElimColorMap]
  right_inv := by rintro ⟨_⟩ <;> simp [toElimColorMap, apply_symm_apply]

@[classical] lemma toElimColorMap_adj_iff {p q : G.RCPGPoints} (adj : G.elimColor.Adj p q) :
    H.elimColor.Adj (f.toElimColorMap p) (f.toElimColorMap q) := by
  simp only [ColoredGraph.elimColor]
  cases adj with
  | roa x y => constructor
  | rao x y => constructor
  | rab x y => constructor
  | rba x y => constructor
  | rap x y =>
    simp only [toElimColorMap]
    convert RCPGRelation.rap (f x) (f y) using 2
    rw [eqRec_eq_cast, cast_eq_iff_heq, ← f.map_color]
  | rpa x y =>
    simp only [toElimColorMap]
    convert RCPGRelation.rpa (f x) (f y) using 2
    rw [eqRec_eq_cast, cast_eq_iff_heq, ← f.map_color]
  | rpo x y =>
    simp only [toElimColorMap]
    convert RCPGRelation.rpo (f x) (f y) using 2
    rw [eqRec_eq_cast, cast_eq_iff_heq, ← f.map_color]
  | rop x y =>
    simp only [toElimColorMap]
    convert RCPGRelation.rop (f x) (f y) using 2
    rw [eqRec_eq_cast, cast_eq_iff_heq, ← f.map_color]
  | rcl x y u => constructor
  | rlc x y u => constructor
  | rcc x y u v adj =>
    constructor
    convert adj
    rw [← propext_iff]
    congr 1 <;> first | rw [← f.map_color] | simp

@[classical] def toElimColorIso : G.elimColor ≃g H.elimColor :=
  { toElimColorEquiv f with
    map_rel_iff' := by
      refine fun {a b} => ⟨fun h => ?_, fun h => ?_⟩
      · convert f.symm.toElimColorMap_adj_iff h
        · exact (f.toElimColorEquiv.left_inv a).symm
        · exact (f.toElimColorEquiv.left_inv b).symm
      · exact f.toElimColorMap_adj_iff h }

end ColoredGraphIso

namespace ColoredGraph

open SimpleGraph

variable {α β γ : Type u} {C : Type v} [HasEnoughRCPG C]
    {G : ColoredGraph α C} {H : ColoredGraph β C} {I : ColoredGraph γ C}
    (f : G.elimColor ≃g H.elimColor) (g : H.elimColor ≃g I.elimColor)
    {p : G.RCPGPoints} (x₀ x y : α) (u : type (G x y))

@[classical] lemma is_leaf_iff : G.elimColor.IsLeaf p ↔ p.Is_b ∨ p.Is_l := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · cases p with
    | o x => exact False.elim ((by simp : ¬_)
        (hp.unique (y₁ := .a x x) (y₂ := .p x x) (by constructor) (by constructor)))
    | a x y => exact False.elim ((by simp : ¬_)
        (hp.unique (y₁ := .b x y) (y₂ := .o x) (by constructor) (by constructor)))
    | b x y => repeat constructor
    | c x y u =>
      obtain ⟨v, hv⟩ := (graph (G x y)).connected_exists_edge (graph_connected _) u
      exact False.elim ((by simp : ¬_)
        (hp.unique (y₁ := .c x y v) (y₂ := .l x y u) (by constructor; exact hv) (by constructor)))
    | l x y u => right; repeat constructor
  · rcases hp with ⟨x, y, hp⟩ | ⟨x, y, u, hp⟩
    · cases hp
      refine ⟨.a x y, by constructor, fun q hq => ?_⟩
      cases hq
      rfl
    · cases hp
      refine ⟨.c x y u, by constructor, fun q hq => ?_⟩
      cases hq
      rfl

@[classical] lemma is_o_iff :
    p.Is_o ↔ ¬G.elimColor.IsLeaf p ∧ ¬∃ x ∈ G.elimColor.neighborSet p, G.elimColor.IsLeaf x := by
  simp only [is_leaf_iff]
  refine ⟨fun hp => ⟨?_, ?_⟩, fun | ⟨hp, hp'⟩ => ?_⟩
  · obtain ⟨x, ⟨_⟩⟩ := hp
    rintro (⟨y, z, ⟨_⟩⟩ | ⟨y, z, u, ⟨_⟩⟩)
  · obtain ⟨x, ⟨_⟩⟩ := hp
    rintro ⟨p, ⟨_⟩, ⟨y, z, ⟨_⟩⟩ | ⟨y, z, u, ⟨_⟩⟩⟩
  · cases p with
    | o x => repeat constructor
    | a x y => exact (hp' ⟨.b x y, by constructor, by repeat constructor⟩).elim
    | b x y => refine (hp (by repeat constructor)).elim
    | c x y u => exact (hp' ⟨.l x y u, by constructor, by right; repeat constructor⟩).elim
    | l x y u => exact (hp (by right; repeat constructor)).elim

@[classical] lemma is_neighbor_original_iff :
    (∃ q ∈ G.elimColor.neighborSet p, q.Is_o) ↔ p.Is_a ∨ p.Is_p := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨_, ⟨_⟩, ⟨_, ⟨_⟩⟩⟩
    · repeat constructor
    · right; repeat constructor
  · rcases h with ⟨x, y, ⟨_⟩⟩ | ⟨x, y, ⟨_⟩⟩
    · use .o x; repeat constructor
    · use .o y; repeat constructor

@[classical] lemma card_neighborSet_a (hp : p.Is_a) : #(G.elimColor.neighborSet p) = 3 := by
  obtain ⟨x, y, hxy⟩ := hp
  transitivity #({.o x, .b x y, .p x y} : Set G.RCPGPoints)
  · congr 2
    ext q
    subst hxy
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h <;> simp
    · rcases h with ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ <;> constructor
  · repeat rw [mk_insert]
    · rw [mk_singleton]
      norm_num
    · simp
    · simp

@[classical] lemma card_neighborSet_p (hp : p.Is_p) : 4 ≤ #(G.elimColor.neighborSet p) := by
  obtain ⟨x, y, hxy⟩ := hp
  obtain ⟨u, hu⟩ := (graph (G x y)).connected_exists_edge (graph_connected _) (point (G x y))
  transitivity #({.a x y, .o y, .l x y (point (G x y)), .c x y u} : Set G.RCPGPoints)
  · repeat rw [mk_insert]
    · rw [mk_singleton]
      norm_num
    · simp
    · simp
    · simp
  · apply mk_le_mk_of_subset
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    cases hxy
    rcases hq with ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ <;> constructor
    exact hu

@[classical] lemma is_a_iff :
    p.Is_a ↔ (∃ q ∈ G.elimColor.neighborSet p, q.Is_o) ∧ #(G.elimColor.neighborSet p) = 3 := by
  rw [is_neighbor_original_iff]
  refine ⟨fun h => ⟨.inl h, ?_⟩, fun | ⟨or, h⟩ => or.resolve_right ?_⟩
  · exact card_neighborSet_a h
  · intro hp
    have := h ▸ card_neighborSet_p hp
    norm_num at this

@[classical] lemma is_p_iff :
    p.Is_p ↔ (∃ q ∈ G.elimColor.neighborSet p, q.Is_o) ∧ #(G.elimColor.neighborSet p) ≠ 3 := by
  rw [is_neighbor_original_iff]
  refine ⟨fun h => ⟨.inr h, ?_⟩, fun | ⟨or, h⟩ => or.resolve_left ?_⟩
  · intro hp
    have := is_a_iff.mpr ⟨is_neighbor_original_iff.mpr (.inr h), hp⟩
    rcases h with ⟨x, y, ⟨_⟩⟩
    rcases this with ⟨x, y, ⟨_⟩⟩
  · contrapose! h
    exact card_neighborSet_a h

@[classical] lemma iso_o : p.Is_o ↔ (f p).Is_o := by
  rw [is_o_iff, is_o_iff, ← propext_iff]
  congr 2
  · rw [f.map_leaf]
  · rw [eq_comm, propext_iff, Set.BijOn.exists (f.map_neighborSet p)]
    congr! 3 with q
    simp [f.map_leaf]

@[classical] lemma iso_a : p.Is_a ↔ (f p).Is_a := by
  rw [is_a_iff, is_a_iff, ← propext_iff]
  congr 1
  · rw [Set.BijOn.exists (f.map_neighborSet p)]
    congr! 3 with q
    rw [iso_o]
  · congr 1
    rw [(f.mapNeighborSet _).cardinal_eq]

@[classical] lemma iso_p : p.Is_p ↔ (f p).Is_p := by
  rw [is_p_iff, is_p_iff, ← propext_iff]
  congr 1
  · rw [Set.BijOn.exists (f.map_neighborSet p)]
    congr! 3 with q
    rw [iso_o]
  · congr 1
    rw [(f.mapNeighborSet _).cardinal_eq]

@[classical] lemma is_b_iff :
    p.Is_b ↔ G.elimColor.IsLeaf p ∧ ∃ q ∈ G.elimColor.neighborSet p, q.Is_a := by
  rw [is_leaf_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨.inl h, ?_⟩
    rcases h with ⟨x, y, ⟨_⟩⟩
    refine ⟨.a x y, ?_⟩
    repeat constructor
  · refine h.1.resolve_right ?_
    rintro ⟨x, y, u, ⟨_⟩⟩
    rcases h with ⟨-, q, ⟨_⟩, ⟨x, y, ⟨_⟩⟩⟩

@[classical] lemma iso_b : p.Is_b ↔ (f p).Is_b := by
  rw [is_b_iff, is_b_iff, ← propext_iff]
  congr 1
  · rw [f.map_leaf]
  · rw [Set.BijOn.exists (f.map_neighborSet p)]
    congr! 3 with q
    rw [iso_a]

@[classical] lemma is_cl_iff : p.Is_c ∨ p.Is_l ↔ ¬p.Is_o ∧ ¬p.Is_a ∧ ¬p.Is_b := by
  cases p <;>
    simp [RCPGPoints.Is_o, RCPGPoints.Is_a, RCPGPoints.Is_b, RCPGPoints.Is_c, RCPGPoints.Is_l]

@[classical] lemma is_c_iff : p.Is_c ↔ ¬G.elimColor.IsLeaf p ∧ ¬p.Is_o ∧ ¬p.Is_a ∧ ¬p.Is_b := by
  rw [← is_cl_iff, is_leaf_iff]
  cases p <;> simp [RCPGPoints.Is_b, RCPGPoints.Is_c, RCPGPoints.Is_l]

@[classical] lemma is_l_iff : p.Is_l ↔ G.elimColor.IsLeaf p ∧ ¬p.Is_o ∧ ¬p.Is_a ∧ ¬p.Is_b := by
  rw [← is_cl_iff, is_leaf_iff]
  cases p <;> simp [RCPGPoints.Is_b, RCPGPoints.Is_c, RCPGPoints.Is_l]

@[classical] lemma iso_c : p.Is_c ↔ (f p).Is_c := by
  rw [is_c_iff, is_c_iff]
  congr! 3
  · rw [f.map_leaf]
  · rw [iso_o]
  · rw [iso_a]
  · rw [iso_b]

@[classical] lemma iso_l : p.Is_l ↔ (f p).Is_l := by
  rw [is_l_iff, is_l_iff]
  congr! 3
  · rw [f.map_leaf]
  · rw [iso_o]
  · rw [iso_a]
  · rw [iso_b]

@[classical] def colorSet : Set G.RCPGPoints :=
  {q | ∃ w : G.elimColor.Walk q (.p x y), ∀ r ∈ w.support, r.Is_c}

@[classical] def colorSet_p : G.colorSet x y := ⟨.p x y, .nil, by simp [RCPGPoints.Is_c]⟩

@[classical] lemma colorSet_eq : G.colorSet x y = Set.range (.c x y) := by
  ext p
  refine ⟨?_, fun | ⟨u, hu⟩ => ?_⟩
  · simp only [colorSet, Set.mem_setOf_eq, forall_exists_index]
    set q := (.p x y : G.RCPGPoints) with hq
    clear_value q
    intro w hw
    induction w with
    | @nil u => simp [hq]
    | @cons r s t adj w ih =>
      cases hq
      simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp] at hw
      specialize ih rfl hw.2
      replace hw := hw.1
      rcases ih with ⟨u, ⟨_⟩⟩
      rcases hw with ⟨x', y', u', ⟨_⟩⟩
      cases adj
      simp
  · subst hu
    obtain ⟨w, -⟩ := (graph_connected (G x y)).exists_walk_length_eq_edist (point (G x y)) u
    replace w := w.reverse
    revert u
    set p := point (G x y) with hp
    clear_value p
    intro u w
    induction w with
    | @nil p =>
      cases hp
      exact (G.colorSet_p x y).2
    | @cons u v p adj w ih =>
      cases hp
      specialize ih rfl
      obtain ⟨w', hw'⟩ := ih
      use .cons (.rcc _ _ _ _ adj) w'
      simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp]
      refine ⟨by simp [RCPGPoints.Is_c], hw'⟩

@[classical] def typeEquivColorSet : type (G x y) ≃ G.colorSet x y :=
  Equiv.ofBijective'
    (fun u => ⟨.c x y u, by simp [colorSet_eq]⟩)
    ⟨by simp [Injective], by simp [Surjective, colorSet_eq]⟩

@[classical] def graphIso : graph (G x y) ≃g G.elimColor.induce (G.colorSet x y) where
  __ := G.typeEquivColorSet x y
  map_rel_iff' := by
    intro u v
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h; assumption
    · constructor; assumption

@[classical] lemma graphIso_map_point : G.graphIso x y (point (G x y)) = G.colorSet_p x y := rfl

@[classical] def colorRCPG : RCPG (G.colorSet x y) :=
  { G.elimColor.induce (G.colorSet x y) with
    p := G.colorSet_p x y
    is_rigid' := by
      refine ⟨fun | ⟨f, hf⟩, ⟨g, hg⟩ => ?_⟩
      let φ := G.graphIso x y
      let f' := φ |>.trans f |>.trans φ.symm
      let g' := φ |>.trans g |>.trans φ.symm
      have := (rcpgOfColor (G x y)).is_rigid.allEq ⟨f', ?_⟩ ⟨g', ?_⟩
      on_goal 2 =>
        rw [← point]
        apply_fun φ
        erw [RelIso.apply_symm_apply]
        simp [hf, φ, graphIso_map_point]
      on_goal 2 =>
        rw [← point]
        apply_fun φ
        erw [RelIso.apply_symm_apply]
        simp [hg, φ, graphIso_map_point]
      replace this := congr_arg (fun e => φ.symm |>.trans e.toRelIso |>.trans φ) this
      simp only [f', g', RelIso.ext_iff, RelIso.trans_apply, RelIso.apply_symm_apply] at this
      ext p : 2
      exact this p
    is_connected := (G.graphIso x y).connected_iff.mp (graph_connected _) }

@[classical] def rcpgOfColorIso : rcpgOfColor (G x y) ≃p G.colorRCPG x y :=
  { G.graphIso x y with
    map_point' := by
      erw [← point, graphIso_map_point]
      rfl }

@[classical] lemma reachable_x : G.elimColor.Reachable (.o x₀) (.o x) := ⟨
  .cons (v := .a x₀ x) (by constructor) <|
  .cons (v := .p x₀ x) (by constructor) <|
  .cons (v := .o x) (by constructor) .nil
⟩

@[classical] lemma reachable_a : G.elimColor.Reachable (.o x₀) (.a x y) :=
  .trans (reachable_x x₀ x) ⟨.cons (v := .a x y) (by constructor) .nil⟩

@[classical] lemma reachable_b : G.elimColor.Reachable (.o x₀) (.b x y) :=
  .trans (reachable_a x₀ x y) ⟨.cons (v := .b x y) (by constructor) .nil⟩

@[classical] lemma reachable_p : G.elimColor.Reachable (.o x₀) (.p x y) :=
  .trans (reachable_a x₀ x y) ⟨.cons (v := .p x y) (by constructor) .nil⟩

@[classical] lemma reachable_c : G.elimColor.Reachable (.o x₀) (.c x y u) :=
  .trans (reachable_p x₀ x y) <| by
    let p : G.colorSet x y := ⟨.p x y, by simp [colorSet_eq]⟩
    let q : G.colorSet x y := ⟨.c x y u, by simp [colorSet_eq]⟩
    obtain ⟨w⟩ := (G.colorRCPG x y).is_connected p q
    exact ⟨w.map (Hom.comap _ _)⟩

@[classical] lemma reachable_l : G.elimColor.Reachable (.o x₀) (.l x y u) :=
  .trans (reachable_c x₀ x y u) ⟨.cons (v := .l x y u) (by constructor) .nil⟩

@[classical] lemma elimColor_connected [ne : Nonempty α] : G.elimColor.Connected := by
  rw [connected_iff_exists_forall_reachable]
  obtain ⟨x₀⟩ := ne
  refine ⟨.o x₀, fun p => ?_⟩
  cases p with
  | o x => exact reachable_x x₀ x
  | a x y => exact reachable_a x₀ x y
  | b x y => exact reachable_b x₀ x y
  | c x y u => exact reachable_c x₀ x y u
  | l x y u => exact reachable_l x₀ x y u

@[classical] def extractOriginal {p : G.RCPGPoints} (hp : p.Is_o) :=
  hp.chooseUnique <| by rintro x y ⟨_⟩ ⟨_⟩; rfl

@[classical] def mapOriginal := extractOriginal ((iso_o f (p := .o x)).mp ⟨_, rfl⟩)

@[classical] lemma mapOriginal_spec : f (.o x) = .o (mapOriginal f x) := by
  simp only [mapOriginal, extractOriginal]
  generalize_proofs h h'
  exact (h.chooseUnique_spec h').symm

@[classical] lemma mapOriginal_refl : mapOriginal (G := G) .refl x = x := by
  have h := mapOriginal_spec (G := G) .refl x
  simpa only [eq_comm, RelIso.refl_apply, RCPGPoints.o.injEq] using h

@[classical] lemma mapOriginal_trans :
    mapOriginal (f.trans g) x = mapOriginal g (mapOriginal f x) := by
  have h₁ := mapOriginal_spec f x
  have h₂ := mapOriginal_spec g (mapOriginal f x)
  have h₃ := mapOriginal_spec (f.trans g) x
  simpa only [eq_comm, RelIso.trans_apply, h₁, h₂, RCPGPoints.o.injEq] using h₃

@[classical] lemma eq_p_iff : p = .p x y ↔
    ∃ a, a.Is_a ∧ G.elimColor.Adj (.o x) a ∧ G.elimColor.Adj a p ∧ G.elimColor.Adj p (.o y) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h
    use .a x y
    repeat constructor
  · rcases h with ⟨a, ⟨_, _, ⟨_⟩⟩, ⟨_⟩, ⟨_⟩, ⟨_⟩⟩
    rfl

@[classical] lemma eq_a_iff : p = .a x y ↔ p.Is_a ∧ G.elimColor.Adj p (.p x y) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h
    repeat constructor
  · rcases h with ⟨⟨_, _, ⟨_⟩⟩, ⟨_⟩⟩
    rfl

@[classical] lemma eq_b_iff : p = .b x y ↔ p.Is_b ∧ G.elimColor.Adj p (.a x y) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h
    repeat constructor
  · rcases h with ⟨⟨_, _, ⟨_⟩⟩, ⟨_⟩⟩
    rfl

@[classical] lemma map_p : f (.p x y) = .p (mapOriginal f x) (mapOriginal f y) := by
  rw [eq_p_iff, ← mapOriginal_spec, ← mapOriginal_spec, ← f.exists_congr_right,
    RelIso.coe_fn_toEquiv]
  conv => enter [1, a]; simp only [f.map_adj_iff, ← iso_a]
  rw [← eq_p_iff]

@[classical] lemma map_a : f (.a x y) = .a (mapOriginal f x) (mapOriginal f y) := by
  rw [eq_a_iff, ← iso_a, ← map_p, f.map_adj_iff, ← eq_a_iff]

@[classical] lemma map_b : f (.b x y) = .b (mapOriginal f x) (mapOriginal f y) := by
  rw [eq_b_iff, ← iso_b, ← map_a, f.map_adj_iff, ← eq_b_iff]

@[classical] lemma mapOriginal_colorSet :
    Set.BijOn f (G.colorSet x y) (H.colorSet (mapOriginal f x) (mapOriginal f y)) := by
  rw [← RelIso.coe_fn_toEquiv, ← Equiv.image_eq_iff_bijOn,
    ColoredGraph.colorSet, ColoredGraph.colorSet, ← Equiv.setOf_apply_symm_eq_image_setOf,
    show ⇑f.toEquiv.symm = ⇑f.symm from rfl]
  ext p
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← map_p f x y]
  conv_lhs => rw [show .p x y = f.symm (f (.p x y)) by simp]
  rw [← f.symm.map_walk.exists_congr_right]
  congr! 2 with w
  simp only [Iso.map_walk, RelIso.symm_symm, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding, Equiv.coe_fn_mk]
  erw [Walk.support_map]
  simp only [RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  congr! 2 with q
  rw [← iso_c]

@[classical] def mapOriginal_colorRCPG :
    G.colorRCPG x y ≃p H.colorRCPG (mapOriginal f x) (mapOriginal f y) where
  __ := (mapOriginal_colorSet f x y).equiv
  map_rel_iff' := f.map_adj_iff
  map_point' := Subtype.ext (map_p f x y)

@[classical] theorem mapOriginal_preserve_color :
    G x y = H (mapOriginal f x) (mapOriginal f y) := by
  apply color_eq_of_iso
  calc
    _ ≃p _ := G.rcpgOfColorIso x y
    _ ≃p _ := mapOriginal_colorRCPG f x y
    _ ≃p _ := H.rcpgOfColorIso (mapOriginal f x) (mapOriginal f y) |>.symm

@[classical] def mapOriginalEquiv : α ≃ β := {
  toFun := mapOriginal f
  invFun := mapOriginal f.symm
  left_inv := by simp [LeftInverse, mapOriginal_refl, ← mapOriginal_trans]
  right_inv := by simp [LeftInverse, RightInverse, mapOriginal_refl, ← mapOriginal_trans]
}

@[classical] def toColoredGraphIso : G ≃c H :=
  { mapOriginalEquiv f with
    map_color' := (mapOriginal_preserve_color _ _ _).symm }

@[classical] lemma toColoredGraphIso_apply : toColoredGraphIso f x = mapOriginal f x := rfl

@[classical] lemma map_c : f (.c x y u) =
    .c (mapOriginal f x) (mapOriginal f y) ((toColoredGraphIso f).map_color ▸ u) := by
  have hmap : mapOriginal (toColoredGraphIso f).toElimColorIso = mapOriginal f := by
    ext x
    rw [← RCPGPoints.o.injEq (C := C), ← mapOriginal_spec]
    rfl
  have := RCPGIso.is_subsingleton.allEq
    (mapOriginal_colorRCPG f x y)
    (hmap ▸ mapOriginal_colorRCPG (toColoredGraphIso f).toElimColorIso x y)
  let p : G.colorSet x y := ⟨.c x y u, by rw [G.colorSet_eq]; repeat constructor⟩
  apply_fun (fun f => (f p).1) at this
  convert this using 1
  simp only [eqRec_eq_cast]
  apply eq_of_heq
  apply HEq.trans (b := (mapOriginal_colorRCPG (toColoredGraphIso f).toElimColorIso x y p).1) .rfl
  congr 2 <;> try simp [hmap]
  all_goals rw [hmap]

@[classical] lemma eq_l_iff : p = .l x y u ↔ p.Is_l ∧ G.elimColor.Adj p (.c x y u) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h
    repeat constructor
  · rcases h with ⟨⟨_, _, _, ⟨_⟩⟩, ⟨_⟩⟩
    rfl

@[classical] lemma map_l : f (.l x y u) =
    .l (mapOriginal f x) (mapOriginal f y) ((toColoredGraphIso f).map_color ▸ u) := by
  rw [eq_l_iff, ← iso_l, ← map_c, f.map_adj_iff, ← eq_l_iff]

@[classical] lemma toColoredGraphIso_injective :
    Injective (toColoredGraphIso (G := G) (H := H)) := by
  intro f g eq
  ext p
  simp only [toColoredGraphIso, mapOriginalEquiv, ColoredGraphIso.mk.injEq, Equiv.mk.injEq] at eq
  replace eq := eq.1
  cases p with
  | o x => simp only [mapOriginal_spec, eq]
  | a x y => simp only [map_a, eq]
  | b x y => simp only [map_b, eq]
  | c x y u =>
    simp only [map_c]
    congr 1 <;> try simp [eq]
    erw [heq_eqRec_iff_heq, eqRec_heq_iff_heq]
  | l x y u =>
    simp only [map_l]
    congr 1 <;> try simp [eq]
    erw [heq_eqRec_iff_heq, eqRec_heq_iff_heq]

@[classical] lemma toColoredGraphIso_surjective :
    Surjective (toColoredGraphIso (G := G) (H := H)) := by
  refine fun f => ⟨f.toElimColorIso, ?_⟩
  ext x
  rw [toColoredGraphIso_apply, ← RCPGPoints.o.injEq (C := C), ← mapOriginal_spec]
  rfl

@[classical] def toColoredGraphIsoEquiv : (G.elimColor ≃g H.elimColor) ≃ (G ≃c H) :=
  .ofBijective'
    (fun _ => toColoredGraphIso _)
    ⟨toColoredGraphIso_injective, toColoredGraphIso_surjective⟩

@[classical] lemma toColoredGraphIsoEquiv_apply {x} :
    toColoredGraphIsoEquiv f x = mapOriginal f x := rfl

@[classical] def toColoredGraphIsoIso : (G.elimColor ≃g G.elimColor) ≃* (G ≃c G) :=
  { toColoredGraphIsoEquiv with
    map_mul' := by
      intro f g
      ext x
      conv in f * g => change g.trans f
      simp [toColoredGraphIsoEquiv_apply, mapOriginal_trans] }

end ColoredGraph

namespace PointedGraph

open ColoredGraph

variable {α β} {G : PointedGraph α} {H : PointedGraph β}

open Classical in
@[classical] def toColoredGraph {α} (G : PointedGraph α) : ColoredGraph α Bool :=
  fun x y => (G.r x y : Bool)

@[classical] def coloredGraphToPointedGraphIso :
    {f : G.toColoredGraph ≃c H.toColoredGraph // f G.p = H.p} ↪ G ≃· H where
  toFun := fun ⟨f, hf⟩ =>
    { f with
      map_rel_iff' := @fun x y => by
        have hc := f.map_color (x := x) (y := y)
        simp only [PointedGraph.toColoredGraph, decide_eq_decide] at hc
        exact hc
      map_point' := hf }
  inj' := by
    intro ⟨f, hf⟩ ⟨g, hg⟩ eq
    rw [Subtype.mk.injEq]
    rw [DFunLike.ext_iff] at eq ⊢
    intro x
    exact eq x

@[classical] def elimColorToPointedGraphIso :
    {f : G.toColoredGraph.elimColor ≃g H.toColoredGraph.elimColor // f (.o G.p) = .o H.p} ↪
    G ≃· H where
  toFun := fun ⟨f, hf⟩ =>
    coloredGraphToPointedGraphIso
    ⟨toColoredGraphIso f, by rwa [mapOriginal_spec, RCPGPoints.o.injEq] at hf⟩
  inj' := by
    intro ⟨f, hf⟩ ⟨g, hg⟩ eq
    simpa [toColoredGraphIso_injective.eq_iff] using eq

@[classical] def toRCPG (hG : G.Rigid) : RCPG G.toColoredGraph.RCPGPoints :=
  { G.toColoredGraph.elimColor with
    p := .o G.p
    is_rigid' := Injective.subsingleton elimColorToPointedGraphIso.injective
    is_connected := (toColoredGraph G).elimColor_connected (ne := ⟨G.p⟩) }

@[classical] def rcpgToPointedGraphIso
    (hG : G.Rigid) (hH : H.Rigid) (f : G.toRCPG hG ≃p H.toRCPG hH) : G ≃· H :=
  elimColorToPointedGraphIso ⟨f.toRelIso, f.map_point'⟩

@[classical] instance {α} [A : HasEnoughPointedGraph α] : HasEnoughRCPG α :=
  let f := fun (⟨G, hG⟩ : A.S) => ⟨_, G.2.toRCPG (A.all_rigid hG)⟩
  have f_inj : Injective f := by
    rintro ⟨⟨β, G⟩, hG⟩ ⟨⟨γ, H⟩, hH⟩ eq
    simp only [f, Sigma.mk.injEq] at eq
    simp only [Subtype.mk.injEq]
    generalize_proofs rigid_G rigid_H at eq
    have iso : G.toRCPG rigid_G ≃p H.toRCPG rigid_H := by
      convert RCPGIso.refl (G := toRCPG rigid_G) using 1
      congr 1
      · exact eq.1.symm
      · exact eq.2.symm
    by_contra ne
    exact (A.not_isomorphic hG hH ne).false (rcpgToPointedGraphIso rigid_G rigid_H iso)
  {
    S := _
    equiv := A.equiv.trans <| Equiv.ofInjective' f f_inj
    nontrivial := by
      rintro ⟨_, _⟩ ⟨⟨⟨β, G⟩, _⟩, ⟨_⟩⟩
      have : Nonempty β := ⟨G.p⟩
      infer_instance
    not_isomorphic := by
      rintro ⟨_, _⟩ ⟨⟨x, hx⟩, ⟨_⟩⟩ ⟨_, _⟩ ⟨⟨y, hy⟩, ⟨_⟩⟩ ne
      replace ne := (f_inj.ne_iff (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).mp ne
      simp only [ne_eq, Subtype.mk.injEq] at ne
      refine ⟨fun iso => ?_⟩
      dsimp only at iso
      exact (A.not_isomorphic hx hy ne).false (rcpgToPointedGraphIso _ _ iso)
  }

end PointedGraph

@[classical] theorem frucht_from_all_cardinals_fafa₂
    {M : Set (Type u)} (hfafa : FAFA₂On M) (htrans : TransitiveClass M)
    (all_cardinals_fafa : ∀ α : Type u, ∃ β ∈ M, Nonempty (α ≃ β)) :
    Frucht.{u} := by
  intro Γ _
  obtain ⟨Δ, hΔ, ⟨iso⟩⟩ := all_cardinals_fafa Γ
  haveI := instHasEnoughPointedGraph hfafa htrans hΔ
  haveI := instHasEnoughPointedGraphFromEquiv iso.symm
  refine ⟨_, (cayley Γ).elimColor, ⟨?_⟩⟩
  exact ColoredGraph.toColoredGraphIsoIso.trans (cayleyIso Γ)

@[classical] lemma fafa₂_iff : FAFA₂.{u} ↔ FAFA₂On.{u} Set.univ := by
  simp only [FAFA₂, FAFA₂On]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rintro α - β - f
    refine h α β (trcl {α}) (trcl {β}) ?_ ?_ ⟨f.toEquiv, ?_⟩
      (top α) (by simp [top]) (top β) (by simp [top]) ?_
    · rw [isTransitiveClosure_iff]
    · rw [isTransitiveClosure_iff]
    · simp only [InvImage, RelIso.coe_fn_toEquiv, PointedGraphIso.coe_fn_toEquiv]
      exact f.map_rel_iff
    · exact f.map_point
  · intro α β X Y hX hY f x' hx' y' hy' hpoint
    rw [isTransitiveClosure_iff] at hX hY
    cases hX
    cases hY
    refine h _ (by simp) _ (by simp) ⟨⟨f.toEquiv, f.map_rel_iff⟩, ?_⟩
    convert hpoint using 1
    · have : x' = (canonicalGraph α).p := by
        apply elements_inj
        simp [hx', canonicalGraph, top]
      apply elements_inj
      simp [hpoint, hy', ← this]
    · apply elements_inj
      simp [hy', canonicalGraph, top]

def constructOrdinal (α : Ordinal.{u}) : WF.{u} := by
  refine Ordinal.lt_wf.fix (C := fun _ => WF.{u}) (fun β f =>
    ⟨ collect fun (x : β.ToType) =>
        match Ordinal.ToType.mk.symm x with
        | ⟨x, hx⟩ => (f x hx).1,
      ?_ ⟩) α
  refine Acc.intro _ ?_
  simp only [mem_collect, forall_exists_index, forall_apply_eq_imp_iff]
  exact fun _ => (f _ _).2

lemma constructOrdinal_mem_of_lt {α β : Ordinal.{u}} (lt : α < β) :
    constructOrdinal α ∈ constructOrdinal β := by
  conv_lhs => simp [constructOrdinal]
  rw [WellFounded.fix_eq _ _]
  simp only [mem_class_iff, mem_collect]
  refine ⟨Ordinal.ToType.mk ⟨α, lt⟩, ?_⟩
  rw [OrderIso.symm_apply_apply]
  rfl

lemma constructOrdinal_inj : Injective constructOrdinal := by
  intro α β ne
  contrapose! ne
  have : α < β ∨ β < α := lt_or_gt_of_ne ne
  obtain this | this := this
  · exact fun h => not_mem_self_wf (h ▸ constructOrdinal_mem_of_lt this)
  · exact fun h => not_mem_self_wf (h ▸ constructOrdinal_mem_of_lt this)

def constructOrdinal_iso (α : Ordinal.{u}) : constructOrdinal α ≃ α.ToType := by
  simp only [constructOrdinal]
  rw [WellFounded.fix_eq]
  conv => enter [1, 1, 1, 1, x, 1, 0, y, x]; change constructOrdinal y
  refine (collectEquivRange _).trans (Equiv.ofInjective' _ ?_).symm
  apply Injective.comp Subtype.val_injective
  apply Injective.comp constructOrdinal_inj
  apply Injective.comp Subtype.val_injective
  exact OrderIso.injective _

@[classical!] theorem fafa₂_implies_frucht : FAFA₂.{u} → Frucht.{u} :=
  fun h => frucht_from_all_cardinals_fafa₂
    (M := Set.univ)
    (by rwa [← fafa₂_iff])
    (by simp [TransitiveClass])
    (fun α => ⟨α, by simp, ⟨.refl _⟩⟩)

@[classical!] theorem foundation_implies_frucht : Foundation.{u} → Frucht.{u} := by
  refine fun h => fafa₂_implies_frucht ?_
  rw [fafa₂_iff]
  convert fafa₂_on_wf
  ext α
  simp only [Set.mem_univ, true_iff]
  by_contra hx
  obtain ⟨x, hx⟩ := h (separate (trcl {α}) (· ∉ WF))
    (by simpa [mem_separate] using ⟨α, trcl_singleton_contains_self, hx⟩)
  simp only [mem_separate, and_imp] at hx
  refine hx.1.2 (.intro _ ?_)
  intro y hy
  by_contra y_not_wf
  exact hx.2 y (trcl_singleton_trans_of_mem hy hx.1.1) y_not_wf hy

theorem choice_implies_frucht : Frucht.{u} :=
  frucht_from_all_cardinals_fafa₂ fafa₂_on_wf transitive_wf <| by
    intro α
    obtain ⟨e⟩ : Nonempty ((#α).ord.ToType ≃ α) := by
      rw [← Cardinal.eq]
      apply mk_ord_toType
    exact ⟨constructOrdinal (#α).ord, by simp, ⟨((constructOrdinal_iso _).trans e).symm⟩⟩
