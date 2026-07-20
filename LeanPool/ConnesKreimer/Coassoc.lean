/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/

/- Coassociativity of the Connes–Kreimer / Foissy (planar, R1) coproduct.
   Core Lean only (List.Perm), no Mathlib → fast builds.
   The element of H⊗H is a formal sum = `List (Forest × Forest)`; equality of formal sums
   = `List.Perm` (multiset equality). Empirically (probe 2026-06-18) coassoc holds up to Perm,
   not literal list equality. WIP, LOCAL only. -/

namespace CK.Coassoc

/-- Planar rooted trees, represented by the forest of children below the root. -/
inductive RTree where
  | node : List RTree → RTree
deriving Repr, Inhabited

/-- A planar rooted forest is a list of planar rooted trees. -/
abbrev Forest := List RTree

/-- Formal sums of coproduct tensor monomials, represented by their forest pairs. -/
abbrev Tens := List (Forest × Forest)

/-- product on H⊗H, leg-wise forest product (R1 planar: list append). -/
def tmul (x y : Tens) : Tens :=
  x.flatMap (fun (p, r) => y.map (fun (p', r') => (p ++ p', r ++ r')))

mutual
  /-- The Connes-Kreimer coproduct on one rooted tree, as a formal list of tensor terms. -/
  def coprodTree : RTree → Tens
    | .node F => ([RTree.node F], []) :: (coprodForest F).map (fun (p, r) => (p, [RTree.node r]))
  /-- The multiplicative extension of the coproduct from trees to forests. -/
  def coprodForest : Forest → Tens
    | []      => [([], [])]
    | t :: ts => tmul (coprodTree t) (coprodForest ts)
end

/-! ### Easy lemmas: units of `tmul`. -/

/-- The empty forest `[([],[])]` is a left unit for `tmul`, literally. -/
@[simp] theorem _root_.CK.Coassoc.tmul_unit_left (y : Tens) : tmul [([], [])] y = y := by
  simp [tmul]

/-- Right unit, up to `=` via `append_nil`. -/
@[simp] theorem _root_.CK.Coassoc.tmul_unit_right (x : Tens) : tmul x [([], [])] = x := by
  induction x with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨p, r⟩ := a
    simp [tmul, List.append_nil]

/-- `tmul` is left-distributive over `++` (formal-sum bilinearity, left). -/
theorem _root_.CK.Coassoc.tmul_append_left (x₁ x₂ y : Tens) :
    tmul (x₁ ++ x₂) y = tmul x₁ y ++ tmul x₂ y := by
  simp [tmul, List.flatMap_append]

/-- `tmul` on a cons unfolds to a `map` head plus the tail product. -/
theorem _root_.CK.Coassoc.tmul_cons (p r : Forest) (xs y : Tens) :
    tmul ((p, r) :: xs) y = y.map (fun (p', r') => (p ++ p', r ++ r')) ++ tmul xs y := by
  simp [tmul]

/-- `tmul` is associative, literally (legs by `append_assoc`, sums by `flatMap` nesting). -/
theorem _root_.CK.Coassoc.tmul_assoc (x y z : Tens) : tmul (tmul x y) z = tmul x (tmul y z) := by
  induction x with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨p, r⟩ := a
    rw [tmul_cons, tmul_append_left, ih, tmul_cons]
    congr 1
    -- head term: (y.map ..).flatMap-into-z  vs  map over (tmul y z)
    simp [tmul, List.flatMap_map, List.map_flatMap, List.append_assoc, Function.comp_def]

/-- Multiplicativity of `Δ`: the coproduct of a forest product is the product of coproducts.
    Literal `=` (rides on `tmul_assoc` + units). -/
theorem _root_.CK.Coassoc.coprodForest_append (F G : Forest) :
    coprodForest (F ++ G) = tmul (coprodForest F) (coprodForest G) := by
  induction F with
  | nil => simp [coprodForest, tmul_unit_left]
  | cons t ts ih =>
    show coprodForest (t :: (ts ++ G)) = _
    rw [show coprodForest (t :: (ts ++ G)) = tmul (coprodTree t) (coprodForest (ts ++ G)) from rfl,
        ih, ← tmul_assoc,
        show tmul (coprodTree t) (coprodForest ts) = coprodForest (t :: ts) from rfl]

/-! ### List/Perm plumbing for the Fubini swap (core Lean, no Mathlib). -/

open List in
/-- `(A++B)++(C++D) ~ (A++C)++(B++D)`: swap the inner two blocks. -/
theorem _root_.CK.Coassoc.perm_middle_swap {α} (A B C D : List α) :
    ((A ++ B) ++ (C ++ D)).Perm ((A ++ C) ++ (B ++ D)) := by
  calc (A ++ B) ++ (C ++ D)
      = A ++ ((B ++ C) ++ D) := by simp [List.append_assoc]
    _ ~ A ++ ((C ++ B) ++ D) := (List.perm_append_comm).append_right D |>.append_left A
    _ = (A ++ C) ++ (B ++ D) := by simp [List.append_assoc]

open List in
/-- `flatMap` distributes over a pointwise append, up to `Perm`. -/
theorem _root_.CK.Coassoc.flatMap_append_distrib {α β} (l : List α) (X Y : α → List β) :
    (l.flatMap (fun a => X a ++ Y a)).Perm (l.flatMap X ++ l.flatMap Y) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons]
    refine (List.Perm.append_left (X a ++ Y a) ih).trans ?_
    exact perm_middle_swap (X a) (Y a) (as.flatMap X) (as.flatMap Y)

open List in
/-- `flatMap` of a constantly-empty function is empty. -/
theorem _root_.CK.Coassoc.flatMap_const_nil {α β} (l : List α) :
    l.flatMap (fun _ => ([] : List β)) = [] := by
  simp_all

/-- `flatMap` of a singleton-valued function is a `map`. -/
theorem _root_.CK.Coassoc.flatMap_singleton_eq_map {α β} (g : α → β) (l : List α) :
    l.flatMap (fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, ih]

open List in
/-- Fubini: two independent nested `flatMap`s commute, up to `Perm`. -/
theorem _root_.CK.Coassoc.flatMap_comm {α β γ} (l1 : List α) (l2 : List β)
    (f : α → β → List γ) :
    (l1.flatMap (fun a => l2.flatMap (fun b => f a b))).Perm
    (l2.flatMap (fun b => l1.flatMap (fun a => f a b))) := by
  induction l1 with
  | nil => simp [flatMap_const_nil]
  | cons a as ih =>
    simp only [List.flatMap_cons]
    refine (List.Perm.append_right _ (List.Perm.refl _)).trans ?_
    refine (List.Perm.append_left (l2.flatMap (fun b => f a b)) ih).trans ?_
    exact (flatMap_append_distrib l2 (fun b => f a b) (fun b => as.flatMap (fun a => f a b))).symm

open List in
/-- Congruence: pointwise-`Perm` inner functions give `Perm` flatMaps (over the same list). -/
theorem _root_.CK.Coassoc.Perm.flatMap_congr_right {α β} (l : List α) {f g : α → List β}
    (h : ∀ a, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.flatMap_cons]; exact (h a).append ih

/-! ### Coassociativity. `Δ³` two ways; equal as formal sums (`List.Perm`). -/

/-- Formal sums of triple tensor monomials, represented by forest triples. -/
abbrev _root_.CK.Coassoc.Tens3 := List (Forest × Forest × Forest)

/-- `(Δ⊗id)∘Δ`: expand the LEFT leg of each tensor via `coprodForest`. -/
def _root_.CK.Coassoc.coLeft (x : Tens) : Tens3 :=
  x.flatMap (fun (p, r) => (coprodForest p).map (fun (a, b) => (a, b, r)))

/-- `(id⊗Δ)∘Δ`: expand the RIGHT leg of each tensor via `coprodForest`. -/
def _root_.CK.Coassoc.coRight (x : Tens) : Tens3 :=
  x.flatMap (fun (p, r) => (coprodForest r).map (fun (b, c) => (p, b, c)))

/-- leg-wise product on triple tensors (R1 planar: list append on each of the 3 legs). -/
def _root_.CK.Coassoc.tmul3 (x y : Tens3) : Tens3 :=
  x.flatMap (fun (a, b, c) => y.map (fun (a', b', c') => (a ++ a', b ++ b', c ++ c')))

/-- `coLeft` is a coalgebra-style morphism for `tmul` → `tmul3`, up to `Perm`. -/
theorem _root_.CK.Coassoc.coLeft_tmul (x y : Tens) :
    (coLeft (tmul x y)).Perm (tmul3 (coLeft x) (coLeft y)) := by
  simp only [coLeft, tmul, tmul3, List.flatMap_map, List.map_flatMap, List.map_map,
    List.flatMap_assoc, Function.comp_def, coprodForest_append]
  -- LHS loops x,y,cFp,cFp' vs RHS x,cFp,y,cFp': swap the independent middle two
  -- under the x-binder.
  exact Perm.flatMap_congr_right x (fun pr => flatMap_comm _ _ _)

/-- `coRight` likewise. -/
theorem _root_.CK.Coassoc.coRight_tmul (x y : Tens) :
    (coRight (tmul x y)).Perm (tmul3 (coRight x) (coRight y)) := by
  simp only [coRight, tmul, tmul3, List.flatMap_map, List.map_flatMap, List.map_map,
    List.flatMap_assoc, Function.comp_def, coprodForest_append]
  exact Perm.flatMap_congr_right x (fun pr => flatMap_comm _ _ _)

/-- Unfold the tree coproduct (the B₊ cocycle), as a `simp` lemma. -/
theorem _root_.CK.Coassoc.coprodTree_node (F : Forest) :
    coprodTree (RTree.node F)
      = ([RTree.node F], []) :: (coprodForest F).map (fun pr => (pr.1, [RTree.node pr.2])) := rfl

/-- A singleton forest's coproduct is the tree coproduct. -/
theorem _root_.CK.Coassoc.coprodForest_single (t : RTree) : coprodForest [t] = coprodTree t := by
  show tmul (coprodTree t) (coprodForest []) = coprodTree t
  rw [show coprodForest ([] : Forest) = [([], [])] from rfl, tmul_unit_right]

/-- `tmul3` respects `Perm` in both arguments. -/
theorem _root_.CK.Coassoc.tmul3_perm {a a' b b' : Tens3} (ha : a.Perm a') (hb : b.Perm b') :
    (tmul3 a b).Perm (tmul3 a' b') := by
  refine (ha.flatMap_right _).trans ?_
  exact Perm.flatMap_congr_right a' (fun _ => hb.map _)

mutual
  /-- Coassociativity on a tree. -/
  theorem _root_.CK.Coassoc.coassocTree (t : RTree) :
      (coLeft (coprodTree t)).Perm (coRight (coprodTree t)) := by
    cases t with
    | node F =>
      simp only [coLeft, coRight, coprodTree_node, coprodForest_single, List.map_cons,
        List.flatMap_cons, List.map_map, List.flatMap_map, Function.comp_def,
        show coprodForest ([] : Forest) = [([], [])] from rfl]
      -- Goal: (head :: (A' ++ L2)).Perm ([head] ++ R2).  Cancel the common head, then A'++L2 ~ R2.
      refine List.Perm.cons _ ?_
      -- R2 ~ A' ++ R2b  (split the inner cons, singleton-flatMap = map = A')
      have hR2 :
          (List.flatMap (fun a => (a.fst, [RTree.node a.snd], []) ::
              List.map (fun x => (a.fst, x.fst, [RTree.node x.snd])) (coprodForest a.snd))
              (coprodForest F)).Perm
          (List.map (fun x => (x.fst, [RTree.node x.snd], [])) (coprodForest F)
            ++ List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
                (coprodForest a.snd)) (coprodForest F)) := by
        have h := flatMap_append_distrib (coprodForest F)
          (fun a => [(a.fst, [RTree.node a.snd], [])])
          (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd])) (coprodForest a.snd))
        rwa [flatMap_singleton_eq_map] at h
      -- L2 ~ R2b  via  L2 = map φ (coLeft), R2b = map φ (coRight),  coassocForest F
      have hkey :
          (List.flatMap (fun a => List.map (fun x => (x.fst, x.snd, [RTree.node a.snd]))
              (coprodForest a.fst)) (coprodForest F)).Perm
          (List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
              (coprodForest a.snd)) (coprodForest F)) := by
        have e1 :
            (List.flatMap (fun a => List.map (fun x => (x.fst, x.snd, [RTree.node a.snd]))
              (coprodForest a.fst)) (coprodForest F))
            = (coLeft (coprodForest F)).map (fun t => (t.1, t.2.1, [RTree.node t.2.2])) := by
          simp [coLeft, List.map_flatMap, List.map_map, Function.comp_def]
        have e2 :
            (List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
              (coprodForest a.snd)) (coprodForest F))
            = (coRight (coprodForest F)).map (fun t => (t.1, t.2.1, [RTree.node t.2.2])) := by
          simp [coRight, List.map_flatMap, List.map_map, Function.comp_def]
        rw [e1, e2]
        exact (coassocForest F).map _
      exact (List.Perm.append_left _ hkey).trans hR2.symm
  /-- Coassociativity on a forest (needed for the mutual recursion). -/
  theorem _root_.CK.Coassoc.coassocForest (F : Forest) :
      (coLeft (coprodForest F)).Perm (coRight (coprodForest F)) := by
    cases F with
    | nil => exact .refl _
    | cons t ts =>
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl]
      refine (coLeft_tmul _ _).trans ?_
      refine (tmul3_perm (coassocTree t) (coassocForest ts)).trans ?_
      exact (coRight_tmul _ _).symm
end

/-- **Coassociativity** of the Connes–Kreimer / Foissy (planar) coproduct on rooted trees:
    `(Δ⊗id)∘Δ` and `(id⊗Δ)∘Δ` agree as formal sums (multiset equality / `List.Perm`).
    The wall: proven by mutual induction tree↔forest via the B₊ Hochschild-1-cocycle,
    on top of multiplicativity + a Fubini swap. First formalization in any ITP. -/
theorem _root_.CK.Coassoc.coprod_coassoc (t : RTree) :
    (coLeft (coprodTree t)).Perm (coRight (coprodTree t)) := coassocTree t

end CK.Coassoc
