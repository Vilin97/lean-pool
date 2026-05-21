/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

namespace LeanPool.Polylean

universe u v w

/-- A `Quiver` `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
    a type `a ⟶ b` of arrows from `a` to `b`.

    It is a common generalisation of multigraphs and categories.
    This definition is taken from `mathlib`:
    https://leanprover-community.github.io/mathlib_docs/combinatorics/quiver/basic.html#quiver. -/
class Quiver (V : Sort u) where
  /-- The type of arrows from one vertex to another. -/
  hom : V → V → Sort v

/-- Arrow notation for the hom type of a quiver. -/
infixr:10 " ⟶ " => Quiver.hom -- type using `\-->` or `\hom`

namespace Quiver

/-- A pre-functor is a morphism of quivers. -/
structure PreFunctor {V V' : Sort _} (Q : Quiver V) (Q' : Quiver V') where
  /-- The map on vertices. -/
  obj : V → V'
  /-- The map on arrows. -/
  map : {X Y : V} → (X ⟶ Y) → (obj X ⟶ obj Y)

namespace PreFunctor

/-- The identity morphism between quivers. -/
@[simp] protected def id (V : Sort _) [Q : Quiver V] : PreFunctor Q Q :=
{ obj := id, map := id }

instance (V : Sort _) [Q : Quiver V] : Inhabited (PreFunctor Q Q) := ⟨PreFunctor.id V⟩

/-- Composition of morphisms between quivers. -/
@[simp] def comp {U V W : Sort _} {QU : Quiver U} {QV : Quiver V} {QW : Quiver W}
  (F : PreFunctor QU QV) (G : PreFunctor QV QW) : PreFunctor QU QW :=
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map }

end PreFunctor

end Quiver


/-- Paths in a quiver. -/
inductive Path {V : Sort _} [Quiver V] : V → V → Sort _
  | nil : {A : V} → Path A A
  | cons : {A B C : V} → (A ⟶ B) → Path B C → Path A C

namespace Quiver

/-- Convert a single quiver arrow to a path. -/
def toPath {V : Sort _} [Quiver V] {A B : V} (e : A ⟶ B) : Path A B :=
  .cons e .nil

end Quiver

namespace Path

variable {V : Sort _} [Quiver V] {A B C D : V}

/-- The empty path at a vertex, with its vertex explicit for pattern matching. -/
@[match_pattern] abbrev nil' (A : V) : Path A A := Path.nil
/-- A path formed by adding an edge to the front, with endpoints explicit for matching. -/
@[match_pattern] abbrev cons' (A B C : V) :
  (A ⟶ B) → Path B C → Path A C := Path.cons

/-- Concatenate an edge to the end of a path. -/
@[match_pattern]
abbrev snoc : {A B C : V} → Path A B → (B ⟶ C) → Path A C
  | _, _, _, .nil, e => .cons e .nil
  | _, _, _, .cons e p', e' => .cons e (snoc p' e')

/-- Append an edge to the end of a path, with endpoints explicit for matching. -/
@[match_pattern]
abbrev snoc' (A B C : V) : Path A B → (B ⟶ C) → Path A C := Path.snoc

/-- Concatenation of paths. -/
def append : {A B C : V} → Path A B → Path B C → Path A C
  | _, _, _, .nil, p => p
  | _, _, _, .cons e p', p => cons e (append p' p)

/-- The length of a path. -/
def length : {A B : V} → Path A B → Nat
  | _, _, .nil => .zero
  | _, _, .cons _ p => .succ (length p)

@[simp] theorem nil_append (p : Path A B) : .append .nil p = p := rfl

@[simp] theorem append_nil (p : Path A B) : .append p .nil = p := by
  induction p
  · case nil => rfl
  · case cons =>
      simp only [append]
      apply congrArg
      assumption

theorem snoc_cons (e : A ⟶ B) (p : Path B C) (e' : C ⟶ D) :
  snoc (cons e p) e' = cons e (snoc p e') := by cases p <;> simp

theorem append_snoc (p : Path A B) (p' : Path B C) (e : C ⟶ D) :
    append p (snoc p' e) = snoc (append p p') e := by
  induction p
  · case nil => rfl
  · case cons ih => simp [append, ih p']

theorem append_cons (p : Path A B) (e : B ⟶ C) (p' : Path C D) :
    append p (cons e p') = append (snoc p e) p' := by
  induction p
  · case nil => rfl
  · case cons ih => dsimp [append]; rw [ih]

theorem append_assoc (p : Path A B) (q : Path B C) (r : Path C D) :
    append (append p q) r = append p (append q r) := by
  induction p
  · case nil => rfl
  · case cons ih => simp [append]; apply ih

-- TODO Rephrase this to work for general paths, not just loops
theorem nil_length {A : V} : (p : Path A A) → p.length = .zero ↔ p = .nil' A
  | .nil => ⟨λ _ => rfl, λ _ => rfl⟩
  | .cons _ p => by apply Iff.intro <;> (intro; simp [length] at *)

theorem snoc_length {A B C : V} : (p : Path A B) → (e : B ⟶ C) → length (.snoc p e) = .succ (length p)
  | .nil, e => rfl
  | .cons _ p', e => by
    rw [snoc_cons]
    dsimp only [length]
    apply congrArg
    apply snoc_length

theorem length_append {A B C : V} : (p : Path A B) → (q : Path B C) → (append p q).length = p.length + q.length
  | .nil, q => by rw [Nat.add_comm]; rfl
  | .cons _ p', q => by
    dsimp [append, length]
    simpa [Nat.succ_add] using congrArg Nat.succ (length_append p' q)

/-- The end-point of the first edge in the path. -/
def first : Path A B → V
  | .nil' v => v
  | .cons' _ v _ _ _ => v

/-- The source of the last end in the path. -/
def last : {A B : V} → Path A B → V
  | _, _, .nil' v => v
  | .(v), _, .cons' v _ _ _ .nil => v
  | _, _, .cons' _ _ _ _ (.cons e p) => last (.cons e p)

theorem first_cons (A B C : V) (e : A ⟶ B) (p : Path B C) : first (cons e p) = B := rfl

theorem last_snoc : (A B C : V) → (p : Path A B) → (e : B ⟶ C) → last (snoc p e) = B
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons' _ _ _ _ .nil, _ => by rw [snoc_cons]; rfl
  | _, _, _, .cons' _ _ _ _ (.cons _ _), _ => by rw [snoc_cons, snoc, last, ← snoc_cons]; apply last_snoc

end Path


/-- A loop is a path whose source and target are the same vertex. -/
abbrev Loop {V : Sort _} [Quiver V] (A : V) := Path A A

namespace Loop

variable {V : Sort _} [Quiver V] (A : V)

/-- Regard a loop as a path. -/
def toPath : Loop A → Path A A := id

/-- The empty loop. -/
abbrev nil : Loop A := Path.nil

/-- The next vertex reached by the first edge of a loop. -/
abbrev next : Loop A → V := Path.first

/-- Concatenate two loops. -/
abbrev concat : Loop A → Loop A → Loop A := Path.append

end Loop
end LeanPool.Polylean
