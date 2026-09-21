/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.MarshallHall.MarshallHall.GraphBasis
import LeanPool.MarshallHall.MarshallHall.FreeFactor

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

namespace MarshallHall

universe u

variable {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]

/-!
## Core-supported words in a spanning-tree basis

The finite-core argument produces paths whose labelled edges belong to a fixed
finite set of generator edges.  The lemmas below make that geometric fact
visible in the free basis supplied by a spanning tree.
-/

def symPathHom {a : Symmetrify (IsFreeGroupoid.Generators G)} :
    ∀ {b : Symmetrify (IsFreeGroupoid.Generators G)},
      Path a b → ((show G from a) ⟶ b)
  | _, Path.nil => 𝟙 _
  | _, Path.cons p e =>
      symPathHom p ≫ Sum.recOn e
        (fun f => IsFreeGroupoid.of f)
        (fun f => inv (IsFreeGroupoid.of f))

@[simp]
theorem symPathHom_nil {a : Symmetrify (IsFreeGroupoid.Generators G)} :
    symPathHom (Path.nil : Path a a) = 𝟙 (show G from a) := rfl

def basisSupport {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))}
    (P : Set (Quiver.Total (IsFreeGroupoid.Generators G))) :
    Set ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ :
      Set (Quiver.Total (IsFreeGroupoid.Generators G))) :=
  {e | e.1 ∈ P}

def forgetSubquiverPath {V : Type u} [Quiver V] {P : WideSubquiver V}
    {a b : P} : @Path P P.quiver a b → @Path V inferInstance (a : V) (b : V)
  | Path.nil => Path.nil
  | Path.cons p e => Path.cons (forgetSubquiverPath p) e.1

@[simp] theorem forgetSubquiverPath_nil {V : Type u} [Quiver V]
    {P : WideSubquiver V} {a : P} :
    forgetSubquiverPath (Path.nil : @Path P P.quiver a a) = Path.nil := rfl

@[simp] theorem forgetSubquiverPath_cons {V : Type u} [Quiver V]
    {P : WideSubquiver V} {a b c : P}
    (p : @Path P P.quiver a b) (e : b ⟶ c) :
    forgetSubquiverPath (p.cons e) = (forgetSubquiverPath p).cons e.1 := rfl

theorem symPathHom_forget_cast_apply
    {G : Type u} [Groupoid G] [IsFreeGroupoid G]
    {P : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))}
    {a a' b b' : P} {R : Type u}
    (f : ∀ {x y : G}, (x ⟶ y) → R)
    (p : @Path P P.quiver a b) (ha : a = a') (hb : b = b') :
    f (symPathHom (G := G)
      (forgetSubquiverPath (P := P) (p.cast ha hb))) =
    f (symPathHom (G := G)
      (forgetSubquiverPath (P := P) p)) := by
  cases ha
  cases hb
  rfl

def positiveEdgeOfSym {a b : Symmetrify (IsFreeGroupoid.Generators G)}
    (e : a ⟶ b) : Quiver.Total (IsFreeGroupoid.Generators G) :=
  match e with
  | Sum.inl f => ⟨a, b, f⟩
  | Sum.inr f => ⟨b, a, f⟩

def retractBasisElement {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (z : K) : K :=
  subsetBasisHom B Y (basisRetraction Y (B.repr z))

theorem retractBasisElement_one {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) :
    retractBasisElement B Y (1 : K) = 1 := by
  unfold retractBasisElement
  rw [B.repr.map_one, (basisRetraction Y).map_one, (subsetBasisHom B Y).map_one]
  rfl

theorem retractBasisElement_mul {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (z w : K) :
    retractBasisElement B Y (z * w) =
      retractBasisElement B Y z * retractBasisElement B Y w := by
  unfold retractBasisElement
  rw [B.repr.map_mul, (basisRetraction Y).map_mul,
    (subsetBasisHom B Y).map_mul]
  rfl

theorem retractBasisElement_inv {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (z : K) :
    retractBasisElement B Y z⁻¹ = (retractBasisElement B Y z)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).2
  rw [← retractBasisElement_mul]
  rw [inv_mul_cancel, retractBasisElement_one]

theorem loopOfHom_comp {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))}
    [Arborescence T] {a b c : G} (p : a ⟶ b) (q : b ⟶ c) :
    IsFreeGroupoid.SpanningTree.loopOfHom T (p ≫ q) =
      IsFreeGroupoid.SpanningTree.loopOfHom T q *
        IsFreeGroupoid.SpanningTree.loopOfHom T p := by
  simp [IsFreeGroupoid.SpanningTree.loopOfHom, Category.assoc]

theorem loopOfHom_inv {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))}
    [Arborescence T] {a b : G} (p : a ⟶ b) :
      IsFreeGroupoid.SpanningTree.loopOfHom T (inv p) =
      (IsFreeGroupoid.SpanningTree.loopOfHom T p)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).2
  simp [IsFreeGroupoid.SpanningTree.loopOfHom, CategoryTheory.End.mul_def,
    Category.assoc]

theorem basis_retraction_loop_of_edge
    {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))}
    [Arborescence T]
    (P : Set (Quiver.Total (IsFreeGroupoid.Generators G)))
    {a b : IsFreeGroupoid.Generators G} (e : a ⟶ b)
    (heP : ⟨a, b, e⟩ ∈ P) :
    retractBasisElement (spanningTreeBasis T) (basisSupport (T := T) P)
      (IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e)) =
      IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e) := by
  let B := spanningTreeBasis T
  let X := ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ :
      Set (Quiver.Total (IsFreeGroupoid.Generators G)))
  let Y := basisSupport (T := T) P
  by_cases heT : e ∈ wideSubquiverSymmetrify T a b
  · rw [IsFreeGroupoid.SpanningTree.loopOfHom_eq_id T e heT]
    exact retractBasisElement_one B Y
  · let x : X := ⟨⟨a, b, e⟩, by
      change ¬ e ∈ wideSubquiverSymmetrify T a b
      exact heT⟩
    have hxY : x ∈ Y := by
      change (⟨a, b, e⟩ : Quiver.Total (IsFreeGroupoid.Generators G)) ∈ P
      exact heP
    have hBx : B x = IsFreeGroupoid.SpanningTree.loopOfHom T
        (IsFreeGroupoid.of e) := by
      exact spanningTreeBasis_apply T x
    have hrepr : B.repr (IsFreeGroupoid.SpanningTree.loopOfHom T
        (IsFreeGroupoid.of e)) = FreeGroup.of x := by
      rw [← hBx]
      exact B.repr_apply_coe x
    calc
      retractBasisElement B Y (IsFreeGroupoid.SpanningTree.loopOfHom T
          (IsFreeGroupoid.of e)) =
          subsetBasisHom B Y (FreeGroup.of ⟨x, hxY⟩) := by
            rw [retractBasisElement, hrepr,
              basisRetraction_apply_of_mem Y hxY]
      _ = (B x : End (show G from root T)) := by
        rw [subsetBasisHom_apply_of]
      _ = IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e) := hBx

theorem basis_retraction_loop_of_path
    {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))}
    [Arborescence T]
    (P : Set (Quiver.Total (IsFreeGroupoid.Generators G)))
    {a : Symmetrify (IsFreeGroupoid.Generators G)}
    (p : @Path (Symmetrify (IsFreeGroupoid.Generators G))
      (symmetrifyQuiver (IsFreeGroupoid.Generators G))
      (show Symmetrify (IsFreeGroupoid.Generators G) from root T) a)
    (hp : ∀ {x y : IsFreeGroupoid.Generators G} (e : x ⟶ y),
      ⟨x, y, e⟩ ∈ P) :
    retractBasisElement (spanningTreeBasis T) (basisSupport (T := T) P)
        (IsFreeGroupoid.SpanningTree.loopOfHom T (symPathHom p)) =
      IsFreeGroupoid.SpanningTree.loopOfHom T (symPathHom p) := by
  let B := spanningTreeBasis T
  let Y := basisSupport (T := T) P
  induction p with
  | nil =>
      rw [symPathHom_nil]
      rw [IsFreeGroupoid.SpanningTree.loopOfHom]
      simp only [Category.id_comp, IsIso.hom_inv_id]
      exact retractBasisElement_one B Y
  | cons p e ih =>
      cases e with
      | inl e =>
          rw [symPathHom.eq_def, loopOfHom_comp]
          simp only [Sum.recOn]
          rw [retractBasisElement_mul,
            basis_retraction_loop_of_edge P e (hp e), ih]
      | inr e =>
          rw [symPathHom.eq_def, loopOfHom_comp]
          simp only [Sum.recOn]
          rw [retractBasisElement_mul, loopOfHom_inv,
            retractBasisElement_inv,
            basis_retraction_loop_of_edge P e (hp e), ih]

theorem basis_retraction_loop_of_subquiver_path
    {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))}
    [Arborescence T]
    (P : Set (Quiver.Total (IsFreeGroupoid.Generators G)))
    (Q : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)))
    (hQ : ∀ {a b : Symmetrify (IsFreeGroupoid.Generators G)}
      (e : a ⟶ b), e ∈ Q a b → positiveEdgeOfSym e ∈ P)
    {a : Q} (p : @Path (WideSubquiver.toType
      (Symmetrify (IsFreeGroupoid.Generators G)) Q) Q.quiver
      (show Q from root T) a) :
    retractBasisElement (spanningTreeBasis T) (basisSupport (T := T) P)
        (IsFreeGroupoid.SpanningTree.loopOfHom T
          (symPathHom (forgetSubquiverPath p))) =
      IsFreeGroupoid.SpanningTree.loopOfHom T
        (symPathHom (forgetSubquiverPath p)) := by
  let B := spanningTreeBasis T
  let Y := basisSupport (T := T) P
  induction p with
  | nil =>
      rw [forgetSubquiverPath_nil, symPathHom_nil]
      rw [IsFreeGroupoid.SpanningTree.loopOfHom]
      simp only [Category.id_comp, IsIso.hom_inv_id]
      exact retractBasisElement_one B Y
  | cons p e ih =>
      rw [forgetSubquiverPath_cons]
      rw [symPathHom.eq_def, loopOfHom_comp]
      rcases e with ⟨e | e, heQ⟩
      · have heP : positiveEdgeOfSym (Sum.inl e) ∈ P :=
            hQ (Sum.inl e) heQ
        have heP' : ⟨_, _, e⟩ ∈ P := by
          simpa [positiveEdgeOfSym] using heP
        rw [retractBasisElement_mul,
          basis_retraction_loop_of_edge P e heP', ih]
      · have heP : positiveEdgeOfSym (Sum.inr e) ∈ P :=
            hQ (Sum.inr e) heQ
        have heP' : ⟨_, _, e⟩ ∈ P := by
          simpa [positiveEdgeOfSym] using heP
        rw [retractBasisElement_mul, loopOfHom_inv,
          retractBasisElement_inv,
          basis_retraction_loop_of_edge P e heP', ih]

end MarshallHall
