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
        (fun f => @CategoryTheory.inv G _ _ _ (IsFreeGroupoid.of f)
          (@IsIso.of_groupoid G _ _ _ (IsFreeGroupoid.of f)))

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

private theorem loopOfHom_id
    {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))} [Arborescence T]
    (a : G) : IsFreeGroupoid.SpanningTree.loopOfHom T (𝟙 a) = 1 := by
  simp [IsFreeGroupoid.SpanningTree.loopOfHom]

private theorem retractBasisElement_of_mem {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (x : X) (hx : x ∈ Y) :
    retractBasisElement B Y (B x) = B x := by
  unfold retractBasisElement
  rw [B.repr_apply_coe, basisRetraction_apply_of_mem Y hx, subsetBasisHom_apply_of]

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

private theorem retract_loop_comp
    {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))} [Arborescence T]
    (Y : Set ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ :
      Set (Quiver.Total (IsFreeGroupoid.Generators G))))
    {a b c : G} (p : a ⟶ b) (q : b ⟶ c)
    (hp : retractBasisElement (spanningTreeBasis T) Y
      (IsFreeGroupoid.SpanningTree.loopOfHom T p) =
        IsFreeGroupoid.SpanningTree.loopOfHom T p)
    (hq : retractBasisElement (spanningTreeBasis T) Y
      (IsFreeGroupoid.SpanningTree.loopOfHom T q) =
        IsFreeGroupoid.SpanningTree.loopOfHom T q) :
    retractBasisElement (spanningTreeBasis T) Y
      (IsFreeGroupoid.SpanningTree.loopOfHom T (p ≫ q)) =
        IsFreeGroupoid.SpanningTree.loopOfHom T (p ≫ q) := by
  exact (congrArg (retractBasisElement (spanningTreeBasis T) Y) (loopOfHom_comp p q)).trans
    ((retractBasisElement_mul (spanningTreeBasis T) Y _ _).trans
      ((congrArg₂ (· * ·) hq hp).trans (loopOfHom_comp p q).symm))

private theorem retract_loop_inv
    {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))} [Arborescence T]
    (Y : Set ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ :
      Set (Quiver.Total (IsFreeGroupoid.Generators G))))
    {a b : G} (p : a ⟶ b)
    (hp : retractBasisElement (spanningTreeBasis T) Y
      (IsFreeGroupoid.SpanningTree.loopOfHom T p) =
        IsFreeGroupoid.SpanningTree.loopOfHom T p) :
    retractBasisElement (spanningTreeBasis T) Y
      (IsFreeGroupoid.SpanningTree.loopOfHom T (inv p)) =
        IsFreeGroupoid.SpanningTree.loopOfHom T (inv p) := by
  exact (congrArg (retractBasisElement (spanningTreeBasis T) Y) (loopOfHom_inv p)).trans
    ((retractBasisElement_inv (spanningTreeBasis T) Y _).trans
      ((congrArg Inv.inv hp).trans (loopOfHom_inv p).symm))

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
    exact (congrArg (fun z => retractBasisElement B Y z = z) hBx).mp
      (retractBasisElement_of_mem B Y x hxY)

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
      change retractBasisElement B Y (IsFreeGroupoid.SpanningTree.loopOfHom T (𝟙 _)) =
        IsFreeGroupoid.SpanningTree.loopOfHom T (𝟙 _)
      rw [loopOfHom_id]
      exact retractBasisElement_one B Y
  | cons p e ih =>
      cases e with
      | inl e =>
          exact retract_loop_comp Y (symPathHom p) (IsFreeGroupoid.of e) ih
            (basis_retraction_loop_of_edge P e (hp e))
      | inr e =>
          exact retract_loop_comp Y (symPathHom p) _ ih
            (retract_loop_inv Y (IsFreeGroupoid.of e)
              (basis_retraction_loop_of_edge P e (hp e)))

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
      change retractBasisElement B Y (IsFreeGroupoid.SpanningTree.loopOfHom T (𝟙 _)) =
        IsFreeGroupoid.SpanningTree.loopOfHom T (𝟙 _)
      rw [loopOfHom_id]
      exact retractBasisElement_one B Y
  | cons p e ih =>
      rcases e with ⟨e | e, heQ⟩
      · have heP : positiveEdgeOfSym (Sum.inl e) ∈ P := hQ (Sum.inl e) heQ
        have heP' : ⟨_, _, e⟩ ∈ P := heP
        exact retract_loop_comp Y (symPathHom (forgetSubquiverPath p))
          (IsFreeGroupoid.of e) ih (basis_retraction_loop_of_edge P e heP')
      · have heP : positiveEdgeOfSym (Sum.inr e) ∈ P := hQ (Sum.inr e) heQ
        have heP' : ⟨_, _, e⟩ ∈ P := heP
        exact retract_loop_comp Y (symPathHom (forgetSubquiverPath p)) _ ih
          (retract_loop_inv Y (IsFreeGroupoid.of e)
            (basis_retraction_loop_of_edge P e heP'))

end MarshallHall
