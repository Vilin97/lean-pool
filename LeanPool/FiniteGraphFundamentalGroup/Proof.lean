/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz
-/

import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

/-!
# The spanning-tree computation for finite quivers

This file builds the combinatorial fundamental group of a finite weakly connected quiver from
Mathlib's free groupoid and identifies a basis indexed by the edges outside a geodesic spanning
tree.
-/

attribute [local implicit_reducible]
  Quiver.Symmetrify IsFreeGroupoid.Generators
  WideSubquiver WideSubquiver.toType WideSubquiver.quiver IsFreeGroupoid.quiverGenerators
  Quiver.symmetrifyQuiver Quiver.wideSubquiverSymmetrify

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

universe u

namespace FiniteGraphFreeGroup

variable {V : Type u} [Quiver.{u} V]

/-- Identifies total arrows of a wide subquiver with their endpoints and underlying arrow. -/
def totalEquiv (T : WideSubquiver V) :
    Quiver.Total T ≃ Σ a : V, Σ b : V, {e : a ⟶ b // e ∈ T a b} where
  toFun e := ⟨e.left, e.right, ⟨e.hom.val, e.hom.property⟩⟩
  invFun e := ⟨e.1, e.2.1, ⟨e.2.2.1, e.2.2.2⟩⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-- The finite structure on the total arrows of a finite wide subquiver. -/
@[reducible]
noncomputable def totalFintype [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver V) : Fintype (Quiver.Total T) := by
  classical
  exact Fintype.ofEquiv _ (totalEquiv T).symm

noncomputable instance totalFintypeInst [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver V) : Fintype (Quiver.Total T) := totalFintype T

noncomputable instance wideSubquiverHomFintype
    [∀ a b : V, Fintype (a ⟶ b)] (T : WideSubquiver V) (a b : T) :
    Fintype (@Quiver.Hom T T.quiver a b) := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun e => e ∈ T a b) (by simp)

noncomputable instance wideSubquiverVertexFintype [Fintype V] (T : WideSubquiver V) :
    Fintype T :=
  Fintype.ofEquiv V (Equiv.refl _)

/-- Identifies total arrows of a quiver with their endpoints and arrow data. -/
def baseTotalEquiv (V : Type u) [Quiver.{u} V] :
    Quiver.Total V ≃ Σ a : V, Σ b : V, a ⟶ b where
  toFun e := ⟨e.left, e.right, e.hom⟩
  invFun e := ⟨e.1, e.2.1, e.2.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-- The finite structure on total arrows of a finite quiver. -/
@[reducible]
noncomputable def baseTotalFintype [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] :
    Fintype (Quiver.Total V) := by
  classical
  exact Fintype.ofEquiv _ (baseTotalEquiv V).symm

noncomputable instance baseTotalFintypeInst [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] :
    Fintype (Quiver.Total V) := baseTotalFintype

noncomputable instance symmetrifyFintype [Fintype V] : Fintype (Symmetrify V) :=
  Fintype.ofEquiv V (Equiv.refl _)

noncomputable instance symmetrifyHomFintype [∀ a b : V, Fintype (a ⟶ b)]
    (a b : Symmetrify V) :
    Fintype (@Quiver.Hom (Symmetrify V) (Quiver.symmetrifyQuiver V) a b) := by
  change Fintype ((@Quiver.Hom V _ a b) ⊕ (@Quiver.Hom V _ b a))
  infer_instance

/-- Identifies a wide subquiver's total arrows with the corresponding subset of base arrows. -/
def wideTotalEquiv {V : Type u} [Quiver.{u} V] (H : WideSubquiver V) :
    Quiver.Total H ≃ (wideSubquiverEquivSetTotal H : Set (Quiver.Total V)) where
  toFun e := ⟨⟨e.left, e.right, e.hom.val⟩, e.hom.property⟩
  invFun e := ⟨e.1.left, e.1.right, ⟨e.1.hom, e.2⟩⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

noncomputable instance wideSubquiverSetTotalFintype {V : Type u} [Quiver.{u} V]
    [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] (H : WideSubquiver V) :
    Fintype (wideSubquiverEquivSetTotal H : Set (Quiver.Total V)) :=
  Fintype.ofEquiv (Quiver.Total H) (wideTotalEquiv H)

lemma exists_last_data (T : WideSubquiver V) [Arborescence T]
    {b : T} (hb : b ≠ root T) :
    Nonempty (Σ a : T, Path (root T) a × (a ⟶ b)) := by
  let q : Path (root T) b := default
  cases q with
  | nil => exact False.elim (hb rfl)
  | cons p e => exact ⟨⟨_, p, e⟩⟩

/-- The penultimate vertex, prefix path, and last edge of the rooted path to a non-root vertex. -/
noncomputable def lastData (T : WideSubquiver V) [Arborescence T]
    (b : {b : T // b ≠ root T}) :
    Σ a : T, Path (root T) a × (a ⟶ b.1) :=
  Classical.choice (exists_last_data T (b := b.1) b.2)

lemma default_path_length_root (T : WideSubquiver V) [Arborescence T]
    (b : T) (h : b = root T) : (default : Path (root T) b).length = 0 := by
  cases h
  exact congrArg Path.length (Subsingleton.elim _ Path.nil)

lemma target_ne_root (T : WideSubquiver V) [Arborescence T]
    (e : Quiver.Total T) : e.right ≠ root T := by
  intro h
  let p : Path (root T) e.left := default
  have hp : (default : Path (root T) e.right) = p.cons e.hom := Subsingleton.elim _ _
  have hlen := congrArg Path.length hp
  have hzero := default_path_length_root T e.right h
  simp [p, hzero] at hlen

/-- Identifies the edges of an arborescence with its non-root vertices. -/
noncomputable def treeEdgeEquiv (T : WideSubquiver V) [Arborescence T] :
    Quiver.Total T ≃ {b : T // b ≠ root T} where
  toFun e := ⟨e.right, target_ne_root T e⟩
  invFun b :=
    let d := lastData T b
    ⟨d.1, b.1, d.2.2⟩
  left_inv e := by
    let b : {b : T // b ≠ root T} := ⟨e.right, target_ne_root T e⟩
    let d := lastData T b
    have hp : d.2.1.cons d.2.2 = (default : Path (root T) e.left).cons e.hom :=
      Subsingleton.elim _ _
    have hc := Path.cons.inj hp
    rcases hc with ⟨hab, hpath, hedge⟩
    exact Quiver.Total.ext hab rfl hedge
  right_inv b := by
    rfl

lemma arborescence_card [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver V) [Arborescence T] :
    Fintype.card (Quiver.Total T) = Fintype.card V - 1 := by
  classical
  rw [Fintype.card_congr (treeEdgeEquiv T)]
  rw [Fintype.card_subtype_compl]
  have hcard : Fintype.card T = Fintype.card V :=
    Fintype.card_congr (Equiv.refl V)
  rw [hcard]
  simp

lemma no_reverse_edges (T : WideSubquiver (Symmetrify V)) [Arborescence T]
    {a b : V} (e : @Quiver.Hom V _ a b)
    (h₁ : T a b (Sum.inl e)) (h₂ : T b a (Sum.inr e)) : False := by
  let A : Arborescence T := inferInstance
  let p : Path (root T) a := (A.uniquePath a).default
  let q : Path (root T) b := (A.uniquePath b).default
  let f : @Quiver.Hom T T.quiver a b := ⟨Sum.inl e, h₁⟩
  let g : @Quiver.Hom T T.quiver b a := ⟨Sum.inr e, h₂⟩
  have hpq : q = p.cons f :=
    (A.uniquePath b).uniq q |>.trans ((A.uniquePath b).uniq (p.cons f)).symm
  have hqp : p = q.cons g :=
    (A.uniquePath a).uniq p |>.trans ((A.uniquePath a).uniq (q.cons g)).symm
  have hpq_len : q.length = p.length + 1 := by
    simpa only [Path.length_cons] using congrArg Path.length hpq
  have hqp_len : p.length = q.length + 1 := by
    simpa only [Path.length_cons] using congrArg Path.length hqp
  omega

/-- Forgets the orientation tag on an edge of a symmetric wide subquiver. -/
def symEdgeForget (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total T) : Quiver.Total (wideSubquiverSymmetrify T) := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  cases f with
  | inl f => exact ⟨a, b, ⟨f, Or.inl hf⟩⟩
  | inr f => exact ⟨b, a, ⟨f, Or.inr hf⟩⟩

/-- Recovers the uniquely oriented tree edge from its underlying graph edge. -/
def symEdgeForgetInv (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total (wideSubquiverSymmetrify T)) : Quiver.Total T := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  change T a b (Sum.inl f) ∨ T b a (Sum.inr f) at hf
  by_cases h : T a b (Sum.inl f)
  · exact ⟨a, b, ⟨Sum.inl f, h⟩⟩
  · exact ⟨b, a, ⟨Sum.inr f, hf.resolve_left h⟩⟩

lemma symEdgeForgetInv_forget (T : WideSubquiver (Symmetrify V)) [Arborescence T]
    (e : Quiver.Total T) : symEdgeForgetInv T (symEdgeForget T e) = e := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  change V at a b
  cases f with
  | inl f =>
      simp only [symEdgeForget, symEdgeForgetInv]
      exact dite_eq_left hf
  | inr f =>
      have hn : ¬T b a (Sum.inl f) := fun h => no_reverse_edges T f h hf
      simp only [symEdgeForget, symEdgeForgetInv]
      exact dite_eq_right hn

lemma symEdgeForget_forgetInv (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total (wideSubquiverSymmetrify T)) :
    symEdgeForget T (symEdgeForgetInv T e) = e := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  change V at a b
  change T a b (Sum.inl f) ∨ T b a (Sum.inr f) at hf
  by_cases h : T a b (Sum.inl f)
  · have hinv : symEdgeForgetInv T ⟨a, b, ⟨f, hf⟩⟩ =
        ⟨a, b, ⟨Sum.inl f, h⟩⟩ := by
      simp only [symEdgeForgetInv]
      exact dite_eq_left h
    rw [hinv]
    simp [symEdgeForget]
  · have h' := hf.resolve_left h
    have hinv : symEdgeForgetInv T ⟨a, b, ⟨f, hf⟩⟩ =
        ⟨b, a, ⟨Sum.inr f, h'⟩⟩ := by
      simp only [symEdgeForgetInv]
      exact dite_eq_right h
    rw [hinv]
    simp [symEdgeForget]

/-- Equates oriented tree edges with the underlying edges of the symmetrified subquiver. -/
def symEdgeEquiv (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Quiver.Total T ≃ Quiver.Total (wideSubquiverSymmetrify T) where
  toFun := symEdgeForget T
  invFun := symEdgeForgetInv T
  left_inv := symEdgeForgetInv_forget T
  right_inv := symEdgeForget_forgetInv T

lemma symmetrified_tree_card [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Fintype.card (Quiver.Total (wideSubquiverSymmetrify T)) = Fintype.card V - 1 := by
  classical
  rw [← Fintype.card_congr (symEdgeEquiv T)]
  have hcard : Fintype.card (Symmetrify V) = Fintype.card V :=
    Fintype.card_congr (Equiv.refl V)
  simpa [hcard] using (arborescence_card T)

lemma symmetrified_tree_set_card [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Fintype.card (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T) :
      Set (Quiver.Total V)) = Fintype.card V - 1 := by
  rw [← Fintype.card_congr (wideTotalEquiv (wideSubquiverSymmetrify T))]
  exact symmetrified_tree_card T

private abbrev spanningRoot {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T] : G :=
  show T from root T

@[reducible]
private def spanningHomOfPath {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T] :
    ∀ {a : G}, Path (root T) a → (spanningRoot T ⟶ a)
  | _, Path.nil => 𝟙 _
  | _, Path.cons p f =>
      spanningHomOfPath T p ≫
        Sum.recOn f.val (fun e => IsFreeGroupoid.of e) fun e => inv (IsFreeGroupoid.of e)

@[reducible]
private def spanningTreeHom {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T]
    (a : G) : spanningRoot T ⟶ a :=
  spanningHomOfPath T default

private lemma spanningTreeHom_eq {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T]
    {a : G} (p : Path (root T) a) : spanningTreeHom T a = spanningHomOfPath T p := by
  rw [spanningTreeHom, Unique.default_eq]

@[simp]
private lemma spanningTreeHom_root {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T] :
    spanningTreeHom T (spanningRoot T) = 𝟙 _ := by
  rw [spanningTreeHom_eq T Path.nil]

@[reducible]
private def spanningLoopOfHom {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T]
    {a b : G} (p : a ⟶ b) : End (spanningRoot T) :=
  spanningTreeHom T a ≫ p ≫ inv (spanningTreeHom T b)

private lemma spanningLoopOfHom_eq_id {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T]
    {a b : IsFreeGroupoid.Generators G} (e : a ⟶ b)
    (h : e ∈ wideSubquiverSymmetrify T a b) :
    spanningLoopOfHom T (IsFreeGroupoid.of e) = 𝟙 (spanningRoot T) := by
  rw [spanningLoopOfHom, ← Category.assoc, IsIso.comp_inv_eq, Category.id_comp]
  rcases h with h | h
  · rw [spanningTreeHom_eq T (Path.cons default ⟨Sum.inl e, h⟩),
      spanningHomOfPath.eq_def]
  · rw [spanningTreeHom_eq T (Path.cons default ⟨Sum.inr e, h⟩),
      spanningHomOfPath.eq_def]
    simp only [IsIso.inv_hom_id, Category.comp_id, Category.assoc, spanningTreeHom]

@[reducible]
private def spanningFunctorOfMonoidHom {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T]
    {X : Type u} [Monoid X] (f : End (spanningRoot T) →* X) :
    G ⥤ CategoryTheory.SingleObj X where
  obj _ := ()
  map p := f (spanningLoopOfHom T p)
  map_id := by
    intro a
    dsimp only [spanningLoopOfHom]
    rw [Category.id_comp, IsIso.hom_inv_id]
    simpa only [CategoryTheory.End.one_def, id_as_one] using f.map_one
  map_comp := by
    intros
    rw [comp_as_mul, ← f.map_mul]
    simp only [IsIso.inv_hom_id_assoc, spanningLoopOfHom, CategoryTheory.End.mul_def,
      Category.assoc]

/-- The free-group basis obtained from the arrows outside a spanning tree. -/
noncomputable def spanningTreeBasis {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T] :
    FreeGroupBasis
      ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ : Set _)
      (End (show G from root T)) := by
  classical
  let X : Set _ := (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ
  apply FreeGroupBasis.ofUniqueLift X
    (fun e => spanningLoopOfHom T (IsFreeGroupoid.of e.val.hom))
  intro Y _ f
  let f' : Labelling (IsFreeGroupoid.Generators G) Y := fun a b e =>
    if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
  rcases IsFreeGroupoid.unique_lift f' with ⟨F', hF', uF'⟩
  refine ⟨F'.mapEnd _, ?_, ?_⟩
  · suffices ∀ {x y} (q : x ⟶ y), F'.map (spanningLoopOfHom T q) = (F'.map q : Y) by
      rintro ⟨⟨a, b, e⟩, h⟩
      simp only [Functor.mapEnd, DFunLike.coe, this, hF']
      exact dite_eq_right h
    intro x y q
    suffices ∀ {a} (p : Path (root T) a), F'.map (spanningHomOfPath T p) = 1 by
      simp only [this, spanningTreeHom, comp_as_mul, inv_as_inv, spanningLoopOfHom, inv_one,
        mul_one, one_mul, Functor.map_inv, Functor.map_comp]
    intro a p
    induction p with
    | nil => rw [spanningHomOfPath, F'.map_id, id_as_one]
    | cons p e ih =>
        rw [spanningHomOfPath, F'.map_comp, comp_as_mul, ih, mul_one]
        rcases e with ⟨e | e, eT⟩
        · rw [hF']
          exact dite_eq_left (Or.inl eT)
        · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
          exact dite_eq_left (Or.inr eT)
  · intro E hE
    ext x
    suffices (spanningFunctorOfMonoidHom T E).map x = F'.map x by
      simpa only [spanningLoopOfHom, spanningFunctorOfMonoidHom, IsIso.inv_id,
        spanningTreeHom_root, Category.id_comp, Category.comp_id] using! this
    congr
    apply uF'
    intro a b e
    change E (spanningLoopOfHom T _) = dite _ _ _
    split_ifs with h
    · rw [spanningLoopOfHom_eq_id T e h, ← CategoryTheory.End.one_def, E.map_one]
    · exact hE ⟨⟨a, b, e⟩, h⟩

instance freeGroupoidIsFree : IsFreeGroupoid (Quiver.FreeGroupoid V) where
  quiverGenerators :=
    ⟨fun a b => @Quiver.Hom V _ a.as b.as⟩
  of := fun {a b} e =>
    Quiver.FreeGroupoid.of V |>.map (show @Quiver.Hom V _ a.as b.as from e)
  unique_lift := by
    intro X _ f
    let f' : Labelling V X := fun {_ _} e =>
      f (a := (Quiver.FreeGroupoid.of V).obj _) (b := (Quiver.FreeGroupoid.of V).obj _) e
    let φ : V ⥤q CategoryTheory.SingleObj X :=
      { obj := fun _ => ()
        map := fun {_ _} e => f' e }
    refine ⟨Quiver.FreeGroupoid.lift φ, ?_, ?_⟩
    · intro a b e
      cases a
      cases b
      have h := Quiver.FreeGroupoid.lift_spec φ
      have hm := congrArg (fun ψ : V ⥤q CategoryTheory.SingleObj X => ψ.map e) h
      simpa [φ, f'] using! hm
    · intro F hF
      apply Quiver.FreeGroupoid.lift_unique φ F
      apply Prefunctor.ext
      · intro a b e
        exact hF ((Quiver.FreeGroupoid.of V).obj a) ((Quiver.FreeGroupoid.of V).obj b) e
      · intro a
        rfl

/-- A quiver with a finite hom-set between every ordered pair of vertices. -/
class FiniteQuiver (V : Type u) [Quiver.{u} V] where
  /-- The finite structure on each hom-set. -/
  finiteHom : ∀ a b : V, Fintype (@Quiver.Hom V _ a b)

@[reducible]
instance finiteHom {V : Type u} [Quiver.{u} V] [FiniteQuiver V] (a b : V) :
    Fintype (@Quiver.Hom V _ a b) :=
  FiniteQuiver.finiteHom (V := V) a b

/-- A quiver whose symmetrification has a path between every pair of vertices. -/
class WeaklyConnected (V : Type u) [Quiver.{u} V] : Prop where
  path : ∀ a b : V,
    Nonempty (@Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b)

instance rootedConnectedFree {V : Type u} [Quiver.{u} V]
    [WeaklyConnected V] (root : V) :
    @RootedConnected (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
      (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
      ((Quiver.FreeGroupoid.of V).obj root) where
  nonempty_path b := by
    rcases b with ⟨b⟩
    obtain ⟨p⟩ := WeaklyConnected.path root b
    induction p with
    | nil => exact ⟨Path.nil⟩
    | cons p e ih =>
        rcases e with e | e
        · exact ⟨ih.some.cons (show
              @Quiver.Hom (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
                (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
                {as := _} {as := _} from Sum.inl e)⟩
        · exact ⟨ih.some.cons (show
              @Quiver.Hom (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
                (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
                {as := _} {as := _} from Sum.inr e)⟩

/-- Identifies the objects of the generated free groupoid with graph vertices. -/
def generatorObjEquiv {V : Type u} [Quiver.{u} V] :
    IsFreeGroupoid.Generators (Quiver.FreeGroupoid V) ≃ V where
  toFun a := a.as
  invFun v := (Quiver.FreeGroupoid.of V).obj v
  left_inv a := by cases a; rfl
  right_inv v := rfl

noncomputable instance freeGroupoidObjFintype {V : Type u} [Quiver.{u} V]
    [Fintype V] : Fintype (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)) :=
  Fintype.ofEquiv V (generatorObjEquiv).symm

noncomputable instance freeGroupoidGeneratorHomFintype {V : Type u}
    [Quiver.{u} V] [FiniteQuiver V]
    (a b : IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)) :
    Fintype (a ⟶ b) := by
  change Fintype (@Quiver.Hom V _ a.as b.as)
  exact FiniteQuiver.finiteHom (V := V) a.as b.as

/-- The number of vertices in a finite graph. -/
def vertexCount {V : Type u} [Fintype V] : ℕ := Fintype.card V

/-- The total number of directed edges in a finite quiver. -/
def edgeCount {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V] : ℕ :=
  Fintype.card (Quiver.Total V)

/-- The graph cycle rank, written to account for truncated subtraction in `ℕ`.

The spanning-tree inequality below identifies it with `E - (V - 1)` for a weakly
connected graph. -/
abbrev cycleRank {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V] : ℕ :=
  edgeCount (V := V) + 1 - vertexCount (V := V)

/-- The endomorphism group at a root in the free groupoid generated by the graph. -/
abbrev graphFundamentalGroup {V : Type u} [Quiver.{u} V] (root : V) :=
  End ((Quiver.FreeGroupoid.of V).obj root)

/-- The canonical geodesic spanning tree rooted at the chosen graph vertex. -/
abbrev graphTree {V : Type u} [Quiver.{u} V]
    [WeaklyConnected V] (root : V) :
    WideSubquiver (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V))) :=
  @geodesicSubtree
    (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
    (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
    ((Quiver.FreeGroupoid.of V).obj root)
    (inferInstance : @RootedConnected
      (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
      (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
      ((Quiver.FreeGroupoid.of V).obj root))

noncomputable instance graphTreeArborescence {V : Type u} [Quiver.{u} V]
    [WeaklyConnected V] (root : V) :
    Arborescence (graphTree root) := by
  infer_instance

/-- Identifies total free-groupoid generator arrows with total graph arrows. -/
def generatorTotalEquiv {V : Type u} [Quiver.{u} V] :
    Quiver.Total (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)) ≃
      Quiver.Total V where
  toFun e := ⟨e.left.as, e.right.as, e.hom⟩
  invFun e := ⟨(Quiver.FreeGroupoid.of V).obj e.left,
    (Quiver.FreeGroupoid.of V).obj e.right, e.hom⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-- The complement of the geodesic tree, indexed by the actual non-tree generator arrows. -/
noncomputable def graphGeneratorSet {V : Type u} [Quiver.{u} V]
    [WeaklyConnected V] (root : V) :
    Set (Quiver.Total (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V))) :=
  (wideSubquiverEquivSetTotal
    (wideSubquiverSymmetrify (graphTree root)))ᶜ

noncomputable instance graphGeneratorSetFintype {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    Fintype (graphGeneratorSet root) := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun e => e ∈ graphGeneratorSet root) (by simp)

lemma graphGeneratorSet_card {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    Fintype.card (graphGeneratorSet root) =
      edgeCount (V := V) + 1 - vertexCount (V := V) := by
  classical
  let G := IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)
  let T := graphTree root
  let S : Set (Quiver.Total G) :=
    wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
  have hGcard : Fintype.card G = Fintype.card V :=
    Fintype.card_congr generatorObjEquiv
  have hS : Fintype.card S = Fintype.card V - 1 := by
    have hS' := symmetrified_tree_set_card T
    rw [hGcard] at hS'
    simpa [S, T] using hS'
  have htotal : Fintype.card (Quiver.Total G) = Fintype.card (Quiver.Total V) :=
    Fintype.card_congr generatorTotalEquiv
  have hcomp : Fintype.card (Sᶜ : Set (Quiver.Total G)) =
      Fintype.card (Quiver.Total G) - Fintype.card S := by
    exact Fintype.card_subtype_compl (fun e : Quiver.Total G => e ∈ S)
  have htreele : Fintype.card S ≤ Fintype.card (Quiver.Total G) := by
    exact Fintype.card_subtype_le _
  have htreele' : Fintype.card V - 1 ≤ Fintype.card (Quiver.Total V) := by
    rw [← hS, ← htotal]
    exact htreele
  have hVpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  calc
    Fintype.card (graphGeneratorSet root) =
        Fintype.card (Sᶜ : Set (Quiver.Total G)) := Fintype.card_congr (Equiv.refl _)
    _ = edgeCount (V := V) + 1 - vertexCount (V := V) := by
      rw [hcomp, htotal, hS]
      change Fintype.card (Quiver.Total V) - (Fintype.card V - 1) =
        Fintype.card (Quiver.Total V) + 1 - Fintype.card V
      omega

/-! The final theorem is kept in the original statement form for the Palomar
    Challenge/Solution correspondence.  The reusable, basis-valued API and
    the consequences of the computation live in `Consequences.lean`. -/

theorem proved_graph_fundamental_group_free_rank {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    Nonempty (graphFundamentalGroup root ≃*
      FreeGroup (Fin (edgeCount (V := V) + 1 - vertexCount (V := V)))) := by
  classical
  let B : FreeGroupBasis (graphGeneratorSet root) (graphFundamentalGroup root) := by
    simpa [graphGeneratorSet] using! (spanningTreeBasis (graphTree root))
  have hcard := graphGeneratorSet_card root
  let eX : graphGeneratorSet root ≃
      Fin (edgeCount (V := V) + 1 - vertexCount (V := V)) :=
    hcard ▸ Fintype.equivFin (graphGeneratorSet root)
  exact ⟨(B.reindex eX).repr⟩

end FiniteGraphFreeGroup
