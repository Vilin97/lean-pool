/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Cases
import LeanPool.Frucht.ClassicalReplacements

/-!
# Choice-free graph lemmas

Reflexive-transitive-closure transport lemmas and the basic graph notions
(pointed graphs, graph isomorphisms) used to build the Cayley colored graphs
in the choice-free proof of Frucht's theorem.
-/

universe u v

open Function Relation

namespace ReflTransGen

variable {α β} {r : α → α → Prop} {p : β → β → Prop} {a b : α}

@[classical] lemma liftInjective
    {f : α → β} (inj : Injective f) (h : ∀ a b, p (f a) (f b) → r a b)
    (hrange : ∀ a b, p a b → a ∈ Set.range f → b ∈ Set.range f) (hab : ReflTransGen p (f a) (f b)) :
    ReflTransGen r a b := by
  set f_a := f a with hf_a
  set f_b := f b with hf_b
  clear_value f_a f_b
  induction hab using ReflTransGen.head_induction_on generalizing a with
  | refl =>
    rw [hf_a] at hf_b
    rw [inj hf_b]
  | @head f_a f_c hac hcb ih =>
    obtain ⟨c, hc⟩ := hrange _ _ hac ⟨a, hf_a.symm⟩
    rw [hf_a, ← hc] at hac
    exact .head (h _ _ hac) (ih hc.symm)

@[classical] lemma liftHom
    {s F} [FunLike F α β] [RelHomClass F r s] (f : F) (hab : ReflTransGen r a b) :
    ReflTransGen s (f a) (f b) :=
  ReflTransGen.lift f (fun _ _ => map_rel _) hab

end ReflTransGen

namespace SimpleGraph

@[classical] theorem pathGraph_rigid
    {n : ℕ} [NeZero n] (f : pathGraph n ≃g pathGraph n) (hf : f 0 = 0) : f = .refl := by
  ext ⟨i, hi⟩
  simp only [RelIso.refl_apply]
  revert hi
  induction i using Nat.strongRec with
  | _ i ih =>
    intro hi
    by_cases i_zero : i = 0
    · cases i_zero
      rw [Fin.ext_iff] at hf
      exact hf
    · obtain ⟨j, ⟨_⟩⟩ := Nat.exists_eq_add_one_of_ne_zero i_zero
      clear i_zero
      set p : Fin n := ⟨j, by omega⟩
      set q : Fin n := ⟨j + 1, hi⟩
      have adj : (pathGraph n).Adj p q := by simp [pathGraph_adj, p, q]
      replace adj := f.map_rel_iff.mpr adj
      simp only [pathGraph_adj] at adj
      obtain adj | adj := adj
      · rw [← adj, ih j (by simp)]
      · rw [ih j (by simp) (by omega)] at adj
        have := ih (f q) (by omega) (by omega)
        rw [← Fin.ext_iff, f.injective.eq_iff, Fin.ext_iff] at this
        conv_rhs at this => simp only [q]
        simp only at this
        omega

@[classical] def IsLeaf {α} (G : SimpleGraph α) (x : α) := ∃! y, G.Adj x y

variable {α : Type u} {β : Type v} {G : SimpleGraph α} {H : SimpleGraph β} (f : G ≃g H)

@[classical] lemma connected_exists_edge [Nontrivial α] (hconn : G.Connected) :
    ∀ x, ∃ y, G.Adj x y := by
  by_contra h
  simp only [not_forall, not_exists] at h
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, ne⟩ := exists_ne x
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_edist x y
  cases p with
  | nil => simp at ne
  | @cons _ _ _ hz => exact hx _ hz

@[classical] lemma Iso.map_leaf (u : α) : G.IsLeaf u ↔ H.IsLeaf (f u) := by
  simp only [IsLeaf]
  apply Equiv.existsUnique_congr f.toEquiv
  simp [Iso.map_adj_iff]

@[classical] def Iso.map_walk {u v : α} : G.Walk u v ≃ H.Walk (f u) (f v) where
  toFun := fun p => p.map f.toHom
  invFun := fun p => (p.map f.symm.toHom).copy (by simp) (by simp)
  left_inv := by
    simp only [LeftInverse, RelHom.coeFn_mk, Embedding.toFun_eq_coe, Embedding.coeFn_mk,
      RelIso.coe_fn_toEquiv, Walk.map_map]
    intro x
    convert_to (Walk.map Hom.id x).copy rfl rfl = x using 2 <;> (try congr 1; simp)
  right_inv := by
    simp only [RightInverse, LeftInverse, RelHom.coeFn_mk, Embedding.toFun_eq_coe,
      Embedding.coeFn_mk, RelIso.coe_fn_toEquiv, Walk.map_copy, Walk.map_map]
    intro x
    convert_to (Walk.map Hom.id x).copy rfl rfl = x using 2 <;> (try congr 1; simp)

@[classical] lemma Iso.map_neighborSet (u : α) :
    Set.BijOn f (G.neighborSet u) (H.neighborSet (f u)) := by
  rw [← RelIso.coe_fn_toEquiv, ← Equiv.image_eq_iff_bijOn,
    neighborSet, neighborSet, ← Equiv.setOf_apply_symm_eq_image_setOf,
    show (f.toEquiv.symm : _ → _) = f.symm from rfl, RelIso.coe_fn_toEquiv]
  congr 1 with y'
  conv_lhs => rw [show u = f.symm (f u) by simp, map_adj_iff]

end SimpleGraph

@[classical] structure PointedGraph (α : Type u) where
  p : α
  r : α → α → Prop

@[classical] structure PointedGraphIso {α β : Type*} (G : PointedGraph α) (H : PointedGraph β)
    extends RelIso G.r H.r where
  map_point' : toRelIso G.p = H.p

infix:25 " ≃· " => PointedGraphIso

namespace PointedGraphIso

variable {α β γ : Type*} {G : PointedGraph α} {H : PointedGraph β} {I : PointedGraph γ}

@[classical] instance : EquivLike (G ≃· H) α β where
  coe x := x.toRelIso
  inv x := x.toRelIso.symm
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  coe_injective' := fun
    | ⟨e₁, _⟩, ⟨e₂, _⟩, h, _ => by simpa using h

instance : RelHomClass (G ≃· H) G.r H.r where
  map_rel f _ _ := Iff.mpr f.map_rel_iff'

@[simp] lemma coe_fn_toEquiv (f : G ≃· H) : (f.toRelIso : α → β) = f :=
  rfl

@[classical] lemma map_point (f : G ≃· H) : f G.p = H.p := f.map_point'
@[classical] lemma map_rel_iff (f : G ≃· H) {a b} :
    H.r (f a) (f b) ↔ G.r a b := f.toRelIso.map_rel_iff

@[classical, ext] lemma ext ⦃f g : G ≃· H⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[classical, refl] def refl : G ≃· G := ⟨.refl G.r, by simp⟩
@[classical, symm] def symm (f : G ≃· H) : H ≃· G :=
  ⟨f.toRelIso.symm, by apply_fun f.toRelIso; simpa using f.map_point'.symm⟩
@[classical, trans] def trans (f : G ≃· H) (g : H ≃· I) : G ≃· I :=
  ⟨f.toRelIso.trans g.toRelIso, by simp [f.map_point', g.map_point']⟩

instance : Trans (@PointedGraphIso α β) (@PointedGraphIso β γ) PointedGraphIso where
  trans := trans

@[simp] lemma apply_symm_apply (f : G ≃· H) (x : β) : f (f.symm x) = x :=
  f.toEquiv.apply_symm_apply x

@[simp] lemma symm_apply_apply (f : G ≃· H) (x : α) : f.symm (f x) = x :=
  f.toEquiv.symm_apply_apply x

end PointedGraphIso

namespace PointedGraph

variable {α : Type u} {β : Type u} {G : PointedGraph α} {H : PointedGraph β} (f : G ≃· H)

@[classical] abbrev Rigid := Subsingleton (G ≃· G)

@[classical] def induce (x : α) : PointedGraph {y // ReflTransGen G.r x y} where
  p := ⟨x, .refl⟩
  r := fun x y => G.r x.val y.val

@[classical] def induceIso (x : α) : G.induce x ≃· H.induce (f x) where
  toFun := fun ⟨y, hy⟩ => ⟨f y, ReflTransGen.liftHom f hy⟩
  invFun := fun ⟨y, hy⟩ => ⟨f.symm y, by simpa using ReflTransGen.liftHom f.symm hy⟩
  left_inv := by simp [LeftInverse]
  right_inv := by simp [RightInverse, LeftInverse]
  map_rel_iff' := by
    simp only [PointedGraph.induce, Equiv.coe_fn_mk, Subtype.forall]
    intro y hy z hz
    apply RelIso.map_rel_iff
  map_point' := by simp [PointedGraph.induce]; congr 1

end PointedGraph

@[classical] structure RCPG (α : Type*) extends SimpleGraph α where
  p : α
  is_rigid' : Subsingleton {f : toSimpleGraph ≃g toSimpleGraph // f p = p}
  is_connected : toSimpleGraph.Connected


@[classical] structure RCPGIso {α β : Type*} (G : RCPG α) (H : RCPG β)
    extends G.toSimpleGraph ≃g H.toSimpleGraph where
  map_point' : toRelIso G.p = H.p

infix:25 " ≃p " => RCPGIso

@[classical] lemma RCPG.is_rigid {α} (G : RCPG α) : Subsingleton (G ≃p G) := by
  refine ⟨fun f g => ?_⟩
  have := G.is_rigid'.allEq ⟨f.toRelIso, f.map_point'⟩ ⟨g.toRelIso, g.map_point'⟩
  simp only [Subtype.ext_iff] at this
  cases f
  cases g
  simpa using this

namespace RCPGIso

variable {α β γ : Type*} {G : RCPG α} {H : RCPG β} {I : RCPG γ}

@[classical] instance : EquivLike (G ≃p H) α β where
  coe f := f.toRelIso
  inv f := f.toRelIso.symm
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  coe_injective' := fun
    | ⟨e₁, _⟩, ⟨e₂, _⟩, h, _ => by simpa using h

@[simp] lemma coe_fn_toEquiv (f : G ≃p H) : (f.toRelIso : α → β) = f := rfl

def Simps.apply (h : G ≃p H) : α → β := h
initialize_simps_projections RCPGIso (toFun → apply)

@[classical, refl, simps! apply] def refl : G ≃p G := ⟨.refl _, by simp⟩
@[classical, symm] def symm (f : G ≃p H) : H ≃p G :=
  ⟨f.toRelIso.symm, by apply_fun f.toRelIso; simpa using f.map_point'.symm⟩

@[classical, trans, simps! apply] def trans (f : G ≃p H) (g : H ≃p I) : G ≃p I :=
  ⟨f.toRelIso.trans g.toRelIso, by simp [f.map_point', g.map_point']⟩

instance : Trans (@RCPGIso α β) (@RCPGIso β γ) RCPGIso where
  trans := trans

@[classical] lemma map_point (f : G ≃p H) : f G.p = H.p := f.map_point'
@[classical, ext] lemma ext ⦃f g : G ≃p H⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[classical, simp] lemma symm_apply_apply (f : G ≃p H) (x : α) : f.symm (f x) = x :=
  f.toEquiv.symm_apply_apply x

@[classical, simp] lemma apply_symm_apply (f : G ≃p H) (x : β) : f (f.symm x) = x :=
  f.toEquiv.apply_symm_apply x

@[classical] lemma is_subsingleton : Subsingleton (G ≃p H) := by
  refine ⟨fun f g => ?_⟩
  have := congr_arg (trans · g) (G.is_rigid.allEq (f.trans g.symm) refl)
  simpa [RCPGIso.ext_iff] using this

end RCPGIso

def ColoredGraph α C := α → α → C

@[classical] structure ColoredGraphIso {α β C : Type*} (G : ColoredGraph α C) (H : ColoredGraph β C)
    extends α ≃ β where
  map_color' : ∀ {a b}, H (toEquiv a) (toEquiv b) = G a b
infix:25 " ≃c " => ColoredGraphIso

namespace ColoredGraphIso

variable {α β γ C : Type*} {G : ColoredGraph α C} {H : ColoredGraph β C} {I : ColoredGraph γ C}

@[classical] instance : EquivLike (G ≃c H) α β where
  coe x := x.toEquiv
  inv x := x.toEquiv.symm
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  coe_injective' := fun
    | ⟨e₁, _⟩, ⟨e₂, _⟩, h, _ => by simpa using h

@[classical, refl] def refl : G ≃c G := ⟨.refl α, by simp⟩
@[classical, symm] def symm (f : G ≃c H) : H ≃c G :=
  ⟨f.toEquiv.symm, fun {a b} => by
    simpa using f.map_color' (a := f.toEquiv.symm a) (b := f.toEquiv.symm b) |>.symm⟩
@[classical, trans] def trans (f : G ≃c H) (g : H ≃c I) : G ≃c I :=
  ⟨f.toEquiv.trans g.toEquiv, by simp [f.map_color', g.map_color']⟩

@[classical] lemma map_color (f : G ≃c H) : ∀ {x y}, H (f x) (f y) = G x y :=
  f.map_color'

@[classical, ext] lemma ext ⦃f g : G ≃c H⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[classical, simp] lemma symm_apply_apply (f : G ≃c H) (x : α) : f.symm (f x) = x :=
  f.toEquiv.symm_apply_apply x

@[classical, simp] lemma apply_symm_apply (f : G ≃c H) (x : β) : f (f.symm x) = x :=
  f.toEquiv.apply_symm_apply x

instance : Group (G ≃c G) where
  one := refl
  mul f₁ f₂ := f₂.trans f₁
  inv := symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel f := ext f.symm_apply_apply

@[simp] lemma mul_apply (f g : G ≃c G) (x : α) : (f * g) x = f (g x) := rfl

end ColoredGraphIso

def cayley (Γ : Type*) [Group Γ] : ColoredGraph Γ Γ := fun a b => a⁻¹ * b
def cayleyIso (Γ : Type*) [Group Γ] : (cayley Γ ≃c cayley Γ) ≃* Γ where
  toFun := fun x => x 1
  invFun := fun x => {
    toFun := fun y => x * y
    invFun := fun y => x⁻¹ * y
    left_inv := by simp [LeftInverse]
    right_inv := by simp [Function.RightInverse, LeftInverse]
    map_color' := by intro a b; simp [cayley]
  }
  left_inv := by
    intro f
    ext x
    have := f.map_color (x := 1) (y := x)
    simp [cayley, inv_mul_eq_iff_eq_mul] at this
    exact this.symm
  right_inv := mul_one
  map_mul' := by
    intro x y
    have := x.map_color (x := 1) (y := y 1)
    simpa [cayley, inv_mul_eq_iff_eq_mul] using this
