/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.DirectedUnitInterval
import LeanPool.DirectedTopologyLean4.UnitIntervalAux
import LeanPool.DirectedTopologyLean4.Fraction

/-!
# LeanPool.DirectedTopologyLean4.Dipath
-/

/-
  This file contains the definition of a dipath in a directed space:
  A path between two points paired with the proof that it is a dipath.
  The following dipath constructions are given:
  * refl : the constant dipath
  * trans : the concatenation of dipaths
  * map : the image of a dipath under a directed map
  * subparam : the monotonic subparametrization of a dipath
-/

noncomputable section

open DirectedMap Set
open scoped unitInterval

universe u
variable {X : Type u} [DirectedSpace X] {x y z : X}

/-- A dipath is a path together with a proof that that path "is a dipath" -/
structure Dipath (x y : X) extends Path x y where
  dipath_toPath : IsDipath toPath

instance : Coe (Dipath x y) (Path x y) := ⟨fun γ => γ.toPath⟩

namespace Dipath

lemma directed (γ : Dipath x y) : DirectedMap.Directed γ.toContinuousMap :=
  fun _ _ _ φ_dipath => isDipath_reparam φ_dipath γ.dipath_toPath

/-- Convert a dipath to its underlying directed map `D(I, X)`. -/
def toDirectedMap (γ : Dipath x y) : D(I,X) where
  toFun := γ.toFun
  continuous_toFun := γ.continuous_toFun
  directed_toFun := Dipath.directed γ

instance instFunLike : FunLike (Dipath x y) I X where
  coe := fun γ => γ.toFun
  coe_injective := fun γ γ' h => by
    obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := γ
    obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := γ'
    congr

instance directedMapClass : DirectedMapClass (Dipath x y) I X where
  map_continuous := fun γ => γ.continuous_toFun
  map_directed := fun γ => directed γ

end Dipath

@[ext]
protected lemma Dipath.ext : ∀ {γ₁ γ₂ : Dipath x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂ := by
  rintro ⟨⟨⟨x, h10⟩, h11, h12⟩, h13⟩ ⟨⟨⟨y, h20⟩, h21, h22⟩, h23⟩ rfl
  rfl

namespace Dipath

/-- Promote a path with a proof of directedness into a dipath. -/
def ofIsDipath {γ : Path x y} (hγ : IsDipath γ) : Dipath x y := {
  toPath := γ,
  dipath_toPath := hγ,
}

/-- An directed map from I to a directed space can be turned into a dipath -/
def ofDirectedMap (f : D(I,X)) : Dipath (f 0) (f 1) where
  toFun := f
  continuous_toFun := f.continuous_toFun
  source' := rfl
  target' := rfl
  dipath_toPath := DirectedUnitInterval.isDipath_of_isDipath_comp_id <|
    f.directed_toFun DirectedUnitInterval.IdentityPath DirectedUnitInterval.isDipath_identityPath

@[simp] lemma coe_mk (f : I → X) (h₀ h₁ h₂ h₃) : ⇑(mk ⟨⟨f, h₀⟩, h₁, h₂⟩ h₃ : Dipath x y) = f := rfl

variable (γ : Dipath x y)

@[continuity]
protected lemma continuous : Continuous γ :=
  γ.continuous_toFun

@[simp] protected lemma source : γ 0 = x :=
  γ.source'

@[simp] protected lemma target : γ 1 = y :=
  γ.target'

namespace simps

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def apply : I → X :=
  γ

end simps

initialize_simps_projections Dipath
  (toPath_toContinuousMap_toFun → simps.apply, -toPath_toContinuousMap)

lemma coe_toContinuousMap : ⇑γ.toContinuousMap = γ := rfl
@[simp]
lemma coe_toDirectedMap : ⇑γ.toDirectedMap = γ := rfl

/-- Any function `φ : Π (a : α), Dipath (x a) (y a)` can be seen as a function `α × I → X`. -/
instance hasUncurryDipath {X α : Type*} [DirectedSpace X] {x y : α → X} :
  Function.HasUncurry (∀ a : α, Dipath (x a) (y a)) (α × I) X :=
⟨fun φ p => φ p.1 p.2⟩


/-! ### Properites about the range of dipaths -/

@[simp] lemma coe_range (γ : Dipath x y) : range γ = range γ.toPath := rfl
lemma range_eq_image (γ : Dipath x y) : range γ = γ.extend '' I :=
  Set.ext (fun z =>
    ⟨fun ⟨t, ht⟩ => ⟨t, t.2, by
      simp only [Subtype.coe_prop, Path.extend_apply, Subtype.coe_eta]
      exact ht⟩,
    fun ⟨t, t_mem_I, ht⟩ => ⟨⟨t, t_mem_I⟩, by
      rw [ht.symm, Path.extend_apply γ.toPath t_mem_I]
      rfl⟩⟩)

lemma range_eq_image_I (γ : Dipath x y) : range γ = γ '' Icc 0 1 :=
  Set.ext (fun _ =>
    ⟨fun ⟨t, ht⟩ => ⟨t, t.2, ht⟩,
    fun ⟨t, t_mem_I, ht⟩ => ⟨⟨t, t_mem_I⟩, ht⟩⟩)

lemma image_extend_eq_image (γ : Dipath x y) (a b : I) :
    γ.extend '' Icc ↑a ↑b = γ '' Icc a b := by
  ext y
  constructor
  · rintro ⟨t, t_ab, ht⟩
    have ht_mem : t ∈ I := ⟨le_trans a.2.1 t_ab.1, le_trans t_ab.2 b.2.2⟩
    refine ⟨⟨t, ht_mem⟩, t_ab, ?_⟩
    rw [← ht, Path.extend_apply γ.toPath ht_mem]
    rfl
  · rintro ⟨t, t_ab, ht⟩
    refine ⟨t, t_ab, ?_⟩
    rw [← ht]
    convert Path.extend_apply γ.toPath ⟨le_trans a.2.1 t_ab.1, le_trans t_ab.2 b.2.2⟩
    rfl

/-! ### Reflexive dipaths -/

/-- The constant dipath from a point to itself -/
@[refl, simps!]
def refl (x : X) : Dipath x x where
  toPath := Path.refl x
  dipath_toPath := isDipath_constant x

lemma refl_range {a : X} : range (Dipath.refl a) = {a} := Path.refl_range

/-! ### Concatenation of dipaths -/

/-- Directed paths can be concatenated -/
@[trans] def trans (γ : Dipath x y) (γ' : Dipath y z) : Dipath x z :=
{
  γ.toPath.trans γ'.toPath with
  dipath_toPath := isDipath_concat γ.dipath_toPath γ'.dipath_toPath
}

@[simp] lemma trans_to_path (γ : Dipath x y) (γ' : Dipath y z) :
  γ.toPath.trans γ'.toPath = (γ.trans γ').toPath := by
  ext t
  rfl

lemma trans_apply (γ : Dipath x y) (γ' : Dipath y z) (t : I) : (γ.trans γ') t =
  if h : (t : ℝ) ≤ 1/2 then
    γ ⟨2 * t, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨t.2.1, h⟩⟩
  else
    γ' ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
Path.trans_apply (γ.toPath) (γ'.toPath) t

lemma trans_range (γ : Dipath x y) (γ' : Dipath y z) : range (γ.trans γ') = range γ ∪ range γ' :=
  Path.trans_range γ.toPath γ'.toPath

lemma trans_eval_at_half (γ : Dipath x y) (γ' : Dipath y z) :
    (γ.trans γ') (Fraction.ofPos two_pos) = y := by
  rw [Dipath.trans_apply]
  simp

/-! ### Mapping dipaths -/

/-- Image of a dipath from `x` to `y` by a directed map -/
def map (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] (f : D(X,Y)) : Dipath (f x) (f y) :=
{
  γ.toPath.map f.continuous_toFun with
  dipath_toPath := f.directed_toFun γ.toPath γ.dipath_toPath,
}

@[simp] lemma map_coe (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] (f : D(X,Y)) :
  (γ.map f : I → Y) = f ∘ γ :=
by { ext t; rfl }

@[simp] lemma map_trans (γ : Dipath x y) (γ' : Dipath y z) {Y : Type*} [DirectedSpace Y]
    (f : D(X,Y)) :
  (γ.trans γ').map f = (γ.map f).trans (γ'.map f) := by
  ext t
  rw [trans_apply, map_coe, Function.comp_apply, trans_apply]
  simp
  split_ifs <;> rfl

@[simp] lemma map_id (γ : Dipath x y) : γ.map (DirectedMap.id X) = γ := by { ext; rfl }

@[simp] lemma map_map (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] {Z : Type*} [DirectedSpace Z]
  (f : D(X,Y)) (g : D(Y,Z)) : (γ.map f).map g = γ.map (g.comp f) := by { ext; rfl }

/-! ### Casting dipaths -/

/-- Casting a dipath from `x` to `y` to a dipath from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) : Dipath x' y' :=
{ toFun := γ,
  continuous_toFun := γ.continuous,
  dipath_toPath := isDipath_cast γ.toPath hx hy γ.dipath_toPath,
  source' := by simp [hx],
  target' := by simp [hy]
}

lemma cast_apply (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) (t : I) :
  (γ.cast hx hy) t = γ t := rfl

@[simp] lemma trans_cast {X : Type*} [DirectedSpace X] {a₁ a₂ b₁ b₂ c₁ c₂ : X}
  (γ : Dipath a₂ b₂) (γ' : Dipath b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
  (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc := rfl

@[simp] lemma cast_coe (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  (γ.cast hx hy : I → X) = γ := rfl

lemma cast_range (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  range (γ.cast hx hy) = range γ := rfl

lemma cast_image (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) (a b : ℝ) :
  (γ.cast hx hy).extend '' Icc a b = γ.extend '' Icc a b := rfl

lemma dipath_of_directed_map_of_to_dimap (γ : Dipath x y) :
  Dipath.ofDirectedMap (γ.toDirectedMap) = γ.cast γ.source' γ.target' := by {ext t; rfl }

/-! ### Reparametrising a path -/

/-- Reparametrize a dipath by precomposing it with a directed self-map of the unit interval. -/
def subparam (γ : Dipath x y) (f : D(I,I)) : Dipath (γ (f 0)) (γ (f 1)) :=
{
  toFun := γ ∘ f
  continuous_toFun := by continuity
  source' := rfl
  target' := rfl
  dipath_toPath := by
      set p : Path (f 0) (f 1) :=
        { toFun := f,
          continuous_toFun := f.continuous_toFun,
          source' := rfl,
          target' := rfl
        }
      have p_mono : Monotone p := DirectedUnitInterval.monotone_of_directed f
      exact isDipath_reparam p_mono γ.dipath_toPath
}

lemma subparam_range (γ : Dipath x y) (f : D(I,I)) :
  range (γ.subparam f) ⊆ range γ := fun _ ⟨a, ha⟩ => ⟨f a, ha⟩

/-- Given a dipath `γ` and a dimap `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
dipath defined by `γ ∘ f`.
-/
def reparam (γ : Dipath x y) (f : D(I,I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  Dipath x y :=
(subparam γ f).cast (hf₀.symm ▸ γ.source.symm) (hf₁.symm ▸ γ.target.symm)

@[simp]
lemma coe_to_fun (γ : Dipath x y) (f : D(I,I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  ⇑(γ.reparam f hf₀ hf₁) = γ ∘ f := rfl

@[simp]
lemma reparam_id (γ : Dipath x y) : γ.reparam (DirectedMap.id I) rfl rfl = γ :=
by { ext; rfl }

lemma range_reparam (γ : Dipath x y) (f : D(I,I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  range (γ.reparam f hf₀ hf₁) = range γ :=
Path.range_reparam γ.toPath f.continuous_toFun hf₀ hf₁

variable {Y : Type*} [DirectedSpace Y] {x₀ x₁ : X} {y₀ y₁ : Y}

/-- Two dipaths together form a dipath in the product space -/
def dipathProduct (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath y₀ y₁) : Dipath (x₀, y₀) (x₁, y₁) where
  toFun := fun t => (γ₁ t, γ₂ t)
  source' := by simp
  target' := by simp
  dipath_toPath := by
      constructor
      { convert γ₁.dipath_toPath
        ext t
        rfl }
      { convert γ₂.dipath_toPath
        ext t
        rfl }

/-- Given a directed path in a product space, we can project it to its first coordinate to
obtain a directed path -/
def ofProductFst (γ : Dipath (x₀, y₀) (x₁, y₁)) : Dipath x₀ x₁ where
  toPath := γ.toPath.map continuous_fst
  dipath_toPath := γ.dipath_toPath.1

/-- Given a directed path in a product space, we can project it to its second coordinate to
obtain a directed path -/
def ofProductSnd (γ : Dipath (x₀, y₀) (x₁, y₁)) : Dipath y₀ y₁ where
  toPath := γ.toPath.map continuous_snd
  dipath_toPath := γ.dipath_toPath.2

end Dipath
