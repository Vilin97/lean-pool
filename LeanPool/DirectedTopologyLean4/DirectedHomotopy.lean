/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.SplitPath.SplitDipath
import LeanPool.DirectedTopologyLean4.StretchPath

/-
  This file contains the definitions of three type of directed homotopies:
  * `Dihomotopy f g` : the type of homotopies between two directed maps `f g : D(X,Y)`.
  * `Dihomotopy_with f g P` : the type of homotopies between two directed maps `f g
      : D(X,Y)` satisfying `P : D(X,Y) → Prop` at all intermediate point `t : I`.
  * `Dihomotopy_rel f g S` : the type of homotopies between two directed maps `f g
      : D(X,Y)` that are fixed on all points of `S : set X`.

  The structure of this file is based on the undirected variant in Mathlib, found at:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Homotopy/Basic.lean
-/

noncomputable section

namespace DirectedMap

open DirectedMap DirectedUnitInterval
open unitIAux
open scoped unitInterval


universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [DirectedSpace X] [DirectedSpace Y] [DirectedSpace Z]

/-- `DirectedMap.Dihomotopy f₀ f₁` is the type of directed homotopies from `f₀` to `f₁`. -/
structure Dihomotopy (f₀ f₁ : DirectedMap X Y) extends D((I × X),Y) where
  map_zero_left : ∀ x, toFun (0, x) = f₀.toFun x
  map_one_left : ∀ x, toFun (1, x) = f₁.toFun x

/-- `DirectedMap.DihomotopyLike F f₀ f₁` states that `F` is a type of homotopies between `f₀` and
`f₁` -/
class DihomotopyLike {X Y : outParam (Type*)} [DirectedSpace X] [DirectedSpace Y]
    (F : Type*) (f₀ f₁ : outParam <| D(X,Y)) [FunLike F (I × X) Y]
    : Prop extends DirectedMapClass F (I × X) Y where
  map_zero_left (f : F) : ∀ x, f (0, x) = f₀ x
  map_one_left (f : F) : ∀x, f (1, x) = f₁ x

namespace Dihomotopy

variable {f₀ f₁ : D(X,Y)}

instance instFunLike : FunLike (Dihomotopy f₀ f₁) (I × X) Y where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

instance : DihomotopyLike (Dihomotopy f₀ f₁) f₀ f₁ where
  map_continuous f := f.continuous_toFun
  map_directed f := f.directed_toFun
  map_zero_left f := f.map_zero_left
  map_one_left f := f.map_one_left

@[ext] theorem ext {f g : Dihomotopy f₀ f₁} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

namespace Simps

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def apply (F : Dihomotopy f₀ f₁) : I × X → Y := F

end Simps

initialize_simps_projections Dihomotopy (toDirectedMap_toContinuousMap_toFun → apply,
    -toDirectedMap_toContinuousMap)

@[simp] lemma apply_zero (F : Dihomotopy f₀ f₁) (a : X) : F (0, a) = f₀ a := F.map_zero_left a
@[simp] lemma apply_one (F : Dihomotopy f₀ f₁) (a : X) : F (1, a) = f₁ a := F.map_one_left a
@[simp] lemma coe_to_continuous_map (F : Dihomotopy f₀ f₁) : ⇑F.toContinuousMap = F := rfl
@[simp] lemma coe_to_directed_map (F : Dihomotopy f₀ f₁) : ⇑F.toDirectedMap = F := rfl

/-- Currying a dihomotopy to a map fron `I` to `D(X,Y)`.
-/
def curry (F : Dihomotopy f₀ f₁) : I → D(X,Y) := by
  intro t
  exact DirectedMap.prod_const_fst ↑F t

@[simp]
lemma curry_apply (F : Dihomotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x) := rfl

/-- Currying a dihomotopy to a map fron `X` to `D(I,Y)`.
-/
def curry_snd (F : Dihomotopy f₀ f₁) : X → D(I,Y) := by
  intro x
  exact DirectedMap.prod_const_snd ↑F x

@[simp]
lemma curry_snd_apply (F : Dihomotopy f₀ f₁) (x : X) (t : I) : F.curry_snd x t = F (t, x) := rfl

/-- Promote a continuous-map homotopy together with a proof of directedness to a dihomotopy. -/
def hom_to_dihom (F : ContinuousMap.Homotopy (↑f₀ : C(X, Y)) ↑f₁) (HF : Directed (F : C(I × X, Y)))
    :
  Dihomotopy f₀ f₁ where
    toFun := F.toFun
    continuous_toFun := F.continuous_toFun
    directed_toFun := HF
    map_zero_left := F.map_zero_left
    map_one_left := F.map_one_left

/-- Forget the directedness of a dihomotopy to obtain the underlying continuous-map homotopy. -/
def dihom_to_hom (F : Dihomotopy f₀ f₁) : ContinuousMap.Homotopy (f₀ : C(X, Y)) ↑f₁ where
  toFun := F.toFun
  continuous_toFun := F.continuous_toFun
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left

instance coe_dihom_to_hom : Coe (Dihomotopy f₀ f₁) (ContinuousMap.Homotopy (f₀ : C(X, Y)) ↑f₁) :=
  ⟨fun F => F.dihom_to_hom⟩

/-! Evaluating dihomotopies at intermidiate points -/

/-- Evaluating a dipath homotopy at an intermediate point in the left coordinate, giving us a
`dipath`.
-/
def eval_at_left {f g : D(I,X)} (F : Dihomotopy f g) (t : I) : Dipath (F (t, 0)) (F (t, 1)) where
  toFun := F.curry t
  source' := by simp
  target' := by simp
  dipath_toPath := DirectedUnitInterval.isDipath_of_isDipath_comp_id
    <| (F.curry t).directed_toFun DirectedUnitInterval.IdentityPath
      DirectedUnitInterval.isDipath_identityPath

/-- Given a dihomotopy H: f ∼ g, get the dipath traced by the point `x` as it moves from
`f x` to `g x`
-/
def eval_at_right {X : Type*} {Y : Type*} [DirectedSpace X] [DirectedSpace Y] {f g : D(X,Y)}
  (H : DirectedMap.Dihomotopy f g) (x : X) : Dipath (f x) (g x) where
    toFun := fun t => H (t, x)
    source' := H.apply_zero x
    target' := H.apply_one x
    dipath_toPath := by
        convert H.directed_toFun { toFun := fun t => (t, x), source' := rfl, target' := rfl}
          ⟨DirectedUnitInterval.isDipath_identityPath, isDipath_constant _⟩ <;> simp

/-- Given a directed map `f`, we can define a `Dihomotopy f f` by `F (t, x) = f x`
-/
lemma directed_refl (f : D(X,Y))
    : Directed (↑(ContinuousMap.Homotopy.refl (↑f : C(X, Y))) : C(I × X, Y)) :=
  fun _ _ γ γ_dipath =>
    (f.directed_toFun (γ.map continuous_snd) (directed_snd.directed_toFun γ γ_dipath))

/-- The trivial reflexive dihomotopy `F (t, x) = f x`. -/
@[simps!]
def refl (f : D(X,Y)) : Dihomotopy f f := hom_to_dihom _ (directed_refl f)

instance : Inhabited (Dihomotopy (DirectedMap.id X) (DirectedMap.id X)) := ⟨Dihomotopy.refl _⟩

/- Note: there is no `Dihomotopy.symm`, as paths generally cannot be reversed -/

/- Auxiliary functions to prove that homotopy.trans is directed if the given homotopies are directed
-/

open SplitPath SplitDipath

variable {t₀ t₁ : I} (γ : Dipath t₀ t₁) {T : I}
variable (hT : γ T = half_I)

/-- The first half of a split dipath, stretched to the interval `[2 t₀, 1]`. -/
def FirstPartStretch (ht₀ : (t₀ : ℝ) ≤ 2⁻¹) : Dipath (⟨2 * (t₀.1 : ℝ), double_mem_I ht₀⟩ : I)
    (1 : I) where
  toFun := Dipath.stretch_up (FirstPart γ T) (by { convert le_refl (2⁻¹ : ℝ); simp [hT] })
  source' := by simp
  target' := by simp [hT]
  dipath_toPath := Dipath.isDipath_stretch_up (_) (by { convert le_refl (2⁻¹ : ℝ); simp [hT] })

/-- The second half of a split dipath, stretched to the interval `[0, 2 t₁ - 1]`. -/
def SecondPartStretch (ht₁ : 2⁻¹ ≤ (t₁ : ℝ)) : Dipath (0 : I) ⟨2 * (t₁.1 : ℝ)
    - 1, double_sub_one_mem_I ht₁⟩ where
  toFun := Dipath.stretch_down (SecondPart γ T) (by { convert le_refl (2⁻¹ : ℝ); simp [hT] })
  source' := by simp [hT]
  target' := by simp
  dipath_toPath := Dipath.isDipath_stretch_down (_) (by { convert le_refl (2⁻¹ : ℝ); simp [hT] })


variable {f₂ : D(X,Y)} (F : Dihomotopy f₀ f₁) (G : Dihomotopy f₁ f₂) (t : I) (x : X)

lemma trans_apply_half_left (ht : t = half_I) : (dihom_to_hom F).trans (dihom_to_hom G) (t, x)
    = F (1, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  have ht_coe : (t : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr ht
  have : (t : ℝ) ≤ 2⁻¹ := by linarith
  simp [this]
  simp [ht_coe]

lemma trans_apply_half_right (ht : t = half_I) : (dihom_to_hom F).trans (dihom_to_hom G) (t, x)
    = G (0, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  have ht_coe : (t : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr ht
  split_ifs <;> simp [ht_coe]

lemma trans_apply_left (t : I) (x : X) (ht : (t : ℝ) ≤ 2⁻¹) :
  (dihom_to_hom F).trans (dihom_to_hom G) (t, x) = F (⟨2 * t, double_mem_I ht⟩, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  simp [ht]
  rfl

lemma trans_apply_right (t : I) (x : X) (ht : 2⁻¹ ≤ (t : ℝ)) :
  (dihom_to_hom F).trans (dihom_to_hom G) (t, x) = G (⟨2 * t - 1, double_sub_one_mem_I ht⟩, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  simp only [one_div]
  split_ifs
  {
    have : (t : ℝ) = 2⁻¹ := by linarith
    simp [this]
  }
  rfl

lemma trans_first_case {a₀ a₁ : I × X} {γ : Path a₀ a₁} (γ_dipath : IsDipath γ)
    (ht₁ : (a₁.1 : ℝ) ≤ 2⁻¹) :
  IsDipath (γ.map ((dihom_to_hom F).trans (dihom_to_hom G)).continuous_toFun) := by
  obtain ⟨t₀, x₀⟩ := a₀
  obtain ⟨t₁, x₁⟩ := a₁
  set Γ := (dihom_to_hom F).trans (dihom_to_hom G) with Γ_def
  set γ_as_dipath := Dipath.of_isDipath γ_dipath
  set γ₁ := γ_as_dipath.of_product_fst
  set γ₂ := γ_as_dipath.of_product_snd
  set p := Dipath.dipath_product (Dipath.stretch_up γ₁ ht₁) γ₂ with p_def
  set p' := p.map (↑F : D(I × X, Y)) with p'_def
  have h : ∀ (t : I) (x : X), (ht : (t : ℝ) ≤ 2⁻¹) → Γ (t, x)
      = F (⟨2 * (t : ℝ), double_mem_I ht⟩, x) := by
    intros t x ht
    rw [Γ_def]
    rw [ContinuousMap.Homotopy.trans_apply (dihom_to_hom F) (dihom_to_hom G) (t, x)]
    simp [ht]
    rfl
  have : (t₀ : ℝ) ≤ 2⁻¹ := by
    have h_le : t₀ ≤ t₁ := directed_path_source_le_target γ_dipath.1
    exact le_trans (Subtype.coe_le_coe.mpr h_le) ht₁
  convert (p'.cast (h t₀ x₀ this) (h t₁ x₁ ht₁)).dipath_toPath
  ext
  simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.Homotopy.coe_toContinuousMap, Path.map_coe,
    Function.comp_apply, DirectedMap.coe_coe]
  exact h _ _ (le_trans (directed_path_bounded γ_dipath.1 _).2 ht₁)

lemma trans_second_case {a₀ a₁ : I × X} {γ : Path a₀ a₁} (γ_dipath : IsDipath γ)
    (ht₀ : 2⁻¹ ≤ (a₀.1 : ℝ)) :
  IsDipath (γ.map ((dihom_to_hom F).trans (dihom_to_hom G)).continuous_toFun) := by
  obtain ⟨t₀, x₀⟩ := a₀
  obtain ⟨t₁, x₁⟩ := a₁
  set Γ := (dihom_to_hom F).trans (dihom_to_hom G) with Γ_def
  set γ_as_dipath := Dipath.of_isDipath γ_dipath
  set γ₁ := γ_as_dipath.of_product_fst
  set γ₂ := γ_as_dipath.of_product_snd
  set p := Dipath.dipath_product (Dipath.stretch_down γ₁ ht₀) γ₂ with p_def
  set p' := p.map (↑G : D(I × X, Y)) with p'_def
  have h : ∀ (t : I) (x : X), (ht : (2⁻¹ : ℝ) ≤ ↑t) →
    Γ (t, x) = G (⟨2 * (t : ℝ) - 1, double_sub_one_mem_I ht⟩, x) := by
    intros t x ht
    rw [Γ_def]
    rw [ContinuousMap.Homotopy.trans_apply (dihom_to_hom F) (dihom_to_hom G) (t, x)]
    split_ifs with ht'
    · simp at ht'
      have : ↑t = (2⁻¹ : ℝ) := by linarith
      simp [this]
    · rfl
  have : 2⁻¹ ≤ (t₁ : ℝ) := by
    have h_le : t₀ ≤ t₁ := directed_path_source_le_target γ₁.dipath_toPath
    exact le_trans ht₀ (Subtype.coe_le_coe.mpr h_le)
  convert (p'.cast (h t₀ x₀ ht₀) (h t₁ x₁ this)).dipath_toPath
  ext
  simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.Homotopy.coe_toContinuousMap, Path.map_coe,
    Function.comp_apply, DirectedMap.coe_coe]
  exact h _ _ (le_trans ht₀ (directed_path_bounded γ_dipath.1 _).1)

/-- Given `Dihomotopy f₀ f₁` and `Dihomotopy f₁ f₂`, we can define a `Dihomotopy f₀ f₂` by putting
the first dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`. -/
def trans {f₂ : D(X,Y)} (F : Dihomotopy f₀ f₁) (G : Dihomotopy f₁ f₂) : Dihomotopy f₀ f₂ := by
  set Fₕ := dihom_to_hom F
  set Gₕ := dihom_to_hom G
  set Γ := Fₕ.trans Gₕ
  apply hom_to_dihom Γ
  rintro ⟨t₀, x₀⟩ ⟨t₁, x₁⟩ γ γ_dipath
  set γ_as_dipath := Dipath.of_isDipath γ_dipath
  set γ₁ := γ_as_dipath.of_product_fst
  set γ₂ := γ_as_dipath.of_product_snd
  by_cases ht₁ : (↑t₁ : ℝ) ≤ 2⁻¹
  ·  -- The entire path falls in the domain of F
    exact trans_first_case F G γ_dipath ht₁
  by_cases ht₀ : (↑t₀ : ℝ) < 2⁻¹
  swap
  · -- The entire path falls in the domain of G
    have ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀ := by linarith
    exact trans_second_case F G γ_dipath ht₀
  · -- Complicated
    push Not at ht₁
    obtain ⟨T, hT⟩ := has_T_half (γ.map continuous_fst) ht₀ ht₁
    obtain ⟨hT₀, ⟨hT₁, hT_half⟩⟩ := hT
    /- Split γ into two parts (one with image in [0, 2⁻¹] × X, the other with image in [2⁻¹, 1] × X)
    -/
    set a₁ := SplitDipath.FirstPart γ_as_dipath T
    set a₂ := SplitDipath.SecondPart γ_as_dipath T
    /- Create two new paths, where the first coordinate is stretched and the second coordinate
    remains the same -/
    set p₁ := FirstPartStretch γ₁ hT_half (le_of_lt ht₀)
    set p₂ := SecondPartStretch γ₁ hT_half (le_of_lt ht₁)
    set p₁' := SplitDipath.FirstPart γ₂ T
    set p₂' := SplitDipath.SecondPart γ₂ T
    set q₁ := (Dipath.dipath_product p₁ p₁').map F.toDirectedMap
    set q₂ := (Dipath.dipath_product p₂ p₂').map G.toDirectedMap
    set φ := SplitDipath.trans_reparam_map hT₀ hT₁
    have φ₀ : φ 0 = 0 := Subtype.ext (SplitPath.trans_reparam_zero T)
    have φ₁ : φ 1 = 1 := Subtype.ext (SplitPath.trans_reparam_one hT₁)
    have hγT_eq_half : ((γ T).1 : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr hT_half
    have hγT_le_half : ((γ T).1 : ℝ) ≤ 2⁻¹ := le_of_eq hγT_eq_half
    set r₁ := q₁.cast (trans_apply_left F G t₀ x₀ (le_of_lt ht₀))
        (trans_apply_half_left F G (γ T).1 (γ T).2 hT_half)
    set r₂ := q₂.cast (trans_apply_half_right F G (γ T).1 (γ T).2 hT_half)
        (trans_apply_right F G t₁ x₁ (le_of_lt ht₁))
    convert ((r₁.trans r₂).reparam φ φ₀ φ₁).dipath_toPath
    ext t
    have hr₁a₁ : r₁.toPath = a₁.toPath.map Γ.continuous_toFun := by
      ext x
      have h₀ : ((a₁ x).1 : ℝ) ≤ 2⁻¹
          := le_trans (directed_path_bounded a₁.dipath_toPath.1 _).2 hγT_le_half
      have : (1/2 : ℝ) = 2⁻¹ := by norm_num
      calc r₁ x
        _ = F (⟨2 * ((a₁ x).1 : ℝ), double_mem_I h₀⟩, (a₁ x).2) := rfl
        _ = if h : ((a₁ x).1 : ℝ) ≤ 1/2
            then F (⟨2 * ((a₁ x).1 : ℝ), double_mem_I (by linarith)⟩, (a₁ x).2)
            else G (⟨2 * ((a₁ x).1 : ℝ) - 1,
                double_sub_one_mem_I (le_of_lt (by linarith [not_le.mp h]))⟩, (a₁ x).2)
                  := by simp [h₀, this]
        _ = if h : ((a₁ x).1 : ℝ) ≤ 1/2
            then Fₕ (⟨2 * ((a₁ x).1 : ℝ), double_mem_I (by linarith)⟩, (a₁ x).2)
            else Gₕ (⟨2 * ((a₁ x).1 : ℝ) - 1,
                double_sub_one_mem_I (le_of_lt (by linarith [not_le.mp h]))⟩, (a₁ x).2)
                  := rfl
        _ = (Fₕ.trans Gₕ) (a₁ x) := (ContinuousMap.Homotopy.trans_apply Fₕ Gₕ (a₁ x)).symm
        _ = Γ (a₁ x) := rfl
        _ = (a₁.toPath.map Γ.continuous_toFun) x := rfl
    have hr₂a₂ : r₂.toPath = a₂.toPath.map Γ.continuous_toFun := by
      ext x
      have : 2⁻¹ ≤ ((a₂ x).1 : ℝ) := by
        calc (2⁻¹ : ℝ)
            _ = ↑(γ T).1 := Subtype.coe_inj.mpr hT_half.symm
            _ ≤ ↑(a₂ x).1 := (directed_path_bounded a₂.dipath_toPath.1 _).1
      calc r₂.toPath x
        _ = G (⟨2 * ((a₂ x).1 : ℝ) - 1, double_sub_one_mem_I this⟩, (a₂ x).2) := rfl
        _ = if h : ((a₂ x).1 : ℝ) ≤ 1/2
                then F (⟨2 * ((a₂ x).1 : ℝ), double_mem_I (by linarith)⟩, (a₂ x).2)
                else G (⟨2 * ((a₂ x).1 : ℝ) - 1,
                    double_sub_one_mem_I (le_of_lt (by linarith [not_le.mp h]))⟩, (a₂ x).2)
              := by
                split_ifs with h
                · have : ((a₂ x).1 : ℝ) ≤ 2⁻¹ := by convert h using 1; norm_num
                  have ha₂x : ((a₂ x).1 : ℝ) = 2⁻¹ := by linarith
                  have : G (0, _) = F (1, _) := Eq.trans (G.map_zero_left (a₂ x).2)
                      (F.map_one_left (a₂ x).2).symm
                  convert this <;> rw [ha₂x] <;> norm_num
                · rfl
        _ = if h : ((a₂ x).1 : ℝ) ≤ 1/2
                then Fₕ (⟨2 * ((a₂ x).1 : ℝ), double_mem_I (by linarith)⟩, (a₂ x).2)
                else Gₕ (⟨2 * ((a₂ x).1 : ℝ) - 1,
                    double_sub_one_mem_I (le_of_lt (by linarith [not_le.mp h]))⟩, (a₂ x).2)
              := rfl
        _ = (Fₕ.trans Gₕ) (a₂ x) := (ContinuousMap.Homotopy.trans_apply Fₕ Gₕ (a₂ x)).symm
        _ = Γ (a₂ x) := rfl
        _ = (a₂.toPath.map Γ.continuous_toFun) x := rfl
    calc (Γ ∘ γ) t
        _ = Γ (γ t) := rfl
        _ = Γ (((a₁.trans a₂).reparam φ φ₀ φ₁) t)
            := by { rw [←SplitDipath.first_trans_second_reparam_eq_self γ_as_dipath hT₀ hT₁]; rfl }
        _ = ((a₁.trans a₂).toPath.map Γ.continuous_toFun).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := by rfl
        _ = ((a₁.toPath.trans a₂.toPath).map Γ.continuous_toFun).reparam φ φ.continuous_toFun
              φ₀ φ₁ t := by rfl
        _ = ((a₁.toPath.map Γ.continuous_toFun).trans
              (a₂.toPath.map Γ.continuous_toFun)).reparam φ φ.continuous_toFun φ₀ φ₁ t := by
            rw [Path.map_trans a₁.toPath a₂.toPath (Γ.continuous_toFun)]
        _ = (r₁.toPath.trans r₂.toPath).reparam φ φ.continuous_toFun φ₀ φ₁ t := by
              rw [hr₁a₁, hr₂a₂]
              rfl
        _ = (r₁.trans r₂).reparam φ φ₀ φ₁ t := rfl

lemma trans_apply {f₀ f₁ f₂ : D(X,Y)} (F : Dihomotopy f₀ f₁) (G : Dihomotopy f₁ f₂) (x : I × X) :
  (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) := by
  have : ((dihom_to_hom F).trans (dihom_to_hom G)) x = (F.trans G) x := rfl
  rw [←this]
  exact ContinuousMap.Homotopy.trans_apply _ _ x

/-- Casting a `Dihomotopy f₀ f₁` to a `Dihomotopy g₀ g₁` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : D(X,Y)} (F : Dihomotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
  Dihomotopy g₀ g₁ where
    toFun := F
    directed_toFun := F.directed_toFun
    map_zero_left := by simp [←h₀]
    map_one_left := by simp [←h₁]

/-- Horizontal composition for `ContinuousMap.Homotopy`. -/
private def Homotopy.hcomp' {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)}
    (F : ContinuousMap.Homotopy f₀ f₁) (G : ContinuousMap.Homotopy g₀ g₁) :
    ContinuousMap.Homotopy (g₀.comp f₀) (g₁.comp f₁) where
  toFun := fun p => G (p.1, F p)
  continuous_toFun := by
    apply Continuous.comp G.continuous_toFun
    exact (continuous_fst).prodMk F.continuous_toFun
  map_zero_left := by intro x; simp
  map_one_left := by intro x; simp

/-- If we have a `Dihomotopy f₀ f₁` and a `Dihomotopy g₀ g₁`, then we can compose them and get a
`Dihomotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
@[simps!]
def hcomp {f₀ f₁ : D(X,Y)} {g₀ g₁ : D(Y,Z)} (F : Dihomotopy f₀ f₁) (G : Dihomotopy g₀ g₁) :
  Dihomotopy (g₀.comp f₀) (g₁.comp f₁) := by
  set Fₕ := dihom_to_hom F
  set Gₕ := dihom_to_hom G
  exact hom_to_dihom (Homotopy.hcomp' Fₕ Gₕ)
    (G.comp (directed_fst.prod_map_mk (F : D(I × X, Y)))).directed_toFun

end Dihomotopy

/-- Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are PreDihomotopic if there exists a
  `Dihomotopy f₀ f₁`.
-/
def PreDihomotopic (f₀ f₁ : D(X,Y)) : Prop := Nonempty (Dihomotopy f₀ f₁)

/-- Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are Dihomotopic if there
  is a chain of PreDihomotopic maps leading from `f₀` to `f₁`.
  In other words, Dihomotopic is the equivalence relation generated by PreDihomotopic.
-/
def Dihomotopic (f₀ f₁ : D(X,Y)) : Prop := (Relation.EqvGen PreDihomotopic) f₀ f₁

namespace Dihomotopic

lemma equivalence : Equivalence (@Dihomotopic X Y _ _) := by apply Relation.EqvGen.is_equivalence

end Dihomotopic

/-- The type of dihomotopies between `f₀ f₁ : D(X,Y)`, where the intermediate maps satisfy the
predicate
`P : D(X,Y) → Prop`
-/
structure DihomotopyWith (f₀ f₁ : D(X,Y)) (P : D(X,Y) → Prop) extends Dihomotopy f₀ f₁ where
  prop' : ∀ (t : I), P (toDirectedMap.prod_const_fst t)

namespace DihomotopyWith

variable {f₀ f₁ : D(X,Y)} {P : D(X,Y) → Prop}

instance instFunLike : FunLike (DihomotopyWith f₀ f₁ P) (I × X) Y where
  coe F := ⇑F.toDihomotopy
  coe_injective' := by
    rintro ⟨⟨⟨⟨F, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨G, _⟩, _⟩, _⟩, _⟩ h
    congr

instance : DihomotopyLike (DihomotopyWith f₀ f₁ P) f₀ f₁ where
  map_continuous F := F.continuous_toFun
  map_directed F := F.directed_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left

theorem coeFn_injective : @Function.Injective (DihomotopyWith f₀ f₁ P) (I × X → Y) (⇑) :=
  DFunLike.coe_injective'

@[ext]
lemma ext {F G : DihomotopyWith f₀ f₁ P} (h : ∀ x, F x = G x) : F = G :=
coeFn_injective <| funext h

namespace Simps

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def apply (F : DihomotopyWith f₀ f₁ P) : I × X → Y := F

end Simps

initialize_simps_projections DihomotopyWith (toDihomotopy_toDirectedMap_toContinuousMap_toFun
    → apply,
    -toDihomotopy_toDirectedMap_toContinuousMap)

@[continuity]
protected lemma continuous (F : DihomotopyWith f₀ f₁ P) : Continuous F := F.continuous_toFun

@[simp]
lemma apply_zero (F : DihomotopyWith f₀ f₁ P) (x : X) : F (0, x) = f₀ x := F.map_zero_left x

@[simp]
lemma apply_one (F : DihomotopyWith f₀ f₁ P) (x : X) : F (1, x) = f₁ x := F.map_one_left x

@[simp]
lemma coe_to_continuous_map (F : DihomotopyWith f₀ f₁ P) : ⇑F.toContinuousMap = F := rfl

@[simp]
lemma coe_to_dihomotopy (F : DihomotopyWith f₀ f₁ P) : ⇑F.toDihomotopy = F := rfl

lemma prop (F : DihomotopyWith f₀ f₁ P) (t : I) : P (F.toDihomotopy.curry t) := F.prop' t

/-- Given a directed map `f`, and a proof `h : P f`, we can define a `DihomotopyWith f f P` by `F
(t, x) = f x`
-/
@[simps!]
def refl (f : D(X,Y)) (hf : P f) : DihomotopyWith f f P := {
  Dihomotopy.refl f with
  prop' := by
    intro t
    convert hf
}

instance : Inhabited (DihomotopyWith (DirectedMap.id X) (DirectedMap.id X) (fun _ => True)) :=
  ⟨DihomotopyWith.refl _ trivial⟩

/-- Given `DihomotopyWith f₀ f₁ P` and `DihomotopyWith f₁ f₂ P`, we can define a `DihomotopyWith f₀
f₂ P`
by putting the first dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : D(X,Y)} (F : DihomotopyWith f₀ f₁ P) (G : DihomotopyWith f₁ f₂ P) :
  DihomotopyWith f₀ f₂ P :=
{
  F.toDihomotopy.trans G.toDihomotopy with
  prop' := fun t => by
    simp only [Dihomotopy.trans]
    change P ⟨⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩, _⟩
    split_ifs with h
    · have hh : ((t : ℝ) ≤ 2⁻¹) := by linarith
      convert F.prop' ⟨2 * (t : ℝ), double_mem_I hh⟩
      ext x
      change ((F.toDihomotopy.dihom_to_hom.extend) (2 * t : ℝ)) x =
        F.toDihomotopy.dihom_to_hom (⟨2 * (t : ℝ), _⟩, x)
      rw [←ContinuousMap.Homotopy.extend_apply_coe F.toDihomotopy.dihom_to_hom _ x]
    · have hh : (2⁻¹ ≤ (t : ℝ)) := by linarith [not_le.mp h]
      convert G.prop' ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I hh⟩
      ext x
      change ((G.toDihomotopy.dihom_to_hom.extend) (2 * (t : ℝ) - 1)) x =
        G.toDihomotopy.dihom_to_hom (⟨2 * (t : ℝ) - 1, _⟩, x)
      rw [←ContinuousMap.Homotopy.extend_apply_coe G.toDihomotopy.dihom_to_hom _ x]
}

lemma trans_apply {f₀ f₁ f₂ : D(X,Y)} (F : DihomotopyWith f₀ f₁ P) (G : DihomotopyWith f₁ f₂ P)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
Dihomotopy.trans_apply _ _ _

/-- Casting a `DihomotopyWith f₀ f₁ P` to a `DihomotopyWith g₀ g₁ P` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : D(X,Y)} (F : DihomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
  DihomotopyWith g₀ g₁ P :=
{
  F.toDihomotopy.cast h₀ h₁ with
  prop' := F.prop,
}

end DihomotopyWith

/-- Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are pre_dihomotopic with respect to the
predicate `P` if there exists a `DihomotopyWith f₀ f₁ P`.
-/
def PreDihomotopicWith (P : D(X,Y) → Prop) (f₀ f₁ : D(X,Y)) : Prop :=
  Nonempty (DihomotopyWith f₀ f₁ P)

/-- `DihomotopicWith` is the equivalence relation generated by `PreDihomotopicWith`.
-/
def DihomotopicWith (P : D(X,Y) → Prop) (f₀ f₁ : D(X,Y)) : Prop
    := Relation.EqvGen (PreDihomotopicWith P) f₀ f₁

/-- A `DihomotopyRel f₀ f₁ S` is a dihomotopy between `f₀` and `f₁` which is fixed on the points in
`S`.
-/
abbrev DihomotopyRel (f₀ f₁ : D(X,Y)) (S : Set X) :=
  DihomotopyWith f₀ f₁ (fun f => ∀ x ∈ S, f x = f₀ x)

namespace DihomotopyRel

variable {f₀ f₁ f₂ : D(X,Y)} {S : Set X}

lemma eq_fst (F : DihomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₀ x :=
  F.prop t x hx

lemma eq_snd (F : DihomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₁ x := by
  rw [F.eq_fst t hx, ← F.eq_fst 1 hx, F.apply_one]

lemma fst_eq_snd (F : DihomotopyRel f₀ f₁ S) {x : X} (hx : x ∈ S) : f₀ x = f₁ x :=
  F.eq_fst 0 hx ▸ F.eq_snd 0 hx

/-- Given a map `f : D(X,Y)` and a set `S`, we can define a `DihomotopyRel f f S` by setting
`F (t, x) = f x` for all `t`. This is defined using `DihomotopyWith.refl`, but with the proof
filled in.
-/
@[simps!]
def refl (f : D(X,Y)) (S : Set X) : DihomotopyRel f f S :=
DihomotopyWith.refl f (fun _ _ => rfl)

/-- Given `DihomotopyRel f₀ f₁ S` and `DihomotopyRel f₁ f₂ S`, we can define a `DihomotopyRel f₀ f₂
S`
by putting the first dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : DihomotopyRel f₀ f₁ S) (G : DihomotopyRel f₁ f₂ S) : DihomotopyRel f₀ f₂ S :=
{
  Dihomotopy.trans F.toDihomotopy G.toDihomotopy with
  prop' := fun t => by
    intros x hx
    simp only [Dihomotopy.trans]
    change (⟨⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩, _⟩ : D(X,Y)) x = f₀ x
    split_ifs with h
    · have : ((t : ℝ) ≤ 2⁻¹) := by linarith
      set t' : I := ⟨2 * (t : ℝ), double_mem_I this⟩
      convert F.eq_fst t' hx
      change ((F.toDihomotopy.dihom_to_hom.extend) (2 * t : ℝ))
          x = F.toDihomotopy.dihom_to_hom (⟨2 * (t : ℝ), _⟩, x)
      rw [←ContinuousMap.Homotopy.extend_apply_coe F.toDihomotopy.dihom_to_hom _ x]
    · have : (2⁻¹ ≤ (t : ℝ)) := by linarith [not_le.mp h]
      set t' : I := ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I this⟩
      convert (G.eq_fst t' hx).trans (F.fst_eq_snd hx).symm
      change ((G.toDihomotopy.dihom_to_hom.extend) (2 * (t : ℝ) - 1))
          x = G.toDihomotopy.dihom_to_hom (⟨2 * (t : ℝ) - 1, _⟩, x)
      rw [←ContinuousMap.Homotopy.extend_apply_coe G.toDihomotopy.dihom_to_hom _ x]
}

lemma trans_apply (F : DihomotopyRel f₀ f₁ S) (G : DihomotopyRel f₁ f₂ S)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
Dihomotopy.trans_apply _ _ _

/-- Casting a `DihomotopyRel f₀ f₁ S` to a `DihomotopyRel g₀ g₁ S` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : D(X,Y)} (F : DihomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
  DihomotopyRel g₀ g₁ S :=
{
  Dihomotopy.cast F.toDihomotopy h₀ h₁ with
  prop' := fun t x hx => by { simpa [←h₀, ←h₁] using F.prop t x hx }
}

end DihomotopyRel

/-- Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are PreDihomotopic relative to a set `S`
if
there exists a `DihomotopyRel f₀ f₁ S`.
-/
def PreDihomotopicRel (S : Set X) (f₀ f₁ : D(X,Y)) : Prop :=
Nonempty (DihomotopyRel f₀ f₁ S)

/-- `DihomotopicRel` is the equivalence relation generated by `PreDihomotopicRel`.
-/
def DihomotopicRel (S : Set X) (f₀ f₁ : D(X,Y)) : Prop := Relation.EqvGen (PreDihomotopicRel S)
    f₀ f₁

namespace DihomotopicRel

variable {S : Set X}

lemma equivalence : Equivalence (fun f g : D(X,Y) => DihomotopicRel S f g)
    := by apply Relation.EqvGen.is_equivalence

end DihomotopicRel

end DirectedMap
