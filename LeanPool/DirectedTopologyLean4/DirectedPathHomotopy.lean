/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.DirectedHomotopy
import LeanPool.DirectedTopologyLean4.TransRefl
import Mathlib.Topology.Homotopy.Path

/-!
# LeanPool.DirectedTopologyLean4.DirectedPathHomotopy
-/

/-
  This file contains the definition of a directed path homotopy, or `Dipath.Dihomotopy`:
  It is a dihomotopy between two paths that keeps the endpoints fixed.

  We prove a few constructions and define the equivalence relation `Dihomtopic` between two paths.
  We show that this relation is closed under reparametrizations, and that concatenation and directed
  maps respect it.

  Much of the structure of this file is based on the undirected version:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Homotopy/Path.lean
-/

universe u v

open unitIAux
open DirectedUnitInterval
open scoped unitInterval

variable {X : Type u} {Y : Type v}
variable [DirectedSpace X] [DirectedSpace Y]
variable {x y z : X}

noncomputable section

namespace Dipath

/-- The type of dihomotopies between two directed paths.
-/
abbrev Dihomotopy (p₀ p₁ : Dipath x y) :=
  DirectedMap.DihomotopyRel p₀.toDirectedMap p₁.toDirectedMap {0, 1}

namespace Dihomotopy

section

variable {p₀ p₁ : Dipath x y}

lemma coeFn_injective : @Function.Injective (Dihomotopy p₀ p₁) (I × I → X) (⇑) :=
  DFunLike.coe_injective

@[simp]
lemma source (F : Dihomotopy p₀ p₁) (t : I) : F (t, 0) = x := by
  calc F (t, 0)
    _ = p₀ 0 := DirectedMap.DihomotopyRel.eq_fst _ _ (.inl rfl)
    _ = x := p₀.source

@[simp]
lemma target (F : Dihomotopy p₀ p₁) (t : I) : F (t, 1) = y := by
  calc F (t, 1)
    _ = p₀ 1 := DirectedMap.DihomotopyRel.eq_fst _ _ (.inr rfl)
    _ = y := p₀.target

/-- A `F : Dihomotopy ↑p₁ ↑p₂` between two dipaths `p₁ p₂ : Dipath y z` can be coerced into a
dihomotopy,
  if it is directed -/
def homToDihom (F : Path.Homotopy p₀.toPath p₁.toPath)
    (HF : DirectedMap.Directed F.toContinuousMap) : Dihomotopy p₀ p₁ where
  toFun := F.toFun
  continuous_toFun := F.continuous_toFun
  directed_toFun := HF
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left
  prop' := F.prop'


/-- A Dihomotopy `F` between two Dipaths `p₁ p₂` can be coerced into a Homotopy between
`p₀.toPath` and `p₁.toPath`. -/
def dihomToHom (F : Dihomotopy p₀ p₁) : Path.Homotopy p₀.toPath p₁.toPath where
  toFun := F.toFun
  continuous_toFun := F.continuous_toFun
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left
  prop' := F.prop'

instance coeDihomToHom : Coe (Dihomotopy p₀ p₁) (Path.Homotopy p₀.toPath p₁.toPath) :=
  ⟨fun F => F.dihomToHom⟩

/-- Evaluating a dipath homotopy at an intermediate point, giving us a `Dipath`.
-/
def eval (F : Dihomotopy p₀ p₁) (t : I) : Dipath x y where
  toFun := F.toDihomotopy.curry t
  source' := F.source t
  target' := F.target t
  dipath_toPath := DirectedUnitInterval.isDipath_of_isDipath_comp_id <|
    (F.toDihomotopy.curry t).directed_toFun DirectedUnitInterval.IdentityPath
      DirectedUnitInterval.isDipath_identityPath

@[simp]
lemma coe_eval (F : Dihomotopy p₀ p₁) (t : I) :
  (⇑(F.eval t) : I → X)  = ⇑(F.toDihomotopy.curry t) := rfl

@[simp]
lemma eval_zero (F : Dihomotopy p₀ p₁) : F.eval 0 = p₀ := by
  ext t
  simp [eval]

@[simp]
lemma eval_one (F : Dihomotopy p₀ p₁) : F.eval 1 = p₁ := by
  ext t
  simp [eval]

end

section
variable {p₀ p₁ p₂ : Dipath x y}

/-- Given a dipath `p`, we can define a `Dihomotopy p p` by `F (t, x) = p x`
-/
@[simps!]
def refl (p : Dipath x y) : Dihomotopy p p :=
  DirectedMap.DihomotopyRel.refl p.toDirectedMap {0, 1}

/-- Given `Dihomotopy p₀ p₁` and `Dihomotopy p₁ p₂`, we can define a `Dihomotopy p₀ p₂` by putting
the first
dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : Dihomotopy p₀ p₁) (G : Dihomotopy p₁ p₂) : Dihomotopy p₀ p₂ :=
  DirectedMap.DihomotopyRel.trans F G

lemma trans_apply (F : Dihomotopy p₀ p₁) (G : Dihomotopy p₁ p₂) (x : I × I) :
  (F.trans G) x =
    if h : (x.1 : ℝ) ≤ 1/2 then
      F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨x.1.2.1, h⟩⟩, x.2)
    else
      G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
DirectedMap.DihomotopyRel.trans_apply _ _ _

/-- Casting a `Dihomotopy p₀ p₁` to a `Dihomotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`.
-/
-- @[simps]
def cast {p₀ p₁ q₀ q₁ : Dipath x y} (F : Dihomotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) :
    Dihomotopy q₀ q₁ :=
  DirectedMap.DihomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)

end

section

variable {p₀ q₀ : Dipath x y} {p₁ q₁ : Dipath y z}

variable (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) (s t : I) (ht : t = halfI)

lemma _root_.Dipath.Dihomotopy.hcomp_apply_half_left (ht : t = halfI) :
    (dihomToHom F).hcomp (dihomToHom G) (s, t) = F (s, 1) := by
  rw [Path.Homotopy.hcomp_apply]
  have ht_coe : (t : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr ht
  have : (t : ℝ) ≤ 2⁻¹ := by linarith
  simp [ht_coe]

lemma _root_.Dipath.Dihomotopy.hcomp_apply_half_right (ht : t = halfI) :
    (dihomToHom F).hcomp (dihomToHom G) (s, t) = G (s, 0) := by
  rw [Path.Homotopy.hcomp_apply]
  have ht_coe : (t : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr ht
  split_ifs <;> simp [ht_coe]

lemma _root_.Dipath.Dihomotopy.hcomp_apply_left (ht : (t : ℝ) ≤ 2⁻¹) :
    (dihomToHom F).hcomp (dihomToHom G) (s, t) = F (s, ⟨2 * t, double_mem_I ht⟩) := by
  rw [Path.Homotopy.hcomp_apply]
  simp [ht]
  rfl

lemma _root_.Dipath.Dihomotopy.hcomp_apply_right (ht : 2⁻¹ ≤ (t : ℝ)) :
    (dihomToHom F).hcomp (dihomToHom G) (s, t) = G (s, ⟨2 * t - 1, double_sub_one_mem_I ht⟩)
        := by
  rw [Path.Homotopy.hcomp_apply]
  simp
  split_ifs
  · have : (t : ℝ) = 2⁻¹ := by linarith
    simp [this]
  · rfl

lemma _root_.Dipath.Dihomotopy.hcomp_first_case (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁)
    {a₀ a₁ : I × I} {γ : Path a₀ a₁}
  (γ_dipath : IsDipath γ) (ht₁ : (a₁.2 : ℝ) ≤ 2⁻¹) :
    IsDipath (γ.map ((dihomToHom F).hcomp (dihomToHom G)).continuous_toFun) := by
  obtain ⟨s₀, t₀⟩ := a₀
  obtain ⟨s₁, t₁⟩ := a₁
  set Γ := (dihomToHom F).hcomp (dihomToHom G)
  set γ_as_dipath := Dipath.ofIsDipath γ_dipath
  set γ₁ := γ_as_dipath.ofProductFst
  set γ₂ := γ_as_dipath.ofProductSnd
  set p := Dipath.dipathProduct γ₁ (Dipath.stretchUp γ₂ ht₁)
  set p' := p.map (F.toDirectedMap)
  have h : ∀ (s t : I), (h : (t : ℝ) ≤ 2⁻¹) → Γ (s, t) = F (s, ⟨2 * (t : ℝ), double_mem_I h⟩) := by
    intros s t ht
    rw [Path.Homotopy.hcomp_apply (dihomToHom F) (dihomToHom G) (s, t)]
    simp [ht]
    rfl
  have ht₀ : (t₀ : ℝ) ≤ 2⁻¹ := by
    have h_le : t₀ ≤ t₁ := directed_path_source_le_target γ_dipath.2
    exact le_trans (Subtype.coe_le_coe.mpr h_le) ht₁
  have hpath : γ.map Γ.continuous_toFun = p'.cast (h s₀ t₀ ht₀) (h s₁ t₁ ht₁) := by
    ext
    simp only [Path.coe_toContinuousMap, ContinuousMap.toFun_eq_coe,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.HomotopyWith.coe_toHomotopy,
      Path.map_coe, Function.comp_apply, coe_toDirectedMap,
      DirectedMap.Dihomotopy.coe_to_directed_map, DirectedMap.DihomotopyWith.coe_to_dihomotopy]
    exact h _ _ (le_trans (directed_path_bounded γ_dipath.2 _).2 ht₁)
  rw [hpath]
  exact (p'.cast (h s₀ t₀ ht₀) (h s₁ t₁ ht₁)).dipath_toPath


lemma _root_.Dipath.Dihomotopy.hcomp_second_case (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁)
    {a₀ a₁ : I × I} {γ : Path a₀ a₁} (γ_dipath : IsDipath γ) (ht₀ : 2⁻¹ ≤ (a₀.2 : ℝ)) :
    IsDipath (γ.map ((dihomToHom F).hcomp (dihomToHom G)).continuous_toFun) := by
  obtain ⟨s₀, t₀⟩ := a₀
  obtain ⟨s₁, t₁⟩ := a₁
  set Γ := (dihomToHom F).hcomp (dihomToHom G)
  set γ_as_dipath := Dipath.ofIsDipath γ_dipath
  set γ₁ := γ_as_dipath.ofProductFst
  set γ₂ := γ_as_dipath.ofProductSnd
  set p := Dipath.dipathProduct γ₁ (Dipath.stretchDown γ₂ ht₀)
  set p' := p.map G.toDirectedMap
  have h : ∀ (s t : I), (h : (2⁻¹ : ℝ) ≤ ↑t) →
    Γ (s, t) = G (s, ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I h⟩) := by
    intros s t ht
    rw [Path.Homotopy.hcomp_apply (dihomToHom F) (dihomToHom G) (s, t)]
    split_ifs with ht'
    · simp at ht'
      have : ↑t = (2⁻¹ : ℝ) := by linarith
      simp [this]
    · rfl
  have ht₁ : 2⁻¹ ≤ (t₁ : ℝ) := by
    have h_le : t₀ ≤ t₁ := directed_path_source_le_target γ_dipath.2
    exact le_trans ht₀ (Subtype.coe_le_coe.mpr h_le)
  have hpath : γ.map Γ.continuous_toFun = p'.cast (h s₀ t₀ ht₀) (h s₁ t₁ ht₁) := by
    ext x
    simp only [Path.coe_toContinuousMap, ContinuousMap.toFun_eq_coe,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.HomotopyWith.coe_toHomotopy,
      Path.map_coe, Function.comp_apply, coe_toDirectedMap,
      DirectedMap.Dihomotopy.coe_to_directed_map, DirectedMap.DihomotopyWith.coe_to_dihomotopy]
    exact h (γ x).1 (γ x).2 (le_trans ht₀ (directed_path_bounded γ_dipath.2 _).1)
  rw [hpath]
  exact (p'.cast (h s₀ t₀ ht₀) (h s₁ t₁ ht₁)).dipath_toPath

/-- Suppose `p₀` and `q₀` are dipaths from `x` to `y`, `p₁` and `q₁` are dipaths from `y` to `z`.
Furthermore, suppose `F : Dihomotopy p₀ q₀` and `G
    : Dihomotopy p₁ q₁`. Then we can define a dihomotopy
from `p₀.trans p₁` to `q₀.trans q₁`.
-/
def _root_.Dipath.Dihomotopy.hcomp (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) :
    Dihomotopy (p₀.trans p₁) (q₀.trans q₁) := by
  set Fₕ := dihomToHom F
  set Gₕ := dihomToHom G
  set Γ := Fₕ.hcomp Gₕ
  have : DirectedMap.Directed Γ.toContinuousMap := by
    rintro ⟨s₀, t₀⟩ ⟨s₁, t₁⟩ γ γ_dipath
    set γ_as_dipath := Dipath.ofIsDipath γ_dipath
    set γ₁ := γ_as_dipath.ofProductFst
    set γ₂ := γ_as_dipath.ofProductSnd
    by_cases ht₁ : (↑t₁ : ℝ) ≤ 2⁻¹
    case pos => exact hcomp_first_case F G γ_dipath ht₁
    by_cases ht₀ : (↑t₀ : ℝ) < 2⁻¹
    case neg => exact hcomp_second_case F G γ_dipath (by linarith)
    -- Complicated
    push Not at ht₁
    obtain ⟨T, hT₀, hT₁, hT_half⟩ := has_T_half (γ.map continuous_snd) ht₀ ht₁
    /- Split γ into two parts (one with image in I × [0, 2⁻¹], the other with image in I × [2⁻¹, 1])
    -/
    set a₁ := SplitDipath.FirstPart γ_as_dipath T
    set a₂ := SplitDipath.SecondPart γ_as_dipath T
    /- Create two new paths, where the first coordinate is stretched and the second coordinate
    remains the same -/
    set p₁ := SplitDipath.FirstPart γ₁ T
    set p₂ := SplitDipath.SecondPart γ₁ T
    set p₁' := DirectedMap.Dihomotopy.FirstPartStretch γ₂ hT_half (le_of_lt ht₀)
    set p₂' := DirectedMap.Dihomotopy.SecondPartStretch γ₂ hT_half (le_of_lt ht₁)
    set q₁ := (Dipath.dipathProduct p₁ p₁').map F.toDirectedMap
    set q₂ := (Dipath.dipathProduct p₂ p₂').map G.toDirectedMap
    set φ := SplitDipath.transReparamMap hT₀ hT₁
    have φ₀ : φ 0 = 0 := Subtype.ext <| SplitPath.trans_reparam_zero T
    have φ₁ : φ 1 = 1 := Subtype.ext <| SplitPath.trans_reparam_one hT₁
    have hγT_eq_half : ((γ T).2 : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr hT_half
    have hγT_le_half : ((γ T).2 : ℝ) ≤ 2⁻¹ := le_of_eq hγT_eq_half
    set r₁ := q₁.cast (hcomp_apply_left F G s₀ t₀ (le_of_lt ht₀))
        (hcomp_apply_half_left F G (γ T).1 (γ T).2 hT_half)
    set r₂ := q₂.cast (hcomp_apply_half_right F G (γ T).1 (γ T).2 hT_half)
        (hcomp_apply_right F G s₁ t₁ (le_of_lt ht₁))
    suffices hpath : γ.map Γ.continuous_toFun = (r₁.trans r₂).reparam φ φ₀ φ₁ by
      rw [hpath]; exact ((r₁.trans r₂).reparam φ φ₀ φ₁).dipath_toPath
    ext t
    have hr₁a₁ : r₁.toPath = a₁.toPath.map Γ.continuous_toFun := by
      ext x
      have this : ((a₁ x).2 : ℝ) ≤ 2⁻¹
          := le_trans (directed_path_bounded a₁.dipath_toPath.2 _).2 hγT_le_half
      calc r₁ x
        _ = F ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ), double_mem_I this⟩)
              := rfl
        _ = if h : ((a₁ x).2 : ℝ) ≤ 1/2
                then F ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ), double_mem_I this⟩)
                else G ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ) - 1,
                    by { apply double_sub_one_mem_I (le_of_lt _); convert h; norm_num }⟩)
              := by apply Eq.symm; apply dif_pos; convert this using 1; norm_num
        _ = if h : ((a₁ x).2 : ℝ) ≤ 1/2
                then Fₕ.eval (a₁ x).1 ⟨2 * ((a₁ x).2 : ℝ), double_mem_I this⟩
                else Gₕ.eval (a₁ x).1 ⟨2 * ((a₁ x).2 : ℝ)
                    - 1, by { apply double_sub_one_mem_I (le_of_lt _); convert h; norm_num }⟩
              := rfl
        _ = (Fₕ.hcomp Gₕ) (a₁ x)
              := (Path.Homotopy.hcomp_apply Fₕ Gₕ (a₁ x)).symm
        _ = Γ (a₁ x)
              := rfl
        _ = (a₁.toPath.map Γ.continuous_toFun) x
              := rfl
    have hr₂a₂ : r₂.toPath = a₂.toPath.map Γ.continuous_toFun := by
      ext x
      have : 2⁻¹ ≤ ((a₂ x).2 : ℝ) := by
        calc (2⁻¹ : ℝ)
          _ = ↑(γ T).2   := Subtype.coe_inj.mpr hT_half.symm
          _ ≤  ↑(a₂ x).2 := (directed_path_bounded a₂.dipath_toPath.2 _).1
      calc r₂.toPath x
        _ = G ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ) - 1, double_sub_one_mem_I this⟩)
              := rfl
        _ = if h : ((a₂ x).2 : ℝ) ≤ 1/2
                then F ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ),
                    by { apply double_mem_I; convert h using 1; norm_num }⟩)
                else G ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ) - 1,
                    by { apply double_sub_one_mem_I (le_of_lt _); convert h using 1; norm_num }⟩)
              := by
                split_ifs with h
                · have : ((a₂ x).2 : ℝ) ≤ 2⁻¹ := by convert h using 1; norm_num
                  have ha₂x : ((a₂ x).2 : ℝ) = 2⁻¹ := by linarith
                  have : G (_, 0) = F (_, 1) := Eq.trans (G.source (a₂ x).1)
                      (F.target (a₂ x).1).symm
                  convert this <;> rw [ha₂x] <;> norm_num
                · rfl
        _ = if h : ((a₂ x).2 : ℝ) ≤ 1/2
                then Fₕ.eval (a₂ x).1 ⟨2 * ((a₂ x).2 : ℝ),
                  by { apply double_mem_I; convert h using 1; norm_num }⟩
                else Gₕ.eval (a₂ x).1 ⟨2 * ((a₂ x).2 : ℝ) - 1,
                  by { apply double_sub_one_mem_I (le_of_lt _)
                       convert h using 1
                       norm_num }⟩
              := rfl
        _ = (Fₕ.hcomp Gₕ) (a₂ x)
              := (Path.Homotopy.hcomp_apply Fₕ Gₕ (a₂ x)).symm
        _ = Γ (a₂ x)
              := rfl
        _ = (a₂.toPath.map Γ.continuous_toFun) x
              := rfl
    calc (Γ ∘ γ) t
      _ = Γ (γ t)
            := rfl
      _ = Γ (((a₁.trans a₂).reparam φ φ₀ φ₁) t)
            := by rw [←SplitDipath.first_trans_second_reparam_eq_self γ_as_dipath hT₀ hT₁]; rfl
      _ = ((a₁.trans a₂).toPath.map Γ.continuous_toFun).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := rfl
      _ = ((a₁.toPath.trans a₂.toPath).map Γ.continuous_toFun).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := rfl
      _ = ((a₁.toPath.map Γ.continuous_toFun).trans
            (a₂.toPath.map Γ.continuous_toFun)).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := by rw [Path.map_trans a₁.toPath a₂.toPath (Γ.continuous_toFun)]
      _ = (r₁.toPath.trans r₂.toPath).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := by rw [hr₁a₁, hr₂a₂]; rfl
      _ = (r₁.trans r₂).reparam φ φ₀ φ₁ t
            := rfl
  exact homToDihom Γ this

lemma _root_.Dipath.Dihomotopy.hcomp_apply (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁)
    (x : I × I) :
    F.hcomp G x =
      if h : (x.2 : ℝ) ≤ 1/2 then
        F.eval x.1 ⟨2 * x.2, (unitInterval.mul_pos_mem_iff two_pos).2 ⟨x.2.2.1, h⟩⟩
      else
        G.eval x.1 ⟨2 * x.2 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.2.2.2⟩⟩
            :=
  show ite _ _ _ = _ by split_ifs <;> exact Path.extend_apply _ _

lemma _root_.Dipath.Dihomotopy.hcomp_half (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) (t : I) :
    F.hcomp G (t, ⟨1/2, by norm_num, by norm_num⟩) = y :=
  show ite _ _ _ = _ by norm_num

end

/-- Suppose `p` is a dipath, and `f g : D(I,I)` two monotonic subparametrizations. If `f` is
dominated by `g`,
i.e. `∀ t, f t ≤ g t`, then we obtain a dihomotopy between the two subparametrization of `p` as
the interpolation between the two becomes directed.
-/
def _root_.Dipath.Dihomotopy.reparam (p : Dipath x y) (f : D(I,I)) (g : D(I,I))
    (hf_le_g : ∀ (t : I), f t ≤ g t)
    (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) (hg₀ : g 0 = 0) (hg₁ : g 1 = 1) :
    Dihomotopy (p.reparam f hf₀ hf₁) (p.reparam g hg₀ hg₁) where
  toFun := p.toContinuousMap.comp (interpolate f.toContinuousMap g.toContinuousMap)
  map_zero_left := fun x => by
    change p ((interpolate f.toContinuousMap g.toContinuousMap) (0, x)) = _
    have h0 : (σ (0 : I) : ℝ) = 1 := by simp
    have hint : (interpolate f.toContinuousMap g.toContinuousMap) (0, x) = f x := by
      apply Subtype.coe_inj.mp
      change (σ (0 : I) : ℝ) * f x + (0 : ℝ) * g x = f x
      rw [h0]; ring
    rw [hint]
    rfl
  map_one_left := fun x => by
    change p ((interpolate f.toContinuousMap g.toContinuousMap) (1, x)) = _
    have h0 : (σ (1 : I) : ℝ) = 0 := by simp
    have hint : (interpolate f.toContinuousMap g.toContinuousMap) (1, x) = g x := by
      apply Subtype.coe_inj.mp
      change (σ (1 : I) : ℝ) * f x + (1 : ℝ) * g x = g x
      rw [h0]; ring
    rw [hint]
    rfl
  prop' := fun t x hx => by
    rcases hx with hx | hx
    · have heq : g 0 = f 0 := hg₀.trans hf₀.symm
      rw [hx]
      change p ((interpolate f.toContinuousMap g.toContinuousMap) (t, 0)) = (p.reparam f hf₀ hf₁) 0
      rw [interpolate_constant_apply f.toContinuousMap g.toContinuousMap 0 (f 0) rfl heq t]
      rfl
    · rw [Set.mem_singleton_iff] at hx
      have heq : g 1 = f 1 := hg₁.trans hf₁.symm
      rw [hx]
      change p ((interpolate f.toContinuousMap g.toContinuousMap) (t, 1)) = (p.reparam f hf₀ hf₁) 1
      rw [interpolate_constant_apply f.toContinuousMap g.toContinuousMap 1 (f 1) rfl heq t]
      rfl
  directed_toFun := fun t₀ t₁ γ γ_dipath =>
    (p.toDirectedMap).directed_toFun (γ.map _) (directed_interpolate f g hf_le_g γ γ_dipath)


/-- For any `p : Dipath x y`, there is a dihomotopy from `p` to `p.trans (Dipath.refl y)`.
-/
def _root_.Dipath.Dihomotopy.transRefl (p : Dipath x y) :
    Dihomotopy p (p.trans (Dipath.refl y)) := by
  set f : D(I,I) := DirectedMap.id I
  set g : D(I,I) := TransReflReparamAuxMap
  have hf_le_g : ∀ (t : I), f t ≤ g t := by
    intro t
    apply Subtype.coe_le_coe.mp
    change (t : ℝ) ≤ TransReflReparamAuxMap t
    change (t : ℝ) ≤ Path.Homotopy.transReflReparamAux t
    unfold Path.Homotopy.transReflReparamAux
    split_ifs
    · have : 0 ≤ (t : ℝ) := t.2.1
      linarith
    · exact t.2.2
  have hf₀ : f 0 = 0 := rfl
  have hf₁ : f 1 = 1 := rfl
  convert reparam p f g hf_le_g hf₀ hf₁
    (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
    (Subtype.ext Path.Homotopy.transReflReparamAux_one)
  · exact (Dipath.reparam_id p).symm
  · exact trans_refl_reparam_dipath p

/-- For any `p : Dipath x y`, there is a dihomotopy from `(Dipath.refl x).trans p` to `p`.
-/
def _root_.Dipath.Dihomotopy.reflTrans (p : Dipath x y) :
    Dihomotopy ((Dipath.refl x).trans p) p := by
  set f : D(I,I) := ReflTransReparamAuxMap
  set g : D(I,I) := DirectedMap.id I
  have hf_le_g : ∀ (t : I), f t ≤ g t := fun t => by
    apply Subtype.coe_le_coe.mp
    change ReflTransReparamAux t ≤ (t : ℝ)
    unfold ReflTransReparamAux
    split_ifs
    · exact t.2.1
    · linarith [t.2.2]
  have hg₀ : g 0 = 0 := rfl
  have hg₁ : g 1 = 1 := rfl
  convert reparam p f g hf_le_g (Subtype.ext reflTransReparamAux_zero)
    (Subtype.ext reflTransReparamAux_one) hg₀ hg₁
  · exact refl_trans_reparam_dipath p
  · exact (Dipath.reparam_id p).symm

/-- For any `p : Dipath x y`, there is a homotopy from `(Dipath.refl x).trans p` to `q.trans
(Dipath.refl y)`,
where `q` is any directed reparametrization of `p`.
-/
def _root_.Dipath.Dihomotopy.reflTransToReparamTransRefl (p : Dipath x y) (f : D(I,I))
    (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Dihomotopy ((Dipath.refl x).trans p) ((p.reparam f hf₀ hf₁).trans (Dipath.refl y)) := by
  set φ₁ : D(I,I) := ReflTransReparamAuxMap
  set φ₂ : D(I,I) := f.comp TransReflReparamAuxMap
  have hφ₁_le_φ₂ : ∀ (t : I), φ₁ t ≤ φ₂ t := by
    intro t
    apply Subtype.coe_le_coe.mp
    change ReflTransReparamAux t ≤ (f ⟨Path.Homotopy.transReflReparamAux t, _⟩ : ℝ)
    unfold ReflTransReparamAux Path.Homotopy.transReflReparamAux
    by_cases h : (t : ℝ) ≤ 2⁻¹
    · have hh : (t : ℝ) ≤ 1/2 := by linarith
      split_ifs with h₁ h₂
      · exact (f _).2.1
      · exact absurd hh h₂
      · exact absurd hh h₁
      · exact absurd hh h₁
    · have hh : ¬(t : ℝ) ≤ 1/2 := by linarith
      split_ifs with h₁ h₂
      · exact absurd h₁ hh
      · exact absurd h₁ hh
      · have ht1 : (t : ℝ) ≤ 1 := t.2.2
        have h1 : (f ⟨(1 : ℝ), unitInterval.one_mem⟩ : ℝ) = 1 := by
          rw [show (⟨(1 : ℝ), unitInterval.one_mem⟩ : I) = (1 : I) from rfl, hf₁]; rfl
        rw [h1]
        linarith
      · have ht1 : (t : ℝ) ≤ 1 := t.2.2
        have h1 : (f ⟨(1 : ℝ), unitInterval.one_mem⟩ : ℝ) = 1 := by
          rw [show (⟨(1 : ℝ), unitInterval.one_mem⟩ : I) = (1 : I) from rfl, hf₁]; rfl
        rw [h1]
        linarith
  have hφ₂₀ : φ₂ 0 = 0 := by
    change f ⟨Path.Homotopy.transReflReparamAux 0, _⟩ = 0
    nth_rewrite 3 [←hf₀]
    congr
    exact Path.Homotopy.transReflReparamAux_zero
  have hφ₂₁ : φ₂ 1 = 1 := by
    change f ⟨Path.Homotopy.transReflReparamAux 1, _⟩ = 1
    nth_rewrite 3 [←hf₁]
    congr
    exact Path.Homotopy.transReflReparamAux_one
  convert reparam p φ₁ φ₂ hφ₁_le_φ₂ (Subtype.ext reflTransReparamAux_zero)
    (Subtype.ext reflTransReparamAux_one) hφ₂₀ hφ₂₁
  · exact refl_trans_reparam_dipath p
  · rw [trans_refl_reparam_dipath (p.reparam f hf₀ hf₁)]
    ext
    rfl


/-- Given `F : Dihomotopy p q`, and `f : D(X,Y)`, there is a dihomotopy from `p.map f` to
`q.map f` given by `f ∘ F`.
-/
@[simps!]
def _root_.Dipath.Dihomotopy.map {p q : Dipath x y} (F : Dihomotopy p q) (f : D(X,Y)) :
    Dihomotopy (p.map f) (q.map f) where
  toFun := f ∘ F
  map_zero_left := fun _ => by simp
  map_one_left := fun _ => by simp
  prop' := fun t s hs => by
    rcases hs with hs | hs
    · rw [hs]
      change f (F (t, 0)) = (p.map f) 0
      simp
    · have hs1 : s = 1 := Set.mem_singleton_iff.mp hs
      rw [hs1]
      change f (F (t, 1)) = (p.map f) 1
      simp
  directed_toFun := (f.comp F.toDirectedMap).directed_toFun

end Dihomotopy


section

variable (p₀ p₁ : Dipath x y)
/-- Two dipaths `p₀` and `p₁` are `Dipath.PreDihomotopic` if there exists a `Dihomotopy` from `p₀`
to `p₁`.
-/
def _root_.Dipath.PreDihomotopic : Prop := Nonempty (Dihomotopy p₀ p₁)

/-- `Dipath.Dihomotopic` is the equivalence generated by `Dipath.PreDihomotopic`.
-/
def _root_.Dipath.Dihomotopic : Prop := Relation.EqvGen PreDihomotopic p₀ p₁

end

namespace Dihomotopic

lemma _root_.Dipath.Dihomotopic.equivalence : Equivalence (@Dihomotopic X _ x y) := by
  apply Relation.EqvGen.is_equivalence

/-- If `p` is dihomotopic with `q`, then `f ∘ p` is dihomotopic with `f ∘ q` for any directed map
`f` -/
lemma _root_.Dipath.Dihomotopic.map {p q : Dipath x y} (h : p.Dihomotopic q) (f : D(X,Y)) :
    Dihomotopic (p.map f) (q.map f) :=
  Relation.EqvGen.rec
    (fun _ _ h => Relation.EqvGen.rel _ _ ⟨h.some.map f⟩)
    (fun x => Relation.EqvGen.refl (x.map f))
    (fun _ _ _ h => Relation.EqvGen.symm _ _ h)
    (fun _ _ _ _ _ h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂)
  h

lemma _root_.Dipath.Dihomotopic.hcomp_aid_left {p₀ p₁ : Dipath x y} (q : Dipath y z)
    (hp : p₀.Dihomotopic p₁) :
    (p₀.trans q).Dihomotopic (p₁.trans q) :=
  Relation.EqvGen.rec
    (fun _ _ h => Relation.EqvGen.rel _ _ ⟨h.some.hcomp (Dihomotopy.refl q)⟩)
    (fun p => Relation.EqvGen.refl (p.trans q))
    (fun _ _ _ h => Relation.EqvGen.symm _ _ h)
    (fun _ _ _ _ _ h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂)
  hp

lemma _root_.Dipath.Dihomotopic.hcomp_aid_right (p : Dipath x y) {q₀ q₁ : Dipath y z}
    (hq : q₀.Dihomotopic q₁) :
    (p.trans q₀).Dihomotopic (p.trans q₁) :=
  Relation.EqvGen.rec
    (fun _ _ h => Relation.EqvGen.rel _ _ ⟨(Dihomotopy.refl p).hcomp h.some⟩)
    (fun q => Relation.EqvGen.refl (p.trans q))
    (fun _ _ _ h => Relation.EqvGen.symm _ _ h)
    (fun _ _ _ _ _ h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂)
  hq

/-- Suppose we have`p₀ p₁ : Dipath x y` and `q₀ q₁ : Dipath y z`.
If `p₀` is dihomotopic with `p₁` and `q₀` is dihomotopic with `q₁`,
then `p₀.trans q₀` is dihomotopic with `p₁.trans q₁`.
-/
lemma _root_.Dipath.Dihomotopic.hcomp {p₀ p₁ : Dipath x y} {q₀ q₁ : Dipath y z}
    (hp : p₀.Dihomotopic p₁) (hq : q₀.Dihomotopic q₁) :
    (p₀.trans q₀).Dihomotopic (p₁.trans q₁) :=
  Relation.EqvGen.rec
    (fun p₀ p₁ hp₀_p₁ => by
      exact Relation.EqvGen.rec
          (fun _ _ hq₀_q₁ => Relation.EqvGen.rel _ _ ⟨hp₀_p₁.some.hcomp hq₀_q₁.some⟩)
          (fun q => Relation.EqvGen.rel _ _ ⟨hp₀_p₁.some.hcomp (Dihomotopy.refl q)⟩)
          (fun q₀ q₁ _ hp₀q₀_p₁q₁ => by
              have hp₀q₁_p₁q₂ := hcomp_aid_left q₁ (Relation.EqvGen.rel _ _ hp₀_p₁)
              have hp₁q₁_p₀q₀ := Relation.EqvGen.symm _ _ hp₀q₀_p₁q₁
              have hp₀q₀_p₁q₀ := hcomp_aid_left q₀ (Relation.EqvGen.rel _ _ hp₀_p₁)
              exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₀q₁_p₁q₂ hp₁q₁_p₀q₀)
                  hp₀q₀_p₁q₀
          )
          (fun q₀ q₁ q₂ hq₀_q₁ hq₁_q₂ _ _ => by
              have hp₀q₀_p₀q₁ := hcomp_aid_right p₀ hq₀_q₁
              have hp₀q₁_p₀q₂ := hcomp_aid_right p₀ hq₁_q₂
              have hp₀q₂_p₁q₂ := hcomp_aid_left q₂ (Relation.EqvGen.rel _ _ hp₀_p₁)
              exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₀q₀_p₀q₁ hp₀q₁_p₀q₂)
                  hp₀q₂_p₁q₂
          )
        hq
    )
    (fun p => by
      exact Relation.EqvGen.rec
          (fun _ _ h => hcomp_aid_right p (Relation.EqvGen.rel _ _ h))
          (fun q => Relation.EqvGen.refl (p.trans q))
          (fun _ _ _ h => Relation.EqvGen.symm _ _ h)
          (fun _ _ _ _ _ h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂)
        hq
    )
    (fun p₀ p₁ hp₀_p₁ _ => by
      have hp₁_p₀ := Relation.EqvGen.symm _ _ hp₀_p₁
      exact Relation.EqvGen.rec
          (fun q₀ q₁ hq₀_q₁ => by
            have hp₁q₀_p₀q₀ := hcomp_aid_left q₀ hp₁_p₀
            have hp₀q₀_p₀q₁ := hcomp_aid_right p₀ (Relation.EqvGen.rel _ _ hq₀_q₁)
            exact Relation.EqvGen.trans _ _ _ hp₁q₀_p₀q₀ hp₀q₀_p₀q₁
          )
          (fun q => hcomp_aid_left q hp₁_p₀)
          (fun q₀ q₁ hq₀_q₁ _ => by
            have hp₁q₁_p₁q₀ := hcomp_aid_right p₁ (Relation.EqvGen.symm _ _ hq₀_q₁)
            have hp₁q₀_p₀q₀ := hcomp_aid_left q₀ (Relation.EqvGen.symm _ _ hp₀_p₁)
            exact Relation.EqvGen.trans _ _ _ hp₁q₁_p₁q₀ hp₁q₀_p₀q₀
          )
          (fun q₀ q₁ q₂ _ _ hp₁q₀_p₀q₁ hp₁q₁_p₀q₂ => by
            have hp₀q₁_p₁q₁ := hcomp_aid_left q₁ hp₀_p₁
            exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₁q₀_p₀q₁ hp₀q₁_p₁q₁)
                hp₁q₁_p₀q₂
          )
        hq
    )
    (fun p₀ p₁ p₂ hp₀_p₁ hp₁_p₂ _ _ => by
      exact Relation.EqvGen.rec
          (fun q₀ q₁ hq₀_q₁ => by
            have hp₀q₁_p₁q₀ := hcomp_aid_left q₀ hp₀_p₁
            have hp₁q₀_p₂q₀ := hcomp_aid_left q₀ hp₁_p₂
            have hp₂q₀_p₂q₁ := hcomp_aid_right p₂ (Relation.EqvGen.rel _ _ hq₀_q₁)
            exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₀q₁_p₁q₀ hp₁q₀_p₂q₀)
                hp₂q₀_p₂q₁
          )
          (fun q => by
            have hp₀q_p₁q := hcomp_aid_left q hp₀_p₁
            have hp₁q_p₂q := hcomp_aid_left q hp₁_p₂
            exact Relation.EqvGen.trans _ _ _ hp₀q_p₁q hp₁q_p₂q
          )
          (fun q₀ q₁ hq₀_q₁ hp₀q₀_p₂q₁ => by
            have hq₁_q₀ := Relation.EqvGen.symm _ _ hq₀_q₁
            have hp₀q₁_p₀q₀ := hcomp_aid_right p₀ hq₁_q₀
            have hp₂q₁_p₂q₀ := hcomp_aid_right p₂ hq₁_q₀
            exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₀q₁_p₀q₀ hp₀q₀_p₂q₁)
                hp₂q₁_p₂q₀
          )
          (fun q₀ q₁ q₂ _ _ hp₀q₀_p₂q₁ hp₀q₁_p₂q₂ => by
            have hp₂_p₀ := Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _ hp₀_p₁ hp₁_p₂)
            have hp₂q₂_p₀q₁ := hcomp_aid_left q₁ hp₂_p₀
            exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hp₀q₀_p₂q₁ hp₂q₂_p₀q₁)
                hp₀q₁_p₂q₂
          )
        hq
    )
  hp

/-- If `p` is a dipath, then it is dihomotopic with any monotonic subparametrization.
-/
lemma _root_.Dipath.Dihomotopic.reparam (p : Dipath x y) (f : D(I,I))
    (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  p.Dihomotopic (p.reparam f hf₀ hf₁) := by
  set p' := p.reparam f hf₀ hf₁
  set p₁ := ((refl x).trans p)
  set p₂ := (p'.trans (refl y))
  have h₁ : p₁.PreDihomotopic p := ⟨Dihomotopy.reflTrans p⟩
  have h₂ : p₁.PreDihomotopic p₂ := ⟨Dihomotopy.reflTransToReparamTransRefl p f hf₀ hf₁⟩
  have h₃ : p'.PreDihomotopic p₂ := ⟨Dihomotopy.transRefl p'⟩
  have h₁ : p.Dihomotopic p₁ := Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h₁)
  have h₂ : p₁.Dihomotopic p₂ := Relation.EqvGen.rel _ _ h₂
  have h₃ : p₂.Dihomotopic p' := Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h₃)
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ h₁ h₂) h₃

/-- The setoid on `Dipath`s defined by the equivalence relation `Dipath.Dihomotopic`. That is, two
paths are
equivalent if there is a chain of `Dihomotopies` starting in one and ending in the other.
-/
@[reducible] protected def _root_.Dipath.Dihomotopic.setoid (x y : X) : Setoid (Dipath x y) :=
  ⟨Dihomotopic, equivalence⟩

/-- The quotient on `Dipath x y` by the equivalence relation `Dipath.Dihomotopic`.
-/
protected def _root_.Dipath.Dihomotopic.Quotient (x y : X) :=
  Quotient (Dihomotopic.setoid x y)

attribute [local instance] Dihomotopic.setoid

instance : Inhabited (Dihomotopic.Quotient x x) :=
  ⟨Quotient.mk' <| Dipath.refl x⟩

/-- The composition of dipath dihomotopy classes. This is `Dipath.trans` descended to the
quotient. -/
def _root_.Dipath.Dihomotopic.Quotient.comp (P₀ : Dipath.Dihomotopic.Quotient x y)
    (P₁ : Dipath.Dihomotopic.Quotient y z) : Dipath.Dihomotopic.Quotient x z :=
  Quotient.map₂ Dipath.trans
    (fun (_ : Dipath x y) _ hp (_ : Dipath y z) _ hq => (hcomp hp hq)) P₀ P₁

lemma _root_.Dipath.Dihomotopic.comp_lift (P₀ : Dipath x y) (P₁ : Dipath y z) :
    ⟦P₀.trans P₁⟧ = Quotient.comp ⟦P₀⟧ ⟦P₁⟧ := rfl

/-- The image of a dipath dihomotopy class `P₀` under a directed map `f`. This is `Dipath.map`
descended to the quotient. -/
def _root_.Dipath.Dihomotopic.Quotient.mapFn (P₀ : Dipath.Dihomotopic.Quotient x y) (f : D(X,Y)) :
  Dipath.Dihomotopic.Quotient (f x) (f y) :=
Quotient.map (fun (q : Dipath x y) => q.map f) (fun _ _ h => Dipath.Dihomotopic.map h f) P₀

lemma _root_.Dipath.Dihomotopic.map_lift (P₀ : Dipath x y) (f : D(X,Y)) :
  ⟦P₀.map f⟧ = Quotient.mapFn ⟦P₀⟧ f := rfl

lemma _root_.Dipath.Dihomotopic.quot_reparam (γ : Dipath x y) {f : D(I,I)} (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) :
    @Eq (Dipath.Dihomotopic.Quotient _ _) ⟦γ.reparam f hf₀ hf₁⟧ ⟦γ⟧ := by
  symm
  exact Quotient.eq.mpr (Dipath.Dihomotopic.reparam γ f hf₀ hf₁)

lemma _root_.Dipath.Dihomotopic.hpath_hext {x₀ x₁ x₂ x₃ : X} {p₁ : Dipath x₀ x₁}
    {p₂ : Dipath x₂ x₃} (hp : ∀ t, p₁ t = p₂ t) :
    @HEq (Dipath.Dihomotopic.Quotient _ _) ⟦p₁⟧ (Dipath.Dihomotopic.Quotient _ _) ⟦p₂⟧ := by
  obtain rfl : x₀ = x₂ := by convert hp 0 <;> simp
  obtain rfl : x₁ = x₃ := by convert hp 1 <;> simp
  rw [heq_iff_eq]
  congr
  ext t
  exact hp t

end Dihomotopic

end Dipath
