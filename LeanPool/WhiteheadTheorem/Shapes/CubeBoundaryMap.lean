/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.Shapes.Cube
import LeanPool.WhiteheadTheorem.Auxiliary
import LeanPool.WhiteheadTheorem.Shapes.UnitInterval

/-!
# LeanPool.WhiteheadTheorem.Shapes.CubeBoundaryMap

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Shapes.CubeBoundaryMap`.
-/


open scoped Topology Topology.Homotopy CategoryTheory
open unitInterval


namespace TopCat.cubeBoundary

/-- `botTopSidesCover` -/
abbrev botTopSidesCover (n : ℕ) : Fin 3 → Set (∂𝕀 (n + 1)) :=
    ![botOrTop n 0, botOrTop n 1, sides n]

lemma sides_eq_iUnion (n : ℕ) :
    sides n = ⋃ (i : Fin n), {⟨⟨y, _⟩⟩ | y i.castSucc = 0 ∨ y i.castSucc = 1} := by
  ext x
  constructor
  · intro ⟨i, hin, hi⟩
    exact Set.mem_iUnion_of_mem ⟨i, hin⟩ hi
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i.castSucc, ⟨Fin.castSucc_lt_last _, hi⟩⟩

lemma sides_eq_union_iUnion (n : ℕ) :
    sides n =
      (⋃ (i : Fin n), {⟨⟨y, _⟩⟩ | y i.castSucc = 0}) ∪
      (⋃ (i : Fin n), {⟨⟨y, _⟩⟩ | y i.castSucc = 1}) := by
  rw [sides_eq_iUnion]
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro ⟨i, h⟩
    split
    cases h with
    | inl _ => left; use i
    | inr _ => right; use i
  · intro h
    cases h with
    | inl h => obtain ⟨i, h⟩ := h; split; use i; left; assumption
    | inr h => obtain ⟨i, h⟩ := h; split; use i; right; assumption

lemma botTopSidesCover_cover (n : ℕ) :
    ∀ y : ∂𝕀 (n + 1), ∃ k, y ∈ botTopSidesCover n k := by
  intro ⟨⟨y, ⟨i, hi⟩⟩⟩
  by_cases hin : i = Fin.last _
  · obtain hi | hi := hi
    · use 0; subst hin; exact hi  -- bot
    · use 1; subst hin; exact hi  -- top
  · have : i < Fin.last _ := Fin.lt_last_iff_ne_last.mpr hin
    use 2, i

lemma botTopSidesCover_closed (n : ℕ) :
    ∀ k, IsClosed (botTopSidesCover n k) := by
  intro k
  fin_cases k
  iterate 2
    exact isClosed_eq ((continuous_apply _).comp (by fun_prop)) continuous_const
  dsimp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
  rw [sides_eq_union_iUnion]
  apply IsClosed.union
  all_goals exact isClosed_iUnion_of_finite fun i ↦
    isClosed_eq ((continuous_apply _).comp (by fun_prop)) continuous_const

lemma splitAtLast_snd_mem_boundary_of_mem_sides {n : ℕ} {y : ∂𝕀 (n + 1)}
    (hy : y ∈ sides n) : (Cube.splitAtLast y.down.val).snd ∈ ∂I^n := by
  obtain ⟨i, hin, hi⟩ := hy
  use ⟨i, hin⟩
  rw [Cube.splitAtLast_snd_apply_eq]
  simp_all only [Fin.castSucc_mk, Fin.eta]



variable {n : ℕ} {Z : TopCat.{u}}
variable (f01 : zeroOne → (cube.{u} n ⟶ Z))  -- bottom or top face of `∂𝕀 (n + 1)`
variable (fs : TopCat.of (I × cubeBoundary.{u} n) ⟶ Z)  -- sides of `∂𝕀 (n + 1)`

/-- `mapVecOfBotTopSides` -/
def mapVecOfBotTopSides : (k : Fin 3) → C(botTopSidesCover n k, Z) :=
  let g0 : C(botOrTop.{u} n 0, Z) :=
    ⟨fun ⟨⟨y, _⟩, _⟩ ↦ f01 0 ⟨(Cube.splitAtLast y).snd⟩, by fun_prop⟩
  let g1 : C(botOrTop.{u} n 1, Z) :=
    ⟨fun ⟨⟨y, _⟩, _⟩ ↦ f01 1 ⟨(Cube.splitAtLast y).snd⟩, by fun_prop⟩
  let gs : C(sides.{u} n, Z) :=
    { toFun := fun ⟨⟨y, _⟩, _⟩ ↦
        fs ⟨(Cube.splitAtLast y).fst,
          ⟨(Cube.splitAtLast y).snd, splitAtLast_snd_mem_boundary_of_mem_sides ‹_›⟩ ⟩
      continuous_toFun := by fun_prop }
  Fin.cons g0 <| Fin.cons g1 <| Fin.cons gs <| finZeroElim

lemma mapVecOfBotTopSides_compatible_botOrTop
    (h : ∀ t y, f01 t (cubeBoundaryIncl _ y) = fs ⟨zeroOneIncl t, y⟩) :
    (∀ y hy0 hy2,
      (mapVecOfBotTopSides f01 fs 0) ⟨y, hy0⟩ =
      (mapVecOfBotTopSides f01 fs 2) ⟨y, hy2⟩ ) ∧
    ∀ y hy1 hy2,
      (mapVecOfBotTopSides f01 fs 1) ⟨y, hy1⟩ =
      (mapVecOfBotTopSides f01 fs 2) ⟨y, hy2⟩ := by
  constructor
  all_goals
    intro ⟨y, ⟨i, hi⟩⟩ hy01 hy2
    change f01 _ _ = fs _
    rw [Cube.splitAtLast_fst_eq, hy01, ← h _]; rfl

theorem mapVecOfBotTopSides_compatible
    (h : ∀ t y, f01 t (cubeBoundaryIncl _ y) = fs ⟨zeroOneIncl t, y⟩) :
    ∀ j k y hyj hyk,
      (mapVecOfBotTopSides f01 fs j) ⟨y, hyj⟩ =
      (mapVecOfBotTopSides f01 fs k) ⟨y, hyk⟩ := by
  intro j k ⟨y, ⟨i, hi⟩⟩ hyj hyk
  fin_cases j <;> (fin_cases k <;> (try simp only [Fin.zero_eta, Fin.mk_one]))  -- j = k
  · exact False.elim <| (by norm_num : (0 : I) ≠ 1) (hyj.symm.trans hyk)
  · apply (mapVecOfBotTopSides_compatible_botOrTop _ _ h).left
  · exact False.elim <| (by norm_num : (0 : I) ≠ 1) (hyk.symm.trans hyj)
  · apply (mapVecOfBotTopSides_compatible_botOrTop _ _ h).right
  · exact mapVecOfBotTopSides_compatible_botOrTop _ _ h |>.left _ hyk hyj |>.symm
  · exact mapVecOfBotTopSides_compatible_botOrTop _ _ h |>.right _ hyk hyj |>.symm

/-- `mapOfBotTopSides` -/
noncomputable def mapOfBotTopSides
  (h : ∀ t y, f01 t (cubeBoundaryIncl _ y) = fs ⟨zeroOneIncl t, y⟩) :
  ∂𝕀 (n + 1) ⟶ Z := ofHom <|
    ContinuousMap.liftCoverClosed (botTopSidesCover n)
      (mapVecOfBotTopSides f01 fs) (mapVecOfBotTopSides_compatible f01 fs h)
      (botTopSidesCover_cover n) (botTopSidesCover_closed n)

lemma cubeInclToBotOrTop_mapOfBotTopSides
    (h : ∀ t y, f01 t (cubeBoundaryIncl _ y) = fs ⟨zeroOneIncl t, y⟩)
    (t : zeroOne) :
    cubeInclToBotOrTop t ≫ mapOfBotTopSides f01 fs h = f01 t := by
  ext y
  simp only [hom_comp, ContinuousMap.comp_apply]
  obtain ht | ht := zeroOne.eq_zero_or_eq_one t
  all_goals subst ht
  · have hmem : (cubeInclToBotOrTop 0) y ∈ botTopSidesCover n 0 :=
      cubeInclToBotOrTop_mem_botOrTop 0 y
    have hlift := ContinuousMap.liftCoverClosed_coe' _ _ (mapVecOfBotTopSides_compatible f01 fs h)
      (botTopSidesCover_cover n) (botTopSidesCover_closed n) _ hmem
    change (ContinuousMap.liftCoverClosed (botTopSidesCover n) (mapVecOfBotTopSides f01 fs)
        (mapVecOfBotTopSides_compatible f01 fs h)
        (botTopSidesCover_cover n) (botTopSidesCover_closed n))
      ((cubeInclToBotOrTop 0).hom y) = _
    rw [hlift]
    unfold mapVecOfBotTopSides cubeInclToBotOrTop
    change (f01 0) ⟨(Cube.splitAtLast (Cube.splitAtLast.symm (0, y.down))).2⟩ = (f01 0) y
    rw [Homeomorph.apply_symm_apply]
    rfl
  · have hmem : (cubeInclToBotOrTop 1) y ∈ botTopSidesCover n 1 :=
      cubeInclToBotOrTop_mem_botOrTop 1 y
    have hlift := ContinuousMap.liftCoverClosed_coe' _ _ (mapVecOfBotTopSides_compatible f01 fs h)
      (botTopSidesCover_cover n) (botTopSidesCover_closed n) _ hmem
    change (ContinuousMap.liftCoverClosed (botTopSidesCover n) (mapVecOfBotTopSides f01 fs)
        (mapVecOfBotTopSides_compatible f01 fs h)
        (botTopSidesCover_cover n) (botTopSidesCover_closed n))
      ((cubeInclToBotOrTop 1).hom y) = _
    rw [hlift]
    unfold mapVecOfBotTopSides cubeInclToBotOrTop
    change (f01 1) ⟨(Cube.splitAtLast (Cube.splitAtLast.symm (1, y.down))).2⟩ = (f01 1) y
    rw [Homeomorph.apply_symm_apply]
    rfl


end TopCat.cubeBoundary  -- namespace
