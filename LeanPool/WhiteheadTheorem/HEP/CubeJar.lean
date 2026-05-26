/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.HEP.Cofibration
import LeanPool.WhiteheadTheorem.HEP.Retract
import LeanPool.WhiteheadTheorem.Shapes.Cube

/-!
This file proves that the pair `(∂𝕀 n, ⊔𝕀 n)` has the homotopy extension property for `n ≥ 1`.
-/

open scoped Topology Topology.Homotopy unitInterval


universe u


namespace TopCat

namespace cubeBoundaryJar

/-- `bot` -/
abbrev bot (n : ℕ) : Set (⊔𝕀 (n + 1)) := { ⟨⟨y, _⟩⟩ | y (Fin.last _) = 0 }
/-- `sides` -/
abbrev sides (n : ℕ) : Set (⊔𝕀 (n + 1)) := { ⟨⟨y, _⟩⟩ | ∃ i < Fin.last _, y i = 0 ∨ y i = 1 }
/-- `botSidesCover` -/
abbrev botSidesCover (n : ℕ) : Fin 2 → Set (⊔𝕀 (n + 1)) := ![bot n, sides n]

lemma botSidesCover_cover (n : ℕ) : ∀ y : ⊔𝕀 (n + 1), ∃ k, y ∈ botSidesCover n k := by
  intro ⟨⟨y, hy⟩⟩
  obtain hy | ⟨i, hi⟩ := Cube.mem_boundaryJar_iff_splitAtLast.mp hy
  · use 0; rwa [Cube.splitAtLast_fst_eq] at hy
  · use 1; obtain hi | hi := hi
    · use i.castSucc, Fin.castSucc_lt_last _; left; exact hi
    · use i.castSucc, Fin.castSucc_lt_last _; right; exact hi

lemma sides_eq_union (n : ℕ) :
    sides n =
      (⋃ (i : Fin n), {⟨⟨y, _⟩⟩ | y i.castSucc = 0}) ∪
      (⋃ (i : Fin n), {⟨⟨y, _⟩⟩ | y i.castSucc = 1}) := by
  ext ⟨⟨y, hy⟩⟩
  constructor
  · simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, forall_exists_index, and_imp]
    intro i hin hi; obtain hi | hi := hi
    · left; use ⟨i, hin⟩; exact hi
    · right; use ⟨i, hin⟩; exact hi
  · simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq]
    intro hi; obtain ⟨i, hi⟩ | ⟨i, hi⟩ := hi
    · use i.castSucc, Fin.castSucc_lt_last _; left; exact hi
    · use i.castSucc, Fin.castSucc_lt_last _; right; exact hi

lemma isClosed_bot (n : ℕ) : IsClosed (bot n) :=
  isClosed_eq ((continuous_apply _).comp (by fun_prop)) continuous_const

lemma isClosed_sides (n : ℕ) : IsClosed (sides n) := by
  rw [sides_eq_union]
  apply IsClosed.union
  all_goals exact isClosed_iUnion_of_finite fun i ↦
    isClosed_eq ((continuous_apply _).comp (by fun_prop)) continuous_const

lemma botSidesCover_closed (n : ℕ) : ∀ k, IsClosed (botSidesCover n k) := by
  intro k; fin_cases k; exacts [isClosed_bot n, isClosed_sides n]

end cubeBoundaryJar


namespace cubeBoundary

/-- `Cube.boundaryJar` as a subset of `Cube.boundary` -/
abbrev jar (n : ℕ) : Set (∂𝕀 (n + 1)) := {y | y.down.val ∈ Cube.boundaryJar (n + 1)}

/-- `jar n` can be written as the union of `2 * n + 1` surfaces of the `(n + 1)`-cube. -/
lemma jar_eq_union (n : ℕ) :
    jar n =
      (⋃ (i : Fin n), {⟨⟨y, _⟩⟩ | y i.castSucc = 0}) ∪
      (⋃ (i : Fin n), {⟨⟨y, _⟩⟩ | y i.castSucc = 1}) ∪
      {⟨⟨y, _⟩⟩ | y (Fin.last _) = 0} := by
  ext ⟨x, ⟨i, hi⟩⟩
  constructor
  all_goals simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq]
  · intro ⟨_, hxn⟩
    by_cases hin : i = Fin.last _
    · subst hin; obtain hi | hi := hi
      · right; exact hi
      · obtain ⟨j, hjn, hj⟩ := hxn hi
        left; obtain hj | hj := hj
        · left; use ⟨j, hjn⟩; exact hj
        · right; use ⟨j, hjn⟩; exact hj
    · left; obtain hi | hi := hi
      · left; use ⟨i, Fin.lt_last_iff_ne_last.mpr hin⟩; exact hi
      · right; use ⟨i, Fin.lt_last_iff_ne_last.mpr hin⟩; exact hi
  · intro hx
    obtain (⟨i, hi⟩ | ⟨i, hi⟩) | hx := hx
    · apply Cube.mem_boundaryJar_of_lt_last; use i.castSucc, Fin.castSucc_lt_last _; left; exact hi
    · apply Cube.mem_boundaryJar_of_lt_last; use i.castSucc, Fin.castSucc_lt_last _; right; exact hi
    · apply Cube.mem_boundaryJar_of_exists_eq_zero; use Fin.last _

lemma isClosed_jar (n : ℕ) : IsClosed (jar n) := by
  rw [jar_eq_union]
  apply IsClosed.union
  · apply IsClosed.union
    all_goals exact isClosed_iUnion_of_finite fun i ↦
      isClosed_eq ((continuous_apply _).comp (by fun_prop)) continuous_const
  · exact isClosed_eq ((continuous_apply _).comp (by fun_prop)) continuous_const

end cubeBoundary


namespace cubeBoundaryProdI  -- ∂𝕀 (n + 1) × I

/-- The back surface of `∂𝕀 (n + 1) × I` -/
abbrev back (n : ℕ) : Set (∂𝕀 (n + 1) × I) := { pt | pt.fst.down.val ∈ Cube.boundaryLid (n + 1) }
-- abbrev back (n : ℕ) : Set (∂𝕀 (n + 1) × I) := { ⟨⟨⟨y, _⟩⟩, _⟩ | y (Fin.last _) = 1 }

/-- The front, left, and right surfaces of `∂𝕀 (n + 1) × I` -/
abbrev flr (n : ℕ) : Set (∂𝕀 (n + 1) × I) := { pt | pt.fst.down.val ∈ Cube.boundaryJar (n + 1) }

/-- `backFlrCover` -/
abbrev backFlrCover (n : ℕ) : Fin 2 → Set (∂𝕀 (n + 1) × I) := ![back n, flr n]

lemma backFlrCover_cover (n : ℕ) :
    ∀ pt : ∂𝕀 (n + 1) × I, ∃ k, pt ∈ backFlrCover n k := by
  intro ⟨⟨y, hy⟩, _⟩
  by_cases hyn : y (Fin.last _) = 1
  · use 0; exact hyn
  · use 1; refine ⟨hy, ?_⟩; intro hyn'; contradiction

lemma flr_eq_sprod (n : ℕ) : flr n = cubeBoundary.jar n ×ˢ Set.univ := by
  ext x : 1
  simp_all only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true]

lemma isClosed_back (n : ℕ) : IsClosed (back n) :=
  isClosed_eq ((continuous_apply _).comp (by fun_prop)) continuous_const

lemma isClosed_flr (n : ℕ) : IsClosed (flr n) := by
  rw [flr_eq_sprod]
  exact IsClosed.prod (cubeBoundary.isClosed_jar n) isClosed_univ

lemma backFlrCover_closed (n : ℕ) : ∀ k, IsClosed (backFlrCover n k) := by
  intro k; fin_cases k; exacts [isClosed_back n, isClosed_flr n]

/-- `backIsoCube` -/
def backIsoCube (n : ℕ) : back n ≃ₜ (I^ Fin (n + 1)) where
  toFun := fun ⟨⟨⟨y, _⟩, t⟩, hy⟩ ↦ Cube.splitAtLast.symm ⟨t, (Cube.splitAtLast y).snd⟩
  invFun := fun y ↦
    let y' := Cube.splitAtLast.symm ⟨1, (Cube.splitAtLast y).snd⟩
    haveI : y' (Fin.last n) = 1 := by unfold y'; rw [Cube.splitAtLast_symm_apply_last]
    ⟨⟨⟨y', ⟨Fin.last n, Or.inr ‹_›⟩⟩, (Cube.splitAtLast y).fst⟩, ‹_›⟩
  left_inv := by
    intro ⟨⟨⟨y, hyb⟩, t⟩, hyl⟩
    change y ∈ Cube.boundaryLid (n + 1) at hyl
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Homeomorph.apply_symm_apply, Subtype.mk.injEq,
      Prod.mk.injEq, and_true]
    congr 2
    ext i
    congr 1
    by_cases hin : i = Fin.last _
    · rw [hin, Cube.splitAtLast_symm_apply_last, hyl]
    · rw [Cube.splitAtLast_symm_apply_eq_of_neq_last _ _ _ hin]; rfl
  right_inv y := by
    simp only [Homeomorph.apply_symm_apply, Prod.mk.eta, Homeomorph.symm_apply_apply]
  continuous_toFun := by fun_prop
  continuous_invFun := by simp only [Set.coe_setOf, Set.mem_setOf_eq]; fun_prop


variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]
variable (f : C(∂𝕀 (n + 1), Y))
variable (h : C(⊔𝕀 (n + 1) × I, Y))



open cubeBoundaryJar

/-- `jarBotMap` -/
def jarBotMap : C(bot n, Y) where
  toFun := fun ⟨⟨⟨y, _⟩⟩, hy⟩ ↦
    let y' : I^ Fin (n + 1) := Cube.splitAtLast.symm ⟨1, (Cube.splitAtLast y).snd⟩
    haveI : y' ∈ ∂I^ (n + 1) := by
      use Fin.last _; right; unfold y'; rw [Cube.splitAtLast_symm_apply_last]
    f ⟨⟨y', ‹_›⟩⟩
  continuous_toFun := by simp only [Set.coe_setOf, Set.mem_setOf_eq]; fun_prop

/-- `jarSidesMap` -/
def jarSidesMap : C(sides n, Y) where
  toFun := fun ⟨⟨⟨y, _⟩⟩, hy⟩ ↦
    let y' : I^ Fin (n + 1) := Cube.splitAtLast.symm ⟨1, (Cube.splitAtLast y).snd⟩
    haveI : y' ∈ ⊔I^ (n + 1) := by
      apply Cube.mem_boundaryJar_of_lt_last
      obtain ⟨i, hin, hi⟩ := hy; use i, hin
      unfold y'
      rwa [Cube.splitAtLast_symm_apply_eq_of_neq_last _ _ _ (Fin.lt_last_iff_ne_last.mp hin)]
    h ⟨⟨⟨y', ‹_›⟩⟩, (Cube.splitAtLast y).fst⟩
  continuous_toFun := by simp only [Set.coe_setOf, Set.mem_setOf_eq]; fun_prop

/-- `botSidesCoverMapVec` -/
def botSidesCoverMapVec : (k : Fin 2) → C(botSidesCover n k, Y) :=
  Fin.cons (jarBotMap f) <| Fin.cons (jarSidesMap h) <| finZeroElim

/--
`jarBotMap` and `jarSidesMap` agree at the intersection of
`cubeBoundaryJar.bot` and `cubeBoundaryJar.sides`.
```
|     |
|     |
*_____*
```
-/
lemma botSidesCoverMapVec_compatible_01
    (fh : f ∘ cubeBoundaryJarInclToBoundary (n + 1) = h ∘ fun x ↦ (x, 0)) :
    ∀ y hy0 hy1,
      (botSidesCoverMapVec f h 0) ⟨y, hy0⟩ =
      (botSidesCoverMapVec f h 1) ⟨y, hy1⟩ := by
  intro ⟨y, ⟨i, hi⟩⟩ hy0 hy1
  change jarBotMap _ _ = jarSidesMap _ _
  unfold jarBotMap jarSidesMap
  let y' : I^ Fin (n + 1) := Cube.splitAtLast.symm ⟨1, (Cube.splitAtLast y).snd⟩
  have hsplit : (Cube.splitAtLast y).1 = 0 := by
    rw [Cube.splitAtLast_fst_eq]; exact hy0
  change f ⟨y', _⟩ = h ⟨⟨y', _⟩, (Cube.splitAtLast y).1⟩
  rw [hsplit]
  generalize_proofs
  have := congrFun fh ⟨y', ‹_›⟩
  simp only [Function.comp_apply] at this
  rw [← this]
  rfl

lemma botSidesCoverMapVec_compatible
    (fh : f ∘ (cubeBoundaryJarInclToBoundary (n + 1)) = h ∘ fun x ↦ (x, 0)) :
    ∀ j k y hyj hyk,
      (botSidesCoverMapVec f h j) ⟨y, hyj⟩ =
      (botSidesCoverMapVec f h k) ⟨y, hyk⟩ := by
  intro j k y hyj hyk
  fin_cases j <;> (fin_cases k <;> (try simp only [Fin.zero_eta, Fin.mk_one]))  -- j = k
  · apply botSidesCoverMapVec_compatible_01 _ _ fh
  · exact (botSidesCoverMapVec_compatible_01 _ _ fh ..).symm

/-- `jarMap` -/
noncomputable def jarMap
    (fh : f ∘ (cubeBoundaryJarInclToBoundary (n + 1)) = h ∘ fun x ↦ (x, 0)) :
    C(⊔𝕀 (n + 1), Y) :=
  ContinuousMap.liftCoverClosed (botSidesCover n)
    (botSidesCoverMapVec f h) (botSidesCoverMapVec_compatible f h fh)
    (botSidesCover_cover n) (botSidesCover_closed n)



/-- `backMap` -/
noncomputable def backMap
    (fh : f ∘ (cubeBoundaryJarInclToBoundary (n + 1)) = h ∘ fun x ↦ (x, 0)) :
    C(back n, Y) where
  toFun := fun yt ↦
    let r := Cube.strongDeformRetrToBoundaryJar n
    let yt' := r.r (backIsoCube n yt)
    -- let yt'' := backIsoCube.{u}.symm yt'
    jarMap f h fh <| ULift.up.{u} ⟨yt', Set.range_subset_iff.mp r.r_range _⟩
  continuous_toFun := by simp only [Set.coe_setOf]; fun_prop

/-- `flrMap` -/
def flrMap : C(flr n, Y) where
  toFun := fun ⟨⟨⟨y, _⟩, t⟩, hy⟩ ↦ h ⟨⟨y, hy⟩, t⟩
  continuous_toFun := by fun_prop

/-- `backFlrCoverMapVec` -/
noncomputable def backFlrCoverMapVec
    (fh : f ∘ (cubeBoundaryJarInclToBoundary (n + 1)) = h ∘ fun x ↦ (x, 0)) :
    (k : Fin 2) → C(backFlrCover n k, Y) :=
  Fin.cons (backMap f h fh) <| Fin.cons (flrMap h) <| finZeroElim

/--
`backMap` and `flrMap` agree on the edges of the back surface.
```
  __________
 /*        /*
/ *       / *
----------  *
| *      |  *
| *______|__*
| /      | /
|/_______|/
```
-/
lemma backFlrCover_mapVec_compatible_01
    (fh : f ∘ (cubeBoundaryJarInclToBoundary (n + 1)) = h ∘ fun x ↦ (x, 0)) :
    ∀ y hy0 hy1,
      (backFlrCoverMapVec f h fh 0) ⟨y, hy0⟩ =
      (backFlrCoverMapVec f h fh 1) ⟨y, hy1⟩ := by
  intro ⟨⟨y, ⟨i, hi⟩⟩, t⟩ hy0 hy1
  change y ∈ Cube.boundaryLid (n + 1) at hy0
  change y ∈ ⊔I^ (n + 1) at hy1
  let yt : back.{u} n := ⟨⟨⟨y, ⟨i, hi⟩⟩, t⟩, hy0⟩
  let r := Cube.strongDeformRetrToBoundaryJar n
  let yt' := r.r (backIsoCube n yt)
  have yt'_mem : yt' ∈ ⊔I^n + 1 := Set.range_subset_iff.mp r.r_range _
  change (jarMap f h fh) (ULift.up.{u} ⟨yt', ‹_›⟩) = h ⟨⟨ ⟨y, hy1⟩ ⟩, t⟩
  have : backIsoCube n yt ∈ ⊔I^ (n + 1) := by
    change Cube.splitAtLast.symm ⟨t, (Cube.splitAtLast y).snd⟩ ∈ ⊔I^ (n + 1)
    obtain ⟨i, hin, hi⟩ := hy1.right hy0
    apply Cube.mem_boundaryJar_of_lt_last
    use i, hin
    rwa [Cube.splitAtLast_symm_apply_eq_of_neq_last _ _ _ (Fin.lt_last_iff_ne_last.mp hin)]
  let yt_jar : ⊔𝕀 (n + 1) := ULift.up.{u} ⟨backIsoCube n yt, ‹_›⟩
  -- `backIsoCube n yt` is fixed by `r.r`
  replace : yt' = backIsoCube n yt := by
    convert r.H.prop' 1 yt_jar.down.val yt_jar.down.property
    simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.id_apply,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.apply_one]
  simp only [this]
  change (jarMap f h fh) yt_jar = _
  replace : yt_jar ∈ cubeBoundaryJar.botSidesCover n 1 := by
    obtain ⟨i, hin, hi⟩ := hy1.right hy0
    use i, hin
    unfold backIsoCube yt
    change Cube.splitAtLast.symm (t, (Cube.splitAtLast y).2) i = 0 ∨
        Cube.splitAtLast.symm (t, (Cube.splitAtLast y).2) i = 1
    rwa [Cube.splitAtLast_symm_apply_eq_of_neq_last _ _ _ (Fin.lt_last_iff_ne_last.mp hin)]
  replace := ContinuousMap.liftCoverClosed_coe' _ _ (botSidesCoverMapVec_compatible f h fh)
    (cubeBoundaryJar.botSidesCover_cover n) (cubeBoundaryJar.botSidesCover_closed n) _ this
  rw [jarMap, this]
  change jarSidesMap _ _ = _
  unfold jarSidesMap yt_jar yt backIsoCube
  change h ({ down := ⟨Cube.splitAtLast.symm (1, (Cube.splitAtLast
      (Cube.splitAtLast.symm (t, (Cube.splitAtLast y).2))).2), _⟩ },
      (Cube.splitAtLast (Cube.splitAtLast.symm (t, (Cube.splitAtLast y).2))).1) =
      h ({ down := ⟨y, hy1⟩ }, t)
  simp only [Homeomorph.apply_symm_apply]
  congr 2
  apply ULift.ext
  apply Subtype.ext
  change Cube.splitAtLast.symm (1, (Cube.splitAtLast y).2) = y
  funext i
  by_cases hin : i = Fin.last _
  · rw [hin, Cube.splitAtLast_symm_apply_last, hy0]
  · rw [Cube.splitAtLast_symm_apply_eq_of_neq_last _ _ _ hin]; rfl

lemma backFlrCover_mapVec_compatible
    (fh : f ∘ (cubeBoundaryJarInclToBoundary (n + 1)) = h ∘ fun x ↦ (x, 0)) :
    ∀ j k y hyj hyk,
      (backFlrCoverMapVec f h fh j) ⟨y, hyj⟩ =
      (backFlrCoverMapVec f h fh k) ⟨y, hyk⟩ := by
  intro j k y hyj hyk
  fin_cases j <;> (fin_cases k <;> (try simp only [Fin.zero_eta, Fin.mk_one]))  -- j = k
  · apply backFlrCover_mapVec_compatible_01 _ _ fh
  · exact (backFlrCover_mapVec_compatible_01 _ _ fh ..).symm

end cubeBoundaryProdI


open cubeBoundaryProdI in
theorem cubeBoundaryJarInclToBoundary_hasHEP
    (n : ℕ) (Y : Type u) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty (cubeBoundaryJarInclToBoundary (n + 1)).hom Y := by
  intro f h fh
  let H : C(cubeBoundary.{u} (n + 1) × I, Y) :=
    ContinuousMap.liftCoverClosed (backFlrCover n)
      (backFlrCoverMapVec f h fh) (backFlrCover_mapVec_compatible f h fh)
      (backFlrCover_cover n) (backFlrCover_closed n)
  use H
  constructor
  · ext ⟨y, ⟨i, hyi⟩⟩
    simp only [Function.comp_apply]
    let yb : cubeBoundary.{u} (n + 1) := ⟨y, ⟨i, hyi⟩⟩
    let yb_t : cubeBoundary.{u} (n + 1) × I := ⟨yb, 0⟩
    by_cases hyn : y (Fin.last _) = 1
    · --     __________
      --    /|        /|
      --   / |       / |
      --   ----------  |
      --   | |      |  |
      --   |  ******|***
      --   | /      | /
      --   |/_______|/
      have := ContinuousMap.liftCoverClosed_coe' _ _ (backFlrCover_mapVec_compatible f h fh)
        (backFlrCover_cover n) (backFlrCover_closed n) _
        (show yb_t ∈ backFlrCover n 0 by exact hyn)
      simp only [Fin.isValue, Matrix.cons_val_zero, Set.coe_setOf, Set.mem_setOf_eq] at this
      rw [this]
      let r := Cube.strongDeformRetrToBoundaryJar n
      let yt_back : back n := ⟨yb_t, hyn⟩
      let yt' := r.r (backIsoCube n yt_back)
      change f yb = backMap f h fh yt_back
      unfold backMap
      simp only [Set.coe_setOf, Set.mem_setOf_eq]
      change _ = jarMap f h fh ⟨⟨yt', _⟩⟩
      replace : backIsoCube n yt_back ∈ ⊔I^ (n + 1) := by
        change Cube.splitAtLast.symm ⟨0, (Cube.splitAtLast y).snd⟩ ∈ ⊔I^ (n + 1)
        apply Cube.mem_boundaryJar_of_exists_eq_zero
        use Fin.last _
        rw [Cube.splitAtLast_symm_apply_last]
      -- `backIsoCube n yt` is fixed by `r.r`
      let yt_jar : ⊔𝕀 (n + 1) := ULift.up.{u} ⟨backIsoCube n yt_back, ‹_›⟩
      replace : yt' = backIsoCube n yt_back := by
        convert r.H.prop' 1 yt_jar.down.val yt_jar.down.property
        simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.id_apply,
          ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.apply_one]
      simp only [this]
      change _ = jarMap f h fh yt_jar
      replace : yt_jar ∈ cubeBoundaryJar.botSidesCover n 0 := by
        change _ ∈ cubeBoundaryJar.bot n
        unfold cubeBoundaryJar.bot yt_jar backIsoCube yt_back yb_t yb
        change Cube.splitAtLast.symm (0, (Cube.splitAtLast y).2) (Fin.last n) = 0
        rw [Cube.splitAtLast_symm_apply_last]
      replace := ContinuousMap.liftCoverClosed_coe' _ _ (botSidesCoverMapVec_compatible f h fh)
        (cubeBoundaryJar.botSidesCover_cover n) (cubeBoundaryJar.botSidesCover_closed n) _ this
      simp only [Fin.isValue, Matrix.cons_val_zero, Set.coe_setOf, Set.mem_setOf_eq] at this
      rw [jarMap, this]
      change _ = jarBotMap f _
      unfold jarBotMap yt_jar yb
      change f { down := ⟨y, _⟩ } =
        f { down := ⟨Cube.splitAtLast.symm
          (1, (Cube.splitAtLast ((backIsoCube n) yt_back)).2), _⟩ }
      congr 2
      apply Subtype.ext
      change y = Cube.splitAtLast.symm (1, (Cube.splitAtLast ((backIsoCube n) yt_back)).2)
      funext i
      by_cases hin : i = Fin.last _
      · rw [hin, Cube.splitAtLast_symm_apply_last, hyn]
      · rw [Cube.splitAtLast_symm_apply_eq_of_neq_last _ _ _ hin]
        unfold yt_back yb_t yb backIsoCube
        change y i = (Cube.splitAtLast (Cube.splitAtLast.symm (0, (Cube.splitAtLast y).2))).2
          ⟨i.val, ?_⟩
        rw [Homeomorph.apply_symm_apply]
        rfl
    · --     __________
      --    /|        /|
      --   / |       / |
      --   ----------  |
      --   | |      |  |
      --   |  *_____|__*
      --   | *      | *
      --   |********|*
      have : y ∈ ⊔I^ (n + 1) := ⟨⟨i, hyi⟩, fun _ ↦ by contradiction⟩
      let yj : cubeBoundaryJar.{u} (n + 1) := ⟨⟨y, ‹_›⟩⟩
      have := ContinuousMap.liftCoverClosed_coe' _ _ (backFlrCover_mapVec_compatible f h fh)
        (backFlrCover_cover n) (backFlrCover_closed n) _
        (show yb_t ∈ backFlrCover n 1 by assumption)
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Set.coe_setOf,
        Set.mem_setOf_eq] at this
      rw [this]
      change _ = flrMap h _
      unfold flrMap yb_t yb
      simp only [Set.coe_setOf, Set.mem_setOf_eq]
      change f yb = h ⟨yj, 0⟩
      replace := congrFun fh yj
      simp only [Function.comp_apply] at this
      rw [← this]
      rfl
  · ext ⟨⟨y, hy⟩, t⟩
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    let yb_t : cubeBoundary.{u} (n + 1) × I := ⟨⟨y, Cube.boundaryJar_subset_boundary _ hy⟩, t⟩
    change _ = H yb_t
    have := ContinuousMap.liftCoverClosed_coe' _ _ (backFlrCover_mapVec_compatible f h fh)
      (backFlrCover_cover n) (backFlrCover_closed n) _
      (show yb_t ∈ backFlrCover n 1 by exact hy)
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Set.coe_setOf,
      Set.mem_setOf_eq] at this
    rw [this]
    rfl

end TopCat
