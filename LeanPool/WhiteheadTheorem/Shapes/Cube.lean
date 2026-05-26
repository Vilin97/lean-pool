/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.Auxiliary
import LeanPool.WhiteheadTheorem.Shapes.UnitInterval
import Mathlib.Topology.Homotopy.HomotopyGroup


open scoped unitInterval Topology Topology.Homotopy


namespace Cube

/-- `Cube.boundaryJar (n + 1) = ∂Iⁿ × I ∪ Iⁿ × {0} ⊆ Iⁿ⁺¹` -/
def boundaryJar (n : ℕ) : Set (I^ Fin n) :=
  match n with
  | 0 => ∅
  | _ + 1 => {y | (∃ i, y i = 0 ∨ y i = 1) ∧
      (y (Fin.last _) = 1 → ∃ i < Fin.last _, y i = 0 ∨ y i = 1) }

/-- `Cube.boundaryLid (n + 1) = Iⁿ × {1} ⊆ Iⁿ⁺¹` -/
def boundaryLid (n : ℕ) : Set (I^ Fin n) :=
  match n with
  | 0 => ∅
  | _ + 1 => {y | y (Fin.last _) = 1}

/-- `«term∂I^_»` -/
scoped[Topology.Homotopy] notation "∂I^" n => Cube.boundary (Fin n)
/-- `«term⊔I^_»` -/
scoped[Topology.Homotopy] notation "⊔I^" n => Cube.boundaryJar n

/-- `boundaryIncl` -/
def boundaryIncl (n : ℕ) : C(∂I^n, I^ (Fin n)) := ⟨Subtype.val, continuous_subtype_val⟩
/-- `boundaryJarIncl` -/
def boundaryJarIncl (n : ℕ) : C(⊔I^n, I^ (Fin n)) := ⟨Subtype.val, continuous_subtype_val⟩

instance isEmpty_boundary_zero : IsEmpty (∂I^0) :=
  Set.isEmpty_coe_sort.mpr <| Set.subset_empty_iff.mp fun _ ⟨i, _⟩ ↦ isEmptyElim i
instance isEmpty_boundaryJar_zero : IsEmpty (⊔I^0) := by
  rw [Set.isEmpty_coe_sort]; rfl

lemma boundaryJar_subset_boundary (n : ℕ) : (⊔I^n) ⊆ (∂I^n) :=
  match n with
  | 0 => fun y hy ↦ isEmptyElim (⟨y, hy⟩ : ⊔I^0)
  | _ + 1 => fun _ ⟨hy1, _⟩ ↦ hy1

/-- `boundaryJarInclToBoundary` -/
def boundaryJarInclToBoundary (n : ℕ) : C(⊔I^n, ∂I^n) where
  toFun := fun ⟨y, hy⟩ ↦ ⟨y, boundaryJar_subset_boundary n hy⟩
  continuous_toFun := by fun_prop

lemma mem_boundaryJar_of_lt_last {n : ℕ} (y : I^(Fin (n + 1)))
    (hy : ∃ i < Fin.last _, y i = 0 ∨ y i = 1) : y ∈ ⊔I^(n+1) := by
  obtain ⟨i, ⟨hi, hyi⟩⟩ := hy
  constructor
  · exact ⟨i, hyi⟩
  · intro _; exact ⟨i, ⟨hi, hyi⟩⟩

lemma mem_boundaryJar_of_exists_eq_zero {n : ℕ} (y : I^Fin n)
    (hy : ∃ i, y i = 0) : y ∈ ⊔I^n :=
  match n with
  | 0 => isEmptyElim hy.choose
  | n + 1 => by
      obtain ⟨i, hi⟩ := hy
      constructor
      · use i; left; exact hi
      · intro hn1
        by_cases h : i = Fin.last _
        · rw [← h] at hn1; exfalso; exact (by norm_num : (1 : I) ≠ 0) (hn1.symm.trans hi)
        · use i; exact ⟨Fin.lt_last_iff_ne_last.mpr h, Or.inl hi⟩

lemma mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary {n : ℕ} (y : I^Fin n)
    (hy : y ∈ ∂I^n) : y ∈ Cube.boundaryLid n ∨ y ∈ ⊔I^n :=
  match n with
  | 0 => isEmptyElim (⟨y, hy⟩ : ∂I^0)
  | n + 1 => by
      by_cases hyn : y (Fin.last _) = 1
      · left; exact hyn
      · right
        constructor
        · exact hy
        · intro hyn'; exfalso; exact hyn hyn'

/-- `⊔I^1 = {0}` is a singleton -/
instance uniqueBoundaryJarOne : Unique (⊔I^1) where
  default := ⟨0,
    ⟨ by use 0; simp only [Pi.zero_apply, zero_ne_one, or_false],
      by intro h; simp only [Pi.zero_apply, zero_ne_one] at h ⟩ ⟩
  uniq := fun ⟨y, ⟨⟨i, hi⟩, hy2⟩⟩ ↦ by
    ext j
    have : Unique (Fin 1) := by infer_instance
    have iz : i = 0 := Subsingleton.eq_zero i
    have jz : j = 0 := Subsingleton.eq_zero j
    rw [iz] at hi
    obtain h0 | h1 := hi
    all_goals simp only [Pi.zero_apply, Set.Icc.coe_zero, Set.Icc.coe_eq_zero]; rw [jz]
    · exact h0
    · exfalso; obtain ⟨k, hk⟩ := hy2 h1; exact Nat.not_succ_le_zero k hk.left

/-- `homeoNeqLast` -/
def homeoNeqLast {n : ℕ} : (I^ Fin n) ≃ₜ I^{ j : Fin (n + 1) // j ≠ Fin.last _ } :=
  Homeomorph.piCongr
    { toFun i := ⟨i.castSucc, by
        simp only [ne_eq]
        exact Fin.lt_last_iff_ne_last.mp i.2 ⟩
      invFun i := ⟨i, by
        have := i.2
        simp only [ne_eq] at this
        exact Fin.lt_last_iff_ne_last.mpr this ⟩
      left_inv i := by simp only [Fin.val_castSucc, Fin.eta]
      right_inv i := by simp only [ne_eq, Fin.castSucc_mk, Fin.eta, Subtype.coe_eta] }
    fun _ ↦ Homeomorph.refl _

/-- A homeomorphism that sends `(y₀, y₁, …, yₙ₋₁, yₙ)` to `(yₙ, (y₀, y₁, …, yₙ₋₁))` -/
def splitAtLast {n : ℕ} : (I^ Fin (n + 1)) ≃ₜ I × (I^ Fin n) :=
  splitAt (Fin.last _) |>.trans <|
    Homeomorph.prodCongr (Homeomorph.refl _) homeoNeqLast.symm

/-- A homeomorphism that sends `(y₀, y₁, …, yₙ₋₁, yₙ)` to `((y₀, y₁, …, yₙ₋₁), yₙ)` -/
def splitAtLastComm {n : ℕ} : (I^ Fin (n + 1)) ≃ₜ (I^ Fin n) × I :=
  splitAtLast.trans <| Homeomorph.prodComm I (I^ Fin n)

lemma splitAtLast_fst_eq {n : ℕ} (y : I^Fin (n + 1)) :
    (splitAtLast y).fst = y (Fin.last n) := by
  simp only [splitAtLast, ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
    Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq]

lemma splitAtLastComm_snd_eq {n : ℕ} (y : I^Fin (n + 1)) :
    (splitAtLastComm y).snd = y (Fin.last n) := by
  simp only [splitAtLastComm, splitAtLast, ne_eq, Homeomorph.trans_apply,
    Homeomorph.funSplitAt_apply, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq, Homeomorph.coe_prodComm, Prod.swap_prod_mk]

lemma splitAtLast_snd_eq {n : ℕ} (y : I^Fin (n + 1)) :
    (splitAtLast y).snd = (splitAtLastComm y).fst := by
  simp only [splitAtLast, ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
    Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq,
    splitAtLastComm, Homeomorph.coe_prodComm, Prod.swap_prod_mk]

lemma splitAtLast_snd_apply_eq {n : ℕ} (y : I^Fin (n + 1)) (i : Fin n) :
    (splitAtLast y).snd i = y i.castSucc := by
  simp only [splitAtLast, ne_eq, homeoNeqLast, Homeomorph.trans_apply,
    Homeomorph.funSplitAt_apply, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq]
  rfl

lemma splitAtLast_symm_apply_last {n : ℕ} (t : I) (y : I^Fin n) :
    (splitAtLast.symm ⟨t, y⟩) (Fin.last _) = t := by
  simp only [splitAtLast, ne_eq, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply,
    Prod.map_apply, id_eq, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]

lemma splitAtLast_symm_apply_eq_of_neq_last {n : ℕ} (t : I) (y : I^Fin n) (i : Fin (n + 1))
    (hi : i ≠ Fin.last _) :
    (splitAtLast.symm ⟨t, y⟩) i = y ⟨i, Fin.lt_last_iff_ne_last.mpr hi⟩ := by
  simp only [splitAtLast, ne_eq, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply,
    Prod.map_apply, id_eq, Homeomorph.funSplitAt_symm_apply]
  simp only [homeoNeqLast, ne_eq, Homeomorph.piCongr_apply]
  simp_all only []
  rfl

/-- `y ∈ ⊔I^(n+1)` if and only if either `y` is on the bottom face,
or its first `n` coordinates constitute a point in `∂I^n`.
Note that `(splitAtLast y).fst` is the last (`n`-th) coordinate. -/
lemma mem_boundaryJar_iff_splitAtLast {n : ℕ} {y : I^Fin (n + 1)} :
    y ∈ (⊔I^(n+1)) ↔ (splitAtLast y).fst = 0 ∨ (splitAtLast y).snd ∈ ∂I^n := by
  constructor
  · intro hy
    simp only [splitAtLast, ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
      Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq]
    by_cases h0 : y (Fin.last n) = 0
    · left; exact h0
    · right
      by_cases h1 : y (Fin.last n) = 1
      · have := hy.right h1
        obtain ⟨i, hi, h⟩ := hy.right h1
        use ⟨i, hi⟩
        rcases h with h | h
        · left; change (homeoNeqLast.invFun _) _ = 0; simpa [homeoNeqLast]
        · right; change (homeoNeqLast.invFun _) _ = 1; simpa [homeoNeqLast]
      · obtain ⟨i, h⟩ := hy.left
        have : i ≠ (Fin.last n) := fun hn ↦ by
          rw [hn] at h; rcases h with h | h; exacts [h0 h, h1 h]
        use ⟨i.val, Fin.lt_last_iff_ne_last.mpr this⟩
        rcases h with h | h
        · left; change (homeoNeqLast.invFun _) _ = 0; simpa [homeoNeqLast]
        · right; change (homeoNeqLast.invFun _) _ = 1; simpa [homeoNeqLast]
  · intro hy
    rcases hy with hy | ⟨i, hi⟩
    · rw [splitAtLast_fst_eq] at hy
      apply mem_boundaryJar_of_exists_eq_zero
      use Fin.last n
    · rw [splitAtLast_snd_apply_eq] at hi
      constructor
      · use i.castSucc
      · intro hyn
        use i.castSucc
        exact ⟨Fin.castSucc_lt_last i, hi⟩

/-- An easy corrolary of `mem_boundaryJar_iff_splitAtLast` -/
lemma splitAtLast_snd_mem_boundary_of_last_neq_zero {n : ℕ} {y : I^Fin (n + 1)}
    (hy : y ∈ ⊔I^(n + 1)) (hyn : y (Fin.last _) ≠ 0) :
    (splitAtLast y).snd ∈ ∂I^n := by
  rw [← splitAtLast_fst_eq y] at hyn
  cases mem_boundaryJar_iff_splitAtLast.mp hy
  · exfalso; exact hyn ‹_›
  · assumption

lemma splitAtLast_symm_mem_boundary_of_mem_boundary
    {n : ℕ} {y : I^Fin n} (t : I) (hy : y ∈ ∂I^n) :
    splitAtLast.symm ⟨t, y⟩ ∈ ∂I^(n + 1) := by
  obtain ⟨i, hi⟩ := hy
  use i.castSucc
  rw [splitAtLast_symm_apply_eq_of_neq_last t y i.castSucc (Fin.castSucc_ne_last i)]
  exact hi

/-- The inclusion from the n-dimensional cube to the top face of the (n+1)-dimensional cube,
mapping (y₀, y₁, …, yₙ₋₁) to (y₀, y₁, …, yₙ₋₁, 1).
(Although `1` appears first in this definition, it is actually the last coordinate
in `(I^ Fin (n + 1))`, due to `Cube.insertAt`). -/
def inclToTop {n : ℕ} : C(I^ Fin n, I^ Fin (n + 1)) where
  toFun y := splitAtLast.symm ⟨1, y⟩
  continuous_toFun := splitAtLast.symm.continuous.comp <|
    Continuous.prodMk continuous_const continuous_id

namespace inclToTop

/-- (y, 1) is in the `boundary`. -/
lemma mem_boundary {n : ℕ} (y : I^Fin n) : inclToTop y ∈ ∂I^(n + 1) := by
  use Fin.last _
  right
  simp only [inclToTop, splitAtLast, ne_eq, Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq, ContinuousMap.coe_mk,
    Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]

/-- If y is in the `boundary`, then (y, 1) is in the `boundaryJar`. -/
lemma mem_boundaryJar_of {n : ℕ} {y : I^Fin n}
    (hy : y ∈ ∂I^n) : inclToTop y ∈ ⊔I^(n + 1) := by
  obtain ⟨i, hi⟩ := hy
  simp only [inclToTop, ContinuousMap.coe_mk]
  constructor
  · use Fin.last _        -- the n-th coordinate of (y, 1) is 1
    simp only [splitAtLast, ne_eq, Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte,
    one_ne_zero, or_true]
  · intro _
    use i.castSucc         -- the i-th coordinate of (y, 1) is 0 or 1, where i < n
    constructor
    · simp only [Fin.castSucc_lt_last]
    · simpa only [splitAtLast, ne_eq, homeoNeqLast, Fin.coe_eq_castSucc,
      Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm, Homeomorph.refl_symm,
      Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq,
      Homeomorph.funSplitAt_symm_apply, Fin.natCast_eq_last, Fin.castSucc_ne_last, ↓reduceDIte,
      Homeomorph.piCongr_apply, Equiv.coe_fn_symm_mk, Fin.val_castSucc, Fin.eta]

end inclToTop

lemma splitAtLast_inclToTop_eq {n : ℕ} {y : I^Fin n} :
    splitAtLast (inclToTop y) = ⟨1, y⟩ := by
  simp only [splitAtLast, ne_eq, inclToTop, Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq, ContinuousMap.coe_mk, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]

/-- `(y₀, y₁, …, yₙ₋₁, yₙ) ↦ (y₀, y₁, …, yₙ₋₁)` -/
def discardLast {n : ℕ} : C(I^ Fin (n + 1), I^ Fin n) where
  toFun y := fun i ↦ y ⟨i.val, i.prop.trans (by omega : n < n + 1)⟩
  continuous_toFun := by fun_prop

/-- (y₀, y₁, …, yₙ₋₁) ↦ (y₀, y₁, …, yₙ₋₁, 0) -/
def inclToBot {n : ℕ} : C(I^ Fin n, I^ Fin (n + 1)) where
  toFun y := Cube.insertAt (Fin.last _) ⟨0, Cube.homeoNeqLast y⟩
  continuous_toFun := (Cube.insertAt _).continuous.comp <|
    Continuous.prodMk continuous_const Cube.homeoNeqLast.continuous

namespace inclToBot

/-- (y, 0) is in the `boundary`. -/
lemma mem_boundary {n : ℕ} (y : I^Fin n) : inclToBot y ∈ ∂I^(n + 1) := by
  use Fin.last _
  left
  simp only [inclToBot, ne_eq, ContinuousMap.coe_mk,
    Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]

/-- (y, 0) is in the `boundaryJar`. -/
lemma mem_boundaryJar {n : ℕ} (y : I^Fin n) : inclToBot y ∈ ⊔I^(n + 1) := by
  constructor
  · exact mem_boundary y
  · intro h; exfalso
    have : inclToBot y (Fin.last n) = (0 : ℝ) := by simp [inclToBot]
    refine (by norm_num : (0 : ℝ) ≠ (1 : ℝ)) <| this.symm.trans ?_
    rw [h, Set.Icc.coe_one]

end inclToBot

/-- The inclusion (y₀, y₁, …, yₙ₋₁) ↦ (y₀, y₁, …, yₙ₋₁, 0) to the bottom face of `⊔I^(n+1)` -/
def inclToBoundaryJarBot {n : ℕ} : C(I^ Fin n, ⊔I^(n+1)) where
  toFun y := ⟨ inclToBot y, inclToBot.mem_boundaryJar y ⟩
  continuous_toFun := Continuous.subtype_mk inclToBot.continuous _

-- /-- The inclusion `(y, t) ↦ (y₀, y₁, …, yₙ₋₁, t)` to
-- the sides of `⊔I^(n+1)`, i.e.,
-- the closure of the complement of the top and bottom faces of `∂I^(n+1)`. -/
-- def inclToBoundaryJarSides {n : ℕ} : C((∂I^n) × I, ⊔I^(n+1)) where
--   toFun := fun ⟨⟨y, hy⟩, t⟩ ↦
--     ⟨ fun ⟨i, hi⟩ ↦
--         ⟨ if _ : i < n then y ⟨i, ‹_›⟩ else t,
--           by split_ifs; repeat {simp only [Subtype.coe_prop]} ⟩,
--       by
--         obtain ⟨⟨i, hi⟩, hyi⟩ := hy
--         constructor
--         · use ⟨i, hi.trans (by omega : n < n + 1)⟩; simp [hi, hyi]
--         · intro _
--           use ⟨i, hi.trans (by omega : n < n + 1)⟩; simpa [hi, hyi] ⟩
--   continuous_toFun := by
--     refine Continuous.subtype_mk ?_ _
--     refine continuous_pi fun i ↦ ?_
--     refine Continuous.subtype_mk ?_ _
--     split_ifs
--     · apply Continuous.subtype_val
--       exact continuous_apply (⟨i.val, ‹_›⟩ : Fin n) |>.comp <|
--         Continuous.subtype_val continuous_fst
--     · exact Continuous.subtype_val continuous_snd

/-- The inclusion `(y, t) ↦ (y₀, y₁, …, yₙ₋₁, t)` to
the sides of `⊔I^(n+1)`, i.e.,
the closure of the complement of the top and bottom faces of `∂I^(n+1)`. -/
def inclToBoundaryJarSides {n : ℕ} : C((∂I^n) × I, ⊔I^(n+1)) where
  toFun := fun yt ↦
    ⟨ (toContinuousMap splitAtLastComm.symm |>.comp <|
        ContinuousMap.prodMap (boundaryIncl n) (ContinuousMap.id _)) yt,
    by
      obtain ⟨⟨y, ⟨i, hyi⟩⟩, t⟩ := yt
      constructor
      · use i.castSucc
        simp [splitAtLastComm, splitAtLast, homeoNeqLast, boundaryIncl]
        simpa [Fin.castSucc_ne_last]
      · intro _; use i.castSucc
        simp [splitAtLastComm, splitAtLast, homeoNeqLast, boundaryIncl]
        simpa [Fin.castSucc_ne_last, Fin.castSucc_lt_last]  ⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [ContinuousMap.coe_comp, ContinuousMap.coe_coe, Homeomorph.comp_continuous_iff]
    apply ContinuousMapClass.map_continuous

/-- The inclusion `(y, t) ↦ (y₀, y₁, …, yₙ₋₁, t)` to the sides of
the $(n+1)$-dimensional cube. -/
def inclToSides {n : ℕ} : C((∂I^n) × I, I^ Fin (n + 1)) where
  toFun := Subtype.val ∘ inclToBoundaryJarSides
  continuous_toFun := Continuous.subtype_val inclToBoundaryJarSides.continuous

end Cube


namespace TopCat

/-- `cube` -/
def cube (n : ℕ) : TopCat.{u} := TopCat.of <| ULift <| I^ Fin n

/-- `cubeBoundary` -/
def cubeBoundary (n : ℕ) : TopCat.{u} := TopCat.of <| ULift <| Cube.boundary (Fin n)

/-- `cubeBoundaryJar` -/
def cubeBoundaryJar (n : ℕ) : TopCat.{u} := TopCat.of <| ULift <| Cube.boundaryJar n

/-- `𝕀 n` denotes the `n`-cube (as an object in `TopCat`). -/
scoped prefix:arg "𝕀 " => cube

/-- `∂𝕀 n` denotes the boundary of the `n`-cube (as an object in `TopCat`). -/
scoped prefix:arg "∂𝕀 " => cubeBoundary

/-- `⊔𝕀 n` denotes the "boundary jar" ($⊔Iⁿ⁺¹ = ∂Iⁿ × I ∪ Iⁿ × {0} ⊆ Iⁿ⁺¹$)
of the `n`-cube (as an object in `TopCat`). -/
scoped prefix:arg "⊔𝕀 " => cubeBoundaryJar

/-- The inclusion `∂𝕀 n ⟶ 𝕀 n` of the boundary of the `n`-cube. -/
def cubeBoundaryIncl (n : ℕ) : cubeBoundary.{u} n ⟶ cube.{u} n :=
  ofHom
    { toFun := fun ⟨⟨p, _⟩⟩ ↦ ⟨p⟩
      continuous_toFun :=
        continuous_uliftUp.comp <| continuous_subtype_val.comp continuous_induced_dom }

/-- `cubeBoundaryJarInclToBoundary` -/
def cubeBoundaryJarInclToBoundary (n : ℕ) : cubeBoundaryJar.{u} n ⟶ cubeBoundary.{u} n :=
  ofHom
    { toFun := fun ⟨p⟩ ↦ ⟨Cube.boundaryJarInclToBoundary n p⟩
      continuous_toFun := by fun_prop }

@[simp↓]
lemma cubeBoundaryIncl_apply_down_eq {n : ℕ} (y : I^Fin n) (hy : y ∈ ∂I^n) :
    (cubeBoundaryIncl n ⟨⟨y, hy⟩⟩).down = y := rfl

/-- `cubeSplitAtLast` -/
def cubeSplitAtLast {n : ℕ} : 𝕀 (n + 1) ≅ TopCat.of (I × 𝕀 n) where
  hom := ofHom ⟨fun ⟨y⟩ ↦ ⟨(Cube.splitAtLast y).fst, ⟨(Cube.splitAtLast y).snd⟩⟩, by fun_prop⟩
  inv := ofHom ⟨fun ⟨t, ⟨y⟩⟩ ↦ ⟨Cube.splitAtLast.symm ⟨t, y⟩⟩, by fun_prop⟩
  hom_inv_id := by
    ext ⟨y⟩
    simp only [hom_comp, ContinuousMap.comp_apply, hom_id,
      ContinuousMap.id_apply]
    change ULift.up _ = _
    simp only [Prod.mk.eta, Homeomorph.symm_apply_apply]
  inv_hom_id := by
    ext ⟨t, ⟨y⟩⟩
    all_goals simp only [hom_comp, ContinuousMap.comp_apply,
        hom_id, ContinuousMap.id_apply]
    · congr 1
      change (Cube.splitAtLast (Cube.splitAtLast.symm _)).fst = _
      simp only [Homeomorph.apply_symm_apply]
    · change ({ down := (Cube.splitAtLast (Cube.splitAtLast.symm (t, y))).2 } : ULift _) = _
      simp only [Homeomorph.apply_symm_apply]

/-- This lemma should be applied before expanding the `match` expression. -/
@[simp↓]
lemma cubeSplitAtLast_inv_down_eq {n : ℕ} (t : I) (y : 𝕀 n) :
    (cubeSplitAtLast.inv ⟨t, y⟩).down = Cube.splitAtLast.symm ⟨t, y.down⟩ := rfl

lemma cubeSplitAtLast_inv_mem_boundary_of_mem_boundary {n : ℕ} (t : I) (y : ∂𝕀 n) :
    (cubeSplitAtLast.inv ⟨t, cubeBoundaryIncl n y⟩).down ∈ ∂I^ (n + 1) := by
  simp only [↓cubeSplitAtLast_inv_down_eq]
  apply Cube.splitAtLast_symm_mem_boundary_of_mem_boundary t y.down.property


namespace cubeBoundary

/-- The inclusion from the n-dimensional cube to the top or bottom face
of the boundary of the (n+1)-dimensional cube,
mapping (y₀, y₁, …, yₙ₋₁) to (y₀, y₁, …, yₙ₋₁, t). -/
def cubeInclToBotOrTop {n : ℕ} (t : unitInterval.zeroOne) : 𝕀 n ⟶ ∂𝕀 (n + 1) :=
  ofHom
    { toFun := fun ⟨y⟩ ↦ ⟨Cube.splitAtLast.symm ⟨unitInterval.zeroOneIncl t, y⟩, by
        use Fin.last _
        simp only [Cube.splitAtLast, ne_eq, ContinuousMap.coe_mk,
          Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm, Homeomorph.refl_symm,
          Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply,
          id_eq, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]
        obtain ht | ht := unitInterval.zeroOne.val_eq_zero_or_val_eq_one t
        · left; simp_all only [Set.Icc.mk_zero]
        · right; simp_all only [Set.Icc.mk_one] ⟩
      continuous_toFun := by fun_prop }

/-- `botOrTop` -/
abbrev botOrTop (n : ℕ) (t : unitInterval.zeroOne) : Set (∂𝕀 (n + 1)) :=
  {⟨⟨y, _⟩⟩ | y (Fin.last _) = unitInterval.zeroOneIncl t}

/-- `sides` -/
abbrev sides (n : ℕ) : Set (∂𝕀 (n + 1)) :=
  {⟨⟨y, _⟩⟩ | ∃ i < Fin.last _, y i = 0 ∨ y i = 1}

lemma cubeInclToBotOrTop_mem_botOrTop
    {n : ℕ} (t : unitInterval.zeroOne) (y : 𝕀 n) :
    cubeInclToBotOrTop t y ∈ botOrTop n t := by
  simp only [cubeInclToBotOrTop, Cube.splitAtLast, ne_eq, ContinuousMap.coe_mk,
    Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm, Homeomorph.refl_symm,
    Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq,
    Set.mem_setOf_eq, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]

/-- Given a point on the boundary of the `n`-dimensional cube,
cast it as a point on the boundary of the `(n + 1)`-dimensional cube
by specifying the height `t : I`. -/
def castSucc {n : ℕ} (t : I) (y : ∂𝕀 n) : ∂𝕀 (n + 1) :=
  ⟨cubeSplitAtLast.inv ⟨t, cubeBoundaryIncl n y⟩ |>.down,
    cubeSplitAtLast_inv_mem_boundary_of_mem_boundary t y⟩

lemma castSucc_mem_sides {n : ℕ} (t : I) (y : ∂𝕀 n) :
    castSucc t y ∈ sides n := by
  obtain ⟨⟨y, ⟨i, hi⟩⟩⟩ := y
  use i.castSucc
  constructor
  · exact Fin.castSucc_lt_last i
  · simp only [↓cubeSplitAtLast_inv_down_eq, ↓cubeBoundaryIncl_apply_down_eq]
    -- change Cube.splitAtLast.symm _ _ = 0 ∨ Cube.splitAtLast.symm _ _ = 1
    rw [Cube.splitAtLast_symm_apply_eq_of_neq_last t y i.castSucc (Fin.castSucc_ne_last i)]
    exact hi

end cubeBoundary

end TopCat
