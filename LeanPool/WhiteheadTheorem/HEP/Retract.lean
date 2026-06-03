/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.HEP.Cube
import LeanPool.WhiteheadTheorem.Shapes.Cube
import LeanPool.WhiteheadTheorem.Shapes.UnitInterval
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Homotopy.Contractible

/-!
# LeanPool.WhiteheadTheorem.HEP.Retract

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.HEP.Retract`.
-/


open TopCat
open scoped Topology unitInterval
open scoped Topology.Homotopy


/-- A strong deformation retraction from `X` to its subset `A` -/
structure StrongDeformRetr (X : Type*) [TopologicalSpace X] (A : Set X) where
  /-- The retraction map -/
  r : C(X, X)
  -- /-- `r` is a retraction, i.e., the restriction of `r` to `A` is the identity map.
  -- (This can be inferred from the relative homotopy `H`.) -/
  -- r_restrict : ∀ a ∈ A, r a = a
  /-- `r` sends all of `X` into `A` -/
  r_range : Set.range r ⊆ A
  /-- A homotopy `H` rel `A`, where `H₀` is the identity map on `X`, and `H₁ = r`. -/
  H : (ContinuousMap.id X).HomotopyRel r A


namespace Cube

lemma splitAtLastComm_inclToBot_eq {n : ℕ} :   -- (I^ Fin n) ↦ (I^ Fin n) × I
    splitAtLastComm ∘ inclToBot = fun x : (I^ Fin n) ↦ (x, 0) := by
  ext x i
  repeat {simp [splitAtLastComm, splitAtLast, inclToBot]}

lemma inclToBot_discardLast_mem_boundary {n : ℕ} (y : I^Fin (n + 1)) :
    inclToBot (discardLast y) ∈ ∂I^(n+1) := by
  use Fin.last n; left; simp [inclToBot]

/-- `(y₀, y₁, …, yₙ₋₁, yₙ) ↦ (y₀, y₁, …, yₙ₋₁) ↦ (y₀, y₁, …, yₙ₋₁, 0)` does nothing if `yₙ = 0`. -/
lemma inclToBot_discardLast_eq_of {n : ℕ} (y : I^Fin (n + 1))
    (hz : y (Fin.last n) = 0) : inclToBot (discardLast y) = y := by
  ext i
  simp only [discardLast, inclToBot, ContinuousMap.coe_mk, Homeomorph.funSplitAt_symm_apply]
  split_ifs with hi
  · rw [hi, hz]
  · rfl

lemma inclToBoundaryJarBot_discardLast_eq_of {n : ℕ} (y : I^Fin (n + 1))
    (hz : y (Fin.last n) = 0) : inclToBoundaryJarBot (discardLast y) = y := by
  ext i
  simp only [discardLast, inclToBoundaryJarBot, inclToBot, ContinuousMap.coe_mk,
    Homeomorph.funSplitAt_symm_apply]
  split_ifs with hi
  · rw [hi, hz]
  · rfl

------------------

lemma splitAtLastComm_inclToSides_eq {n : ℕ} :   -- (∂I^n) × I ↦ (I^ Fin n) × I
    splitAtLastComm ∘ inclToSides = Prod.map (boundaryIncl n) id := by
  ext ⟨y, t⟩ i
  repeat { simp [splitAtLastComm, splitAtLast, boundaryIncl,
    inclToSides, inclToBoundaryJarSides] }

/-- Project the $(n+1)$-dimensional cube to its boundary `∂I^(n+1)`.
This fixes every point on the boundary, and maps other points to the default value `0`.
This (non-continuous) function is convenient for diagram-chasing when applying
the homotopy extension property in `retrToBoundaryJar`.
This function is `noncomputable` due to `Real.decidableEq`. -/
noncomputable def projToBoundary {n : ℕ} : (I^ Fin (n + 1)) → ∂I^(n+1) := fun y ↦
  let _ : Decidable (y ∈ ∂I^(n+1)) := by
    simp only [Cube.boundary, Set.mem_setOf_eq]
    infer_instance
  if _ : y ∈ ∂I^(n+1)
    then ⟨y, ‹_›⟩
    else ⟨0, ⟨0, by simp only [Pi.zero_apply, zero_ne_one, or_false]⟩⟩

/-- `projToBoundary y` does nothing if `y` is already in the boundary. -/
lemma projToBoundary_eq_of_mem_boundary {n : ℕ} (y : I^Fin (n + 1))
    (hy : y ∈ ∂I^(n + 1)) : projToBoundary y = y := by
  simp only [projToBoundary, hy, ↓reduceDIte]

/-- Project the $(n+2)$-dimensional cube to its sides `(∂I^(n+1)) × I`
(the closure of the complement of the top and bottom faces of the boundary).
Since `∂I^0 = ∅`, the cube shoule be at least 2-dimensional. -/
noncomputable def projToSides {n : ℕ} : (I^ Fin (n + 1 + 1)) → (∂I^(n+1)) × I :=
  (Prod.map projToBoundary id) ∘ splitAtLastComm

lemma inclToSides_projToSides_eq_of {n : ℕ} (y : I^Fin (n + 1 + 1))
    (hs : (splitAtLast y).snd ∈ ∂I^(n + 1)) :
    inclToSides (projToSides y) = y := by
  change inclToSides (projToBoundary (splitAtLastComm y).1, (splitAtLastComm y).2) = y
  rw [splitAtLast_snd_eq] at hs
  have h_pj : projToBoundary (splitAtLastComm y).1 = ⟨(splitAtLastComm y).1, ‹_›⟩ :=
    Subtype.ext_iff.mpr (projToBoundary_eq_of_mem_boundary _ hs)
  rw [h_pj]
  ext i
  simp only [inclToSides, inclToBoundaryJarSides, splitAtLastComm, splitAtLast, boundaryIncl,
    ContinuousMap.coe_mk, ContinuousMap.comp_apply, ContinuousMap.coe_coe,
    ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
    Function.comp_apply,
    Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm, Homeomorph.refl_symm,
    Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply,
    Homeomorph.funSplitAt_symm_apply]
  split_ifs with hi
  · rw [hi]; rfl
  · rfl

lemma inclToBoundaryJarSides_projToSides_eq_of {n : ℕ} (y : I^Fin (n + 1 + 1))
    (hs : (splitAtLast y).snd ∈ ∂I^(n + 1)) :
    inclToBoundaryJarSides (projToSides y) = y := by
  change inclToBoundaryJarSides (projToBoundary (splitAtLastComm y).1, (splitAtLastComm y).2) = y
  rw [splitAtLast_snd_eq] at hs
  have h_pj : projToBoundary (splitAtLastComm y).1 = ⟨(splitAtLastComm y).1, ‹_›⟩ :=
    Subtype.ext_iff.mpr (projToBoundary_eq_of_mem_boundary _ hs)
  rw [h_pj]
  ext i
  -- Reduce inclToBoundaryJarSides to its underlying ContinuousMap component
  simp only [inclToBoundaryJarSides, splitAtLastComm, splitAtLast, boundaryIncl,
    ContinuousMap.coe_mk, ContinuousMap.comp_apply, ContinuousMap.coe_coe,
    ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
    Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.refl_symm, Homeomorph.symm_symm,
    Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Homeomorph.funSplitAt_symm_apply]
  split_ifs with hi
  · rw [hi]; rfl
  · rfl



/-- A  retraction from `I^n` to `⊔I^n`, for `n ≥ 1`. -/
noncomputable def retrToBoundaryJar (n : ℕ) :
    { r' : C(Fin (n + 1) → I, ⊔I^n + 1) // ∀ y ∈ ⊔I^(n+1), r' y = y } := by
  let f : C(I^ Fin n, ⊔I^(n + 1)) := inclToBoundaryJarBot
  let h : C((∂I^n) × I, ⊔I^(n + 1)) := inclToBoundaryJarSides
  have : f ∘ (boundaryIncl n) = h ∘ fun x ↦ (x, 0) := by
    ext x i
    simp [boundaryIncl, f, h, inclToBoundaryJarBot, inclToBoundaryJarSides, inclToBot,
          splitAtLastComm, splitAtLast]
  have hep := Cube.boundaryIncl_hasHEP n (⊔I^(n + 1)) f h this
  let H := Classical.choose hep
  have spec : (f = H ∘ fun x ↦ (x, 0)) ∧ h = H ∘ Prod.map (boundaryIncl n) id :=
    Classical.choose_spec hep
  let r' : C(I^ Fin (n + 1), ⊔I^(n+1)) := H.comp (toContinuousMap splitAtLastComm)
  exact ⟨r', fun y hy ↦ by
    by_cases hbot : y (Fin.last n) = 0
    · nth_rw 1 [← inclToBot_discardLast_eq_of y hbot]
      change (H ∘ splitAtLastComm ∘ inclToBot) _ = y
      rw [splitAtLastComm_inclToBot_eq]
      rw [← spec.left, inclToBoundaryJarBot_discardLast_eq_of y hbot]
    · induction n with
      | zero =>
          have : (H ∘ splitAtLastComm) y = ⟨y, hy⟩ := by
            rw [uniqueBoundaryJarOne.uniq ⟨y, hy⟩]
            rw [uniqueBoundaryJarOne.uniq ((H ∘ splitAtLastComm) y)]
          apply_fun Subtype.val at this
          exact this
      | succ n =>
          obtain hy' | hy' := mem_boundaryJar_iff_splitAtLast.mp hy
          · exfalso; rw [splitAtLast_fst_eq] at hy'; exact hbot hy'
          nth_rw 1 [← inclToSides_projToSides_eq_of y hy']
          change (H ∘ splitAtLastComm ∘ inclToSides) _ = y
          rw [splitAtLastComm_inclToSides_eq]
          rw [← spec.right]
          apply inclToBoundaryJarSides_projToSides_eq_of y
          exact hy' ⟩

/-- A strong deformation retraction from `I^n` to `⊔I^n`, for `n ≥ 1`.
I'm writing down the formula for each coordinate because:
  - `failed to synthesize ContinuousSMul (↑I) (Fin (n + 1) → ↑I)`
  - Using `Convex` requires going to a subset of ℝ^(n+1) and back
    (although `Convex ℝ I` is very helpful) -/
noncomputable def strongDeformRetrToBoundaryJar (n : ℕ) :
    StrongDeformRetr (I^ Fin (n + 1)) (⊔I^ (n + 1)) :=
  let ⟨r', r'_restrict⟩ := retrToBoundaryJar n
  { r := (boundaryJarIncl (n + 1)).comp r'
    r_range := fun y hy ↦ by
      simp only [boundaryJarIncl, ContinuousMap.coe_comp, ContinuousMap.coe_mk, Set.mem_range,
        Function.comp_apply] at hy
      obtain ⟨z, hz⟩ := hy; rw [← hz]; simp only [Subtype.coe_prop]
    H :=
      { toFun := fun ⟨t, y⟩ ↦ fun i ↦
          ⟨ (σ t).val • (y i).val + t.val • ((r' y).val i).val,  -- σ t = 1 - t
            (convex_Icc _ _ : Convex ℝ I).starConvex (y i).property ((r' y).val i).property
              (unitInterval.nonneg (σ t)) (unitInterval.nonneg t)
              (by simp only [unitInterval.coe_symm_eq, sub_add_cancel]) ⟩
        continuous_toFun := by
          refine continuous_pi fun i ↦ Continuous.subtype_mk (Continuous.add ?_ ?_) _
          · apply Continuous.smul
            · exact Continuous.subtype_val <| unitInterval.continuous_symm.comp continuous_fst
            · exact Continuous.subtype_val <| (continuous_apply i).comp continuous_snd
          · apply Continuous.smul
            · exact Continuous.subtype_val continuous_fst
            · refine Continuous.subtype_val <| (continuous_apply i).comp ?_
              exact Continuous.subtype_val <| r'.continuous.comp continuous_snd
        map_zero_left y := by simp only [unitInterval.symm_zero, Set.Icc.coe_one, smul_eq_mul,
          one_mul, Set.Icc.coe_zero, zero_mul, add_zero, Subtype.coe_eta, ContinuousMap.id_apply]
        map_one_left y := by
          simp only [unitInterval.symm_one, Set.Icc.coe_zero, smul_eq_mul, zero_mul,
            Set.Icc.coe_one, one_mul, zero_add, Subtype.coe_eta, ContinuousMap.comp_apply]
          simp only [boundaryJarIncl, ContinuousMap.coe_mk]
        prop' t y hy := by
          ext i
          simp only [unitInterval.coe_symm_eq, smul_eq_mul, ContinuousMap.coe_mk,
            ContinuousMap.id_apply]
          rw [r'_restrict y hy, sub_mul, sub_add_cancel, one_mul] }}




open scoped ContinuousMap

example (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] (f g : C(X, Y)) (hfg : f = g) :
    f.Homotopic g :=
  hfg ▸ ContinuousMap.Homotopic.refl f

/-- Deformation retraction from the cube to its bottom face -/
def deformRetrToBot {n : ℕ} : C(I × I^ Fin (n + 1), I^ Fin (n + 1)) :=
  let f₁ : C(I × I^ Fin (n + 1), I × I × I^ Fin n) :=
    (ContinuousMap.id _).prodMap (toContinuousMap splitAtLast)
  let f₂ : C(I × I × I^ Fin n, I × I^ Fin n) :=
    { toFun := fun ⟨t, ⟨s, y⟩⟩ ↦ ⟨s * t, y⟩
      continuous_toFun := by fun_prop }  -- uses `unitInterval.continuousMul` in `Shapes/Maps.lean`
  let f₃ : C(I × I^ Fin n, I^ Fin (n + 1)) :=
    toContinuousMap splitAtLast.symm
  f₃.comp <| f₂.comp f₁

/-- If `y` is in the bottom face of the cube,
then `deformRetrToBot ⟨t, y⟩` is in the bottom face for all `t`. -/
lemma deformRetrToBot_apply_bot {n : ℕ}
    (t : I) {y : I^Fin (n + 1)} (hy : y (Fin.last n) = 0) :
    deformRetrToBot ⟨t, y⟩ (Fin.last n) = 0 := by
  unfold deformRetrToBot
  simp only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply, ContinuousMap.coe_id,
    ContinuousMap.coe_coe, Prod.map_apply, id_eq, ContinuousMap.coe_mk]
  unfold splitAtLast
  simp only [ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
    Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq,
    Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm, Homeomorph.refl_symm,
    Homeomorph.symm_symm, Homeomorph.apply_symm_apply, Homeomorph.funSplitAt_symm_apply,
    ↓reduceDIte, mul_eq_zero]
  exact Or.inl hy

/-- If `y` is in the sides
(the closure of the complement of the top and bottom faces of the boundary) of the cube,
then `deformRetrToBot ⟨t, y⟩` is in the sides for all `t`. -/
lemma deformRetrToBot_apply_sides {n : ℕ}
    (t : I) {y : I^Fin (n + 1)} (hy : (splitAtLast y).snd ∈ ∂I^n) :
    (splitAtLast (deformRetrToBot ⟨t, y⟩)).snd ∈ ∂I^n := by
  unfold deformRetrToBot
  simpa only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply, ContinuousMap.coe_id,
    ContinuousMap.coe_coe, Prod.map_apply, id_eq, ContinuousMap.coe_mk, Homeomorph.apply_symm_apply]

/-- Deformation retraction from `⊔I^(n + 1)` to its bottom face -/
def boundaryJarDeformRetrToBot {n : ℕ} : C(I × ⊔I^(n + 1), ⊔I^(n + 1)) :=
  let f₀ : C(I × ⊔I^(n + 1), I × I^ Fin (n + 1)) :=
    (ContinuousMap.id _).prodMap <| boundaryJarIncl (n + 1)
  { toFun ty := ⟨deformRetrToBot (f₀ ty), by
      obtain ⟨t, ⟨y, hy⟩⟩ := ty
      -- simp? [f₀, deformRetrToBot]
      obtain hbot | hsides := mem_boundaryJar_iff_splitAtLast.mp hy
      · simp only [boundaryJarIncl, ContinuousMap.prodMap_apply, ContinuousMap.coe_id,
          ContinuousMap.coe_mk, Prod.map_apply, id_eq, f₀]
        rw [splitAtLast_fst_eq] at hbot
        have := deformRetrToBot_apply_bot t hbot
        apply mem_boundaryJar_of_exists_eq_zero
        use Fin.last n
      · simp only [boundaryJarIncl, ContinuousMap.prodMap_apply, ContinuousMap.coe_id,
          ContinuousMap.coe_mk, Prod.map_apply, id_eq, f₀]
        have := deformRetrToBot_apply_sides t hsides
        exact mem_boundaryJar_iff_splitAtLast.mpr <| Or.inr this ⟩
    continuous_toFun := by fun_prop }

/-- `hequivBoundaryJar` -/
def hequivBoundaryJar {n : ℕ} : (I^ Fin n) ≃ₕ ⊔I^(n + 1) where
  toFun := inclToBoundaryJarBot
  invFun := discardLast.comp (boundaryJarIncl (n + 1))
  left_inv := by
    apply ContinuousMap.Homotopic.of_eq
    ext y i
    simp only [discardLast, boundaryJarIncl, inclToBoundaryJarBot, inclToBot, ne_eq,
      ContinuousMap.coe_mk, ContinuousMap.comp_assoc, ContinuousMap.comp_apply,
      Homeomorph.funSplitAt_symm_apply, ContinuousMap.id_apply]
    split
    · rename_i hi
      change i.castSucc = _ at hi
      exfalso
      exact (Fin.castSucc_ne_last i) hi
    · simp only [homeoNeqLast, ne_eq, Homeomorph.piCongr_apply]
      rfl
  right_inv := Nonempty.intro <|
    { toContinuousMap := boundaryJarDeformRetrToBot
      map_zero_left y := by
        unfold boundaryJarDeformRetrToBot inclToBoundaryJarBot discardLast boundaryJarIncl
        simp only [ContinuousMap.prodMap_apply, ContinuousMap.coe_id, ContinuousMap.coe_mk,
          Prod.map_apply, id_eq, ContinuousMap.comp_apply, Subtype.mk.injEq]
        unfold deformRetrToBot inclToBot
        simp only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply, ContinuousMap.coe_id,
          ContinuousMap.coe_coe, Prod.map_apply, id_eq, ContinuousMap.coe_mk, mul_zero, ne_eq]
        unfold splitAtLast homeoNeqLast
        simp only [ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
          Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply,
          id_eq, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm, Homeomorph.refl_symm,
          Homeomorph.symm_symm, Homeomorph.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq,
          Prod.mk.injEq, true_and]
        ext i
        simp only [Homeomorph.piCongr_apply,
          ]
        rfl
      map_one_left y := by
        unfold boundaryJarDeformRetrToBot boundaryJarIncl deformRetrToBot
        simp only [ContinuousMap.prodMap_apply, ContinuousMap.coe_id, ContinuousMap.coe_mk,
          Prod.map_apply, id_eq, ContinuousMap.comp_apply, ContinuousMap.coe_coe, mul_one,
          Prod.mk.eta, Homeomorph.symm_apply_apply, Subtype.coe_eta, ContinuousMap.id_apply] }

/-- Deformation retraction from the cube to the point `0`. -/
def deformRetrToZero {n : ℕ} : C(I × I^ Fin n, I^ Fin n) where
  toFun := fun ⟨t, y⟩ ↦ fun i ↦ y i * σ t
  continuous_toFun := by fun_prop

instance instContractibleSpace {n : ℕ} : ContractibleSpace (I^ Fin n) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  use 0
  exact Nonempty.intro <|
    { toContinuousMap := deformRetrToZero
      map_zero_left y := by
        simp only [deformRetrToZero, ContinuousMap.toFun_eq_coe, ContinuousMap.coe_mk,
          unitInterval.symm_zero, mul_one, ContinuousMap.id_apply]
      map_one_left y := by
        simp only [deformRetrToZero, ContinuousMap.toFun_eq_coe, ContinuousMap.coe_mk,
          unitInterval.symm_one, mul_zero, ContinuousMap.const_apply]
        rfl }

instance instContractibleSpaceBoundaryJar {n : ℕ} : ContractibleSpace (boundaryJar (n + 1)) :=
  ContinuousMap.HomotopyEquiv.contractibleSpace hequivBoundaryJar.symm



end Cube
