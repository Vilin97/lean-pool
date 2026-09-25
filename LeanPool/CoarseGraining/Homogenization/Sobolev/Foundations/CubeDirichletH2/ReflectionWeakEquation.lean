/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionL2
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentTestFold

/-! # Reflection Weak Equation -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-!
# Folded tests for the Dirichlet odd-reflection weak equation

The full reflected weak equation is reduced to the original Dirichlet weak
problem by folding a parent test back to the original cube with the product
odd-reflection sign.  This file packages the folded test as an `H¹₀` test on
origin cubes.
-/

/-- Fold a parent scalar test back to the original cube using the product
Dirichlet odd-reflection sign. -/
def cubeDirichletOddReflectionFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) (φ : Vec d → ℝ) : Vec d → ℝ :=
  fun y =>
    ∑ choice : Fin d → Fin 3,
      cubeDirichletOddReflectionCellSign choice *
        φ (cubeFaceReflectionCellFoldMap Q choice y)

private theorem eq_zero_of_tsupport_subset_of_notMem
    {d : ℕ} {U : Set (Vec d)} {φ : Vec d → ℝ} {x : Vec d}
    (hφ_sub : tsupport φ ⊆ U) (hx : x ∉ U) :
    φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hxt => hx (hφ_sub hxt)

private theorem hasCompactSupport_finset_sum
    {α β ι : Type*} [TopologicalSpace α] [AddCommMonoid β] [DecidableEq ι]
    (s : Finset ι) (f : ι → α → β)
    (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  revert hf
  refine Finset.induction_on s ?zero ?insert
  · intro _hf
    simpa using! (HasCompactSupport.zero : HasCompactSupport (fun _ : α => (0 : β)))
  · intro a s has hs hf
    have ha : HasCompactSupport (f a) := hf a (by simp [has])
    have hs' : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
      exact hs (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert has] using! ha.add hs'

private theorem cubeDirichletOddReflectionCellSign_lowerChoiceSwap_of_choice_eq_zero
    {d : ℕ} (i : Fin d) (choice : Fin d → Fin 3)
    (h0 : choice i = 0) :
    cubeDirichletOddReflectionCellSign
        (cubeFaceReflectionLowerChoiceSwap i choice) =
      -cubeDirichletOddReflectionCellSign choice := by
  classical
  unfold cubeDirichletOddReflectionCellSign
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i]
  have hrest :
      (∏ x ∈ {i}ᶜ,
          (if cubeFaceReflectionLowerChoiceSwap i choice x = 1 then (1 : ℝ) else -1)) =
        ∏ x ∈ {i}ᶜ, (if choice x = 1 then (1 : ℝ) else -1) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [cubeFaceReflectionLowerChoiceSwap, Function.update_of_ne hji]
  rw [hrest]
  simp [cubeFaceReflectionLowerChoiceSwap, h0]

private theorem cubeDirichletOddReflectionCellSign_lowerChoiceSwap_of_choice_eq_one
    {d : ℕ} (i : Fin d) (choice : Fin d → Fin 3)
    (h1 : choice i = 1) :
    cubeDirichletOddReflectionCellSign
        (cubeFaceReflectionLowerChoiceSwap i choice) =
      -cubeDirichletOddReflectionCellSign choice := by
  classical
  unfold cubeDirichletOddReflectionCellSign
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i]
  have hrest :
      (∏ x ∈ {i}ᶜ,
          (if cubeFaceReflectionLowerChoiceSwap i choice x = 1 then (1 : ℝ) else -1)) =
        ∏ x ∈ {i}ᶜ, (if choice x = 1 then (1 : ℝ) else -1) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [cubeFaceReflectionLowerChoiceSwap, Function.update_of_ne hji]
  rw [hrest]
  simp [cubeFaceReflectionLowerChoiceSwap, h1]

private theorem cubeDirichletOddReflectionCellSign_upperChoiceSwap_of_choice_eq_one
    {d : ℕ} (i : Fin d) (choice : Fin d → Fin 3)
    (h1 : choice i = 1) :
    cubeDirichletOddReflectionCellSign
        (cubeFaceReflectionUpperChoiceSwap i choice) =
      -cubeDirichletOddReflectionCellSign choice := by
  classical
  unfold cubeDirichletOddReflectionCellSign
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i]
  have hrest :
      (∏ x ∈ {i}ᶜ,
          (if cubeFaceReflectionUpperChoiceSwap i choice x = 1 then (1 : ℝ) else -1)) =
        ∏ x ∈ {i}ᶜ, (if choice x = 1 then (1 : ℝ) else -1) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [cubeFaceReflectionUpperChoiceSwap, Function.update_of_ne hji]
  rw [hrest]
  simp [cubeFaceReflectionUpperChoiceSwap, h1]

private theorem cubeDirichletOddReflectionCellSign_upperChoiceSwap_of_choice_eq_two
    {d : ℕ} (i : Fin d) (choice : Fin d → Fin 3)
    (h2 : choice i = 2) :
    cubeDirichletOddReflectionCellSign
        (cubeFaceReflectionUpperChoiceSwap i choice) =
      -cubeDirichletOddReflectionCellSign choice := by
  classical
  unfold cubeDirichletOddReflectionCellSign
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i]
  have hrest :
      (∏ x ∈ {i}ᶜ,
          (if cubeFaceReflectionUpperChoiceSwap i choice x = 1 then (1 : ℝ) else -1)) =
        ∏ x ∈ {i}ᶜ, (if choice x = 1 then (1 : ℝ) else -1) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [cubeFaceReflectionUpperChoiceSwap, Function.update_of_ne hji]
  rw [hrest]
  simp [cubeFaceReflectionUpperChoiceSwap, h2]

/-- Lower-face cancellation for the product-sign folded parent test, assuming
the unpaired upper-strip outer cell evaluates to zero. -/
theorem cubeDirichletOddReflectionFoldedParentScalarTest_lowerFaceProjection_eq_zero_of_outer
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (houter : ∀ choice : Fin d → Fin 3, ∀ x : Vec d,
      choice i ≠ 0 → choice i ≠ 1 →
        φ (cubeFaceReflectionCellFoldMap Q choice
          (cubeLowerFaceProjection Q i x)) = 0) :
    ∀ x : Vec d,
      cubeDirichletOddReflectionFoldedParentScalarTest Q φ
        (cubeLowerFaceProjection Q i x) = 0 := by
  classical
  intro x
  unfold cubeDirichletOddReflectionFoldedParentScalarTest
  let f : (Fin d → Fin 3) → ℝ := fun choice =>
    cubeDirichletOddReflectionCellSign choice *
      φ (cubeFaceReflectionCellFoldMap Q choice
        (cubeLowerFaceProjection Q i x))
  simpa [f] using
    (Finset.sum_ninvolution (s := Finset.univ) (f := f)
      (cubeFaceReflectionLowerChoiceSwap i)
      (by
        intro choice
        by_cases h0 : choice i = 0
        · have hsign :=
            cubeDirichletOddReflectionCellSign_lowerChoiceSwap_of_choice_eq_zero
              i choice h0
          simp [f, hsign,
            cubeFaceReflectionCellFoldMap_lowerChoiceSwap_lowerFaceProjection
              Q i choice x]
        · by_cases h1 : choice i = 1
          · have hsign :=
              cubeDirichletOddReflectionCellSign_lowerChoiceSwap_of_choice_eq_one
                i choice h1
            simp [f, hsign,
              cubeFaceReflectionCellFoldMap_lowerChoiceSwap_lowerFaceProjection
                Q i choice x]
          · have hzero := houter choice x h0 h1
            simp [f, hzero,
              cubeFaceReflectionCellFoldMap_lowerChoiceSwap_lowerFaceProjection
                Q i choice x])
      (by
        intro choice hf hfix
        by_cases h0 : choice i = 0
        · have hi := congrFun hfix i
          simp [cubeFaceReflectionLowerChoiceSwap, h0] at hi
        · by_cases h1 : choice i = 1
          · have hi := congrFun hfix i
            simp [cubeFaceReflectionLowerChoiceSwap, h1] at hi
          · have hzero := houter choice x h0 h1
            simp [f, hzero] at hf)
      (by intro choice; simp)
      (cubeFaceReflectionLowerChoiceSwap_involutive i))

/-- Upper-face cancellation for the product-sign folded parent test, assuming
the unpaired lower-strip outer cell evaluates to zero. -/
theorem cubeDirichletOddReflectionFoldedParentScalarTest_upperFaceProjection_eq_zero_of_outer
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (houter : ∀ choice : Fin d → Fin 3, ∀ x : Vec d,
      choice i ≠ 1 → choice i ≠ 2 →
        φ (cubeFaceReflectionCellFoldMap Q choice
          (cubeUpperFaceProjection Q i x)) = 0) :
    ∀ x : Vec d,
      cubeDirichletOddReflectionFoldedParentScalarTest Q φ
        (cubeUpperFaceProjection Q i x) = 0 := by
  classical
  intro x
  unfold cubeDirichletOddReflectionFoldedParentScalarTest
  let f : (Fin d → Fin 3) → ℝ := fun choice =>
    cubeDirichletOddReflectionCellSign choice *
      φ (cubeFaceReflectionCellFoldMap Q choice
        (cubeUpperFaceProjection Q i x))
  simpa [f] using
    (Finset.sum_ninvolution (s := Finset.univ) (f := f)
      (cubeFaceReflectionUpperChoiceSwap i)
      (by
        intro choice
        by_cases h1 : choice i = 1
        · have hsign :=
            cubeDirichletOddReflectionCellSign_upperChoiceSwap_of_choice_eq_one
              i choice h1
          simp [f, hsign,
            cubeFaceReflectionCellFoldMap_upperChoiceSwap_upperFaceProjection
              Q i choice x]
        · by_cases h2 : choice i = 2
          · have hsign :=
              cubeDirichletOddReflectionCellSign_upperChoiceSwap_of_choice_eq_two
                i choice h2
            simp [f, hsign,
              cubeFaceReflectionCellFoldMap_upperChoiceSwap_upperFaceProjection
                Q i choice x]
          · have hzero := houter choice x h1 h2
            simp [f, hzero,
              cubeFaceReflectionCellFoldMap_upperChoiceSwap_upperFaceProjection
                Q i choice x])
      (by
        intro choice hf hfix
        by_cases h1 : choice i = 1
        · have hi := congrFun hfix i
          simp [cubeFaceReflectionUpperChoiceSwap, h1] at hi
        · by_cases h2 : choice i = 2
          · have hi := congrFun hfix i
            simp [cubeFaceReflectionUpperChoiceSwap, h2] at hi
          · have hzero := houter choice x h1 h2
            simp [f, hzero] at hf)
      (by intro choice; simp)
      (cubeFaceReflectionUpperChoiceSwap_involutive i))

/-- Origin-cube lower-face cancellation for parent tests supported in the next
larger centered cube. -/
theorem cubeDirichletOddReflectionFoldedParentScalarTest_lowerFaceProjection_eq_zero_originCube
    {d : ℕ} (m : ℤ) (i : Fin d) {φ : Vec d → ℝ}
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∀ x : Vec d,
      cubeDirichletOddReflectionFoldedParentScalarTest (originCube d m) φ
        (cubeLowerFaceProjection (originCube d m) i x) = 0 := by
  refine
    cubeDirichletOddReflectionFoldedParentScalarTest_lowerFaceProjection_eq_zero_of_outer
      (originCube d m) i ?_
  intro choice x h0 h1
  exact eq_zero_of_tsupport_subset_of_notMem hφ_sub
    (cubeFaceReflectionCellFoldMap_lowerFaceProjection_notMem_openCubeSet_succ_originCube
      m i choice x h0 h1)

/-- Origin-cube upper-face cancellation for parent tests supported in the next
larger centered cube. -/
theorem cubeDirichletOddReflectionFoldedParentScalarTest_upperFaceProjection_eq_zero_originCube
    {d : ℕ} (m : ℤ) (i : Fin d) {φ : Vec d → ℝ}
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∀ x : Vec d,
      cubeDirichletOddReflectionFoldedParentScalarTest (originCube d m) φ
        (cubeUpperFaceProjection (originCube d m) i x) = 0 := by
  refine
    cubeDirichletOddReflectionFoldedParentScalarTest_upperFaceProjection_eq_zero_of_outer
      (originCube d m) i ?_
  intro choice x h1 h2
  exact eq_zero_of_tsupport_subset_of_notMem hφ_sub
    (cubeFaceReflectionCellFoldMap_upperFaceProjection_notMem_openCubeSet_succ_originCube
      m i choice x h1 h2)

/-- The product-sign folded parent test is smooth when the parent test is
smooth. -/
theorem contDiff_cubeDirichletOddReflectionFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (cubeDirichletOddReflectionFoldedParentScalarTest Q φ) := by
  classical
  unfold cubeDirichletOddReflectionFoldedParentScalarTest
  exact
    ContDiff.sum fun choice _ =>
      contDiff_const.mul
        (contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ)

/-- The product-sign folded parent test has compact support when the parent
test has compact support. -/
theorem hasCompactSupport_cubeDirichletOddReflectionFoldedParentScalarTest
    {d : ℕ} (Q : TriadicCube d) {φ : Vec d → ℝ}
    (hφ : HasCompactSupport φ) :
    HasCompactSupport (cubeDirichletOddReflectionFoldedParentScalarTest Q φ) := by
  classical
  unfold cubeDirichletOddReflectionFoldedParentScalarTest
  simpa using
    hasCompactSupport_finset_sum (Finset.univ : Finset (Fin d → Fin 3))
      (fun choice y =>
        cubeDirichletOddReflectionCellSign choice *
          φ (cubeFaceReflectionCellFoldMap Q choice y))
      (by
        intro choice _hchoice
        exact
          (hasCompactSupport_comp_cubeFaceReflectionCellFoldMap Q choice hφ).mul_left)

/-- Coordinate derivative of the product-sign folded parent test. -/
theorem euclideanCoordDeriv_cubeDirichletOddReflectionFoldedParentScalarTest
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    euclideanCoordDeriv i
        (cubeDirichletOddReflectionFoldedParentScalarTest Q φ) x =
      ∑ choice : Fin d → Fin 3,
        (cubeDirichletOddReflectionCellSign choice *
          cubeFaceReflectionCellFoldSign choice i) *
          euclideanCoordDeriv i φ
            (cubeFaceReflectionCellFoldMap Q choice x) := by
  classical
  unfold cubeDirichletOddReflectionFoldedParentScalarTest euclideanCoordDeriv
  rw [fderiv_fun_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro choice _hchoice
    have hdiff :
        DifferentiableAt ℝ
          (fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)) x :=
      (contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ).differentiable
        (by simp) x
    rw [fderiv_const_mul hdiff]
    change cubeDirichletOddReflectionCellSign choice *
        euclideanCoordDeriv i
          (fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)) x =
      (cubeDirichletOddReflectionCellSign choice *
        cubeFaceReflectionCellFoldSign choice i) *
        euclideanCoordDeriv i φ
          (cubeFaceReflectionCellFoldMap Q choice x)
    rw [euclideanCoordDeriv_comp_cubeFaceReflectionCellFoldMap hφ Q choice i x]
    by_cases h1 : choice i = 1 <;>
      simp [cubeFaceReflectionCellFoldSign, h1]
  · intro choice _hchoice
    exact
      (contDiff_const.mul
        (contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ)).differentiable
        (by simp) x

namespace H10Function

/-- The folded parent test, packaged as an `H¹₀` function on an origin cube. -/
noncomputable def cubeDirichletOddReflectionFoldedParentScalarTestToH10
    {d : ℕ} (m : ℤ) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    H10Function (openCubeSet (originCube d m)) :=
  H10Function.ofContDiffFaceZeroOnOpenCubeSet (originCube d m)
    (contDiff_cubeDirichletOddReflectionFoldedParentScalarTest
      (originCube d m) hφ)
    (hasCompactSupport_cubeDirichletOddReflectionFoldedParentScalarTest
      (originCube d m) hφ_compact)
    (fun i =>
      cubeDirichletOddReflectionFoldedParentScalarTest_lowerFaceProjection_eq_zero_originCube
        m i hφ_sub)
    (fun i =>
      cubeDirichletOddReflectionFoldedParentScalarTest_upperFaceProjection_eq_zero_originCube
        m i hφ_sub)

end H10Function

private theorem integrable_openCubeSet_cubeDirichletOddCellVectorPairing
    {d : ℕ} {Q : TriadicCube d} {G : Vec d → Vec d}
    (choice : Fin d → Fin 3)
    (hG : MemVectorL2 (openCubeSet Q) G)
    {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ) :
    MeasureTheory.Integrable
      (fun y =>
        cubeDirichletOddReflectionCellSign choice *
          vecDot (G y)
            (cubeFaceReflectionCellFoldLinear choice
              (euclideanGradient φ
                (cubeFaceReflectionCellFoldMap Q choice y))))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  let ψ : Vec d → ℝ :=
    fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ] using
      contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ
  have hψ_compact : HasCompactSupport ψ := by
    simpa [ψ] using
      hasCompactSupport_comp_cubeFaceReflectionCellFoldMap Q choice hφ_compact
  have hgradψ : MemVectorL2 (openCubeSet Q) (euclideanGradient ψ) :=
    memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hψ hψ_compact
  have hbase :
      MeasureTheory.Integrable
        (fun y => vecDot (G y) (euclideanGradient ψ y))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      integrableOn_vecDot_of_memVectorL2
        (U := openCubeSet Q) hG hgradψ
  refine (hbase.const_mul (cubeDirichletOddReflectionCellSign choice)).congr ?_
  filter_upwards with y
  have hgrad :=
    euclideanGradient_comp_cubeFaceReflectionCellFoldMap hφ Q choice y
  simpa [ψ] using congrArg
    (fun v => cubeDirichletOddReflectionCellSign choice * vecDot (G y) v)
    hgrad

private theorem integrable_openCubeSet_cubeDirichletOddCellScalarPairing
    {d : ℕ} {Q : TriadicCube d} {F : Vec d → ℝ}
    (choice : Fin d → Fin 3)
    (hF : MemScalarL2 (openCubeSet Q) F)
    {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ) :
    MeasureTheory.Integrable
      (fun y =>
        F y *
          (cubeDirichletOddReflectionCellSign choice *
            φ (cubeFaceReflectionCellFoldMap Q choice y)))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  let ψ : Vec d → ℝ :=
    fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ] using
      contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ
  have hψ_compact : HasCompactSupport ψ := by
    simpa [ψ] using
      hasCompactSupport_comp_cubeFaceReflectionCellFoldMap Q choice hφ_compact
  have hψL2 : MemScalarL2 (openCubeSet Q) ψ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (hψ.continuous.memLp_of_hasCompactSupport hψ_compact).restrict
        (openCubeSet Q)
  have hbase :
      MeasureTheory.Integrable (fun y => F y * ψ y)
        (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    hF.integrable_mul hψL2
  simpa [ψ, mul_assoc, mul_left_comm, mul_comm] using
    hbase.const_mul (cubeDirichletOddReflectionCellSign choice)

/-- Change variables on one reflection cell in the odd-reflected gradient
pairing. -/
theorem setIntegral_cubeFaceReflectionCellCube_vecDot_cubeDirichletOddReflectionVectorField_eq
    {d : ℕ} {Q : TriadicCube d} {G : Vec d → Vec d}
    (choice : Fin d → Fin 3) {φ : Vec d → ℝ} :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        vecDot (cubeDirichletOddReflectionVectorField Q G x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ y in openCubeSet Q,
        cubeDirichletOddReflectionCellSign choice *
          vecDot (G y)
            (cubeFaceReflectionCellFoldLinear choice
              (euclideanGradient φ
                (cubeFaceReflectionCellFoldMap Q choice y)))
          ∂MeasureTheory.volume := by
  let T : Vec d → Vec d := cubeFaceReflectionCellFoldMap Q choice
  let L : Vec d →L[ℝ] Vec d := cubeFaceReflectionCellFoldLinear choice
  let s : ℝ := cubeDirichletOddReflectionCellSign choice
  calc
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        vecDot (cubeDirichletOddReflectionVectorField Q G x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (fun y => s * vecDot (G y) (L (euclideanGradient φ (T y)))) (T x)
          ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
          intro x hx
          change
            vecDot (cubeDirichletOddReflectionVectorField Q G x)
                (euclideanGradient φ x) =
              s * vecDot (G (T x)) (L (euclideanGradient φ (T (T x))))
          have hvec :=
            cubeDirichletOddReflectionVectorField_eq_cellVectorField_of_mem_cellCube
              Q choice G hx
          rw [hvec]
          change
            vecDot (s • L (G (T x))) (euclideanGradient φ x) =
              s * vecDot (G (T x)) (L (euclideanGradient φ (T (T x))))
          calc
            vecDot (s • L (G (T x))) (euclideanGradient φ x) =
                s * vecDot (L (G (T x))) (euclideanGradient φ x) := by
                  rw [vecDot_smul_left]
            _ = s * vecDot (G (T x)) (L (euclideanGradient φ x)) := by
                  rw [vecDot_cubeFaceReflectionCellFoldLinear_left]
            _ = s * vecDot (G (T x))
                (L (euclideanGradient φ (T (T x)))) := by
                  simp [T, cubeFaceReflectionCellFoldMap_involutive Q choice x]
    _ = ∫ y in openCubeSet Q,
        cubeDirichletOddReflectionCellSign choice *
          vecDot (G y)
            (cubeFaceReflectionCellFoldLinear choice
              (euclideanGradient φ
                (cubeFaceReflectionCellFoldMap Q choice y)))
          ∂MeasureTheory.volume := by
          simpa [T, L, s] using
            setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
              Q choice
              (fun y => s * vecDot (G y) (L (euclideanGradient φ (T y))))

/-- Change variables on one reflection cell in the odd-reflected scalar
pairing. -/
theorem setIntegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionScalar_mul_eq
    {d : ℕ} {Q : TriadicCube d} {F : Vec d → ℝ}
    (choice : Fin d → Fin 3) {φ : Vec d → ℝ} :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        cubeDirichletOddReflectionScalar Q F x * φ x
          ∂MeasureTheory.volume =
      ∫ y in openCubeSet Q,
        F y *
          (cubeDirichletOddReflectionCellSign choice *
            φ (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := by
  let T : Vec d → Vec d := cubeFaceReflectionCellFoldMap Q choice
  let s : ℝ := cubeDirichletOddReflectionCellSign choice
  calc
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        cubeDirichletOddReflectionScalar Q F x * φ x
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (fun y => F y * (s * φ (T y))) (T x)
          ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
          intro x hx
          change
            cubeDirichletOddReflectionScalar Q F x * φ x =
              F (T x) * (s * φ (T (T x)))
          rw [cubeDirichletOddReflectionScalar_eq_cellScalar_of_mem_cellCube
            Q choice F hx]
          simp [cubeDirichletOddReflectionCellScalar, T, s,
            cubeFaceReflectionCellFoldMap_involutive Q choice x,
            mul_assoc, mul_comm]
    _ = ∫ y in openCubeSet Q,
        F y *
          (cubeDirichletOddReflectionCellSign choice *
            φ (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := by
          simpa [T, s] using
            setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
              Q choice (fun y => F y * (s * φ (T y)))

/-- The block pairing with the odd-reflected vector field is the original-cube
pairing against the folded derivative sum. -/
theorem setIntegral_cubeFaceReflectionBlockSet_vecDot_cubeDirichletOddReflectionVectorField_eq_folded_derivSum
    {d : ℕ} {Q : TriadicCube d} {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet Q) G)
    {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot (cubeDirichletOddReflectionVectorField Q G x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ y in openCubeSet Q,
        vecDot (G y)
          (fun i : Fin d =>
            ∑ choice : Fin d → Fin 3,
              (cubeDirichletOddReflectionCellSign choice *
                cubeFaceReflectionCellFoldSign choice i) *
                euclideanCoordDeriv i φ
                  (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := by
  classical
  let f : Vec d → ℝ := fun x =>
    vecDot (cubeDirichletOddReflectionVectorField Q G x)
      (euclideanGradient φ x)
  have hfCell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable f
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    let T : Vec d → Vec d := cubeFaceReflectionCellFoldMap Q choice
    let L : Vec d →L[ℝ] Vec d := cubeFaceReflectionCellFoldLinear choice
    let s : ℝ := cubeDirichletOddReflectionCellSign choice
    have hbase :=
      integrable_openCubeSet_cubeDirichletOddCellVectorPairing
        (Q := Q) (G := G) choice hG hφ hφ_compact
    have hcomp :
        MeasureTheory.Integrable
          (fun x => (fun y => s * vecDot (G y) (L (euclideanGradient φ (T y)))) (T x))
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
      simpa [T, L, s] using
        integrable_cubeFaceReflectionCellCube_comp_cellFoldMap
          (Q := Q) (choice := choice)
          (g := fun y => s * vecDot (G y) (L (euclideanGradient φ (T y))))
          hbase
    refine hcomp.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))]
      with x hx
    change
      s * vecDot (G (T x)) (L (euclideanGradient φ (T (T x)))) =
        vecDot (cubeDirichletOddReflectionVectorField Q G x)
          (euclideanGradient φ x)
    have hvec :=
      cubeDirichletOddReflectionVectorField_eq_cellVectorField_of_mem_cellCube
        Q choice G hx
    rw [hvec]
    change
      s * vecDot (G (T x)) (L (euclideanGradient φ (T (T x)))) =
        vecDot (s • L (G (T x))) (euclideanGradient φ x)
    symm
    calc
      vecDot (s • L (G (T x))) (euclideanGradient φ x) =
          s * vecDot (L (G (T x))) (euclideanGradient φ x) := by
            rw [vecDot_smul_left]
      _ = s * vecDot (G (T x)) (L (euclideanGradient φ x)) := by
            rw [vecDot_cubeFaceReflectionCellFoldLinear_left]
      _ = s * vecDot (G (T x))
          (L (euclideanGradient φ (T (T x)))) := by
            simp [T, cubeFaceReflectionCellFoldMap_involutive Q choice x]
  calc
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot (cubeDirichletOddReflectionVectorField Q G x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q, f x ∂MeasureTheory.volume := rfl
    _ = ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            f x ∂MeasureTheory.volume := by
          exact setIntegral_cubeFaceReflectionBlockSet_cellCube Q f hfCell
    _ = ∑ choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q,
            cubeDirichletOddReflectionCellSign choice *
              vecDot (G y)
                (cubeFaceReflectionCellFoldLinear choice
                  (euclideanGradient φ
                    (cubeFaceReflectionCellFoldMap Q choice y)))
              ∂MeasureTheory.volume := by
          apply Finset.sum_congr rfl
          intro choice _hchoice
          simpa [f] using
            setIntegral_cubeFaceReflectionCellCube_vecDot_cubeDirichletOddReflectionVectorField_eq
              (Q := Q) (G := G) choice (φ := φ)
    _ = ∫ y in openCubeSet Q,
          ∑ choice : Fin d → Fin 3,
            cubeDirichletOddReflectionCellSign choice *
              vecDot (G y)
                (cubeFaceReflectionCellFoldLinear choice
                  (euclideanGradient φ
                    (cubeFaceReflectionCellFoldMap Q choice y)))
          ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_finsetSum]
          intro choice _hchoice
          exact integrable_openCubeSet_cubeDirichletOddCellVectorPairing
            (Q := Q) (G := G) choice hG hφ hφ_compact
    _ = ∫ y in openCubeSet Q,
        vecDot (G y)
          (fun i : Fin d =>
            ∑ choice : Fin d → Fin 3,
              (cubeDirichletOddReflectionCellSign choice *
                cubeFaceReflectionCellFoldSign choice i) *
                euclideanCoordDeriv i φ
                  (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet Q) ?_
          intro y _hy
          simp [vecDot, cubeFaceReflectionCellFoldLinear_apply,
            cubeFaceReflectionCellFoldSign, euclideanGradient, euclideanCoordDeriv,
            Finset.mul_sum, mul_left_comm]
          rw [Finset.sum_comm]

/-- The block pairing with the odd-reflected scalar forcing is the
original-cube folded scalar pairing. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar_mul_eq_folded
    {d : ℕ} {Q : TriadicCube d} {F : Vec d → ℝ}
    (hF : MemScalarL2 (openCubeSet Q) F)
    {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeDirichletOddReflectionScalar Q F x * φ x
          ∂MeasureTheory.volume =
      ∫ y in openCubeSet Q,
        F y *
          (∑ choice : Fin d → Fin 3,
            cubeDirichletOddReflectionCellSign choice *
              φ (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := by
  classical
  let f : Vec d → ℝ := fun x => cubeDirichletOddReflectionScalar Q F x * φ x
  have hfCell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable f
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    let T : Vec d → Vec d := cubeFaceReflectionCellFoldMap Q choice
    let s : ℝ := cubeDirichletOddReflectionCellSign choice
    have hbase :=
      integrable_openCubeSet_cubeDirichletOddCellScalarPairing
        (Q := Q) (F := F) choice hF hφ hφ_compact
    have hcomp :
        MeasureTheory.Integrable
          (fun x => (fun y => F y * (s * φ (T y))) (T x))
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
      simpa [T, s] using
        integrable_cubeFaceReflectionCellCube_comp_cellFoldMap
          (Q := Q) (choice := choice)
          (g := fun y => F y * (s * φ (T y))) hbase
    refine hcomp.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))]
      with x hx
    change
      F (T x) * (s * φ (T (T x))) =
        cubeDirichletOddReflectionScalar Q F x * φ x
    rw [cubeDirichletOddReflectionScalar_eq_cellScalar_of_mem_cellCube
      Q choice F hx]
    simp [cubeDirichletOddReflectionCellScalar, T, s,
      cubeFaceReflectionCellFoldMap_involutive Q choice x,
      mul_assoc, mul_comm]
  calc
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeDirichletOddReflectionScalar Q F x * φ x
          ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q, f x ∂MeasureTheory.volume := rfl
    _ = ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            f x ∂MeasureTheory.volume := by
          exact setIntegral_cubeFaceReflectionBlockSet_cellCube Q f hfCell
    _ = ∑ choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q,
            F y *
              (cubeDirichletOddReflectionCellSign choice *
                φ (cubeFaceReflectionCellFoldMap Q choice y))
            ∂MeasureTheory.volume := by
          apply Finset.sum_congr rfl
          intro choice _hchoice
          simpa [f] using
            setIntegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionScalar_mul_eq
              (Q := Q) (F := F) choice (φ := φ)
    _ = ∫ y in openCubeSet Q,
        ∑ choice : Fin d → Fin 3,
          F y *
            (cubeDirichletOddReflectionCellSign choice *
              φ (cubeFaceReflectionCellFoldMap Q choice y))
        ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_finsetSum]
          intro choice _hchoice
          exact integrable_openCubeSet_cubeDirichletOddCellScalarPairing
            (Q := Q) (F := F) choice hF hφ hφ_compact
    _ = ∫ y in openCubeSet Q,
        F y *
          (∑ choice : Fin d → Fin 3,
            cubeDirichletOddReflectionCellSign choice *
              φ (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet Q) ?_
          intro y _hy
          change
            (∑ choice : Fin d → Fin 3,
              F y *
                (cubeDirichletOddReflectionCellSign choice *
                  φ (cubeFaceReflectionCellFoldMap Q choice y))) =
              F y *
                (∑ choice : Fin d → Fin 3,
                  cubeDirichletOddReflectionCellSign choice *
                    φ (cubeFaceReflectionCellFoldMap Q choice y))
          rw [Finset.mul_sum]

namespace CubeDirichletWeakPoissonProblem

/-- The original Dirichlet weak equation may be tested against the folded
parent test produced by odd reflection. -/
theorem test_cubeDirichletOddReflectionFoldedParentScalarTest_originCube
    {d : ℕ} {m : ℤ} {u : H10Function (openCubeSet (originCube d m))}
    {F φ : Vec d → ℝ}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∫ y in openCubeSet (originCube d m),
        vecDot (u.toH1Function.grad y)
          (euclideanGradient
            (cubeDirichletOddReflectionFoldedParentScalarTest
              (originCube d m) φ) y) ∂MeasureTheory.volume =
      ∫ y in openCubeSet (originCube d m),
        F y *
          cubeDirichletOddReflectionFoldedParentScalarTest
            (originCube d m) φ y ∂MeasureTheory.volume := by
  let ψ : H10Function (openCubeSet (originCube d m)) :=
    H10Function.cubeDirichletOddReflectionFoldedParentScalarTestToH10
      m hφ hφ_compact hφ_sub
  have htest := hweak ψ
  simpa [ψ, H10Function.cubeDirichletOddReflectionFoldedParentScalarTestToH10,
    H10Function.ofContDiffFaceZeroOnOpenCubeSet_toFun,
    H10Function.ofContDiffFaceZeroOnOpenCubeSet_grad, euclideanGradient]
    using! htest

/-- Expanded cell-sum form of the folded-test weak identity.  This is the
algebraic shape needed for the subsequent reflected-block
change-of-variables step. -/
theorem test_cubeDirichletOddReflectionFoldedParentScalarTest_derivSum_originCube
    {d : ℕ} {m : ℤ} {u : H10Function (openCubeSet (originCube d m))}
    {F φ : Vec d → ℝ}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∫ y in openCubeSet (originCube d m),
        vecDot (u.toH1Function.grad y)
          (fun i : Fin d =>
            ∑ choice : Fin d → Fin 3,
              (cubeDirichletOddReflectionCellSign choice *
                cubeFaceReflectionCellFoldSign choice i) *
                euclideanCoordDeriv i φ
                  (cubeFaceReflectionCellFoldMap (originCube d m) choice y))
          ∂MeasureTheory.volume =
      ∫ y in openCubeSet (originCube d m),
        F y *
          (∑ choice : Fin d → Fin 3,
            cubeDirichletOddReflectionCellSign choice *
              φ (cubeFaceReflectionCellFoldMap (originCube d m) choice y))
          ∂MeasureTheory.volume := by
  have hbase :=
    hweak.test_cubeDirichletOddReflectionFoldedParentScalarTest_originCube
      hφ hφ_compact hφ_sub
  calc
    ∫ y in openCubeSet (originCube d m),
        vecDot (u.toH1Function.grad y)
          (fun i : Fin d =>
            ∑ choice : Fin d → Fin 3,
              (cubeDirichletOddReflectionCellSign choice *
                cubeFaceReflectionCellFoldSign choice i) *
                euclideanCoordDeriv i φ
                  (cubeFaceReflectionCellFoldMap (originCube d m) choice y))
          ∂MeasureTheory.volume =
      ∫ y in openCubeSet (originCube d m),
        vecDot (u.toH1Function.grad y)
          (euclideanGradient
            (cubeDirichletOddReflectionFoldedParentScalarTest
              (originCube d m) φ) y) ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (originCube d m)) ?_
          intro y _hy
          have hgrad :
              euclideanGradient
                  (cubeDirichletOddReflectionFoldedParentScalarTest
                    (originCube d m) φ) y =
                fun i : Fin d =>
                  ∑ choice : Fin d → Fin 3,
                    (cubeDirichletOddReflectionCellSign choice *
                      cubeFaceReflectionCellFoldSign choice i) *
                      euclideanCoordDeriv i φ
                        (cubeFaceReflectionCellFoldMap (originCube d m) choice y) := by
            ext i
            rw [show
              (euclideanGradient
                (cubeDirichletOddReflectionFoldedParentScalarTest
                  (originCube d m) φ) y) i =
                euclideanCoordDeriv i
                  (cubeDirichletOddReflectionFoldedParentScalarTest
                    (originCube d m) φ) y by
                  rfl]
            exact euclideanCoordDeriv_cubeDirichletOddReflectionFoldedParentScalarTest
              (originCube d m) i hφ y
          change
            vecDot (u.toH1Function.grad y)
              (fun i : Fin d =>
                ∑ choice : Fin d → Fin 3,
                  (cubeDirichletOddReflectionCellSign choice *
                    cubeFaceReflectionCellFoldSign choice i) *
                    euclideanCoordDeriv i φ
                      (cubeFaceReflectionCellFoldMap (originCube d m) choice y)) =
              vecDot (u.toH1Function.grad y)
                (euclideanGradient
                  (cubeDirichletOddReflectionFoldedParentScalarTest
                    (originCube d m) φ) y)
          rw [hgrad]
    _ = ∫ y in openCubeSet (originCube d m),
        F y *
          cubeDirichletOddReflectionFoldedParentScalarTest
            (originCube d m) φ y ∂MeasureTheory.volume := hbase
    _ = ∫ y in openCubeSet (originCube d m),
        F y *
          (∑ choice : Fin d → Fin 3,
            cubeDirichletOddReflectionCellSign choice *
              φ (cubeFaceReflectionCellFoldMap (originCube d m) choice y))
          ∂MeasureTheory.volume := rfl

/-- Compact-test weak equation for the odd-reflected Dirichlet solution on
the full all-coordinate reflection block of an origin cube. -/
theorem cubeFaceReflectionBlock_oddWeakEquationOnBlock_originCube
    {d : ℕ} {m : ℤ} {u : H10Function (openCubeSet (originCube d m))}
    {F φ : Vec d → ℝ}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF : MemScalarL2 (openCubeSet (originCube d m)) F)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∫ x in cubeFaceReflectionBlockSet (originCube d m),
        vecDot
          (cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet (originCube d m),
        cubeDirichletOddReflectionScalar (originCube d m) F x * φ x
          ∂MeasureTheory.volume := by
  have hG : MemVectorL2 (openCubeSet (originCube d m))
      (fun y => u.toH1Function.grad y) := by
    simpa [MemVectorL2, volumeMeasureOn] using
      u.toH1Function.grad_memVectorL2
  rw [
    setIntegral_cubeFaceReflectionBlockSet_vecDot_cubeDirichletOddReflectionVectorField_eq_folded_derivSum
      (Q := originCube d m) (G := fun y => u.toH1Function.grad y)
      hG hφ hφ_compact,
    setIntegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar_mul_eq_folded
      (Q := originCube d m) (F := F) hF hφ hφ_compact]
  exact
    hweak.test_cubeDirichletOddReflectionFoldedParentScalarTest_derivSum_originCube
      hφ hφ_compact hφ_sub

/-- Centered parent-cube compact-test weak equation for the odd-reflected
Dirichlet solution. -/
theorem cubeDirichletOddReflectionParent_weakEquationOnParent_originCube
    {d : ℕ} {m : ℤ} {u : H10Function (openCubeSet (originCube d m))}
    {F φ : Vec d → ℝ}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF : MemScalarL2 (openCubeSet (originCube d m)) F)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet (originCube d (m + 1)),
        cubeDirichletOddReflectionScalar (originCube d m) F x * φ x
          ∂MeasureTheory.volume := by
  rw [
    setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
      (m := m)
      (f := fun x =>
        vecDot
          (cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) x)
          (euclideanGradient φ x)),
    setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
      (m := m)
      (f := fun x =>
        cubeDirichletOddReflectionScalar (originCube d m) F x * φ x)]
  exact
    hweak.cubeFaceReflectionBlock_oddWeakEquationOnBlock_originCube
      hF hφ hφ_compact hφ_sub

/-- Centered parent-cube weak equation, with the forcing hypothesis in the
normalized cube measure used by the public regularity contract. -/
theorem cubeDirichletOddReflectionParent_weakEquationOnParent_originCube_of_memLp_normalizedCubeMeasure
    {d : ℕ} {m : ℤ} {u : H10Function (openCubeSet (originCube d m))}
    {F φ : Vec d → ℝ}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet (originCube d (m + 1)),
        cubeDirichletOddReflectionScalar (originCube d m) F x * φ x
          ∂MeasureTheory.volume := by
  have hFopen : MemScalarL2 (openCubeSet (originCube d m)) F := by
    simpa [MemL2On, MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure
        (originCube d m) hF
  exact
    hweak.cubeDirichletOddReflectionParent_weakEquationOnParent_originCube
      hFopen hφ hφ_compact hφ_sub

/-- If the odd-reflected vector field has already been realized as the weak
gradient of an `H¹` function on the centered parent cube, the parent integral
identity becomes the standard `WeakPoissonEquationOn` interface. -/
theorem cubeDirichletOddReflectionParent_weakPoissonEquationOn_originCube_of_grad_eq
    {d : ℕ} {m : ℤ} {u : H10Function (openCubeSet (originCube d m))}
    {F : Vec d → ℝ}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (huP_grad :
      uP.grad =
        cubeDirichletOddReflectionVectorField (originCube d m)
          (fun y => u.toH1Function.grad y))
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    WeakPoissonEquationOn (openCubeSet (originCube d (m + 1))) uP
      (cubeDirichletOddReflectionScalar (originCube d m) F) := by
  intro φ hφ hφ_compact hφ_sub
  rw [huP_grad]
  exact
    hweak.cubeDirichletOddReflectionParent_weakEquationOnParent_originCube_of_memLp_normalizedCubeMeasure
      hF hφ hφ_compact hφ_sub

end CubeDirichletWeakPoissonProblem

end

end Homogenization
