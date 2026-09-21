/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.FaceVanishCollar
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Folding

/-! # Reflection Parent Test Fold -/

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-!
# Signed folded parent tests

For the parent-cube H¹ gluing step, a parent test is pulled back to the
original cube through every reflection cell.  In the weak-gradient identity
for coordinate `i`, the cell pullback is weighted by the `i`th reflection
sign.  The resulting signed sum is the test whose boundary-face cancellation
should feed the face-zero cutoff closure.
-/

/-- The sign contributed by a reflection cell in coordinate `i`. -/
def cubeFaceReflectionCellFoldSign {d : ℕ}
    (choice : Fin d → Fin 3) (i : Fin d) : ℝ :=
  if choice i = 1 then 1 else -1

@[simp] theorem cubeFaceReflectionCellFoldSign_mul_self {d : ℕ}
    (choice : Fin d → Fin 3) (i : Fin d) :
    cubeFaceReflectionCellFoldSign choice i *
        cubeFaceReflectionCellFoldSign choice i = 1 := by
  by_cases h : choice i = 1 <;>
    simp [cubeFaceReflectionCellFoldSign, h]

/-- Signed pullback of a parent scalar test to the original cube, for the
weak-gradient identity in coordinate `i`. -/
def cubeFaceReflectionFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (φ : Vec d → ℝ) : Vec d → ℝ :=
  fun y =>
    ∑ choice : Fin d → Fin 3,
      cubeFaceReflectionCellFoldSign choice i *
        φ (cubeFaceReflectionCellFoldMap Q choice y)

/-- Involution on reflection-cell choices pairing the lower neighbor strip
with the original strip in coordinate `i`.  The upper strip is fixed. -/
def cubeFaceReflectionLowerChoiceSwap {d : ℕ}
    (i : Fin d) (choice : Fin d → Fin 3) : Fin d → Fin 3 :=
  Function.update choice i
    (if choice i = 0 then 1 else if choice i = 1 then 0 else choice i)

/-- Involution on reflection-cell choices pairing the original strip with the
upper neighbor strip in coordinate `i`.  The lower strip is fixed. -/
def cubeFaceReflectionUpperChoiceSwap {d : ℕ}
    (i : Fin d) (choice : Fin d → Fin 3) : Fin d → Fin 3 :=
  Function.update choice i
    (if choice i = 1 then 2 else if choice i = 2 then 1 else choice i)

@[simp] theorem cubeFaceReflectionLowerChoiceSwap_apply_self {d : ℕ}
    (i : Fin d) (choice : Fin d → Fin 3) :
    cubeFaceReflectionLowerChoiceSwap i choice i =
      if choice i = 0 then 1 else if choice i = 1 then 0 else choice i := by
  simp [cubeFaceReflectionLowerChoiceSwap]

@[simp] theorem cubeFaceReflectionUpperChoiceSwap_apply_self {d : ℕ}
    (i : Fin d) (choice : Fin d → Fin 3) :
    cubeFaceReflectionUpperChoiceSwap i choice i =
      if choice i = 1 then 2 else if choice i = 2 then 1 else choice i := by
  simp [cubeFaceReflectionUpperChoiceSwap]

@[simp] theorem cubeFaceReflectionLowerChoiceSwap_apply_ne {d : ℕ}
    {i j : Fin d} (hji : j ≠ i) (choice : Fin d → Fin 3) :
    cubeFaceReflectionLowerChoiceSwap i choice j = choice j := by
  simp [cubeFaceReflectionLowerChoiceSwap, Function.update_of_ne hji]

@[simp] theorem cubeFaceReflectionUpperChoiceSwap_apply_ne {d : ℕ}
    {i j : Fin d} (hji : j ≠ i) (choice : Fin d → Fin 3) :
    cubeFaceReflectionUpperChoiceSwap i choice j = choice j := by
  simp [cubeFaceReflectionUpperChoiceSwap, Function.update_of_ne hji]

@[simp] theorem cubeFaceReflectionLowerChoiceSwap_involutive {d : ℕ}
    (i : Fin d) :
    Function.Involutive (cubeFaceReflectionLowerChoiceSwap (d := d) i) := by
  intro choice
  ext j
  by_cases hji : j = i
  · subst j
    by_cases h0 : choice i = 0
    · simp [cubeFaceReflectionLowerChoiceSwap, h0]
    · by_cases h1 : choice i = 1
      · simp [cubeFaceReflectionLowerChoiceSwap, h1]
      · simp [cubeFaceReflectionLowerChoiceSwap, h0, h1]
  · simp [hji]

@[simp] theorem cubeFaceReflectionUpperChoiceSwap_involutive {d : ℕ}
    (i : Fin d) :
    Function.Involutive (cubeFaceReflectionUpperChoiceSwap (d := d) i) := by
  intro choice
  ext j
  by_cases hji : j = i
  · subst j
    by_cases h1 : choice i = 1
    · simp [cubeFaceReflectionUpperChoiceSwap, h1]
    · by_cases h2 : choice i = 2
      · simp [cubeFaceReflectionUpperChoiceSwap, h2]
      · simp [cubeFaceReflectionUpperChoiceSwap, h1, h2]
  · simp [hji]

/-- On the lower `i`-face, the lower/original paired cell fold maps agree. -/
theorem cubeFaceReflectionCellFoldMap_lowerChoiceSwap_lowerFaceProjection
    {d : ℕ} (Q : TriadicCube d) (i : Fin d)
    (choice : Fin d → Fin 3) (x : Vec d) :
    cubeFaceReflectionCellFoldMap Q (cubeFaceReflectionLowerChoiceSwap i choice)
        (cubeLowerFaceProjection Q i x) =
      cubeFaceReflectionCellFoldMap Q choice (cubeLowerFaceProjection Q i x) := by
  ext j
  by_cases hji : j = i
  · subst j
    by_cases h0 : choice i = 0
    · simp [cubeFaceReflectionCellFoldMap, cubeLowerFaceProjection, h0]
      ring
    · by_cases h1 : choice i = 1
      · simp [cubeFaceReflectionCellFoldMap, cubeLowerFaceProjection, h1]
        ring
      · simp [cubeFaceReflectionCellFoldMap, cubeLowerFaceProjection, h0, h1]
  · simp [cubeFaceReflectionCellFoldMap, cubeLowerFaceProjection, hji]

/-- On the upper `i`-face, the original/upper paired cell fold maps agree. -/
theorem cubeFaceReflectionCellFoldMap_upperChoiceSwap_upperFaceProjection
    {d : ℕ} (Q : TriadicCube d) (i : Fin d)
    (choice : Fin d → Fin 3) (x : Vec d) :
    cubeFaceReflectionCellFoldMap Q (cubeFaceReflectionUpperChoiceSwap i choice)
        (cubeUpperFaceProjection Q i x) =
      cubeFaceReflectionCellFoldMap Q choice (cubeUpperFaceProjection Q i x) := by
  ext j
  by_cases hji : j = i
  · subst j
    by_cases h1 : choice i = 1
    · simp [cubeFaceReflectionCellFoldMap, cubeUpperFaceProjection, h1]
      ring
    · by_cases h2 : choice i = 2
      · simp [cubeFaceReflectionCellFoldMap, cubeUpperFaceProjection, h2]
        ring
      · simp [cubeFaceReflectionCellFoldMap, cubeUpperFaceProjection, h1, h2]
  · simp [cubeFaceReflectionCellFoldMap, cubeUpperFaceProjection, hji]

/-- Lower-face cancellation for the signed folded parent test, assuming the
unpaired upper-strip outer cell evaluates to zero. -/
theorem cubeFaceReflectionFoldedParentScalarTest_lowerFaceProjection_eq_zero_of_outer
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (houter : ∀ choice : Fin d → Fin 3, ∀ x : Vec d,
      choice i ≠ 0 → choice i ≠ 1 →
        φ (cubeFaceReflectionCellFoldMap Q choice
          (cubeLowerFaceProjection Q i x)) = 0) :
    ∀ x : Vec d,
      cubeFaceReflectionFoldedParentScalarTest Q i φ
        (cubeLowerFaceProjection Q i x) = 0 := by
  classical
  intro x
  unfold cubeFaceReflectionFoldedParentScalarTest
  let f : (Fin d → Fin 3) → ℝ := fun choice =>
    cubeFaceReflectionCellFoldSign choice i *
      φ (cubeFaceReflectionCellFoldMap Q choice
        (cubeLowerFaceProjection Q i x))
  simpa [f] using
    (Finset.sum_ninvolution (s := Finset.univ) (f := f)
      (cubeFaceReflectionLowerChoiceSwap i)
      (by
        intro choice
        by_cases h0 : choice i = 0
        · simp [f, cubeFaceReflectionCellFoldSign, h0,
            cubeFaceReflectionCellFoldMap_lowerChoiceSwap_lowerFaceProjection Q i choice x]
        · by_cases h1 : choice i = 1
          · simp [f, cubeFaceReflectionCellFoldSign, h1,
              cubeFaceReflectionCellFoldMap_lowerChoiceSwap_lowerFaceProjection Q i choice x]
          · have hzero := houter choice x h0 h1
            simp [f, hzero,
              cubeFaceReflectionCellFoldMap_lowerChoiceSwap_lowerFaceProjection Q i choice x])
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

/-- Upper-face cancellation for the signed folded parent test, assuming the
unpaired lower-strip outer cell evaluates to zero. -/
theorem cubeFaceReflectionFoldedParentScalarTest_upperFaceProjection_eq_zero_of_outer
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (houter : ∀ choice : Fin d → Fin 3, ∀ x : Vec d,
      choice i ≠ 1 → choice i ≠ 2 →
        φ (cubeFaceReflectionCellFoldMap Q choice
          (cubeUpperFaceProjection Q i x)) = 0) :
    ∀ x : Vec d,
      cubeFaceReflectionFoldedParentScalarTest Q i φ
        (cubeUpperFaceProjection Q i x) = 0 := by
  classical
  intro x
  unfold cubeFaceReflectionFoldedParentScalarTest
  let f : (Fin d → Fin 3) → ℝ := fun choice =>
    cubeFaceReflectionCellFoldSign choice i *
      φ (cubeFaceReflectionCellFoldMap Q choice
        (cubeUpperFaceProjection Q i x))
  simpa [f] using
    (Finset.sum_ninvolution (s := Finset.univ) (f := f)
      (cubeFaceReflectionUpperChoiceSwap i)
      (by
        intro choice
        by_cases h1 : choice i = 1
        · simp [f, cubeFaceReflectionCellFoldSign, h1,
            cubeFaceReflectionCellFoldMap_upperChoiceSwap_upperFaceProjection Q i choice x]
        · by_cases h2 : choice i = 2
          · simp [f, cubeFaceReflectionCellFoldSign, h2,
              cubeFaceReflectionCellFoldMap_upperChoiceSwap_upperFaceProjection Q i choice x]
          · have hzero := houter choice x h1 h2
            simp [f, hzero,
              cubeFaceReflectionCellFoldMap_upperChoiceSwap_upperFaceProjection Q i choice x])
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

private theorem fin_three_eq_zero_of_ne_one_ne_two
    (a : Fin 3) (h1 : a ≠ 1) (h2 : a ≠ 2) : a = 0 := by
  revert a
  decide

private theorem eq_zero_of_tsupport_subset_of_notMem
    {d : ℕ} {U : Set (Vec d)} {φ : Vec d → ℝ} {x : Vec d}
    (hφ_sub : tsupport φ ⊆ U) (hx : x ∉ U) :
    φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hxt => hx (hφ_sub hxt)

/-- On the lower original face, the unpaired upper reflection cell lands on
the upper outer face of the parent centered cube. -/
theorem cubeFaceReflectionCellFoldMap_lowerFaceProjection_notMem_openCubeSet_succ_originCube
    {d : ℕ} (m : ℤ) (i : Fin d) (choice : Fin d → Fin 3) (x : Vec d)
    (h0 : choice i ≠ 0) (h1 : choice i ≠ 1) :
    cubeFaceReflectionCellFoldMap (originCube d m) choice
        (cubeLowerFaceProjection (originCube d m) i x) ∉
      openCubeSet (originCube d (m + 1)) := by
  intro hmem
  have hi := (mem_openCubeSet_originCube_iff.mp hmem) i
  have hcoord :
      cubeFaceReflectionCellFoldMap (originCube d m) choice
          (cubeLowerFaceProjection (originCube d m) i x) i =
        (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1) := by
    simp [cubeFaceReflectionCellFoldMap, cubeLowerFaceProjection,
      cubeLowerFaceCoord, cubeUpperFaceCoord, originCube, cubeScaleFactor,
      h0, h1, zpow_add₀, show (3 : ℝ) ≠ 0 by norm_num]
    ring
  have hlt :
      (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1) <
        (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1) := by
    simpa [hcoord] using hi.2
  exact (lt_irrefl _ hlt)

/-- On the upper original face, the unpaired lower reflection cell lands on
the lower outer face of the parent centered cube. -/
theorem cubeFaceReflectionCellFoldMap_upperFaceProjection_notMem_openCubeSet_succ_originCube
    {d : ℕ} (m : ℤ) (i : Fin d) (choice : Fin d → Fin 3) (x : Vec d)
    (h1 : choice i ≠ 1) (h2 : choice i ≠ 2) :
    cubeFaceReflectionCellFoldMap (originCube d m) choice
        (cubeUpperFaceProjection (originCube d m) i x) ∉
      openCubeSet (originCube d (m + 1)) := by
  intro hmem
  have hi := (mem_openCubeSet_originCube_iff.mp hmem) i
  have h0 : choice i = 0 := fin_three_eq_zero_of_ne_one_ne_two (choice i) h1 h2
  have hcoord :
      cubeFaceReflectionCellFoldMap (originCube d m) choice
          (cubeUpperFaceProjection (originCube d m) i x) i =
        (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (m + 1) := by
    simp [cubeFaceReflectionCellFoldMap, cubeUpperFaceProjection,
      cubeLowerFaceCoord, cubeUpperFaceCoord, originCube, cubeScaleFactor,
      h0, zpow_add₀, show (3 : ℝ) ≠ 0 by norm_num]
    ring
  have hlt :
      (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (m + 1) <
        (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (m + 1) := by
    simpa [hcoord] using hi.1
  exact (lt_irrefl _ hlt)

/-- Origin-cube lower-face cancellation for parent tests supported in the next
larger centered cube. -/
theorem cubeFaceReflectionFoldedParentScalarTest_lowerFaceProjection_eq_zero_originCube
    {d : ℕ} (m : ℤ) (i : Fin d) {φ : Vec d → ℝ}
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∀ x : Vec d,
      cubeFaceReflectionFoldedParentScalarTest (originCube d m) i φ
        (cubeLowerFaceProjection (originCube d m) i x) = 0 := by
  refine
    cubeFaceReflectionFoldedParentScalarTest_lowerFaceProjection_eq_zero_of_outer
      (originCube d m) i ?_
  intro choice x h0 h1
  exact eq_zero_of_tsupport_subset_of_notMem hφ_sub
    (cubeFaceReflectionCellFoldMap_lowerFaceProjection_notMem_openCubeSet_succ_originCube
      m i choice x h0 h1)

/-- Origin-cube upper-face cancellation for parent tests supported in the next
larger centered cube. -/
theorem cubeFaceReflectionFoldedParentScalarTest_upperFaceProjection_eq_zero_originCube
    {d : ℕ} (m : ℤ) (i : Fin d) {φ : Vec d → ℝ}
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∀ x : Vec d,
      cubeFaceReflectionFoldedParentScalarTest (originCube d m) i φ
        (cubeUpperFaceProjection (originCube d m) i x) = 0 := by
  refine
    cubeFaceReflectionFoldedParentScalarTest_upperFaceProjection_eq_zero_of_outer
      (originCube d m) i ?_
  intro choice x h1 h2
  exact eq_zero_of_tsupport_subset_of_notMem hφ_sub
    (cubeFaceReflectionCellFoldMap_upperFaceProjection_notMem_openCubeSet_succ_originCube
      m i choice x h1 h2)

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

/-- The signed folded parent test is smooth when the parent test is smooth. -/
theorem contDiff_cubeFaceReflectionFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (cubeFaceReflectionFoldedParentScalarTest Q i φ) := by
  classical
  unfold cubeFaceReflectionFoldedParentScalarTest
  exact
    ContDiff.sum fun choice _ =>
      contDiff_const.mul
        (contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ)

/-- Coordinate derivative of the signed folded parent test.  The prefactor
sign cancels the chain-rule reflection sign. -/
theorem euclideanCoordDeriv_cubeFaceReflectionFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    euclideanCoordDeriv i
        (cubeFaceReflectionFoldedParentScalarTest Q i φ) x =
      ∑ choice : Fin d → Fin 3,
        euclideanCoordDeriv i φ
          (cubeFaceReflectionCellFoldMap Q choice x) := by
  classical
  unfold cubeFaceReflectionFoldedParentScalarTest euclideanCoordDeriv
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
    change cubeFaceReflectionCellFoldSign choice i *
        euclideanCoordDeriv i
          (fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)) x =
      euclideanCoordDeriv i φ (cubeFaceReflectionCellFoldMap Q choice x)
    rw [euclideanCoordDeriv_comp_cubeFaceReflectionCellFoldMap hφ Q choice i x]
    by_cases h1 : choice i = 1 <;>
      simp [cubeFaceReflectionCellFoldSign, h1]
  · intro choice _hchoice
    exact
      (contDiff_const.mul
        (contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ)).differentiable
        (by simp) x

/-- The signed folded parent test has compact support when the parent test
has compact support. -/
theorem hasCompactSupport_cubeFaceReflectionFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : HasCompactSupport φ) :
    HasCompactSupport (cubeFaceReflectionFoldedParentScalarTest Q i φ) := by
  classical
  unfold cubeFaceReflectionFoldedParentScalarTest
  simpa using
    hasCompactSupport_finset_sum (Finset.univ : Finset (Fin d → Fin 3))
      (fun choice y =>
        cubeFaceReflectionCellFoldSign choice i *
          φ (cubeFaceReflectionCellFoldMap Q choice y))
      (by
        intro choice _hchoice
        exact
          (hasCompactSupport_comp_cubeFaceReflectionCellFoldMap Q choice hφ).mul_left)

end

end Homogenization
