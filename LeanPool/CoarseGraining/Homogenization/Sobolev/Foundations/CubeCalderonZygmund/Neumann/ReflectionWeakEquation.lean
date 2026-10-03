/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix
public import LeanPool.CoarseGraining.Homogenization.PDE.NeumannRHS
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.ReflectionFiniteP
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentOrthogonality

/-!
# Neumann divergence equations under even reflection

A compactly supported parent test is folded through every reflection cell and
summed on the source cube.  Its gradient is exactly the folded parent gradient
appearing in the existing change-of-variables theorem.  Subtracting its source
average makes it an admissible mean-zero Neumann test without changing that
gradient.  This proves the reflected divergence equation without introducing
any boundary or comparison hypothesis.
-/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory Set
open CubeCalderonZygmund

/-- Unsigned fold of a parent scalar test through all reflection cells. -/
def neumannEvenFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) (phi : Vec d → ℝ) : Vec d → ℝ :=
  fun y ↦
    ∑ choice : Fin d → Fin 3,
      phi (cubeFaceReflectionCellFoldMap Q choice y)

private theorem hasCompactSupport_finset_sum
    {alpha beta iota : Type*} [TopologicalSpace alpha] [AddCommMonoid beta]
    [DecidableEq iota] (s : Finset iota) (f : iota → alpha → beta)
    (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simpa using! (HasCompactSupport.zero :
      HasCompactSupport (fun _ : alpha ↦ (0 : beta)))
  · intro a s has hs hf
    have ha : HasCompactSupport (f a) := hf a (by simp [has])
    have hs' : HasCompactSupport (fun x ↦ ∑ i ∈ s, f i x) :=
      hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert has] using! ha.add hs'

/-- The unsigned folded parent test is smooth. -/
theorem contDiff_neumannEvenFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) {phi : Vec d → ℝ}
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) :
    ContDiff ℝ (⊤ : ℕ∞) (neumannEvenFoldedParentScalarTest Q phi) := by
  classical
  unfold neumannEvenFoldedParentScalarTest
  exact ContDiff.sum fun choice _ ↦
    contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hphi

/-- The unsigned folded parent test has compact support. -/
theorem hasCompactSupport_neumannEvenFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) {phi : Vec d → ℝ}
    (hphi : HasCompactSupport phi) :
    HasCompactSupport (neumannEvenFoldedParentScalarTest Q phi) := by
  classical
  unfold neumannEvenFoldedParentScalarTest
  simpa using
    hasCompactSupport_finset_sum
      (Finset.univ : Finset (Fin d → Fin 3))
      (fun choice y ↦ phi (cubeFaceReflectionCellFoldMap Q choice y))
      (by
        intro choice _hchoice
        exact hasCompactSupport_comp_cubeFaceReflectionCellFoldMap Q choice hphi)

/-- Coordinate derivative of the unsigned folded parent test. -/
theorem euclideanCoordDeriv_neumannEvenFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {phi : Vec d → ℝ}
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (y : Vec d) :
    euclideanCoordDeriv i (neumannEvenFoldedParentScalarTest Q phi) y =
      ∑ choice : Fin d → Fin 3,
        cubeFaceReflectionCellFoldSign choice i *
          euclideanCoordDeriv i phi
            (cubeFaceReflectionCellFoldMap Q choice y) := by
  classical
  unfold neumannEvenFoldedParentScalarTest euclideanCoordDeriv
  rw [fderiv_fun_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro choice _hchoice
    exact euclideanCoordDeriv_comp_cubeFaceReflectionCellFoldMap
      hphi Q choice i y
  · intro choice _hchoice
    exact
      (contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hphi).differentiable
        (by simp) y

/-- The gradient of the folded scalar test is the existing folded parent
vector field applied to the parent gradient. -/
theorem euclideanGradient_neumannEvenFoldedParentScalarTest {d : ℕ}
    (Q : TriadicCube d) {phi : Vec d → ℝ}
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) :
    euclideanGradient (neumannEvenFoldedParentScalarTest Q phi) =
      cubeFaceReflectionFoldedParentVectorField Q (euclideanGradient phi) := by
  funext y i
  rw [show
    euclideanGradient (neumannEvenFoldedParentScalarTest Q phi) y i =
      euclideanCoordDeriv i (neumannEvenFoldedParentScalarTest Q phi) y by
        rfl]
  rw [euclideanCoordDeriv_neumannEvenFoldedParentScalarTest Q i hphi y]
  unfold cubeFaceReflectionFoldedParentVectorField
  simp only [Finset.sum_apply, cubeFaceReflectionCellFoldLinear_apply]
  apply Finset.sum_congr rfl
  intro choice _hchoice
  by_cases hchoice : choice i = 1
  · simp [cubeFaceReflectionCellFoldSign, hchoice]
    rfl
  · simp [cubeFaceReflectionCellFoldSign, hchoice]
    rfl

/-- Convert the raw scalar-matrix Neumann predicate with datum `-h` to the
explicit constant-coefficient negative-pairing equation. -/
theorem IsMeanZeroNeumannRhsWeakSolution.scalarMatrix_neg_weak
    {d : ℕ} {U : Set (Vec d)} {sigma0 : ℝ}
    {u : H1MeanZeroFunction U} {h : Vec d → Vec d}
    (hweak : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0) U u (fun x ↦ -h x)) :
    ∀ psi : H1MeanZeroFunction U,
      sigma0 * ∫ x in U,
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in U,
          vecDot (h x) (psi.toH1Function.grad x) ∂volume := by
  intro psi
  simpa only [matVecMul_scalarMatrix, vecDot_smul_left, integral_const_mul,
    Pi.neg_apply, vecDot_neg_left, integral_neg] using hweak psi

private theorem neumannEvenReflection_parent_weakEquation
    {d : ℕ} {m : ℤ} {sigma0 : ℝ}
    {u : H1MeanZeroFunction (openCubeSet (originCube d m))}
    {h : Vec d → Vec d}
    (hh : MemVectorL2 (openCubeSet (originCube d m)) h)
    (hweak : ∀ psi : H1MeanZeroFunction (openCubeSet (originCube d m)),
      sigma0 * ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet (originCube d m),
          vecDot (h x) (psi.toH1Function.grad x) ∂volume)
    {phi : Vec d → ℝ} (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hphi_compact : HasCompactSupport phi) :
    sigma0 * ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m)
            (fun y ↦ u.toH1Function.grad y) x)
          (euclideanGradient phi x) ∂volume =
      -∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m) h x)
          (euclideanGradient phi x) ∂volume := by
  let Q : TriadicCube d := originCube d m
  let v : H1Function (openCubeSet Q) :=
    H1Function.ofContDiff (isOpen_openCubeSet Q)
      ((contDiff_neumannEvenFoldedParentScalarTest Q hphi).of_le (by simp))
      (hasCompactSupport_neumannEvenFoldedParentScalarTest Q hphi_compact)
  let psi : H1MeanZeroFunction (openCubeSet Q) := v.toMeanZero
  have hpsi_grad : psi.toH1Function.grad =
      cubeFaceReflectionFoldedParentVectorField Q (euclideanGradient phi) := by
    funext y i
    simp only [psi, H1Function.toMeanZero_grad]
    change euclideanGradient (neumannEvenFoldedParentScalarTest Q phi) y i = _
    rw [euclideanGradient_neumannEvenFoldedParentScalarTest Q hphi]
  have hsource := hweak psi
  have hsource' :
      sigma0 * ∫ y in openCubeSet Q,
          vecDot (u.toH1Function.grad y)
            (cubeFaceReflectionFoldedParentVectorField Q
              (euclideanGradient phi) y) ∂volume =
        -∫ y in openCubeSet Q,
          vecDot (h y)
            (cubeFaceReflectionFoldedParentVectorField Q
              (euclideanGradient phi) y) ∂volume := by
    simpa only [Q, hpsi_grad] using hsource
  have hgradphi : MemVectorL2 (openCubeSet (originCube d (m + 1)))
      (euclideanGradient phi) :=
    memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport
      hphi hphi_compact
  have huTransport :=
    setIntegral_originCube_succ_vecDot_field_reflectedVectorField_eq_folded
      (m := m) (g := euclideanGradient phi)
      (G := fun y ↦ u.toH1Function.grad y)
      hgradphi u.toH1Function.grad_memVectorL2
  have hhTransport :=
    setIntegral_originCube_succ_vecDot_field_reflectedVectorField_eq_folded
      (m := m) (g := euclideanGradient phi) (G := h) hgradphi hh
  calc
    sigma0 * ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m)
            (fun y ↦ u.toH1Function.grad y) x)
          (euclideanGradient phi x) ∂volume =
      sigma0 * ∫ y in openCubeSet Q,
        vecDot (u.toH1Function.grad y)
          (cubeFaceReflectionFoldedParentVectorField Q
            (euclideanGradient phi) y) ∂volume := by
            rw [show Q = originCube d m by rfl]
            congr 1
            simpa only [vecDot_comm] using huTransport
    _ = -∫ y in openCubeSet Q,
        vecDot (h y)
          (cubeFaceReflectionFoldedParentVectorField Q
            (euclideanGradient phi) y) ∂volume := hsource'
    _ = -∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m) h x)
          (euclideanGradient phi x) ∂volume := by
            rw [show Q = originCube d m by rfl]
            congr 1
            simpa only [vecDot_comm] using hhTransport.symm

/-- The block-folded source solution satisfies the reflected compact-test
divergence equation on the full reflection block. -/
theorem H1MeanZeroFunction.cubeFaceReflectionBlockFold_neumannDivergence_weakEquationOnBlock
    {d : ℕ} {m : ℤ} {sigma0 : ℝ}
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    {h : Vec d → Vec d}
    (hh : MemVectorL2 (openCubeSet (originCube d m)) h)
    (hweak : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h x))
    {phi : Vec d → ℝ} (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hphi_compact : HasCompactSupport phi) :
    sigma0 * ∫ x in cubeFaceReflectionBlockSet (originCube d m),
        vecDot
          (u.toH1Function.cubeFaceReflectionBlockFold.grad x)
          (euclideanGradient phi x) ∂volume =
      -∫ x in cubeFaceReflectionBlockSet (originCube d m),
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m) h x)
          (euclideanGradient phi x) ∂volume := by
  change
    sigma0 * ∫ x in cubeFaceReflectionBlockSet (originCube d m),
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m)
            (fun y ↦ u.toH1Function.grad y) x)
          (euclideanGradient phi x) ∂volume = _
  rw [← setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
      (m := m)
      (f := fun x ↦ vecDot
        (cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y ↦ u.toH1Function.grad y) x)
        (euclideanGradient phi x)),
    ← setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
      (m := m)
      (f := fun x ↦ vecDot
        (cubeCoordinateFoldReflectedVectorField (originCube d m) h x)
        (euclideanGradient phi x))]
  exact neumannEvenReflection_parent_weakEquation hh
    hweak.scalarMatrix_neg_weak hphi hphi_compact

/-- An honest parent-cube `H¹` realization of the Neumann even reflection,
together with its compact-test divergence equation. -/
theorem exists_h1Function_neumannEvenReflectionParent_divergence_rhs_originCube
    {d : ℕ} {m : ℤ} {sigma0 : ℝ}
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    {h : Vec d → Vec d}
    (hh : MemVectorL2 (openCubeSet (originCube d m)) h)
    (hweak : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h x)) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.grad =
          cubeCoordinateFoldReflectedVectorField (originCube d m)
            (fun y ↦ u.toH1Function.grad y) ∧
        ∀ (phi : Vec d → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) phi →
          HasCompactSupport phi →
          tsupport phi ⊆ openCubeSet (originCube d (m + 1)) →
          sigma0 * ∫ x in openCubeSet (originCube d (m + 1)),
              vecDot (uP.grad x) (euclideanGradient phi x) ∂volume =
            -∫ x in openCubeSet (originCube d (m + 1)),
              vecDot
                (cubeCoordinateFoldReflectedVectorField (originCube d m) h x)
                (euclideanGradient phi x) ∂volume := by
  obtain ⟨uP, _huP_toFun, huP_grad⟩ :=
    exists_cubeFaceReflectionParentH1Function_originCube u.toH1Function
  refine ⟨uP, huP_grad, ?_⟩
  intro phi hphi hphi_compact _hphi_sub
  rw [huP_grad]
  exact neumannEvenReflection_parent_weakEquation hh
    hweak.scalarMatrix_neg_weak hphi hphi_compact

/-- The reflected-parent package specialized to an `L² ∩ L^p` cube datum. -/
theorem exists_h1Function_neumannEvenReflectionParent_divergence_rhs_of_cubeData
    {d : ℕ} {m : ℤ} {q : FiniteLpExponent} {sigma0 : ℝ}
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hweak : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x)) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.grad =
          cubeCoordinateFoldReflectedVectorField (originCube d m)
            (fun y ↦ u.toH1Function.grad y) ∧
        ∀ (phi : Vec d → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) phi →
          HasCompactSupport phi →
          tsupport phi ⊆ openCubeSet (originCube d (m + 1)) →
          sigma0 * ∫ x in openCubeSet (originCube d (m + 1)),
              vecDot (uP.grad x) (euclideanGradient phi x) ∂volume =
            -∫ x in openCubeSet (originCube d (m + 1)),
              vecDot
                (h.neumannEvenReflectionToParent.toField x)
                (euclideanGradient phi x) ∂volume := by
  simpa only
      [CubeEuclideanL2LpField.neumannEvenReflectionToParent_toField] using
    exists_h1Function_neumannEvenReflectionParent_divergence_rhs_originCube
      u h.memVectorL2_openCubeSet hweak

end

end Homogenization
