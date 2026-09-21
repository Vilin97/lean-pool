/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph.Graph
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionWeakEquation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit

/-! # Reflection Parent H1Graph -/

namespace Homogenization

open scoped BigOperators ENNReal Manifold

noncomputable section

/-!
# Parent `H¹` realization for the Dirichlet odd reflection

This file turns the pointwise odd reflection on the centered parent cube into
an honest `H1Function`.  The proof uses the closed `H¹` graph: after folding
parent tests back to the original cube, the zero-trace approximation package
of `H10Function` supplies the needed integration-by-parts identity.
-/

private theorem memScalarL2_of_contDiff_hasCompactSupport {d : ℕ}
    (U : Set (Vec d)) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_compact : HasCompactSupport ψ) :
    MemScalarL2 U ψ := by
  simpa [MemScalarL2, volumeMeasureOn] using
    (hψ.continuous.memLp_of_hasCompactSupport hψ_compact).restrict U

private theorem memScalarL2_euclideanCoordDeriv_of_contDiff_hasCompactSupport
    {d : ℕ} (U : Set (Vec d)) (i : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_compact : HasCompactSupport ψ) :
    MemScalarL2 U (euclideanCoordDeriv i ψ) := by
  simpa [MemScalarL2, volumeMeasureOn] using
    ((contDiff_euclideanCoordDeriv hψ i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordDeriv hψ_compact i)).restrict U

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

namespace H10Function

/-- A zero-trace `H¹` function may be integrated by parts against any smooth
compactly supported ambient test, without requiring the test support to lie
inside the domain. -/
theorem integral_mul_deriv_eq_neg_integral_mul_of_contDiff_hasCompactSupport
    {d : ℕ} {U : Set (Vec d)} (u : H10Function U) (i : Fin d)
    {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_compact : HasCompactSupport ψ) :
    ∫ x in U, u.toH1Function.toFun x * euclideanCoordDeriv i ψ x
        ∂MeasureTheory.volume =
      -∫ x in U, u.toH1Function.grad x i * ψ x
        ∂MeasureTheory.volume := by
  let Dψ : Vec d → ℝ := euclideanCoordDeriv i ψ
  let Dapprox : ℕ → Vec d → ℝ := fun n x =>
    euclideanCoordDeriv i (u.approx n) x
  have hψL2 : MemScalarL2 U ψ :=
    memScalarL2_of_contDiff_hasCompactSupport U hψ hψ_compact
  have hDψL2 : MemScalarL2 U Dψ :=
    memScalarL2_euclideanCoordDeriv_of_contDiff_hasCompactSupport
      U i hψ hψ_compact
  have happroxL2 : ∀ n, MemScalarL2 U (u.approx n) := by
    intro n
    exact memScalarL2_of_contDiff_hasCompactSupport
      U (u.approx_smooth n) (u.approx_hasCompactSupport n)
  have hDapproxL2 : ∀ n, MemScalarL2 U (Dapprox n) := by
    intro n
    exact memScalarL2_euclideanCoordDeriv_of_contDiff_hasCompactSupport
      U i (u.approx_smooth n) (u.approx_hasCompactSupport n)
  have happrox_to_u :
      Filter.Tendsto (fun n => toScalarL2 (happroxL2 n))
        Filter.atTop (nhds (toScalarL2 u.toH1Function.memL2)) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm
      (F := fun n => u.approx n) (G := u.toH1Function.toFun)
      happroxL2 u.toH1Function.memL2 u.tendsto_approx
  have hDapprox_to_grad :
      Filter.Tendsto (fun n => toScalarL2 (hDapproxL2 n))
        Filter.atTop (nhds (toScalarL2 (u.toH1Function.gradMemL2 i))) := by
    refine tendsto_toScalarL2_of_tendsto_eLpNorm
      (F := Dapprox) (G := fun x => u.toH1Function.grad x i)
      hDapproxL2 (u.toH1Function.gradMemL2 i) ?_
    simpa [Dapprox, euclideanCoordDeriv] using u.tendsto_approx_grad i
  have hleft :
      Filter.Tendsto
        (fun n => ∫ x in U, Dψ x * u.approx n x ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∫ x in U, Dψ x * u.toH1Function.toFun x ∂MeasureTheory.volume)) :=
    tendsto_integral_mul_of_tendsto_toScalarL2
      hDψL2 happroxL2 u.toH1Function.memL2 happrox_to_u
  have hright :
      Filter.Tendsto
        (fun n => -∫ x in U, ψ x * Dapprox n x ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (-∫ x in U, ψ x * u.toH1Function.grad x i
          ∂MeasureTheory.volume)) := by
    exact
      (tendsto_integral_mul_of_tendsto_toScalarL2
        hψL2 hDapproxL2 (u.toH1Function.gradMemL2 i)
        hDapprox_to_grad).neg
  have hseq :
      (fun n => ∫ x in U, Dψ x * u.approx n x ∂MeasureTheory.volume) =
        fun n => -∫ x in U, ψ x * Dapprox n x ∂MeasureTheory.volume := by
    funext n
    have hleft_zero :
        ∀ x, x ∉ U → u.approx n x * Dψ x = 0 := by
      intro x hx
      have hx_notin : x ∉ tsupport (u.approx n) :=
        fun hx' => hx (u.approx_support_subset n hx')
      simp [image_eq_zero_of_notMem_tsupport hx_notin]
    have hright_zero :
        ∀ x, x ∉ U → Dapprox n x * ψ x = 0 := by
      intro x hx
      have hx_notin : x ∉ tsupport (u.approx n) :=
        fun hx' => hx (u.approx_support_subset n hx')
      have hzero_eventually : u.approx n =ᶠ[nhds x] 0 :=
        (isClosed_tsupport (f := u.approx n)).isOpen_compl.eventually_mem
          hx_notin |>.mono
            (fun y hy => image_eq_zero_of_notMem_tsupport hy)
      rw [show Dapprox n x = 0 by
        simp [Dapprox, euclideanCoordDeriv,
          Filter.EventuallyEq.fderiv_eq hzero_eventually]]
      ring
    have hweakApprox :
        ∫ x in Set.univ, u.approx n x * Dψ x ∂MeasureTheory.volume =
          -∫ x in Set.univ, Dapprox n x * ψ x ∂MeasureTheory.volume := by
      have hweak :
          HasWeakPartialDerivOn Set.univ i (u.approx n) (Dapprox n) := by
        simpa [Dapprox, euclideanCoordDeriv] using
          HasWeakPartialDerivOn.of_contDiff
            (U := Set.univ) (i := i)
            ((u.approx_smooth n).of_le (by simp))
      simpa [Dψ, Dapprox, euclideanCoordDeriv] using
        hweak ψ hψ hψ_compact (by simp)
    calc
      ∫ x in U, Dψ x * u.approx n x ∂MeasureTheory.volume =
        ∫ x in U, u.approx n x * Dψ x ∂MeasureTheory.volume := by
          congr 1
          funext x
          ring
      _ = ∫ x in Set.univ, u.approx n x * Dψ x ∂MeasureTheory.volume := by
          rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero]
          simp
      _ = -∫ x in Set.univ, Dapprox n x * ψ x ∂MeasureTheory.volume :=
          hweakApprox
      _ = -∫ x in U, Dapprox n x * ψ x ∂MeasureTheory.volume := by
          rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero]
          simp
      _ = -∫ x in U, ψ x * Dapprox n x ∂MeasureTheory.volume := by
          congr 1
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun x => by ring)
  have hlimit :
      ∫ x in U, Dψ x * u.toH1Function.toFun x ∂MeasureTheory.volume =
        -∫ x in U, ψ x * u.toH1Function.grad x i
          ∂MeasureTheory.volume :=
    tendsto_nhds_unique (hleft.congr' (Filter.EventuallyEq.of_eq hseq)) hright
  calc
    ∫ x in U, u.toH1Function.toFun x * euclideanCoordDeriv i ψ x
        ∂MeasureTheory.volume =
      ∫ x in U, Dψ x * u.toH1Function.toFun x ∂MeasureTheory.volume := by
        congr 1
        funext x
        simp [Dψ]
        ring
    _ = -∫ x in U, ψ x * u.toH1Function.grad x i
        ∂MeasureTheory.volume := hlimit
    _ = -∫ x in U, u.toH1Function.grad x i * ψ x
        ∂MeasureTheory.volume := by
        congr 1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun x => by ring)

end H10Function

/-- Fold a parent scalar test back to the original cube with the sign needed
for the `i`th weak-gradient graph constraint of the Dirichlet odd reflection.

The coefficient is the product of the odd-reflection cell sign and the
coordinate fold sign. -/
def cubeDirichletOddReflectionFoldedParentCoordTest {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (φ : Vec d → ℝ) : Vec d → ℝ :=
  fun y =>
    ∑ choice : Fin d → Fin 3,
      (cubeDirichletOddReflectionCellSign choice *
        cubeFaceReflectionCellFoldSign choice i) *
        φ (cubeFaceReflectionCellFoldMap Q choice y)

/-- The signed coordinate-folded graph test is smooth when the parent test is
smooth. -/
theorem contDiff_cubeDirichletOddReflectionFoldedParentCoordTest {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (cubeDirichletOddReflectionFoldedParentCoordTest Q i φ) := by
  classical
  unfold cubeDirichletOddReflectionFoldedParentCoordTest
  exact
    ContDiff.sum fun choice _ =>
      contDiff_const.mul
        (contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ)

/-- The signed coordinate-folded graph test has compact support when the
parent test has compact support. -/
theorem hasCompactSupport_cubeDirichletOddReflectionFoldedParentCoordTest
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : HasCompactSupport φ) :
    HasCompactSupport
      (cubeDirichletOddReflectionFoldedParentCoordTest Q i φ) := by
  classical
  unfold cubeDirichletOddReflectionFoldedParentCoordTest
  simpa using
    hasCompactSupport_finset_sum (Finset.univ : Finset (Fin d → Fin 3))
      (fun choice y =>
        (cubeDirichletOddReflectionCellSign choice *
          cubeFaceReflectionCellFoldSign choice i) *
          φ (cubeFaceReflectionCellFoldMap Q choice y))
      (by
        intro choice _hchoice
        exact
          (hasCompactSupport_comp_cubeFaceReflectionCellFoldMap Q choice hφ).mul_left)

/-- Coordinate derivative of the signed coordinate-folded graph test.  The
coordinate fold sign squares away, leaving only the odd-reflection cell sign. -/
theorem euclideanCoordDeriv_cubeDirichletOddReflectionFoldedParentCoordTest
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    euclideanCoordDeriv i
        (cubeDirichletOddReflectionFoldedParentCoordTest Q i φ) x =
      ∑ choice : Fin d → Fin 3,
        cubeDirichletOddReflectionCellSign choice *
          euclideanCoordDeriv i φ
            (cubeFaceReflectionCellFoldMap Q choice x) := by
  classical
  unfold cubeDirichletOddReflectionFoldedParentCoordTest euclideanCoordDeriv
  rw [fderiv_fun_sum]
  · simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro choice _hchoice
    have hdiff :
        DifferentiableAt ℝ
          (fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)) x :=
      (contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ).differentiable
        (by simp) x
    rw [fderiv_const_mul hdiff]
    change
      (cubeDirichletOddReflectionCellSign choice *
          cubeFaceReflectionCellFoldSign choice i) *
        euclideanCoordDeriv i
          (fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)) x =
        cubeDirichletOddReflectionCellSign choice *
          euclideanCoordDeriv i φ
            (cubeFaceReflectionCellFoldMap Q choice x)
    rw [euclideanCoordDeriv_comp_cubeFaceReflectionCellFoldMap hφ Q choice i x]
    let s : ℝ := cubeDirichletOddReflectionCellSign choice
    let σ : ℝ := cubeFaceReflectionCellFoldSign choice i
    let a : ℝ :=
      euclideanCoordDeriv i φ (cubeFaceReflectionCellFoldMap Q choice x)
    change (s * σ) * (σ * a) = s * a
    calc
      (s * σ) * (σ * a) = s * ((σ * σ) * a) := by ring
      _ = s * (1 * a) := by
            rw [show σ * σ = 1 by
              simp [σ]]
      _ = s * a := by ring
  · intro choice _hchoice
    exact
      (contDiff_const.mul
        (contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ)).differentiable
        (by simp) x

namespace H10Function

/-- The zero-trace weak-gradient identity tested against the signed
coordinate-folded graph test, with the derivative expanded cellwise. -/
theorem integral_mul_cubeDirichletOddReflectionFoldedParentCoordTest_derivSum_eq_neg_integral_mul_originCube
    {d : ℕ} {m : ℤ}
    (u : H10Function (openCubeSet (originCube d m))) (i : Fin d)
    {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ) :
    ∫ y in openCubeSet (originCube d m),
        u.toH1Function.toFun y *
          (∑ choice : Fin d → Fin 3,
            cubeDirichletOddReflectionCellSign choice *
              euclideanCoordDeriv i φ
                (cubeFaceReflectionCellFoldMap (originCube d m) choice y))
        ∂MeasureTheory.volume =
      -∫ y in openCubeSet (originCube d m),
          u.toH1Function.grad y i *
            cubeDirichletOddReflectionFoldedParentCoordTest
              (originCube d m) i φ y
          ∂MeasureTheory.volume := by
  have hbase :=
    u.integral_mul_deriv_eq_neg_integral_mul_of_contDiff_hasCompactSupport
      i
      (contDiff_cubeDirichletOddReflectionFoldedParentCoordTest
        (originCube d m) i hφ)
      (hasCompactSupport_cubeDirichletOddReflectionFoldedParentCoordTest
        (originCube d m) i hφ_compact)
  convert hbase using 1
  refine MeasureTheory.setIntegral_congr_fun
    (measurableSet_openCubeSet (originCube d m)) ?_
  intro y _hy
  change u.toH1Function.toFun y *
      (∑ choice : Fin d → Fin 3,
        cubeDirichletOddReflectionCellSign choice *
          euclideanCoordDeriv i φ
            (cubeFaceReflectionCellFoldMap (originCube d m) choice y)) =
    u.toH1Function.toFun y *
      euclideanCoordDeriv i
        (cubeDirichletOddReflectionFoldedParentCoordTest
          (originCube d m) i φ) y
  rw [euclideanCoordDeriv_cubeDirichletOddReflectionFoldedParentCoordTest
    (Q := originCube d m) (i := i) (φ := φ) hφ y]

end H10Function

/-- Centered parent-cube form of the odd reflected scalar derivative
pairing. -/
theorem setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar_mul_deriv_eq_folded
    {d : ℕ} {m : ℤ} {F φ : Vec d → ℝ}
    (hF : MemScalarL2 (openCubeSet (originCube d m)) F)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (i : Fin d) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        cubeDirichletOddReflectionScalar (originCube d m) F x *
          euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
      ∫ y in openCubeSet (originCube d m),
        F y *
          (∑ choice : Fin d → Fin 3,
            cubeDirichletOddReflectionCellSign choice *
              euclideanCoordDeriv i φ
                (cubeFaceReflectionCellFoldMap (originCube d m) choice y))
          ∂MeasureTheory.volume := by
  rw [setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
    (m := m)
    (f := fun x =>
      cubeDirichletOddReflectionScalar (originCube d m) F x *
        euclideanCoordDeriv i φ x)]
  exact
    setIntegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar_mul_eq_folded
      (Q := originCube d m) (F := F)
      hF (contDiff_euclideanCoordDeriv hφ i)
      (hasCompactSupport_euclideanCoordDeriv hφ_compact i)

private theorem memScalarL2_comp_cellFoldMap_of_contDiff_hasCompactSupport
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_compact : HasCompactSupport ψ) :
    MemScalarL2 (openCubeSet Q)
      (fun y => ψ (cubeFaceReflectionCellFoldMap Q choice y)) := by
  have hcomp_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y => ψ (cubeFaceReflectionCellFoldMap Q choice y)) := by
    simpa using contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hψ
  have hcomp_compact :
      HasCompactSupport
        (fun y => ψ (cubeFaceReflectionCellFoldMap Q choice y)) := by
    simpa using hasCompactSupport_comp_cubeFaceReflectionCellFoldMap
      Q choice hψ_compact
  exact memScalarL2_of_contDiff_hasCompactSupport
    (openCubeSet Q) hcomp_smooth hcomp_compact

private theorem integrable_openCubeSet_cubeDirichletOddCellVectorCoordPairing
    {d : ℕ} {Q : TriadicCube d} {G : Vec d → Vec d}
    (choice : Fin d → Fin 3)
    (hG : MemVectorL2 (openCubeSet Q) G)
    {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (i : Fin d) :
    MeasureTheory.Integrable
      (fun y =>
        G y i *
          ((cubeDirichletOddReflectionCellSign choice *
              cubeFaceReflectionCellFoldSign choice i) *
            φ (cubeFaceReflectionCellFoldMap Q choice y)))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  have hGi : MemScalarL2 (openCubeSet Q) (fun y => G y i) :=
    memScalarL2_coord_of_memVectorL2 hG i
  have hφcomp :
      MemScalarL2 (openCubeSet Q)
        (fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)) :=
    memScalarL2_comp_cellFoldMap_of_contDiff_hasCompactSupport
      Q choice hφ hφ_compact
  exact hGi.integrable_mul
    (hφcomp.const_mul
      (cubeDirichletOddReflectionCellSign choice *
        cubeFaceReflectionCellFoldSign choice i))

/-- Change variables on one reflection cell in one coordinate of the
odd-reflected vector-field pairing. -/
theorem setIntegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionVectorField_coord_mul_eq
    {d : ℕ} {Q : TriadicCube d} {G : Vec d → Vec d} {φ : Vec d → ℝ}
    (choice : Fin d → Fin 3) (i : Fin d) :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (cubeDirichletOddReflectionVectorField Q G x) i * φ x
          ∂MeasureTheory.volume =
      ∫ y in openCubeSet Q,
        G y i *
          ((cubeDirichletOddReflectionCellSign choice *
              cubeFaceReflectionCellFoldSign choice i) *
            φ (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := by
  let T : Vec d → Vec d := cubeFaceReflectionCellFoldMap Q choice
  let L : Vec d →L[ℝ] Vec d := cubeFaceReflectionCellFoldLinear choice
  let s : ℝ := cubeDirichletOddReflectionCellSign choice
  let σ : ℝ := cubeFaceReflectionCellFoldSign choice i
  let g : Vec d → ℝ := fun y => G y i * ((s * σ) * φ (T y))
  calc
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (cubeDirichletOddReflectionVectorField Q G x) i * φ x
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        g (T x) ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
          intro x hx
          change
            (cubeDirichletOddReflectionVectorField Q G x) i * φ x =
              G (T x) i * ((s * σ) * φ (T (T x)))
          rw [cubeDirichletOddReflectionVectorField_eq_cellVectorField_of_mem_cellCube
            Q choice G hx]
          change (s • L (G (T x))) i * φ x =
            G (T x) i * ((s * σ) * φ (T (T x)))
          by_cases h1 : choice i = 1
          · simp [L, σ, cubeFaceReflectionCellFoldSign, h1, T,
              cubeFaceReflectionCellFoldMap_involutive Q choice x,
              mul_assoc, mul_comm]
          · simp [L, σ, cubeFaceReflectionCellFoldSign, h1, T,
              cubeFaceReflectionCellFoldMap_involutive Q choice x,
              mul_assoc, mul_comm]
    _ = ∫ y in openCubeSet Q,
        G y i *
          ((cubeDirichletOddReflectionCellSign choice *
              cubeFaceReflectionCellFoldSign choice i) *
            φ (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := by
          simpa [g, T, s, σ] using
            setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
              Q choice g

/-- The block pairing with one coordinate of the odd-reflected vector field is
the original-cube pairing against the signed coordinate-folded graph test. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField_coord_mul_eq_folded
    {d : ℕ} {Q : TriadicCube d} {G : Vec d → Vec d} {φ : Vec d → ℝ}
    (hG : MemVectorL2 (openCubeSet Q) G)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (i : Fin d) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        (cubeDirichletOddReflectionVectorField Q G x) i * φ x
          ∂MeasureTheory.volume =
      ∫ y in openCubeSet Q,
        G y i *
          cubeDirichletOddReflectionFoldedParentCoordTest Q i φ y
          ∂MeasureTheory.volume := by
  classical
  let f : Vec d → ℝ := fun x =>
    (cubeDirichletOddReflectionVectorField Q G x) i * φ x
  have hfCell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable f
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    let T : Vec d → Vec d := cubeFaceReflectionCellFoldMap Q choice
    let L : Vec d →L[ℝ] Vec d := cubeFaceReflectionCellFoldLinear choice
    let s : ℝ := cubeDirichletOddReflectionCellSign choice
    let σ : ℝ := cubeFaceReflectionCellFoldSign choice i
    let g : Vec d → ℝ := fun y => G y i * ((s * σ) * φ (T y))
    have hbase :
        MeasureTheory.Integrable g
          (MeasureTheory.volume.restrict (openCubeSet Q)) := by
      simpa [g, T, s, σ] using
        integrable_openCubeSet_cubeDirichletOddCellVectorCoordPairing
          (Q := Q) (G := G) choice hG hφ hφ_compact i
    have hcomp :
        MeasureTheory.Integrable (fun x => g (T x))
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) :=
      integrable_cubeFaceReflectionCellCube_comp_cellFoldMap
        (Q := Q) (choice := choice) (g := g) hbase
    refine hcomp.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))]
      with x hx
    change
      G (T x) i * ((s * σ) * φ (T (T x))) =
        (cubeDirichletOddReflectionVectorField Q G x) i * φ x
    rw [cubeDirichletOddReflectionVectorField_eq_cellVectorField_of_mem_cellCube
      Q choice G hx]
    change
      G (T x) i * ((s * σ) * φ (T (T x))) =
        (s • L (G (T x))) i * φ x
    by_cases h1 : choice i = 1
    · simp [L, σ, cubeFaceReflectionCellFoldSign, h1, T,
        cubeFaceReflectionCellFoldMap_involutive Q choice x,
        mul_assoc, mul_comm]
    · simp [L, σ, cubeFaceReflectionCellFoldSign, h1, T,
        cubeFaceReflectionCellFoldMap_involutive Q choice x,
        mul_assoc, mul_comm]
  calc
    ∫ x in cubeFaceReflectionBlockSet Q,
        (cubeDirichletOddReflectionVectorField Q G x) i * φ x
          ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q, f x ∂MeasureTheory.volume := rfl
    _ = ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            f x ∂MeasureTheory.volume := by
          exact setIntegral_cubeFaceReflectionBlockSet_cellCube Q f hfCell
    _ = ∑ choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q,
            G y i *
              ((cubeDirichletOddReflectionCellSign choice *
                  cubeFaceReflectionCellFoldSign choice i) *
                φ (cubeFaceReflectionCellFoldMap Q choice y))
            ∂MeasureTheory.volume := by
          apply Finset.sum_congr rfl
          intro choice _hchoice
          simpa [f] using
            setIntegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionVectorField_coord_mul_eq
              (Q := Q) (G := G) (φ := φ) choice i
    _ = ∫ y in openCubeSet Q,
        ∑ choice : Fin d → Fin 3,
          G y i *
            ((cubeDirichletOddReflectionCellSign choice *
                cubeFaceReflectionCellFoldSign choice i) *
              φ (cubeFaceReflectionCellFoldMap Q choice y))
        ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_finsetSum]
          intro choice _hchoice
          exact
            integrable_openCubeSet_cubeDirichletOddCellVectorCoordPairing
              (Q := Q) (G := G) choice hG hφ hφ_compact i
    _ = ∫ y in openCubeSet Q,
        G y i *
          cubeDirichletOddReflectionFoldedParentCoordTest Q i φ y
          ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet Q) ?_
          intro y _hy
          change
            (∑ choice : Fin d → Fin 3,
              G y i *
                ((cubeDirichletOddReflectionCellSign choice *
                    cubeFaceReflectionCellFoldSign choice i) *
                  φ (cubeFaceReflectionCellFoldMap Q choice y))) =
              G y i *
                (∑ choice : Fin d → Fin 3,
                  (cubeDirichletOddReflectionCellSign choice *
                    cubeFaceReflectionCellFoldSign choice i) *
                    φ (cubeFaceReflectionCellFoldMap Q choice y))
          rw [Finset.mul_sum]

/-- Centered parent-cube form of the reflected vector coordinate pairing. -/
theorem setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_coord_mul_eq_folded
    {d : ℕ} {m : ℤ} {G : Vec d → Vec d} {φ : Vec d → ℝ}
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (i : Fin d) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        (cubeDirichletOddReflectionVectorField (originCube d m) G x) i *
          φ x ∂MeasureTheory.volume =
      ∫ y in openCubeSet (originCube d m),
        G y i *
          cubeDirichletOddReflectionFoldedParentCoordTest
            (originCube d m) i φ y
          ∂MeasureTheory.volume := by
  rw [setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
    (m := m)
    (f := fun x =>
      (cubeDirichletOddReflectionVectorField (originCube d m) G x) i * φ x)]
  exact
    setIntegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField_coord_mul_eq_folded
      (Q := originCube d m) (G := G) (φ := φ) hG hφ hφ_compact i

/-- The all-face odd reflection of an origin-cube zero-trace `H¹` function
defines a point of the closed parent-cube weak-gradient graph. -/
theorem mem_h1GraphClosedSubmodule_cubeDirichletOddReflection_originCube
    {d : ℕ} {m : ℤ}
    (u : H10Function (openCubeSet (originCube d m)))
    (hscalar :
      MemScalarL2 (openCubeSet (originCube d (m + 1)))
        (cubeDirichletOddReflectionScalar (originCube d m)
          u.toH1Function.toFun))
    (hvector :
      MemVectorL2 (openCubeSet (originCube d (m + 1)))
        (cubeDirichletOddReflectionVectorField (originCube d m)
          (fun y => u.toH1Function.grad y))) :
    (toScalarL2 hscalar, toHilbertVectorL2OfVecField hvector) ∈
      h1GraphClosedSubmodule
        (U := openCubeSet (originCube d (m + 1))) := by
  rw [mem_h1GraphClosedSubmodule_iff]
  intro i φ
  let Q : TriadicCube d := originCube d m
  let Uparent : Set (Vec d) := openCubeSet (originCube d (m + 1))
  let fR : Vec d → ℝ :=
    cubeDirichletOddReflectionScalar Q u.toH1Function.toFun
  let GR : Vec d → Vec d :=
    cubeDirichletOddReflectionVectorField Q
      (fun y => u.toH1Function.grad y)
  have hrawScalar :
      ∫ x in Uparent,
          (toScalarL2 hscalar) x * φ.deriv i x ∂MeasureTheory.volume =
        ∫ x in Uparent,
          fR x * euclideanCoordDeriv i φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [coeFn_toScalarL2 hscalar] with x hx
    rw [hx]
    simp [H1WeakTestFunction.deriv, euclideanCoordDeriv, fR, Q]
  have hrawVector :
      ∫ x in Uparent,
          (toHilbertVectorL2OfVecField hvector) x i * φ x
            ∂MeasureTheory.volume =
        ∫ x in Uparent, GR x i * φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [coeFn_toHilbertVectorL2OfVecField hvector] with x hx
    rw [hx]
    simp [hilbertifyVecField, GR, Q]
  have hscalarFold :
      ∫ x in Uparent,
          fR x * euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
        ∫ y in openCubeSet Q,
          u.toH1Function.toFun y *
            (∑ choice : Fin d → Fin 3,
              cubeDirichletOddReflectionCellSign choice *
                euclideanCoordDeriv i φ
                  (cubeFaceReflectionCellFoldMap Q choice y))
            ∂MeasureTheory.volume := by
    simpa [Uparent, fR, Q] using
      setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar_mul_deriv_eq_folded
        (m := m) (F := u.toH1Function.toFun) (φ := φ)
        u.toH1Function.memL2 φ.smooth φ.compactSupport i
  have hvectorFold :
      ∫ x in Uparent, GR x i * φ x ∂MeasureTheory.volume =
        ∫ y in openCubeSet Q,
          u.toH1Function.grad y i *
            cubeDirichletOddReflectionFoldedParentCoordTest Q i φ y
            ∂MeasureTheory.volume := by
    have hG : MemVectorL2 (openCubeSet Q)
        (fun y => u.toH1Function.grad y) := by
      simpa [MemVectorL2, volumeMeasureOn, Q] using
        u.toH1Function.grad_memVectorL2
    simpa [Uparent, GR, Q] using
      setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_coord_mul_eq_folded
        (m := m) (G := fun y => u.toH1Function.grad y) (φ := φ)
        hG φ.smooth φ.compactSupport i
  have hweak :=
    u.integral_mul_cubeDirichletOddReflectionFoldedParentCoordTest_derivSum_eq_neg_integral_mul_originCube
      i φ.smooth φ.compactSupport
  calc
    h1WeakConstraintCLM
        (U := openCubeSet (originCube d (m + 1))) i φ
        (toScalarL2 hscalar, toHilbertVectorL2OfVecField hvector)
        =
      ∫ x in Uparent,
          (toScalarL2 hscalar) x * φ.deriv i x ∂MeasureTheory.volume +
        ∫ x in Uparent,
          (toHilbertVectorL2OfVecField hvector) x i * φ x
          ∂MeasureTheory.volume := by
          simpa [Uparent] using
            h1WeakConstraintCLM_apply_eq_integral
              (U := openCubeSet (originCube d (m + 1))) i φ
              (toScalarL2 hscalar, toHilbertVectorL2OfVecField hvector)
    _ =
      ∫ x in Uparent,
          fR x * euclideanCoordDeriv i φ x ∂MeasureTheory.volume +
        ∫ x in Uparent, GR x i * φ x ∂MeasureTheory.volume := by
          rw [hrawScalar, hrawVector]
    _ =
      ∫ y in openCubeSet Q,
          u.toH1Function.toFun y *
            (∑ choice : Fin d → Fin 3,
              cubeDirichletOddReflectionCellSign choice *
                euclideanCoordDeriv i φ
                  (cubeFaceReflectionCellFoldMap Q choice y))
            ∂MeasureTheory.volume +
        ∫ y in openCubeSet Q,
          u.toH1Function.grad y i *
            cubeDirichletOddReflectionFoldedParentCoordTest Q i φ y
            ∂MeasureTheory.volume := by
          rw [hscalarFold, hvectorFold]
    _ = 0 := by
          rw [hweak]
          ring

/-- Choose the parent `H¹` function whose exact representatives are the
all-face Dirichlet odd reflection and its reflected gradient. -/
theorem exists_h1Function_cubeDirichletOddReflectionParent_originCube
    {d : ℕ} {m : ℤ}
    (u : H10Function (openCubeSet (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
        cubeDirichletOddReflectionScalar (originCube d m)
          u.toH1Function.toFun ∧
      uP.grad =
        cubeDirichletOddReflectionVectorField (originCube d m)
          (fun y => u.toH1Function.grad y) := by
  have hscalar :
      MemScalarL2 (openCubeSet (originCube d (m + 1)))
        (cubeDirichletOddReflectionScalar (originCube d m)
          u.toH1Function.toFun) :=
    memScalarL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar
      (m := m) u.toH1Function.memL2
  have hG : MemVectorL2 (openCubeSet (originCube d m))
      (fun y => u.toH1Function.grad y) := by
    simpa [MemVectorL2, volumeMeasureOn] using
      u.toH1Function.grad_memVectorL2
  have hvector :
      MemVectorL2 (openCubeSet (originCube d (m + 1)))
        (cubeDirichletOddReflectionVectorField (originCube d m)
          (fun y => u.toH1Function.grad y)) :=
    memVectorL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField
      (m := m) hG
  have hz :=
    mem_h1GraphClosedSubmodule_cubeDirichletOddReflection_originCube
      u hscalar hvector
  exact
    exists_h1Function_of_toScalarL2_toHilbertVectorL2OfVecField_mem_h1GraphClosedSubmodule
      (U := openCubeSet (originCube d (m + 1)))
      hscalar hvector hz

namespace CubeDirichletWeakPoissonProblem

/-- The odd-reflected parent weak equation with the parent `H¹` realization
chosen by the closed graph construction. -/
theorem exists_cubeDirichletOddReflectionParent_weakPoissonEquationOn_originCube
    {d : ℕ} {m : ℤ} {u : H10Function (openCubeSet (originCube d m))}
    {F : Vec d → ℝ}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
        cubeDirichletOddReflectionScalar (originCube d m)
          u.toH1Function.toFun ∧
      uP.grad =
        cubeDirichletOddReflectionVectorField (originCube d m)
          (fun y => u.toH1Function.grad y) ∧
      WeakPoissonEquationOn (openCubeSet (originCube d (m + 1))) uP
        (cubeDirichletOddReflectionScalar (originCube d m) F) := by
  rcases exists_h1Function_cubeDirichletOddReflectionParent_originCube
      (m := m) u with
    ⟨uP, huP_fun, huP_grad⟩
  refine ⟨uP, huP_fun, huP_grad, ?_⟩
  exact
    hweak.cubeDirichletOddReflectionParent_weakPoissonEquationOn_originCube_of_grad_eq
      uP huP_grad hF

end CubeDirichletWeakPoissonProblem

end

end Homogenization
