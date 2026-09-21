/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Casts
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.Energy
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHS
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.GlobalIteration
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise
import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities
import LeanPool.CoarseGraining.Homogenization.PDE.NeumannRHS
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalCubeBridge

/-! # H1Transport -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public H1 transport bridges for Chapter 3

This file transports public H1, H10, mean-zero, and zero-trace data to the
deterministic half-open cube setting used by Chapter 3 engines.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- View a public open-domain `H¹` function as an `H¹` function on the
half-open triadic cube used by the deterministic layer. -/
noncomputable def publicH1ToCubeSet {d : ℕ} [NeZero d]
    {Q : TriadicCube d}
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    H1Function (cubeSet Q) :=
  (castH1Domain (Ch02.cubeDomain_coe Q) u).toCubeSet

@[simp] theorem publicH1ToCubeSet_grad {d : ℕ} [NeZero d]
    {Q : TriadicCube d}
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    (publicH1ToCubeSet u).grad = u.grad := by
  simp only [publicH1ToCubeSet]
  rw [H1Function.grad_toCubeSet]
  exact castH1Domain_grad _ u

@[simp] theorem publicH1ToCubeSet_toFun {d : ℕ} [NeZero d]
    {Q : TriadicCube d}
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    (publicH1ToCubeSet u).toFun = u.toFun := by
  simp only [publicH1ToCubeSet]
  rw [H1Function.toFun_toCubeSet]
  exact castH1Domain_toFun _ u

theorem publicH1ToCubeSet_grad_memVectorL2_descendant_cubeSet
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (hR : R ∈ descendantsAtDepth Q j) :
    MemVectorL2 (cubeSet R) u.grad := by
  have hmono :
      volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
        (cubeSet_subset_of_mem_descendantsAtDepth hR)
  simpa using (publicH1ToCubeSet u).grad_memVectorL2.mono_measure hmono

namespace H1MeanZeroFunction

/-- Promote a mean-zero `H¹` witness on an open triadic cube to the
corresponding half-open cube. -/
noncomputable def toCubeSet {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H1MeanZeroFunction (openCubeSet Q)) :
    H1MeanZeroFunction (cubeSet Q) :=
  { toH1Function := u.toH1Function.toCubeSet
    meanZero := by
      unfold MeanZeroOn
      have hset := setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q) (f := u.toH1Function.toFun)
      simpa using hset.trans u.meanZero }

@[simp] theorem toCubeSet_toH1Function_grad
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H1MeanZeroFunction (openCubeSet Q)) :
    (toCubeSet u).toH1Function.grad = u.toH1Function.grad := by
  simp [toCubeSet]

@[simp] theorem toCubeSet_toH1Function_toFun
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H1MeanZeroFunction (openCubeSet Q)) :
    (toCubeSet u).toH1Function.toFun = u.toH1Function.toFun := by
  simp [toCubeSet]

/-- Restrict a mean-zero `H¹` witness on a half-open triadic cube to its open
realization. -/
noncomputable def toOpenCubeSet {d : ℕ} {Q : TriadicCube d}
    (u : H1MeanZeroFunction (cubeSet Q)) :
    H1MeanZeroFunction (openCubeSet Q) :=
  { toH1Function := u.toH1Function.toOpenCubeSet
    meanZero := by
      unfold MeanZeroOn
      have hset := setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q) (f := u.toH1Function.toFun)
      simpa using hset.symm.trans u.meanZero }

@[simp] theorem toOpenCubeSet_toH1Function_grad
    {d : ℕ} {Q : TriadicCube d}
    (u : H1MeanZeroFunction (cubeSet Q)) :
    (toOpenCubeSet u).toH1Function.grad = u.toH1Function.grad := by
  simp [toOpenCubeSet]

@[simp] theorem toOpenCubeSet_toH1Function_toFun
    {d : ℕ} {Q : TriadicCube d}
    (u : H1MeanZeroFunction (cubeSet Q)) :
    (toOpenCubeSet u).toH1Function.toFun = u.toH1Function.toFun := by
  simp [toOpenCubeSet]

end H1MeanZeroFunction

/-- View a public open-domain mean-zero `H¹` function as a mean-zero `H¹`
function on the half-open triadic cube used by the deterministic layer. -/
noncomputable def publicH1MeanZeroToCubeSet {d : ℕ} [NeZero d]
    {Q : TriadicCube d}
    (u : H1MeanZeroFunction (Ch02.cubeDomain Q : Set (Vec d))) :
    H1MeanZeroFunction (cubeSet Q) :=
  H1MeanZeroFunction.toCubeSet
    (castH1MeanZeroDomain (Ch02.cubeDomain_coe Q) u)

@[simp] theorem publicH1MeanZeroToCubeSet_toH1Function_grad
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H1MeanZeroFunction (Ch02.cubeDomain Q : Set (Vec d))) :
    (publicH1MeanZeroToCubeSet u).toH1Function.grad =
      u.toH1Function.grad := by
  simp only [publicH1MeanZeroToCubeSet, H1MeanZeroFunction.toCubeSet]
  rw [H1Function.grad_toCubeSet]
  exact castH1MeanZeroDomain_toH1Function_grad _ u

@[simp] theorem publicH1MeanZeroToCubeSet_toH1Function_toFun
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H1MeanZeroFunction (Ch02.cubeDomain Q : Set (Vec d))) :
    (publicH1MeanZeroToCubeSet u).toH1Function.toFun =
      u.toH1Function.toFun := by
  simp only [publicH1MeanZeroToCubeSet, H1MeanZeroFunction.toCubeSet]
  rw [H1Function.toFun_toCubeSet]
  exact castH1MeanZeroDomain_toH1Function_toFun _ u

/-- View a public open-domain `H¹₀` function as an `H¹₀` function on the
half-open triadic cube used by the deterministic layer. -/
noncomputable def publicH10ToCubeSet {d : ℕ} [NeZero d]
    {Q : TriadicCube d}
    (u : H10Function (Ch02.cubeDomain Q : Set (Vec d))) :
    H10Function (cubeSet Q) :=
  (castH10Domain (Ch02.cubeDomain_coe Q) u).toCubeSet

@[simp] theorem publicH10ToCubeSet_toH1Function_grad {d : ℕ} [NeZero d]
    {Q : TriadicCube d}
    (u : H10Function (Ch02.cubeDomain Q : Set (Vec d))) :
    (publicH10ToCubeSet u).toH1Function.grad = u.toH1Function.grad := by
  simp only [publicH10ToCubeSet]
  rw [H10Function.toCubeSet_toH1Function_grad]
  exact castH10Domain_toH1Function_grad _ u

@[simp] theorem publicH10ToCubeSet_toH1Function_toFun {d : ℕ} [NeZero d]
    {Q : TriadicCube d}
    (u : H10Function (Ch02.cubeDomain Q : Set (Vec d))) :
    (publicH10ToCubeSet u).toH1Function.toFun = u.toH1Function.toFun := by
  simp only [publicH10ToCubeSet]
  rw [H10Function.toCubeSet_toH1Function_toFun]
  exact castH10Domain_toH1Function_toFun _ u

theorem publicH10ToCubeSet_toH1Function_grad_memVectorL2_descendant_cubeSet
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (u : H10Function (Ch02.cubeDomain Q : Set (Vec d)))
    (hR : R ∈ descendantsAtDepth Q j) :
    MemVectorL2 (cubeSet R) u.toH1Function.grad := by
  have hmono :
      volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
        (cubeSet_subset_of_mem_descendantsAtDepth hR)
  simpa using
    (publicH10ToCubeSet u).toH1Function.grad_memVectorL2.mono_measure hmono

/-- Chosen public zero-trace representative for the Dirichlet boundary
condition `v - h ∈ H¹₀(Q)`. -/
noncomputable def DirichletForcedCubeSolution.zeroTraceDifferenceH10
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    (u : DirichletForcedCubeSolution Q a g) :
    H10Function (Ch02.cubeDomain Q : Set (Vec d)) :=
  Classical.choose u.zeroTraceDifference

theorem DirichletForcedCubeSolution.zeroTraceDifferenceH10_toFun_ae_eq
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    (u : DirichletForcedCubeSolution Q a g) :
    u.zeroTraceDifferenceH10.toH1Function.toFun
      =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
        fun x => u.toH1.toFun x - u.boundaryData.toFun x :=
  Classical.choose_spec u.zeroTraceDifference

/-- The chosen public zero-trace representative, transported to the
deterministic half-open cube. -/
noncomputable def DirichletForcedCubeSolution.zeroTraceDifferenceH10CubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (u : DirichletForcedCubeSolution Q a g) :
    H10Function (cubeSet Q) :=
  publicH10ToCubeSet u.zeroTraceDifferenceH10

@[simp] theorem DirichletForcedCubeSolution.zeroTraceDifferenceH10CubeSet_grad
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (u : DirichletForcedCubeSolution Q a g) :
    u.zeroTraceDifferenceH10CubeSet.toH1Function.grad =
      u.zeroTraceDifferenceH10.toH1Function.grad := by
  simp [DirichletForcedCubeSolution.zeroTraceDifferenceH10CubeSet]

@[simp] theorem DirichletForcedCubeSolution.zeroTraceDifferenceH10CubeSet_toFun
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (u : DirichletForcedCubeSolution Q a g) :
    u.zeroTraceDifferenceH10CubeSet.toH1Function.toFun =
      u.zeroTraceDifferenceH10.toH1Function.toFun := by
  simp [DirichletForcedCubeSolution.zeroTraceDifferenceH10CubeSet]

/-- Zero-trace public test functions provide the deterministic
zero-trace-potential predicate on the corresponding half-open cube. -/
theorem isPotentialZeroTraceOn_cubeSet_of_publicH10Function
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H10Function (Ch02.cubeDomain Q : Set (Vec d))) :
    IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1Function.grad x) := by
  simpa using (publicH10ToCubeSet u).isPotentialZeroTraceOn

theorem ZeroTraceForcedCubeSolution.isPotentialZeroTraceOn_cubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (u : ZeroTraceForcedCubeSolution Q a g) :
    IsPotentialZeroTraceOn (cubeSet Q)
      (fun x => u.toH10.toH1Function.grad x) :=
  isPotentialZeroTraceOn_cubeSet_of_publicH10Function u.toH10

namespace HasWeakPartialDerivOn

/-- Weak partial derivatives are unique even when the underlying scalar
representatives agree only a.e. on the open domain. -/
theorem ae_eq_of_toFun_ae_eq {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {i : Fin d} {u v gi hi : Vec d → ℝ}
    (huv : u =ᵐ[MeasureTheory.volume.restrict U] v)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (hhiLoc : MeasureTheory.LocallyIntegrableOn hi U MeasureTheory.volume)
    (hgi : HasWeakPartialDerivOn U i u gi)
    (hhi : HasWeakPartialDerivOn U i v hi) :
    gi =ᵐ[MeasureTheory.volume.restrict U] hi := by
  refine HasWeakPartialDerivOn.ae_eq hU hgiLoc hhiLoc hgi ?_
  intro φ hφ_smooth hφ_compact hφ_sub
  calc
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      ∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume := by
        exact MeasureTheory.integral_congr_ae <|
          huv.mono fun x hx => by simp [hx]
    _ = -∫ x in U, hi x * φ x ∂MeasureTheory.volume :=
        hhi φ hφ_smooth hφ_compact hφ_sub

end HasWeakPartialDerivOn

namespace H1Function

/-- On an open domain, two `H¹` representatives with a.e.-equal values have
a.e.-equal weak gradients. -/
theorem grad_ae_eq_of_toFun_ae_eq {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {u v : H1Function U}
    (huv : u.toFun =ᵐ[MeasureTheory.volume.restrict U] v.toFun) :
    u.grad =ᵐ[MeasureTheory.volume.restrict U] v.grad := by
  have hcoord :
      ∀ i : Fin d,
        (fun x => u.grad x i) =ᵐ[MeasureTheory.volume.restrict U]
          fun x => v.grad x i := by
    intro i
    exact
      HasWeakPartialDerivOn.ae_eq_of_toFun_ae_eq hU huv
        (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
          ((u.gradMemL2 i).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)))
        (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
          ((v.gradMemL2 i).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)))
        (u.hasWeakGradient i) (v.hasWeakGradient i)
  have hall :
      ∀ᵐ x ∂MeasureTheory.volume.restrict U,
        ∀ i : Fin d, u.grad x i = v.grad x i :=
    MeasureTheory.ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx
  ext i
  exact hx i

end H1Function

theorem DirichletForcedCubeSolution.zeroTraceDifferenceH10CubeSet_grad_ae_eq
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (u : DirichletForcedCubeSolution Q a g) :
    u.zeroTraceDifferenceH10CubeSet.toH1Function.grad
      =ᵐ[volumeMeasureOn (cubeSet Q)]
        fun x => u.toH1.grad x - u.boundaryData.grad x := by
  let wOpen : H10Function (openCubeSet Q) :=
    castH10Domain (Ch02.cubeDomain_coe Q) u.zeroTraceDifferenceH10
  let zOpen : H1Function (openCubeSet Q) :=
    castH1Domain (Ch02.cubeDomain_coe Q) (u.toH1 - u.boundaryData)
  have hwOpen :
      wOpen.toH1Function.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)]
        zOpen.toFun := by
    show (castH10Domain (Ch02.cubeDomain_coe Q) u.zeroTraceDifferenceH10).toH1Function.toFun
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
          (castH1Domain (Ch02.cubeDomain_coe Q) (u.toH1 - u.boundaryData)).toFun
    rw [castH10Domain_toH1Function_toFun, castH1Domain_toFun, H1Function.sub_toFun,
      ← Ch02.cubeDomain_coe Q]
    exact u.zeroTraceDifferenceH10_toFun_ae_eq
  have hgradOpen :
      wOpen.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
        fun x => u.toH1.grad x - u.boundaryData.grad x := by
    have h :=
      H1Function.grad_ae_eq_of_toFun_ae_eq
        (isOpen_openCubeSet Q) (u := wOpen.toH1Function)
        (v := zOpen) hwOpen
    have ez : zOpen.grad = fun x => u.toH1.grad x - u.boundaryData.grad x := by
      show (castH1Domain (Ch02.cubeDomain_coe Q) (u.toH1 - u.boundaryData)).grad =
        fun x => u.toH1.grad x - u.boundaryData.grad x
      rw [castH1Domain_grad, H1Function.sub_grad]
    rw [ez] at h
    exact h
  have efun : u.zeroTraceDifferenceH10CubeSet.toH1Function.grad = wOpen.toH1Function.grad := by
    show (publicH10ToCubeSet u.zeroTraceDifferenceH10).toH1Function.grad =
      (castH10Domain (Ch02.cubeDomain_coe Q) u.zeroTraceDifferenceH10).toH1Function.grad
    rw [publicH10ToCubeSet_toH1Function_grad, castH10Domain_toH1Function_grad]
  have hmeas : volumeMeasureOn (cubeSet Q) = volumeMeasureOn (openCubeSet Q) :=
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  rw [efun, hmeas]
  exact hgradOpen

/-- Coefficient-energy split for a public Dirichlet solution:
`∇v = ∇(v - h) + ∇h` on the deterministic cube, with the zero-trace
representative chosen from the public boundary condition. -/
theorem DirichletForcedCubeSolution.cubeAverage_energy_le_two_mul_zeroTraceDifference_add_boundary
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (u : DirichletForcedCubeSolution Q a g) :
    cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q a) u.toH1.grad) ≤
      2 * cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (fun x => u.zeroTraceDifferenceH10CubeSet.toH1Function.grad x)) +
      2 * cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (dirichletBoundaryGradientField u)) := by
  let A : CoeffField d := publicCoeffField Q a
  let zgrad : Vec d → Vec d :=
    fun x => u.zeroTraceDifferenceH10CubeSet.toH1Function.grad x
  let hgrad : Vec d → Vec d := dirichletBoundaryGradientField u
  let hgradNeg : Vec d → Vec d := (-1 : ℝ) • hgrad
  have hEll : IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam (cubeSet Q) A :=
    publicCoeffField_isEllipticFieldOn_cubeSet Q a
  have hu_mem : MemVectorL2 (cubeSet Q) u.toH1.grad := by
    simpa [publicH1ToCubeSet_grad] using (publicH1ToCubeSet u.toH1).grad_memVectorL2
  have hz_mem : MemVectorL2 (cubeSet Q) zgrad := by
    simpa [zgrad] using u.zeroTraceDifferenceH10CubeSet.toH1Function.grad_memVectorL2
  have hh_mem : MemVectorL2 (cubeSet Q) hgrad := by
    simpa [hgrad, dirichletBoundaryGradientField, publicH1ToCubeSet_grad] using
      (publicH1ToCubeSet u.boundaryData).grad_memVectorL2
  have hhn_mem : MemVectorL2 (cubeSet Q) hgradNeg := by
    change MemVectorL2 (cubeSet Q) ((-1 : ℝ) • hgrad)
    exact hh_mem.const_smul (-1)
  have huEnergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A u.toH1.grad)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hu_mem
  have hzEnergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A zgrad)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hz_mem
  have hhnEnergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A hgradNeg)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hhn_mem
  have hmem :
      ∀ᵐ x ∂volumeMeasureOn (cubeSet Q), x ∈ cubeSet Q :=
    (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2
      (Filter.Eventually.of_forall fun _ hx => hx)
  have hgrad_ae :
      zgrad =ᵐ[volumeMeasureOn (cubeSet Q)] fun x => u.toH1.grad x - hgrad x := by
    simpa [zgrad, hgrad, dirichletBoundaryGradientField] using
      u.zeroTraceDifferenceH10CubeSet_grad_ae_eq
  have hpoint :
      ∀ᵐ x ∂volumeMeasureOn (cubeSet Q),
        coefficientEnergyDensity A u.toH1.grad x ≤
          2 * (coefficientEnergyDensity A zgrad x +
            coefficientEnergyDensity A hgradNeg x) := by
    filter_upwards [hmem, hgrad_ae] with x hx hz
    have hleft :
        coefficientEnergyDensity A u.toH1.grad x =
          coefficientEnergyDensity A (fun y => zgrad y - hgradNeg y) x := by
      have hvec : u.toH1.grad x = zgrad x - hgradNeg x := by
        rw [hz]
        simp [hgradNeg]
      unfold coefficientEnergyDensity
      rw [hvec]
    exact hleft.trans_le
      (coefficientEnergyDensity_sub_le_two_mul_add_of_isEllipticFieldOn
        hEll zgrad hgradNeg x hx)
  have havg_raw :
      cubeAverage Q (coefficientEnergyDensity A u.toH1.grad) ≤
        cubeAverage Q
          (fun x => 2 * (coefficientEnergyDensity A zgrad x +
            coefficientEnergyDensity A hgradNeg x)) := by
    unfold cubeAverage
    have hvol_inv_nonneg : 0 ≤ (cubeVolume Q)⁻¹ :=
      inv_nonneg.mpr (le_of_lt (cubeVolume_pos Q))
    refine mul_le_mul_of_nonneg_left ?_ hvol_inv_nonneg
    exact
      MeasureTheory.integral_mono_ae huEnergy_int
        ((hzEnergy_int.add hhnEnergy_int).const_mul (2 : ℝ)) hpoint
  have hsplit :
      cubeAverage Q
          (fun x => 2 * (coefficientEnergyDensity A zgrad x +
            coefficientEnergyDensity A hgradNeg x)) =
        2 * cubeAverage Q (coefficientEnergyDensity A zgrad) +
          2 * cubeAverage Q (coefficientEnergyDensity A hgradNeg) := by
    unfold cubeAverage
    have hfun :
        (fun x => 2 * (coefficientEnergyDensity A zgrad x +
            coefficientEnergyDensity A hgradNeg x)) =
          fun x => 2 * coefficientEnergyDensity A zgrad x +
            2 * coefficientEnergyDensity A hgradNeg x := by
      funext x
      ring
    rw [hfun, MeasureTheory.integral_add (hzEnergy_int.const_mul (2 : ℝ))
      (hhnEnergy_int.const_mul (2 : ℝ))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  have hneg_avg :
      cubeAverage Q (coefficientEnergyDensity A hgradNeg) =
        cubeAverage Q (coefficientEnergyDensity A hgrad) := by
    apply cubeAverage_eq_of_eq_on_cubeSet
    intro x _hx
    unfold coefficientEnergyDensity
    simp [hgradNeg, matVecMul_neg, vecDot_neg_left, vecDot_neg_right]
  calc
    cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q a) u.toH1.grad)
        ≤
      cubeAverage Q
        (fun x => 2 * (coefficientEnergyDensity A zgrad x +
          coefficientEnergyDensity A hgradNeg x)) := by
        simpa [A] using havg_raw
    _ =
      2 * cubeAverage Q (coefficientEnergyDensity A zgrad) +
        2 * cubeAverage Q (coefficientEnergyDensity A hgradNeg) := hsplit
    _ =
      2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => u.zeroTraceDifferenceH10CubeSet.toH1Function.grad x)) +
        2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (dirichletBoundaryGradientField u)) := by
        rw [hneg_avg]

/-- The public value-level zero-trace difference `u - v ∈ H¹₀` supplies the
deterministic zero-trace-potential predicate for the gradient difference. -/
theorem isPotentialZeroTraceOn_cubeSet_of_public_zeroTraceDifference
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    {u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    (hzero :
      ∃ w : H10Function (Ch02.cubeDomain Q : Set (Vec d)),
        w.toH1Function.toFun =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
          fun x => u.toFun x - v.toFun x) :
    IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x) := by
  rcases hzero with ⟨w, hw⟩
  let wOpen : H10Function (openCubeSet Q) :=
    castH10Domain (Ch02.cubeDomain_coe Q) w
  let zOpen : H1Function (openCubeSet Q) :=
    castH1Domain (Ch02.cubeDomain_coe Q) (u - v)
  have hwOpen :
      wOpen.toH1Function.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)]
        zOpen.toFun := by
    show (castH10Domain (Ch02.cubeDomain_coe Q) w).toH1Function.toFun
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
          (castH1Domain (Ch02.cubeDomain_coe Q) (u - v)).toFun
    rw [castH10Domain_toH1Function_toFun, castH1Domain_toFun, H1Function.sub_toFun,
      ← Ch02.cubeDomain_coe Q]
    exact hw
  have hgradOpen :
      wOpen.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
        fun x => u.grad x - v.grad x := by
    have h :=
      H1Function.grad_ae_eq_of_toFun_ae_eq
        (isOpen_openCubeSet Q) (u := wOpen.toH1Function)
        (v := zOpen) hwOpen
    have ez : zOpen.grad = fun x => u.grad x - v.grad x := by
      show (castH1Domain (Ch02.cubeDomain_coe Q) (u - v)).grad =
        fun x => u.grad x - v.grad x
      rw [castH1Domain_grad, H1Function.sub_grad]
    rw [ez] at h
    exact h
  exact
    isPotentialZeroTraceOn_cubeSet_triadicCube_of_openCubeSet
      (IsPotentialZeroTraceOn.congr_ae hgradOpen
        wOpen.isPotentialZeroTraceOn)

theorem HomogenizationComparisonDatum.isPotentialZeroTraceOn_cubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d}
    (w : HomogenizationComparisonDatum Q a a0) :
    IsPotentialZeroTraceOn (cubeSet Q)
      (fun x => w.u.grad x - w.v.grad x) :=
  isPotentialZeroTraceOn_cubeSet_of_public_zeroTraceDifference
    (Q := Q) (u := w.u) (v := w.v) w.zeroTraceDifference

theorem CoarseGrainingComparisonDatum.isPotentialZeroTraceOn_cubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d} {g : Vec d → Vec d}
    (w : CoarseGrainingComparisonDatum Q a a0 g) :
    IsPotentialZeroTraceOn (cubeSet Q)
      (fun x => w.u.grad x - w.v.grad x) :=
  isPotentialZeroTraceOn_cubeSet_of_public_zeroTraceDifference
    (Q := Q) (u := w.u) (v := w.v) w.zeroTraceDifference


end

end Ch03
end Book
end Homogenization
