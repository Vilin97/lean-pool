/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
public import LeanPool.CoarseGraining.Homogenization.Multiscale.CubeAverage
public import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities
public import LeanPool.CoarseGraining.Homogenization.PDE.Harmonic
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalCubeBridge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Realization

/-! # Correctors -/

@[expose] public section

namespace Homogenization

/-!
# Coarse Poincare with right-hand side

This file starts the deterministic Chapter-3 RHS development. The present pass
only packages the local zero-trace corrector surface on one triadic cube,
leaving the scale recurrence and iteration for downstream work.
-/

theorem isFiniteMeasureVolumeMeasureOnCubeSet_rhs {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) := by
  let U : Set (Vec d) := cubeSet Q
  let : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_cubeSet_lt_top Q⟩
  change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)
  infer_instance

instance instIsFiniteMeasureVolumeMeasureOnCubeSet_rhs {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
  isFiniteMeasureVolumeMeasureOnCubeSet_rhs Q

private theorem openCubeSet_nonempty_rhs {d : ℕ} (Q : TriadicCube d) :
    Set.Nonempty (openCubeSet Q) := by
  refine ⟨fun i => (Q.index i : ℝ) * cubeScaleFactor Q, ?_⟩
  intro i
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  constructor <;> nlinarith

/-- A local zero-trace corrector on one cube for the weak equation
`- div (a grad rho) = div g`. -/
structure ZeroTraceDirichletCorrectorData {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d) where
  toH10 : H10Function (cubeSet Q)
  weakSolution : IsZeroTraceDirichletRhsWeakSolution a (cubeSet Q) toH10 g

/-- Package a local zero-trace corrector on one cube from the abstract
Dirichlet RHS existence theorem. -/
private noncomputable def zeroTraceDirichletCorrectorDataOf_potentialZeroTraceClosureRealization
    {d : ℕ} (Q : TriadicCube d) {a : CoeffField d} {g : Vec d → Vec d}
    {lam Lam : ℝ} (hg : MemVectorL2 (cubeSet Q) g)
    (hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization (cubeSet Q))
    (hne : Set.Nonempty (cubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    ZeroTraceDirichletCorrectorData Q a g := by
  exact
    ⟨zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
        (a := a) (U := cubeSet Q) (g := g) (lam := lam) (Lam := Lam)
        hg hRealize hne hEll,
      isZeroTraceDirichletRhsWeakSolution_zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
        (a := a) (U := cubeSet Q) (g := g) (lam := lam) (Lam := Lam)
        hg hRealize hne hEll⟩

theorem isZeroTraceDirichletRhsWeakSolution_cubeSet_of_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} {u : H10Function (openCubeSet Q)}
    (hu : IsZeroTraceDirichletRhsWeakSolution a (openCubeSet Q) u g) :
    IsZeroTraceDirichletRhsWeakSolution a (cubeSet Q) u.toCubeSet g := by
  intro φ
  have hopen := hu φ.toOpenCubeSet
  have hleft :
      ∫ x in cubeSet Q,
          vecDot (matVecMul (a x) (u.toCubeSet.toH1Function.grad x))
            (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (matVecMul (a x) (u.toH1Function.grad x))
            (φ.toOpenCubeSet.toH1Function.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q)
        (f := fun x =>
          vecDot (matVecMul (a x) (u.toCubeSet.toH1Function.grad x))
            (φ.toH1Function.grad x)))
  have hright :
      ∫ x in cubeSet Q, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (g x) (φ.toOpenCubeSet.toH1Function.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q) (f := fun x => vecDot (g x) (φ.toH1Function.grad x)))
  calc
    ∫ x in cubeSet Q,
        vecDot (matVecMul (a x) (u.toCubeSet.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume
        =
          ∫ x in openCubeSet Q,
            vecDot (matVecMul (a x) (u.toH1Function.grad x))
              (φ.toOpenCubeSet.toH1Function.grad x) ∂MeasureTheory.volume := hleft
    _ =
          ∫ x in openCubeSet Q,
            vecDot (g x) (φ.toOpenCubeSet.toH1Function.grad x)
              ∂MeasureTheory.volume := hopen
    _ =
          ∫ x in cubeSet Q, vecDot (g x) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume := hright.symm

/-- Canonical local zero-trace corrector on the half-open cube, obtained by
solving the Dirichlet problem on the corresponding open cube and transporting
the weak formulation across the a.e.-equal cube realizations. -/
noncomputable def zeroTraceDirichletCorrectorDataOf_isEllipticFieldOn_cubeSet
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {a : CoeffField d}
    {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 (cubeSet Q) g)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    ZeroTraceDirichletCorrectorData Q a g := by
  have hgOpen : MemVectorL2 (openCubeSet Q) g := by
    simpa [MemVectorL2, volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      using hg
  have hRealizeOpen :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization (openCubeSet Q) :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q)
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    IsEllipticFieldOn.mono hEll (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  haveI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let uOpen : H10Function (openCubeSet Q) :=
    zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
      (a := a) (U := openCubeSet Q) (g := g) (lam := lam) (Lam := Lam)
      hgOpen hRealizeOpen (openCubeSet_nonempty_rhs Q) hEllOpen
  refine ⟨uOpen.toCubeSet, ?_⟩
  exact
    isZeroTraceDirichletRhsWeakSolution_cubeSet_of_openCubeSet
      (Q := Q) (a := a) (g := g) (u := uOpen)
      (isZeroTraceDirichletRhsWeakSolution_zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
        (a := a) (U := openCubeSet Q) (g := g) (lam := lam) (Lam := Lam)
        hgOpen hRealizeOpen (openCubeSet_nonempty_rhs Q) hEllOpen)

namespace ZeroTraceDirichletCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

theorem residualFlux_solenoidal
    {lam Lam : ℝ} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hmem : MemVectorL2 (cubeSet Q) g) :
    IsSolenoidalOn (cubeSet Q)
      (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x) - g x) := by
  intro φ
  have hflux_mem :
      MemVectorL2 (cubeSet Q)
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      ρ.toH10.toH1Function.grad_memVectorL2
  have hflux_int :
      MeasureTheory.IntegrableOn
        (fun x =>
          vecDot (matVecMul (a x) (ρ.toH10.toH1Function.grad x))
            (φ.toH1Function.grad x)) (cubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hflux_mem φ.toH1Function.grad_memVectorL2
  have hg_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (g x) (φ.toH1Function.grad x)) (cubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hmem φ.toH1Function.grad_memVectorL2
  have hfun :
      (fun x =>
          vecDot (matVecMul (a x) (ρ.toH10.toH1Function.grad x) - g x)
            (φ.toH1Function.grad x)) =
        fun x =>
          vecDot (matVecMul (a x) (ρ.toH10.toH1Function.grad x))
              (φ.toH1Function.grad x) -
            vecDot (g x) (φ.toH1Function.grad x) := by
    funext x
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  rw [hfun, MeasureTheory.integral_sub hflux_int hg_int, ρ.weakSolution φ]
  ring

theorem exists_aHarmonicRemainder_of_potential_solenoidal
    {lam Lam : ℝ} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d}
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hmem : MemVectorL2 (cubeSet Q) g) :
    ∃ w : AHarmonicFunction a (cubeSet Q),
      ∀ x ∈ cubeSet Q,
        u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x := by
  rcases hu_potential with ⟨v, hv⟩
  let wH1 : H1Function (cubeSet Q) := v - ρ.toH10.toH1Function
  have hρ_residual :=
    ρ.residualFlux_solenoidal hEll hmem
  have hu_mem : MemVectorL2 (cubeSet Q) u := by
    simpa [← hv] using v.grad_memVectorL2
  have hflux_u_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (u x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hu_mem
  have hres_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x) :=
    hflux_u_mem.sub hmem
  have hflux_ρ_mem :
      MemVectorL2 (cubeSet Q)
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      ρ.toH10.toH1Function.grad_memVectorL2
  have hρ_res_mem :
      MemVectorL2 (cubeSet Q)
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x) - g x) :=
    hflux_ρ_mem.sub hmem
  have hsol_sum :
      IsSolenoidalOn (cubeSet Q)
        ((fun x => matVecMul (a x) (u x) - g x) +
          (-1 : ℝ) •
            (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x) - g x)) :=
    isSolenoidalOn_add_of_memVectorL2 hres_mem (hρ_res_mem.const_smul (-1))
      hu_residual (isSolenoidalOn_smul hρ_residual (-1))
  have hsol :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (wH1.grad x)) := by
    convert hsol_sum using 1
    funext x
    ext i
    simp [wH1, hv, sub_eq_add_neg, matVecMul_add, matVecMul_neg, Pi.add_apply]
  let w : AHarmonicFunction a (cubeSet Q) :=
    { toH1 := wH1
      isHarmonic := ⟨wH1.isPotentialOn, hsol⟩ }
  refine ⟨w, ?_⟩
  intro x hx
  change u x = wH1.grad x + ρ.toH10.toH1Function.grad x
  simp [wH1, hv, sub_eq_add_neg]

/-- Descendant-cube form of the local harmonic-remainder construction. The
global PDE predicates on the parent half-open cube are restricted to `R` using
the Sobolev cube bridge, and then the existing one-cube corrector lemma is
applied on `R`. -/
theorem exists_aHarmonicRemainder_of_parent_potential_solenoidal
    [NeZero d] {R : TriadicCube d} {n : ℕ} {lam Lam : ℝ}
    (ρ : ZeroTraceDirichletCorrectorData R a g)
    {u : Vec d → Vec d}
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth Q n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g) :
    ∃ w : AHarmonicFunction a (cubeSet R),
      ∀ x ∈ cubeSet R,
        u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x := by
  have hu_potential_R :
      IsPotentialOn (cubeSet R) u :=
    hu_potential.restrict_cubeSet_of_mem_descendantsAtDepth hR
  have hflux_memR :
      MemVectorL2 (cubeSet R) (fun x => matVecMul (a x) (u x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllR hu_memR
  have hres_memR :
      MemVectorL2 (cubeSet R) (fun x => matVecMul (a x) (u x) - g x) :=
    hflux_memR.sub hg_memR
  have hu_residual_R :
      IsSolenoidalOn (cubeSet R) (fun x => matVecMul (a x) (u x) - g x) :=
    hu_residual.restrict_cubeSet_of_mem_descendantsAtDepth hR hres_memR
  exact
    ρ.exists_aHarmonicRemainder_of_potential_solenoidal
      hu_potential_R hu_residual_R hEllR hg_memR

/-- Fully constructed descendant-cube corrector and harmonic remainder from
parent potential/solenoidal PDE data. The zero-trace corrector is built on the
open cube and transported to the half-open cube, so callers no longer need a
separate realization hypothesis on `cubeSet R`. -/
theorem exists_corrector_aHarmonicRemainder_of_parent_potential_solenoidal
    [NeZero d] {R : TriadicCube d} {n : ℕ} {lam Lam : ℝ}
    {u : Vec d → Vec d}
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth Q n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g) :
    ∃ ρ : ZeroTraceDirichletCorrectorData R a g,
      ∃ w : AHarmonicFunction a (cubeSet R),
        ∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x := by
  let ρ : ZeroTraceDirichletCorrectorData R a g :=
    zeroTraceDirichletCorrectorDataOf_isEllipticFieldOn_cubeSet
      (Q := R) (a := a) (g := g) (lam := lam) (Lam := Lam) hg_memR hEllR
  rcases ρ.exists_aHarmonicRemainder_of_parent_potential_solenoidal
      (Q := Q) (u := u) hu_potential hu_residual hR hEllR hu_memR hg_memR with
    ⟨w, hw⟩
  exact ⟨ρ, w, hw⟩

end ZeroTraceDirichletCorrectorData

end Homogenization
