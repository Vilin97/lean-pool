/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.ForcedGalerkin
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinModeCalculus

/-! Linear coefficient transforms of forced finite-dimensional Galerkin paths. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology
open AVenhance.Infra.Parabolic.FourierGalerkin

namespace AVenhance.Infra.Classical

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The forcing generated when a fixed linear map is applied to a forced Galerkin path. -/
def ForcedGalerkinData.transformedForcing (D : ForcedGalerkinData E G)
    (L : E →L[ℝ] E) (y : ℝ → E) : ℝ → E :=
  fun t => L (D.forcing t) + L (D.weak.coefficient t (y t)) -
    D.weak.coefficient t (L (y t))

/-- Reuse the same weak operator and assign the transformed path its correct initial state and
commutator forcing. -/
def ForcedGalerkinData.linearTransform (D : ForcedGalerkinData E G)
    (L : E →L[ℝ] E) (y : ℝ → E)
    (hforcing : IntervalIntegrable (D.transformedForcing L y) volume 0 1) :
    ForcedGalerkinData E G :=
  { weak := D.weak
    initial := L D.initial
    forcing := D.transformedForcing L y
    forcing_integrable := hforcing }

/-- Apply a continuous linear map to a coefficient path. -/
def ForcedGalerkinData.mapPath (L : E →L[ℝ] E)
    (u : C(Icc (0 : ℝ) 1, E)) : C(Icc (0 : ℝ) 1, E) :=
  ⟨fun t => L (u t), L.continuous.comp u.continuous⟩

omit [CompleteSpace E] in
@[simp]
theorem ForcedGalerkinData.extendCurve_mapPath
    (L : E →L[ℝ] E)
    (u : C(Icc (0 : ℝ) 1, E)) :
    AVenhance.Infra.ODE.extendCurve (by norm_num)
      (ForcedGalerkinData.mapPath L u) =
      fun t => L (AVenhance.Infra.ODE.extendCurve (by norm_num) u t) := by
  funext t
  rfl

/-- A continuous linear transform of a forced Galerkin solution again solves the same weak
operator equation, with its commutator included in the forcing. -/
theorem ForcedGalerkinData.mapPath_isSolution
    (D : ForcedGalerkinData E G)
    (u : C(Icc (0 : ℝ) 1, E))
    (hu : D.ode.IsSolution u)
    (L : E →L[ℝ] E)
    (hforcing : IntervalIntegrable
      (D.transformedForcing L
        (AVenhance.Infra.ODE.extendCurve (by norm_num) u)) volume 0 1) :
    (D.linearTransform L
      (AVenhance.Infra.ODE.extendCurve (by norm_num) u) hforcing).ode.IsSolution
        (ForcedGalerkinData.mapPath L u) := by
  let y := AVenhance.Infra.ODE.extendCurve (by norm_num) u
  let D' := D.linearTransform L y hforcing
  have hsol := hu.integralSolution D.ode
  have hRhs : IntervalIntegrable
      (AVenhance.Infra.ODE.linearRhs D.weak.coefficient D.forcing y) volume 0 1 := by
    change IntervalIntegrable (D.ode.rhs u) volume 0 1
    exact D.ode.rhs_intervalIntegrable u
  have hmap := LinearIntegralSolution.continuousLinearMap_transform
    (hab := show (0 : ℝ) ≤ 1 by norm_num) hsol hRhs L
  have hext := ForcedGalerkinData.extendCurve_mapPath L u
  apply (D'.ode.isSolution_iff_integralSolution
    (ForcedGalerkinData.mapPath L u)).2
  intro t ht
  rw [hext]
  change L (y t) = L D.initial +
    ∫ s in 0..t, AVenhance.Infra.ODE.linearRhs D.weak.coefficient
      (D.transformedForcing L y) (fun s => L (y s)) s
  simpa only [ForcedGalerkinData.transformedForcing,
    AVenhance.Infra.ODE.linearRhs, ForcedGalerkinData.ode, y] using hmap t ht

/-- The commutator forcing produced by a continuous linear transform of a finite Galerkin path is
interval integrable. -/
theorem ForcedGalerkinData.transformedForcing_intervalIntegrable
    (D : ForcedGalerkinData E G)
    (u : C(Icc (0 : ℝ) 1, E)) (L : E →L[ℝ] E) :
    IntervalIntegrable
      (D.transformedForcing L (AVenhance.Infra.ODE.extendCurve (by norm_num) u))
      volume 0 1 := by
  let y := AVenhance.Infra.ODE.extendCurve (by norm_num) u
  let uL := ForcedGalerkinData.mapPath L u
  let yL := AVenhance.Infra.ODE.extendCurve (by norm_num) uL
  have hyL (t : ℝ) : yL t = L (y t) := by
    change AVenhance.Infra.ODE.extendCurve (by norm_num)
        (ForcedGalerkinData.mapPath L u) t =
      L (AVenhance.Infra.ODE.extendCurve (by norm_num) u t)
    rw [ForcedGalerkinData.extendCurve_mapPath]
  have hRhs := D.ode.rhs_intervalIntegrable u
  change IntervalIntegrable
    (AVenhance.Infra.ODE.linearRhs D.weak.coefficient D.forcing y) volume 0 1 at hRhs
  have hAy : IntervalIntegrable
      (fun t => D.weak.coefficient t (y t)) volume 0 1 := by
    simpa [AVenhance.Infra.ODE.linearRhs] using hRhs.sub D.forcing_integrable
  have hRhsL := D.ode.rhs_intervalIntegrable uL
  change IntervalIntegrable
    (AVenhance.Infra.ODE.linearRhs D.weak.coefficient D.forcing yL) volume 0 1 at hRhsL
  have hAyL : IntervalIntegrable
      (fun t => D.weak.coefficient t (L (y t))) volume 0 1 := by
    have hsub := hRhsL.sub D.forcing_integrable
    have hEq : (fun t => D.weak.coefficient t (yL t)) =
        fun t => D.weak.coefficient t (L (y t)) := by
      funext t
      rw [hyL]
    simpa [AVenhance.Infra.ODE.linearRhs, hEq] using hsub
  have hLf : IntervalIntegrable (fun t => L (D.forcing t)) volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact L.integrable_comp (intervalIntegrable_iff.mp D.forcing_integrable)
  have hLAy : IntervalIntegrable
      (fun t => L (D.weak.coefficient t (y t))) volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact L.integrable_comp (intervalIntegrable_iff.mp hAy)
  have hsum := (hLf.add hLAy).sub hAyL
  have hEq :
      (D.transformedForcing L y) =
        fun t => L (D.forcing t) + L (D.weak.coefficient t (y t)) -
          D.weak.coefficient t (L (y t)) := by
    rfl
  simpa [hEq, y] using hsum

/-- The forced Galerkin data and path obtained by differentiating every retained Fourier mode
along one ordered spatial derivative word. -/
def ForcedGalerkinData.wordDerivativeTransform {N : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (D : ForcedGalerkinData (Coefficients (RealFourierDimension N)) G)
    (u : C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N)))
    (w : List (Fin 2)) : ForcedGalerkinData (Coefficients (RealFourierDimension N)) G :=
  D.linearTransform (realFourierWordDerivativeMap N w)
    (AVenhance.Infra.ODE.extendCurve (by norm_num) u)
    (D.transformedForcing_intervalIntegrable u (realFourierWordDerivativeMap N w))

/-- The coefficient path obtained by differentiating a Galerkin path solves the transformed
forced system with the commutator included in its forcing. -/
theorem ForcedGalerkinData.wordDerivativeTransform_isSolution {N : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (D : ForcedGalerkinData (Coefficients (RealFourierDimension N)) G)
    (u : C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N)))
    (hu : D.ode.IsSolution u) (w : List (Fin 2)) :
    (D.wordDerivativeTransform u w).ode.IsSolution
      (ForcedGalerkinData.mapPath (realFourierWordDerivativeMap N w) u) := by
  exact D.mapPath_isSolution u hu (realFourierWordDerivativeMap N w)
    (D.transformedForcing_intervalIntegrable u (realFourierWordDerivativeMap N w))

end AVenhance.Infra.Classical

end
