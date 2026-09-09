/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpFiniteTensorReconstruction
public import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.MeanPathSpatialRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldAlgebra

@[expose] public section

/-!
# Literal smooth L² fields from the actual solved translation orbit

All full spatial derivative tensors of the canonical representative are in
L². Their L² classes are reconstructed from the finitely many genuine strong
coordinate derivatives. A smooth orbit of a continuous-time path supplies
continuity of every tensor jet in time.
-/

noncomputable section

namespace EulerMeanSmoothRepresentative

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanClassicalWordBounds EulerParameterWordGevrey EulerLpFiniteTensor
  EulerMeanTimeContinuousTranslation
open scoped ContDiff

/-- The literal tensor-valued L² field assembled from actual strong derivatives. -/
def orbitTensorLp (u : L2) (n : ℕ) : Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space) :=
  tensorLpReassembly (volume : Measure Space) n (fun w => ordinaryWord direction u w)

theorem orbitTensorLp_ae (u : L2) (hu : SmoothOrbit u) (n : ℕ) :
    (orbitTensorLp u n : Space → (Space [×n]→L[ℝ] Space)) =ᵐ[volume]
      iteratedFDeriv ℝ n (representative u hu) := by
  apply tensorLpReassembly_eq_ae
  intro w
  exact ordinaryWord_ae direction u hu w

/-- Integrability of full tensors is proved, rather than added as an output hypothesis. -/
theorem representative_iteratedFDeriv_memLp (u : L2) (hu : SmoothOrbit u) (n : ℕ) :
    MemLp (iteratedFDeriv ℝ n (representative u hu)) 2 (volume : Measure Space) :=
  (Lp.memLp (orbitTensorLp u n)).ae_eq (orbitTensorLp_ae u hu n)

/-- A smooth translation orbit produces a genuine smooth spatial L² field. -/
def smoothL2Field (u : L2) (hu : SmoothOrbit u) : EulerLpTranslation.SmoothL2Field Space where
  field := representative u hu
  smooth := representative_smooth u hu
  integrable := representative_iteratedFDeriv_memLp u hu

@[simp] theorem smoothL2Field_field (u : L2) (hu : SmoothOrbit u) (x : Space) :
    (smoothL2Field u hu).field x = representative u hu x := rfl

@[simp] theorem smoothL2Field_toLp (u : L2) (hu : SmoothOrbit u) :
    (smoothL2Field u hu).toLp = u := by
  apply Lp.ext
  exact (smoothL2Field u hu).toLp_ae.trans (representative_ae u hu).symm

@[simp] theorem smoothL2Field_jetLp (u : L2) (hu : SmoothOrbit u) (n : ℕ) :
    (smoothL2Field u hu).jetLp n = orbitTensorLp u n := by
  apply Lp.ext
  exact ((smoothL2Field u hu).jetLp_ae n).trans (orbitTensorLp_ae u hu n).symm

/-- A finite coordinate family is all that the qualitative tensor reconstruction uses. -/
theorem orbitTensorLp_continuous {K : Type*} [TopologicalSpace K]
    (u : K → L2) (n : ℕ)
    (h : ∀ w : Fin n → Fin 3, Continuous (fun t => ordinaryWord direction (u t) w)) :
    Continuous (fun t => orbitTensorLp (u t) n) :=
  (tensorLpReassembly (V := Space) (volume : Measure Space) n).continuous.comp (continuous_pi h)

/-- Every literal tensor jet of the reconstructed path is continuous in L². -/
theorem smoothL2Field_path_jet_continuous (T : ℝ)
    (p : C(Icc (0 : ℝ) T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) (n : ℕ) :
    Continuous (fun t => (smoothL2Field (p t) (pathTranslation_evaluation_contDiff T p hp t)).jetLp
      n) := by
  simp only [smoothL2Field_jetLp]
  apply orbitTensorLp_continuous
  intro w
  let q : C(Icc (0 : ℝ) T,L2) :=
    iteratedFDeriv ℝ n (fun a : Space => pathTranslation T a p) 0 (fun i => direction (w i))
  have he : (fun t => ordinaryWord direction (p t) w) = q := by
    funext t
    unfold ordinaryWord wordDerivative
    rw [path_orbit_tensor_evaluation T p hp]
    rfl
  rw [he]
  exact q.continuous

end EulerMeanSmoothRepresentative
