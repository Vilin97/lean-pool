/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothBanachFlow
public import LeanPool.NavierStokesAndEuler.Euler.FinitePathTensor
import LeanPool.NavierStokesAndEuler.Euler.FinitePathTensorIntegral
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual time identities for all spatial jets of the constructed flow

The spatial derivative is taken in the full continuous-path Banach space.
The bounded time integral commutes with it at every order. Reassembling
the tensor paths therefore gives genuine within-time derivatives of all
jets, without assuming differentiability of an ODE solution family.
-/

@[expose] public section


noncomputable section


open scoped ContDiff BoundedContinuousFunction

namespace EulerSmoothBanachFlow

open Set EulerContinuousTimeIntegral EulerVolterraConvolution EulerFinitePathTensor

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)

/-- Velocity family, given by `A.superposition (pathFamily T hT A x)`. -/
def velocityFamily (x : E) : C(Icc (0 : ℝ) T,E) :=
  A.superposition (pathFamily T hT A x)

theorem velocityFamily_contDiff : ContDiff ℝ ∞ (velocityFamily T hT A) :=
  A.superposition_contDiff.comp (pathFamily_contDiff T hT A)

/-- Displacement family, given by `pathFamily T hT A x - (ContinuousLinearMap.const ℝ (Icc (0 :
ℝ) T)) x`. -/
def displacementFamily (x : E) : C(Icc (0 : ℝ) T,E) :=
  pathFamily T hT A x - (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) x

theorem displacementFamily_contDiff : ContDiff ℝ ∞ (displacementFamily T hT A) := by
  exact (pathFamily_contDiff T hT A).sub
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := E)
      (F := C(Icc (0 : ℝ) T,E)) (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)))

theorem displacementFamily_integral (x : E) :
    displacementFamily T hT A x = integral T hT (velocityFamily T hT A x) := by
  unfold displacementFamily velocityFamily
  exact sub_eq_iff_eq_add.mpr (by
    simpa only [add_comm] using pathFamily_integral T hT A x)

/-- Jet path, given by `tensorPathMap n (iteratedFDeriv ℝ n (pathFamily T hT A) x)`. -/
def jetPath (n : ℕ) (x : E) : C(Icc (0 : ℝ) T,E [×n]→L[ℝ] E) :=
  tensorPathMap n (iteratedFDeriv ℝ n (pathFamily T hT A) x)

/-- Velocity jet path, given by `tensorPathMap n (iteratedFDeriv ℝ n (velocityFamily T hT A)
x)`. -/
def velocityJetPath (n : ℕ) (x : E) : C(Icc (0 : ℝ) T,E [×n]→L[ℝ] E) :=
  tensorPathMap n (iteratedFDeriv ℝ n (velocityFamily T hT A) x)

/-- Displacement jet path, given by `tensorPathMap n (iteratedFDeriv ℝ n (displacementFamily T
hT A) x)`. -/
def displacementJetPath (n : ℕ) (x : E) : C(Icc (0 : ℝ) T,E [×n]→L[ℝ] E) :=
  tensorPathMap n (iteratedFDeriv ℝ n (displacementFamily T hT A) x)

theorem jetPath_apply (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    jetPath T hT A n x t = iteratedFDeriv ℝ n
      (fun y => (flowData T hT A).forward t y) x :=
  tensorPath_iteratedFDeriv _ (pathFamily_contDiff T hT A) n x t

theorem velocityJetPath_apply (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    velocityJetPath T hT A n x t = iteratedFDeriv ℝ n
      (fun y => A.field t ((flowData T hT A).forward t y)) x :=
  tensorPath_iteratedFDeriv _ (velocityFamily_contDiff T hT A) n x t

theorem displacementJetPath_integral (n : ℕ) (x : E) :
    displacementJetPath T hT A n x = integral T hT (velocityJetPath T hT A n x) := by
  have he : displacementFamily T hT A =
      (integral T hT) ∘ velocityFamily T hT A :=
    funext (displacementFamily_integral T hT A)
  unfold displacementJetPath
  rw [he, (integral T hT).iteratedFDeriv_comp_left
    (velocityFamily_contDiff T hT A).contDiffAt (by simp)]
  exact tensorPath_integral T hT n _

theorem displacementJetPath_hasDerivWithinAt (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (displacementJetPath T hT A n x))
      (velocityJetPath T hT A n x t) (Icc (0 : ℝ) T) t := by
  rw [displacementJetPath_integral]
  exact integral_hasDerivWithinAt T hT _ t

/-- The clamped extension is used only to state derivatives on the closed
time interval; there it is exactly the constructed flow minus its label. -/
def displacement (t : ℝ) (x : E) : E :=
  extendPath T hT (displacementFamily T hT A x) t

theorem displacement_eq (t : Icc (0 : ℝ) T) (x : E) :
    displacement T hT A t x = (flowData T hT A).forward t x - x := by
  simp only [displacement, extendPath, projIcc_of_mem hT t.property]
  rfl

theorem displacement_contDiff (t : ℝ) : ContDiff ℝ ∞ (displacement T hT A t) := by
  change ContDiff ℝ ∞ ((ContinuousMap.evalCLM ℝ (projIcc 0 T hT t)) ∘
    displacementFamily T hT A)
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T,E)) (F := E)
    (ContinuousMap.evalCLM ℝ (projIcc 0 T hT t))).comp
      (displacementFamily_contDiff T hT A)

theorem displacement_zero : displacement T hT A 0 = 0 := by
  funext x
  rw [show (0 : ℝ) = (⟨0,le_rfl,hT⟩ : Icc (0 : ℝ) T).val from rfl, displacement_eq]
  simp only [EulerBoundedLipschitzFlow.Data.forward_zero, sub_self, Pi.zero_apply]

theorem displacementJetPath_apply (n : ℕ) (x : E) (t : ℝ) :
    extendPath T hT (displacementJetPath T hT A n x) t =
      iteratedFDeriv ℝ n (displacement T hT A t) x :=
  tensorPath_iteratedFDeriv _ (displacementFamily_contDiff T hT A) n x (projIcc 0 T hT t)

theorem velocityJetPath_displacement (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    velocityJetPath T hT A n x t =
      iteratedFDeriv ℝ n (fun y => A.field t (y + displacement T hT A t y)) x := by
  rw [velocityJetPath_apply]
  congr 1
  funext y
  rw [displacement_eq]
  congr 1
  abel

/-- Every actual spatial tensor has the differentiated ODE as its genuine
time derivative, including one-sided derivatives at both endpoints. -/
theorem displacement_jet_hasDerivWithinAt (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => iteratedFDeriv ℝ n (displacement T hT A s) x)
      (iteratedFDeriv ℝ n (fun y => A.field t (y + displacement T hT A t y)) x)
      (Icc (0 : ℝ) T) t := by
  have he : (fun s => iteratedFDeriv ℝ n (displacement T hT A s) x) =
      extendPath T hT (displacementJetPath T hT A n x) :=
    funext (fun s => (displacementJetPath_apply T hT A n x s).symm)
  rw [he, ← velocityJetPath_displacement]
  exact displacementJetPath_hasDerivWithinAt T hT A n x t

theorem displacement_jet_continuous (n : ℕ) (x : E) :
    Continuous (fun t => iteratedFDeriv ℝ n (displacement T hT A t) x) := by
  have he : (fun t => iteratedFDeriv ℝ n (displacement T hT A t) x) =
      extendPath T hT (displacementJetPath T hT A n x) :=
    funext (fun t => (displacementJetPath_apply T hT A n x t).symm)
  rw [he]
  exact extendPath_continuous T hT _

theorem velocity_jet_continuous (n : ℕ) (x : E) :
    Continuous (fun t : Icc (0 : ℝ) T => iteratedFDeriv ℝ n
      (fun y => A.field t (y + displacement T hT A t y)) x) := by
  have he : (fun t : Icc (0 : ℝ) T => iteratedFDeriv ℝ n
      (fun y => A.field t (y + displacement T hT A t y)) x) =
      velocityJetPath T hT A n x :=
    funext (fun t => (velocityJetPath_displacement T hT A n x t).symm)
  rw [he]
  exact (velocityJetPath T hT A n x).continuous

end EulerSmoothBanachFlow
