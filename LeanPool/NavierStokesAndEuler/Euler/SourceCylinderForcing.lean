/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceForwardCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity

@[expose] public section

/-!
# Actual source forcing and physical velocity on cylinder L²

The projected forcing uses the constructed Gram left inverse. The physical
velocity uses the actual frame. Both preserve the closed spatial support,
actual mixed-orbit smoothness, and the external-word radius at fixed Hq.
-/

noncomputable section

namespace EulerSourceCylinderForcing

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerSourceForwardCoefficient EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerGevrey EulerParameterWordGevrey
  EulerTimeLpGramGevrey EulerTransverseForwardCoefficientGevrey
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {K U E ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (S : Set Space) (hS : MeasurableSet S)
  (Q : SmoothCoefficientPath K (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)

/-- The actual projected forcing on the supported cylinder. -/
def projectedForcing (f : C(K,Supported period E S hS)) : C(K,Supported period U S hS) :=
  supportedMultiplierMap period S hS (sourceForcing Q c hc hQ) f

/-- The actual physical velocity associated with the coordinate field. -/
def physicalVelocity (u : C(K,Supported period U S hS)) : C(K,Supported period E S hS) :=
  supportedMultiplierMap period S hS Q.field u

theorem projectedForcing_contDiff (f : C(K,Supported period E S hS))
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
      :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a
      (includePath period S hS (projectedForcing period S hS Q c hc hQ f))) :=
  supported_product_orbit_contDiff period (sourceForcing Q c hc hQ)
    (sourceForcing_translation_contDiff Q c hc hQ) S hS f hf

omit [CompleteSpace U] [CompleteSpace E] in
theorem physicalVelocity_contDiff (u : C(K,Supported period U S hS))
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS u)))
      :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a
      (includePath period S hS (physicalVelocity period S hS Q u))) :=
  supported_product_orbit_contDiff period Q.field Q.translation_contDiff S hS u hu

/-- The source forcing multiplication costs an explicit coefficient polynomial,
with no change to the forcing's radius or shift. -/
theorem projectedForcing_block_bound
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (f : C(K,Supported period E S hS))
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
    (Rc C Ri R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hRi : 2*gramCost c C 1*(Rc+1) ≤ Ri)
    (hR : sobolevCoefficientRadius ι (4*Ri) ≤ R)
    (hbQ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q.field t : Space → U →L[ℝ] E) x‖ ≤ C*majorant Rc 0 n)
    (d : ℕ) (hbf : ∀ n, block directions q
      (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)) n 0 ≤ D*majorant
        R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate period a
      (includePath period S hS (projectedForcing period S hS Q c hc hQ f))) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q (4*Ri) (3*Ri*C)*D)*majorant R d n := by
  obtain ⟨hRi₀,-⟩ := inverseRadius_bounds c C Rc Ri hc hRc hRi
  change block directions q (fun a : LiftTangent => pathTranslate period a
    (includePath period S hS (supportedMultiplierMap period S hS (sourceForcing Q c hc hQ) f))) n 0
      ≤ _
  rw [include_supportedMultiplier]
  exact product_orbit_block_bound period (sourceForcing Q c hc hQ)
    (sourceForcing_translation_contDiff Q c hc hQ) directions hd q (includePath period S hS f) hf
    (4*Ri) (3*Ri*C) R D (by positivity) (by positivity) hD hR
    (sourceForcing_translation_bound Q c hc hQ Rc C Ri hRc hC hRi hbQ) d hbf n

omit [CompleteSpace U] [CompleteSpace E] in
/-- Reconstruction by the physical frame also preserves the same external radius. -/
theorem physicalVelocity_block_bound
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (u : C(K,Supported period U S hS))
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS u)))
    (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbQ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q.field t : Space → U →L[ℝ] E) x‖ ≤ C*majorant Rc 0 n)
    (d : ℕ) (hbu : ∀ n, block directions q
      (fun a : LiftTangent => pathTranslate period a (includePath period S hS u)) n 0 ≤ D*majorant
        R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate period a
      (includePath period S hS (physicalVelocity period S hS Q u))) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C*D)*majorant R d n := by
  change block directions q (fun a : LiftTangent => pathTranslate period a
    (includePath period S hS (supportedMultiplierMap period S hS Q.field u))) n 0 ≤ _
  rw [include_supportedMultiplier]
  exact product_orbit_block_bound period Q.field Q.translation_contDiff directions hd q
    (includePath period S hS u) hu Rc C R D hRc hC hD hR
    (fun j a => Q.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC (majorant_nonneg Rc hRc 0 j)) (hbQ j) a) d hbu n

end EulerSourceCylinderForcing
