/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketRestriction
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentPhysicalBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketCommonRadius

@[expose] public section

/-! Actual parent fields and the physical tangent growth estimate supply
the complete joined-packet input at one common radius. The history
Jacobi law, inverse coefficients and all coefficient matches are proved. -/

noncomputable section

namespace EulerParentPacketFrames

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerPacketParentLabelBounds EulerTimeIntervalRestriction EulerTransversePacketProvider
  EulerPacketSourcePropagator EulerVolterraConvolution EulerTransverseSourceCoefficientPath

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

structure JoinedInputs (M : EulerMeanPacketProvider.Data) (D : Data U)
    (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T) (H : HistoryData (D.initial τ hτ hτT.le)) where
  linear : EulerTransversePacketJoin.Budget D τ hτ hτT H (Fin 4) 6
  normal : EulerTransversePacketJoin.NormalBudget D 6 linear.R
  mean : EulerMeanPacketProvider.Budget M 6 linear.R

namespace Parent

variable (G : Parent) (H : LowBounds G)
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)

def historyOn : HistoryData ((G.transverseData m hm R S hS).initial τ hτ hτT.le) :=
  (G.historyData m hm R S hS H).initial τ hτ hτT.le

omit [CompleteSpace U] in
def secondInitial : SmoothCoefficientPath (Icc (0 : ℝ) τ) (Space →L[ℝ] Space) :=
  G.second.toSmoothCoefficientPath.comp (initialInclusion G.T τ hτT.le)

omit [CompleteSpace U] in
theorem secondInitial_derivative (t : ℝ) (ht : t ∈ Icc (0 : ℝ) τ) (x : Space) :
    HasDerivWithinAt
      (fun s => extendPath τ hτ.le ((G.transverseData m hm R S hS).initial τ hτ hτT.le).F₁.field s
        x)
      (extendPath τ hτ.le (G.secondInitial τ hτT).field t x) (Icc (0 : ℝ) τ) t :=
  initialPath_hasDerivWithinAt G.T τ G.T_pos.le hτ.le hτT.le
    (pathEvaluation x G.first.field) (pathEvaluation x G.second.field)
    (fun s hs => G.first_within s hs x) t ht

end Parent

namespace LabelData

variable {G : Parent} (L : LabelData G) (H : LowBounds G)
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (Ti Cp : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti) (hCp : 0 ≤ Cp)
  (g : C(Icc (0 : ℝ) (G.T-τ),ℝ)) (hg : ∀ t, 0 < g t)
  (hg0 : g ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩=1)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1/2 : ℝ))
  (hphysical : PhysicalGrowth ((G.transverseData m hm R S hS).tail τ hτ.le hτT)
    EulerPacketParentPhysicalBudgets.halfBall g Cp)

def joinedRaw : EulerTransversePacketJoin.Budget (G.transverseData m hm R S hS) τ hτ hτT
    (G.historyOn H m hm R S hS τ hτ hτT) (Fin 4) 6 :=
  EulerPacketParentPhysicalBudgets.joinedBudget (G.transverseData m hm R S hS) τ hτ hτT
    (G.historyOn H m hm R S hS τ hτ hτT) 6 L.displacement L.velocity
    (fun t => L.acceleration (initialInclusion G.T τ hτT.le t)) (G.secondInitial τ hτT)
    G.ell L.K Ti Cp G.ell_pos.le G.ell_le_one (zero_le_one.trans L.K_one) hτ1 hTi hCp
    L.displacement_bound L.velocity_bound
    (fun t => L.acceleration_bound (initialInclusion G.T τ hτT.le t))
    L.frame_match L.first_match (fun t x => L.second_match (initialInclusion G.T τ hτT.le t) x)
    (G.secondInitial_derivative m hm R S hS τ hτ hτT) G.frame_det
    g hg hg0 Ω hΩ hΩo hsub hΩball hphysical

def joinedInputs (TiTotal : ℝ) (hT1 : G.T ≤ 1) (hTiTotal : G.T⁻¹ ≤ TiTotal) :
    JoinedInputs (G.meanData H) (G.transverseData m hm R S hS) τ hτ hτT
      (G.historyOn H m hm R S hS τ hτ hτT) := by
  let A := L.joinedRaw H m hm R S hS τ hτ hτT Ti Cp hτ1 hTi hCp g hg hg0 Ω hΩ hΩo hsub hΩball
    hphysical
  let N := L.normalBudget m hm R S hS 6
  let M := L.meanBudget H 6 TiTotal hT1 hTiTotal
  let Rn := EulerPacketParentNormalBudget.radius (coefficientRadius L.K)
    (frameAmplitude L.K) (gradientAmplitude L.K)
  let Rm := EulerPacketParentMeanBudget.radius 6 G.T TiTotal (coefficientRadius L.K)
    (frameAmplitude L.K) (gradientAmplitude L.K) (gradientAmplitude L.K) H.L
  let Rc := max A.R (max Rn Rm)
  exact {
    linear := A.enlargeRadius Rc (le_max_left _ _)
    normal := N.enlargeRadius Rc ((le_max_left Rn Rm).trans (le_max_right _ _))
    mean := M.enlargeRadius Rc ((le_max_right Rn Rm).trans (le_max_right _ _)) }

end LabelData
end EulerParentPacketFrames
