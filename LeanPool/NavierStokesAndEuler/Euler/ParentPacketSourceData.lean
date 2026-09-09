/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketFrames
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketData
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceEquations

@[expose] public section

/-! The actual parent label fields construct both source-provider data
records. Their coefficient agreement, inverses and time identities are
conclusions. Only the manuscript's scalar low-order guards remain inputs. -/

noncomputable section

namespace EulerParentPacketFrames

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerMeanBoundary EulerMeanSourceInverse EulerMeanHarmonic EulerVolterraConvolution
  EulerTransverseFrameCoordinates
open scoped ContDiff BoundedContinuousFunction

structure LowBounds (G : Parent) where
  Be : ℝ
  Bc : ℝ
  L : ℝ
  r : ℝ
  K : ℝ
  Be_nonneg : 0 ≤ Be
  Bc_nonneg : 0 ≤ Bc
  L_lower : boundaryLocalizationC1*Bc ≤ L
  r_nonneg : 0 ≤ r
  r_le_quarter : r ≤ 1/4
  K_nonneg : 0 ≤ K
  exterior_lower : ∀ x, r ≤ ‖G.ell • x‖ → ∀ v : Space,
    -Be*‖v‖^2 ≤ ⟪G.initialStrain.field x v,v⟫_ℝ
  core_lower : ∀ x, ‖G.ell • x‖ < r → ∀ v : Space,
    -Bc*‖v‖^2 ≤ ⟪G.initialStrain.field x v,v⟫_ℝ
  curvature_upper : ∀ t x v, ⟪G.curvature.field t x v,v⟫_ℝ ≤ K*‖v‖^2
  small : K*(G.T^2/2)+Be*G.T+boundaryLocalizationC2*Bc*r^3*G.T ≤ 1/2

namespace Parent

variable (G : Parent)

theorem frame_within (t : ℝ) (ht : t ∈ Icc (0 : ℝ) G.T) (x : Space) :
    HasDerivWithinAt (fun s => extendPath G.T G.T_pos.le G.frame.field s x)
      (extendPath G.T G.T_pos.le G.first.field t x) (Icc (0 : ℝ) G.T) t := by
  simpa only [extendPath,SmoothTimeField.realField,projIcc_of_mem G.T_pos.le ht]
    using G.frame_time ⟨t,ht⟩ x

theorem first_within (t : ℝ) (ht : t ∈ Icc (0 : ℝ) G.T) (x : Space) :
    HasDerivWithinAt (fun s => extendPath G.T G.T_pos.le G.first.field s x)
      (extendPath G.T G.T_pos.le G.second.field t x) (Icc (0 : ℝ) G.T) t := by
  simpa only [extendPath,SmoothTimeField.realField,projIcc_of_mem G.T_pos.le ht]
    using G.first_time ⟨t,ht⟩ x

def meanData (H : LowBounds G) : EulerMeanPacketProvider.Data where
  T := G.T
  T_pos := G.T_pos
  ℓ := G.ell
  ℓ_pos := G.ell_pos
  ℓ_le_one := G.ell_le_one
  F := G.frame.toSmoothCoefficientPath
  F₁ := G.first.toSmoothCoefficientPath
  F₂ := G.second.toSmoothCoefficientPath
  M := G.strain.toSmoothCoefficientPath
  H := G.curvature.toSmoothCoefficientPath
  FInv := G.inverse.field
  M0 := G.initialStrain
  Be := H.Be
  Bc := H.Bc
  L := H.L
  r := H.r
  K := H.K
  Be_nonneg := H.Be_nonneg
  Bc_nonneg := H.Bc_nonneg
  L_lower := H.L_lower
  r_nonneg := H.r_nonneg
  r_le_quarter := H.r_le_quarter
  K_nonneg := H.K_nonneg
  exterior_lower := H.exterior_lower
  core_lower := H.core_lower
  inverse_left := G.inverse_left
  inverse_right := G.inverse_right
  inverse_initial := G.inverse_initial
  derivative_initial _ := rfl
  frame_time := G.frame_within
  derivative_time := G.first_within
  second_equation := G.second_equation
  strain_equation := G.strain_equation
  curvature_upper := H.curvature_upper
  small := H.small

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)

def transverseData : EulerTransversePacketProvider.Data U where
  T := G.T
  T_pos := G.T_pos
  support := S
  support_compact := hS
  m₀ := m
  m₀_unit := hm
  R := R
  F := G.frame.toSmoothCoefficientPath
  F₁ := G.first.toSmoothCoefficientPath
  FInv := G.inverse.toSmoothCoefficientPath
  M := G.strain.toSmoothCoefficientPath
  inverse_left := G.inverse_left
  inverse_right := G.inverse_right
  frame_time := G.frame_within
  strain_equation := G.strain_equation

theorem sourceAgreement (H : LowBounds G) :
    EulerPacketCylinderField.SourceCoefficientAgreement (G.meanData H) (G.transverseData m hm R S
      hS) where
  inverse t x := by
    change G.inverse.field t x = G.inverse.field ((G.transverseData m hm R S hS).clamp t) x
    exact congrArg (fun s => G.inverse.field s x)
      ((G.transverseData m hm R S hS).clamp_coe t).symm
  strain t x := by
    change G.strain.field t x = G.strain.field ((G.transverseData m hm R S hS).clamp t) x
    exact congrArg (fun s => G.strain.field s x)
      ((G.transverseData m hm R S hS).clamp_coe t).symm

theorem history_small (H : LowBounds G) : H.K*(G.T^2/2) ≤ 1/2 := by
  have hB := mul_nonneg H.Be_nonneg G.T_pos.le
  have hR := mul_nonneg (mul_nonneg (mul_nonneg boundaryLocalizationC2_nonneg H.Bc_nonneg)
    (pow_nonneg H.r_nonneg 3)) G.T_pos.le
  linarith [H.small]

def historyData (H : LowBounds G) : EulerTransversePacketProvider.HistoryData (G.transverseData m
  hm R S hS) where
  H := G.curvature.toSmoothCoefficientPath
  jacobi t ht x := by
    have h := G.first_within t ht x
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      change -(G.curvature.field (projIcc 0 G.T G.T_pos.le t) x
        (G.frame.field (projIcc 0 G.T G.T_pos.le t) x v)) =
          G.second.field (projIcc 0 G.T G.T_pos.le t) x v
      rw [projIcc_of_mem G.T_pos.le ht]
      exact (G.second_equation ⟨t,ht⟩ x v).symm
    · rfl
  potential := H.K
  potential_nonneg := H.K_nonneg
  potential_bound := H.curvature_upper
  small := G.history_small H

end Parent
end EulerParentPacketFrames
