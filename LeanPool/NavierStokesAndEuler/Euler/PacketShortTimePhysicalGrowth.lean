/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentForwardBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePropagator
import LeanPool.NavierStokesAndEuler.Euler.ShortTimeLinearGrowth
import Mathlib.Algebra.Order.Star.Real

/-! The source tangent equation is a reflection of the strain applied to
the velocity. Its actual norm is therefore unchanged by the normal factor.
A short interval controlled by the low strain norm supplies H3 with g=1. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourcePropagator

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerMeanCoefficients EulerPacketPiola EulerGevrey
open scoped ContDiff BoundedContinuousFunction

theorem normal_reflection_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m r : E) : ‖-r+(2*⟪m,r⟫_ℝ/‖m‖^2) • m‖ = ‖r‖ := by
  by_cases hm : m=0
  · simp only [hm,inner_zero_left,mul_zero,zero_div,smul_zero,add_zero,norm_neg]
  have hn : ‖m‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hm)
  have hh : ‖-r+(2*⟪m,r⟫_ℝ/‖m‖^2) • m‖^2 = ‖r‖^2 := by
    rw [norm_add_sq_real]
    simp only [norm_neg,inner_smul_right,inner_neg_left,norm_smul,
      Real.norm_eq_abs,mul_pow,sq_abs]
    rw [real_inner_comm r m]
    field_simp
    ring
  nlinarith [norm_nonneg (-r+(2*⟪m,r⟫_ℝ/‖m‖^2) • m),norm_nonneg r]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U)

omit [CompleteSpace U] in
theorem physicalRhs_norm (t : Icc (0 : ℝ) D.T) (x w : Space) :
    ‖physicalRhs D t x w‖ = ‖D.M.field t x w‖ :=
  normal_reflection_norm (D.normal.field t x) (D.M.field t x w)

omit [CompleteSpace U] in
/-- No inverse normal bound or all-order coefficient norm occurs in the
shortness condition. The derivative equation is required literally. -/
theorem physicalGrowth_one_of_short (S : Set Space) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ t : Icc (0 : ℝ) D.T, ∀ x ∈ S, ‖D.M.field t x‖ ≤ C)
    (hshort : C*D.T ≤ 1/2) : PhysicalGrowth D S (fun _ => 1) 2 := by
  intro x hx w hd _ t s hst
  let f' : ℝ → Space := fun r => physicalRhs D (projIcc 0 D.T D.T_pos.le r) x (w r)
  have hd' (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) :
      HasDerivWithinAt w (f' r) (Icc (0 : ℝ) D.T) r := by
    simpa only [f',projIcc_of_mem D.T_pos.le hr] using hd ⟨r,hr⟩
  have hb (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) : ‖f' r‖ ≤ C*‖w r‖ := by
    simp only [f',projIcc_of_mem D.T_pos.le hr,physicalRhs_norm]
    exact ((D.M.field ⟨r,hr⟩ x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hM ⟨r,hr⟩ x hx) (norm_nonneg _))
  simpa only [mul_one,div_one] using
    EulerShortTimeLinearGrowth.norm_le_two D.T C hC w f' hd' hb hshort s t hst

/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instPacketShortTimePhysicalGrowth1 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instPacketShortTimePhysicalGrowth2 : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

/-- A low strain bound on the H3 ball suffices for the entire source
forward budget. The coordinate propagation cost is the polynomial 6 C³. -/
def shortPhysicalForwardBudget (q : ℕ) (R C C₁ CM : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hCM : 0 ≤ CM)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C * majorant R
        0 n)
    (hF₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₁ *
        majorant
        R 0 n)
    (hM : ∀ t x, ‖x‖ ≤ (1 / 2 : ℝ) → ‖D.M.field t x‖ ≤ CM)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hsub : D.support ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
    (hshort : CM * D.T ≤ 1 / 2) :
    EulerTransversePacketForward.Budget D (Fin 4) q := by
  have hf (r : Icc (0 : ℝ) D.T) (y : Space) : ‖D.F.field r y‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hF 0 r y
  let S : Set Space := {x | ‖x‖ ≤ (1/2 : ℝ)}
  have hphysical : PhysicalGrowth D S (fun _ => 1) 2 :=
    physicalGrowth_one_of_short D S CM hCM hM hshort
  apply EulerPacketParentForwardBudget.sourceForwardBudget D q R C C₁ (6*C^3)
    hR hC hC₁ (by positivity) hdet hF hF₁ (1 : C(Icc (0 : ℝ) D.T,ℝ))
    (by intro t; norm_num) (by norm_num) Ω hΩ hΩo hsub hΩball
  intro t s hst x hx
  have hh := propagator_bound_of_deformation D S (fun _ => 1) (by intro r; norm_num)
    2 C (by norm_num) hC hphysical (fun r y _ => hdet r y) (fun r y _ => hf r y) t s hst x hx
  simpa only [ContinuousMap.one_apply,mul_one,div_one,propagator,fundamental,
    show 3*C^3*2=6*C^3 by ring] using hh

end EulerPacketSourcePropagator
