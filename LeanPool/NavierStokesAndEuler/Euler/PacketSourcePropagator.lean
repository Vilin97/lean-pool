/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceForwardCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.LinearFundamentalPath
public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
import LeanPool.NavierStokesAndEuler.Euler.LpSupportedConstructedEvolution
import LeanPool.NavierStokesAndEuler.Euler.PacketCofactorOperator
import LeanPool.NavierStokesAndEuler.Euler.TransverseNormalResidual

/-! The constructed source coordinate propagator is an actual physical
tangent solution after multiplication by F R.  Consequently a physical
propagator estimate supplies H3 with only the explicit F and F⁻¹ factors,
preserving exactly the time-profile ratio. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourcePropagator

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerMeanCoefficients EulerTransversePacketProvider EulerSourceForwardCoefficient
  EulerLinearFundamentalExistence EulerLpSupportedConstructedEvolution
  EulerVolterraConvolution EulerTransverseGramInverse EulerTransverseNormalResidual
  EulerPacketCofactor EulerPacketPiola
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Cache the standard `NormedSpace ℝ U` instance to shorten typeclass synthesis. -/
local instance instPacketSourcePropagator1 : NormedSpace ℝ U := inferInstance
/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instPacketSourcePropagator2 : NormedAddCommGroup Space := inferInstance
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instPacketSourcePropagator3 : NormedSpace ℝ Space := inferInstance
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketSourcePropagator4 : NormedAddCommGroup (U →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] Space)` instance to shorten typeclass synthesis. -/
local instance instPacketSourcePropagator5 : NormedSpace ℝ (U →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instPacketSourcePropagator6 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAlgebra ℝ (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instPacketSourcePropagator7 : NormedAlgebra ℝ (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instPacketSourcePropagator8 : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAlgebra ℝ (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instPacketSourcePropagator9 : NormedAlgebra ℝ (Space →ᵇ U →L[ℝ] U) := inferInstance

variable (D : Data U)

/-- Fundamental: an abbreviation for `fundamentalPath D.T D.T_pos.le (sourceGenerator D.frame
D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower)`. -/
abbrev fundamental := fundamentalPath D.T D.T_pos.le
  (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower)

/-- Propagator, given by `((fundamental D).forward t x).comp ((fundamental D).backward s x)`. -/
def propagator (t s : Icc (0 : ℝ) D.T) (x : Space) : U →L[ℝ] U :=
  ((fundamental D).forward t x).comp ((fundamental D).backward s x)

/-- Coordinate, given by `extendPath D.T D.T_pos.le (fundamental D).forward t x ((fundamental
D).backward s x v)`. -/
def coordinate (s : Icc (0 : ℝ) D.T) (x : Space) (v : U) (t : ℝ) : U :=
  extendPath D.T D.T_pos.le (fundamental D).forward t x ((fundamental D).backward s x v)

/-- Physical, given by `extendPath D.T D.T_pos.le D.frame.field t x (coordinate D s x v t)`. -/
def physical (s : Icc (0 : ℝ) D.T) (x : Space) (v : U) (t : ℝ) : Space :=
  extendPath D.T D.T_pos.le D.frame.field t x (coordinate D s x v t)

/-- Physical rhs, given by `-(D.M.field t x) w + (2*⟪D.normal.field t x,(D.M.field t x)
w⟫_ℝ/‖D.normal.field t x‖^2) • D.normal.field t x`. -/
def physicalRhs (t : Icc (0 : ℝ) D.T) (x w : Space) : Space :=
  -(D.M.field t x) w +
    (2*⟪D.normal.field t x,(D.M.field t x) w⟫_ℝ/‖D.normal.field t x‖^2) • D.normal.field t x

@[simp] theorem coordinate_at (s t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    coordinate D s x v t = propagator D t s x v := by
  simp only [coordinate,propagator,extendPath,projIcc_of_mem D.T_pos.le t.property,comp_apply]

@[simp] theorem physical_at (s t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    physical D s x v t = D.frame.field t x (propagator D t s x v) := by
  simp only [physical,coordinate_at,extendPath,projIcc_of_mem D.T_pos.le t.property]

@[simp] theorem propagator_self (s : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    propagator D s s x v = v := by
  have h := congrArg (fun A : Space →ᵇ U →L[ℝ] U => A x v) ((fundamental D).forward_backward s)
  exact h

theorem physical_tangent (s t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    ⟪D.normal.field t x,physical D s x v t⟫_ℝ = 0 := by
  rw [physical_at]
  exact D.frame_tangent t x _

theorem coordinate_hasDerivWithinAt (s t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    HasDerivWithinAt (coordinate D s x v)
      (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower t x
        (coordinate D s x v t)) (Icc (0 : ℝ) D.T) t := by
  have hd := fundamental_pointwise_derivative D.T D.T_pos.le
    (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower)
    t t.property x
  have ha := hd.clm_apply (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) D.T)
    ((fundamental D).backward s x v))
  simp only [extendPath,projIcc_of_mem D.T_pos.le t.property,map_zero,add_zero,comp_apply] at ha
  convert ha using 1
  · rfl
  · simp only [coordinate,extendPath,projIcc_of_mem D.T_pos.le t.property]

theorem physical_hasDerivWithinAt (s t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    HasDerivWithinAt (physical D s x v) (physicalRhs D t x (physical D s x v t))
      (Icc (0 : ℝ) D.T) t := by
  let a := coordinate D s x v t
  let b := sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower t
      x a
  have hd : HasDerivWithinAt (physical D s x v)
      (D.frameDerivative.field t x a+D.frame.field t x b) (Icc (0 : ℝ) D.T) t := by
    have hp := (D.frame_derivative t t.property x).clm_apply (coordinate_hasDerivWithinAt D s t x v)
    simp only [extendPath,projIcc_of_mem D.T_pos.le t.property] at hp
    convert hp using 1
    all_goals rfl
  have hnormal : D.normal.field t x ≠ 0 := by
    intro hz
    have hn := D.normal_lower t x
    rw [hz,norm_zero,zero_pow (by omega : 2 ≠ 0)] at hn
    exact (not_le_of_gt D.normalLower_pos) hn
  have he : gram (D.frame.field t x) b =
      (D.frame.field t x).adjoint (0-(2 : ℝ) • D.frameDerivative.field t x a) := by
    change gram (D.frame.field t x) ((-2 : ℝ) •
      gramInverse (D.frame.field t x) D.frameLower D.frameLower_pos (D.frame_lower t x)
        ((D.frame.field t x).adjoint (D.frameDerivative.field t x a))) = _
    rw [map_smul,gram_inverse_apply,map_sub,map_zero,map_smul]
    module
  have hb := physical_velocity_balance (D.frame.field t x) (D.frameDerivative.field t x)
    (D.M.field t x) (D.normal.field t x) hnormal (D.frame_tangent t x) (D.frame_range t x)
    (D.frame_strain t x) a b 0 he
  have hv : physical D s x v t = D.frame.field t x a := by
    simp only [physical,extendPath,projIcc_of_mem D.T_pos.le t.property,a]
  apply hd.congr_deriv
  rw [physicalRhs,hv]
  simp only [inner_zero_right,zero_sub,neg_div,neg_smul] at hb
  linear_combination (norm := module) hb

/-- A physical growth assertion is tested only on genuine solutions of
the literal tangent ODE, with the actual transported normal. -/
def PhysicalGrowth (S : Set Space) (g : Icc (0 : ℝ) D.T → ℝ) (C : ℝ) : Prop :=
  ∀ x ∈ S, ∀ w : ℝ → Space,
    (∀ t : Icc (0 : ℝ) D.T, HasDerivWithinAt w (physicalRhs D t x (w t)) (Icc (0 : ℝ) D.T) t) →
    ⟪D.normal.field ⟨0,le_rfl,D.T_pos.le⟩ x,w 0⟫_ℝ = 0 →
    ∀ t s : Icc (0 : ℝ) D.T, s ≤ t → ‖w t‖ ≤ C*g t/g s*‖w s‖

/-- Coordinate norms cost precisely the inverse deformation at the final
time and deformation at the initial time.  No extremum of g is used. -/
theorem propagator_bound_of_physical (S : Set Space)
    (g : Icc (0 : ℝ) D.T → ℝ) (hg : ∀ t, 0 < g t)
    (C F I : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F) (hI : 0 ≤ I)
    (hphysical : PhysicalGrowth D S g C)
    (hframe : ∀ t x, x ∈ S → ‖D.F.field t x‖ ≤ F)
    (hinverse : ∀ t x, x ∈ S → ‖D.FInv.field t x‖ ≤ I)
    (t s : Icc (0 : ℝ) D.T) (hst : s ≤ t) (x : Space) (hx : x ∈ S) :
    ‖propagator D t s x‖ ≤ (I*C*F)*g t/g s := by
  have hr : 0 ≤ C*g t/g s := div_nonneg (mul_nonneg hC (hg t).le) (hg s).le
  apply (propagator D t s x).opNorm_le_bound
    (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hI hC) hF) (hg t).le) (hg s).le)
  intro v
  have hp := hphysical x hx (physical D s x v) (fun r => physical_hasDerivWithinAt D s r x v)
    (physical_tangent D s ⟨0,le_rfl,D.T_pos.le⟩ x v) t s hst
  have hf : ‖physical D s x v s‖ ≤ F*‖v‖ := by
    rw [physical_at,propagator_self]
    change ‖D.F.field s x (D.R v : Space)‖ ≤ _
    have hRv : ‖(D.R v : Space)‖ = ‖v‖ := D.R.norm_map v
    exact ((D.F.field s x).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (hframe s x hx) (norm_nonneg (D.R v : Space))).trans_eq
        (congrArg (fun r => F*r) hRv))
  have hi : ‖propagator D t s x v‖ ≤ I*‖physical D s x v t‖ := by
    calc
      _ = ‖(D.R (propagator D t s x v) : Space)‖ := (D.R.norm_map _).symm
      _ = ‖D.FInv.field t x (physical D s x v t)‖ := by
        rw [physical_at]
        exact (congrArg norm (D.inverse_left t x (D.R (propagator D t s x v) : Space))).symm
      _ ≤ ‖D.FInv.field t x‖*‖physical D s x v t‖ := (D.FInv.field t x).le_opNorm _
      _ ≤ I*‖physical D s x v t‖ := mul_le_mul_of_nonneg_right (hinverse t x hx) (norm_nonneg _)
  calc
    _ ≤ I*‖physical D s x v t‖ := hi
    _ ≤ I*(C*g t/g s*‖physical D s x v s‖) := mul_le_mul_of_nonneg_left hp hI
    _ ≤ I*(C*g t/g s*(F*‖v‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf hr) hI
    _ = ((I*C*F)*g t/g s)*‖v‖ := by ring

/-- For det F=1, the inverse factor is a proved cofactor bound.  Thus the
physical propagator constant C becomes the polynomial 3 F³ C in H3. -/
theorem propagator_bound_of_deformation (S : Set Space)
    (g : Icc (0 : ℝ) D.T → ℝ) (hg : ∀ t, 0 < g t)
    (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hphysical : PhysicalGrowth D S g C)
    (hdet : ∀ t x, x ∈ S → (operatorMatrix (D.F.field t x)).det = 1)
    (hframe : ∀ t x, x ∈ S → ‖D.F.field t x‖ ≤ F)
    (t s : Icc (0 : ℝ) D.T) (hst : s ≤ t) (x : Space) (hx : x ∈ S) :
    ‖propagator D t s x‖ ≤ (3*F^3*C)*g t/g s := by
  have hi (r : Icc (0 : ℝ) D.T) (y : Space) (hy : y ∈ S) : ‖D.FInv.field r y‖ ≤ 3*F^2 := by
    rw [inverse_eq_adjugate (D.F.field r y) (D.FInv.field r y) (hdet r y hy) (D.inverse_left r y)]
    exact (adjugate_norm _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hframe r y hy) 2) (by norm_num))
  have h := propagator_bound_of_physical D S g hg C F (3*F^2) hC hF (by positivity)
    hphysical hframe hi t s hst x hx
  convert h using 1
  ring

end EulerPacketSourcePropagator
