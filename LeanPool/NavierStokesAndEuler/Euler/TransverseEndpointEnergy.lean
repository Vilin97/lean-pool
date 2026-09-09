/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.InitialTimePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.DirichletEndpointReduction
public import LeanPool.NavierStokesAndEuler.Euler.TransverseVariationalInverse

@[expose] public section

/-!
The actual endpoint energy in the activation argument.  Paths are genuine
initial-zero Bochner H¹ paths, and the zero-terminal correction is solved in
the existing closed transverse derivative space.  Symmetry, positivity and
minimum energy are conclusions of the construction.
-/

noncomputable section


namespace EulerTransverseEndpointEnergy

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseVariationalInverse
  EulerDirichletEndpointReduction

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

variable (T : ℝ) (hT : 0 ≤ T) (m : Icc (0 : ℝ) T → E)
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))

/-- The physical kinetic-minus-potential form on all initial-zero H¹ paths. -/
def energyOperator : TimeLp T E →L[ℝ] TimeLp T E :=
  dirichletOperator (initialPrimitiveTimeLp T hT) (timeMultiplier T hT H)

theorem energyOperator_inner (u v : TimeLp T E) :
    ⟪energyOperator T hT H u, v⟫_ℝ = ⟪u, v⟫_ℝ -
      ⟪timeMultiplier T hT H (initialPrimitiveTimeLp T hT u),
        initialPrimitiveTimeLp T hT v⟫_ℝ :=
  dirichletOperator_inner _ _ u v

/-- The source upper Hessian bound and time smallness give actual coercivity,
also when the terminal value is nonzero. -/
theorem energyOperator_coercive (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2) (u : TimeLp T E) :
    (1 / 2 : ℝ) * ‖u‖ ^ 2 ≤ ⟪energyOperator T hT H u, u⟫_ℝ :=
  dirichletOperator_coercive (initialPrimitiveTimeLp (E := E) T hT)
    (timeMultiplier T hT H) (T ^ 2 / 2) K hK
    (initialPrimitiveTimeLp_norm_sq_le T hT)
    (timeMultiplier_quadratic_upper T hT H K hH) hsmall u

omit [CompleteSpace E] in
theorem timeMultiplier_symmetric (hH : ∀ t, (H t).IsSymmetric) :
    (timeMultiplier T hT H).IsSymmetric := by
  intro u v
  change ⟪timeMultiplier T hT H u, v⟫_ℝ = ⟪u, timeMultiplier T hT H v⟫_ℝ
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [timeMultiplier_ae T hT H u, timeMultiplier_ae T hT H v]
    with t hu hv
  rw [hu, hv]
  exact hH (projIcc 0 T hT t) (u t) (v t)

theorem energyOperator_symmetric (hH : ∀ t, (H t).IsSymmetric) :
    (energyOperator T hT H).IsSymmetric := by
  intro u v
  change ⟪energyOperator T hT H u, v⟫_ℝ = ⟪u, energyOperator T hT H v⟫_ℝ
  rw [energyOperator_inner, real_inner_comm (energyOperator T hT H v) u,
    energyOperator_inner, real_inner_comm u v]
  congr 1
  have hs := timeMultiplier_symmetric T hT H hH
    (initialPrimitiveTimeLp T hT u) (initialPrimitiveTimeLp T hT v)
  change ⟪timeMultiplier T hT H (initialPrimitiveTimeLp T hT u),
      initialPrimitiveTimeLp T hT v⟫_ℝ =
    ⟪initialPrimitiveTimeLp T hT u, timeMultiplier T hT H (initialPrimitiveTimeLp T hT v)⟫_ℝ at hs
  exact hs.trans (real_inner_comm _ _)

omit [CompleteSpace E] in
theorem initialPrimitive_transverse (u : transverseDerivatives T hT m)
    (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT (u : TimeLp T E) t =
      terminalPrimitive T hT (u : TimeLp T E) t := by
  rw [initialPrimitive_eq_terminal_sub, u.property.1, sub_zero]

omit [CompleteSpace E] in
theorem initialPrimitiveTimeLp_transverse (u : transverseDerivatives T hT m) :
    initialPrimitiveTimeLp T hT (u : TimeLp T E) = transversePrimitive T hT m u := by
  change pathLpOperator T hT (initialPrimitive T hT (u : TimeLp T E)) =
    pathLpOperator T hT (terminalPrimitive T hT (u : TimeLp T E))
  congr 1
  ext t
  exact initialPrimitive_transverse T hT m u t

variable (K : ℝ) (hK : 0 ≤ K)
  (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

/-- Solve the zero-endpoint variation problem for an explicit terminal trial lift. -/
def endpointDerivative (L : U →L[ℝ] TimeLp T E) : U →L[ℝ] TimeLp T E :=
  endpointExtension (transverseDerivatives T hT m) (energyOperator T hT H)
    (1 / 2) (by norm_num) (energyOperator_coercive T hT H K hK hH hsmall) L

/-- The constructed physical stationary path. -/
def endpointDisplacement (L : U →L[ℝ] TimeLp T E) : U →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  (initialPrimitive T hT).comp (endpointDerivative T hT m H K hK hH hsmall L)

/-- The genuine endpoint quadratic form represented by a bounded operator. -/
def dirichletToNeumann (L : U →L[ℝ] TimeLp T E) : U →L[ℝ] U :=
  endpointOperator (transverseDerivatives T hT m) (energyOperator T hT H)
    (1 / 2) (by norm_num) (energyOperator_coercive T hT H K hK hH hsmall) L

omit [CompleteSpace U] in
theorem endpointDisplacement_initial (L : U →L[ℝ] TimeLp T E) (Y : U) :
    endpointDisplacement T hT m H K hK hH hsmall L Y ⟨0, le_rfl, hT⟩ = 0 :=
  initialPrimitive_initial T hT _

omit [CompleteSpace U] in
theorem endpointDerivative_sub_mem (L : U →L[ℝ] TimeLp T E) (Y : U) :
    endpointDerivative T hT m H K hK hH hsmall L Y - L Y ∈ transverseDerivatives T hT m :=
  stationaryPart_sub_mem _ _ _ _ _ (L Y)

omit [CompleteSpace U] in
/-- The stationary correction preserves the actual terminal trace. -/
theorem endpointDisplacement_terminal (L : U →L[ℝ] TimeLp T E) (Y : U) :
    endpointDisplacement T hT m H K hK hH hsmall L Y ⟨T, hT, le_rfl⟩ =
      initialPrimitive T hT (L Y) ⟨T, hT, le_rfl⟩ := by
  let v : transverseDerivatives T hT m :=
    ⟨endpointDerivative T hT m H K hK hH hsmall L Y - L Y,
      endpointDerivative_sub_mem T hT m H K hK hH hsmall L Y⟩
  have hv := initialPrimitive_transverse T hT m v ⟨T, hT, le_rfl⟩
  rw [terminalPrimitive_terminal] at hv
  change initialPrimitive T hT
    (endpointDerivative T hT m H K hK hH hsmall L Y - L Y) ⟨T, hT, le_rfl⟩ = 0 at hv
  rw [map_sub, ContinuousMap.sub_apply] at hv
  exact sub_eq_zero.mp hv

omit [CompleteSpace U] in
/-- A genuinely tangent trial produces a genuinely tangent stationary path. -/
theorem endpointDisplacement_tangent (L : U →L[ℝ] TimeLp T E)
    (hL : ∀ Y t, ⟪m t, initialPrimitive T hT (L Y) t⟫_ℝ = 0) (Y : U)
    (t : Icc (0 : ℝ) T) :
    ⟪m t, endpointDisplacement T hT m H K hK hH hsmall L Y t⟫_ℝ = 0 := by
  let v : transverseDerivatives T hT m :=
    ⟨endpointDerivative T hT m H K hK hH hsmall L Y - L Y,
      endpointDerivative_sub_mem T hT m H K hK hH hsmall L Y⟩
  have hv : ⟪m t, initialPrimitive T hT (v : TimeLp T E) t⟫_ℝ = 0 := by
    rw [initialPrimitive_transverse]
    exact v.property.2 t
  change ⟪m t, initialPrimitive T hT
    (endpointDerivative T hT m H K hK hH hsmall L Y - L Y) t⟫_ℝ = 0 at hv
  rw [map_sub, ContinuousMap.sub_apply, inner_sub_right, hL, sub_zero] at hv
  exact hv

omit [CompleteSpace U] in
/-- Every zero-endpoint transverse test satisfies the literal stationary weak equation. -/
theorem endpointDerivative_weak (L : U →L[ℝ] TimeLp T E) (Y : U)
    (v : transverseDerivatives T hT m) :
    ⟪endpointDerivative T hT m H K hK hH hsmall L Y, (v : TimeLp T E)⟫_ℝ -
      ⟪timeMultiplier T hT H
        (initialPrimitiveTimeLp T hT (endpointDerivative T hT m H K hK hH hsmall L Y)),
          transversePrimitive T hT m v⟫_ℝ = 0 := by
  have hh := stationaryPart_orthogonal (transverseDerivatives T hT m)
    (energyOperator T hT H) (1 / 2) (by norm_num)
    (energyOperator_coercive T hT H K hK hH hsmall) (L Y) v
  rw [energyOperator_inner, initialPrimitiveTimeLp_transverse] at hh
  exact hh

/-- The endpoint pairing is the actual kinetic-minus-potential energy pairing. -/
theorem dirichletToNeumann_inner (L : U →L[ℝ] TimeLp T E) (Y Z : U) :
    ⟪dirichletToNeumann T hT m H K hK hH hsmall L Y, Z⟫_ℝ =
      ⟪endpointDerivative T hT m H K hK hH hsmall L Y,
        endpointDerivative T hT m H K hK hH hsmall L Z⟫_ℝ -
      ⟪timeMultiplier T hT H
        (initialPrimitiveTimeLp T hT (endpointDerivative T hT m H K hK hH hsmall L Y)),
        initialPrimitiveTimeLp T hT (endpointDerivative T hT m H K hK hH hsmall L Z)⟫_ℝ := by
  rw [dirichletToNeumann, endpointOperator_inner, energyOperator_inner]
  rfl

/-- The source endpoint operator is symmetric positive semidefinite. -/
theorem dirichletToNeumann_positive (hHs : ∀ t, (H t).IsSymmetric)
    (L : U →L[ℝ] TimeLp T E) :
    (dirichletToNeumann T hT m H K hK hH hsmall L).IsPositive :=
  endpointOperator_positive _ _ _ _ _ (energyOperator_symmetric T hT H hHs) L

/-- The endpoint norm costs only trial energy, with no inverse or frame norm factor. -/
theorem dirichletToNeumann_norm_le (hHs : ∀ t, (H t).IsSymmetric)
    (L : U →L[ℝ] TimeLp T E) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ Y, ‖L Y‖ ^ 2 -
      ⟪timeMultiplier T hT H (initialPrimitiveTimeLp T hT (L Y)),
        initialPrimitiveTimeLp T hT (L Y)⟫_ℝ ≤ C * ‖Y‖ ^ 2) :
    ‖dirichletToNeumann T hT m H K hK hH hsmall L‖ ≤ C := by
  apply endpointOperator_norm_le _ _ _ _ _ (energyOperator_symmetric T hT H hHs) L C hC
  intro Y
  rw [energyOperator_inner, real_inner_self_eq_norm_sq]
  exact hL Y

end EulerTransverseEndpointEnergy
