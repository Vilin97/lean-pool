/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.InitialTimePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.TransverseVariationalInverse
public import Mathlib.Analysis.InnerProductSpace.Positive
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CoerciveProjection
import LeanPool.NavierStokesAndEuler.Euler.Foundations.DNSelection

/-!
The actual endpoint energy in the activation argument.  Paths are genuine
initial-zero Bochner H¹ paths, and the zero-terminal correction is solved in
the existing closed transverse derivative space.  Symmetry, positivity and
minimum energy are conclusions of the construction.
-/

section

/-!
The endpoint Schur complement of a coercive quadratic form.  The stationary
extension is constructed by the inverse of the form on the closed zero-trace
space.  No stationary extension or Dirichlet-to-Neumann map is an input.
-/

@[expose] public section

noncomputable section

namespace EulerDirichletEndpointReduction

open InnerProductSpace ContinuousLinearMap EulerCoerciveProjection

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

variable (S : Submodule ℝ E) [CompleteSpace S]
  (A : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
  (hA : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)

/-- The zero-trace correction obtained by a genuine coercive inverse. -/
def correction : E →L[ℝ] S :=
  (projectedInverse S A c hc hA).comp (S.orthogonalProjectionOnto.comp A)

/-- Subtract the solved zero-trace correction from any trial extension. -/
def stationaryPart : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - S.subtypeL.comp (correction S A c hc hA)

theorem stationaryPart_eq (x : E) :
    stationaryPart S A c hc hA x = x - (correction S A c hc hA x : E) := rfl

theorem correction_equation (x : E) (v : S) :
    ⟪A (correction S A c hc hA x : E), (v : E)⟫_ℝ = ⟪A x, (v : E)⟫_ℝ := by
  rw [← projectedOperator_inner S A]
  change ⟪projectedOperator S A
    (projectedInverse S A c hc hA (S.orthogonalProjectionOnto (A x))), v⟫_ℝ = _
  rw [projectedOperator_inverse_apply]
  exact S.inner_orthogonalProjectionOnto_eq_of_mem_right v (A x)

/-- The constructed extension satisfies all zero-trace stationary equations. -/
theorem stationaryPart_orthogonal (x : E) (v : S) :
    ⟪A (stationaryPart S A c hc hA x), (v : E)⟫_ℝ = 0 := by
  rw [stationaryPart_eq, map_sub, inner_sub_left, correction_equation, sub_self]

theorem stationaryPart_sub_mem (x : E) : stationaryPart S A c hc hA x - x ∈ S := by
  rw [stationaryPart_eq]
  have he : x - (correction S A c hc hA x : E) - x =
      -(correction S A c hc hA x : E) := by abel
  rw [he]
  exact S.neg_mem (correction S A c hc hA x).property

theorem stationaryPart_subspace (v : S) : stationaryPart S A c hc hA (v : E) = 0 := by
  have hcorr : correction S A c hc hA (v : E) = v := by
    change coerciveInverse (projectedOperator S A) c hc
      (projectedOperator_coercive S A c hA) (projectedOperator S A v) = v
    exact inverse_operator_apply _ _ _ _ v
  rw [stationaryPart_eq, hcorr, sub_self]

/-- The actual extension depends only on the terminal class of the trial. -/
theorem stationaryPart_eq_of_sub_mem (x y : E) (hxy : x - y ∈ S) :
    stationaryPart S A c hc hA x = stationaryPart S A c hc hA y := by
  have he := stationaryPart_subspace S A c hc hA ⟨x - y, hxy⟩
  change stationaryPart S A c hc hA (x - y) = 0 at he
  rw [map_sub] at he
  exact sub_eq_zero.mp he

/-- Energy splits orthogonally along the stationary extension and zero-trace variations. -/
theorem energy_split (hAs : A.IsSymmetric) (x : E) (v : S) :
    ⟪A (stationaryPart S A c hc hA x + (v : E)),
      stationaryPart S A c hc hA x + (v : E)⟫_ℝ =
        ⟪A (stationaryPart S A c hc hA x), stationaryPart S A c hc hA x⟫_ℝ +
          ⟪A (v : E), (v : E)⟫_ℝ := by
  have hz := stationaryPart_orthogonal S A c hc hA x v
  have hz' : ⟪A (v : E), stationaryPart S A c hc hA x⟫_ℝ = 0 := by
    have hs := hAs (v : E) (stationaryPart S A c hc hA x)
    change ⟪A (v : E), stationaryPart S A c hc hA x⟫_ℝ =
      ⟪(v : E), A (stationaryPart S A c hc hA x)⟫_ℝ at hs
    rw [hs, real_inner_comm]
    exact hz
  simp only [map_add, inner_add_left, inner_add_right, hz, hz', add_zero, zero_add]

/-- The solved extension minimizes the actual quadratic form in its trace class. -/
theorem stationaryPart_minimizes (hAs : A.IsSymmetric) (x : E) :
    ⟪A (stationaryPart S A c hc hA x), stationaryPart S A c hc hA x⟫_ℝ ≤
      ⟪A x, x⟫_ℝ := by
  have he := energy_split S A c hc hA hAs x (correction S A c hc hA x)
  rw [stationaryPart_eq, sub_add_cancel] at he
  have hp := hA (correction S A c hc hA x : E)
  have hc0 := mul_nonneg hc.le (sq_nonneg ‖(correction S A c hc hA x : E)‖)
  rw [stationaryPart_eq]
  linarith

variable [CompleteSpace E]

/-- A prescribed bounded trial lift followed by the actual stationary projection. -/
def endpointExtension (L : U →L[ℝ] E) : U →L[ℝ] E :=
  (stationaryPart S A c hc hA).comp L

/-- The operator representing the actual stationary endpoint energy. -/
def endpointOperator (L : U →L[ℝ] E) : U →L[ℝ] U :=
  (endpointExtension S A c hc hA L).adjoint.comp
    (A.comp (endpointExtension S A c hc hA L))

theorem endpointOperator_inner (L : U →L[ℝ] E) (x y : U) :
    ⟪endpointOperator S A c hc hA L x, y⟫_ℝ =
      ⟪A (endpointExtension S A c hc hA L x), endpointExtension S A c hc hA L y⟫_ℝ := by
  simp only [endpointOperator, comp_apply, adjoint_inner_left]

/-- Positivity is inherited from the actual displacement form. -/
theorem endpointOperator_positive (hAs : A.IsSymmetric) (L : U →L[ℝ] E) :
    (endpointOperator S A c hc hA L).IsPositive := by
  have hp : A.IsPositive := (ContinuousLinearMap.isPositive_iff A).2
    ⟨hAs, fun x => (mul_nonneg hc.le (sq_nonneg ‖x‖)).trans (hA x)⟩
  exact hp.adjoint_conj (endpointExtension S A c hc hA L)

/-- Any explicit admissible trial controls the endpoint quadratic form. -/
theorem endpointOperator_trial_bound (hAs : A.IsSymmetric) (L : U →L[ℝ] E) (x : U) :
    ⟪endpointOperator S A c hc hA L x, x⟫_ℝ ≤ ⟪A (L x), L x⟫_ℝ := by
  rw [endpointOperator_inner]
  exact stationaryPart_minimizes S A c hc hA hAs (L x)

omit [CompleteSpace E] in
/-- A nonnegative quadratic-form bound gives the same operator-norm bound. -/
theorem positive_norm_le_of_quadratic (B : E →L[ℝ] E) (hB : B.IsPositive)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ⟪B x, x⟫_ℝ ≤ C * ‖x‖ ^ 2) : ‖B‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  have hx' : ⟪B x, x⟫_ℝ ≤ C := by simpa only [hx, one_pow, mul_one] using hb x
  have hy' : ⟪B y, y⟫_ℝ ≤ C := by simpa only [hy, one_pow, mul_one] using hb y
  have hcross := EulerDNSelection.positive_cross_sq_le B hB x y
  have hprod := mul_le_mul hx' hy' (hB.inner_nonneg_left y) hC
  have hs : |⟪B x, y⟫_ℝ| ^ 2 ≤ C ^ 2 := by
    rw [sq_abs]
    nlinarith only [hcross, hprod]
  have habs := (sq_le_sq₀ (abs_nonneg _) hC).1 hs
  exact (le_abs_self _).trans habs

/-- The endpoint norm is controlled by the energy of the trial, without an inverse norm loss. -/
theorem endpointOperator_norm_le (hAs : A.IsSymmetric) (L : U →L[ℝ] E)
    (C : ℝ) (hC : 0 ≤ C) (hL : ∀ x, ⟪A (L x), L x⟫_ℝ ≤ C * ‖x‖ ^ 2) :
    ‖endpointOperator S A c hc hA L‖ ≤ C := by
  apply positive_norm_le_of_quadratic _ (endpointOperator_positive S A c hc hA hAs L) C hC
  intro x
  exact (endpointOperator_trial_bound S A c hc hA hAs L x).trans (hL x)

end EulerDirichletEndpointReduction

end
end

end

@[expose] public section

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
