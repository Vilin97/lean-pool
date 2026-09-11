/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TerminalTimePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.TransverseVariationalOperator
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The actual zero-endpoint transverse displacement inverse

We use the derivative of the physical displacement as the Hilbert-space
variable.  Terminal integration supplies the displacement.  Its initial trace
and its moving normal component are bounded linear constraints, hence define a
closed Hilbert subspace.  The kinetic energy is exactly the squared norm on this
space; no norm equivalence or pre-existing differential inverse is assumed.

This constructs the weak transverse inverse in source lines 172--184.  The
coordinate identity `η = F R ξ` and strong coordinate evolution require the
separate frame and regularity arguments; they are not assumed in this file.
-/

section

/-!
# Recovering the source's transverse coordinates

The moving plane with normal `(F⁻¹)* m₀` is exactly the image under `F` of
the fixed plane `m₀⊥`.  Orthogonal projection gives a bounded coordinate map,
and on the moving plane its reconstruction is the identity.  These are
coefficient identities, not assumptions about a differential inverse.
-/

@[expose] public section

noncomputable section

namespace EulerTransverseFrameCoordinates

open InnerProductSpace ContinuousLinearMap

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The fixed reference transverse plane. -/
abbrev referencePlane (m₀ : E) : Submodule ℝ E := (ℝ ∙ m₀)ᗮ

/-- The actual pulled-back normal used by the packet construction. -/
def movingNormal (F : E ≃L[ℝ] E) (m₀ : E) : E := F.symm.toContinuousLinearMap.adjoint m₀

/-- Bounded recovery of fixed-plane coordinates from a physical displacement. -/
def coordinates (F : E ≃L[ℝ] E) (m₀ : E) : E →L[ℝ] referencePlane m₀ :=
  (referencePlane m₀).orthogonalProjectionOnto.comp F.symm.toContinuousLinearMap

/-- Moving tangency is exactly fixed-plane membership after applying `F⁻¹`. -/
theorem tangent_iff (F : E ≃L[ℝ] E) (m₀ η : E) :
    ⟪movingNormal F m₀, η⟫_ℝ = 0 ↔ F.symm η ∈ referencePlane m₀ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  unfold movingNormal
  rw [adjoint_inner_left]
  rfl

/-- Reconstructing a tangent displacement from its recovered coordinates is exact. -/
theorem reconstruct (F : E ≃L[ℝ] E) (m₀ η : E)
    (hη : ⟪movingNormal F m₀, η⟫_ℝ = 0) :
    F (coordinates F m₀ η : E) = η := by
  have hm : F.symm η ∈ referencePlane m₀ := (tangent_iff F m₀ η).1 hη
  have hp := (referencePlane m₀).orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨F.symm η, hm⟩ : referencePlane m₀)
  change F ((referencePlane m₀).orthogonalProjectionOnto (F.symm η) : E) = η
  rw [hp]
  exact F.apply_symm_apply η

omit [CompleteSpace E] in
/-- The coordinate map is a left inverse to `F` restricted to the reference plane. -/
theorem coordinates_leftInverse (F : E ≃L[ℝ] E) (m₀ : E) (ξ : referencePlane m₀) :
    coordinates F m₀ (F (ξ : E)) = ξ := by
  change (referencePlane m₀).orthogonalProjectionOnto (F.symm (F (ξ : E))) = ξ
  rw [F.symm_apply_apply]
  exact (referencePlane m₀).orthogonalProjectionOnto_mem_subspace_eq_self ξ

omit [CompleteSpace E] in
/-- The coordinate map has the expected polynomial bound from the inverse frame. -/
theorem coordinates_norm (F : E ≃L[ℝ] E) (m₀ η : E) :
    ‖coordinates F m₀ η‖ ≤ ‖F.symm.toContinuousLinearMap‖ * ‖η‖ := by
  exact ((referencePlane m₀).norm_orthogonalProjectionOnto_apply_le (F.symm η)).trans
    (F.symm.toContinuousLinearMap.le_opNorm η)

/-- Any orthonormal identification with the fixed plane gives the source's `R⊥` coordinates. -/
def frameCoordinates (F : E ≃L[ℝ] E) (m₀ : E)
    (R : U ≃ₗᵢ[ℝ] referencePlane m₀) : E →L[ℝ] U :=
  R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (coordinates F m₀)

/-- The full source reconstruction `η = F R⊥ ξ` follows from moving tangency. -/
theorem frame_reconstruct (F : E ≃L[ℝ] E) (m₀ η : E)
    (R : U ≃ₗᵢ[ℝ] referencePlane m₀) (hη : ⟪movingNormal F m₀, η⟫_ℝ = 0) :
    F (R (frameCoordinates F m₀ R η) : E) = η := by
  change F (R (R.symm (coordinates F m₀ η)) : E) = η
  rw [R.apply_symm_apply]
  exact reconstruct F m₀ η hη

omit [CompleteSpace E] in
/-- Passing to an orthonormal coordinate basis has no extra norm cost. -/
theorem frameCoordinates_norm (F : E ≃L[ℝ] E) (m₀ η : E)
    (R : U ≃ₗᵢ[ℝ] referencePlane m₀) :
    ‖frameCoordinates F m₀ R η‖ ≤ ‖F.symm.toContinuousLinearMap‖ * ‖η‖ := by
  change ‖R.symm (coordinates F m₀ η)‖ ≤ _
  rw [R.symm.norm_map]
  exact coordinates_norm F m₀ η

section Paths

variable {X : Type*} [TopologicalSpace X]

/-- Applying a continuous inverse-frame path produces actual continuous
transverse coordinates, not separate incompatible pointwise choices. -/
def coordinatePath (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
    (A : C(X, E →L[ℝ] E)) (η : C(X, E)) : C(X, U) :=
  ⟨fun t => R.symm ((referencePlane m₀).orthogonalProjectionOnto (A t (η t))),
    R.symm.continuous.comp ((referencePlane m₀).orthogonalProjectionOnto.continuous.comp
      (A.continuous.clm_apply η.continuous))⟩

/-- The recovered continuous coordinates reconstruct every tangent displacement. -/
theorem coordinatePath_reconstruct (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
    (F : X → E ≃L[ℝ] E) (A : C(X, E →L[ℝ] E))
    (hA : ∀ t, A t = (F t).symm.toContinuousLinearMap) (η : C(X, E))
    (hη : ∀ t, ⟪movingNormal (F t) m₀, η t⟫_ℝ = 0) (t : X) :
    F t (R (coordinatePath m₀ R A η t) : E) = η t := by
  change F t (R (R.symm ((referencePlane m₀).orthogonalProjectionOnto
    (A t (η t)))) : E) = η t
  rw [hA t]
  exact frame_reconstruct (F t) m₀ (η t) R (hη t)

omit [CompleteSpace E] in
/-- Zero endpoint displacements give zero endpoint coordinates. -/
theorem coordinatePath_zero_at (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
    (A : C(X, E →L[ℝ] E)) (η : C(X, E)) (t : X) (hη : η t = 0) :
    coordinatePath m₀ R A η t = 0 := by
  change R.symm ((referencePlane m₀).orthogonalProjectionOnto (A t (η t))) = 0
  simp only [hη, map_zero]

omit [CompleteSpace E] in
/-- Pointwise coordinate control only pays the actual inverse-frame norm. -/
theorem coordinatePath_norm (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
    (A : C(X, E →L[ℝ] E)) (η : C(X, E)) (t : X) :
    ‖coordinatePath m₀ R A η t‖ ≤ ‖A t‖ * ‖η t‖ := by
  change ‖R.symm ((referencePlane m₀).orthogonalProjectionOnto (A t (η t)))‖ ≤ _
  rw [R.symm.norm_map]
  exact ((referencePlane m₀).norm_orthogonalProjectionOnto_apply_le (A t (η t))).trans
    ((A t).le_opNorm (η t))

end Paths

end EulerTransverseFrameCoordinates

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransverseVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Derivatives of actual zero-endpoint displacements tangent to the moving plane. -/
def transverseDerivatives (T : ℝ) (hT : 0 ≤ T) (m : Icc (0 : ℝ) T → E) :
    Submodule ℝ (TimeLp T E) where
  carrier := {u | initialTrace T hT u = 0 ∧
    ∀ t, ⟪m t, terminalPrimitive T hT u t⟫_ℝ = 0}
  zero_mem' := by
    constructor
    · exact map_zero _
    · intro t
      simp only [map_zero, ContinuousMap.zero_apply, inner_zero_right]
  add_mem' := by
    intro u v hu hv
    constructor
    · simp only [map_add, hu.1, hv.1, add_zero]
    · intro t
      simp only [map_add, ContinuousMap.add_apply, inner_add_right, hu.2 t, hv.2 t,
        add_zero]
  smul_mem' := by
    intro a u hu
    constructor
    · simp only [map_smul, hu.1, smul_zero]
    · intro t
      simp only [map_smul, ContinuousMap.smul_apply, inner_smul_right, hu.2 t,
        mul_zero]

/-- The two endpoint and moving tangency conditions are closed constraints. -/
theorem transverseDerivatives_closed (T : ℝ) (hT : 0 ≤ T) (m : Icc (0 : ℝ) T → E) :
    IsClosed (transverseDerivatives T hT m : Set (TimeLp T E)) := by
  change IsClosed {u : TimeLp T E | initialTrace T hT u = 0 ∧
    ∀ t, ⟪m t, terminalPrimitive T hT u t⟫_ℝ = 0}
  rw [Set.ofPred_and, Set.ofPred_forall]
  apply (isClosed_eq (initialTrace T hT).continuous continuous_const).inter
  apply isClosed_iInter
  intro t
  exact isClosed_eq
    (continuous_const.inner ((ContinuousMap.evalCLM ℝ t).continuous.comp
      (terminalPrimitive T hT).continuous)) continuous_const

/-- Closedness supplies completeness for the actual displacement-derivative space. -/
instance transverseDerivatives_complete [CompleteSpace E] (T : ℝ) (hT : 0 ≤ T)
    (m : Icc (0 : ℝ) T → E) : CompleteSpace (transverseDerivatives T hT m) :=
  (transverseDerivatives_closed T hT m).completeSpace_coe

/-- The zero initial trace is exactly the zero-mean condition on the time derivative. -/
theorem transverseDerivatives_integral_zero (T : ℝ) (hT : 0 ≤ T)
    (m : Icc (0 : ℝ) T → E) (u : transverseDerivatives T hT m) :
    (∫ t in 0..T, (u : TimeLp T E) t) = 0 := by
  have hi := u.property.1
  rw [initialTrace_eq_integral] at hi
  exact neg_eq_zero.mp hi

/-- Every genuine absolutely continuous zero-endpoint transverse path with an
L² derivative belongs to this Hilbert model.  Thus the test space is not an
assumed family of already solved displacements. -/
theorem derivative_mem_of_ac [CompleteSpace E] (T : ℝ) (hT : 0 ≤ T)
    (m : Icc (0 : ℝ) T → E) (u : TimeLp T E) (η : ℝ → E)
    (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (u t) t)
    (hzero : η 0 = 0) (hterminal : η T = 0)
    (htangent : ∀ t : Icc (0 : ℝ) T, ⟪m t, η t⟫_ℝ = 0) :
    u ∈ transverseDerivatives T hT m := by
  have heq := eq_realPrimitive_of_ac_hasDerivAt_ae T hT u η hη hder hterminal
  constructor
  · change realPrimitive T u 0 = 0
    rw [← heq 0 ⟨le_rfl, hT⟩, hzero]
  · intro t
    change ⟪m t, realPrimitive T u t⟫_ℝ = 0
    rw [← heq t t.property]
    exact htangent t

/-- The actual terminal primitive restricted to the transverse derivative space. -/
def transversePrimitive (T : ℝ) (hT : 0 ≤ T) (m : Icc (0 : ℝ) T → E) :
    transverseDerivatives T hT m →L[ℝ] TimeLp T E :=
  (primitiveTimeLp T hT).comp (transverseDerivatives T hT m).subtypeL

/-- The sharp time Poincaré bound holds on the actual transverse space. -/
theorem transversePrimitive_norm_sq (T : ℝ) (hT : 0 ≤ T)
    (m : Icc (0 : ℝ) T → E) (u : transverseDerivatives T hT m) :
    ‖transversePrimitive T hT m u‖ ^ 2 ≤ T ^ 2 / 2 * ‖u‖ ^ 2 :=
  primitiveTimeLp_norm_sq_le T hT (u : TimeLp T E)

/-- A convenient polynomial operator bound for the terminal primitive. -/
theorem transversePrimitive_norm_le (T : ℝ) (hT : 0 ≤ T)
    (m : Icc (0 : ℝ) T → E) : ‖transversePrimitive T hT m‖ ≤ T := by
  apply ContinuousLinearMap.opNorm_le_bound _ hT
  intro u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hT (norm_nonneg u))).1
  calc
    ‖transversePrimitive T hT m u‖ ^ 2 ≤ T ^ 2 / 2 * ‖u‖ ^ 2 :=
      transversePrimitive_norm_sq T hT m u
    _ ≤ T ^ 2 * ‖u‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖u‖)
      nlinarith only [sq_nonneg T]
    _ = (T * ‖u‖) ^ 2 := by ring

variable [CompleteSpace E]
variable (T : ℝ) (hT : 0 ≤ T) (m : Icc (0 : ℝ) T → E)
variable (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
variable (K : ℝ) (hK : 0 ≤ K)
variable (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
variable (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

/-- The actual transverse forcing-to-derivative map, constructed from the
primitive and the given time-dependent Hessian. -/
def transverseSolver : TimeLp T E →L[ℝ] transverseDerivatives T hT m :=
  dirichletSolver (transversePrimitive T hT m) (timeMultiplier T hT H)
    (T ^ 2 / 2) K hK (transversePrimitive_norm_sq T hT m)
    (timeMultiplier_quadratic_upper T hT H K hH) hsmall

/-- The continuous displacement is constructed by integrating its solved derivative. -/
def transverseDisplacement : TimeLp T E →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  (terminalPrimitive T hT).comp
    ((transverseDerivatives T hT m).subtypeL.comp
      (transverseSolver T hT m H K hK hH hsmall))

/-- The solved displacement vanishes at the initial endpoint. -/
theorem transverseDisplacement_initial (f : TimeLp T E) :
    transverseDisplacement T hT m H K hK hH hsmall f ⟨0, le_rfl, hT⟩ = 0 :=
  (transverseSolver T hT m H K hK hH hsmall f).property.1

/-- The solved displacement vanishes at the terminal endpoint. -/
theorem transverseDisplacement_terminal (f : TimeLp T E) :
    transverseDisplacement T hT m H K hK hH hsmall f ⟨T, hT, le_rfl⟩ = 0 := by
  change terminalPrimitive T hT
    (transverseSolver T hT m H K hK hH hsmall f : TimeLp T E) ⟨T, hT, le_rfl⟩ = 0
  exact terminalPrimitive_terminal T hT
    (transverseSolver T hT m H K hK hH hsmall f : TimeLp T E)

/-- The solved displacement belongs to the actual moving transverse plane. -/
theorem transverseDisplacement_tangent (f : TimeLp T E) (t : Icc (0 : ℝ) T) :
    ⟪m t, transverseDisplacement T hT m H K hK hH hsmall f t⟫_ℝ = 0 :=
  (transverseSolver T hT m H K hK hH hsmall f).property.2 t

/-- The derivative of the constructed displacement is the solved L² field,
as an actual almost-everywhere derivative of its continuous real-time representative. -/
theorem transverseDisplacement_hasDerivAt_ae (f : TimeLp T E) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (realPrimitive T
        (transverseSolver T hT m H K hK hH hsmall f : TimeLp T E))
        ((transverseSolver T hT m H K hK hH hsmall f : TimeLp T E) t) t :=
  realPrimitive_hasDerivAt_ae T
    (transverseSolver T hT m H K hK hH hsmall f : TimeLp T E)

/-- The actual weak transverse displacement equation, tested against every
zero-endpoint displacement in the same moving plane. -/
theorem transverseSolver_weak (f : TimeLp T E) (v : transverseDerivatives T hT m) :
    let u := transverseSolver T hT m H K hK hH hsmall f
    ⟪(u : TimeLp T E), (v : TimeLp T E)⟫_ℝ -
        ⟪timeMultiplier T hT H (transversePrimitive T hT m u),
          transversePrimitive T hT m v⟫_ℝ =
      -⟪f, transversePrimitive T hT m v⟫_ℝ :=
  dirichletSolver_weak (transversePrimitive T hT m) (timeMultiplier T hT H)
    (T ^ 2 / 2) K hK (transversePrimitive_norm_sq T hT m)
    (timeMultiplier_quadratic_upper T hT H K hH) hsmall f v

/-- The constructed weak inverse is unique in the actual transverse displacement space. -/
theorem transverseSolver_unique (f : TimeLp T E) (u : transverseDerivatives T hT m)
    (hu : ∀ v : transverseDerivatives T hT m,
      ⟪(u : TimeLp T E), (v : TimeLp T E)⟫_ℝ -
          ⟪timeMultiplier T hT H (transversePrimitive T hT m u),
            transversePrimitive T hT m v⟫_ℝ =
        -⟪f, transversePrimitive T hT m v⟫_ℝ) :
    u = transverseSolver T hT m H K hK hH hsmall f :=
  dirichletSolver_unique (transversePrimitive T hT m) (timeMultiplier T hT H)
    (T ^ 2 / 2) K hK (transversePrimitive_norm_sq T hT m)
    (timeMultiplier_quadratic_upper T hT H K hH) hsmall f u hu

/-- The solved derivative has a polynomial finite-time bound, with no exponential in H. -/
theorem transverseSolver_norm (f : TimeLp T E) :
    ‖transverseSolver T hT m H K hK hH hsmall f‖ ≤ 2 * T * ‖f‖ := by
  apply (dirichletSolver_norm (transversePrimitive T hT m) (timeMultiplier T hT H)
    (T ^ 2 / 2) K hK (transversePrimitive_norm_sq T hT m)
    (timeMultiplier_quadratic_upper T hT H K hH) hsmall f).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (transversePrimitive_norm_le T hT m) (by norm_num))
    (norm_nonneg f)

/-- Zero forcing has zero displacement, the pointwise-in-label support preservation property. -/
@[simp] theorem transverseDisplacement_zero :
    transverseDisplacement T hT m H K hK hH hsmall 0 = 0 := map_zero _

/-- The inverse preserves sign, hence oddness in a parameter with unchanged coefficients. -/
theorem transverseDisplacement_neg (f : TimeLp T E) :
    transverseDisplacement T hT m H K hK hH hsmall (-f) =
      -transverseDisplacement T hT m H K hK hH hsmall f := map_neg _ _

/-- A zero angle mean of the forcing gives a zero angle mean of the displacement.
The measure can be the normalized periodic angle measure; coefficients are fixed in this parameter.
-/
theorem transverseDisplacement_integral_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → TimeLp T E) (hf : Integrable f μ)
    (hmean : ∫ a, f a ∂μ = 0) :
    (∫ a, transverseDisplacement T hT m H K hK hH hsmall (f a) ∂μ) = 0 := by
  rw [(transverseDisplacement T hT m H K hK hH hsmall).integral_comp_comm hf,
    hmean, map_zero]

include K hK hH hsmall in
/-- Existence and uniqueness follow from the actual sharp time primitive estimate,
the pointwise potential bound, and closed transverse constraints. -/
theorem existsUnique_transverse_weak_solution (f : TimeLp T E) :
    ∃! u : transverseDerivatives T hT m,
      ∀ v : transverseDerivatives T hT m,
        ⟪(u : TimeLp T E), (v : TimeLp T E)⟫_ℝ -
            ⟪timeMultiplier T hT H (transversePrimitive T hT m u),
              transversePrimitive T hT m v⟫_ℝ =
          -⟪f, transversePrimitive T hT m v⟫_ℝ := by
  exact ⟨transverseSolver T hT m H K hK hH hsmall f,
    transverseSolver_weak T hT m H K hK hH hsmall f,
    fun u hu => transverseSolver_unique T hT m H K hK hH hsmall f u hu⟩

include K hK hH hsmall in
/-- The actual weak inverse has the source's form `η = F R⊥ ξ`, with continuous
coordinates and both endpoint conditions.  The frame is prescribed coefficient
data; neither a displacement nor a differential inverse is supplied. -/
theorem exists_transverse_frame_displacement
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (m₀ : E) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m₀)
    (F : Icc (0 : ℝ) T → E ≃L[ℝ] E)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hA : ∀ t, A t = (F t).symm.toContinuousLinearMap) (f : TimeLp T E) :
    let mF := fun t => EulerTransverseFrameCoordinates.movingNormal (F t) m₀
    ∃ (u : transverseDerivatives T hT mF)
      (η : C(Icc (0 : ℝ) T, E)) (ξ : C(Icc (0 : ℝ) T, U)),
      η = terminalPrimitive T hT (u : TimeLp T E) ∧
      η ⟨0, le_rfl, hT⟩ = 0 ∧ η ⟨T, hT, le_rfl⟩ = 0 ∧
      ξ ⟨0, le_rfl, hT⟩ = 0 ∧ ξ ⟨T, hT, le_rfl⟩ = 0 ∧
      (∀ t, F t (R (ξ t) : E) = η t) ∧
      ‖u‖ ≤ 2 * T * ‖f‖ ∧
      ∀ v : transverseDerivatives T hT mF,
        ⟪(u : TimeLp T E), (v : TimeLp T E)⟫_ℝ -
          ⟪timeMultiplier T hT H (transversePrimitive T hT mF u),
            transversePrimitive T hT mF v⟫_ℝ =
          -⟪f, transversePrimitive T hT mF v⟫_ℝ := by
  let mF := fun t => EulerTransverseFrameCoordinates.movingNormal (F t) m₀
  let u := transverseSolver T hT mF H K hK hH hsmall f
  let η := transverseDisplacement T hT mF H K hK hH hsmall f
  let ξ := EulerTransverseFrameCoordinates.coordinatePath m₀ R A η
  have h0 : η ⟨0, le_rfl, hT⟩ = 0 :=
    transverseDisplacement_initial T hT mF H K hK hH hsmall f
  have hT' : η ⟨T, hT, le_rfl⟩ = 0 :=
    transverseDisplacement_terminal T hT mF H K hK hH hsmall f
  refine ⟨u, η, ξ, rfl, h0, hT', ?_, ?_, ?_,
    transverseSolver_norm T hT mF H K hK hH hsmall f,
    transverseSolver_weak T hT mF H K hK hH hsmall f⟩
  · exact EulerTransverseFrameCoordinates.coordinatePath_zero_at m₀ R A η _ h0
  · exact EulerTransverseFrameCoordinates.coordinatePath_zero_at m₀ R A η _ hT'
  · exact EulerTransverseFrameCoordinates.coordinatePath_reconstruct m₀ R F A hA η
      (transverseDisplacement_tangent T hT mF H K hK hH hsmall f)

end EulerTransverseVariationalInverse
