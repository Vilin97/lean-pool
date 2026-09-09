/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPressure
public import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientFrame
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
public import LeanPool.NavierStokesAndEuler.Euler.MeanPathSpatialRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalWordBounds

@[expose] public section

/-!
# A normalized scalar pressure for the actual mean solution

The radial integral is applied to the real F-adjoint pressure force, whose
closed-gradient-space membership was proved from the actual Gram equation.
The resulting scalar is spatially smooth, normalized at zero, and gives the
pointwise physical equation. No scalar potential or pressure time derivative
is assumed.
-/

noncomputable section

namespace EulerMeanScalarPressure

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanSmoothRepresentative EulerMeanCoefficients
  EulerMeanTimeContinuousTranslation EulerMeanVariationalInverse EulerMeanPressure
  EulerCanonicalGraphPotential EulerTimeLp EulerVolterraConvolution
open scoped ContDiff

/-- The canonical smooth spatial representative of an actual continuous L² path. -/
def pathRepresentative (T : ℝ) (p : C(Icc (0 : ℝ) T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (t : Icc (0 : ℝ) T) : Space → Space :=
  representative (p t) (pathTranslation_evaluation_contDiff T p hp t)

theorem pathRepresentative_smooth (T : ℝ) (p : C(Icc (0 : ℝ) T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (pathRepresentative T p hp t) := representative_smooth _ _

theorem pathRepresentative_ae (T : ℝ) (p : C(Icc (0 : ℝ) T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) (t : Icc (0 : ℝ) T) :
    (p t : Space → Space) =ᵐ[volume] pathRepresentative T p hp t := representative_ae _ _

theorem pathRepresentative_continuous (T : ℝ) (p : C(Icc (0 : ℝ) T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) :
    Continuous (fun z : Icc (0 : ℝ) T × Space => pathRepresentative T p hp z.1 z.2) :=
  path_representative_joint_continuous T p hp

/-- An actual L² equation between continuous spatial representatives holds everywhere. -/
theorem representative_equation (B D R f : L2)
    (hB : SmoothOrbit B) (hD : SmoothOrbit D) (hR : SmoothOrbit R) (hf : SmoothOrbit f)
    (M : Field) (heq : D+multiplier M B+R=f) (x : Space) :
    representative D hD x+M x (representative B hB x)+representative R hR x =
      representative f hf x := by
  have hae : (fun y => representative D hD y+M y (representative B hB y)+representative R hR y)
      =ᵐ[volume] representative f hf := by
    filter_upwards [representative_ae B hB, representative_ae D hD, representative_ae R hR,
      representative_ae f hf, multiplier_ae M B, Lp.coeFn_add D (multiplier M B),
      Lp.coeFn_add (D+multiplier M B) R] with y hby hdy hry hfy hmy hsum hsum2
    have hy := congrArg (fun z : L2 => z y) heq
    rw [hsum2] at hy
    simp only [Pi.add_apply] at hy
    rw [hsum] at hy
    simpa only [Pi.add_apply, hmy, hby, hdy, hry, hfy] using hy
  exact congrFun (Measure.eq_of_ae_eq hae
    (((representative_smooth D hD).continuous.add
      (M.continuous.clm_apply (representative_smooth B hB).continuous)).add
        (representative_smooth R hR).continuous)
    (representative_smooth f hf).continuous) x

theorem pathRepresentative_equation (T : ℝ)
    (B D R f : C(Icc (0 : ℝ) T,L2))
    (hB : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a B))
    (hD : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a D))
    (hR : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a R))
    (hf : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a f))
    (M : C(Icc (0 : ℝ) T,Field))
    (heq : ∀ t, D t+multiplier (M t) (B t)+R t=f t)
    (t : Icc (0 : ℝ) T) (x : Space) :
    pathRepresentative T D hD t x+M t x (pathRepresentative T B hB t x)+
      pathRepresentative T R hR t x = pathRepresentative T f hf t x :=
  representative_equation (B t) (D t) (R t) (f t)
    (pathTranslation_evaluation_contDiff T B hB t) (pathTranslation_evaluation_contDiff T D hD t)
    (pathTranslation_evaluation_contDiff T R hR t) (pathTranslation_evaluation_contDiff T f hf t)
    (M t) (heq t) x

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (FInv : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2))
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv (operatorPath T F.field) (operatorPath T F₁.field) A L u f)
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T (operatorPath T F.field) t v‖^2)
  (fC : C(Icc (0 : ℝ) T,L2))
  (hR : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a (s.pressurePath c hc hLower fC)))

/-- The concrete normalized scalar mean pressure, constructed by a radial integral. -/
def pressureScalar (t : Icc (0 : ℝ) T) : Space → ℝ :=
  radialPotential (fun x => (F.field t x).adjoint
    (pathRepresentative T (s.pressurePath c hc hLower fC) hR t x))

/-- Spatial smoothness, normalization, and exact gradient of the constructed pressure. -/
theorem pressureScalar_spec (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (pressureScalar T hT F F₁ FInv s c hc hLower fC hR t) ∧
    pressureScalar T hT F F₁ FInv s c hc hLower fC hR t 0 = 0 ∧
    ∀ x, gradient (pressureScalar T hT F F₁ FInv s c hc hLower fC hR t) x =
      (F.field t x).adjoint (pathRepresentative T (s.pressurePath c hc hLower fC) hR t x) := by
  have hAdj : ContDiff ℝ ∞ (fun x : Space => (F.field t x).adjoint) :=
    (EulerTransverseGramInverse.realAdjoint (U := Space) (E := Space)).contDiff.comp (F.smooth t)
  exact weighted_pressure_has_potential (F.field t) (adjointField (F.field t)) (fun _ => rfl)
    (s.pressurePath c hc hLower fC t) (s.pressurePath_gradient c hc hLower fC t)
    (pathRepresentative T (s.pressurePath c hc hLower fC) hR t)
    (pathRepresentative_ae T _ hR t) (hAdj.clm_apply (pathRepresentative_smooth T _ hR t))

/-- The source mean pressure has no angular dependence. -/
def pressureProfile (t : Icc (0 : ℝ) T) (x : Space) (_θ : ℝ) : ℝ :=
  pressureScalar T hT F F₁ FInv s c hc hLower fC hR t x

theorem pressureProfile_angle_derivative (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    HasDerivAt (pressureProfile T hT F F₁ FInv s c hc hLower fC hR t x) 0 θ :=
  hasDerivAt_const θ _

/-- The physical pressure force is exactly the actual residual, because the
inverse-transpose cancels the transpose of the given frame. -/
theorem pressureScalar_physicalGradient
    (Finv : C(Icc (0 : ℝ) T,Field))
    (hFinv : ∀ t x v, F.field t x (Finv t x v) = v)
    (t : Icc (0 : ℝ) T) (x : Space) :
    (Finv t x).adjoint (gradient (pressureScalar T hT F F₁ FInv s c hc hLower fC hR t) x) =
      pathRepresentative T (s.pressurePath c hc hLower fC) hR t x := by
  rw [(pressureScalar_spec T hT F F₁ FInv s c hc hLower fC hR t).2.2 x]
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left, adjoint_inner_left, hFinv]

/-- The constructed pressure gives the literal pointwise source equation. -/
theorem pressureScalar_equation
    (hTpos : 0 < T)
    (hFTime : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT (operatorPath T F.field))
        (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
    (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    (hMF : ∀ t x v, F₁.field t x v = M.field t x (F.field t x v))
    (Finv : C(Icc (0 : ℝ) T,Field)) (hFinv : ∀ t x v, F.field t x (Finv t x v) = v)
    (hB : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a s.continuousVelocity))
    (hD : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a (s.classicalPhysicalDerivative c hc
      hLower fC)))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (t : Icc (0 : ℝ) T) (x : Space) :
    pathRepresentative T (s.classicalPhysicalDerivative c hc hLower fC) hD t x+
      M.field t x (pathRepresentative T s.continuousVelocity hB t x)+
      (Finv t x).adjoint (gradient (pressureScalar T hT F F₁ FInv s c hc hLower fC hR t) x) =
        pathRepresentative T fC hfC t x := by
  rw [pressureScalar_physicalGradient T hT F F₁ FInv s c hc hLower fC hR Finv hFinv t x]
  exact pathRepresentative_equation T s.continuousVelocity
    (s.classicalPhysicalDerivative c hc hLower fC) (s.pressurePath c hc hLower fC) fC
    hB hD hR hfC M.field
    (s.pressurePath_equation c hc hLower fC hTpos hFTime (operatorPath T M.field)
      (operatorPath_comp T M.field F.field F₁.field hMF)) t x

end EulerMeanScalarPressure
