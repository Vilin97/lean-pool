/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import Mathlib.Algebra.Group.Ext
import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.ParametrizedInner
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyMixedRegularity
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyKoszulVariation

/-!
# Mixed regularity of metric pairings

This module specializes the intrinsic chart bridge to the scalar pairings that occur in the
Koszul formula.  The joint spacetime regularity and spatial regularity of the velocity pairing
remain explicit hypotheses: they are genuine analytic regularity, not consequences of the
slicewise `TimeDependentRiemannianMetric` abbreviation.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
/-- A jointly `C²` metric tensor pairs jointly `C²` spatial sections.

The input regularity is the actual bilinear-form section `(t, x) ↦ (g t).inner x`
over spacetime.  This is stronger than slicewise `C²` regularity of `g` and is not
inferred from the slicewise Ricci-flow predicate.  The conclusion follows by applying
that section to the two pulled-back vector fields; no derivative or evolution identity
is involved. -/
theorem jointMetricPairing_contMDiff_of_jointMetricTensor
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (hmetric : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun p : ℝ × M => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)))
    {U V : Π y : M, TM y}
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% U))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% V)) :
    ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => (g p.1).inner p.2 (U p.2) (V p.2)) := by
  letI : FiberBundle E TM := TangentSpace.fiberBundle
  letI : VectorBundle ℝ E TM := TangentSpace.vectorBundle
  have hUjoint : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun p : ℝ × M => (T% U) p.2) := by
    change ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      ((T% U) ∘ Prod.snd)
    exact hU.comp contMDiff_snd
  have hVjoint : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun p : ℝ × M => (T% V) p.2) := by
    change ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      ((T% V) ∘ Prod.snd)
    exact hV.comp contMDiff_snd
  exact PoincareCurvature.ParametrizedInner.contMDiff_paramBilin_apply₂
    (B := M) (F := E) (E := TM) (b := Prod.snd)
    (ψ := fun p : ℝ × M => (g p.1).inner p.2)
    (v := fun p : ℝ × M => U p.2)
    (w := fun p : ℝ × M => V p.2)
    hmetric hUjoint hVjoint
theorem hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y Z : Π y : M, TM y} (x : M)
    (hjoint : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)))
    (hdotSpace : MDiffAt (fun y : M => hdot y (Y y) (Z y)) x) :
    HasDerivAt
      (fun τ : ℝ => mvfderiv (I := I)
        (fun y : M => (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I) (fun y : M => hdot y (Y y) (Z y)) x (X x)) t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  exact PoincareCurvature.hasDerivAt_mvfderiv_of_joint_contMDiff
    (F := fun τ y => (g τ).inner y (Y y) (Z y))
    (Fdot := fun y => hdot y (Y y) (Z y)) hjoint
    (fun y => hmetric y (Y y) (Z y)) x hdotSpace (X x)
/-- Mixed time--space differentiation for a metric pairing with one moving
section.  The time derivative of the pairing is obtained from the actual
metric velocity and the pointwise velocity of the section; joint spacetime
regularity then permits differentiation in the spatial direction.  This is
one scalar ingredient for the moving Koszul identity, not a connection- or
curvature-evolution assumption. -/
theorem hasDerivAt_metricPairing_mvfderiv_movingLeft_of_jointContMDiff
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {Y : ℝ → Π y : M, TM y} (Ydot : Π y : M, TM y)
    (hYtime : ∀ y : M,
      HasDerivAt (fun τ : ℝ => Y τ y) (Ydot y) t)
    {Z : Π y : M, TM y} (x : M)
    (hjoint : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => (g p.1).inner p.2 (Y p.1 p.2) (Z p.2)))
    (hFdotSpace : MDiffAt
      (fun y : M =>
        hdot y (Y t y) (Z y) + (g t).inner y (Ydot y) (Z y)) x)
    (v : TM x) :
    HasDerivAt
      (fun τ : ℝ => mvfderiv (I := I)
        (fun y : M => (g τ).inner y (Y τ y) (Z y)) x v)
      (mvfderiv (I := I)
        (fun y : M =>
          hdot y (Y t y) (Z y) + (g t).inner y (Ydot y) (Z y)) x v) t := by
  let F : ℝ → M → ℝ := fun τ y => (g τ).inner y (Y τ y) (Z y)
  let Fdot : M → ℝ := fun y =>
    hdot y (Y t y) (Z y) + (g t).inner y (Ydot y) (Z y)
  have hFjoint : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => F p.1 p.2) := by
    simpa [F] using hjoint
  have hFdotTime : ∀ y : M,
      HasDerivAt (fun τ : ℝ => F τ y) (Fdot y) t := by
    intro y
    exact hasDerivAt_metricInner_left_of_pairwise_derivative
      (I := I) (M := M) g hdot (t := t) hmetric y
      (fun τ => Y τ y) (Ydot y) (Z y) (hYtime y)
  have hFdotSpace' : MDiffAt Fdot x := by
    simpa [Fdot] using hFdotSpace
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  simpa [F, Fdot] using
    PoincareCurvature.hasDerivAt_mvfderiv_of_joint_contMDiff
      (I := I) (M := M) F Fdot hFjoint hFdotTime x hFdotSpace' v
/-- Product rule for a spatial differential evaluated on a moving tangent
vector.  The differential itself is obtained from the joint spacetime
regularity of the scalar field; the second term is the ordinary velocity of
the direction vector. -/
theorem hasDerivAt_mvfderiv_apply_movingVector_of_jointContMDiff
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    {t : ℝ} {F : ℝ → M → ℝ} {Fdot : M → ℝ}
    (hFjoint : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => F p.1 p.2))
    (hFdotTime : ∀ y : M,
      HasDerivAt (fun τ : ℝ => F τ y) (Fdot y) t)
    {x : M} (hFdotSpace : MDiffAt Fdot x)
    {V : ℝ → TM x} (Vdot : TM x)
    (hVtime : HasDerivAt (fun τ : ℝ => V τ) Vdot t) :
    HasDerivAt
      (fun τ : ℝ => mvfderiv (I := I) (fun y : M => F τ y) x (V τ))
      (mvfderiv (I := I) Fdot x (V t) +
        mvfderiv (I := I) (fun y : M => F t y) x Vdot) t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  let n : ℕ := Module.finrank ℝ (TM x)
  let b : OrthonormalBasis (Fin n) ℝ (TM x) :=
    stdOrthonormalBasis ℝ (TM x)
  let coeff : ℝ → Fin n → ℝ :=
    fun τ i => Inner.inner ℝ (b i) (V τ)
  let diff : ℝ → Fin n → ℝ :=
    fun τ i => mvfderiv (I := I) (fun y : M => F τ y) x (b i)
  have hcoeff (i : Fin n) :
      HasDerivAt (fun τ : ℝ => coeff τ i)
        (Inner.inner ℝ (b i) Vdot) t := by
    have hb : HasDerivAt (fun _ : ℝ => b i) 0 t :=
      hasDerivAt_const (x := t) (c := b i)
    simpa [coeff] using
      (HasDerivAt.inner (𝕜 := ℝ) (E := TM x) hb hVtime)
  have hdiff (i : Fin n) :
      HasDerivAt (fun τ : ℝ => diff τ i)
        (mvfderiv (I := I) Fdot x (b i)) t := by
    exact PoincareCurvature.hasDerivAt_mvfderiv_of_joint_contMDiff
      (I := I) (M := M) F Fdot hFjoint hFdotTime x hFdotSpace (b i)
  have hterm (i : Fin n) :
      HasDerivAt
        (fun τ : ℝ => coeff τ i * diff τ i)
        (Inner.inner ℝ (b i) Vdot * diff t i +
          coeff t i * mvfderiv (I := I) Fdot x (b i)) t := by
    change HasDerivAt
      ((fun τ : ℝ => coeff τ i) * (fun τ : ℝ => diff τ i))
      (Inner.inner ℝ (b i) Vdot * diff t i +
        coeff t i * mvfderiv (I := I) Fdot x (b i)) t
    exact (hcoeff i).mul (hdiff i)
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun i (_hi : i ∈ Finset.univ) => hterm i)
  have hsumFun :
      (∑ i : Fin n, fun τ : ℝ => coeff τ i * diff τ i) =
        (fun τ : ℝ => ∑ i, coeff τ i * diff τ i) := by
    funext τ
    simp
  rw [hsumFun] at hsum
  have hlin (f : M → ℝ) (w : TM x) :
      mvfderiv (I := I) f x w =
        ∑ i : Fin n, Inner.inner ℝ (b i) w * mvfderiv (I := I) f x (b i) := by
    calc
      mvfderiv (I := I) f x w =
          mvfderiv (I := I) f x
            (∑ i : Fin n, Inner.inner ℝ (b i) w • b i) := by
              exact congrArg (mvfderiv (I := I) f x) (b.sum_repr' w).symm
      _ = ∑ i : Fin n,
          Inner.inner ℝ (b i) w * mvfderiv (I := I) f x (b i) := by
            simp [map_sum, smul_eq_mul]
  have hExpand (τ : ℝ) :
      mvfderiv (I := I) (fun y : M => F τ y) x (V τ) =
        ∑ i : Fin n, coeff τ i * diff τ i := by
    simpa [coeff, diff] using hlin (fun y : M => F τ y) (V τ)
  have htarget := hsum.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun τ => hExpand τ))
  have hderiv :
      (∑ i : Fin n,
        (Inner.inner ℝ (b i) Vdot * diff t i +
          coeff t i * mvfderiv (I := I) Fdot x (b i))) =
        mvfderiv (I := I) (fun y : M => F t y) x Vdot +
          mvfderiv (I := I) Fdot x (V t) := by
    rw [Finset.sum_add_distrib]
    simp only [coeff, diff]
    rw [← hlin (fun y : M => F t y) Vdot, ← hlin Fdot (V t)]
  exact htarget.congr_deriv (hderiv.trans (add_comm _ _))

/-- Moving a section in the right slot of the metric pairing.  This is
obtained from the left-slot product rule using the symmetry of the actual
metric velocity and of each time-slice metric. -/
theorem hasDerivAt_metricInner_right_of_pairwise_derivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (hdotSymm : ∀ (x : M) (u v : TM x), hdot x u v = hdot x v u)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    (x : M) (u : TM x) (σ : ℝ → TM x) (σdot : TM x)
    (hσ : HasDerivAt (fun τ : ℝ => σ τ) σdot t) :
    HasDerivAt (fun τ : ℝ => (g τ).inner x u (σ τ))
      (hdot x u (σ t) + (g t).inner x u σdot) t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hleft :=
    hasDerivAt_metricInner_left_of_pairwise_derivative
      (I := I) (M := M) g hdot (t := t) hmetric x σ σdot u hσ
  have hswap (τ : ℝ) :
      (g τ).inner x u (σ τ) = (g τ).inner x (σ τ) u := by
    letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
    change Inner.inner ℝ u (σ τ) = Inner.inner ℝ (σ τ) u
    exact real_inner_comm _ _
  have hderiv :
      hdot x (σ t) u + (g t).inner x σdot u =
        hdot x u (σ t) + (g t).inner x u σdot := by
    rw [hdotSymm]
    change hdot x u (σ t) + Inner.inner ℝ σdot u =
      hdot x u (σ t) + Inner.inner ℝ u σdot
    rw [real_inner_comm]
  exact (hleft.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ => hswap τ)).congr_deriv hderiv
/-- Time-differentiate the scalar Koszul expression when its middle field
varies in time.  The three spatial metric pairings use genuine joint
spacetime regularity; the two moving Lie brackets use their actual section
velocities.  This is the scalar moving-section bridge needed before metric
duality can produce the connection variation. -/
theorem hasDerivAt_metricKoszulExpression_movingMiddle_of_jointContMDiff
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (hdotSymm : ∀ (x : M) (u v : TM x), hdot x u v = hdot x v u)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Z : Π y : M, TM y} {Y : ℝ → Π y : M, TM y}
    (Ydot : Π y : M, TM y) {x : M}
    (hYtime : ∀ y : M,
      HasDerivAt (fun τ : ℝ => Y τ y) (Ydot y) t)
    (hjointYZ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => (g p.1).inner p.2 (Y p.1 p.2) (Z p.2)))
    (hdotSpaceYZ : MDiffAt
      (fun y : M => hdot y (Y t y) (Z y)) x)
    (hmetricSpaceYdotZ : MDiffAt
      (fun y : M => (g t).inner y (Ydot y) (Z y)) x)
    (hjointXZ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Z p.2)))
    (hdotSpaceXZ : MDiffAt
      (fun y : M => hdot y (X y) (Z y)) x)
    (hjointYX : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => (g p.1).inner p.2 (Y p.1 p.2) (X p.2)))
    (hdotSpaceYX : MDiffAt
      (fun y : M => hdot y (Y t y) (X y)) x)
    (hmetricSpaceYdotX : MDiffAt
      (fun y : M => (g t).inner y (Ydot y) (X y)) x)
    (hbracketYZ : HasDerivAt
      (fun τ : ℝ => VectorField.mlieBracket I (Y τ) Z x)
      (VectorField.mlieBracket I Ydot Z x) t)
    (hbracketXY : HasDerivAt
      (fun τ : ℝ => VectorField.mlieBracket I X (Y τ) x)
      (VectorField.mlieBracket I X Ydot x) t) :
    HasDerivAt
      (fun τ : ℝ => metricKoszulExpression (I := I) (M := M)
        g τ X (Y τ) Z x)
      (metricVelocityKoszulExpression (I := I) (M := M)
          hdot X (Y t) Z x +
        metricKoszulExpression (I := I) (M := M)
          g t X Ydot Z x) t := by
  have hdotSpaceYZ' : MDiffAt
      (fun y : M =>
        hdot y (Y t y) (Z y) + (g t).inner y (Ydot y) (Z y)) x :=
    hdotSpaceYZ.add hmetricSpaceYdotZ
  have hdotSpaceYX' : MDiffAt
      (fun y : M =>
        hdot y (Y t y) (X y) + (g t).inner y (Ydot y) (X y)) x :=
    hdotSpaceYX.add hmetricSpaceYdotX
  have h1 :=
    hasDerivAt_metricPairing_mvfderiv_movingLeft_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric
      (Y := Y) Ydot hYtime (Z := Z) x hjointYZ hdotSpaceYZ' (X x)
  have hdotTimeXZ : ∀ y : M,
      HasDerivAt (fun τ : ℝ => (g τ).inner y (X y) (Z y))
        (hdot y (X y) (Z y)) t := by
    intro y
    exact hmetric y (X y) (Z y)
  have h2 :=
    hasDerivAt_mvfderiv_apply_movingVector_of_jointContMDiff
      (I := I) (M := M) g
      (F := fun τ y => (g τ).inner y (X y) (Z y))
      (Fdot := fun y => hdot y (X y) (Z y))
      (t := t) hjointXZ hdotTimeXZ (x := x) hdotSpaceXZ
      (V := fun τ => Y τ x) (Ydot x) (hYtime x)
  have h3 :=
    hasDerivAt_metricPairing_mvfderiv_movingLeft_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric
      (Y := Y) Ydot hYtime (Z := X) x hjointYX hdotSpaceYX' (Z x)
  have h4 :=
    hasDerivAt_metricInner_right_of_pairwise_derivative
      (I := I) (M := M) g hdot hdotSymm (t := t) hmetric
      x (X x) (fun τ => VectorField.mlieBracket I (Y τ) Z x)
      (VectorField.mlieBracket I Ydot Z x) hbracketYZ
  let bZX : TM x := VectorField.mlieBracket I Z X x
  have h5 :=
    hasDerivAt_metricInner_left_of_pairwise_derivative
      (I := I) (M := M) g hdot (t := t) hmetric x
      (fun τ => Y τ x) (Ydot x) bZX (hYtime x)
  have h6 :=
    hasDerivAt_metricInner_right_of_pairwise_derivative
      (I := I) (M := M) g hdot hdotSymm (t := t) hmetric
      x (Z x) (fun τ => VectorField.mlieBracket I X (Y τ) x)
      (VectorField.mlieBracket I X Ydot x) hbracketXY
  have hswapMetric (τ : ℝ) :
      (fun y : M => (g τ).inner y (X y) (Y τ y)) =
        (fun y : M => (g τ).inner y (Y τ y) (X y)) := by
    funext y
    letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
    change Inner.inner ℝ (X y) (Y τ y) = Inner.inner ℝ (Y τ y) (X y)
    exact real_inner_comm _ _
  have hthirdSwap (τ : ℝ) :
      mvfderiv (I := I) (fun y : M => (g τ).inner y (X y) (Y τ y))
          x (Z x) =
        mvfderiv (I := I) (fun y : M => (g τ).inner y (Y τ y) (X y))
          x (Z x) :=
    congrArg (fun f : M → ℝ => mvfderiv (I := I) f x (Z x))
      (hswapMetric τ)
  let bYZ : ℝ → TM x :=
    fun τ => VectorField.mlieBracket I (Y τ) Z x
  let bXY : ℝ → TM x :=
    fun τ => VectorField.mlieBracket I X (Y τ) x
  let S : ℝ → ℝ := fun τ =>
    mvfderiv (I := I)
      (fun y : M => (g τ).inner y (Y τ y) (Z y)) x (X x) +
    mvfderiv (I := I)
      (fun y : M => (g τ).inner y (X y) (Z y)) x (Y τ x) -
    mvfderiv (I := I)
      (fun y : M => (g τ).inner y (Y τ y) (X y)) x (Z x) -
    (g τ).inner x (X x) (bYZ τ) +
    (g τ).inner x (Y τ x) bZX +
    (g τ).inner x (Z x) (bXY τ)
  let D : ℝ :=
    mvfderiv (I := I)
        (fun y : M =>
          hdot y (Y t y) (Z y) + (g t).inner y (Ydot y) (Z y)) x (X x) +
      (mvfderiv (I := I) (fun y : M => hdot y (X y) (Z y)) x (Y t x) +
        mvfderiv (I := I) (fun y : M => (g t).inner y (X y) (Z y)) x
          (Ydot x)) -
      mvfderiv (I := I)
        (fun y : M =>
          hdot y (Y t y) (X y) + (g t).inner y (Ydot y) (X y)) x (Z x) -
      (hdot x (X x) (bYZ t) +
        (g t).inner x (X x) (VectorField.mlieBracket I Ydot Z x)) +
      (hdot x (Y t x) bZX + (g t).inner x (Ydot x) bZX) +
      (hdot x (Z x) (bXY t) +
        (g t).inner x (Z x) (VectorField.mlieBracket I X Ydot x))
  have hrealAdd :
      Real.instAddCommGroup = Real.normedAddCommGroup.toAddCommGroup := by
    ext a b <;> rfl
  have hrealModule :
      (Semiring.toModule : Module ℝ ℝ) = RCLike.toInnerProductSpaceReal.toModule := by
    ext a b <;> rfl
  have hsum₀ :=
    (((((h1.add h2).sub h3).sub h4).add h5).add h6)
  have hsum : HasDerivAt S D t := by
    convert hsum₀ using 1
    all_goals first
      | exact hrealAdd
      | exact hrealModule
      | (funext τ; simp [S, bYZ, bXY, bZX, add_assoc, sub_eq_add_neg])
      | simp [D, bYZ, bXY, bZX, add_assoc, sub_eq_add_neg]
  have hKfun :
      (fun τ : ℝ => metricKoszulExpression (I := I) (M := M)
        g τ X (Y τ) Z x) = S := by
    funext τ
    simp only [metricKoszulExpression, S, bYZ, bXY, bZX]
    rw [hthirdSwap τ]
  have hK := hsum.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ => congrFun hKfun τ)
  have hdotYXSymm :
      (fun y : M => hdot y (Y t y) (X y)) =
        (fun y : M => hdot y (X y) (Y t y)) := by
    funext y
    exact hdotSymm y (Y t y) (X y)
  have hmetricYdotXSymm :
      (fun y : M => (g t).inner y (Ydot y) (X y)) =
        (fun y : M => (g t).inner y (X y) (Ydot y)) := by
    funext y
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    change Inner.inner ℝ (Ydot y) (X y) = Inner.inner ℝ (X y) (Ydot y)
    exact real_inner_comm _ _
  have hthirdDotSwap :
      mvfderiv (I := I)
          (fun y : M =>
            hdot y (Y t y) (X y) + (g t).inner y (Ydot y) (X y)) x
          (Z x) =
        mvfderiv (I := I)
          (fun y : M =>
            hdot y (X y) (Y t y) + (g t).inner y (X y) (Ydot y)) x
          (Z x) := by
    apply congrArg (fun f : M → ℝ => mvfderiv (I := I) f x (Z x))
    funext y
    calc
      hdot y (Y t y) (X y) + (g t).inner y (Ydot y) (X y) =
          hdot y (X y) (Y t y) + (g t).inner y (Ydot y) (X y) := by
            rw [hdotSymm]
      _ = hdot y (X y) (Y t y) + (g t).inner y (X y) (Ydot y) := by
            rw [congrFun hmetricYdotXSymm y]
  have hmvfAddYZ :
      mvfderiv (I := I)
          (fun y : M =>
            hdot y (Y t y) (Z y) + (g t).inner y (Ydot y) (Z y)) x =
        mvfderiv (I := I) (fun y : M => hdot y (Y t y) (Z y)) x +
          mvfderiv (I := I) (fun y : M => (g t).inner y (Ydot y) (Z y)) x :=
    mvfderiv_add hdotSpaceYZ hmetricSpaceYdotZ
  have hmvfAddYX :
      mvfderiv (I := I)
          (fun y : M =>
            hdot y (Y t y) (X y) + (g t).inner y (Ydot y) (X y)) x =
        mvfderiv (I := I) (fun y : M => hdot y (Y t y) (X y)) x +
          mvfderiv (I := I) (fun y : M => (g t).inner y (Ydot y) (X y)) x :=
    mvfderiv_add hdotSpaceYX hmetricSpaceYdotX
  have hthirdSplitSwap :
      mvfderiv (I := I)
          (fun y : M =>
            hdot y (Y t y) (X y) + (g t).inner y (Ydot y) (X y)) x
          (Z x) =
        mvfderiv (I := I) (fun y : M => hdot y (X y) (Y t y)) x (Z x) +
          mvfderiv (I := I) (fun y : M => (g t).inner y (X y) (Ydot y)) x
            (Z x) := by
    rw [hmvfAddYX]
    rw [show mvfderiv (I := I) (fun y : M => hdot y (Y t y) (X y)) x =
        mvfderiv (I := I) (fun y : M => hdot y (X y) (Y t y)) x from
          congrArg (fun f : M → ℝ => mvfderiv (I := I) f x) hdotYXSymm]
    rw [show mvfderiv (I := I) (fun y : M => (g t).inner y (Ydot y) (X y)) x =
        mvfderiv (I := I) (fun y : M => (g t).inner y (X y) (Ydot y)) x from
          congrArg (fun f : M → ℝ => mvfderiv (I := I) f x) hmetricYdotXSymm]
    simp only [add_apply]
  have hD :
      D = metricVelocityKoszulExpression (I := I) (M := M)
            hdot X (Y t) Z x +
          metricKoszulExpression (I := I) (M := M)
            g t X Ydot Z x := by
    dsimp [D, bYZ, bXY, bZX, metricVelocityKoszulExpression,
      metricKoszulExpression]
    rw [hmvfAddYZ, hthirdSplitSwap]
    simp only [add_apply]
    ring_nf
  exact hK.congr_deriv hD

/- The preceding scalar bridge discharges all three mixed-derivative families in the
finite-dimensional Koszul constructor. -/
theorem exists_hasDerivAt_along_const_of_jointMetricPairingRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y : Π y : M, TM y} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hjointXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)))
    (hdotSpaceXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (Y y) (Z y)) x)
    (hjointYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Z p.2)))
    (hdotSpaceYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (X y) (Z y)) x)
    (hjointZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Y p.2)))
    (hdotSpaceZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (X y) (Y y)) x) :
    ∃ Axy : TM x, HasDerivAt (fun τ : ℝ => (cov τ).along X Y x) Axy t := by
  apply exists_hasDerivAt_along_const_of_koszulExpression
    (I := I) (M := M) g cov hcov hLevi hdot (t := t) hmetric
    (X := X) (Y := Y) (x := x) hX hY
  · intro Z hZ
    have hZ₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z) :=
      hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := X) (Y := Y) (Z := Z)
      x (hjointXYZ Z hZ) (hdotSpaceXYZ Z hZ₁)
  · intro Z hZ
    have hZ₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z) :=
      hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := Y) (Y := X) (Z := Z)
      x (hjointYXZ Z hZ) (hdotSpaceYXZ Z hZ₁)
  · intro Z hZ
    have hZ₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z) :=
      hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := Z) (Y := X) (Z := Y)
      x (hjointZXY Z hZ) (hdotSpaceZXY Z hZ₁)

/- The same replacement can be made at the cyclic level.  Thus the fixed-field
connection velocity used by the geometric evolution interface is obtained from
the actual spacetime metric pairings, rather than from three opaque mixed-
derivative assumptions. -/
theorem exists_hasDerivAt_along_const_with_cyclic_metricVariation_of_jointMetricPairingRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y : Π y : M, TM y} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hjointXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)))
    (hdotSpaceXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (Y y) (Z y)) x)
    (hjointYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Z p.2)))
    (hdotSpaceYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (X y) (Z y)) x)
    (hjointZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Y p.2)))
    (hdotSpaceZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (X y) (Y y)) x) :
    ∃ Axy : TM x,
      HasDerivAt (fun τ : ℝ => (cov τ).along X Y x) Axy t ∧
      ∀ (Z : Π y : M, TM y),
        ContMDiff I (I.prod 𝓘(ℝ, E)) 2
          (fun y ↦ TotalSpace.mk' E y (Z y)) →
        2 * (g t).inner x Axy (Z x) =
          metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t X Y Z x +
            metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t Y X Z x -
            metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t Z X Y x := by
  apply exists_hasDerivAt_along_const_with_cyclic_metricVariation
    (I := I) (M := M) g cov hcov hLevi hdot (t := t) hmetric
    (X := X) (Y := Y) (x := x) hX hY
  · intro Z hZ
    have hZ₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z) :=
      hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := X) (Y := Y) (Z := Z)
      x (hjointXYZ Z hZ) (hdotSpaceXYZ Z hZ₁)
  · intro Z hZ
    have hZ₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z) :=
      hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := Y) (Y := X) (Z := Z)
      x (hjointYXZ Z hZ) (hdotSpaceYXZ Z hZ₁)
  · intro Z hZ
    have hZ₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z) :=
      hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := Z) (Y := X) (Z := Y)
      x (hjointZXY Z hZ) (hdotSpaceZXY Z hZ₁)

end CovariantDerivative.TimeDependentRiemannianMetric
