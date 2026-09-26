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

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckBackgroundFormula
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InverseGramDerivative

/-!
# Local derivative formula for the standard DeTurck field

This file differentiates the genuine local-frame formula for the corrected
standard DeTurck vector field.  It records the inverse-Gram and
Levi-Civita-correction derivative terms separately.  It deliberately stops
before commuting derivatives or identifying a principal part.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Filter
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The `k`-th local-frame coefficient of the explicit Levi-Civita correction
whose two inputs are the `j`-th and `i`-th local tangent-frame vectors. -/
def standardDeTurckCorrectionLocalComponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (k i j : ι) : M → ℝ :=
  fun y =>
    e.localFrameCoeff I b k y
      (explicitLeviCivitaCorrection (I := I) (M := M) g background t y
        (e.localFrame b j y) (e.localFrame b i y))

/-- The `k`-th coefficient of the standard DeTurck field is the local
inverse-Gram contraction of the explicit Levi-Civita correction. -/
theorem standardDeTurckVectorField_localFrameCoeff_eq_sum_correctionComponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) (k : ι) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    e.localFrameCoeff I b k x
        (standardDeTurckVectorField (I := I) (M := M) g background t x) =
      ∑ i : ι, ∑ j : ι,
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j *
          standardDeTurckCorrectionLocalComponent (I := I) (M := M)
            g background t e b k i j x := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  rw [standardDeTurckVectorField_eq_sum_localFrame_inverseGram_explicitLeviCivitaCorrection
    (I := I) (M := M) g background t e b hx]
  simp only [map_sum, map_smul, smul_eq_mul,
    standardDeTurckCorrectionLocalComponent]

/-- **Derivative of a corrected standard DeTurck component in a local frame.**

The first summand differentiates the explicit Levi-Civita correction and the
second differentiates the inverse Gram coefficient.  The latter is written as
`-G⁻¹ (dG) G⁻¹` entrywise.  No derivative commutation, principal-part
identification, or reaction-term assertion is made here. -/
theorem mvfderiv_standardDeTurckVectorField_localFrameCoeff_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (X : TM x) (k : ι)
    (hCorrection : ∀ i j : ι,
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (standardDeTurckCorrectionLocalComponent (I := I) (M := M)
          g background t e b k i j) x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
    mvfderiv (I := I)
        (fun y => e.localFrameCoeff I b k y
          (standardDeTurckVectorField (I := I) (M := M) g background t y)) x X =
      ∑ i : ι, ∑ j : ι, (
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j *
          mvfderiv (I := I)
            (standardDeTurckCorrectionLocalComponent (I := I) (M := M)
              g background t e b k i j) x X +
        standardDeTurckCorrectionLocalComponent (I := I) (M := M)
            g background t e b k i j x *
          (-(
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹ *
            (show Matrix ι ι ℝ from fun p q => mvfderiv (I := I)
              (fun y => CovariantDerivative.localFrameGramMatrix (I := I) e b y p q)
              x X) *
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹)) i j) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let C : ι → ι → M → ℝ := fun i j =>
    standardDeTurckCorrectionLocalComponent (I := I) (M := M)
      g background t e b k i j
  have hC : ∀ i j : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (C i j) x := by
    intro i j
    simpa only [C] using hCorrection i j
  have hInv : ∀ i j : ι, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j) x := by
    intro i j
    have hmatrix := CovariantDerivative.contMDiffOn_localFrameGramMatrix_inv
      (I := I) (E := E) e b e.open_baseSet (fun _ hy => hy)
    rw [contMDiffOn_pi_space] at hmatrix
    have hi := hmatrix i
    rw [contMDiffOn_pi_space] at hi
    exact (hi j x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
      |>.mdifferentiableAt (by norm_num)
  have hterm : ∀ i j : ι, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y =>
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x := by
    intro i j
    exact (hInv i j).mul (hC i j)
  have mdiff_sum (F : ι → M → ℝ)
      (hF : ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (F i) x) :
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ i : ι, F i y) x := by
    classical
    have hsumDiff (s : Finset ι) :
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, F i y) x := by
      induction s using Finset.induction_on with
      | empty => simpa using (mdifferentiableAt_const (c := (0 : ℝ)) (x := x))
      | @insert i s hnot ih =>
          simp only [Finset.sum_insert hnot]
          rw [show (fun y => F i y + ∑ j ∈ s, F j y) =
            F i + (fun y => ∑ j ∈ s, F j y) by rfl]
          exact (hF i).add ih
    simpa using hsumDiff Finset.univ
  have mvfderiv_sum_apply (F : ι → M → ℝ)
      (hF : ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (F i) x) :
      mvfderiv (I := I) (fun y => ∑ i : ι, F i y) x X =
        ∑ i : ι, mvfderiv (I := I) (F i) x X := by
    classical
    have hsumDiff (s : Finset ι) :
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, F i y) x := by
      induction s using Finset.induction_on with
      | empty => simpa using (mdifferentiableAt_const (c := (0 : ℝ)) (x := x))
      | @insert i s hnot ih =>
          simp only [Finset.sum_insert hnot]
          rw [show (fun y => F i y + ∑ j ∈ s, F j y) =
            F i + (fun y => ∑ j ∈ s, F j y) by rfl]
          exact (hF i).add ih
    have hsum (s : Finset ι) :
        mvfderiv (I := I) (fun y => ∑ i ∈ s, F i y) x X =
          ∑ i ∈ s, mvfderiv (I := I) (F i) x X := by
      induction s using Finset.induction_on with
      | empty => simp [mvfderiv_const]
      | @insert i s hnot ih =>
          have hsDiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
              (fun y => ∑ j ∈ s, F j y) x := hsumDiff s
          simp only [Finset.sum_insert hnot]
          rw [show (fun y => F i y + ∑ j ∈ s, F j y) =
            F i + (fun y => ∑ j ∈ s, F j y) by rfl]
          rw [mvfderiv_add (I := I) (hF i) hsDiff]
          simp only [add_apply]
          rw [ih]
    simpa using hsum Finset.univ
  have hsum :
      mvfderiv (I := I)
          (fun y => ∑ i : ι, ∑ j : ι,
            CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x X =
        ∑ i : ι, ∑ j : ι,
          mvfderiv (I := I)
            (fun y =>
              CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x X := by
    have hinnerDiff (i : ι) : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y => ∑ j : ι,
          CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x :=
      mdiff_sum (fun j y =>
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y)
        (fun j => hterm i j)
    have hinner (i : ι) :
        mvfderiv (I := I)
            (fun y => ∑ j : ι,
              CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x X =
          ∑ j : ι, mvfderiv (I := I)
            (fun y =>
              CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x X :=
      mvfderiv_sum_apply (fun j y =>
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y)
        (fun j => hterm i j)
    calc
      mvfderiv (I := I)
          (fun y => ∑ i : ι, ∑ j : ι,
            CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x X =
          ∑ i : ι, mvfderiv (I := I)
            (fun y => ∑ j : ι,
              CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x X :=
        mvfderiv_sum_apply (fun i y => ∑ j : ι,
          CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y)
          hinnerDiff
      _ = ∑ i : ι, ∑ j : ι, mvfderiv (I := I)
            (fun y =>
              CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x X := by
          apply Finset.sum_congr rfl
          intro i _
          exact hinner i
  have hproduct : ∀ i j : ι,
      mvfderiv (I := I)
          (fun y =>
            CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x X =
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j *
          mvfderiv (I := I) (C i j) x X +
        C i j x * mvfderiv (I := I)
          (fun y => CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j) x X := by
    intro i j
    change mvfderiv (I := I)
      ((fun y => CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j) * C i j) x X = _
    have hmul := congrArg (fun L : TM x →L[ℝ] ℝ => L X)
      (mvfderiv_mul (I := I) (hInv i j) (hC i j))
    simpa [smul_eq_mul] using hmul
  have hInvDerivative : ∀ i j : ι,
      mvfderiv (I := I)
          (fun y => CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j) x X =
        (-(
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹ *
          (show Matrix ι ι ℝ from fun p q => mvfderiv (I := I)
            (fun y => CovariantDerivative.localFrameGramMatrix (I := I) e b y p q)
            x X) *
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹)) i j := by
    intro i j
    exact CovariantDerivative.mvfderiv_localFrameInverseGramMatrix_apply
      (I := I) (E := E) e b hx X i j
  have hlocal :
      (fun y => e.localFrameCoeff I b k y
        (standardDeTurckVectorField (I := I) (M := M) g background t y)) =ᶠ[𝓝 x]
        (fun y => ∑ i : ι, ∑ j : ι,
          CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    simpa only [C] using
      standardDeTurckVectorField_localFrameCoeff_eq_sum_correctionComponent
        (I := I) (M := M) g background t e b hy k
  have mvfderiv_eq_of_eventuallyEq_local {f g' : M → ℝ}
      (hfg : f =ᶠ[𝓝 x] g') :
      mvfderiv (I := I) f x = mvfderiv (I := I) g' x := by
    unfold mvfderiv
    rw [hfg.eq_of_nhds, hfg.mfderiv_eq]
    ext v
    rfl
  have hderivEq :
      mvfderiv (I := I)
          (fun y => e.localFrameCoeff I b k y
            (standardDeTurckVectorField (I := I) (M := M) g background t y)) x =
        mvfderiv (I := I)
          (fun y => ∑ i : ι, ∑ j : ι,
            CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x := by
    exact mvfderiv_eq_of_eventuallyEq_local hlocal
  calc
    mvfderiv (I := I)
        (fun y => e.localFrameCoeff I b k y
          (standardDeTurckVectorField (I := I) (M := M) g background t y)) x X =
        mvfderiv (I := I)
          (fun y => ∑ i : ι, ∑ j : ι,
            CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x X := by
          exact congrArg (fun L : TM x →L[ℝ] ℝ => L X) hderivEq
    _ = ∑ i : ι, ∑ j : ι,
          mvfderiv (I := I)
            (fun y =>
              CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j * C i j y) x X := hsum
    _ = ∑ i : ι, ∑ j : ι, (
          CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j *
            mvfderiv (I := I) (C i j) x X +
          C i j x * mvfderiv (I := I)
            (fun y => CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j) x X) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hproduct i j
    _ = ∑ i : ι, ∑ j : ι, (
          CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j *
            mvfderiv (I := I) (C i j) x X +
          C i j x *
            (-(
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹ *
              (show Matrix ι ι ℝ from fun p q => mvfderiv (I := I)
              (fun y => CovariantDerivative.localFrameGramMatrix (I := I) e b y p q)
              x X) *
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹)) i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hInvDerivative i j]
    _ = _ := by rfl

end RicciFlow
