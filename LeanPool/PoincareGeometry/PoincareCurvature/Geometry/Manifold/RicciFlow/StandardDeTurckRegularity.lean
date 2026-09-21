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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurck

/-!
# Spatial regularity of the standard DeTurck vector field

This file proves a local `C¹` regularity statement for the corrected standard
DeTurck vector field.  The proof uses its exact inverse-Gram local-frame
formula and the actual connection difference; it makes no assertion about a
Ricci--DeTurck PDE or about a coordinate reaction term.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- On a trivializing patch, `C¹` regularity of the metric Levi-Civita slice
and the background connection slice gives `C¹` regularity of the corrected
standard DeTurck vector field.  The input hypotheses govern the two actual
connections in `tr_g (∇ᵍ - ∇̄)`, and the inverse metric factors are derived
from the Riemannian metric carried by `g t`. -/
theorem standardDeTurckVectorField_contMDiffOn_of_contMDiffCovariantDerivativeOn
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hchosen : ContMDiffCovariantDerivativeOn E 1
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t).toFun u)
    (hbackground : ContMDiffCovariantDerivativeOn E 1 (background t).toFun u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x
        (standardDeTurckVectorField (I := I) (M := M) g background t x)) u := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  have hInv : ∀ i j, ContMDiffOn I 𝓘(ℝ) 1
      (fun x ↦ CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j) u := by
    intro i j
    have hmatrix := CovariantDerivative.contMDiffOn_localFrameGramMatrix_inv
      (I := I) (E := E) e b hu hu'
    rw [contMDiffOn_pi_space] at hmatrix
    have hi := hmatrix i
    rw [contMDiffOn_pi_space] at hi
    exact (hi j).of_le (by norm_num)
  have hDifference : ∀ i j,
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun x ↦ TotalSpace.mk' E x
          ((CovariantDerivative.difference
            ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
            (e.localFrame b j x)) (e.localFrame b i x))) u := by
    intro i j
    refine (contMDiffOn_iff_localFrameCoeff
      (I := I) (e := e) (b := b) (s := fun x ↦
        (CovariantDerivative.difference
          ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
          (e.localFrame b j x)) (e.localFrame b i x))
      (t := u) (k := (1 : WithTop ℕ∞)) hu hu').2 ?_
    intro k
    exact connectionDifference_localFrameCoeff_contMDiffOn
      (I := I) (M := M)
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t)
      e b hu hu' hchosen hbackground j i k
  have hTerm : ∀ i j,
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun x ↦ TotalSpace.mk' E x
          (CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j •
            ((CovariantDerivative.difference
              ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
              (e.localFrame b j x)) (e.localFrame b i x)))) u := by
    intro i j
    exact (hInv i j).smul_section (hDifference i j)
  have hInner : ∀ i,
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun x ↦ TotalSpace.mk' E x
          (∑ j : ι,
            CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j •
              ((CovariantDerivative.difference
                ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
                (e.localFrame b j x)) (e.localFrame b i x)))) u := by
    intro i
    exact ContMDiffOn.sum_section (s := (Finset.univ : Finset ι))
      (fun j _ ↦ hTerm i j)
  have hSum :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun x ↦ TotalSpace.mk' E x
          (∑ i : ι, ∑ j : ι,
            CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j •
              ((CovariantDerivative.difference
                ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
                (e.localFrame b j x)) (e.localFrame b i x)))) u :=
    ContMDiffOn.sum_section (s := (Finset.univ : Finset ι))
      (fun i _ ↦ hInner i)
  refine hSum.congr ?_
  intro x hx
  congr 1
  simpa using
    (standardDeTurckVectorField_eq_sum_localFrame_inverseGram
      (I := I) (M := M) g background t e b (hu' hx))

/-- A globally `C¹` background connection slice makes the corrected standard
DeTurck vector field spatially `C¹` at every point.  The metric Levi-Civita
slice is supplied by the `C²` metric family itself. -/
theorem standardDeTurckVectorField_contMDiffAt_of_contMDiffCovariantDerivative_background
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y
        (standardDeTurckVectorField (I := I) (M := M) g background t y)) x := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x
  letI : MemTrivializationAtlas e := by infer_instance
  let b := Module.finBasis ℝ E
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt E TM x
  have hchosenOn :
      ContMDiffCovariantDerivativeOn E 1
        ((chosenLeviCivitaFamily (I := I) (M := M) g) t).toFun e.baseSet := by
    letI : CovariantDerivative.ContMDiffCovariantDerivative
        ((chosenLeviCivitaFamily (I := I) (M := M) g) t) 1 :=
      CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
        (I := I) (M := M) g t
    exact CovariantDerivative.contMDiffCovariantDerivativeOn_of_contMDiffCovariantDerivative
      (I := I) (E := E) (u := e.baseSet) e.open_baseSet
  have hbackgroundOn :
      ContMDiffCovariantDerivativeOn E 1 (background t).toFun e.baseSet := by
    letI : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1 := hbackground
    exact CovariantDerivative.contMDiffCovariantDerivativeOn_of_contMDiffCovariantDerivative
      (I := I) (E := E) (u := e.baseSet) e.open_baseSet
  have hOn := standardDeTurckVectorField_contMDiffOn_of_contMDiffCovariantDerivativeOn
    (I := I) (M := M) g background t e b e.open_baseSet (subset_refl _)
    hchosenOn hbackgroundOn
  exact (hOn x hxbase).contMDiffAt (e.open_baseSet.mem_nhds hxbase)

/-- Fixed-time global spatial `C¹` regularity of the corrected standard
DeTurck vector field from a globally `C¹` background connection slice. -/
theorem standardDeTurckVectorField_contMDiff_of_contMDiffCovariantDerivative_background
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y
        (standardDeTurckVectorField (I := I) (M := M) g background t y)) := by
  intro x
  exact standardDeTurckVectorField_contMDiffAt_of_contMDiffCovariantDerivative_background
    (I := I) (M := M) g background t hbackground x

end RicciFlow
