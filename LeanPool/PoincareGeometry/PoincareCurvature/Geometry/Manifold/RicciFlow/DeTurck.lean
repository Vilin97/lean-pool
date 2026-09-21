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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence
/-!
# Intrinsic DeTurck geometry for Ricci flow

This internal file adds the geometric DeTurck data attached to the intrinsic
Ricci-flow boundary from `LocalExistence.lean`.

It defines:

- the trace endomorphism / one-form / vector field built from the difference
  between the chosen Levi-Civita family and a background connection family,
- the corresponding intrinsic DeTurck correction to the metric equation,
- the gauge-fixed Ricci-DeTurck right-hand side and its reduction to intrinsic
  Ricci flow when the background family is Levi-Civita.

These lemmas are proof-bearing preparatory infrastructure only. They do not
complete roadmap point 4 by themselves.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

section ChosenLeviCivita

variable [SigmaCompactSpace M]

/-- The canonical smooth Levi-Civita family attached to `g`. -/
abbrev chosenLeviCivitaFamily
    (g : MetricFamily (I := I) (M := M)) : ConnectionFamily (I := I) (M := M) :=
  CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
    (I := I) (M := M) g

lemma chosenLeviCivitaFamily_isLeviCivita
    (g : MetricFamily (I := I) (M := M)) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g (chosenLeviCivitaFamily (I := I) (M := M) g) :=
  CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
    (I := I) (M := M) g

/-- The traced connection-difference endomorphism whose trace defines the intrinsic DeTurck
one-form. -/
def intrinsicDeTurckTraceEndomorphism
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w : TM x) :
    TM x →L[ℝ] TM x where
  toFun u :=
    (CovariantDerivative.difference
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x u) w
  map_add' u v := by
    exact congrArg
      (fun F : TM x →L[ℝ] TM x => F w)
      ((CovariantDerivative.difference
        ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x).map_add u v)
  map_smul' c u := by
    exact congrArg
      (fun F : TM x →L[ℝ] TM x => F w)
      ((CovariantDerivative.difference
        ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x).map_smul c u)

@[simp] lemma intrinsicDeTurckTraceEndomorphism_apply
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w u : TM x) :
    intrinsicDeTurckTraceEndomorphism (I := I) (M := M) g background t x w u =
      (CovariantDerivative.difference
        ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x u) w := rfl

lemma intrinsicDeTurckTraceEndomorphism_add
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w₁ w₂ : TM x) :
    intrinsicDeTurckTraceEndomorphism (I := I) (M := M) g background t x (w₁ + w₂) =
      intrinsicDeTurckTraceEndomorphism (I := I) (M := M) g background t x w₁ +
        intrinsicDeTurckTraceEndomorphism (I := I) (M := M) g background t x w₂ := by
  ext u
  exact
    ((CovariantDerivative.difference
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x u).map_add w₁ w₂)

lemma intrinsicDeTurckTraceEndomorphism_smul
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (c : ℝ) (w : TM x) :
    intrinsicDeTurckTraceEndomorphism (I := I) (M := M) g background t x (c • w) =
      c • intrinsicDeTurckTraceEndomorphism (I := I) (M := M) g background t x w := by
  ext u
  exact
    ((CovariantDerivative.difference
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x u).map_smul c w)

/-- On zero-dimensional tangent fibers, the endomorphism traced in the DeTurck one-form vanishes. -/
theorem intrinsicDeTurckTraceEndomorphism_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w : TM x) :
    intrinsicDeTurckTraceEndomorphism (I := I) (M := M) g background t x w = 0 := by
  ext u
  exact Subsingleton.elim _ _

/-- The intrinsic DeTurck one-form obtained by tracing the connection-difference endomorphism. -/
def intrinsicDeTurckOneForm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) :
    TM x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w =>
        LinearMap.trace ℝ (TM x)
          (intrinsicDeTurckTraceEndomorphism (I := I) (M := M) g background t x w).toLinearMap
      map_add' := by
        intro w₁ w₂
        calc
          LinearMap.trace ℝ (TM x)
              (intrinsicDeTurckTraceEndomorphism
                (I := I) (M := M) g background t x (w₁ + w₂)).toLinearMap
            = LinearMap.trace ℝ (TM x)
                ((intrinsicDeTurckTraceEndomorphism
                  (I := I) (M := M) g background t x w₁ +
                    intrinsicDeTurckTraceEndomorphism
                      (I := I) (M := M) g background t x w₂).toLinearMap) := by
                rw [intrinsicDeTurckTraceEndomorphism_add]
          _ = LinearMap.trace ℝ (TM x)
                (intrinsicDeTurckTraceEndomorphism
                  (I := I) (M := M) g background t x w₁).toLinearMap +
              LinearMap.trace ℝ (TM x)
                (intrinsicDeTurckTraceEndomorphism
                  (I := I) (M := M) g background t x w₂).toLinearMap := by
                simp [LinearMap.map_add]
      map_smul' := by
        intro c w
        calc
          LinearMap.trace ℝ (TM x)
              (intrinsicDeTurckTraceEndomorphism
                (I := I) (M := M) g background t x (c • w)).toLinearMap
            = LinearMap.trace ℝ (TM x)
                ((c • intrinsicDeTurckTraceEndomorphism
                  (I := I) (M := M) g background t x w).toLinearMap) := by
                rw [intrinsicDeTurckTraceEndomorphism_smul]
          _ = c * LinearMap.trace ℝ (TM x)
                (intrinsicDeTurckTraceEndomorphism
                  (I := I) (M := M) g background t x w).toLinearMap := by
                simp }

@[simp] lemma intrinsicDeTurckOneForm_apply
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w : TM x) :
    intrinsicDeTurckOneForm (I := I) (M := M) g background t x w =
      LinearMap.trace ℝ (TM x)
        (intrinsicDeTurckTraceEndomorphism
          (I := I) (M := M) g background t x w).toLinearMap := by
  simp [intrinsicDeTurckOneForm]

/-- In a local frame, evaluating the intrinsic DeTurck one-form on a frame vector is the
finite trace sum of the diagonal connection-difference coefficients. -/
theorem intrinsicDeTurckOneForm_apply_localFrame_eq_sum_localFrameCoeff
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    intrinsicDeTurckOneForm (I := I) (M := M) g background t x
        (e.localFrame b i x) =
      ∑ j, e.localFrameCoeff I b j x
        ((CovariantDerivative.difference
          ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
          (e.localFrame b j x)) (e.localFrame b i x)) := by
  have hcoeff : ∀ (j : ι) (v : TM x),
      e.localFrameCoeff I b j x v = (e.basisAt b hx).repr v j := by
    intro j v
    let he := e.isLocalFrameOn_localFrame_baseSet I 1 b
    have hbasis : e.basisAt b hx = he.toBasisAt hx := by
      ext k
      simp [IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
        Bundle.Trivialization.basisAt, hx]
    simp [Bundle.Trivialization.localFrameCoeff, IsLocalFrameOn.coeff, hx, hbasis]
  rw [intrinsicDeTurckOneForm_apply]
  rw [LinearMap.trace_eq_matrix_trace ℝ (e.basisAt b hx)]
  simp [Matrix.trace, LinearMap.toMatrix_apply,
    Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hx,
    hcoeff]

/-- On zero-dimensional tangent fibers, the intrinsic DeTurck one-form vanishes. -/
theorem intrinsicDeTurckOneForm_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) :
    intrinsicDeTurckOneForm (I := I) (M := M) g background t x = 0 := by
  ext w
  rw [intrinsicDeTurckOneForm_apply]
  have hEnd :
      (intrinsicDeTurckTraceEndomorphism
        (I := I) (M := M) g background t x w).toLinearMap = 0 := by
    rw [intrinsicDeTurckTraceEndomorphism_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) g background t x w]
    rfl
  simp [hEnd]

/-- Local-frame scalar components of the intrinsic DeTurck one-form suffice to
prove `C¹` regularity of the one-form section. -/
theorem intrinsicDeTurckOneForm_contMDiffOn_of_localFrame_apply
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcoeff : ∀ i,
      ContMDiffOn I 𝓘(ℝ) 1
        (fun x ↦ intrinsicDeTurckOneForm (I := I) (M := M)
          g background t x (e.localFrame b i x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TM y →L[ℝ] ℝ) x
        (intrinsicDeTurckOneForm (I := I) (M := M) g background t x)) u := by
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp
  let eStar :
      Trivialization (E →L[ℝ] ℝ)
        (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) (fun x : M ↦ TM x →L[ℝ] ℝ) → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  refine (contMDiffOn_iff_localFrameCoeff
    (I := I) (e := eStar) (b := CovariantDerivative.continuousDualBasis b)
    (s := intrinsicDeTurckOneForm (I := I) (M := M) g background t)
    (t := u) (k := (1 : WithTop ℕ∞)) hu huStar).2 ?_
  intro i
  refine ContMDiffOn.congr (hcoeff i) ?_
  intro x hx
  have hxE : x ∈ e.baseSet := hu' hx
  have hxStar : x ∈ eStar.baseSet := huStar hx
  rw [show ((LinearMap.piApply
      (eStar.localFrameCoeff I (CovariantDerivative.continuousDualBasis b) i))
      (intrinsicDeTurckOneForm (I := I) (M := M) g background t)) x =
        eStar.localFrameCoeff I (CovariantDerivative.continuousDualBasis b) i x
          (intrinsicDeTurckOneForm (I := I) (M := M) g background t x) by rfl,
    Bundle.Trivialization.localFrameCoeff_eq_coeff
      (I := I) (e := eStar) (b := CovariantDerivative.continuousDualBasis b)
      (s := intrinsicDeTurckOneForm (I := I) (M := M) g background t)
      (hxe := hxStar) (i := i),
    CovariantDerivative.continuousDualBasis_repr]
  simp [eStar, eLine, Bundle.Trivialization.continuousLinearMap_apply,
    Bundle.Trivialization.basisAt, hxE]

/-- Local diagonal connection-difference coefficients imply `C¹` regularity of each scalar
local-frame evaluation of the intrinsic DeTurck one-form. -/
theorem intrinsicDeTurckOneForm_localFrame_apply_contMDiffOn_of_connectionDifference_coeff
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu' : u ⊆ e.baseSet)
    (hcoeff : ∀ i j,
      ContMDiffOn I 𝓘(ℝ) 1
        (fun x ↦ e.localFrameCoeff I b j x
          ((CovariantDerivative.difference
            ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
            (e.localFrame b j x)) (e.localFrame b i x))) u) :
    ∀ i, ContMDiffOn I 𝓘(ℝ) 1
      (fun x ↦ intrinsicDeTurckOneForm (I := I) (M := M)
        g background t x (e.localFrame b i x)) u := by
  intro i
  have hsum :
      ∀ s : Finset ι,
        ContMDiffOn I 𝓘(ℝ) 1
          (fun x ↦ s.sum fun j ↦ e.localFrameCoeff I b j x
            ((CovariantDerivative.difference
              ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
              (e.localFrame b j x)) (e.localFrame b i x))) u := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (contMDiffOn_const :
        ContMDiffOn I 𝓘(ℝ) 1 (fun _ : M ↦ (0 : ℝ)) u)
    · intro j s hj hs
      have hadd :
          ContMDiffOn I 𝓘(ℝ) 1
            (fun x ↦
              e.localFrameCoeff I b j x
                ((CovariantDerivative.difference
                  ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
                  (e.localFrame b j x)) (e.localFrame b i x)) +
              s.sum (fun j' ↦ e.localFrameCoeff I b j' x
                ((CovariantDerivative.difference
                  ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
                  (e.localFrame b j' x)) (e.localFrame b i x)))) u :=
        (hcoeff i j).add hs
      refine ContMDiffOn.congr hadd ?_
      intro x hx
      simp [Finset.sum_insert, hj]
  refine ContMDiffOn.congr (hsum Finset.univ) ?_
  intro x hx
  exact intrinsicDeTurckOneForm_apply_localFrame_eq_sum_localFrameCoeff
    (I := I) (M := M) g background t e b (hu' hx) i

/-- Local diagonal connection-difference coefficient regularity packages into `C¹` regularity of the
intrinsic DeTurck one-form section. -/
theorem intrinsicDeTurckOneForm_contMDiffOn_of_connectionDifference_coeff
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcoeff : ∀ i j,
      ContMDiffOn I 𝓘(ℝ) 1
        (fun x ↦ e.localFrameCoeff I b j x
          ((CovariantDerivative.difference
            ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
            (e.localFrame b j x)) (e.localFrame b i x))) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TM y →L[ℝ] ℝ) x
        (intrinsicDeTurckOneForm (I := I) (M := M) g background t x)) u := by
  exact intrinsicDeTurckOneForm_contMDiffOn_of_localFrame_apply
    (I := I) (M := M) g background t e b hu hu'
    (intrinsicDeTurckOneForm_localFrame_apply_contMDiffOn_of_connectionDifference_coeff
      (I := I) (M := M) g background t e b hu' hcoeff)

/-- If two tangent covariant derivatives are `C¹` on a local frame domain, then each local-frame
coefficient of their difference tensor is `C¹`. -/
theorem connectionDifference_localFrameCoeff_contMDiffOn
    (cov cov' : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun u)
    (hcov' : ContMDiffCovariantDerivativeOn E 1 cov'.toFun u)
    (a d c : ι) :
    ContMDiffOn I 𝓘(ℝ) 1
      (fun x ↦ e.localFrameCoeff I b c x
        ((CovariantDerivative.difference cov cov' x (e.localFrame b a x))
          (e.localFrame b d x))) u := by
  have hframeA₂ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun x ↦ TotalSpace.mk' E x (e.localFrame b a x)) u :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
      (n := (2 : WithTop ℕ∞)) (b := b) a).mono hu'
  have hframeD₁ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun x ↦ TotalSpace.mk' E x (e.localFrame b d x)) u :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
      (n := (1 : WithTop ℕ∞)) (b := b) d).mono hu'
  have hcovA :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun y : M ↦ TM y →L[ℝ] TM y) x
          (cov (e.localFrame b a) x)) u :=
    hcov.contMDiff hframeA₂
  have hcovA' :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun y : M ↦ TM y →L[ℝ] TM y) x
          (cov' (e.localFrame b a) x)) u :=
    hcov'.contMDiff hframeA₂
  have hcovApply :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun x ↦ TotalSpace.mk' E x
          ((cov (e.localFrame b a) x) (e.localFrame b d x))) u := by
    simpa using hcovA.clm_bundle_apply hframeD₁
  have hcovApply' :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun x ↦ TotalSpace.mk' E x
          ((cov' (e.localFrame b a) x) (e.localFrame b d x))) u := by
    simpa using hcovA'.clm_bundle_apply hframeD₁
  have hcovCoeff :
      ContMDiffOn I 𝓘(ℝ) 1
        (fun x ↦ e.localFrameCoeff I b c x
          ((cov (e.localFrame b a) x) (e.localFrame b d x))) u :=
    contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b)
      hu hu' hcovApply c
  have hcovCoeff' :
      ContMDiffOn I 𝓘(ℝ) 1
        (fun x ↦ e.localFrameCoeff I b c x
          ((cov' (e.localFrame b a) x) (e.localFrame b d x))) u :=
    contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b)
      hu hu' hcovApply' c
  refine ContMDiffOn.congr (hcovCoeff.sub hcovCoeff') ?_
  intro x hx
  have hframeAt :
      MDiffAt (T% (e.localFrame b a)) x :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := (1 : WithTop ℕ∞)) a (hu' hx)).mdifferentiableAt one_ne_zero
  have hdiff :
      cov.difference cov' x (e.localFrame b a x) =
        cov (e.localFrame b a) x - cov' (e.localFrame b a) x := by
    simpa [CovariantDerivative.difference] using
      (IsCovariantDerivativeOn.difference_apply
        (hcov := cov.isCovariantDerivativeOnUniv)
        (hcov' := cov'.isCovariantDerivativeOnUniv)
        (x := x) (s := Set.univ) (hx := by trivial)
        (σ := e.localFrame b a) (hσ := hframeAt))
  rw [hdiff]
  exact (e.localFrameCoeff I b c x).map_sub
    ((cov (e.localFrame b a) x) (e.localFrame b d x))
    ((cov' (e.localFrame b a) x) (e.localFrame b d x))

/-- Local `C¹` regularity of the chosen Levi-Civita slice and background connection slice implies
`C¹` regularity of the intrinsic DeTurck one-form section. -/
theorem intrinsicDeTurckOneForm_contMDiffOn_of_contMDiffCovariantDerivativeOn
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
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TM y →L[ℝ] ℝ) x
        (intrinsicDeTurckOneForm (I := I) (M := M) g background t x)) u := by
  refine intrinsicDeTurckOneForm_contMDiffOn_of_connectionDifference_coeff
    (I := I) (M := M) g background t e b hu hu' ?_
  intro i j
  exact connectionDifference_localFrameCoeff_contMDiffOn
    (I := I) (M := M)
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t)
    e b hu hu' hchosen hbackground j i j

/-- The intrinsic DeTurck vector field obtained by raising the intrinsic DeTurck one-form with the
evolving metric. -/
def intrinsicDeTurckVectorField
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    CovariantDerivative.TimeDependentVectorField (I := I) (M := M) :=
  fun t x ↦ by
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    exact CovariantDerivative.rieszMap (I := I) x
      (intrinsicDeTurckOneForm (I := I) (M := M) g background t x)

@[simp] lemma intrinsicDeTurckVectorField_apply
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) :
    intrinsicDeTurckVectorField (I := I) (M := M) g background t x = by
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact CovariantDerivative.rieszMap (I := I) x
        (intrinsicDeTurckOneForm (I := I) (M := M) g background t x) := rfl

/-- If the traced intrinsic DeTurck one-form is `C¹` at a fixed time, then
raising it with the time-slice metric gives a differentiable intrinsic DeTurck
vector-field section. -/
theorem intrinsicDeTurckVectorField_mdiffAt_of_contMDiff_intrinsicDeTurckOneForm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hω : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TM y →L[ℝ] ℝ) x
        (intrinsicDeTurckOneForm (I := I) (M := M) g background t x)))
    (x : M) :
    MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) x := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let e := trivializationAt E TM x
  letI : MemTrivializationAtlas e := by infer_instance
  let b := Module.finBasis ℝ E
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt E TM x
  have hωon :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun z : M ↦ TM z →L[ℝ] ℝ) y
          (intrinsicDeTurckOneForm (I := I) (M := M) g background t y)) e.baseSet :=
    hω.contMDiffOn
  have hW :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y
          (CovariantDerivative.rieszMap (I := I) y
            (intrinsicDeTurckOneForm (I := I) (M := M) g background t y))) e.baseSet :=
    CovariantDerivative.contMDiffOn_rieszMap_section
      (I := I) (E := E) (M := M) (e := e) (b := b)
      e.open_baseSet (by intro y hy; exact hy) hωon
  have hWat :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y
          (CovariantDerivative.rieszMap (I := I) y
            (intrinsicDeTurckOneForm (I := I) (M := M) g background t y))) x :=
    (hW x hxbase).contMDiffAt (e.open_baseSet.mem_nhds hxbase)
  simpa [intrinsicDeTurckVectorField] using hWat.mdifferentiableAt one_ne_zero

/-- Local version of
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiff_intrinsicDeTurckOneForm`. -/
theorem intrinsicDeTurckVectorField_mdiffAt_of_contMDiffOn_intrinsicDeTurckOneForm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hω : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TM y →L[ℝ] ℝ) x
        (intrinsicDeTurckOneForm (I := I) (M := M) g background t x)) u)
    {x : M} (hx : x ∈ u) :
    MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) x := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  have hxbase : x ∈ e.baseSet := hu' hx
  have hωon :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun z : M ↦ TM z →L[ℝ] ℝ) y
          (intrinsicDeTurckOneForm (I := I) (M := M) g background t y)) u :=
    hω
  have hW :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y
          (CovariantDerivative.rieszMap (I := I) y
            (intrinsicDeTurckOneForm (I := I) (M := M) g background t y))) u :=
    CovariantDerivative.contMDiffOn_rieszMap_section
      (I := I) (E := E) (M := M) (e := e) (b := b)
      hu hu' hωon
  have hWat :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y
          (CovariantDerivative.rieszMap (I := I) y
            (intrinsicDeTurckOneForm (I := I) (M := M) g background t y))) x :=
    (hW x hx).contMDiffAt (hu.mem_nhds hx)
  simpa [intrinsicDeTurckVectorField] using hWat.mdifferentiableAt one_ne_zero

/-- **`C¹` regularity (undowngraded) of the raised intrinsic DeTurck vector field on a patch.**
The `ContMDiffOn` strengthening of
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiffOn_intrinsicDeTurckOneForm`: exactly the rieszMap
section regularity that lemma establishes internally (via
`CovariantDerivative.contMDiffOn_rieszMap_section`) before discarding it to mere pointwise
differentiability.  If the traced intrinsic DeTurck one-form is `C¹` on an open patch `u` of a
trivialization `e`, then raising it with the time-slice metric gives a `C¹` intrinsic DeTurck
vector-field section on `u`.  This is the regularity input a covariant-derivative-regularity step
(`ContMDiffCovariantDerivativeOn.contMDiff`) consumes for the DeTurck correction. -/
theorem intrinsicDeTurckVectorField_contMDiffOn_of_contMDiffOn_intrinsicDeTurckOneForm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hω : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TM y →L[ℝ] ℝ) x
        (intrinsicDeTurckOneForm (I := I) (M := M) g background t x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (T% (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) u := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  have hW :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y
          (CovariantDerivative.rieszMap (I := I) y
            (intrinsicDeTurckOneForm (I := I) (M := M) g background t y))) u :=
    CovariantDerivative.contMDiffOn_rieszMap_section
      (I := I) (E := E) (M := M) (e := e) (b := b)
      hu hu' hω
  simpa [intrinsicDeTurckVectorField] using hW

/-- **`C¹` regularity (undowngraded) of the raised intrinsic DeTurck vector field at a point.**
The `ContMDiffAt` strengthening of
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiff_intrinsicDeTurckOneForm`: from a globally `C¹`
traced intrinsic DeTurck one-form, raising it with the time-slice metric gives a `C¹` intrinsic
DeTurck vector-field section at each point (proved in the trivialization at `x`). -/
theorem intrinsicDeTurckVectorField_contMDiffAt_of_contMDiff_intrinsicDeTurckOneForm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hω : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TM y →L[ℝ] ℝ) x
        (intrinsicDeTurckOneForm (I := I) (M := M) g background t x)))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (T% (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) x := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let e := trivializationAt E TM x
  letI : MemTrivializationAtlas e := by infer_instance
  let b := Module.finBasis ℝ E
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt E TM x
  have hωon :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun z : M ↦ TM z →L[ℝ] ℝ) y
          (intrinsicDeTurckOneForm (I := I) (M := M) g background t y)) e.baseSet :=
    hω.contMDiffOn
  have hW :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y
          (CovariantDerivative.rieszMap (I := I) y
            (intrinsicDeTurckOneForm (I := I) (M := M) g background t y))) e.baseSet :=
    CovariantDerivative.contMDiffOn_rieszMap_section
      (I := I) (E := E) (M := M) (e := e) (b := b)
      e.open_baseSet (fun _ hy ↦ hy) hωon
  have hWat :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y
          (CovariantDerivative.rieszMap (I := I) y
            (intrinsicDeTurckOneForm (I := I) (M := M) g background t y))) x :=
    (hW x hxbase).contMDiffAt (e.open_baseSet.mem_nhds hxbase)
  simpa [intrinsicDeTurckVectorField] using hWat

/-- Local diagonal connection-difference coefficient regularity implies differentiability of the
raised intrinsic DeTurck vector field at points of the coordinate patch. -/
theorem intrinsicDeTurckVectorField_mdiffAt_of_connectionDifference_coeff
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcoeff : ∀ i j,
      ContMDiffOn I 𝓘(ℝ) 1
        (fun x ↦ e.localFrameCoeff I b j x
          ((CovariantDerivative.difference
            ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
            (e.localFrame b j x)) (e.localFrame b i x))) u)
    {x : M} (hx : x ∈ u) :
    MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) x := by
  have hω :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun z : M ↦ TM z →L[ℝ] ℝ) y
          (intrinsicDeTurckOneForm (I := I) (M := M) g background t y)) u :=
    intrinsicDeTurckOneForm_contMDiffOn_of_connectionDifference_coeff
      (I := I) (M := M) g background t e b hu hu' hcoeff
  exact intrinsicDeTurckVectorField_mdiffAt_of_contMDiffOn_intrinsicDeTurckOneForm
    (I := I) (M := M) g background t e b hu hu' hω hx

/-- Local `C¹` regularity of the chosen Levi-Civita slice and background connection slice implies
differentiability of the raised intrinsic DeTurck vector field on the patch. -/
theorem intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivativeOn
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hchosen : ContMDiffCovariantDerivativeOn E 1
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t).toFun u)
    (hbackground : ContMDiffCovariantDerivativeOn E 1 (background t).toFun u)
    {x : M} (hx : x ∈ u) :
    MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) x := by
  have hcoeff : ∀ i j,
      ContMDiffOn I 𝓘(ℝ) 1
        (fun x ↦ e.localFrameCoeff I b j x
          ((CovariantDerivative.difference
            ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
            (e.localFrame b j x)) (e.localFrame b i x))) u := by
    intro i j
    exact connectionDifference_localFrameCoeff_contMDiffOn
      (I := I) (M := M)
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t)
      e b hu hu' hchosen hbackground j i j
  exact intrinsicDeTurckVectorField_mdiffAt_of_connectionDifference_coeff
    (I := I) (M := M) g background t e b hu hu' hcoeff hx

/-- A globally `C¹` background connection slice gives differentiability of the raised intrinsic
DeTurck vector field at every point of that fixed time slice. -/
theorem intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivative_background
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) :
    MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) x := by
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
  exact intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivativeOn
    (I := I) (M := M) g background t e b e.open_baseSet (subset_refl _)
    hchosenOn hbackgroundOn hxbase

/-- Fixed-time global version of
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivative_background`. -/
theorem intrinsicDeTurckVectorField_mdiff_of_contMDiffCovariantDerivative_background
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    MDiff (T% (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) := by
  intro x
  exact intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivative_background
    (I := I) (M := M) g background t hbackground x

/-- **`ContMDiffOn` (undowngraded) DeTurck vector field from local connection-difference coefficient
regularity.**  The `ContMDiffOn` strengthening of
`intrinsicDeTurckVectorField_mdiffAt_of_connectionDifference_coeff`, obtained by feeding the
`ContMDiffOn` DeTurck one-form (from `intrinsicDeTurckOneForm_contMDiffOn_of_connectionDifference_coeff`)
into `intrinsicDeTurckVectorField_contMDiffOn_of_contMDiffOn_intrinsicDeTurckOneForm`. -/
theorem intrinsicDeTurckVectorField_contMDiffOn_of_connectionDifference_coeff
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcoeff : ∀ i j,
      ContMDiffOn I 𝓘(ℝ) 1
        (fun x ↦ e.localFrameCoeff I b j x
          ((CovariantDerivative.difference
            ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
            (e.localFrame b j x)) (e.localFrame b i x))) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (T% (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) u := by
  have hω :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun z : M ↦ TM z →L[ℝ] ℝ) y
          (intrinsicDeTurckOneForm (I := I) (M := M) g background t y)) u :=
    intrinsicDeTurckOneForm_contMDiffOn_of_connectionDifference_coeff
      (I := I) (M := M) g background t e b hu hu' hcoeff
  exact intrinsicDeTurckVectorField_contMDiffOn_of_contMDiffOn_intrinsicDeTurckOneForm
    (I := I) (M := M) g background t e b hu hu' hω

/-- **`ContMDiffOn` (undowngraded) DeTurck vector field from `C¹` chosen Levi-Civita and background
connection slices on a patch.**  The `ContMDiffOn` strengthening of
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivativeOn`. -/
theorem intrinsicDeTurckVectorField_contMDiffOn_of_contMDiffCovariantDerivativeOn
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
      (T% (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) u := by
  have hcoeff : ∀ i j,
      ContMDiffOn I 𝓘(ℝ) 1
        (fun x ↦ e.localFrameCoeff I b j x
          ((CovariantDerivative.difference
            ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
            (e.localFrame b j x)) (e.localFrame b i x))) u := by
    intro i j
    exact connectionDifference_localFrameCoeff_contMDiffOn
      (I := I) (M := M)
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t)
      e b hu hu' hchosen hbackground j i j
  exact intrinsicDeTurckVectorField_contMDiffOn_of_connectionDifference_coeff
    (I := I) (M := M) g background t e b hu hu' hcoeff

/-- **`ContMDiffAt` (undowngraded) DeTurck vector field from a globally `C¹` background connection
slice.**  The `ContMDiffAt` strengthening of
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivative_background`: the chosen
Levi-Civita slice is `C¹` from the ambient bundle structure, so a `C¹` background connection slice
yields a `C¹` intrinsic DeTurck vector-field section at every point. -/
theorem intrinsicDeTurckVectorField_contMDiffAt_of_contMDiffCovariantDerivative_background
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (T% (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) x := by
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
  have hOn := intrinsicDeTurckVectorField_contMDiffOn_of_contMDiffCovariantDerivativeOn
    (I := I) (M := M) g background t e b e.open_baseSet (subset_refl _)
    hchosenOn hbackgroundOn
  exact (hOn x hxbase).contMDiffAt (e.open_baseSet.mem_nhds hxbase)

/-- **Fixed-time global `ContMDiff` (undowngraded) DeTurck vector field from a globally `C¹`
background connection slice.**  The `ContMDiff` strengthening of
`intrinsicDeTurckVectorField_mdiff_of_contMDiffCovariantDerivative_background`.  This is the
end-to-end `C¹` regularity of the intrinsic DeTurck vector field consumed by the covariant-derivative
regularity step for the DeTurck correction. -/
theorem intrinsicDeTurckVectorField_contMDiff_of_contMDiffCovariantDerivative_background
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (T% (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) := by
  intro x
  exact intrinsicDeTurckVectorField_contMDiffAt_of_contMDiffCovariantDerivative_background
    (I := I) (M := M) g background t hbackground x

/-- Global version of
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiff_intrinsicDeTurckOneForm`. -/
theorem intrinsicDeTurckVectorField_mdiff_of_contMDiff_intrinsicDeTurckOneForm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hω : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TM y →L[ℝ] ℝ) x
        (intrinsicDeTurckOneForm (I := I) (M := M) g background t x))) :
    MDiff (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) := by
  intro x
  exact intrinsicDeTurckVectorField_mdiffAt_of_contMDiff_intrinsicDeTurckOneForm
    (I := I) (M := M) g background t hω x

/-- On zero-dimensional tangent fibers, the intrinsic DeTurck vector field vanishes. -/
theorem intrinsicDeTurckVectorField_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    intrinsicDeTurckVectorField (I := I) (M := M) g background = 0 := by
  funext t x
  exact Subsingleton.elim _ _

/-- The symmetrized covariant derivative of the intrinsic DeTurck vector field. -/
def intrinsicDeTurckCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    MetricTensorFamily (I := I) (M := M) :=
  fun t x u v ↦ by
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    exact
      (g t).inner x
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x u) v +
      (g t).inner x u
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x v)

@[simp] lemma intrinsicDeTurckCorrection_apply
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v = by
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact
        (g t).inner x
          (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
            (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x u) v +
        (g t).inner x u
          (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
            (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x v) := rfl

/-- The DeTurck correction is symmetric in its two tangent slots. -/
theorem intrinsicDeTurckCorrection_symm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v =
      intrinsicDeTurckCorrection (I := I) (M := M) g background t x v u := by
  rw [intrinsicDeTurckCorrection_apply, intrinsicDeTurckCorrection_apply]
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let nablaW :=
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t)
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x
  have h₁ : (g t).inner x (nablaW u) v = (g t).inner x v (nablaW u) := (g t).symm x _ _
  have h₂ : (g t).inner x u (nablaW v) = (g t).inner x (nablaW v) u := (g t).symm x _ _
  rw [h₁, h₂]
  abel

/-- The DeTurck correction vanishes on zero-dimensional tangent fibers, for any background. -/
theorem intrinsicDeTurckCorrection_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v = 0 := by
  rw [intrinsicDeTurckCorrection_apply]
  have hleft :
      (g t).inner x
          (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
            (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x u) v = 0 := by
    simpa [metricTensor] using
      metricTensor_eq_zero_of_subsingleton_tangent
        (I := I) (M := M) g t x
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x u) v
  have hright :
      (g t).inner x u
          (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
            (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x v) = 0 := by
    simpa [metricTensor] using
      metricTensor_eq_zero_of_subsingleton_tangent
        (I := I) (M := M) g t x u
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x v)
  simp [hleft, hright]

/-- The intrinsic Ricci-DeTurck right-hand side obtained by adding the DeTurck correction to the
intrinsic Ricci-flow right-hand side. -/
def intrinsicRicciDeTurckRHS
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    MetricTensorFamily (I := I) (M := M) :=
  fun t x u v ↦
    intrinsicRicciFlowRHS (I := I) (M := M) g t x u v +
      intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v

@[simp] lemma intrinsicRicciDeTurckRHS_apply
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M) g t x u v +
        intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v := rfl

/-- The intrinsic Ricci-DeTurck right-hand side is symmetric whenever the intrinsic Ricci-flow
right-hand side is symmetric. This isolates the remaining Ricci-symmetry input from the already
proved symmetry of the DeTurck correction term. -/
theorem intrinsicRicciDeTurckRHS_symm_of_intrinsicRicciFlowRHS_symm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hRicciSymm : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciFlowRHS (I := I) (M := M) g t x u v =
        intrinsicRicciFlowRHS (I := I) (M := M) g t x v u)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v =
      intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x v u := by
  rw [intrinsicRicciDeTurckRHS_apply, intrinsicRicciDeTurckRHS_apply,
    hRicciSymm t x u v,
    intrinsicDeTurckCorrection_symm (I := I) (M := M) g background t x u v]

/-- Symmetry of the intrinsic Ricci tensor implies symmetry of the full intrinsic Ricci-DeTurck
right-hand side. The DeTurck correction part is handled by
`intrinsicDeTurckCorrection_symm`, so this exposes the exact remaining tensor-symmetry input. -/
theorem intrinsicRicciDeTurckRHS_symm_of_intrinsicRicciTensor_symm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hRicciSymm : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) g t x u v =
        intrinsicRicciTensor (I := I) (M := M) g t x v u)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v =
      intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x v u := by
  exact intrinsicRicciDeTurckRHS_symm_of_intrinsicRicciFlowRHS_symm
    (I := I) (M := M) g background
    (intrinsicRicciFlowRHS_symm_of_intrinsicRicciTensor_symm
      (I := I) (M := M) g hRicciSymm)
    t x u v

/-- Curvature pair symmetry for the chosen Levi-Civita family implies symmetry of the full
intrinsic Ricci-DeTurck right-hand side. This combines the algebraic Ricci-symmetry contraction
bridge with the already symmetric DeTurck correction term. -/
theorem intrinsicRicciDeTurckRHS_symm_of_curvature_inner_pair_symm
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hpair : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      letI : CovariantDerivative.ContMDiffCovariantDerivative
          (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
            (I := I) (M := M) g t) 1 :=
        CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g t;
      ∀ (a b c d : TM x),
        Inner.inner ℝ
            (CovariantDerivative.curvatureTensor
              (cov := CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
                (I := I) (M := M) g t) x a b c) d =
          Inner.inner ℝ
            (CovariantDerivative.curvatureTensor
              (cov := CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
                (I := I) (M := M) g t) x c d a) b)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v =
      intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x v u := by
  exact intrinsicRicciDeTurckRHS_symm_of_intrinsicRicciTensor_symm
    (I := I) (M := M) g background
    (intrinsicRicciTensor_symm_of_curvature_inner_pair_symm
      (I := I) (M := M) g hpair)
    t x u v

/-- Skew-adjointness of the chosen Levi-Civita curvature operators implies symmetry of the full
intrinsic Ricci-DeTurck right-hand side. This is the version aimed directly at the
metric-compatibility curvature identity. -/
theorem intrinsicRicciDeTurckRHS_symm_of_curvature_inner_skew_adjoint
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hskew : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      letI : CovariantDerivative.ContMDiffCovariantDerivative
          (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
            (I := I) (M := M) g t) 1 :=
        CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g t;
      ∀ (a b c d : TM x),
        Inner.inner ℝ
            (CovariantDerivative.curvatureTensor
              (cov := CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
                (I := I) (M := M) g t) x a b c) d +
          Inner.inner ℝ c
            (CovariantDerivative.curvatureTensor
              (cov := CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
                (I := I) (M := M) g t) x a b d) = 0)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v =
      intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x v u := by
  exact intrinsicRicciDeTurckRHS_symm_of_intrinsicRicciTensor_symm
    (I := I) (M := M) g background
      (intrinsicRicciTensor_symm_of_curvature_inner_skew_adjoint
        (I := I) (M := M) g hskew)
    t x u v

/-- The intrinsic Ricci-DeTurck right-hand side is symmetric, using the chosen smooth
Levi-Civita family for the Ricci term and the symmetric DeTurck correction. -/
theorem intrinsicRicciDeTurckRHS_symm
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v =
      intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x v u := by
  exact intrinsicRicciDeTurckRHS_symm_of_intrinsicRicciFlowRHS_symm
    (I := I) (M := M) g background
    (intrinsicRicciFlowRHS_symm (I := I) (M := M) g)
    t x u v

theorem intrinsicRicciDeTurckRHS_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v = 0 := by
  rw [intrinsicRicciDeTurckRHS_apply,
    intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent (I := I) (M := M) g t x u v,
    intrinsicDeTurckCorrection_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) g background t x u v]
  norm_num

theorem intrinsicDeTurckTraceEndomorphism_eq_zero_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    (t : ℝ) (x : M) (w : TM x) :
    intrinsicDeTurckTraceEndomorphism (I := I) (M := M) g background t x w = 0 := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hdiff :
      CovariantDerivative.difference
        ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) = 0 := by
    exact CovariantDerivative.difference_eq_zero_of_isLeviCivita
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t))
      (background t)
      ((chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g) t)
      (hbackground t)
  ext u
  have hzero :
      (CovariantDerivative.difference
        ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x u) w = 0 := by
    simpa using congrArg
      (fun D => D x u w)
      hdiff
  simpa [intrinsicDeTurckTraceEndomorphism] using hzero

theorem intrinsicDeTurckOneForm_eq_zero_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    (t : ℝ) (x : M) :
    intrinsicDeTurckOneForm (I := I) (M := M) g background t x = 0 := by
  ext w
  rw [intrinsicDeTurckOneForm_apply]
  simpa using congrArg
    (fun A => LinearMap.trace ℝ (TM x) A.toLinearMap)
    (intrinsicDeTurckTraceEndomorphism_eq_zero_of_isLeviCivita
      (I := I) (M := M) (g := g) (background := background)
      (hbackground := hbackground) (t := t) (x := x) (w := w))

theorem intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    intrinsicDeTurckVectorField (I := I) (M := M) g background = 0 := by
  funext t x
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hone :
      intrinsicDeTurckOneForm (I := I) (M := M) g background t x = 0 :=
    intrinsicDeTurckOneForm_eq_zero_of_isLeviCivita
      (I := I) (M := M) g background hbackground t x
  simp [intrinsicDeTurckVectorField, hone]

/-- With a Levi-Civita background, the intrinsic DeTurck vector field is the zero
section, hence it satisfies the pointwise differentiability hypothesis needed
by covariant-derivative and Lie-correction arguments. -/
theorem intrinsicDeTurckVectorField_mdiffAt_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    (t : ℝ) (x : M) :
    MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) x := by
  have hW :
      intrinsicDeTurckVectorField (I := I) (M := M) g background t = 0 := by
    exact congrArg (fun W => W t)
      (intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
        (I := I) (M := M) g background hbackground)
  rw [hW]
  change MDiffAt (Bundle.zeroSection (B := M) E (TangentSpace I : M → Type _)) x
  exact mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := E) (E := TM) (x := x)

/-- Global version of
`intrinsicDeTurckVectorField_mdiffAt_of_isLeviCivita`. -/
theorem intrinsicDeTurckVectorField_mdiff_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    (t : ℝ) :
    MDiff (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) := by
  intro x
  exact intrinsicDeTurckVectorField_mdiffAt_of_isLeviCivita
    (I := I) (M := M) g background hbackground t x

theorem intrinsicDeTurckCorrection_eq_zero_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    intrinsicDeTurckCorrection (I := I) (M := M) g background = 0 := by
  funext t x u v
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hvector :
      intrinsicDeTurckVectorField (I := I) (M := M) g background t = 0 := by
    exact congrArg
      (fun W => W t)
      (intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
        (I := I) (M := M) g background hbackground)
  have hcovZero :
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x) = 0 := by
    rw [hvector]
    exact congrArg
      (fun A => A x)
      (CovariantDerivative.zero
        (cov := ((chosenLeviCivitaFamily (I := I) (M := M) g) t)))
  have hcovU :
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x u) = 0 := by
    simpa using congrArg (fun A => A u) hcovZero
  have hcovV :
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x v) = 0 := by
    simpa using congrArg (fun A => A v) hcovZero
  rw [intrinsicDeTurckCorrection_apply, hcovU, hcovV]
  simp

theorem intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background =
      intrinsicRicciFlowRHS (I := I) (M := M) g := by
  funext t x u v
  have hcorr :
      intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v = 0 := by
    simpa using congrArg
      (fun F => F t x u v)
      (intrinsicDeTurckCorrection_eq_zero_of_isLeviCivita
            (I := I) (M := M) g background hbackground)
  rw [intrinsicRicciDeTurckRHS_apply, hcorr, add_zero]

/-- **Self-DeTurck reduction: when the background is the evolving metric's own chosen Levi-Civita
family, the intrinsic Ricci-DeTurck right-hand side collapses to the pure intrinsic Ricci-flow
right-hand side `(-2)•Ric`.**  This is the `chosenLeviCivitaFamily`-specialised instance of
`intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita` (discharging its Levi-Civita
hypothesis with `chosenLeviCivitaFamily_isLeviCivita`).  It is exactly the reduction the chart-closure
`chartRHS_eq_intrinsic` obligation needs: that field identifies the chart operator along the solution
with `intrinsicRicciDeTurckRHS (spatial sol).metric (chosenLeviCivitaFamily (spatial sol).metric)`,
which by this lemma equals `intrinsicRicciFlowRHS (spatial sol).metric` — the flowing metric's DeTurck
term vanishes in its own Levi-Civita gauge. -/
theorem intrinsicRicciDeTurckRHS_chosenLeviCivitaFamily_eq_intrinsicRicciFlowRHS
    (g : MetricFamily (I := I) (M := M)) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g (chosenLeviCivitaFamily (I := I) (M := M) g) =
      intrinsicRicciFlowRHS (I := I) (M := M) g :=
  intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita
    (I := I) (M := M) g (chosenLeviCivitaFamily (I := I) (M := M) g)
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g)

/-- The intrinsic Ricci-DeTurck right-hand side vanishes wherever the intrinsic Ricci tensor
vanishes and the background is the Levi-Civita connection of the evolving metric. -/
theorem intrinsicRicciDeTurckRHS_eq_zero_of_isLeviCivita_of_intrinsicRicciTensor_eq_zero
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    {t : ℝ} {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M) g t x u v = 0) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v = 0 := by
  calc
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v =
        intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := by
      simpa using congrArg (fun F => F t x u v)
        (intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita
          (I := I) (M := M) g background hbackground)
    _ = 0 :=
      intrinsicRicciFlowRHS_eq_zero_of_intrinsicRicciTensor_eq_zero
        (I := I) (M := M) g hRicciZero

/-- The intrinsic Ricci-DeTurck equation at a single time. -/
def SatisfiesIntrinsicDeTurckEquationAt
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) : Prop :=
  ∀ x : M, ∀ u v : TM x,
    gdot t x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v

theorem SatisfiesIntrinsicDeTurckEquationAt.metricVelocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)} {t : ℝ}
    (h : SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M) g gdot background t)
    (x : M) (u v : TM x) :
    gdot t x u v = 0 := by
  rw [h x u v]
  exact intrinsicRicciDeTurckRHS_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) g background t x u v

/-- If the intrinsic Ricci tensor vanishes and the background is Levi-Civita, then the
Ricci-DeTurck equation forces the corresponding metric-velocity component to vanish. -/
theorem SatisfiesIntrinsicDeTurckEquationAt.metricVelocity_eq_zero_of_isLeviCivita_of_intrinsicRicciTensor_eq_zero
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)} {t : ℝ}
    (h : SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M) g gdot background t)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M) g t x u v = 0) :
    gdot t x u v = 0 := by
  rw [h x u v]
  exact intrinsicRicciDeTurckRHS_eq_zero_of_isLeviCivita_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) g background hbackground hRicciZero

theorem satisfiesIntrinsicDeTurckEquationAt_iff_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M) g gdot background t ↔
      SatisfiesIntrinsicEquationAt (I := I) (M := M) g gdot t := by
  constructor <;> intro hEq <;> intro x u v
  · calc
      gdot t x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v := hEq x u v
      _ = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := by
        simpa using congrArg
          (fun F => F t x u v)
          (intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita
            (I := I) (M := M) g background hbackground)
  · calc
      gdot t x u v = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := hEq x u v
      _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v := by
        simpa using congrArg
          (fun F => F t x u v)
          (intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita
            (I := I) (M := M) g background hbackground).symm

/-- On zero-dimensional tangent fibers, the intrinsic Ricci-DeTurck equation is equivalent to the
intrinsic Ricci-flow equation for any background connection family. -/
theorem satisfiesIntrinsicDeTurckEquationAt_iff_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) :
    SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M) g gdot background t ↔
      SatisfiesIntrinsicEquationAt (I := I) (M := M) g gdot t := by
  constructor
  · intro hEq x u v
    calc
      gdot t x u v = 0 :=
        SatisfiesIntrinsicDeTurckEquationAt.metricVelocity_eq_zero_of_subsingleton_tangent
          (I := I) (M := M) hEq x u v
      _ = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := by
        exact (intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent
          (I := I) (M := M) g t x u v).symm
  · intro hEq x u v
    calc
      gdot t x u v = 0 :=
        SatisfiesIntrinsicEquationAt.metricVelocity_eq_zero_of_subsingleton_tangent
          (I := I) (M := M) hEq x u v
      _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v := by
        exact (intrinsicRicciDeTurckRHS_eq_zero_of_subsingleton_tangent
          (I := I) (M := M) g background t x u v).symm

/-- A metric family solves the intrinsic Ricci-DeTurck equation on `s` when its tensor derivative
exists there and agrees with the intrinsic Ricci-DeTurck right-hand side. -/
def IsIntrinsicRicciDeTurckOn
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  HasTimeDerivativeOn (I := I) (M := M) g gdot s ∧
    ∀ ⦃t : ℝ⦄, t ∈ s →
      SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M) g gdot background t

theorem isIntrinsicRicciDeTurckOn_iff_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    IsIntrinsicRicciDeTurckOn (I := I) (M := M) g gdot background s ↔
      IsIntrinsicRicciFlowOn (I := I) (M := M) g gdot s := by
  constructor
  · intro hFlow
    refine ⟨hFlow.1, ?_⟩
    intro t ht
    exact
      (satisfiesIntrinsicDeTurckEquationAt_iff_of_isLeviCivita
        (I := I) (M := M) g gdot background t hbackground).1
        (hFlow.2 ht)
  · intro hFlow
    refine ⟨hFlow.1, ?_⟩
    intro t ht
    exact
        (satisfiesIntrinsicDeTurckEquationAt_iff_of_isLeviCivita
          (I := I) (M := M) g gdot background t hbackground).2
        (hFlow.2 ht)

/-- On zero-dimensional tangent fibers, intrinsic Ricci-DeTurck flow is intrinsic Ricci flow for
any background connection family. -/
theorem isIntrinsicRicciDeTurckOn_iff_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) :
    IsIntrinsicRicciDeTurckOn (I := I) (M := M) g gdot background s ↔
      IsIntrinsicRicciFlowOn (I := I) (M := M) g gdot s := by
  constructor
  · intro hFlow
    refine ⟨hFlow.1, ?_⟩
    intro t ht
    exact
      (satisfiesIntrinsicDeTurckEquationAt_iff_of_subsingleton_tangent
        (I := I) (M := M) g gdot background t).1
        (hFlow.2 ht)
  · intro hFlow
    refine ⟨hFlow.1, ?_⟩
    intro t ht
    exact
      (satisfiesIntrinsicDeTurckEquationAt_iff_of_subsingleton_tangent
        (I := I) (M := M) g gdot background t).2
        (hFlow.2 ht)

/-- An intrinsic Ricci-DeTurck solution packages the evolving metric, its tensor velocity, and the
background connection family used in the DeTurck correction. -/
structure IntrinsicDeTurckSolution where
  /-- The time set on which the solution is defined. -/
  timeSet : Set ℝ
  /-- The evolving metric. -/
  metric : MetricFamily (I := I) (M := M)
  /-- The time derivative of the metric tensor. -/
  metricVelocity : MetricTensorFamily (I := I) (M := M)
  /-- The background connection family used in the DeTurck gauge. -/
  background : ConnectionFamily (I := I) (M := M)
  /-- The intrinsic Ricci-DeTurck equation on the time set. -/
  isRicciDeTurck : IsIntrinsicRicciDeTurckOn (I := I) (M := M)
    metric metricVelocity background timeSet

lemma intrinsicDeTurckSolution_hasTimeDerivativeOn
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M)) :
    HasTimeDerivativeOn (I := I) (M := M)
      sol.metric sol.metricVelocity sol.timeSet :=
  sol.isRicciDeTurck.1

lemma intrinsicDeTurckSolution_equation
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    {t : ℝ} (ht : t ∈ sol.timeSet) :
    SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M)
      sol.metric sol.metricVelocity sol.background t :=
  sol.isRicciDeTurck.2 ht

/-- Restrict an intrinsic Ricci-DeTurck solution to a smaller time set.  The
metric, velocity, and background families are unchanged; only the equation
domain is narrowed. -/
def IntrinsicDeTurckSolution.restrictTimeSet
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (s : Set ℝ) (hsub : s ⊆ sol.timeSet) :
    IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M) where
  timeSet := s
  metric := sol.metric
  metricVelocity := sol.metricVelocity
  background := sol.background
  isRicciDeTurck := by
    refine ⟨(intrinsicDeTurckSolution_hasTimeDerivativeOn
      (I := I) (M := M) sol).mono hsub, ?_⟩
    intro t ht
    exact intrinsicDeTurckSolution_equation (I := I) (M := M) sol (hsub ht)

@[simp] theorem IntrinsicDeTurckSolution.restrictTimeSet_timeSet
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (s : Set ℝ) (hsub : s ⊆ sol.timeSet) :
    (sol.restrictTimeSet s hsub).timeSet = s :=
  rfl

@[simp] theorem IntrinsicDeTurckSolution.restrictTimeSet_metric
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (s : Set ℝ) (hsub : s ⊆ sol.timeSet) :
    (sol.restrictTimeSet s hsub).metric = sol.metric :=
  rfl

@[simp] theorem IntrinsicDeTurckSolution.restrictTimeSet_metricVelocity
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (s : Set ℝ) (hsub : s ⊆ sol.timeSet) :
    (sol.restrictTimeSet s hsub).metricVelocity = sol.metricVelocity :=
  rfl

@[simp] theorem IntrinsicDeTurckSolution.restrictTimeSet_background
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (s : Set ℝ) (hsub : s ⊆ sol.timeSet) :
    (sol.restrictTimeSet s hsub).background = sol.background :=
  rfl

theorem IntrinsicDeTurckSolution.metricVelocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    {t : ℝ} (ht : t ∈ sol.timeSet) (x : M) (u v : TM x) :
    sol.metricVelocity t x u v = 0 :=
  SatisfiesIntrinsicDeTurckEquationAt.metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) (intrinsicDeTurckSolution_equation (I := I) (M := M) sol ht)
    x u v

/-- A Ricci-DeTurck solution with Levi-Civita background has zero velocity in any component where
the intrinsic Ricci tensor vanishes. -/
theorem IntrinsicDeTurckSolution.metricVelocity_eq_zero_of_isLeviCivita_of_intrinsicRicciTensor_eq_zero
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) sol.metric sol.background)
    {t : ℝ} (ht : t ∈ sol.timeSet) {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M) sol.metric t x u v = 0) :
    sol.metricVelocity t x u v = 0 :=
  SatisfiesIntrinsicDeTurckEquationAt.metricVelocity_eq_zero_of_isLeviCivita_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) (intrinsicDeTurckSolution_equation (I := I) (M := M) sol ht)
    hbackground hRicciZero

/-- On zero-dimensional tangent fibers, the intrinsic Ricci tensor of the evolving DeTurck metric
vanishes pointwise. -/
theorem IntrinsicDeTurckSolution.intrinsicRicciTensor_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) sol.metric t x u v = 0 :=
  _root_.RicciFlow.intrinsicRicciTensor_eq_zero_of_subsingleton_tangent (I := I) (M := M)
    sol.metric t x u v

/-- On zero-dimensional tangent fibers, the intrinsic Ricci-flow right-hand side of the evolving
DeTurck metric vanishes pointwise. -/
theorem IntrinsicDeTurckSolution.intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M) sol.metric t x u v = 0 :=
  _root_.RicciFlow.intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent (I := I) (M := M)
    sol.metric t x u v

/-- On zero-dimensional tangent fibers, the intrinsic Ricci-DeTurck right-hand side of the evolving
DeTurck metric vanishes pointwise for the stored background. -/
theorem IntrinsicDeTurckSolution.intrinsicRicciDeTurckRHS_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) sol.metric sol.background t x u v = 0 :=
  _root_.RicciFlow.intrinsicRicciDeTurckRHS_eq_zero_of_subsingleton_tangent (I := I) (M := M)
    sol.metric sol.background t x u v

/-- On zero-dimensional tangent fibers, every DeTurck background is Levi-Civita for the evolving
metric. -/
theorem IntrinsicDeTurckSolution.background_isLeviCivita_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M)) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) sol.metric sol.background :=
  sol.metric.isLeviCivita_of_subsingleton_tangent sol.background

/-- If the DeTurck background family is Levi-Civita for the evolving metric, then an intrinsic
Ricci-DeTurck solution canonically determines an intrinsic Ricci-flow solution. -/
def IntrinsicDeTurckSolution.toIntrinsicSolution
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) sol.metric sol.background) :
    IntrinsicSolution (E := E) (H := H) (I := I) (M := M) where
  timeSet := sol.timeSet
  metric := sol.metric
  metricVelocity := sol.metricVelocity
  isRicciFlow :=
    (isIntrinsicRicciDeTurckOn_iff_of_isLeviCivita
      (I := I) (M := M) sol.metric sol.metricVelocity sol.background sol.timeSet
      hbackground).1
      sol.isRicciDeTurck

/-- With Levi-Civita background, zero DeTurck velocity at a fixed component is equivalent to
vanishing intrinsic Ricci tensor there. -/
theorem IntrinsicDeTurckSolution.metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero_of_isLeviCivita
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) sol.metric sol.background)
    {t : ℝ} (ht : t ∈ sol.timeSet) (x : M) (u v : TM x) :
    sol.metricVelocity t x u v = 0 ↔
      intrinsicRicciTensor (I := I) (M := M) sol.metric t x u v = 0 := by
  simpa [IntrinsicDeTurckSolution.toIntrinsicSolution] using
    IntrinsicSolution.metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) (sol.toIntrinsicSolution hbackground) ht x u v

/-- On zero-dimensional tangent fibers, a Ricci-DeTurck solution is an intrinsic Ricci-flow
solution for any DeTurck background family. -/
def IntrinsicDeTurckSolution.toIntrinsicSolution_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicSolution (E := E) (H := H) (I := I) (M := M) where
  timeSet := sol.timeSet
  metric := sol.metric
  metricVelocity := sol.metricVelocity
  isRicciFlow :=
    (isIntrinsicRicciDeTurckOn_iff_of_subsingleton_tangent
      (I := I) (M := M) sol.metric sol.metricVelocity sol.background sol.timeSet).1
      sol.isRicciDeTurck

/-- Any intrinsic Ricci-flow solution becomes an intrinsic Ricci-DeTurck solution for a chosen
Levi-Civita background family. -/
def IntrinsicSolution.toIntrinsicDeTurckSolution
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) sol.metric background) :
    IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M) where
  timeSet := sol.timeSet
  metric := sol.metric
  metricVelocity := sol.metricVelocity
  background := background
  isRicciDeTurck :=
    (isIntrinsicRicciDeTurckOn_iff_of_isLeviCivita
      (I := I) (M := M) sol.metric sol.metricVelocity background sol.timeSet
      hbackground).2
      sol.isRicciFlow

/-- On zero-dimensional tangent fibers, any intrinsic Ricci-flow solution is a Ricci-DeTurck
solution for any background connection family. -/
def IntrinsicSolution.toIntrinsicDeTurckSolution_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M) where
  timeSet := sol.timeSet
  metric := sol.metric
  metricVelocity := sol.metricVelocity
  background := background
  isRicciDeTurck :=
    (isIntrinsicRicciDeTurckOn_iff_of_subsingleton_tangent
      (I := I) (M := M) sol.metric sol.metricVelocity background sol.timeSet).2
      sol.isRicciFlow

/-- Specialize an intrinsic Ricci-flow solution to the chosen smooth Levi-Civita background family. -/
def IntrinsicSolution.toChosenIntrinsicDeTurckSolution
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M) :=
  sol.toIntrinsicDeTurckSolution
    (chosenLeviCivitaFamily (I := I) (M := M) sol.metric)
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) sol.metric)

/-- Initial-metric matching condition for an intrinsic Ricci-DeTurck solution. -/
def IntrinsicDeTurckMatchesInitialMetric
    (sol : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ x : M, ∀ u v : TM x,
    metricTensor (I := I) (M := M) sol.metric ivp.initialTime x u v =
      ivp.initialMetric.inner x u v

/-- A local intrinsic Ricci-DeTurck solution is an interval solution together with a matched
initial metric. -/
structure IntrinsicDeTurckLocalSolution
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- Terminal time of the local solution interval. -/
  terminalTime : ℝ
  /-- The interval is genuinely forward in time. -/
  initial_lt_terminal : ivp.initialTime < terminalTime
  /-- The underlying intrinsic Ricci-DeTurck solution object. -/
  toIntrinsicDeTurckSolution : IntrinsicDeTurckSolution (E := E) (H := H) (I := I) (M := M)
  /-- The solution is defined on the whole interval `[t₀, T]`. -/
  interval_subset : Set.Icc ivp.initialTime terminalTime ⊆ toIntrinsicDeTurckSolution.timeSet
  /-- The initial metric is matched at the initial time. -/
  matchesInitialMetric :
    IntrinsicDeTurckMatchesInitialMetric (I := I) (M := M) toIntrinsicDeTurckSolution ivp

/-- Restrict an intrinsic Ricci-DeTurck local solution to any shorter forward terminal time. -/
def IntrinsicDeTurckLocalSolution.restrictTerminal
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := T
  initial_lt_terminal := hT₀
  toIntrinsicDeTurckSolution := sol.toIntrinsicDeTurckSolution
  interval_subset := by
    intro t ht
    exact sol.interval_subset ⟨ht.1, le_trans ht.2 hT⟩
  matchesInitialMetric := sol.matchesInitialMetric

/-- Restrict an intrinsic Ricci-DeTurck local solution to a specified smaller
time set and terminal time.  This is stronger than `restrictTerminal`: the
underlying solution record also has its `timeSet` replaced by the named set. -/
def IntrinsicDeTurckLocalSolution.restrictTimeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (s : Set ℝ) {T : ℝ} (hT₀ : ivp.initialTime < T)
    (hinterval : Set.Icc ivp.initialTime T ⊆ s)
    (hsub : s ⊆ sol.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := T
  initial_lt_terminal := hT₀
  toIntrinsicDeTurckSolution := sol.toIntrinsicDeTurckSolution.restrictTimeSet s hsub
  interval_subset := hinterval
  matchesInitialMetric := by
    simpa [IntrinsicDeTurckMatchesInitialMetric,
      IntrinsicDeTurckSolution.restrictTimeSet] using sol.matchesInitialMetric

/-- Restrict a local Ricci-DeTurck solution to a symmetric closed time interval
around the initial time. -/
def IntrinsicDeTurckLocalSolution.restrictSymmetricIcc
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {ε : ℝ} (hε : 0 < ε)
    (hsub : Set.Icc (ivp.initialTime - ε) (ivp.initialTime + ε) ⊆
      sol.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.restrictTimeSet (Set.Icc (ivp.initialTime - ε) (ivp.initialTime + ε))
    (T := ivp.initialTime + ε)
    (by linarith)
    (by
      intro t ht
      exact ⟨by linarith [ht.1, hε], ht.2⟩)
    hsub

@[simp] theorem IntrinsicDeTurckLocalSolution.restrictTerminal_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).terminalTime = T :=
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.restrictTerminal_toIntrinsicDeTurckSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).toIntrinsicDeTurckSolution =
      sol.toIntrinsicDeTurckSolution :=
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.restrictTimeSet_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (s : Set ℝ) {T : ℝ} (hT₀ : ivp.initialTime < T)
    (hinterval : Set.Icc ivp.initialTime T ⊆ s)
    (hsub : s ⊆ sol.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictTimeSet s hT₀ hinterval hsub).terminalTime = T :=
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.restrictTimeSet_toIntrinsicDeTurckSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (s : Set ℝ) {T : ℝ} (hT₀ : ivp.initialTime < T)
    (hinterval : Set.Icc ivp.initialTime T ⊆ s)
    (hsub : s ⊆ sol.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictTimeSet s hT₀ hinterval hsub).toIntrinsicDeTurckSolution =
      sol.toIntrinsicDeTurckSolution.restrictTimeSet s hsub :=
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.restrictTimeSet_timeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (s : Set ℝ) {T : ℝ} (hT₀ : ivp.initialTime < T)
    (hinterval : Set.Icc ivp.initialTime T ⊆ s)
    (hsub : s ⊆ sol.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictTimeSet s hT₀ hinterval hsub).toIntrinsicDeTurckSolution.timeSet = s :=
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.restrictSymmetricIcc_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {ε : ℝ} (hε : 0 < ε)
    (hsub : Set.Icc (ivp.initialTime - ε) (ivp.initialTime + ε) ⊆
      sol.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictSymmetricIcc hε hsub).terminalTime = ivp.initialTime + ε :=
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.restrictSymmetricIcc_timeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {ε : ℝ} (hε : 0 < ε)
    (hsub : Set.Icc (ivp.initialTime - ε) (ivp.initialTime + ε) ⊆
      sol.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictSymmetricIcc hε hsub).toIntrinsicDeTurckSolution.timeSet =
      Set.Icc (ivp.initialTime - ε) (ivp.initialTime + ε) :=
  rfl

lemma intrinsicDeTurckLocalSolution_initialTime_mem
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    ivp.initialTime ∈ sol.toIntrinsicDeTurckSolution.timeSet :=
  sol.interval_subset ⟨le_rfl, le_of_lt sol.initial_lt_terminal⟩

lemma intrinsicDeTurckLocalSolution_metric_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric ivp.initialTime x u v =
        ivp.initialMetric.inner x u v :=
  sol.matchesInitialMetric x u v

/-- If the background family is Levi-Civita for the evolving metric, then an intrinsic
Ricci-DeTurck local solution canonically determines an intrinsic local Ricci-flow solution. -/
def IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  toIntrinsicSolution := sol.toIntrinsicDeTurckSolution.toIntrinsicSolution hbackground
  interval_subset := sol.interval_subset
  matchesInitialMetric := by
    simpa [IntrinsicDeTurckMatchesInitialMetric, IntrinsicMatchesInitialMetric,
      MatchesInitialMetric, IntrinsicDeTurckSolution.toIntrinsicSolution, IntrinsicSolution.toSolution]
      using sol.matchesInitialMetric

@[simp] theorem IntrinsicDeTurckLocalSolution.restrictTerminal_toIntrinsicLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).toIntrinsicLocalSolution hbackground =
      (sol.toIntrinsicLocalSolution hbackground).restrictTerminal hT₀ hT :=
  rfl

/-- On zero-dimensional tangent fibers, an intrinsic Ricci-DeTurck local solution canonically
determines an intrinsic Ricci-flow local solution for any background connection family. -/
def IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  toIntrinsicSolution := sol.toIntrinsicDeTurckSolution.toIntrinsicSolution_of_subsingleton_tangent
  interval_subset := sol.interval_subset
  matchesInitialMetric := by
    simpa [IntrinsicDeTurckMatchesInitialMetric, IntrinsicMatchesInitialMetric,
      MatchesInitialMetric, IntrinsicDeTurckSolution.toIntrinsicSolution_of_subsingleton_tangent,
      IntrinsicSolution.toSolution]
      using sol.matchesInitialMetric

/-- On zero-dimensional tangent fibers, the background of any local Ricci-DeTurck solution is
Levi-Civita for its evolving metric. -/
theorem IntrinsicDeTurckLocalSolution.background_isLeviCivita_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background :=
  sol.toIntrinsicDeTurckSolution.background_isLeviCivita_of_subsingleton_tangent

/-- Rewrite an intrinsic local Ricci-flow solution as an intrinsic Ricci-DeTurck local solution for
an arbitrary Levi-Civita background family. -/
def IntrinsicLocalSolution.toIntrinsicDeTurckLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) sol.toIntrinsicSolution.metric background) :
    IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  toIntrinsicDeTurckSolution := sol.toIntrinsicSolution.toIntrinsicDeTurckSolution background hbackground
  interval_subset := sol.interval_subset
  matchesInitialMetric := by
    change ∀ x : M, ∀ u v : TM x,
      metricTensor (I := I) (M := M) sol.toIntrinsicSolution.metric ivp.initialTime x u v =
        ivp.initialMetric.inner x u v
    exact sol.matchesInitialMetric

/-- On zero-dimensional tangent fibers, an intrinsic Ricci-flow local solution can be rewritten as an
intrinsic Ricci-DeTurck local solution for any background connection family. -/
def IntrinsicLocalSolution.toIntrinsicDeTurckLocalSolution_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (background : ConnectionFamily (I := I) (M := M)) :
    IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  toIntrinsicDeTurckSolution :=
    sol.toIntrinsicSolution.toIntrinsicDeTurckSolution_of_subsingleton_tangent background
  interval_subset := sol.interval_subset
  matchesInitialMetric := by
    simpa [IntrinsicDeTurckMatchesInitialMetric, IntrinsicMatchesInitialMetric,
      MatchesInitialMetric, IntrinsicSolution.toIntrinsicDeTurckSolution_of_subsingleton_tangent,
      IntrinsicSolution.toSolution]
      using sol.matchesInitialMetric

/-- Specialize an intrinsic local Ricci-flow solution to the chosen smooth Levi-Civita background
family. -/
def IntrinsicLocalSolution.toChosenIntrinsicDeTurckLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toIntrinsicDeTurckLocalSolution
    (chosenLeviCivitaFamily (I := I) (M := M) sol.toIntrinsicSolution.metric)
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) sol.toIntrinsicSolution.metric)

/-- The canonical Levi-Civita connection family extracted from an intrinsic Ricci-DeTurck local
solution once the background family is known to be Levi-Civita. -/
abbrev IntrinsicDeTurckLocalSolution.canonicalConnection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    ConnectionFamily (I := I) (M := M) :=
  (sol.toIntrinsicLocalSolution hbackground).toIntrinsicSolution.toSolution.connection

section IntrinsicDeTurckLocalWrappers

/-- Along an intrinsic Ricci-DeTurck local solution with Levi-Civita background, zero metric
velocity on the whole interval implies vanishing intrinsic Ricci tensor there. -/
theorem intrinsicDeTurckLocalSolution_ricciTensor_eq_zero_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v = 0 := by
  simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution,
    IntrinsicDeTurckSolution.toIntrinsicSolution] using
    intrinsicLocalSolution_ricciTensor_eq_zero_of_zero_velocity
      (I := I) (M := M) (sol.toIntrinsicLocalSolution hbackground) hzero ht x u v

/-- Along an intrinsic Ricci-DeTurck local solution with Levi-Civita background, zero metric
velocity on the whole interval is equivalent to vanishing intrinsic Ricci tensor there. -/
theorem intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    (∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0) ↔
      (∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v = 0) := by
  simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution,
    IntrinsicDeTurckSolution.toIntrinsicSolution] using
    intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) (sol.toIntrinsicLocalSolution hbackground)

/-- A Ricci-DeTurck local solution with Levi-Civita background has zero velocity in any interval
component where the intrinsic Ricci tensor vanishes. -/
theorem intrinsicDeTurckLocalSolution_metricVelocity_eq_zero_of_isLeviCivita_of_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric t x u v = 0) :
    sol.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 :=
  IntrinsicDeTurckSolution.metricVelocity_eq_zero_of_isLeviCivita_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) sol.toIntrinsicDeTurckSolution hbackground
    (sol.interval_subset ht) hRicciZero

/-- On the local interval, and with Levi-Civita background, zero DeTurck velocity at a fixed
component is equivalent to vanishing intrinsic Ricci tensor there. -/
theorem intrinsicDeTurckLocalSolution_metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero_of_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    sol.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 ↔
      intrinsicRicciTensor (I := I) (M := M)
        sol.toIntrinsicDeTurckSolution.metric t x u v = 0 :=
  IntrinsicDeTurckSolution.metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero_of_isLeviCivita
    (I := I) (M := M) sol.toIntrinsicDeTurckSolution hbackground
    (sol.interval_subset ht) x u v

/-- If the metric velocity vanishes on the whole intrinsic Ricci-DeTurck local-solution interval
and the background is Levi-Civita, then the metric tensor stays equal to the initial metric tensor
there. -/
theorem intrinsicDeTurckLocalSolution_metric_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution,
    IntrinsicDeTurckSolution.toIntrinsicSolution] using
    intrinsicLocalSolution_metric_eq_initial_of_zero_velocity
      (I := I) (M := M) (sol.toIntrinsicLocalSolution hbackground) hzero ht x u v

/-- If the metric velocity vanishes on the whole intrinsic Ricci-DeTurck local-solution interval
and the background is Levi-Civita, then the canonical Levi-Civita connection stays equal to the
initial one there. -/
theorem intrinsicDeTurckLocalSolution_connection_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.canonicalConnection hbackground t σ x =
      sol.canonicalConnection hbackground ivp.initialTime σ x := by
  simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution,
    IntrinsicDeTurckSolution.toIntrinsicSolution, IntrinsicDeTurckLocalSolution.canonicalConnection] using
    intrinsicLocalSolution_connection_eq_initial_of_zero_velocity
      (I := I) (M := M) (sol.toIntrinsicLocalSolution hbackground) hzero ht hσ

/-- If the intrinsic Ricci tensor vanishes on the whole intrinsic Ricci-DeTurck local-solution
interval and the background is Levi-Civita, then the metric tensor stays equal to the initial
metric tensor there. -/
theorem intrinsicDeTurckLocalSolution_metric_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  exact intrinsicDeTurckLocalSolution_metric_eq_initial_of_zero_velocity
    (I := I) (M := M) sol hbackground
    ((intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol hbackground).2 hRicciZero)
    ht x u v

/-- If the intrinsic Ricci tensor vanishes on the whole intrinsic Ricci-DeTurck local-solution
interval and the background is Levi-Civita, then the canonical Levi-Civita connection stays equal
to the initial one there. -/
theorem intrinsicDeTurckLocalSolution_connection_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.canonicalConnection hbackground t σ x =
      sol.canonicalConnection hbackground ivp.initialTime σ x := by
  exact intrinsicDeTurckLocalSolution_connection_eq_initial_of_zero_velocity
    (I := I) (M := M) sol hbackground
    ((intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol hbackground).2 hRicciZero)
    ht hσ

/-- Two intrinsic Ricci-DeTurck local solutions with Levi-Civita backgrounds and zero metric
velocity on their intervals have the same evolving metric tensor on the common initial interval. -/
theorem intrinsicDeTurckLocalSolution_unique_metric_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground₁ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₁.toIntrinsicDeTurckSolution.metric sol₁.toIntrinsicDeTurckSolution.background)
    (hbackground₂ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₂.toIntrinsicDeTurckSolution.metric sol₂.toIntrinsicDeTurckSolution.background)
    (hzero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₁.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    (hzero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₂.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicDeTurckSolution.metric t x u v := by
  simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution,
    IntrinsicDeTurckSolution.toIntrinsicSolution] using
    intrinsicLocalSolution_unique_metric_of_zero_velocity
      (I := I) (M := M)
      (sol₁.toIntrinsicLocalSolution hbackground₁)
      (sol₂.toIntrinsicLocalSolution hbackground₂)
      hzero₁ hzero₂ ht x u v

/-- Two intrinsic Ricci-DeTurck local solutions with Levi-Civita backgrounds and zero metric
velocity on their intervals have the same canonical Levi-Civita connection on the common initial
interval. -/
theorem intrinsicDeTurckLocalSolution_unique_connection_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground₁ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₁.toIntrinsicDeTurckSolution.metric sol₁.toIntrinsicDeTurckSolution.background)
    (hbackground₂ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₂.toIntrinsicDeTurckSolution.metric sol₂.toIntrinsicDeTurckSolution.background)
    (hzero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₁.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    (hzero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₂.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.canonicalConnection hbackground₁ t σ x =
      sol₂.canonicalConnection hbackground₂ t σ x := by
  simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution,
    IntrinsicDeTurckSolution.toIntrinsicSolution, IntrinsicDeTurckLocalSolution.canonicalConnection] using
    intrinsicLocalSolution_unique_connection_of_zero_velocity
      (I := I) (M := M)
      (sol₁.toIntrinsicLocalSolution hbackground₁)
      (sol₂.toIntrinsicLocalSolution hbackground₂)
      hzero₁ hzero₂ ht hσ

/-- On zero-dimensional tangent fibers, every intrinsic Ricci-DeTurck local solution has zero metric
velocity on its local interval. -/
theorem intrinsicDeTurckLocalSolution_metricVelocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    sol.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 :=
  IntrinsicDeTurckSolution.metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol.toIntrinsicDeTurckSolution (sol.interval_subset ht) x u v

/-- On zero-dimensional tangent fibers, every intrinsic Ricci-DeTurck local solution has vanishing
intrinsic Ricci tensor on its local interval, independently of the stored background. -/
theorem intrinsicDeTurckLocalSolution_intrinsicRicciTensor_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric t x u v = 0 :=
  sol.toIntrinsicDeTurckSolution.intrinsicRicciTensor_eq_zero_of_subsingleton_tangent t x u v

/-- On zero-dimensional tangent fibers, every intrinsic Ricci-DeTurck local solution has vanishing
intrinsic Ricci-flow right-hand side on its local interval. -/
theorem intrinsicDeTurckLocalSolution_intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric t x u v = 0 :=
  sol.toIntrinsicDeTurckSolution.intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent t x u v

/-- On zero-dimensional tangent fibers, every intrinsic Ricci-DeTurck local solution has vanishing
Ricci-DeTurck right-hand side on its local interval, for its stored background. -/
theorem intrinsicDeTurckLocalSolution_intrinsicRicciDeTurckRHS_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background t x u v = 0 :=
  sol.toIntrinsicDeTurckSolution.intrinsicRicciDeTurckRHS_eq_zero_of_subsingleton_tangent
    t x u v

/-- On zero-dimensional tangent fibers, every intrinsic Ricci-DeTurck local solution with
Levi-Civita background is stationary in metric tensor components on its local interval. -/
theorem intrinsicDeTurckLocalSolution_metric_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  refine intrinsicDeTurckLocalSolution_metric_eq_initial_of_zero_velocity
    (I := I) (M := M) sol hbackground ?_ ht x u v
  intro τ hτ y a b
  exact intrinsicDeTurckLocalSolution_metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol hτ y a b

/-- On zero-dimensional tangent fibers, every intrinsic Ricci-DeTurck local solution is stationary
in metric tensor components, independently of the DeTurck background family. -/
theorem intrinsicDeTurckLocalSolution_metric_eq_initial_of_subsingleton_tangent_any_background
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_of_subsingleton_tangent,
    IntrinsicDeTurckSolution.toIntrinsicSolution_of_subsingleton_tangent] using
    intrinsicLocalSolution_metric_eq_initial_of_subsingleton_tangent
      (I := I) (M := M)
      (sol.toIntrinsicLocalSolution_of_subsingleton_tangent) ht x u v

/-- On zero-dimensional tangent fibers, any two intrinsic Ricci-DeTurck local solutions have the
same metric tensor on every common time. -/
theorem intrinsicDeTurckLocalSolution_unique_metric_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicDeTurckSolution.metric t x u v := by
  rw [metricTensor_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) sol₁.toIntrinsicDeTurckSolution.metric t x u v,
    metricTensor_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) sol₂.toIntrinsicDeTurckSolution.metric t x u v]

/-- On zero-dimensional tangent fibers, all canonical connections of intrinsic Ricci-DeTurck local
solutions with Levi-Civita backgrounds agree. -/
theorem intrinsicDeTurckLocalSolution_connection_eq_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground₁ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₁.toIntrinsicDeTurckSolution.metric sol₁.toIntrinsicDeTurckSolution.background)
    (hbackground₂ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₂.toIntrinsicDeTurckSolution.metric sol₂.toIntrinsicDeTurckSolution.background)
    (t₁ t₂ : ℝ) {x : M} {σ : Π y : M, TM y} :
    sol₁.canonicalConnection hbackground₁ t₁ σ x =
      sol₂.canonicalConnection hbackground₂ t₂ σ x :=
  Subsingleton.elim _ _

/-- On zero-dimensional tangent fibers, every intrinsic Ricci-DeTurck local solution with
Levi-Civita background is stationary in canonical connection values on its local interval. -/
theorem intrinsicDeTurckLocalSolution_connection_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} :
    sol.canonicalConnection hbackground t σ x =
      sol.canonicalConnection hbackground ivp.initialTime σ x :=
  intrinsicDeTurckLocalSolution_connection_eq_of_subsingleton_tangent
    (I := I) (M := M) sol sol hbackground hbackground t ivp.initialTime

/-- On zero-dimensional tangent fibers, any two intrinsic Ricci-DeTurck local solutions with
Levi-Civita backgrounds have the same canonical connection values on every common time. -/
theorem intrinsicDeTurckLocalSolution_unique_connection_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground₁ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₁.toIntrinsicDeTurckSolution.metric sol₁.toIntrinsicDeTurckSolution.background)
    (hbackground₂ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₂.toIntrinsicDeTurckSolution.metric sol₂.toIntrinsicDeTurckSolution.background)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} :
    sol₁.canonicalConnection hbackground₁ t σ x =
      sol₂.canonicalConnection hbackground₂ t σ x :=
  intrinsicDeTurckLocalSolution_connection_eq_of_subsingleton_tangent
    (I := I) (M := M) sol₁ sol₂ hbackground₁ hbackground₂ t t

/-- On zero-dimensional tangent fibers, the stored DeTurck background connection values of any two
local solutions agree, without assuming those backgrounds were chosen Levi-Civita families. -/
theorem intrinsicDeTurckLocalSolution_background_connection_eq_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (t₁ t₂ : ℝ) {x : M} {σ : Π y : M, TM y} :
    sol₁.toIntrinsicDeTurckSolution.background t₁ σ x =
      sol₂.toIntrinsicDeTurckSolution.background t₂ σ x :=
  Subsingleton.elim _ _

/-- On zero-dimensional tangent fibers, a DeTurck local solution's stored background connection is
stationary in connection values. -/
theorem intrinsicDeTurckLocalSolution_background_connection_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} :
    sol.toIntrinsicDeTurckSolution.background t σ x =
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime σ x :=
  intrinsicDeTurckLocalSolution_background_connection_eq_of_subsingleton_tangent
    (I := I) (M := M) sol sol t ivp.initialTime

/-- On zero-dimensional tangent fibers, any two DeTurck local solutions have the same stored
background connection values on every common time. -/
theorem intrinsicDeTurckLocalSolution_unique_background_connection_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} :
    sol₁.toIntrinsicDeTurckSolution.background t σ x =
      sol₂.toIntrinsicDeTurckSolution.background t σ x :=
  intrinsicDeTurckLocalSolution_background_connection_eq_of_subsingleton_tangent
    (I := I) (M := M) sol₁ sol₂ t t

/-- Two intrinsic Ricci-DeTurck local solutions with Levi-Civita backgrounds whose intrinsic Ricci
tensors vanish on their intervals have the same evolving metric tensor on the common initial
interval. -/
theorem intrinsicDeTurckLocalSolution_unique_metric_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground₁ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₁.toIntrinsicDeTurckSolution.metric sol₁.toIntrinsicDeTurckSolution.background)
    (hbackground₂ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₂.toIntrinsicDeTurckSolution.metric sol₂.toIntrinsicDeTurckSolution.background)
    (hRicciZero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol₁.toIntrinsicDeTurckSolution.metric t x u v = 0)
    (hRicciZero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol₂.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicDeTurckSolution.metric t x u v := by
  exact intrinsicDeTurckLocalSolution_unique_metric_of_zero_velocity
    (I := I) (M := M) sol₁ sol₂ hbackground₁ hbackground₂
    ((intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol₁ hbackground₁).2 hRicciZero₁)
    ((intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol₂ hbackground₂).2 hRicciZero₂)
    ht x u v

/-- Two intrinsic Ricci-DeTurck local solutions with Levi-Civita backgrounds whose intrinsic Ricci
tensors vanish on their intervals have the same canonical Levi-Civita connection on the common
initial interval. -/
theorem intrinsicDeTurckLocalSolution_unique_connection_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground₁ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₁.toIntrinsicDeTurckSolution.metric sol₁.toIntrinsicDeTurckSolution.background)
    (hbackground₂ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₂.toIntrinsicDeTurckSolution.metric sol₂.toIntrinsicDeTurckSolution.background)
    (hRicciZero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol₁.toIntrinsicDeTurckSolution.metric t x u v = 0)
    (hRicciZero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol₂.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.canonicalConnection hbackground₁ t σ x =
      sol₂.canonicalConnection hbackground₂ t σ x := by
  exact intrinsicDeTurckLocalSolution_unique_connection_of_zero_velocity
    (I := I) (M := M) sol₁ sol₂ hbackground₁ hbackground₂
    ((intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol₁ hbackground₁).2 hRicciZero₁)
    ((intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol₂ hbackground₂).2 hRicciZero₂)
    ht hσ

/-- If two intrinsic Ricci-DeTurck local solutions with Levi-Civita backgrounds have the same
metric tensor at a common time, then their canonical Levi-Civita connections agree there. -/
theorem intrinsicDeTurckLocalSolution_connection_eq_of_metric_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground₁ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₁.toIntrinsicDeTurckSolution.metric sol₁.toIntrinsicDeTurckSolution.background)
    (hbackground₂ : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol₂.toIntrinsicDeTurckSolution.metric sol₂.toIntrinsicDeTurckSolution.background)
    {t : ℝ}
    (ht₁ : t ∈ sol₁.toIntrinsicDeTurckSolution.timeSet)
    (ht₂ : t ∈ sol₂.toIntrinsicDeTurckSolution.timeSet)
    (hmetric : ∀ x : M, ∀ u v : TM x,
      metricTensor (I := I) (M := M) sol₁.toIntrinsicDeTurckSolution.metric t x u v =
        metricTensor (I := I) (M := M) sol₂.toIntrinsicDeTurckSolution.metric t x u v)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.canonicalConnection hbackground₁ t σ x =
      sol₂.canonicalConnection hbackground₂ t σ x := by
  simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution,
    IntrinsicDeTurckSolution.toIntrinsicSolution, IntrinsicDeTurckLocalSolution.canonicalConnection] using
    intrinsicLocalSolution_connection_eq_of_metric_eq
      (I := I) (M := M)
      (sol₁.toIntrinsicLocalSolution hbackground₁)
      (sol₂.toIntrinsicLocalSolution hbackground₂)
      ht₁ ht₂ hmetric hσ

end IntrinsicDeTurckLocalWrappers

/-- Predicate asserting that an intrinsic Ricci-DeTurck local solution uses the chosen smooth
Levi-Civita family as its background connection. -/
def UsesChosenBackground
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) : Prop :=
  sol.toIntrinsicDeTurckSolution.background =
    chosenLeviCivitaFamily (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric

lemma usesChosenBackground_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background := by
  rw [hchosen]
  exact chosenLeviCivitaFamily_isLeviCivita
    (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric

lemma intrinsicLocalSolution_usesChosenBackground
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    UsesChosenBackground (I := I) (M := M) (sol.toChosenIntrinsicDeTurckLocalSolution) := by
  rfl

/-- The DeTurck local-solution subtype using the chosen smooth Levi-Civita background. -/
abbrev ChosenIntrinsicDeTurckLocalSolution
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :=
  {sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp //
    UsesChosenBackground (I := I) (M := M) sol}

/-- Restrict a chosen-background Ricci-DeTurck local solution to a shorter terminal time. -/
def ChosenIntrinsicDeTurckLocalSolution.restrictTerminal
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.1.terminalTime) :
    ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  ⟨sol.1.restrictTerminal hT₀ hT, by
    simpa [IntrinsicDeTurckLocalSolution.restrictTerminal, UsesChosenBackground] using sol.2⟩

/-- Restrict a chosen-background Ricci-DeTurck local solution to a named smaller
time set.  The chosen-background condition is preserved because the metric and
background families are unchanged. -/
def ChosenIntrinsicDeTurckLocalSolution.restrictTimeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (s : Set ℝ) {T : ℝ} (hT₀ : ivp.initialTime < T)
    (hinterval : Set.Icc ivp.initialTime T ⊆ s)
    (hsub : s ⊆ sol.1.toIntrinsicDeTurckSolution.timeSet) :
    ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  ⟨sol.1.restrictTimeSet s hT₀ hinterval hsub, by
    simpa [IntrinsicDeTurckLocalSolution.restrictTimeSet,
      IntrinsicDeTurckSolution.restrictTimeSet, UsesChosenBackground] using sol.2⟩

/-- Restrict a chosen-background Ricci-DeTurck local solution to a symmetric
closed time interval around the initial time. -/
def ChosenIntrinsicDeTurckLocalSolution.restrictSymmetricIcc
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {ε : ℝ} (hε : 0 < ε)
    (hsub : Set.Icc (ivp.initialTime - ε) (ivp.initialTime + ε) ⊆
      sol.1.toIntrinsicDeTurckSolution.timeSet) :
    ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  ⟨IntrinsicDeTurckLocalSolution.restrictSymmetricIcc
      (I := I) (M := M) sol.1 hε hsub, by
    simpa [IntrinsicDeTurckLocalSolution.restrictSymmetricIcc,
      IntrinsicDeTurckLocalSolution.restrictTimeSet,
      IntrinsicDeTurckSolution.restrictTimeSet, UsesChosenBackground] using sol.2⟩

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.restrictTerminal_val
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.1.terminalTime) :
    (sol.restrictTerminal hT₀ hT).1 = sol.1.restrictTerminal hT₀ hT :=
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.restrictTerminal_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.1.terminalTime) :
    (sol.restrictTerminal hT₀ hT).1.terminalTime = T :=
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.restrictTimeSet_val
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (s : Set ℝ) {T : ℝ} (hT₀ : ivp.initialTime < T)
    (hinterval : Set.Icc ivp.initialTime T ⊆ s)
    (hsub : s ⊆ sol.1.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictTimeSet s hT₀ hinterval hsub).1 =
      sol.1.restrictTimeSet s hT₀ hinterval hsub :=
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.restrictTimeSet_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (s : Set ℝ) {T : ℝ} (hT₀ : ivp.initialTime < T)
    (hinterval : Set.Icc ivp.initialTime T ⊆ s)
    (hsub : s ⊆ sol.1.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictTimeSet s hT₀ hinterval hsub).1.terminalTime = T :=
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.restrictTimeSet_timeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (s : Set ℝ) {T : ℝ} (hT₀ : ivp.initialTime < T)
    (hinterval : Set.Icc ivp.initialTime T ⊆ s)
    (hsub : s ⊆ sol.1.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictTimeSet s hT₀ hinterval hsub).1.toIntrinsicDeTurckSolution.timeSet = s :=
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.restrictSymmetricIcc_val
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {ε : ℝ} (hε : 0 < ε)
    (hsub : Set.Icc (ivp.initialTime - ε) (ivp.initialTime + ε) ⊆
      sol.1.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictSymmetricIcc hε hsub).1 =
      IntrinsicDeTurckLocalSolution.restrictSymmetricIcc
        (I := I) (M := M) sol.1 hε hsub :=
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.restrictSymmetricIcc_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {ε : ℝ} (hε : 0 < ε)
    (hsub : Set.Icc (ivp.initialTime - ε) (ivp.initialTime + ε) ⊆
      sol.1.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictSymmetricIcc hε hsub).1.terminalTime = ivp.initialTime + ε :=
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.restrictSymmetricIcc_timeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {ε : ℝ} (hε : 0 < ε)
    (hsub : Set.Icc (ivp.initialTime - ε) (ivp.initialTime + ε) ⊆
      sol.1.toIntrinsicDeTurckSolution.timeSet) :
    (sol.restrictSymmetricIcc hε hsub).1.toIntrinsicDeTurckSolution.timeSet =
      Set.Icc (ivp.initialTime - ε) (ivp.initialTime + ε) :=
  rfl

/-- The compact-manifold point-4 theorem package stated with the chosen smooth Levi-Civita family as
the DeTurck background. -/
structure ChosenIntrinsicDeTurckLocalExistenceUniqueness
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- Existence of a chosen-background intrinsic Ricci-DeTurck local solution. -/
  exists_solution :
    Nonempty (ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
  /-- Uniqueness of the evolving metric on the overlap of two chosen-background local solution
  intervals. -/
  unique_metric :
    ∀ sol₁ sol₂ :
        ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime),
        ∀ x : M, ∀ u v : TM x,
          metricTensor (I := I) (M := M)
            sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
              metricTensor (I := I) (M := M)
                sol₂.1.toIntrinsicDeTurckSolution.metric t x u v

theorem chosenIntrinsicDeTurckLocalExistenceUniqueness_nonempty_localSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.exists_solution

theorem chosenIntrinsicDeTurckLocalExistenceUniqueness_metric_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v :=
  pkg.unique_metric sol₁ sol₂ t ht x u v

/-- Endpoint closure for functions that agree on a left-open neighborhood of the endpoint. -/
theorem eq_of_continuousAt_of_eqOn_Ico {α : Type*} [TopologicalSpace α] [T2Space α]
    {f g : ℝ → α} {a b : ℝ} (hab : a < b)
    (hf : ContinuousAt f b) (hg : ContinuousAt g b)
    (hEq : Set.EqOn f g (Set.Ico a b)) : f b = g b := by
  have hfg : f =ᶠ[𝓝[<] b] g := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hab]
    exact eventuallyEq_nhdsWithin_of_eqOn hEq
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left nhdsWithin_le_nhds)
    (hg.mono_left nhdsWithin_le_nhds) hfg

/-- If chosen-background DeTurck metric uniqueness is known on the open common
overlap, then the time-derivative data in the local-solution records closes the
metric equality at the common terminal as well. -/
theorem chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_interval_of_common_Ico
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hmetric : ∀ {t : ℝ}, t ∈ Set.Ico ivp.initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime) →
      ∀ (x : M) (u v : TM x),
        metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
          metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
  let Tcommon := min sol₁.1.terminalTime sol₂.1.terminalTime
  by_cases htlt : t < Tcommon
  · exact hmetric (t := t) ⟨ht.1, htlt⟩ x u v
  · have ht_eq : t = Tcommon :=
      le_antisymm (by simpa [Tcommon] using ht.2) (le_of_not_gt htlt)
    subst t
    have hT₀ : ivp.initialTime < Tcommon := by
      exact lt_min sol₁.1.initial_lt_terminal sol₂.1.initial_lt_terminal
    have htime₁ : Tcommon ∈ sol₁.1.toIntrinsicDeTurckSolution.timeSet := by
      exact sol₁.1.interval_subset ⟨le_of_lt hT₀, min_le_left _ _⟩
    have htime₂ : Tcommon ∈ sol₂.1.toIntrinsicDeTurckSolution.timeSet := by
      exact sol₂.1.interval_subset ⟨le_of_lt hT₀, min_le_right _ _⟩
    have hf : ContinuousAt
        (fun τ : ℝ ↦ metricTensor (I := I) (M := M)
          sol₁.1.toIntrinsicDeTurckSolution.metric τ x u v) Tcommon := by
      exact ((intrinsicDeTurckSolution_hasTimeDerivativeOn
        (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution) htime₁ x u v).continuousAt
    have hg : ContinuousAt
        (fun τ : ℝ ↦ metricTensor (I := I) (M := M)
          sol₂.1.toIntrinsicDeTurckSolution.metric τ x u v) Tcommon := by
      exact ((intrinsicDeTurckSolution_hasTimeDerivativeOn
        (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution) htime₂ x u v).continuousAt
    exact eq_of_continuousAt_of_eqOn_Ico hT₀ hf hg (fun τ hτ ↦ hmetric hτ x u v)

/-- Connection-level endpoint closure from open-overlap metric uniqueness.  The
endpoint connection equality follows from the closed metric bridge and the
canonical Levi-Civita connection uniqueness lemma. -/
theorem chosenIntrinsicDeTurckLocalSolution_connection_eq_on_common_interval_of_common_Ico_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hmetric : ∀ {t : ℝ}, t ∈ Set.Ico ivp.initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime) →
      ∀ (x : M) (u v : TM x),
        metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
          metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x := by
  have ht₁ : t ∈ sol₁.1.toIntrinsicDeTurckSolution.timeSet := by
    exact sol₁.1.interval_subset ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ sol₂.1.toIntrinsicDeTurckSolution.timeSet := by
    exact sol₂.1.interval_subset ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  exact intrinsicDeTurckLocalSolution_connection_eq_of_metric_eq
    (I := I) (M := M) sol₁.1 sol₂.1
    (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2)
    (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
    ht₁ ht₂
    (fun y u v ↦
      chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_interval_of_common_Ico
        (I := I) (M := M) sol₁ sol₂ hmetric ht y u v)
    hσ

/-- If chosen-background DeTurck metric uniqueness is available on every
prescribed shorter common terminal, then it is available on the open common
candidate overlap.  This is the order-theoretic continuation bridge from
restricted-terminal readouts to open-overlap readouts. -/
theorem chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_Ico_of_restricted_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hmetric : ∀ {S : ℝ},
      ivp.initialTime < S → S ≤ sol₁.1.terminalTime → S ≤ sol₂.1.terminalTime →
      ∀ {t : ℝ}, t ∈ Set.Icc ivp.initialTime S → ∀ (x : M) (u v : TM x),
        metricTensor (I := I) (M := M)
          sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
            metricTensor (I := I) (M := M)
              sol₂.1.toIntrinsicDeTurckSolution.metric t x u v)
    {t : ℝ} (ht : t ∈ Set.Ico ivp.initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
  rcases exists_between ht.2 with ⟨S, htS, hScommon⟩
  have hS₀ : ivp.initialTime < S := lt_of_le_of_lt ht.1 htS
  have hS₁ : S ≤ sol₁.1.terminalTime :=
    le_trans (le_of_lt hScommon) (min_le_left _ _)
  have hS₂ : S ≤ sol₂.1.terminalTime :=
    le_trans (le_of_lt hScommon) (min_le_right _ _)
  have htScc : t ∈ Set.Icc ivp.initialTime S := ⟨ht.1, le_of_lt htS⟩
  exact hmetric hS₀ hS₁ hS₂ htScc x u v

/-- Restricted-terminal metric uniqueness closes all the way to the common
terminal: the open-overlap continuation bridge supplies equality from the left,
and time-continuity of local solutions supplies the endpoint. -/
theorem chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_interval_of_restricted_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hmetric : ∀ {S : ℝ},
      ivp.initialTime < S → S ≤ sol₁.1.terminalTime → S ≤ sol₂.1.terminalTime →
      ∀ {t : ℝ}, t ∈ Set.Icc ivp.initialTime S → ∀ (x : M) (u v : TM x),
        metricTensor (I := I) (M := M)
          sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
            metricTensor (I := I) (M := M)
              sol₂.1.toIntrinsicDeTurckSolution.metric t x u v)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
  exact
    chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_interval_of_common_Ico
      (I := I) (M := M) sol₁ sol₂
      (fun {τ} hτ y w z =>
        chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_Ico_of_restricted_interval
          (I := I) (M := M) sol₁ sol₂ hmetric hτ y w z)
      ht x u v

/-- Restricted-terminal metric uniqueness also gives closed-common canonical
connection uniqueness for chosen-background DeTurck solutions. -/
theorem
    chosenIntrinsicDeTurckLocalSolution_connection_eq_on_common_interval_of_restricted_interval_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hmetric : ∀ {S : ℝ},
      ivp.initialTime < S → S ≤ sol₁.1.terminalTime → S ≤ sol₂.1.terminalTime →
      ∀ {t : ℝ}, t ∈ Set.Icc ivp.initialTime S → ∀ (x : M) (u v : TM x),
        metricTensor (I := I) (M := M)
          sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
            metricTensor (I := I) (M := M)
              sol₂.1.toIntrinsicDeTurckSolution.metric t x u v)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x := by
  exact
    chosenIntrinsicDeTurckLocalSolution_connection_eq_on_common_interval_of_common_Ico_metric
      (I := I) (M := M) sol₁ sol₂
      (fun {τ} hτ y u v =>
        chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_Ico_of_restricted_interval
          (I := I) (M := M) sol₁ sol₂ hmetric hτ y u v)
      ht hσ

/-- Build the chosen-background DeTurck theorem package from existence and
metric uniqueness on every prescribed shorter common terminal. -/
def ChosenIntrinsicDeTurckLocalExistenceUniqueness.ofRestrictedMetricReadout
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hexists : Nonempty (ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp))
    (hmetric : ∀ sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ {S : ℝ},
        ivp.initialTime < S → S ≤ sol₁.1.terminalTime → S ≤ sol₂.1.terminalTime →
        ∀ {t : ℝ}, t ∈ Set.Icc ivp.initialTime S → ∀ (x : M) (u v : TM x),
          metricTensor (I := I) (M := M)
            sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
              metricTensor (I := I) (M := M)
                sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := hexists
  unique_metric := by
    intro sol₁ sol₂ t ht x u v
    exact
      chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_interval_of_restricted_interval
        (I := I) (M := M) sol₁ sol₂ (hmetric sol₁ sol₂) ht x u v

/-- Convert the intrinsic compact theorem package to the chosen-background DeTurck one. -/
def IntrinsicLocalExistenceUniqueness.toChosenIntrinsicDeTurck
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨⟨sol.toChosenIntrinsicDeTurckLocalSolution,
      intrinsicLocalSolution_usesChosenBackground (I := I) (M := M) sol⟩⟩
  · intro sol₁ sol₂ t ht x u v
    simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution,
      IntrinsicDeTurckSolution.toIntrinsicSolution] using
      pkg.unique_metric
        (sol₁.1.toIntrinsicLocalSolution
          (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2))
        (sol₂.1.toIntrinsicLocalSolution
          (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2))
        t ht x u v

/-- Convert the chosen-background DeTurck compact theorem package back to the intrinsic Ricci-flow
one. -/
def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.1.toIntrinsicLocalSolution
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2)⟩
  · intro sol₁ sol₂ t ht x u v
    exact pkg.unique_metric
      ⟨sol₁.toChosenIntrinsicDeTurckLocalSolution,
        intrinsicLocalSolution_usesChosenBackground (I := I) (M := M) sol₁⟩
      ⟨sol₂.toChosenIntrinsicDeTurckLocalSolution,
        intrinsicLocalSolution_usesChosenBackground (I := I) (M := M) sol₂⟩
      t ht x u v

/-- The theorem-family version of chosen-background Ricci-DeTurck local
existence/uniqueness. -/
structure ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily where
  package :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalExistenceUniqueness
        (E := E) (H := H) (I := I) (M := M) ivp

/-- Build the chosen-background DeTurck theorem family from uniform existence
and metric uniqueness on every prescribed shorter common terminal. -/
def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.ofRestrictedMetricReadout
    (hexists : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      Nonempty (ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp))
    (hmetric :
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ {S : ℝ},
        ivp.initialTime < S → S ≤ sol₁.1.terminalTime → S ≤ sol₂.1.terminalTime →
        ∀ {t : ℝ}, t ∈ Set.Icc ivp.initialTime S → ∀ (x : M) (u v : TM x),
          metricTensor (I := I) (M := M)
            sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
              metricTensor (I := I) (M := M)
                sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    ChosenIntrinsicDeTurckLocalExistenceUniqueness.ofRestrictedMetricReadout
      (I := I) (M := M) (hexists ivp) (hmetric ivp)

def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsic
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.package ivp).toIntrinsic

def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinary
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.toIntrinsic ivp).toOrdinary

def IntrinsicLocalExistenceUniquenessFamily.toChosenIntrinsicDeTurck
    (pkg : IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toChosenIntrinsicDeTurck

def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := pkg.toIntrinsic

def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toIntrinsicFamily.toOrdinary

theorem ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.nonempty_localSolution
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  (pkg.toOrdinary ivp).exists_solution

/-- A Ricci-DeTurck local-existence/uniqueness package that does not restrict the background
connection carried by candidate local solutions. This is stronger than the chosen-background package
only in settings, such as zero-dimensional tangent fibers, where the DeTurck background no longer
affects the metric equation. -/
structure IntrinsicDeTurckLocalExistenceUniqueness
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- Existence of an intrinsic Ricci-DeTurck local solution with some background. -/
  exists_solution :
    Nonempty (IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
  /-- Metric uniqueness for arbitrary-background intrinsic Ricci-DeTurck local solutions. -/
  unique_metric :
    ∀ sol₁ sol₂ :
        IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime),
        ∀ x : M, ∀ u v : TM x,
          metricTensor (I := I) (M := M)
            sol₁.toIntrinsicDeTurckSolution.metric t x u v =
              metricTensor (I := I) (M := M)
                sol₂.toIntrinsicDeTurckSolution.metric t x u v

theorem IntrinsicDeTurckLocalExistenceUniqueness.nonempty_localSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.exists_solution

theorem IntrinsicDeTurckLocalExistenceUniqueness.metric_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicDeTurckSolution.metric t x u v :=
  pkg.unique_metric sol₁ sol₂ t ht x u v

/-- If every candidate DeTurck local solution in the package uses a Levi-Civita background for its
evolving metric, then the arbitrary-background DeTurck package yields the intrinsic Ricci-flow point-4
package. Existence converts the package's DeTurck solution; uniqueness rewrites arbitrary intrinsic
Ricci-flow candidates as chosen-background DeTurck candidates and uses DeTurck uniqueness. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_of_all_backgrounds_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : ∀ sol : IntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
        (I := I) (M := M)
        sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toIntrinsicLocalSolution (hbackground sol)⟩
  unique_metric := by
    intro sol₁ sol₂ t ht x u v
    exact pkg.unique_metric sol₁.toChosenIntrinsicDeTurckLocalSolution
      sol₂.toChosenIntrinsicDeTurckLocalSolution t ht x u v

/-- In the zero-dimensional tangent-fiber case, an intrinsic Ricci-flow local-existence package
gives a Ricci-DeTurck package whose uniqueness compares all backgrounds. -/
def IntrinsicLocalExistenceUniqueness.toIntrinsicDeTurck_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toChosenIntrinsicDeTurckLocalSolution⟩
  · intro sol₁ sol₂ t ht x u v
    exact intrinsicDeTurckLocalSolution_unique_metric_of_subsingleton_tangent
      (I := I) (M := M) sol₁ sol₂ ht x u v

/-- In the zero-dimensional tangent-fiber case, an arbitrary-background Ricci-DeTurck package
converts back to the intrinsic Ricci-flow package. -/
def IntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toIntrinsicLocalSolution_of_subsingleton_tangent⟩
  · intro sol₁ sol₂ t ht x u v
    simpa [IntrinsicLocalSolution.toChosenIntrinsicDeTurckLocalSolution,
      IntrinsicLocalSolution.toIntrinsicDeTurckLocalSolution,
      IntrinsicSolution.toIntrinsicDeTurckSolution] using
      pkg.unique_metric
        sol₁.toChosenIntrinsicDeTurckLocalSolution
        sol₂.toChosenIntrinsicDeTurckLocalSolution
        t ht x u v

/-- In the zero-dimensional tangent-fiber case, a chosen-background DeTurck package can be widened
to the arbitrary-background DeTurck package. -/
def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsicDeTurck_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toIntrinsic.toIntrinsicDeTurck_of_subsingleton_tangent

/-- In the zero-dimensional tangent-fiber case, an arbitrary-background DeTurck package can be
restricted back to the chosen-background package. -/
def IntrinsicDeTurckLocalExistenceUniqueness.toChosenIntrinsicDeTurck_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toIntrinsic_of_subsingleton_tangent.toChosenIntrinsicDeTurck

/-- The theorem-family version of arbitrary-background Ricci-DeTurck local
existence/uniqueness. -/
structure IntrinsicDeTurckLocalExistenceUniquenessFamily where
  package :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      IntrinsicDeTurckLocalExistenceUniqueness
        (E := E) (H := H) (I := I) (M := M) ivp

/-- Family-level version of
`IntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_of_all_backgrounds_isLeviCivita`. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsic_of_all_backgrounds_isLeviCivita
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
        (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp),
        CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
          (I := I) (M := M)
          sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toIntrinsic_of_all_backgrounds_isLeviCivita (hbackground ivp)

def IntrinsicLocalExistenceUniquenessFamily.toIntrinsicDeTurck_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toIntrinsicDeTurck_of_subsingleton_tangent

def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicDeTurck_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toIntrinsicDeTurck_of_subsingleton_tangent

def IntrinsicDeTurckLocalExistenceUniquenessFamily.toChosenIntrinsicDeTurck_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toChosenIntrinsicDeTurck_of_subsingleton_tangent

def IntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsic_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.package ivp).toIntrinsic_of_subsingleton_tangent

def IntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinary_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.toIntrinsic_of_subsingleton_tangent ivp).toOrdinary

def IntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := pkg.toIntrinsic_of_subsingleton_tangent

def IntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toIntrinsicFamily_of_subsingleton_tangent.toOrdinary

theorem IntrinsicDeTurckLocalExistenceUniquenessFamily.nonempty_localSolution_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  (pkg.toOrdinary_of_subsingleton_tangent ivp).exists_solution

/-- Arbitrary-background Ricci-DeTurck local existence/uniqueness on compact manifolds whose tangent
fibers are all subsingletons. -/
noncomputable def intrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
    [CompactSpace M] [∀ x : M, Subsingleton (TM x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_subsingleton_tangent (I := I) (M := M) ivp)
    |>.toIntrinsicDeTurck_of_subsingleton_tangent

noncomputable def intrinsicDeTurckLocalExistenceUniquenessFamily_of_subsingleton_tangent
    [CompactSpace M] [∀ x : M, Subsingleton (TM x)] :
    IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    intrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
      (I := I) (M := M) ivp

/-- Arbitrary-background Ricci-DeTurck local existence/uniqueness on empty compact manifolds. -/
noncomputable def intrinsicDeTurckLocalExistenceUniqueness_of_isEmpty
    [CompactSpace M] [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp := by
  letI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  exact intrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
    (I := I) (M := M) ivp

noncomputable def intrinsicDeTurckLocalExistenceUniquenessFamily_of_isEmpty
    [CompactSpace M] [IsEmpty M] :
    IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    intrinsicDeTurckLocalExistenceUniqueness_of_isEmpty (I := I) (M := M) ivp

/-- Chosen-background Ricci-DeTurck local existence/uniqueness on compact manifolds whose tangent
fibers are all subsingletons. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
    [CompactSpace M] [∀ x : M, Subsingleton (TM x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_subsingleton_tangent (I := I) (M := M) ivp)
    |>.toChosenIntrinsicDeTurck

noncomputable def chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_subsingleton_tangent
    [CompactSpace M] [∀ x : M, Subsingleton (TM x)] :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    chosenIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
      (I := I) (M := M) ivp

/-- Chosen-background Ricci-DeTurck version of the empty-compact-manifold point-4 package. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniqueness_of_isEmpty
    [CompactSpace M] [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_isEmpty (I := I) (M := M) ivp).toChosenIntrinsicDeTurck

noncomputable def chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_isEmpty
    [CompactSpace M] [IsEmpty M] :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    chosenIntrinsicDeTurckLocalExistenceUniqueness_of_isEmpty (I := I) (M := M) ivp

theorem chosenIntrinsicDeTurckLocalExistenceUniqueness_connection_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x := by
  have ht₁ : t ∈ sol₁.1.toIntrinsicDeTurckSolution.timeSet := by
    exact sol₁.1.interval_subset ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ sol₂.1.toIntrinsicDeTurckSolution.timeSet := by
    exact sol₂.1.interval_subset ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  exact intrinsicDeTurckLocalSolution_connection_eq_of_metric_eq
    (I := I) (M := M) sol₁.1 sol₂.1
    (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2)
    (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
    ht₁ ht₂
    (fun y u v ↦ pkg.unique_metric sol₁ sol₂ t ht y u v)
    hσ

theorem ChosenIntrinsicDeTurckLocalExistenceUniqueness.connection_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x :=
  chosenIntrinsicDeTurckLocalExistenceUniqueness_connection_eq_on_common_interval
    (I := I) (M := M) pkg sol₁ sol₂ ht hσ

theorem ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.connection_eq_on_common_interval
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x :=
  (pkg.package ivp).connection_eq_on_common_interval sol₁ sol₂ ht hσ

/-- The canonical intrinsic Ricci-DeTurck local solution attached to Ricci-flat initial data,
using the chosen smooth Levi-Civita family as background. -/
noncomputable def stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
    (I := I) (M := M) ivp hRicciFlat).toChosenIntrinsicDeTurckLocalSolution

theorem chosenIntrinsicDeTurckLocalSolution_nonempty_of_isRicciFlat
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) := by
  exact ⟨stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
    (I := I) (M := M) ivp hRicciFlat⟩

theorem stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).terminalTime,
      ∀ x : M, ∀ u v : TM x,
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metricVelocity
          t x u v = 0 := by
  simpa [stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat,
    IntrinsicLocalSolution.toChosenIntrinsicDeTurckLocalSolution,
    IntrinsicLocalSolution.toIntrinsicDeTurckLocalSolution,
    IntrinsicSolution.toChosenIntrinsicDeTurckSolution,
    IntrinsicSolution.toIntrinsicDeTurckSolution] using
    stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat

theorem stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciTensor_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
            (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric
          t x u v = 0 :=
  (intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
    (I := I) (M := M)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)).1
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)

theorem stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciFlowRHS_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric
      t x u v = 0 :=
  intrinsicRicciFlowRHS_eq_zero_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) ivp hRicciFlat t ht x u v)

theorem stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciDeTurckRHS_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.background
      t x u v = 0 :=
  intrinsicRicciDeTurckRHS_eq_zero_of_isLeviCivita_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.background
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) ivp hRicciFlat t ht x u v)

theorem stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metric_eq_initial
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric
      t x u v =
        ivp.initialMetric.inner x u v := by
  exact intrinsicDeTurckLocalSolution_metric_eq_initial_of_zero_velocity
    (I := I) (M := M)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)
    ht x u v

theorem stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_connection_eq_initial
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).canonicalConnection
      (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric) t σ x =
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).canonicalConnection
        (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
          (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
            (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)
        ivp.initialTime σ x := by
  exact intrinsicDeTurckLocalSolution_connection_eq_initial_of_zero_velocity
    (I := I) (M := M)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)
    ht hσ

theorem stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_metric_of_zero_velocity
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric
      t x u v =
        metricTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v := by
  exact intrinsicDeTurckLocalSolution_unique_metric_of_zero_velocity
    (I := I) (M := M)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    sol
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)
    hbackground
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)
    hzero
    ht x u v

theorem stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_metric_of_ricciTensor_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric
      t x u v =
        metricTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v := by
  exact intrinsicDeTurckLocalSolution_unique_metric_of_ricciTensor_zero
    (I := I) (M := M)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    sol
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)
    hbackground
    ((intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat)
      (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)).1
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
        (I := I) (M := M) ivp hRicciFlat))
    hRicciZero
    ht x u v

theorem stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_connection_of_zero_velocity
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).canonicalConnection
      (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric) t σ x =
      sol.canonicalConnection hbackground t σ x := by
  exact intrinsicDeTurckLocalSolution_unique_connection_of_zero_velocity
    (I := I) (M := M)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    sol
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)
    hbackground
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)
    hzero
    ht hσ

theorem stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_connection_of_ricciTensor_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).canonicalConnection
      (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric) t σ x =
      sol.canonicalConnection hbackground t σ x := by
  exact intrinsicDeTurckLocalSolution_unique_connection_of_ricciTensor_zero
    (I := I) (M := M)
    (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    sol
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)
    hbackground
    ((intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M)
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat)
      (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
        (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).toIntrinsicDeTurckSolution.metric)).1
      (stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
        (I := I) (M := M) ivp hRicciFlat))
    hRicciZero
    ht hσ

end ChosenLeviCivita

end RicciFlow
