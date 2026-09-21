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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Along
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InducedHomRegularity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TorsionRegularity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.HomBundleComp

/-!
# Higher regularity of the Levi-Civita correction

The static correction construction in `LeviCivita` is initially given at the
`C¹` level.  This file develops the next regularity level from explicit
smoothness of the reference connection and Riemannian metric.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 3 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TStar" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "TEnd" => (fun x : M => TM x →L[ℝ] TM x)
local notation "TCorr" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x)

namespace CovariantDerivative

/-- The metric dual of a `C³` tangent field is a `C³` cotangent section when
the actual Riemannian metric is `C³`. -/
theorem contMDiffOn_toDualSection_three
    {u : Set M} (hu : IsOpen u)
    {σ : Π y : M, TM y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (σ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 3
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) y
        (InnerProductSpace.toDual ℝ (TM y) (σ y))) u := by
  rcases (show IsContMDiffRiemannianBundle I 3 E TM from inferInstance).exists_contMDiff with
    ⟨g, hg, hinner⟩
  have hgOn : ContMDiffOn I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 3
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E :=
        fun x : M ↦ TM x →L[ℝ] TM x →L[ℝ] ℝ) y (g y)) u := by
    exact hg.contMDiffOn.mono (Set.subset_univ _)
  have happly : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 3
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) y (g y (σ y))) u := by
    exact hgOn.clm_bundle_apply hσ
  refine ContMDiffOn.congr happly ?_
  intro y hy
  refine congrArg (fun φ ↦ TotalSpace.mk' (E := TStar) (E →L[ℝ] ℝ) y φ) ?_
  ext v
  simp [hinner]

/-- A `C²` tangent field has a `C²` metric dual when the actual metric is
`C³`. -/
theorem contMDiffOn_toDualSection_two
    {u : Set M} (hu : IsOpen u)
    {σ : Π y : M, TM y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (σ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) y
        (InnerProductSpace.toDual ℝ (TM y) (σ y))) u := by
  rcases (show IsContMDiffRiemannianBundle I 3 E TM from inferInstance).exists_contMDiff with
    ⟨g, hg, hinner⟩
  have hgOn : ContMDiffOn I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E :=
        fun x : M ↦ TM x →L[ℝ] TM x →L[ℝ] ℝ) y (g y)) u := by
    exact (hg.contMDiffOn.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).mono (Set.subset_univ _)
  have happly : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) y (g y (σ y))) u := by
    exact hgOn.clm_bundle_apply hσ
  refine ContMDiffOn.congr happly ?_
  intro y hy
  refine congrArg (fun φ ↦ TotalSpace.mk' (E := TStar) (E →L[ℝ] ℝ) y φ) ?_
  ext v
  simp [hinner]

/-- If the reference connection is `C²` and the actual metric is `C³`, its
metric-defect covector on two `C³` fields is `C²`.  The proof uses the
defining metric-defect formula, retaining both the differentiated actual
metric pairing and the reference-connection terms. -/
theorem contMDiffOn_metricDefect_section_two
    {s : Set M} (hs : IsOpen s)
    {cov : CovariantDerivative I E TM}
    (hcov : ContMDiffCovariantDerivativeOn E 2 cov.toFun s)
    {σ τ : Π y : M, TM y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (σ y)) s)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (τ y)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (cov.metricDefect x (σ x) (τ x))) s := by
  have hinner : ContMDiffOn I 𝓘(ℝ) 3 (fun y => inner ℝ (σ y) (τ y)) s := by
    exact ContMDiffOn.inner_bundle (IM := I) (IB := I) (F := E) (E := TM)
      (b := id) (v := σ) (w := τ) hσ hτ
  have hext :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
          (mvfderiv (I := I) (fun y => inner ℝ (σ y) (τ y)) x)) s := by
    intro x hx
    exact (((hinner x hx).contMDiffAt (hs.mem_nhds hx)).extDerivSection
      (I := I) (E := E) (m := (2 : WithTop ℕ∞)) (n := 3) (by norm_num)).contMDiffWithinAt
  have hcovσ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x (cov σ x)) s :=
    hcov.contMDiff hσ
  have hcovτ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x (cov τ x)) s :=
    hcov.contMDiff hτ
  have hτdual := contMDiffOn_toDualSection_three (I := I) (E := E) hs hτ
  have hσdual := contMDiffOn_toDualSection_three (I := I) (E := E) hs hσ
  have htermστ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        ((InnerProductSpace.toDual ℝ (TM x) (τ x)).comp (cov σ x))) s := by
    exact (hτdual.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).clm_bundle_comp hcovσ
  have htermτσ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        ((InnerProductSpace.toDual ℝ (TM x) (σ x)).comp (cov τ x))) s := by
    exact (hσdual.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).clm_bundle_comp hcovτ
  have haux : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (metricDefectAux cov x σ τ)) s := by
    simpa [metricDefectAux] using (hext.sub_section htermστ).sub_section htermτσ
  refine ContMDiffOn.congr haux ?_
  intro x hx
  refine congrArg (fun φ ↦ TotalSpace.mk' (E := TStar) (E →L[ℝ] ℝ) x φ) ?_
  exact cov.metricDefect_apply_sections
    ((((hσ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero)
    ((((hτ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero)

/-- Pairing a `C²` torsion tensor with the actual `C³` metric remains `C²`.
This is the torsion term needed by the Levi-Civita correction formula. -/
theorem contMDiffOn_torsionInner_section_two
    {s : Set M} (hs : IsOpen s)
    {cov : CovariantDerivative I E TM}
    (hcov : ContMDiffCovariantDerivativeOn E 2 cov.toFun s)
    {σ τ : Π y : M, TM y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (σ y)) s)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (τ y)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (torsionInnerFunctional (I := I) cov x (σ x) (τ x))) s := by
  have hTorsion := contMDiffOn_torsion_section_two (I := I) (E := E) hs hcov hσ hτ
  have hdual := contMDiffOn_toDualSection_two (I := I) (E := E) hs hTorsion
  refine ContMDiffOn.congr hdual ?_
  intro x hx
  refine congrArg (fun φ ↦ TotalSpace.mk' (E := TStar) (E →L[ℝ] ℝ) x φ) ?_
  ext w
  simp [torsionInnerFunctional_apply]

/-- The pointwise Levi-Civita correction functional is `C²` when the reference
connection is `C²` and the actual Riemannian metric is `C³`. -/
theorem contMDiffOn_correctionFunctional_apply_section_two
    {u : Set M} (hu : IsOpen u)
    {cov : CovariantDerivative I E TM}
    (hcov : ContMDiffCovariantDerivativeOn E 2 cov.toFun u)
    {σ τ υ : Π y : M, TM y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (σ y)) u)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (τ y)) u)
    (hυ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (υ y)) u) :
    ContMDiffOn I 𝓘(ℝ) 2
      (fun x ↦ correctionFunctional cov x (σ x) (τ x) (υ x)) u := by
  have hσ₂ := hσ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hτ₂ := hτ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hυ₂ := hυ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hmetricσυ := contMDiffOn_metricDefect_section_two (I := I) (E := E) hu hcov hσ hυ
  have hmetricτυ := contMDiffOn_metricDefect_section_two (I := I) (E := E) hu hcov hτ hυ
  have hmetricτσ := contMDiffOn_metricDefect_section_two (I := I) (E := E) hu hcov hτ hσ
  have hterm1 : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun x ↦ TotalSpace.mk' ℝ x (cov.metricDefect x (σ x) (υ x) (τ x))) u := by
    simpa using hmetricσυ.clm_bundle_apply hτ₂
  have hterm2 : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun x ↦ TotalSpace.mk' ℝ x (cov.metricDefect x (τ x) (υ x) (σ x))) u := by
    simpa using hmetricτυ.clm_bundle_apply hσ₂
  have hterm3 : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun x ↦ TotalSpace.mk' ℝ x (cov.metricDefect x (τ x) (σ x) (υ x))) u := by
    simpa using hmetricτσ.clm_bundle_apply hυ₂
  have htorsτσ := contMDiffOn_torsionInner_section_two (I := I) (E := E) hu hcov hτ hσ
  have htorsσυ := contMDiffOn_torsionInner_section_two (I := I) (E := E) hu hcov hσ hυ
  have htorsυτ := contMDiffOn_torsionInner_section_two (I := I) (E := E) hu hcov hυ hτ
  have htors1 : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun x ↦ TotalSpace.mk' ℝ x
        (torsionInnerFunctional (I := I) cov x (τ x) (σ x) (υ x))) u := by
    simpa using htorsτσ.clm_bundle_apply hυ₂
  have htors2 : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun x ↦ TotalSpace.mk' ℝ x
        (torsionInnerFunctional (I := I) cov x (σ x) (υ x) (τ x))) u := by
    simpa using htorsσυ.clm_bundle_apply hτ₂
  have htors3 : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun x ↦ TotalSpace.mk' ℝ x
        (torsionInnerFunctional (I := I) cov x (υ x) (τ x) (σ x))) u := by
    simpa using htorsυτ.clm_bundle_apply hσ₂
  have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun x ↦ TotalSpace.mk' ℝ x
        (cov.metricDefect x (σ x) (υ x) (τ x) +
          cov.metricDefect x (τ x) (υ x) (σ x) -
          cov.metricDefect x (τ x) (σ x) (υ x) -
          torsionInnerFunctional (I := I) cov x (τ x) (σ x) (υ x) +
          torsionInnerFunctional (I := I) cov x (σ x) (υ x) (τ x) -
          torsionInnerFunctional (I := I) cov x (υ x) (τ x) (σ x))) u := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      ((((hterm1.add_section hterm2).sub_section hterm3).sub_section htors1).add_section
        htors2).sub_section htors3
  have hcorrectionSection : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun x ↦ TotalSpace.mk' ℝ x
        (correctionFunctional cov x (σ x) (τ x) (υ x))) u := by
    have hscaled : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
        (fun x ↦ TotalSpace.mk' ℝ x
          ((1 / 2 : ℝ) *
            (cov.metricDefect x (σ x) (υ x) (τ x) +
              cov.metricDefect x (τ x) (υ x) (σ x) -
              cov.metricDefect x (τ x) (σ x) (υ x) -
              torsionInnerFunctional (I := I) cov x (τ x) (σ x) (υ x) +
              torsionInnerFunctional (I := I) cov x (σ x) (υ x) (τ x) -
              torsionInnerFunctional (I := I) cov x (υ x) (τ x) (σ x)))) u := by
      simpa [Pi.smul_apply, smul_eq_mul] using contMDiffOn_const.smul_section hsum
    refine ContMDiffOn.congr hscaled ?_
    intro x hx
    simp [correctionFunctional_apply, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  exact
    ((eLine.contMDiffOn_section_iff (IB := I) (n := (2 : WithTop ℕ∞))
      (s := fun x ↦ correctionFunctional cov x (σ x) (τ x) (υ x)) (a := u) hu
      (by
        intro x hx
        change x ∈ (Bundle.Trivial.trivialization M ℝ).baseSet
        simp [Bundle.Trivial.trivialization])).mp hcorrectionSection)

/-- The covector-valued correction functional is a `C²` section, as checked
in the induced cotangent frame. -/
theorem contMDiffOn_correctionFunctional_section_two
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 2 cov.toFun u)
    {σ τ : Π y : M, TM y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (σ y)) u)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (τ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (correctionFunctional cov x (σ x) (τ x))) u := by
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  let eStar : Trivialization (E →L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) TStar → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  let corrSec : Π x : M, TStar x := fun x ↦ correctionFunctional cov x (σ x) (τ x)
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) 2
      ((LinearMap.piApply (eStar.localFrameCoeff I (continuousDualBasis b) i)) corrSec) u := by
    intro i
    have hframe : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
        (fun y ↦ TotalSpace.mk' E y (e.localFrame b i y)) u :=
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (3 : WithTop ℕ∞)) (b := b) i).mono hu'
    have happly : ContMDiffOn I 𝓘(ℝ) 2
        (fun x ↦ correctionFunctional cov x (σ x) (τ x) (e.localFrame b i x)) u :=
      contMDiffOn_correctionFunctional_apply_section_two (I := I) (E := E)
        hu hcov hσ hτ hframe
    refine ContMDiffOn.congr happly ?_
    intro x hx
    have hxE : x ∈ e.baseSet := hu' hx
    have hxStar : x ∈ eStar.baseSet := huStar hx
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE,
      show ((LinearMap.piApply (eStar.localFrameCoeff I (continuousDualBasis b) i)) corrSec) x =
          eStar.localFrameCoeff I (continuousDualBasis b) i x (corrSec x) by rfl,
      Bundle.Trivialization.localFrameCoeff_eq_coeff
        (I := I) (e := eStar) (b := continuousDualBasis b) (s := corrSec)
        (hxe := hxStar) (i := i),
      continuousDualBasis_repr]
    simp [corrSec, eStar, eLine, Bundle.Trivialization.continuousLinearMap_apply,
      Bundle.Trivialization.basisAt, correctionFunctional_apply, hxE, hxStar]
  have hsStar : IsLocalFrameOn I (E →L[ℝ] ℝ) 2
      (eStar.localFrame (continuousDualBasis b)) u :=
    (eStar.isLocalFrameOn_localFrame_baseSet I 2 (continuousDualBasis b)).mono huStar
  have hcoeffStar : ∀ i, ContMDiffOn I 𝓘(ℝ) 2
      ((LinearMap.piApply (hsStar.coeff i)) corrSec) u := by
    intro i
    refine (hcoeff i).congr ?_
    intro x hx
    have hbasis : hsStar.toBasisAt hx = eStar.basisAt (continuousDualBasis b) (huStar hx) := by
      ext j
      simp [hsStar, IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
        Bundle.Trivialization.basisAt, huStar hx]
    change hsStar.coeff i x (corrSec x) =
      eStar.localFrameCoeff I (continuousDualBasis b) i x (corrSec x)
    rw [IsLocalFrameOn.coeff_apply_of_mem (hs := hsStar) hx corrSec i,
      Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
        (I := I) (e := eStar) (b := continuousDualBasis b) (hx := huStar hx)
        (s := corrSec) (i := i)]
    simp [hbasis]
  have hωSection : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (corrSec x)) u :=
    hsStar.contMDiffOn_of_coeff hcoeffStar
  simpa [corrSec] using hωSection

/-- The Riesz representative of a `C²` cotangent section is `C²` under the
actual `C³` Riemannian metric.  In a tangent frame its coefficients are the
inverse Gram matrix applied to the covector coefficients. -/
theorem contMDiffOn_rieszMap_section_two
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    {omega : Π x : M, TStar x}
    (hω : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (omega x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun x ↦ TotalSpace.mk' E x (rieszMap (I := I) x (omega x))) u := by
  classical
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  let eStar : Trivialization (E →L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) TStar → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  have hωcoeff : ∀ j, ContMDiffOn I 𝓘(ℝ) 2
      (fun x ↦ omega x (e.localFrame b j x)) u := by
    intro j
    have hj : ContMDiffOn I 𝓘(ℝ) 2
        ((LinearMap.piApply (eStar.localFrameCoeff I (continuousDualBasis b) j)) omega) u :=
      contMDiffOn_localFrameCoeff
        (I := I) (e := eStar) (b := continuousDualBasis b) hu huStar hω j
    refine ContMDiffOn.congr hj ?_
    intro x hx
    have hxE : x ∈ e.baseSet := hu' hx
    have hxStar : x ∈ eStar.baseSet := huStar hx
    rw [show ((LinearMap.piApply (eStar.localFrameCoeff I (continuousDualBasis b) j)) omega) x =
        eStar.localFrameCoeff I (continuousDualBasis b) j x (omega x) by rfl,
      Bundle.Trivialization.localFrameCoeff_eq_coeff
        (I := I) (e := eStar) (b := continuousDualBasis b) (s := omega)
        (hxe := hxStar) (i := j),
      continuousDualBasis_repr]
    simp [eStar, eLine, Bundle.Trivialization.continuousLinearMap_apply,
      Bundle.Trivialization.basisAt, hxE, hxStar]
  have hInvEntry : ∀ i j, ContMDiffOn I 𝓘(ℝ) 2
      (fun x ↦
        (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j)) u := by
    intro i j
    have hInv := contMDiffOn_localFrameGramMatrix_inv (I := I) (E := E) e b hu hu'
    rw [contMDiffOn_pi_space] at hInv
    have hi := hInv i
    rw [contMDiffOn_pi_space] at hi
    exact hi j
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) 2
      ((LinearMap.piApply (e.localFrameCoeff I b i))
        (fun x ↦ rieszMap (I := I) x (omega x))) u := by
    intro i
    have hsum : ∀ s : Finset ι, ContMDiffOn I 𝓘(ℝ) 2
        (fun x ↦ s.sum fun j =>
          (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j) *
            omega x (e.localFrame b j x)) u := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simpa using (contMDiffOn_const :
          ContMDiffOn I 𝓘(ℝ) 2 (fun _ : M ↦ (0 : ℝ)) u)
      · intro j s hj hs
        have hfirst : ContMDiffOn I 𝓘(ℝ) 2
            (fun x ↦
              (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j) *
                omega x (e.localFrame b j x)) u :=
          (hInvEntry i j).mul (hωcoeff j)
        have hadd : ContMDiffOn I 𝓘(ℝ) 2
            (fun x ↦
              (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j) *
                  omega x (e.localFrame b j x) +
                s.sum (fun j' =>
                  (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ :
                      Matrix ι ι ℝ) i j') *
                    omega x (e.localFrame b j' x))) u :=
          hfirst.add hs
        refine ContMDiffOn.congr hadd ?_
        intro x hx
        simp [Finset.sum_insert, hj, add_assoc, add_comm, add_left_comm]
    refine ContMDiffOn.congr (hsum Finset.univ) ?_
    intro x hx
    simpa using
      (localFrameCoeff_rieszMap (I := I) (E := E) (e := e) (b := b)
        (omega := omega) (hx := hu' hx) (i := i))
  exact (contMDiffOn_iff_localFrameCoeff
    (I := I) (e := e) (b := b)
    (s := fun x ↦ rieszMap (I := I) x (omega x)) (t := u) (k := (2 : WithTop ℕ∞)) hu hu').2 hcoeff

/-- The correction applied to two `C³` tangent fields is a `C²` tangent
field. -/
theorem contMDiffOn_leviCivitaCorrection_apply_section_two
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 2 cov.toFun u)
    {σ τ : Π y : M, TM y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (σ y)) u)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (τ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun x ↦ TotalSpace.mk' E x (cov.leviCivitaCorrection x (σ x) (τ x))) u := by
  have hcorr : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (correctionFunctional cov x (σ x) (τ x))) u :=
    contMDiffOn_correctionFunctional_section_two (I := I) (E := E) e b hu hu' hcov hσ hτ
  simpa [CovariantDerivative.leviCivitaCorrection_apply] using
    contMDiffOn_rieszMap_section_two (I := I) (E := E) (e := e) (b := b) hu hu' hcorr

/-- With the first tangent input left free, the Levi-Civita correction is a
`C²` endomorphism-valued section. -/
theorem contMDiffOn_leviCivitaCorrection_partial_section_two
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 2 cov.toFun u)
    {σ : Π y : M, TM y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (σ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x
        (cov.leviCivitaCorrection x (σ x))) u := by
  classical
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  let eStar : Trivialization (E →L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) TStar → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  have hdual : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (eStar.localFrame (continuousDualBasis b) i x)) u := by
    intro i
    exact (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := eStar)
      (n := (2 : WithTop ℕ∞)) (b := continuousDualBasis b) i).mono huStar
  have hvalue : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun x ↦ TotalSpace.mk' E x
        (cov.leviCivitaCorrection x (σ x) (e.localFrame b i x))) u := by
    intro i
    have hframe : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
        (fun x ↦ TotalSpace.mk' E x (e.localFrame b i x)) u :=
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (3 : WithTop ℕ∞)) (b := b) i).mono hu'
    exact contMDiffOn_leviCivitaCorrection_apply_section_two
      (I := I) (E := E) e b hu hu' hcov hσ hframe
  have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x
        (∑ i, (eStar.localFrame (continuousDualBasis b) i x).smulRight
          (cov.leviCivitaCorrection x (σ x) (e.localFrame b i x)))) u := by
    simpa using
      (ContMDiffOn.sum_section (s := (Finset.univ : Finset ι)) fun i hi ↦
        ContMDiffOn.smulRightSection_of_level (n := (2 : WithTop ℕ∞))
          (I := I) (F := E) (V := TM) hu (hdual i) (hvalue i))
  refine ContMDiffOn.congr hsum ?_
  intro x hx
  have hxE : x ∈ e.baseSet := hu' hx
  have hxStar : x ∈ eStar.baseSet := huStar hx
  apply congrArg (fun A ↦ TotalSpace.mk' (E := TEnd) (E →L[ℝ] E) x A)
  ext v
  let basis := e.basisAt b hxE
  let s : Π y : M, TM y := fun y ↦ ∑ j, basis.repr v j • e.localFrame b j y
  have hsx : s x = v := by
    simpa [s, basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      using basis.sum_repr v
  have hcoeff_v : ∀ i, e.localFrameCoeff I b i x v = basis.repr v i := by
    intro i
    calc
      e.localFrameCoeff I b i x v = e.localFrameCoeff I b i x (s x) := by rw [hsx]
      _ = basis.repr (s x) i := by
            simpa [basis] using
              (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
                (I := I) (e := e) (b := b) (hx := hxE) (s := s) (i := i))
      _ = basis.repr v i := by rw [hsx]
  have hdual_basis : ∀ i j,
      eStar.localFrame (continuousDualBasis b) i x (e.localFrame b j x) = if i = j then 1 else 0 := by
    intro i j
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := eStar) (b := continuousDualBasis b) hxStar,
      Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
    simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
    rw [Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
    rw [← Bundle.Trivialization.symmL_apply (R := ℝ) e hxE]
    have hsymm : eStar.symm x ((continuousDualBasis b) i) =
        (eLine.symmL ℝ x).comp (((continuousDualBasis b) i).comp (e.continuousLinearMapAt ℝ x)) := by
      change (Bundle.Pretrivialization.continuousLinearMap (RingHom.id ℝ) e eLine).symm x
          ((continuousDualBasis b) i) =
        (eLine.symmL ℝ x).comp
          (((continuousDualBasis b) i).comp (e.continuousLinearMapAt ℝ x))
      simpa [eLine] using
        (Bundle.Pretrivialization.continuousLinearMap_symm_apply'
          (σ := RingHom.id ℝ) (e₁ := e) (e₂ := eLine) (b := x)
          (hb := ⟨hxE, by simp [eLine]⟩) ((continuousDualBasis b) i))
    rw [hsymm]
    simp only [ContinuousLinearMap.comp_apply]
    rw [Bundle.Trivialization.continuousLinearMapAt_symmL (e := e) (R := ℝ) (hb := hxE)]
    simpa [eLine, continuousDualBasis, Finsupp.single_apply, eq_comm]
  have hdual_apply : ∀ i, eStar.localFrame (continuousDualBasis b) i x v =
      e.localFrameCoeff I b i x v := by
    intro i
    calc
      eStar.localFrame (continuousDualBasis b) i x v =
          eStar.localFrame (continuousDualBasis b) i x
            (∑ j, basis.repr v j • basis j) := by rw [basis.sum_repr v]
      _ = ∑ j, basis.repr v j * eStar.localFrame (continuousDualBasis b) i x (basis j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [map_smul]
            simp [smul_eq_mul]
      _ = ∑ j, basis.repr v j * (if i = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa [basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
              using congrArg (fun r : ℝ ↦ basis.repr v j * r) (hdual_basis i j)
      _ = basis.repr v i := by simp
      _ = e.localFrameCoeff I b i x v := by rw [hcoeff_v i]
  have hdecomp :
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x = v := by
    calc
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x =
          ∑ i, e.localFrameCoeff I b i x v • e.localFrame b i x := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hdual_apply i]
      _ = ∑ i, basis.repr v i • basis i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [basis, hcoeff_v i,
              Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      _ = v := by simpa using basis.sum_repr v
  have hmap :
      (cov.leviCivitaCorrection x (σ x))
          (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x) =
        ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v •
          cov.leviCivitaCorrection x (σ x) (e.localFrame b i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [map_smul]
  calc
    cov.leviCivitaCorrection x (σ x) v =
        (cov.leviCivitaCorrection x (σ x))
          (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x) := by
            rw [hdecomp]
    _ = ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v •
          cov.leviCivitaCorrection x (σ x) (e.localFrame b i x) := by rw [hmap]
    _ = (∑ i, (eStar.localFrame (continuousDualBasis b) i x).smulRight
          (cov.leviCivitaCorrection x (σ x) (e.localFrame b i x))) v := by
            simp [ContinuousLinearMap.smulRight_apply]

/-- The full tensor-valued Levi-Civita correction is `C²` over a tangent
trivialization. -/
theorem contMDiffOn_leviCivitaCorrection_section_two
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 2 cov.toFun u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E :=
        fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] TM y) x (cov.leviCivitaCorrection x)) u := by
  classical
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  let eStar : Trivialization (E →L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) TStar → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  have hdual : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
        (eStar.localFrame (continuousDualBasis b) i x)) u := by
    intro i
    exact (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := eStar)
      (n := (2 : WithTop ℕ∞)) (b := continuousDualBasis b) i).mono huStar
  have hvalue : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x
        (cov.leviCivitaCorrection x (e.localFrame b i x))) u := by
    intro i
    have hframe : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
        (fun x ↦ TotalSpace.mk' E x (e.localFrame b i x)) u :=
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (3 : WithTop ℕ∞)) (b := b) i).mono hu'
    exact contMDiffOn_leviCivitaCorrection_partial_section_two
      (I := I) (E := E) e b hu hu' hcov hframe
  letI endThree : ContMDiffVectorBundle 3 (E →L[ℝ] E) TEnd I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI endOne : ContMDiffVectorBundle 1 (E →L[ℝ] E) TEnd I :=
    ContMDiffVectorBundle.of_le (m := 1) (n := 3) (by norm_num)
  have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E :=
        fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] TM y) x
        (∑ i, (eStar.localFrame (continuousDualBasis b) i x).smulRight
          (cov.leviCivitaCorrection x (e.localFrame b i x)))) u := by
    simpa using
      (ContMDiffOn.sum_section (s := (Finset.univ : Finset ι)) fun i hi ↦
        ContMDiffOn.smulRightSection_of_level (n := (2 : WithTop ℕ∞))
          (I := I) (F := E →L[ℝ] E) (V := TEnd) hu (hdual i) (hvalue i))
  refine ContMDiffOn.congr hsum ?_
  intro x hx
  have hxE : x ∈ e.baseSet := hu' hx
  have hxStar : x ∈ eStar.baseSet := huStar hx
  apply congrArg (fun A ↦ TotalSpace.mk' (E :=
    fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] TM y)
      (E →L[ℝ] E →L[ℝ] E) x A)
  ext v u'
  let basis := e.basisAt b hxE
  let s : Π y : M, TM y := fun y ↦ ∑ j, basis.repr v j • e.localFrame b j y
  have hsx : s x = v := by
    simpa [s, basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      using basis.sum_repr v
  have hcoeff_v : ∀ i, e.localFrameCoeff I b i x v = basis.repr v i := by
    intro i
    calc
      e.localFrameCoeff I b i x v = e.localFrameCoeff I b i x (s x) := by rw [hsx]
      _ = basis.repr (s x) i := by
            simpa [basis] using
              (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
                (I := I) (e := e) (b := b) (hx := hxE) (s := s) (i := i))
      _ = basis.repr v i := by rw [hsx]
  have hdual_basis : ∀ i j,
      eStar.localFrame (continuousDualBasis b) i x (e.localFrame b j x) = if i = j then 1 else 0 := by
    intro i j
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := eStar) (b := continuousDualBasis b) hxStar,
      Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
    simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
    rw [Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
    rw [← Bundle.Trivialization.symmL_apply (R := ℝ) e hxE]
    have hsymm : eStar.symm x ((continuousDualBasis b) i) =
        (eLine.symmL ℝ x).comp (((continuousDualBasis b) i).comp (e.continuousLinearMapAt ℝ x)) := by
      change (Bundle.Pretrivialization.continuousLinearMap (RingHom.id ℝ) e eLine).symm x
          ((continuousDualBasis b) i) =
        (eLine.symmL ℝ x).comp
          (((continuousDualBasis b) i).comp (e.continuousLinearMapAt ℝ x))
      simpa [eLine] using
        (Bundle.Pretrivialization.continuousLinearMap_symm_apply'
          (σ := RingHom.id ℝ) (e₁ := e) (e₂ := eLine) (b := x)
          (hb := ⟨hxE, by simp [eLine]⟩) ((continuousDualBasis b) i))
    rw [hsymm]
    simp only [ContinuousLinearMap.comp_apply]
    rw [Bundle.Trivialization.continuousLinearMapAt_symmL (e := e) (R := ℝ) (hb := hxE)]
    simpa [eLine, continuousDualBasis, Finsupp.single_apply, eq_comm]
  have hdual_apply : ∀ i, eStar.localFrame (continuousDualBasis b) i x v =
      e.localFrameCoeff I b i x v := by
    intro i
    calc
      eStar.localFrame (continuousDualBasis b) i x v =
          eStar.localFrame (continuousDualBasis b) i x
            (∑ j, basis.repr v j • basis j) := by rw [basis.sum_repr v]
      _ = ∑ j, basis.repr v j * eStar.localFrame (continuousDualBasis b) i x (basis j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [map_smul]
            simp [smul_eq_mul]
      _ = ∑ j, basis.repr v j * (if i = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa [basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
              using congrArg (fun r : ℝ ↦ basis.repr v j * r) (hdual_basis i j)
      _ = basis.repr v i := by simp
      _ = e.localFrameCoeff I b i x v := by rw [hcoeff_v i]
  have hdecomp :
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x = v := by
    calc
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x =
          ∑ i, e.localFrameCoeff I b i x v • e.localFrame b i x := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hdual_apply i]
      _ = ∑ i, basis.repr v i • basis i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [basis, hcoeff_v i,
              Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      _ = v := by simpa using basis.sum_repr v
  have hmap :
      (cov.leviCivitaCorrection x)
          (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x) =
        ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v •
          cov.leviCivitaCorrection x (e.localFrame b i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [map_smul]
  calc
    cov.leviCivitaCorrection x v u' =
        ((cov.leviCivitaCorrection x)
          (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x)) u' := by
            rw [hdecomp]
    _ = (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v •
          cov.leviCivitaCorrection x (e.localFrame b i x)) u' := by
            exact congrArg (fun A : TEnd x ↦ A u') hmap
    _ = ((∑ i, (eStar.localFrame (continuousDualBasis b) i x).smulRight
          (cov.leviCivitaCorrection x (e.localFrame b i x))) v) u' := by
            simp [ContinuousLinearMap.smulRight_apply]

/-! The following global wrappers turn the local tensor estimate into a
regularity theorem for the actual Levi-Civita connection. -/

/-- A globally `C²` covariant derivative is locally `C²` on every open set.

The proof localizes each test section with a smooth bump function. The global
connection regularity is then applied to the resulting `C³` section, which is
why one extra derivative is used in this localization step. -/
theorem contMDiffCovariantDerivativeOn_of_contMDiffCovariantDerivative_two
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 2]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E 2 cov.toFun u := by
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  have hux : u ∈ nhds x := hu.mem_nhds hx
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hux).mem_iff.mp hux
  have hψ : ContMDiff I 𝓘(ℝ) 3 ψ := by
    exact ψ.contMDiff.of_le (show (3 : WithTop ℕ∞) ≤ ∞ by decide)
  let τ : Π y : M, TM y := fun y ↦ ψ y • σ y
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (τ y)) := by
    simpa [τ] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E) (V := TM) (u := u)
        (n := (3 : WithTop ℕ∞)) (ψ := ψ) hψ.contMDiffOn hu hψtsupp hσ)
  have hcovτ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) y (cov τ y)) := by
    have hτOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
        (fun y ↦ TotalSpace.mk' E y (τ y)) Set.univ := by
      simpa [contMDiffOn_univ] using hτ
    simpa [contMDiffOn_univ] using
      ((inferInstance : ContMDiffCovariantDerivative cov 2).contMDiff.contMDiff hτOn)
  have hψeq1 : {y : M | ψ y = 1} ∈ nhds x := by
    filter_upwards [ψ.eventuallyEq_one] with y hy
    simpa using hy
  rcases mem_nhds_iff.mp hψeq1 with ⟨w, hwsub, hwopen, hxw⟩
  have hwu : w ⊆ u := by
    intro y hy
    have hy1 : ψ y = 1 := hwsub hy
    have hysupp : y ∈ Function.support ψ := by
      simpa [Function.support] using show ψ y ≠ 0 by rw [hy1]; norm_num
    exact hψsupp hysupp
  have hEq : ∀ y ∈ w, cov σ y = cov τ y := by
    intro y hy
    have hyu : y ∈ u := hwu hy
    have hσy : MDiffAt (fun z ↦ TotalSpace.mk' E z (σ z)) y := by
      exact ((((hσ y hyu).contMDiffAt (hu.mem_nhds hyu)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2 + 1)).mdifferentiableAt one_ne_zero)
    have hτy : MDiffAt (fun z ↦ TotalSpace.mk' E z (τ z)) y := by
      exact ((hτ.contMDiffAt.of_le (by simp : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt
        one_ne_zero)
    exact (cov.isCovariantDerivativeOn (s := w)).congr_of_eqOn hσy hτy
      (hwopen.mem_nhds hy) (fun z hz ↦ by
        have hz1 : ψ z = 1 := hwsub hz
        calc
          σ z = 1 • σ z := by simpa using (one_smul ℝ (σ z)).symm
          _ = ψ z • σ z := by simpa [hz1])
  have hcovσw : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) y (cov σ y)) w := by
    refine ContMDiffOn.congr hcovτ.contMDiffOn ?_
    intro y hy
    exact congrArg (fun A ↦ TotalSpace.mk' (E := TEnd) (E →L[ℝ] E) y A) (hEq y hy)
  refine ⟨w, hwopen, hxw, ?_⟩
  simpa [Set.inter_eq_right.mpr hwu] using hcovσw

theorem contMDiff_leviCivitaCorrection_section_two
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 2] :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E := TCorr) x
        (cov.leviCivitaCorrection x)) := by
  apply contMDiff_of_locally_contMDiffOn
  intro x
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) := trivializationAt E TM x
  let b := Module.finBasis ℝ E
  refine ⟨e.baseSet, e.open_baseSet, FiberBundle.mem_baseSet_trivializationAt E TM x, ?_⟩
  have hcov : ContMDiffCovariantDerivativeOn E 2 cov.toFun e.baseSet :=
    contMDiffCovariantDerivativeOn_of_contMDiffCovariantDerivative_two
      (I := I) (E := E) (cov := cov) e.open_baseSet
  simpa [e, b] using
    (contMDiffOn_leviCivitaCorrection_section_two (I := I) (E := E) (cov := cov) e b
      e.open_baseSet (subset_refl _) hcov)

/-- A `C²` reference covariant derivative determines a `C²` Levi-Civita
connection for the actual `C³` Riemannian-bundle metric. The `C³` tangent
bundle structure is also explicit in this module's assumptions. -/
theorem contMDiffCovariantDerivative_leviCivitaConnection_two
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 2] :
    ContMDiffCovariantDerivative (cov.leviCivitaConnection) 2 := by
  simpa [CovariantDerivative.leviCivitaConnection] using
    (ContMDiffCovariantDerivative.addOneForm (I := I) (E := E) (F := E) (V := TM) (n := 2)
      (cov := cov) (A := cov.leviCivitaCorrection)
      (contMDiff_leviCivitaCorrection_section_two (I := I) (E := E) (cov := cov)))

/-- On a σ-compact smooth manifold, a `C³` Riemannian-bundle metric and a
`C³` tangent bundle structure yield an existing `C²` Levi-Civita connection. -/
theorem exists_contMDiffLeviCivitaConnection_two [SigmaCompactSpace M] :
    ∃ cov : CovariantDerivative I E TM,
      IsLeviCivita cov ∧ ContMDiffCovariantDerivative cov 2 := by
  letI : ContMDiffVectorBundle 2 E TM I :=
    ContMDiffVectorBundle.of_le (n := 3) (by norm_num)
  haveI : ContMDiffVectorBundle (2 + 1) E TM I := by
    exact ContMDiffVectorBundle.of_le (n := 3) (by norm_num)
  obtain ⟨⟨base, hbase⟩⟩ :=
    contMDiff_nonempty_of_level (I := I) (F := E) (V := TM) (n := 2)
      (WithTop.coe_le_coe.mpr le_top)
  letI : ContMDiffCovariantDerivative base 2 := hbase
  exact ⟨leviCivitaConnection base,
    leviCivitaConnection_isLeviCivita base,
    contMDiffCovariantDerivative_leviCivitaConnection_two
      (I := I) (E := E) (cov := base)⟩

end CovariantDerivative
