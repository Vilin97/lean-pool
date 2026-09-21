/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InducedHom
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HomEvaluation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian

/-!
# Regularity of induced hom-bundle connections

This file proves the regularity fact used by the intrinsic Hamilton--Ivey
operator: a C1 connection on each input bundle induces a C1 connection
on the hom bundle.  The proof is local and uses the actual induced-connection
product rule on local frames.

The real-line base case is proved from the manifold derivative-section theorem
and is used to build the regularity of the induced cotangent connection.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ V₂ : M → Type*}
  [TopologicalSpace (TotalSpace F₁ V₁)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [∀ x, FiniteDimensional ℝ (V₁ x)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle 2 F₁ V₁ I] [ContMDiffVectorBundle 2 F₂ V₂ I]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "Hom₁₂" => (fun x : M => V₁ x →L[ℝ] V₂ x)

/-- The ordinary real-line connection has the regularity expected of a
C1 covariant derivative. -/
theorem contMDiffCovariantDerivative_realLine :
    ContMDiffCovariantDerivative
      (trivialCovariantDerivative (I := I) (M := M) ℝ) 1 := by
  refine ⟨?_⟩
  refine { contMDiff := ?_ }
  intro σ hσ x
  have hσx : ContMDiffAt I 𝓘(ℝ) 2 (fun y => σ y) x := by
    have hσxTotal : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) 2
        (fun y => TotalSpace.mk' ℝ y (σ y)) x := by
      simpa only [one_add_one_eq_two] using
        ((hσ x (Set.mem_univ x)).contMDiffAt
          (isOpen_univ.mem_nhds (Set.mem_univ x)))
    simpa [Bundle.Trivial.eq_trivialization, Bundle.Trivial.trivialization_apply] using
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).contMDiffAt_section_iff
        (n := (2 : WithTop ℕ∞))
        (FiberBundle.mem_baseSet_trivializationAt' x)).mp hσxTotal
  simpa [trivialCovariantDerivative] using
    ((hσx.extDerivSection (E := E) (m := (1 : WithTop ℕ∞))
      (n := (2 : WithTop ℕ∞)) (by norm_num)).contMDiffWithinAt :
        ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y
            (trivialCovariantDerivative (I := I) (M := M) ℝ σ y)) Set.univ x)

/-- The ordinary real-line connection is also a `C²` covariant derivative.
The section input is `C³`, and the manifold derivative loses exactly one
order. -/
theorem contMDiffCovariantDerivative_realLine_two :
    ContMDiffCovariantDerivative
      (trivialCovariantDerivative (I := I) (M := M) ℝ) 2 := by
  refine ⟨?_⟩
  refine { contMDiff := ?_ }
  intro σ hσ x
  have hσx : ContMDiffAt I 𝓘(ℝ) 3 (fun y => σ y) x := by
    have hσxTotal : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) 3
        (fun y => TotalSpace.mk' ℝ y (σ y)) x := by
      simpa only [two_add_one_eq_three] using
        ((hσ x (Set.mem_univ x)).contMDiffAt
          (isOpen_univ.mem_nhds (Set.mem_univ x)))
    simpa [Bundle.Trivial.eq_trivialization, Bundle.Trivial.trivialization_apply] using
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).contMDiffAt_section_iff
        (n := (3 : WithTop ℕ∞))
        (FiberBundle.mem_baseSet_trivializationAt' x)).mp hσxTotal
  simpa [trivialCovariantDerivative] using
    ((hσx.extDerivSection (E := E) (m := (2 : WithTop ℕ∞))
      (n := (3 : WithTop ℕ∞)) (by norm_num)).contMDiffWithinAt :
        ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y
            (trivialCovariantDerivative (I := I) (M := M) ℝ σ y)) Set.univ x)
/-- A C1 pair of bundle connections induces a C1 hom-bundle
connection. -/
theorem contMDiffCovariantDerivative_inducedHom
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂)
    [ContMDiffCovariantDerivative cov₁ 1]
    [ContMDiffCovariantDerivative cov₂ 1] :
    ContMDiffCovariantDerivative
      (inducedHomCovariantDerivative cov₁ cov₂) 1 := by
  refine ⟨?_⟩
  refine { contMDiff := ?_ }
  intro φ hφ
  have hφOn : ContMDiffOn I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 2
      (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) y (φ y)) Set.univ := by
    simpa only [one_add_one_eq_two, contMDiffOn_univ] using hφ
  have hresult : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (F₁ →L[ℝ] F₂))) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] (F₁ →L[ℝ] F₂))
        (E := fun z : M => TangentSpace I z →L[ℝ] (V₁ z →L[ℝ] V₂ z)) y
        ((inducedHomCovariantDerivative cov₁ cov₂) φ y)) := by
    intro x
    let eT := trivializationAt E TM x
    let bT := Module.finBasis ℝ E
    let e₁ := trivializationAt F₁ V₁ x
    let b₁ := Module.finBasis ℝ F₁
    have hxT : x ∈ eT.baseSet := by
      exact FiberBundle.mem_baseSet_trivializationAt E TM x
    have hx₁ : x ∈ e₁.baseSet := by
      exact FiberBundle.mem_baseSet_trivializationAt F₁ V₁ x
    refine contMDiffAt_homBundle_of_forall_apply_localFrame
      (IB := I) (E₁ := TM) (E₂ := Hom₁₂) (F₂ := F₁ →L[ℝ] F₂)
      x bT ?_
    intro i
    refine contMDiffAt_homBundle_of_forall_apply_localFrame
      (IB := I) (E₁ := V₁) (E₂ := V₂) x b₁ ?_
    intro j
    let X : ∀ y : M, TM y := eT.localFrame bT i
    let Y : ∀ y : M, V₁ y := e₁.localFrame b₁ j
    have hXOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y => TotalSpace.mk' E y (X y)) eT.baseSet := by
      exact (eT.contMDiffOn_localFrame_baseSet (I := I) (n := (1 : WithTop ℕ∞))
        bT i)
    have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun y => TotalSpace.mk' E y (X y)) x := by
      exact (hXOn x hxT).contMDiffAt (eT.open_baseSet.mem_nhds hxT)
    have hYOn : ContMDiffOn I (I.prod 𝓘(ℝ, F₁)) 2
        (fun y => TotalSpace.mk' F₁ y (Y y)) e₁.baseSet := by
      exact e₁.contMDiffOn_localFrame_baseSet (I := I) (n := (2 : WithTop ℕ∞))
        b₁ j
    have hY : ContMDiffAt I (I.prod 𝓘(ℝ, F₁)) 2
        (fun y => TotalSpace.mk' F₁ y (Y y)) x := by
      exact (hYOn x hx₁).contMDiffAt (e₁.open_baseSet.mem_nhds hx₁)
    have hcov₁On : ContMDiffCovariantDerivativeOn F₁ 1 cov₁.toFun e₁.baseSet :=
      contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
        e₁.open_baseSet
    have hcov₂On : ContMDiffCovariantDerivativeOn F₂ 1 cov₂.toFun e₁.baseSet :=
      contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
        e₁.open_baseSet
    have hcov₁YOn : ContMDiffOn I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₁)) 1
        (fun y => TotalSpace.mk' (E →L[ℝ] F₁)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₁ z) y
          (cov₁ Y y)) e₁.baseSet := by
      exact hcov₁On.contMDiff hYOn
    have hcov₁Y : ContMDiffAt I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₁)) 1
        (fun y => TotalSpace.mk' (E →L[ℝ] F₁)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₁ z) y
          (cov₁ Y y)) x := by
      exact (hcov₁YOn x hx₁).contMDiffAt (e₁.open_baseSet.mem_nhds hx₁)
    have hcov₁YX : ContMDiffAt I (I.prod 𝓘(ℝ, F₁)) 1
        (fun y => TotalSpace.mk' F₁ y ((cov₁ Y y) (X y))) x := by
      exact hcov₁Y.clm_bundle_apply hX
    have hφAt : ContMDiffAt I
        (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 2
        (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂)
          (E := Hom₁₂) y (φ y)) x := by
      exact (hφOn x (Set.mem_univ x)).contMDiffAt
        (isOpen_univ.mem_nhds (Set.mem_univ x))
    have hφAt₁ := hφAt.of_le (by norm_num :
      (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))
    have hφcov₁YX : ContMDiffAt I (I.prod 𝓘(ℝ, F₂)) 1
        (fun y => TotalSpace.mk' F₂ y (φ y ((cov₁ Y y) (X y)))) x := by
      exact hφAt₁.clm_bundle_apply hcov₁YX
    have hφYOn : ContMDiffOn I (I.prod 𝓘(ℝ, F₂)) 2
        (fun y => TotalSpace.mk' F₂ y (φ y (Y y))) e₁.baseSet := by
      intro z hz
      have hφRestrict : ContMDiffWithinAt I
          (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 2
          (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂)
            (E := Hom₁₂) y (φ y)) e₁.baseSet z := by
        exact (hφOn z (Set.mem_univ z)).mono
          (Set.subset_univ e₁.baseSet)
      exact ContMDiffWithinAt.clm_bundle_apply
        (F₁ := F₁) (F₂ := F₂) (E₁ := V₁) (E₂ := V₂)
        (b := fun w : M => w)
        hφRestrict (hYOn z hz)
    have hcov₂φYOn : ContMDiffOn I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) 1
        (fun y => TotalSpace.mk' (E →L[ℝ] F₂)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₂ z) y
          (cov₂ (fun z => φ z (Y z)) y)) e₁.baseSet := by
      exact hcov₂On.contMDiff hφYOn
    have hcov₂φY : ContMDiffAt I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) 1
        (fun y => TotalSpace.mk' (E →L[ℝ] F₂)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₂ z) y
          (cov₂ (fun z => φ z (Y z)) y)) x := by
      exact (hcov₂φYOn x hx₁).contMDiffAt (e₁.open_baseSet.mem_nhds hx₁)
    have hcov₂φYX : ContMDiffAt I (I.prod 𝓘(ℝ, F₂)) 1
        (fun y => TotalSpace.mk' F₂ y
          ((cov₂ (fun z => φ z (Y z)) y) (X y))) x := by
      exact hcov₂φY.clm_bundle_apply hX
    have hsum := hcov₂φYX.sub_section hφcov₁YX
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [e₁.open_baseSet.mem_nhds hx₁] with y hy
    have hφy : MDiffAt
        (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂)
          (E := Hom₁₂) z (φ z)) y := by
      exact (((hφOn y (Set.mem_univ y)).contMDiffAt
        (isOpen_univ.mem_nhds (Set.mem_univ y))).mdifferentiableAt (by norm_num))
    have hYy : MDiffAt
        (fun z => TotalSpace.mk' F₁ z (Y z)) y := by
      exact ((hYOn y hy).contMDiffAt (e₁.open_baseSet.mem_nhds hy)).mdifferentiableAt
        (by norm_num)
    have hpoint := congrArg (fun q : V₂ y => TotalSpace.mk' F₂ y q)
      (inducedHomCovariantDerivative_apply_section_general
        cov₁ cov₂ hφy hYy (X y))
    simpa [X, Y] using hpoint

  simpa only [contMDiffOn_univ] using hresult
/-- A `C²` pair of bundle connections induces a `C²` hom-bundle connection.

The source and target bundles are assumed `C³`: taking a covariant derivative
loses one spatial derivative, so this is exactly the regularity needed to
apply the two input connections to local frames. -/
theorem contMDiffCovariantDerivative_inducedHom_two
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂)
    [ContMDiffVectorBundle 3 F₁ V₁ I]
    [ContMDiffVectorBundle 3 F₂ V₂ I]
    [ContMDiffCovariantDerivative cov₁ 2]
    [ContMDiffCovariantDerivative cov₂ 2] :
    ContMDiffCovariantDerivative
      (inducedHomCovariantDerivative cov₁ cov₂) 2 := by
  refine ⟨?_⟩
  refine { contMDiff := ?_ }
  intro φ hφ
  have hφOn : ContMDiffOn I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 3
      (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) y (φ y)) Set.univ := by
    simpa only [two_add_one_eq_three] using hφ
  have hresult : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (F₁ →L[ℝ] F₂))) 2
      (fun y => TotalSpace.mk' (E →L[ℝ] (F₁ →L[ℝ] F₂))
        (E := fun z : M => TangentSpace I z →L[ℝ] (V₁ z →L[ℝ] V₂ z)) y
        ((inducedHomCovariantDerivative cov₁ cov₂) φ y)) := by
    intro x
    let eT := trivializationAt E TM x
    let bT := Module.finBasis ℝ E
    let e₁ := trivializationAt F₁ V₁ x
    let b₁ := Module.finBasis ℝ F₁
    have hxT : x ∈ eT.baseSet := by
      exact FiberBundle.mem_baseSet_trivializationAt E TM x
    have hx₁ : x ∈ e₁.baseSet := by
      exact FiberBundle.mem_baseSet_trivializationAt F₁ V₁ x
    refine contMDiffAt_homBundle_of_forall_apply_localFrame
      (IB := I) (E₁ := TM) (E₂ := Hom₁₂) (F₂ := F₁ →L[ℝ] F₂)
      x bT ?_
    intro i
    refine contMDiffAt_homBundle_of_forall_apply_localFrame
      (IB := I) (E₁ := V₁) (E₂ := V₂) x b₁ ?_
    intro j
    let X : ∀ y : M, TM y := eT.localFrame bT i
    let Y : ∀ y : M, V₁ y := e₁.localFrame b₁ j
    have hXOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun y => TotalSpace.mk' E y (X y)) eT.baseSet := by
      exact (eT.contMDiffOn_localFrame_baseSet (I := I) (n := (2 : WithTop ℕ∞))
        bT i)
    have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2
        (fun y => TotalSpace.mk' E y (X y)) x := by
      exact (hXOn x hxT).contMDiffAt (eT.open_baseSet.mem_nhds hxT)
    have hYOn : ContMDiffOn I (I.prod 𝓘(ℝ, F₁)) 3
        (fun y => TotalSpace.mk' F₁ y (Y y)) e₁.baseSet := by
      exact e₁.contMDiffOn_localFrame_baseSet (I := I) (n := (3 : WithTop ℕ∞))
        b₁ j
    have hY : ContMDiffAt I (I.prod 𝓘(ℝ, F₁)) 3
        (fun y => TotalSpace.mk' F₁ y (Y y)) x := by
      exact (hYOn x hx₁).contMDiffAt (e₁.open_baseSet.mem_nhds hx₁)
    have hcov₁On : ContMDiffCovariantDerivativeOn F₁ 2 cov₁.toFun e₁.baseSet :=
      contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two
        e₁.open_baseSet
    have hcov₂On : ContMDiffCovariantDerivativeOn F₂ 2 cov₂.toFun e₁.baseSet :=
      contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two
        e₁.open_baseSet
    have hcov₁YOn : ContMDiffOn I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₁)) 2
        (fun y => TotalSpace.mk' (E →L[ℝ] F₁)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₁ z) y
          (cov₁ Y y)) e₁.baseSet := by
      exact hcov₁On.contMDiff hYOn
    have hcov₁Y : ContMDiffAt I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₁)) 2
        (fun y => TotalSpace.mk' (E →L[ℝ] F₁)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₁ z) y
          (cov₁ Y y)) x := by
      exact (hcov₁YOn x hx₁).contMDiffAt (e₁.open_baseSet.mem_nhds hx₁)
    have hcov₁YX : ContMDiffAt I (I.prod 𝓘(ℝ, F₁)) 2
        (fun y => TotalSpace.mk' F₁ y ((cov₁ Y y) (X y))) x := by
      exact hcov₁Y.clm_bundle_apply hX
    have hφAt : ContMDiffAt I
        (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 3
        (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂)
          (E := Hom₁₂) y (φ y)) x := by
      exact (hφOn x (Set.mem_univ x)).contMDiffAt
        (isOpen_univ.mem_nhds (Set.mem_univ x))
    have hφAt₂ := hφAt.of_le (by norm_num :
      (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))
    have hφcov₁YX : ContMDiffAt I (I.prod 𝓘(ℝ, F₂)) 2
        (fun y => TotalSpace.mk' F₂ y (φ y ((cov₁ Y y) (X y)))) x := by
      exact hφAt₂.clm_bundle_apply hcov₁YX
    have hφYOn : ContMDiffOn I (I.prod 𝓘(ℝ, F₂)) 3
        (fun y => TotalSpace.mk' F₂ y (φ y (Y y))) e₁.baseSet := by
      intro z hz
      have hφRestrict : ContMDiffWithinAt I
          (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 3
          (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂)
            (E := Hom₁₂) y (φ y)) e₁.baseSet z := by
        exact (hφOn z (Set.mem_univ z)).mono
          (Set.subset_univ e₁.baseSet)
      exact ContMDiffWithinAt.clm_bundle_apply
        (F₁ := F₁) (F₂ := F₂) (E₁ := V₁) (E₂ := V₂)
        (b := fun w : M => w)
        hφRestrict (hYOn z hz)
    have hcov₂φYOn : ContMDiffOn I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) 2
        (fun y => TotalSpace.mk' (E →L[ℝ] F₂)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₂ z) y
          (cov₂ (fun z => φ z (Y z)) y)) e₁.baseSet := by
      exact hcov₂On.contMDiff hφYOn
    have hcov₂φY : ContMDiffAt I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) 2
        (fun y => TotalSpace.mk' (E →L[ℝ] F₂)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₂ z) y
          (cov₂ (fun z => φ z (Y z)) y)) x := by
      exact (hcov₂φYOn x hx₁).contMDiffAt (e₁.open_baseSet.mem_nhds hx₁)
    have hcov₂φYX : ContMDiffAt I (I.prod 𝓘(ℝ, F₂)) 2
        (fun y => TotalSpace.mk' F₂ y
          ((cov₂ (fun z => φ z (Y z)) y) (X y))) x := by
      exact hcov₂φY.clm_bundle_apply hX
    have hsum := hcov₂φYX.sub_section hφcov₁YX
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [e₁.open_baseSet.mem_nhds hx₁] with y hy
    have hφy : MDiffAt
        (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂)
          (E := Hom₁₂) z (φ z)) y := by
      exact (((hφOn y (Set.mem_univ y)).contMDiffAt
        (isOpen_univ.mem_nhds (Set.mem_univ y))).mdifferentiableAt (by norm_num))
    have hYy : MDiffAt
        (fun z => TotalSpace.mk' F₁ z (Y z)) y := by
      exact ((hYOn y hy).contMDiffAt (e₁.open_baseSet.mem_nhds hy)).mdifferentiableAt
        (by norm_num)
    have hpoint := congrArg (fun q : V₂ y => TotalSpace.mk' F₂ y q)
      (inducedHomCovariantDerivative_apply_section_general
        cov₁ cov₂ hφy hYy (X y))
    simpa [X, Y] using hpoint

  simpa only [contMDiffOn_univ] using hresult

section TensorRegularity

variable [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "T₀" => (Bundle.Trivial M ℝ)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

@[reducible] local instance tensorRegularityOneModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance tensorRegularityOneModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance tensorRegularityOneFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₁ x) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance tensorRegularityOneFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₁ x) := ContinuousLinearMap.toNormedSpace

local instance tensorRegularityOneTotalSpaceTopology :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ T₀
local instance tensorRegularityOneFiberBundle : FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ) E TM ℝ T₀
local instance tensorRegularityOneVectorBundle : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ) E TM ℝ T₀

/-! Naming the depth-two operator-space instances prevents typeclass search
from repeatedly unfolding the covector model while constructing the next
induced Hom bundle.  These are the canonical structures used in
`covariantTwoTensorCovariantDerivative`. -/
@[reducible] local instance tensorRegularityTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[reducible] local instance tensorRegularityTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[reducible] local instance tensorRegularityTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
@[reducible] local instance tensorRegularityTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance

local instance tensorRegularityTwoTotalSpaceTopology :
    TopologicalSpace (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance tensorRegularityTwoFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance tensorRegularityTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁

/-- A `C²` tangent-bundle connection induces a `C²` cotangent-bundle
connection.  The tangent bundle is required to be `C³`, as required by the
one-derivative loss in the connection. -/
theorem contMDiffCovariantDerivative_covector_two
    (cov : CovariantDerivative I E TM)
    [hContTangent : ContMDiffVectorBundle 3 E TM I]
    [hcov : ContMDiffCovariantDerivative cov 2] :
    ContMDiffCovariantDerivative
      (covectorCovariantDerivative (I := I) (M := M) cov) 2 := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) :=
    PoincareCurvature.instNormedAddCommGroupTangentSpace I
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) :=
    PoincareCurvature.instNormedSpaceTangentSpace I
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let hContTangentTwo : ContMDiffVectorBundle 2 E TM I :=
    ContMDiffVectorBundle.of_le (m := 2) (n := 3) (by norm_num)
  let cov₀ := realLineCovariantDerivative (I := I) (M := M)
  let hcov₀ : ContMDiffCovariantDerivative cov₀ 2 :=
    contMDiffCovariantDerivative_realLine_two (I := I) (M := M)
  let hContScalarTwo : ContMDiffVectorBundle 2 ℝ T₀ I :=
    Bundle.Trivial.contMDiffVectorBundle ℝ
  let hContScalarThree : ContMDiffVectorBundle 3 ℝ T₀ I :=
    Bundle.Trivial.contMDiffVectorBundle ℝ
  dsimp [covectorCovariantDerivative, cov₀, realLineCovariantDerivative, Bundle.Trivial]
  exact @contMDiffCovariantDerivative_inducedHom_two
    E _ _ H _ I M _ _ _ _ _ _
    E ℝ _ _ _ _ _ _
    TM T₀ _ _ nTM sTM fTM _ _
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    (Bundle.Trivial.fiberBundle M ℝ) (Bundle.Trivial.vectorBundle ℝ M ℝ)
    hContTangentTwo hContScalarTwo
    cov cov₀
    hContTangent hContScalarThree
    hcov hcov₀

/-- A `C²` tangent-bundle connection induces a `C²` connection on covariant
two-tensors.  Together with the existing `C¹` induced-Hom theorem, this
supplies the two- and three-tensor regularity levels used by the local tensor
heat atlas once the corresponding base-connection levels are available. -/
theorem contMDiffCovariantDerivative_covariantTwoTensor_two
    (cov : CovariantDerivative I E TM)
    [hContTangent : ContMDiffVectorBundle 3 E TM I]
    [hcov : ContMDiffCovariantDerivative cov 2] :
    ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative (E := E) (I := I) (M := M) cov) 2 := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) :=
    PoincareCurvature.instNormedAddCommGroupTangentSpace I
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) :=
    PoincareCurvature.instNormedSpaceTangentSpace I
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let hContTangentTwo : ContMDiffVectorBundle 2 E TM I :=
    ContMDiffVectorBundle.of_le (m := 2) (n := 3) (by norm_num)
  let cov₀ := realLineCovariantDerivative (I := I) (M := M)
  let hcov₀ : ContMDiffCovariantDerivative cov₀ 2 :=
    contMDiffCovariantDerivative_realLine_two (I := I) (M := M)
  let hContScalarTwo : ContMDiffVectorBundle 2 ℝ T₀ I :=
    Bundle.Trivial.contMDiffVectorBundle ℝ
  let hContScalarThree : ContMDiffVectorBundle 3 ℝ T₀ I :=
    Bundle.Trivial.contMDiffVectorBundle ℝ
  let hContOneThree : ContMDiffVectorBundle 3 (E →L[ℝ] ℝ) T₁ I :=
    ContMDiffVectorBundle.continuousLinearMap
  let hContOneTwo : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
    ContMDiffVectorBundle.of_le (m := 2) (n := 3) (by norm_num)
  let cov₁ := covectorCovariantDerivative (I := I) (M := M) cov
  let hcov₁ : ContMDiffCovariantDerivative cov₁ 2 := by
    dsimp [cov₁, covectorCovariantDerivative, cov₀,
      realLineCovariantDerivative, Bundle.Trivial]
    exact @contMDiffCovariantDerivative_inducedHom_two
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM T₀ _ _ nTM sTM fTM _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      (Bundle.Trivial.fiberBundle M ℝ) (Bundle.Trivial.vectorBundle ℝ M ℝ)
      hContTangentTwo hContScalarTwo
      cov cov₀
      hContTangent hContScalarThree
      hcov hcov₀
  dsimp [covariantTwoTensorCovariantDerivative, cov₁,
    covectorCovariantDerivative, cov₀, realLineCovariantDerivative, Bundle.Trivial]
  exact @contMDiffCovariantDerivative_inducedHom_two
    E _ _ H _ I M _ _ _ _ _ _
    E (E →L[ℝ] ℝ) _ _ _ _ _ _
    TM T₁ _ _ nTM sTM fTM
    tensorRegularityOneFiberNormedAddCommGroup tensorRegularityOneFiberNormedSpace
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    tensorRegularityOneFiberBundle tensorRegularityOneVectorBundle
    hContTangentTwo hContOneTwo
    cov cov₁
    hContTangent hContOneThree
    hcov hcov₁

/-- A `C¹` tangent-bundle connection induces a `C¹` cotangent-bundle
connection.  This is the tensor-specialized form of the induced-Hom theorem,
kept named so the tensor-heat regularity chain does not need to reconstruct
the scalar target connection. -/
theorem contMDiffCovariantDerivative_covector_one
    (cov : CovariantDerivative I E TM)
    [hContTangent : ContMDiffVectorBundle 2 E TM I]
    [hcov : ContMDiffCovariantDerivative cov 1] :
    ContMDiffCovariantDerivative
      (covectorCovariantDerivative (I := I) (M := M) cov) 1 := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) :=
    PoincareCurvature.instNormedAddCommGroupTangentSpace I
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) :=
    PoincareCurvature.instNormedSpaceTangentSpace I
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let cov₀ := realLineCovariantDerivative (I := I) (M := M)
  let hcov₀ : ContMDiffCovariantDerivative cov₀ 1 :=
    contMDiffCovariantDerivative_realLine (I := I) (M := M)
  let hContScalar : ContMDiffVectorBundle 2 ℝ T₀ I :=
    Bundle.Trivial.contMDiffVectorBundle ℝ
  dsimp [covectorCovariantDerivative, cov₀, realLineCovariantDerivative, Bundle.Trivial]
  exact @contMDiffCovariantDerivative_inducedHom
    E _ _ H _ I M _ _ _ _ _ _
    E ℝ _ _ _ _ _ _
    TM T₀ _ _ nTM sTM fTM _ _
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    (Bundle.Trivial.fiberBundle M ℝ) (Bundle.Trivial.vectorBundle ℝ M ℝ)
    hContTangent hContScalar
    cov cov₀ hcov hcov₀

/-- A `C¹` tangent-bundle connection induces a `C¹` connection on covariant
two-tensors. -/
theorem contMDiffCovariantDerivative_covariantTwoTensor_one
    (cov : CovariantDerivative I E TM)
    [hContTangent : ContMDiffVectorBundle 2 E TM I]
    [hcov : ContMDiffCovariantDerivative cov 1] :
    ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative (E := E) (I := I) (M := M) cov) 1 := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) :=
    PoincareCurvature.instNormedAddCommGroupTangentSpace I
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) :=
    PoincareCurvature.instNormedSpaceTangentSpace I
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let cov₀ := realLineCovariantDerivative (I := I) (M := M)
  let hcov₀ : ContMDiffCovariantDerivative cov₀ 1 :=
    contMDiffCovariantDerivative_realLine (I := I) (M := M)
  let hContScalar : ContMDiffVectorBundle 2 ℝ T₀ I :=
    Bundle.Trivial.contMDiffVectorBundle ℝ
  let hContOne : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
    ContMDiffVectorBundle.continuousLinearMap
  let cov₁ := covectorCovariantDerivative (I := I) (M := M) cov
  let hcov₁ : ContMDiffCovariantDerivative cov₁ 1 := by
    dsimp [cov₁, covectorCovariantDerivative, cov₀,
      realLineCovariantDerivative, Bundle.Trivial]
    exact @contMDiffCovariantDerivative_inducedHom
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM T₀ _ _ nTM sTM fTM _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      (Bundle.Trivial.fiberBundle M ℝ) (Bundle.Trivial.vectorBundle ℝ M ℝ)
      hContTangent hContScalar
      cov cov₀ hcov hcov₀
  dsimp [covariantTwoTensorCovariantDerivative, cov₁,
    covectorCovariantDerivative, cov₀, realLineCovariantDerivative, Bundle.Trivial]
  exact @contMDiffCovariantDerivative_inducedHom
    E _ _ H _ I M _ _ _ _ _ _
    E (E →L[ℝ] ℝ) _ _ _ _ _ _
    TM T₁ _ _ nTM sTM fTM
    tensorRegularityOneFiberNormedAddCommGroup tensorRegularityOneFiberNormedSpace
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    tensorRegularityOneFiberBundle tensorRegularityOneVectorBundle
    hContTangent hContOne
    cov cov₁ hcov hcov₁

/-- A `C¹` tangent-bundle connection and a `C¹` induced two-tensor connection
induce a `C¹` connection on covariant three-tensors.  Both `C¹` premises are
explicit because the abstract `ContMDiffCovariantDerivative` API does not
coerce a `C²` instance to a `C¹` instance. -/
theorem contMDiffCovariantDerivative_covariantThreeTensor_one
    (cov : CovariantDerivative I E TM)
    [hContTangent : ContMDiffVectorBundle 2 E TM I]
    [hcov : ContMDiffCovariantDerivative cov 1]
    [hcovTwo : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative (E := E) (I := I) (M := M) cov) 1] :
    ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative (E := E) (I := I) (M := M) cov) 1 := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) :=
    PoincareCurvature.instNormedAddCommGroupTangentSpace I
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) :=
    PoincareCurvature.instNormedSpaceTangentSpace I
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let hContOne : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
    ContMDiffVectorBundle.continuousLinearMap
  let hContTwo : ContMDiffVectorBundle 2 (E →L[ℝ] E →L[ℝ] ℝ) T₂ I :=
    ContMDiffVectorBundle.continuousLinearMap
  dsimp [covariantThreeTensorCovariantDerivative]
  exact @contMDiffCovariantDerivative_inducedHom
    E _ _ H _ I M _ _ _ _ _ _
    E (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _ _ _
    TM T₂ _ _ nTM sTM fTM
    tensorRegularityTwoFiberNormedAddCommGroup tensorRegularityTwoFiberNormedSpace
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    tensorRegularityTwoFiberBundle tensorRegularityTwoVectorBundle
    hContTangent hContTwo
    cov (covariantTwoTensorCovariantDerivative (E := E) (I := I) (M := M) cov)
    hcov hcovTwo

end TensorRegularity

end CovariantDerivative
