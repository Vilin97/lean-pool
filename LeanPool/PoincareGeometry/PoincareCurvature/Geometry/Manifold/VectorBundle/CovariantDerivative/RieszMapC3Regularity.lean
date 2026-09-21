/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# C³ regularity of the metric Riesz map

A C⁴ Riemannian metric on a C⁴ tangent bundle makes the local-frame Gram
matrix, its inverse, and the fiberwise Riesz map C³.  This is the extra
regularity bridge needed when the Levi-Civita correction is built from a C³
connection.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 4 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 4 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TStar" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "⟪" x ", " y "⟫" => inner ℝ x y

local instance (priority := 100) smoothRiemannianMetricThree : IsContMDiffRiemannianBundle I 3 E TM :=
  IsContMDiffRiemannianBundle.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4)

local instance (priority := 100) smoothRiemannianMetricTwo : IsContMDiffRiemannianBundle I 2 E TM :=
  IsContMDiffRiemannianBundle.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 4)

local instance (priority := 100) smoothRiemannianMetricOne : IsContMDiffRiemannianBundle I 1 E TM :=
  IsContMDiffRiemannianBundle.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 4)

local instance (priority := 100) smoothTangentBundleThree : ContMDiffVectorBundle 3 E TM I :=
  ContMDiffVectorBundle.of_le (F := E) (E := TM) (IB := I)
    (m := 3) (n := 4) (by norm_num)

local instance (priority := 100) smoothTangentBundleTwo : ContMDiffVectorBundle 2 E TM I :=
  ContMDiffVectorBundle.of_le (F := E) (E := TM) (IB := I)
    (m := 2) (n := 4) (by norm_num)

namespace CovariantDerivative

private theorem contDiff_matrix_det_three {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContDiff ℝ 3 (fun A : ι → ι → ℝ => Matrix.det (show Matrix ι ι ℝ from A)) := by
  classical
  let f : (ι → ι → ℝ) → ℝ :=
    fun A => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i
  have hf : ContDiff ℝ 3 f := by
    rw [contDiff_iff_contDiffAt]
    intro A
    refine ContDiffAt.sum ?_
    intro σ hσ
    refine (contDiffAt_const : ContDiffAt ℝ 3
      (fun _ : ι → ι → ℝ => ((Equiv.Perm.sign σ : ℤ) : ℝ)) A).mul ?_
    refine contDiffAt_prod ?_
    intro i hi
    simpa using
      (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) (n := (3 : WithTop ℕ∞))
        (i := σ i) (j := i)).contDiffAt
  have hEq : f = fun A : ι → ι → ℝ => Matrix.det (show Matrix ι ι ℝ from A) := by
    funext A
    symm
    simpa using (Matrix.det_apply' (show Matrix ι ι ℝ from A))
  simpa [hEq] using hf

private theorem contDiff_matrix_updateRow_three {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i j : ι) :
    ContDiff ℝ 3
      (fun A : ι → ι → ℝ =>
        (show ι → ι → ℝ from Matrix.updateRow (show Matrix ι ι ℝ from A) j
          (Pi.single i (1 : ℝ)))) := by
  classical
  rw [contDiff_pi]
  intro k
  change ContDiff ℝ 3
    (fun A : ι → ι → ℝ => Function.update A j (Pi.single i (1 : ℝ)) k)
  by_cases hk : k = j
  · subst hk
    simpa [Function.update] using
      (contDiff_const : ContDiff ℝ 3
        (fun _ : ι → ι → ℝ => (Pi.single i (1 : ℝ) : ι → ℝ)))
  · simpa [Function.update, hk] using
      (contDiff_apply (𝕜 := ℝ) (E := ι → ℝ) (n := (3 : WithTop ℕ∞)) (i := k))

private theorem contDiff_matrix_adjugate_three {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    ContDiff ℝ 3
      (fun A : ι → ι → ℝ =>
        (show ι → ι → ℝ from Matrix.adjugate (show Matrix ι ι ℝ from A))) := by
  classical
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  change ContDiff ℝ 3
    (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j)
  have hEq :
      (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j) =
        (fun A : ι → ι → ℝ =>
          ((Matrix.of A).updateRow j (Pi.single i (1 : ℝ))).det) := by
    funext A
    exact Matrix.adjugate_apply (Matrix.of A) i j
  rw [hEq]
  convert (contDiff_matrix_det_three (ι := ι)).comp
    (contDiff_matrix_updateRow_three (ι := ι) i j) using 1; rfl

/-- The local-frame Gram matrix is C³ when the metric and tangent bundle are C⁴. -/
theorem contMDiffOn_localFrameGramMatrix_three
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) {u : Set M} (hu : IsOpen u)
    (hu' : u ⊆ e.baseSet) :
    ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) 3
      (localFrameGramMatrix (I := I) e b) u := by
  rw [contMDiffOn_pi_space]
  intro i
  rw [contMDiffOn_pi_space]
  intro j
  have hi : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 4
      (fun x => TotalSpace.mk' E x (e.localFrame b i x)) u :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
      (n := (4 : WithTop ℕ∞)) (b := b) i).mono hu'
  have hj : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 4
      (fun x => TotalSpace.mk' E x (e.localFrame b j x)) u :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
      (n := (4 : WithTop ℕ∞)) (b := b) j).mono hu'
  have hinner : ContMDiffOn I 𝓘(ℝ) 4
      (fun x => ⟪e.localFrame b i x, e.localFrame b j x⟫) u :=
    ContMDiffOn.inner_bundle (IM := I) (IB := I) (F := E) (E := TM) hi hj
  exact hinner.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4)

/-- The determinant of the local-frame Gram matrix is C³ for C⁴ metric data. -/
theorem contMDiffOn_localFrameGramMatrix_det_three
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {u : Set M} (hu : IsOpen u)
    (hu' : u ⊆ e.baseSet) :
    ContMDiffOn I 𝓘(ℝ) 3
      (fun x => Matrix.det (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)) u := by
  intro x hx
  have hG := contMDiffOn_localFrameGramMatrix_three (I := I) (E := E) e b hu hu' x hx
  have h := (contDiff_matrix_det_three (ι := ι)).comp_contMDiffWithinAt hG
  exact ContMDiffWithinAt.congr h (by intro y hy; rfl) (by rfl)

/-- The adjugate of the local-frame Gram matrix is C³ for C⁴ metric data. -/
theorem contMDiffOn_localFrameGramMatrix_adjugate_three
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {u : Set M} (hu : IsOpen u)
    (hu' : u ⊆ e.baseSet) :
    ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) 3
      (fun x =>
        (show ι → ι → ℝ from
          Matrix.adjugate (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x))) u := by
  intro x hx
  have hG := contMDiffOn_localFrameGramMatrix_three (I := I) (E := E) e b hu hu' x hx
  have h := (contDiff_matrix_adjugate_three (ι := ι)).comp_contMDiffWithinAt hG
  exact ContMDiffWithinAt.congr h (by intro y hy; rfl) (by rfl)

/-- The inverse local-frame Gram matrix is C³ under a C⁴ Riemannian metric. -/
theorem contMDiffOn_localFrameGramMatrix_inv_three
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {u : Set M} (hu : IsOpen u)
    (hu' : u ⊆ e.baseSet) :
    ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) 3
      (fun x =>
        (show ι → ι → ℝ from
          (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ :
            Matrix ι ι ℝ)))) u := by
  refine ContMDiffOn.congr
    (((contMDiffOn_localFrameGramMatrix_det_three (I := I) (E := E) e b hu hu').inv₀
      (fun x hx => localFrameGramMatrix_det_ne_zero (I := I) (E := E) e b (hu' hx))).smul
      (contMDiffOn_localFrameGramMatrix_adjugate_three (I := I) (E := E) e b hu hu')) ?_
  intro x hx
  change (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ =
    ((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x).det)⁻¹ •
      Matrix.adjugate (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)
  rw [Matrix.inv_def, Ring.inverse_eq_inv]

/-- The fiberwise Riesz map sends a C³ cotangent section to a C³ tangent
section when the Riemannian metric and tangent bundle are C⁴. -/
theorem contMDiffOn_rieszMap_section_three
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {u : Set M} (hu : IsOpen u)
    (hu' : u ⊆ e.baseSet) {omega : Π x : M, TStar x}
    (hω : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 3
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (omega x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun x => TotalSpace.mk' E x (rieszMap (I := I) x (omega x))) u := by
  classical

  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M => ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈
      ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  let eStar : Trivialization (E →L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) TStar → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  have hωcoeff : ∀ j, ContMDiffOn I 𝓘(ℝ) 3
      (fun x => omega x (e.localFrame b j x)) u := by
    intro j
    have hj : ContMDiffOn I 𝓘(ℝ) 3
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
  have hInvEntry : ∀ i j, ContMDiffOn I 𝓘(ℝ) 3
      (fun x =>
        (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ :
          Matrix ι ι ℝ) i j)) u := by
    intro i j
    have hInv := contMDiffOn_localFrameGramMatrix_inv_three
      (I := I) (E := E) e b hu hu'
    rw [contMDiffOn_pi_space] at hInv
    have hi := hInv i
    rw [contMDiffOn_pi_space] at hi
    exact hi j
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) 3
      ((LinearMap.piApply (e.localFrameCoeff I b i))
        (fun x => rieszMap (I := I) x (omega x))) u := by
    intro i
    have hsum : ∀ s : Finset ι, ContMDiffOn I 𝓘(ℝ) 3
        (fun x => s.sum fun j =>
          (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ :
            Matrix ι ι ℝ) i j) * omega x (e.localFrame b j x)) u := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simpa using (contMDiffOn_const :
          ContMDiffOn I 𝓘(ℝ) 3 (fun _ : M => (0 : ℝ)) u)
      · intro j s hj hs
        have hfirst : ContMDiffOn I 𝓘(ℝ) 3
            (fun x =>
              (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ :
                Matrix ι ι ℝ) i j) * omega x (e.localFrame b j x)) u :=
          (hInvEntry i j).mul (hωcoeff j)
        have hadd : ContMDiffOn I 𝓘(ℝ) 3
            (fun x =>
              (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ :
                Matrix ι ι ℝ) i j) * omega x (e.localFrame b j x) +
                s.sum (fun j' =>
                  (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ :
                    Matrix ι ι ℝ) i j') * omega x (e.localFrame b j' x))) u :=
          hfirst.add hs
        refine ContMDiffOn.congr hadd ?_
        intro x hx
        simp [Finset.sum_insert, hj]
    refine ContMDiffOn.congr (hsum Finset.univ) ?_
    intro x hx
    simpa using
      (localFrameCoeff_rieszMap (I := I) (E := E) (e := e) (b := b)
        (omega := omega) (hx := hu' hx) (i := i))
  exact (contMDiffOn_iff_localFrameCoeff
    (I := I) (e := e) (b := b)
    (s := fun x => rieszMap (I := I) x (omega x)) (t := u)
    (k := (3 : WithTop ℕ∞)) hu hu').2 hcoeff

end CovariantDerivative

end
