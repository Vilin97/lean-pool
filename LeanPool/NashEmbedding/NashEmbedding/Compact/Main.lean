/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/
module


/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
public import Mathlib.Tactic
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import LeanPool.NashEmbedding.NashEmbedding.Torus.Main
public import LeanPool.NashEmbedding.NashEmbedding.Compact.WhitneyExtension
public import LeanPool.NashEmbedding.NashEmbedding.Compact.AmbientMetric
public import LeanPool.NashEmbedding.NashEmbedding.Compact.Periodization

/-!
# Nash embedding for compact manifolds

Nash's isometric embedding theorem for closed manifolds, proved by reduction to
`nashTorus` via Whitney embedding (Wassermann §13).

Design (recorded 2026-08-30):
 - The Riemannian metric is Mathlib's `ContMDiffRiemannianMetric` on the
   tangent bundle — the only dependence on Mathlib's Riemannian API, and
   only as an *input* type.
 - The conclusion uses `mfderiv` and the Euclidean inner product only:
   no `IsImmersion` / `IsSmoothEmbedding` (their `comp`/`contMDiff` API is
   `proof_wanted` at the pinned Mathlib version).
 - The periodic-ℝᴺ torus of `nashTorus` never appears in the statement.

The labels S2–S5 used in this file name the steps of the reduction — Whitney extension
(S2), ambient metric (S3), periodization (S4), assembly (S5) — for cross-reference among
its proofs.  The assembly `nashCompact` was directly authored by Claude from four lemmas
S5-1 – S5-4 below,
which (with the leaves in `WhitneyExtension`, `AmbientMetric`, `Periodization`) were
proved by Aristotle (projects 564db993, 6f927eaf, bf61e09c, 7856eea9; 2026-08-30).

## Main statements

* `nashCompact` — Nash's theorem for closed manifolds;
* `nashCompact_isClosedEmbedding`, `PullsBackEuclidean.injective_mfderiv` — the map is a
  closed embedding and an immersion.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Bundle Set Function Matrix

noncomputable
section

namespace NashEmbedding

/-- Forget the base point of a tangent vector to Euclidean space: the tangent
  space `TangentSpace 𝓘(ℝ, ℝᵠ) y` is definitionally `ℝᵠ`, but does not carry the
  inner-product instance, so we transport explicitly. -/
def toEuclid {q : ℕ} {y : EuclideanSpace ℝ (Fin q)}
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) y) : EuclideanSpace ℝ (Fin q) :=
  v

/-! ### Elementary auxiliary facts -/

/-- The open cube `(-π,π)ᴺ` is open: a finite intersection of preimages of open sets
  under the (continuous) coordinate maps. -/
lemma isOpen_openCube (N : ℕ) : IsOpen (openCube N) := by
  have h : openCube N = ⋂ j : Fin N, {x : Fin N → ℝ | |x j| < Real.pi} := by
    ext x; simp [openCube, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun j => isOpen_lt ((continuous_apply j).abs) continuous_const

/-- The quadratic form of the identity matrix is positive on nonzero vectors. -/
lemma quadForm_one_pos {N : ℕ} (v : Fin N → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ (1 : Matrix (Fin N) (Fin N) ℝ).mulVec v := by
  rw [Matrix.one_mulVec]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have h2 : 0 < v i * v i := mul_self_pos.2 (by simpa using hi)
  simp only [dotProduct]
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ i, h2⟩

/-- The quadratic form is homogeneous of degree one in the matrix. -/
lemma quadForm_smul_matrix {N : ℕ} (c : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) :
    v ⬝ᵥ (c • A).mulVec v = c * (v ⬝ᵥ A.mulVec v) := by
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]

section Statement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `w : M → ℝᵠ` pulls the Euclidean metric back to `g`:
  `g_x(v, v') = ⟨dw_x v, dw_x v'⟩` for all `x` and tangent vectors `v, v'`. -/
def PullsBackEuclidean (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {q : ℕ} (w : M → EuclideanSpace ℝ (Fin q)) : Prop :=
  ∀ (x : M) (v v' : TangentSpace I x),
    g.inner x v v' =
      inner ℝ (toEuclid (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w x v))
              (toEuclid (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w x v'))

/-! ### Assembly lemmas (S5)

  The reduction to `nashTorus`, in four steps.  `equivE N : EuclideanSpace ℝ (Fin N) ≃L[ℝ] (Fin
      N → ℝ)`
  is `EuclideanSpace.equiv`. -/

/-- **S5-1 (Whitney immersion into the cube, with extension).**  A compact boundaryless
  manifold admits a smooth injective immersion `u` into some `ℝᴺ` (`N ≥ 1`) whose image lies
  in the open cube `(-π,π)ᴺ`, such that every smooth matrix-valued function on `M` extends
  smoothly along `u`.  (Whitney via `SmoothBumpCovering.exists_immersion_euclidean`'s
  construction `eEF ∘ embeddingPiTangent`, then `WhitneyExtension`, then scaling by a small
  `ε > 0`.) -/
/- `ChartedSpace` on matrices over themselves, with the topology spelled two ways:
the model side carries the norm-derived chain (as `𝓘(ℝ, Matrix …)` elaborates it),
the manifold side the direct Pi-derived instance. The two are definitionally equal,
but v4.31's `Matrix` is a `def`, so instance search needs this exact mixed shape;
`chartedSpaceSelf` alone cannot match it. This bridge is not a workaround for
our instance choices: in isolated tests the same mixed goal also defeated
Mathlib's scoped `Matrix.Norms.Elementwise` instances (with or without
`fast_instance%`), so the `ContMDiff _ 𝓘(ℝ, Matrix _ _ ℝ) _ _` statements in
this file need a user-supplied instance of this shape at the v4.31 pin. -/
instance instChartedSpaceMatrixSelf {N : ℕ} :
    @ChartedSpace (Matrix (Fin N) (Fin N) ℝ)
      (@UniformSpace.toTopologicalSpace (Matrix (Fin N) (Fin N) ℝ)
        (@PseudoMetricSpace.toUniformSpace (Matrix (Fin N) (Fin N) ℝ)
          (@SeminormedAddCommGroup.toPseudoMetricSpace (Matrix (Fin N) (Fin N) ℝ)
            (@NormedAddCommGroup.toSeminormedAddCommGroup (Matrix (Fin N) (Fin N) ℝ)
              (NashEmbedding.matrixNormedAddCommGroup N)))))
      (Matrix (Fin N) (Fin N) ℝ)
      (@instTopologicalSpaceMatrix (Fin N) (Fin N) ℝ
        (@UniformSpace.toTopologicalSpace ℝ (@PseudoMetricSpace.toUniformSpace ℝ
            Real.pseudoMetricSpace))) :=
  @chartedSpaceSelf (Matrix (Fin N) (Fin N) ℝ) _

theorem exists_immersion_in_cube [T2Space M] [CompactSpace M] [I.Boundaryless] [Nonempty M] :
    ∃ (N : ℕ) (u : M → EuclideanSpace ℝ (Fin N)), 0 < N ∧
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ u ∧ Injective u ∧
      (∀ x, Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) u x)) ∧
      (∀ x, (EuclideanSpace.equiv (Fin N) ℝ (u x)) ∈ openCube N) ∧
      (∀ h : M → Matrix (Fin N) (Fin N) ℝ, ContMDiff I 𝓘(ℝ, Matrix (Fin N) (Fin N) ℝ) ∞ h →
        ∃ F : EuclideanSpace ℝ (Fin N) → Matrix (Fin N) (Fin N) ℝ,
          ContDiff ℝ ∞ F ∧ ∀ x, F (u x) = h x) := by
  classical
  obtain ⟨ι, f, -⟩ :=
    SmoothBumpCovering.exists_isSubordinate I isClosed_univ (fun (x : M) _ => Filter.univ_mem)
  have := f.fintype
  have : Nonempty ι := ⟨f.ind (Classical.arbitrary M) trivial⟩
  let : IsNoetherian ℝ (E × ℝ) := IsNoetherian.iff_fg.2 inferInstance
  let : FiniteDimensional ℝ (ι → E × ℝ) := IsNoetherian.iff_fg.1 inferInstance
  set n := Module.finrank ℝ (ι → E × ℝ) with hn
  have hN : 0 < n := Module.finrank_pos
  set eEF : (ι → E × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm with heEF
  set Phi : M → EuclideanSpace ℝ (Fin n) := fun x => eEF (f.embPiTan x) with hPhi
  have hPhicomp : Phi = ⇑eEF ∘ ⇑f.embPiTan := rfl
  have hPhism : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Phi :=
    eEF.toDiffeomorph.contMDiff.comp f.embPiTan.contMDiff
  have hPhiinj : Injective Phi := eEF.injective.comp (f.embPiTan_injective)
  have hPhid : ∀ x, Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Phi x) := by
    intro x
    rw [hPhicomp, mfderiv_comp x eEF.differentiableAt.mdifferentiableAt
        (f.embPiTan.contMDiff.mdifferentiableAt (by simp)), eEF.mfderiv_eq]
    exact eEF.injective.comp (f.embPiTan_injective_mfderiv _ trivial)
  -- the image of the compact `M` is bounded, so a small enough dilation lands in the cube
  obtain ⟨x₀, -, hmax⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty (α := M))
    (continuous_norm.comp hPhism.continuous).continuousOn
  set C := ‖Phi x₀‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  set eps := Real.pi / (C + 1) with heps
  have hCpos : 0 < C + 1 := by linarith
  have hepspos : 0 < eps := div_pos Real.pi_pos hCpos
  have hepsne : eps ≠ 0 := ne_of_gt hepspos
  have hbound : ∀ (x : M) (j : Fin n), |eps * Phi x j| < Real.pi := by
    intro x j
    have h1 : |Phi x j| ≤ ‖Phi x‖ := by
      have := PiLp.norm_apply_le (p := 2) (Phi x) j
      simpa using this
    have h2 : ‖Phi x‖ ≤ C := hmax (mem_univ x)
    have h3 : |eps * Phi x j| = eps * |Phi x j| := by
      rw [abs_mul, abs_of_pos hepspos]
    rw [h3]
    have h4 : eps * |Phi x j| ≤ eps * C := mul_le_mul_of_nonneg_left (h1.trans h2) hepspos.le
    have h5 : eps * C < Real.pi := by
      rw [heps, div_mul_eq_mul_div, div_lt_iff₀ hCpos]
      nlinarith [Real.pi_pos]
    linarith
  refine ⟨n, fun x => eps • Phi x, hN, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => eps) := contMDiff_const
    exact hc.smul hPhism
  · intro x y hxy
    exact hPhiinj (smul_right_injective (EuclideanSpace ℝ (Fin n)) hepsne hxy)
  · intro x
    have hmd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Phi x :=
      hPhism.mdifferentiableAt (by simp)
    have hd := const_smul_mfderiv (I := I) hmd eps
    intro a b hab
    apply hPhid x
    have h1 : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun x => eps • Phi x) x) a
        = eps • (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Phi x) a := by
      rw [show (fun x => eps • Phi x) = eps • Phi from rfl, hd]
      rfl
    have h2 : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun x => eps • Phi x) x) b
        = eps • (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Phi x) b := by
      rw [show (fun x => eps • Phi x) = eps • Phi from rfl, hd]
      rfl
    rw [h1, h2] at hab
    exact smul_right_injective (EuclideanSpace ℝ (Fin n)) hepsne hab
  · intro x j
    exact hbound x j
  · intro h hh
    obtain ⟨F₀, hF₀, hF₀eq⟩ := SmoothBumpCovering.exists_extension f hh
    refine ⟨fun y => F₀ (eEF.symm (eps⁻¹ • y)), ?_, ?_⟩
    · exact hF₀.comp (eEF.symm.contDiff.comp (contDiff_id.const_smul eps⁻¹))
    · intro x
      change F₀ (eEF.symm (eps⁻¹ • (eps • Phi x))) = h x
      rw [inv_smul_smul₀ hepsne, hPhi]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
      exact hF₀eq x

/-! ### The ambient metric for a manifold modelled on a general normed space

  `exists_ambient_metric` (S3) assumes the model space `E` carries an inner product
  (the pseudo-inverse of `du_x` is built from an adjoint).  Here `E` is only a
  finite-dimensional normed space, so the construction is transported along a linear
  isomorphism `ll : E ≃L[ℝ] F` with `F` Euclidean; `toEuclidean` provides such an `ll`. -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- Smoothness of `x ↦ (f x).bilinearComp (p x) (q x)` (as `contMDiffAt_bilinearComp`, but
  without an inner product on the model space `E`). -/
theorem contMDiffAt_bilinearComp' {A B C A' B' : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup A'] [NormedSpace ℝ A'] [NormedAddCommGroup B'] [NormedSpace ℝ B']
    {f : M → A →L[ℝ] B →L[ℝ] C} {p : M → A' →L[ℝ] A} {q : M → B' →L[ℝ] B} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(ℝ, A →L[ℝ] B →L[ℝ] C) ∞ f x₀)
    (hp : ContMDiffAt I 𝓘(ℝ, A' →L[ℝ] A) ∞ p x₀)
    (hq : ContMDiffAt I 𝓘(ℝ, B' →L[ℝ] B) ∞ q x₀) :
    ContMDiffAt I 𝓘(ℝ, A' →L[ℝ] B' →L[ℝ] C) ∞
      (fun x => (f x).bilinearComp (p x) (q x)) x₀ :=
  contDiff_clm_flip.comp_contMDiffAt
    ((contDiff_clm_flip.comp_contMDiffAt (hf.clm_comp hp)).clm_comp hq)

omit [FiniteDimensional ℝ E] in
/-- **S3 for a general model space.**  Along a smooth immersion `u : M → E'` there is a
  smooth family of positive-definite symmetric bilinear forms on `E'` pulling back to `g`.
  Same statement as `exists_ambient_metric`, but the model space `E` of `M` is only assumed
  to be a finite-dimensional normed space: the pseudo-inverse construction is transported
  along a linear isomorphism `ll : E ≃L[ℝ] F` onto an inner-product space `F`. -/
theorem exists_ambient_metric_of_equiv {E' F : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (ll : E ≃L[ℝ] F)
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {u : M → E'} (hu : ContMDiff I 𝓘(ℝ, E') ∞ u)
    (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, E') u x)) :
    ∃ G : M → (E' →L[ℝ] E' →L[ℝ] ℝ),
      ContMDiff I 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ G ∧
      (∀ x a b, G x a b = G x b a) ∧
      (∀ x a, a ≠ 0 → 0 < G x a a) ∧
      (∀ x (v w : E), G x (diff (I := I) u x v) (diff (I := I) u x w) = metricAt g x v w) := by
  classical
  have hinj' : ∀ x, Injective (diff (I := I) u x) := hinj
  set Lh : M → (F →L[ℝ] E') := fun x => diff (I := I) u x ∘L (ll.symm : F →L[ℝ] E) with hLhdef
  have hLhinj : ∀ x, Injective (Lh x) := by
    intro x a b hab
    exact ll.symm.injective ((hinj' x) hab)
  set P : M → (E' →L[ℝ] F) := fun x => pinv (Lh x) with hPdef
  set gh : M → (F →L[ℝ] F →L[ℝ] ℝ) := fun x =>
    (metricAt g x).bilinearComp (ll.symm : F →L[ℝ] E) (ll.symm : F →L[ℝ] E) with hghdef
  have happ : ∀ (x : M) (a b : E'),
      ((gh x).bilinearComp (P x) (P x) +
        (innerBilin E').bilinearComp (ContinuousLinearMap.id ℝ E' - Lh x ∘L P x)
          (ContinuousLinearMap.id ℝ E' - Lh x ∘L P x)) a b =
      metricAt g x (ll.symm (P x a)) (ll.symm (P x b)) +
        inner ℝ (a - Lh x (P x a)) (b - Lh x (P x b)) := fun x a b => rfl
  have hPL : ∀ (x : M) (v : E), P x (diff (I := I) u x v) = ll v := by
    intro x v
    have h := ContinuousLinearMap.ext_iff.1 (pinv_comp (hLhinj x)) (ll v)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.id_apply] at h
    have h2 : Lh x (ll v) = diff (I := I) u x v := by simp [hLhdef]
    rw [h2] at h
    exact h
  refine ⟨fun x => (gh x).bilinearComp (P x) (P x) +
      (innerBilin E').bilinearComp (ContinuousLinearMap.id ℝ E' - Lh x ∘L P x)
        (ContinuousLinearMap.id ℝ E' - Lh x ∘L P x), ?_, ?_, ?_, ?_⟩
  · -- smoothness, in the tangent coordinates at each `x₀`
    intro x₀
    set Lt : M → E →L[ℝ] E' :=
      inTangentCoordinates I 𝓘(ℝ, E') id u (mfderiv I 𝓘(ℝ, E') u) x₀ with hLtdef
    set Lht : M → F →L[ℝ] E' := fun x => Lt x ∘L (ll.symm : F →L[ℝ] E) with hLhtdef
    set gt : M → E →L[ℝ] E →L[ℝ] ℝ := fun x => (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, g.inner x⟩).2 with hgtdef
    set ght : M → F →L[ℝ] F →L[ℝ] ℝ := fun x =>
      (gt x).bilinearComp (ll.symm : F →L[ℝ] E) (ll.symm : F →L[ℝ] E) with hghtdef
    have hx₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    obtain ⟨S₀, hS₀⟩ := tcoord_isInvertible (I := I) (x₀ := x₀) (x := x₀) hx₀
    have hLt₀ : Lt x₀ = diff (I := I) u x₀ ∘L (S₀ : E →L[ℝ] E) := by
      rw [hS₀, hLtdef]
      exact inTangentCoordinates_mfderiv_eq hx₀
    have hLht₀inj : Injective (Lht x₀) := by
      intro a b hab
      apply ll.symm.injective
      apply S₀.injective
      apply hinj' x₀
      have h : (Lt x₀) (ll.symm a) = (Lt x₀) (ll.symm b) := hab
      rw [hLt₀] at h
      simpa using h
    have hLhtm : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] E') ∞ Lht x₀ :=
      (contMDiffAt_inTangentCoordinates_mfderiv hu x₀).clm_comp contMDiffAt_const
    have hPtm : ContMDiffAt I 𝓘(ℝ, E' →L[ℝ] F) ∞ (fun x => pinv (Lht x)) x₀ :=
      (contDiffAt_pinv hLht₀inj).comp_contMDiffAt hLhtm
    have hghtm : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞ ght x₀ :=
      contMDiffAt_bilinearComp' (contMDiffAt_metric_trivialization g x₀) contMDiffAt_const
        contMDiffAt_const
    have hRm : ContMDiffAt I 𝓘(ℝ, E' →L[ℝ] E') ∞
        (fun x => ContinuousLinearMap.id ℝ E' - Lht x ∘L pinv (Lht x)) x₀ :=
      contMDiffAt_const.sub (hLhtm.clm_comp hPtm)
    have hsmooth : ContMDiffAt I 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞
        (fun x => (ght x).bilinearComp (pinv (Lht x)) (pinv (Lht x)) +
          (innerBilin E').bilinearComp (ContinuousLinearMap.id ℝ E' - Lht x ∘L pinv (Lht x))
            (ContinuousLinearMap.id ℝ E' - Lht x ∘L pinv (Lht x))) x₀ :=
      (contMDiffAt_bilinearComp' hghtm hPtm hPtm).add
        (contMDiffAt_bilinearComp' contMDiffAt_const hRm hRm)
    refine hsmooth.congr_of_eventuallyEq ?_
    filter_upwards [chart_source_mem_nhds H x₀] with x hx
    obtain ⟨S, hS⟩ := tcoord_isInvertible (I := I) (x₀ := x₀) (x := x) hx
    have hLtx : Lt x = diff (I := I) u x ∘L (S : E →L[ℝ] E) := by
      rw [hS, hLtdef]
      exact inTangentCoordinates_mfderiv_eq hx
    set Sh : F ≃L[ℝ] F := (ll.symm.trans S).trans ll with hShdef
    have hLhtx : Lht x = Lh x ∘L (Sh : F →L[ℝ] F) := by
      ext a
      simp [hLhtdef, hLtx, hLhdef, hShdef]
    have hPt : pinv (Lht x) = (Sh.symm : F →L[ℝ] F) ∘L P x := by
      rw [hLhtx]
      exact pinv_comp_equiv (hLhinj x) Sh
    have hLP : Lht x ∘L pinv (Lht x) = Lh x ∘L P x := by
      rw [hPt, hLhtx]
      ext a
      simp
    have hLPa : ∀ c : E', Lht x (pinv (Lht x) c) = Lh x (P x c) := fun c =>
      ContinuousLinearMap.ext_iff.1 hLP c
    have hgterm : ∀ a b : E', ght x (pinv (Lht x) a) (pinv (Lht x) b) =
        metricAt g x (ll.symm (P x a)) (ll.symm (P x b)) := by
      intro a b
      have hmt := metric_trivialization_apply g hx
        ((ll.symm : F →L[ℝ] E) (pinv (Lht x) a)) ((ll.symm : F →L[ℝ] E) (pinv (Lht x) b))
      have hc : ∀ c : E', tcoord I x₀ x ((ll.symm : F →L[ℝ] E) (pinv (Lht x) c))
          = ll.symm (P x c) := by
        intro c
        rw [hPt, ← hS]
        simp [hShdef]
      rw [hc, hc] at hmt
      exact hmt
    ext a b
    rw [happ, ← hgterm, ← hLPa a, ← hLPa b]
    rfl
  · intro x a b
    rw [happ, happ, real_inner_comm]
    congr 1
    exact g.symm x _ _
  · intro x a ha
    rw [happ]
    rcases eq_or_ne (ll.symm (P x a)) 0 with h | h
    · have hP0 : P x a = 0 := by
        have := congrArg ll h
        simpa using this
      have hR : a - Lh x (P x a) = a := by simp [hP0]
      have hpos : (0:ℝ) < inner ℝ a a := real_inner_self_pos.2 ha
      rw [hR, h]
      simpa using hpos
    · have h1 : 0 < metricAt g x (ll.symm (P x a)) (ll.symm (P x a)) := g.pos x _ h
      have h2 : (0:ℝ) ≤ inner ℝ (a - Lh x (P x a)) (a - Lh x (P x a)) := real_inner_self_nonneg
      linarith
  · intro x v w
    rw [happ, hPL, hPL]
    simp [hLhdef]

/-- **S5-2 (the ambient matrix field).**  Given such a `u` and the metric `g`, there is a
  smooth matrix field `G` on `ℝᴺ`, symmetric and with positive quadratic form everywhere,
  equal to the identity outside a compact subset of the open cube, whose values along `u`
  pull back to `g`.  (S3 `exists_ambient_metric` + `formMatrix` + extension + `symmetrize`
  + cutoff `ψ` from `exists_cutoff_compact` on `W := {quadForm pos} ∩ openCube`.
  Smoothness of `formMatrix ∘ G₃ : M → Matrix` is `contDiff_formMatrix.comp_contMDiff`
  applied to S3's `ContMDiff` conclusion; `hext` then needs it as `ContMDiff I 𝓘(ℝ, Matrix …)
      ∞`.) -/
theorem exists_ambient_matrix_field {N : ℕ} [CompactSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {u : M → EuclideanSpace ℝ (Fin N)} (hu : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ u)
    (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) u x))
    (hcube : ∀ x, (EuclideanSpace.equiv (Fin N) ℝ (u x)) ∈ openCube N)
    (hext : ∀ h : M → Matrix (Fin N) (Fin N) ℝ, ContMDiff I 𝓘(ℝ, Matrix (Fin N) (Fin N) ℝ) ∞ h →
        ∃ F : EuclideanSpace ℝ (Fin N) → Matrix (Fin N) (Fin N) ℝ,
          ContDiff ℝ ∞ F ∧ ∀ x, F (u x) = h x) :
    ∃ G : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ, ContDiff ℝ ∞ G ∧
      (∀ y, (G y).IsSymm) ∧ (∀ y v, v ≠ 0 → 0 < v ⬝ᵥ (G y).mulVec v) ∧
      (∀ y, G y - 1 ≠ 0 → y ∈ openCube N) ∧ HasCompactSupport (fun y => G y - 1) ∧
      ∀ x (a b : E),
        (EuclideanSpace.equiv (Fin N) ℝ (diff (I := I) u x a)) ⬝ᵥ
          (G (EuclideanSpace.equiv (Fin N) ℝ (u x))).mulVec
            (EuclideanSpace.equiv (Fin N) ℝ (diff (I := I) u x b)) = metricAt g x a b := by
  classical
  obtain ⟨G₃, hG₃sm, hG₃symm, hG₃pos, hG₃pull⟩ :=
    exists_ambient_metric_of_equiv (toEuclidean (E := E)) g hu hinj
  set eN := EuclideanSpace.equiv (Fin N) ℝ with heN
  have hco : ∀ z : EuclideanSpace ℝ (Fin N), eN z = z.ofLp := fun z => rfl
  have hmsymm : ∀ x, (formMatrix (G₃ x)).IsSymm := by
    intro x
    change (formMatrix (G₃ x))ᵀ = formMatrix (G₃ x)
    ext i j
    simp [formMatrix, Matrix.transpose_apply, hG₃symm x]
  have hhs : ContMDiff I 𝓘(ℝ, Matrix (Fin N) (Fin N) ℝ) ∞ (fun x => formMatrix (G₃ x)) :=
    contDiff_formMatrix.comp_contMDiff hG₃sm
  obtain ⟨F₀, hF₀, hF₀eq⟩ := hext _ hhs
  set G₁ : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ := fun y => symmetrize (F₀ (eN.symm y))
    with hG₁def
  have hG₁ : ContDiff ℝ ∞ G₁ := contDiff_symmetrize.comp (hF₀.comp eN.symm.contDiff)
  have hG₁symm : ∀ y, (G₁ y).IsSymm := fun y => symmetrize_isSymm _
  have hkey : ∀ x, G₁ (eN (u x)) = formMatrix (G₃ x) := by
    intro x
    have h1 : eN.symm (eN (u x)) = u x := eN.symm_apply_apply _
    rw [hG₁def]
    simp only [h1, hF₀eq x]
    exact symmetrize_eq_self (hmsymm x)
  have hquad : ∀ (x : M) (v : Fin N → ℝ), v ≠ 0 → 0 < v ⬝ᵥ (formMatrix (G₃ x)).mulVec v := by
    intro x v hv
    have hne : (eN.symm v) ≠ 0 := by
      intro hz
      apply hv
      have := congrArg (fun z : EuclideanSpace ℝ (Fin N) => eN z) hz
      simpa using this
    have h := hG₃pos x (eN.symm v) hne
    rw [formMatrix_apply] at h
    exact h
  set W : Set (Fin N → ℝ) :=
    (G₁ ⁻¹' {A : Matrix (Fin N) (Fin N) ℝ | ∀ v, v ≠ 0 → 0 < v ⬝ᵥ A.mulVec v}) ∩ openCube N
    with hWdef
  have hWopen : IsOpen W := (isOpen_quadForm_pos.preimage hG₁.continuous).inter (isOpen_openCube N)
  set K : Set (Fin N → ℝ) := (fun x => eN (u x)) '' univ with hKdef
  have hKcpt : IsCompact K := isCompact_univ.image (eN.continuous.comp hu.continuous)
  have hKW : K ⊆ W := by
    rintro _ ⟨x, -, rfl⟩
    refine ⟨?_, hcube x⟩
    change ∀ v, v ≠ 0 → 0 < v ⬝ᵥ (G₁ (eN (u x))).mulVec v
    rw [hkey x]
    exact hquad x
  obtain ⟨ψ, hψ, hψ1, hψ0, hψI⟩ := exists_cutoff_compact hKcpt hWopen hKW
  set Gm : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ :=
    fun y => ψ y • G₁ y + (1 - ψ y) • (1 : Matrix (Fin N) (Fin N) ℝ) with hGmdef
  have hGm : ∀ y, Gm y = ψ y • G₁ y + (1 - ψ y) • (1 : Matrix (Fin N) (Fin N) ℝ) := fun y => rfl
  have hzero : ∀ y, ψ y = 0 → Gm y - 1 = 0 := by
    intro y hy
    rw [hGm, hy]
    simp
  have hmemW : ∀ y, Gm y - 1 ≠ 0 → y ∈ W := by
    intro y hy
    by_contra hyW
    exact hy (hzero y (hψ0 y hyW))
  refine ⟨Gm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hψ.smul hG₁).add ((contDiff_const.sub hψ).smul contDiff_const)
  · intro y
    rw [hGm]
    exact ((hG₁symm y).smul _).add ((Matrix.isSymm_one).smul _)
  · intro y v hv
    rw [hGm]
    have hqe : v ⬝ᵥ (ψ y • G₁ y + (1 - ψ y) • (1 : Matrix (Fin N) (Fin N) ℝ)).mulVec v
        = ψ y * (v ⬝ᵥ (G₁ y).mulVec v)
          + (1 - ψ y) * (v ⬝ᵥ (1 : Matrix (Fin N) (Fin N) ℝ).mulVec v) := by
      rw [Matrix.add_mulVec, dotProduct_add, quadForm_smul_matrix, quadForm_smul_matrix]
    rw [hqe]
    have h1 : 0 < v ⬝ᵥ (1 : Matrix (Fin N) (Fin N) ℝ).mulVec v := quadForm_one_pos v hv
    rcases eq_or_ne (ψ y) 0 with h | h
    · rw [h]
      simpa using h1
    · have hyW : y ∈ W := by
        by_contra hy
        exact h (hψ0 y hy)
      have h2 : 0 < v ⬝ᵥ (G₁ y).mulVec v := hyW.1 v hv
      have h3 : 0 < ψ y := lt_of_le_of_ne (hψI y).1 (Ne.symm h)
      have h4 : 0 ≤ 1 - ψ y := by linarith [(hψI y).2]
      nlinarith
  · exact fun y hy => (hmemW y hy).2
  · have hsub : (Function.support fun y => Gm y - 1)
        ⊆ Metric.closedBall (0 : Fin N → ℝ) Real.pi := by
      intro y hy
      have hcube' : y ∈ openCube N := (hmemW y hy).2
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 fun j =>
        (Real.norm_eq_abs _ ▸ (hcube' j).le)
    exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin N → ℝ) Real.pi)
      isClosed_closure (closure_minimal hsub Metric.isClosed_closedBall)
  · intro x a b
    have hy : eN (u x) ∈ K := ⟨x, mem_univ x, rfl⟩
    rw [hGm, hψ1 _ hy]
    simp only [sub_self, zero_smul, add_zero, one_smul]
    rw [hkey x, hco, hco, ← formMatrix_apply (G₃ x) (diff (I := I) u x a) (diff (I := I) u x b)]
    exact hG₃pull x a b

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **S5-3 (pullback through a realization).**  If `v` realizes `gT` and `w := equiv.symm ∘ v ∘
equiv ∘ u`,
  then `⟪dw a, dw b⟫ = (equiv (du a)) ⬝ᵥ gT (equiv (u x)) (equiv (du b))`. -/
theorem inner_mfderiv_comp_realizes {N q : ℕ}
    {u : M → EuclideanSpace ℝ (Fin N)} (hu : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ u)
    {v : (Fin N → ℝ) → (Fin q → ℝ)} (hv : ContDiff ℝ ∞ v)
    {gT : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ} (hr : Realizes v gT) (x : M) (a b : E) :
    let w : M → EuclideanSpace ℝ (Fin q) :=
      fun y => (EuclideanSpace.equiv (Fin q) ℝ).symm (v (EuclideanSpace.equiv (Fin N) ℝ (u y)))
    inner ℝ (toEuclid (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w x a))
            (toEuclid (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w x b)) =
      (EuclideanSpace.equiv (Fin N) ℝ (diff (I := I) u x a)) ⬝ᵥ
        (gT (EuclideanSpace.equiv (Fin N) ℝ (u x))).mulVec
          (EuclideanSpace.equiv (Fin N) ℝ (diff (I := I) u x b)) := by
  intro w
  set eN := EuclideanSpace.equiv (Fin N) ℝ with heN
  set eQ := EuclideanSpace.equiv (Fin q) ℝ with heQ
  set L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
    (eQ.symm : (Fin q → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin q)).comp
      ((fderiv ℝ v (eN (u x))).comp (eN : EuclideanSpace ℝ (Fin N) →L[ℝ] (Fin N → ℝ))) with hL
  have hfd : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin N) => eQ.symm (v (eN z))) L (u x) := by
    have h1 : HasFDerivAt v (fderiv ℝ v (eN (u x))) (eN (u x)) :=
      (hv.differentiable (by simp)).differentiableAt.hasFDerivAt
    exact eQ.symm.hasFDerivAt.comp (u x) (h1.comp (u x) eN.hasFDerivAt)
  have hux : HasMFDerivAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) u x
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) u x) :=
    (hu.mdifferentiableAt (by simp)).hasMFDerivAt
  have hw : HasMFDerivAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w x
      (L.comp (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) u x)) :=
    hfd.hasMFDerivAt.comp x hux
  rw [hw.mfderiv]
  change inner ℝ (eQ.symm (fderiv ℝ v (eN (u x)) (eN (diff (I := I) u x a))))
      (eQ.symm (fderiv ℝ v (eN (u x)) (eN (diff (I := I) u x b)))) = _
  rw [show ∀ p p' : Fin q → ℝ, inner ℝ (eQ.symm p) (eQ.symm p') = p ⬝ᵥ p' from fun p p' => by
    simp [heQ, PiLp.inner_apply, dotProduct, mul_comm]]
  exact realizes_fderiv_dot hr _ _ _

/-- **S5-4 (injectivity through the cube).**  A map injective modulo `2πℤᴺ` is injective on
  the open cube `(-π,π)ᴺ`. -/
theorem injOn_openCube_of_isInjectiveMod2Pi {N q : ℕ} {v : (Fin N → ℝ) → (Fin q → ℝ)}
    (hv : IsInjectiveMod2Pi v) : InjOn v (openCube N) := by
  intro x hx y hy hxy
  obtain ⟨k, hk⟩ := hv x y hxy
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  funext j
  have hkj : x j - y j = 2 * Real.pi * (k j : ℝ) := by
    have := congrFun hk j
    simpa [NashEmbedding.Sobolev.periodicShift, Pi.sub_apply] using this
  have hxj : |x j| < Real.pi := hx j
  have hyj : |y j| < Real.pi := hy j
  rw [abs_lt] at hxj hyj
  have habs : |(k j : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hk0 : k j = 0 := by
    have h1 : ((|k j| : ℤ) : ℝ) < 1 := by rwa [Int.cast_abs]
    have h2 : |k j| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.mp h2
  rw [hk0] at hkj
  simp only [Int.cast_zero, mul_zero, sub_eq_zero] at hkj
  exact hkj

/-- **Nash embedding theorem (compact case).**  Every compact `C^∞` Riemannian
  manifold admits a `C^∞` injective map into some Euclidean space that pulls the
  Euclidean metric back to the given one.  (Injective + compact + Hausdorff gives
  a closed topological embedding; injectivity of `dw` follows from positivity of
  `g`.  Both are corollaries, not part of the statement.)

  `[I.Boundaryless]` is required by the Whitney-extension step
  (`NashEmbedding/Compact/WhitneyExtension.lean`): `I.Boundaryless` supplies
  open chart targets in `E`, which is what pushing a chart-supported function
  forward and extending by zero uses.  A model that satisfies only the
  pointwise `BoundarylessManifold I M`, or one with genuine boundary, would
  need extra argument here; nothing else in the reduction depends on
  `[I.Boundaryless]`. -/
theorem nashCompact [T2Space M] [CompactSpace M] [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    ∃ (q : ℕ) (w : M → EuclideanSpace ℝ (Fin q)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧
      Function.Injective w ∧
      PullsBackEuclidean g w := by
  classical
  -- Empty manifold: anything works.
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨0, fun x => (hM.elim x), ?_, ?_, ?_⟩
    · intro x; exact (hM.elim x)
    · intro x; exact (hM.elim x)
    · intro x; exact (hM.elim x)
  -- Step 1: Whitney immersion into the cube, with the extension property.
  obtain ⟨N, u, hN, hu, huinj, hdinj, hcube, hext⟩ := exists_immersion_in_cube (I := I) (M := M)
  -- Step 2: the ambient matrix field on ℝᴺ.
  obtain ⟨G, hG, hGsymm, hGpos, hGsupp, hGcpt, hGpull⟩ :=
    exists_ambient_matrix_field g hu hdinj hcube hext
  -- Step 3: periodize and apply `nashTorus`.
  set gT : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ := periodicMatrixExt N G with hgT
  have hgT_metric : IsPosDefSmoothMetric gT :=
    ⟨periodicMatrixExt_smoothPeriodic hG hGcpt,
     periodicMatrixExt_posDef hGsupp (fun y => posDef_of_isSymm_of_quadForm_pos (hGsymm y)
         (hGpos y))⟩
  obtain ⟨q, v, hvemb, hvreal⟩ := nashTorus hN hgT_metric
  -- Step 4: the embedding.
  let eN := EuclideanSpace.equiv (Fin N) ℝ
  let eq := EuclideanSpace.equiv (Fin q) ℝ
  refine ⟨q, fun y => eq.symm (v (eN (u y))), ?_, ?_, ?_⟩
  · -- smooth
    have h1 : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin N) => eq.symm (v (eN z))) :=
      eq.symm.contDiff.comp (hvemb.smoothPeriodic.smooth.comp eN.contDiff)
    exact h1.comp_contMDiff hu
  · -- injective
    intro x y hxy
    have hx := hcube x
    have hy := hcube y
    have : v (eN (u x)) = v (eN (u y)) := eq.symm.injective hxy
    have := injOn_openCube_of_isInjectiveMod2Pi hvemb.injective hx hy this
    exact huinj (eN.injective this)
  · -- pullback
    intro x a b
    rw [inner_mfderiv_comp_realizes hu hvemb.smoothPeriodic.smooth hvreal x a b]
    have hcx : ∀ j, |eN (u x) j| ≤ Real.pi := fun j => le_of_lt (hcube x j)
    rw [show gT (eN (u x)) = G (eN (u x)) from periodicMatrixExt_eq_of_mem hGsupp hcx]
    exact ((hGpull x a b).symm : _)

/-- **Corollary.** The map of `nashCompact` is a closed topological embedding. -/
theorem nashCompact_isClosedEmbedding [T2Space M] [CompactSpace M] [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    ∃ (q : ℕ) (w : M → EuclideanSpace ℝ (Fin q)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧
      Topology.IsClosedEmbedding w ∧
      PullsBackEuclidean g w := by
  obtain ⟨q, w, hw, hinj, hpull⟩ := nashCompact g
  exact ⟨q, w, hw, hw.continuous.isClosedEmbedding hinj, hpull⟩

omit [FiniteDimensional ℝ E] in
/-- **Corollary.** A map pulling the Euclidean metric back to a Riemannian metric has
  injective differential everywhere (an immersion). -/
theorem PullsBackEuclidean.injective_mfderiv
    {g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {q : ℕ} {w : M → EuclideanSpace ℝ (Fin q)} (h : PullsBackEuclidean g w) (x : M) :
    Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w x) := by
  intro v v' hvv'
  by_contra hne
  have hd : v - v' ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g.pos x (v - v') hd
  have h0 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w x (v - v') = 0 := by
    rw [map_sub, hvv', sub_self]
  have key : g.inner x (v - v') (v - v') = 0 := by
    have hgen := h x (v - v') (v - v')
    rw [h0] at hgen
    rw [hgen]
    -- `simp [norm_zero]` cannot fire here: the `0` carries `TangentSpace`'s derived
    -- `Zero` instance (v4.31 makes `TangentSpace` non-reducible), which only tactic
    -- `exact` reconciles with the Euclidean instances at default transparency.
    exact inner_zero_left _
  exact hpos.ne' key

end Statement

/-! ## Witnesses against the statement alone

  The informative witnesses live in `Examples/`: the round spheres and their
  products (`Examples/Sphere.lean`) and the `Circle × Circle` cross-check
  against `nashTorus` (`Examples/FlatTorus.lean`).  The degenerate witness
  below confirms only that the hypothesis type is inhabited and that the
  conclusion is attainable in the trivial case. -/

section Witnesses

/-- The point, as the `0`-dimensional Euclidean space. -/
abbrev Pt := EuclideanSpace ℝ (Fin 0)

/-- The standard (here: zero) metric on the point, at smoothness `∞`. -/
def ptMetric : ContMDiffRiemannianMetric 𝓘(ℝ, Pt) ∞ Pt
    (TangentSpace 𝓘(ℝ, Pt) : Pt → Type _) :=
  { riemannianMetricVectorSpace Pt with
    contMDiff := (riemannianMetricVectorSpace Pt).contMDiff.of_le le_top }

/-- **W0.** The hypothesis type of `nashCompact` is inhabited (on the point). -/
example : ContMDiffRiemannianMetric 𝓘(ℝ, Pt) ∞ Pt (TangentSpace 𝓘(ℝ, Pt) : Pt → Type _) :=
  ptMetric

/-- **W1.** The statement type-checks on the point and is provable there
    without `nashCompact`: the identity map works. -/
example : ∃ (q : ℕ) (w : Pt → EuclideanSpace ℝ (Fin q)),
    ContMDiff 𝓘(ℝ, Pt) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧
    Function.Injective w ∧ PullsBackEuclidean ptMetric w := by
  refine ⟨0, id, contMDiff_id, Function.injective_id, ?_⟩
  intro x v v'
  -- On the `0`-dimensional space every inner product is `0`; stating this with
  -- quantified arguments lets `rw` match both sides without any syntactic
  -- sensitivity to which `Zero` instance each vanishing argument carries.
  have hz : ∀ a b : EuclideanSpace ℝ (Fin 0), inner ℝ a b = (0 : ℝ) := fun a b => by
    rw [Subsingleton.elim a (0 : EuclideanSpace ℝ (Fin 0))]
    exact inner_zero_left _
  change inner ℝ (v : Pt) (v' : Pt) = _
  rw [hz]
  exact hz _ _

end Witnesses

end NashEmbedding

end
