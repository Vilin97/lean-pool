/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Tactic

/-!
# The ambient metric along an immersion

Let `u : M → E'` be a smooth immersion of a manifold `M` (modelled on `E`) into a
finite-dimensional real inner-product space `E'`, and `g` a smooth Riemannian
metric on `M`.  At each `x`, with `L = mfderiv u x : T_xM → E'` injective, put

    P := (L† ∘ L)⁻¹ ∘ L†   (left inverse of `L`),   Q := L ∘ P   (projection onto `range L`),
    G x a b := g_x (P a) (P b) + ⟪(1 - Q) a, (1 - Q) b⟫.

Then `G x` is a positive-definite symmetric bilinear form on `E'` with
`G x (L v) (L w) = g_x v w`, and `x ↦ G x` is smooth `M → (E' →L E' →L ℝ)`.

**Theorem** (`exists_ambient_metric`): such a `G` exists.  It is the input to the
Whitney-extension step (`WhitneyExtension.lean`), which extends `G ∘ u⁻¹`
from `u '' M` to a smooth matrix field on `E'`.

Smoothness.  `T_xM` is definitionally `E`, but `x ↦ mfderiv u x` is not
continuous as a raw map `M → (E →L E')` (the chart at `x` jumps).  Mathlib's
invariant form is `inTangentCoordinates`: near `x₀`,
    L̃ x := mfderiv u x ∘L S x,   S x := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x,
is smooth (`ContMDiffAt.mfderiv_const`), and similarly
    g̃ x a b := g.inner x (S x a) (S x b)
is smooth (section smoothness of `g` in the trivialization at `x₀`).  Since
`S x` is a linear isomorphism, `pinv (L ∘L S) = S⁻¹ ∘L pinv L`, so
    G x a b = g̃ x (pinv (L̃ x) a) (pinv (L̃ x) b) + ⟪(1 - L̃ x ∘L pinv (L̃ x)) a, …⟫,
a smooth expression in `L̃ x` and `g̃ x` (leaves L1–L4 for `pinv`).

Leaves L1–L7 and the assembly L8 were proved by Aristotle (project 6f927eaf, 2026-08-30).
-/

open scoped Manifold ContDiff Topology InnerProduct
open Set Function ContinuousLinearMap Bundle

noncomputable section

namespace NashEmbedding

/-! ## Pseudo-inverse of an injective linear map between inner-product spaces -/

section Pinv

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

/-- The Moore–Penrose left inverse `(L† ∘ L)⁻¹ ∘ L†` (with `inverse 0 = 0` if `L† ∘ L`
  is not invertible). -/
def pinv (L : E →L[ℝ] E') : E' →L[ℝ] E :=
  (ContinuousLinearMap.inverse (L.adjoint ∘L L)) ∘L L.adjoint

/-- **L1.** The adjoint is smooth (it is a linear isometry equivalence). -/
theorem contDiff_adjoint :
    ContDiff ℝ ∞ (fun L : E →L[ℝ] E' => L.adjoint) := by
  have h1 : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h2 : CompleteSpace E' := FiniteDimensional.complete ℝ E'
  let f : (E →L[ℝ] E') →ₗ[ℝ] (E' →L[ℝ] E) :=
    { toFun := fun L => L.adjoint
      map_add' := fun L L' => map_add ContinuousLinearMap.adjoint L L'
      map_smul' := fun c L => by simp }
  have hb : ∀ L : E →L[ℝ] E', ‖f L‖ ≤ 1 * ‖L‖ := by
    intro L
    simp only [one_mul]
    exact le_of_eq (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E') |>.norm_map L)
  exact (f.mkContinuous 1 hb).contDiff

/-- **L2.** For injective `L`, `L† ∘ L` is invertible. -/
theorem isInvertible_adjoint_comp_self {L : E →L[ℝ] E'} (hL : Injective L) :
    (L.adjoint ∘L L).IsInvertible := by
  have h1 : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h2 : CompleteSpace E' := FiniteDimensional.complete ℝ E'
  have hker : (L.adjoint ∘L L : E →L[ℝ] E).toLinearMap.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : (L.adjoint ∘L L) x = 0 := hx
    have h3 : ‖L x‖ ^ 2 = RCLike.re (inner ℝ ((L.adjoint ∘L L) x) x) :=
      ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left L x
    rw [hx0] at h3
    simp? at h3
    exact hL (by rw [h3, map_zero])
  have hrange : (L.adjoint ∘L L : E →L[ℝ] E).toLinearMap.range = ⊤ :=
    LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective).1 (LinearMap.ker_eq_bot.mp hker))
  exact ⟨ContinuousLinearEquiv.ofBijective (L.adjoint ∘L L) hker hrange, rfl⟩

/-- **L3.** `pinv` is a left inverse on injective maps. -/
theorem pinv_comp {L : E →L[ℝ] E'} (hL : Injective L) :
    pinv L ∘L L = ContinuousLinearMap.id ℝ E := by
  have h := isInvertible_adjoint_comp_self hL
  rw [pinv, ContinuousLinearMap.comp_assoc, h.inverse_comp_self]

/-- **L4.** `pinv` is smooth at injective maps. -/
theorem contDiffAt_pinv {L : E →L[ℝ] E'} (hL : Injective L) :
    ContDiffAt ℝ ∞ (pinv : (E →L[ℝ] E') → (E' →L[ℝ] E)) L := by
  have h1 : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hA : ContDiffAt ℝ ∞ (fun M : E →L[ℝ] E' => M.adjoint ∘L M) L :=
    (contDiff_adjoint.clm_comp contDiff_id).contDiffAt
  have hinv : ContDiffAt ℝ ∞ (ContinuousLinearMap.inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
      (L.adjoint ∘L L) := (isInvertible_adjoint_comp_self hL).contDiffAt_map_inverse
  have hcomp : ContDiffAt ℝ ∞
      (fun M : E →L[ℝ] E' => ContinuousLinearMap.inverse (M.adjoint ∘L M)) L :=
    ContDiffAt.comp (𝕜 := ℝ) (n := ∞) (x := L)
      (g := (ContinuousLinearMap.inverse : (E →L[ℝ] E) → (E →L[ℝ] E)))
      (f := fun M : E →L[ℝ] E' => M.adjoint ∘L M) hinv hA
  exact hcomp.clm_comp contDiff_adjoint.contDiffAt

/-- **L5.** Change of coordinates in the source: `pinv (L ∘ S) = S⁻¹ ∘ pinv L` for a
  linear isomorphism `S`. -/
theorem pinv_comp_equiv {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {L : E →L[ℝ] E'} (_hL : Injective L) (S : F ≃L[ℝ] E) :
    pinv (L ∘L (S : F →L[ℝ] E)) = ((S.symm : E →L[ℝ] F) ∘L pinv L) := by
  have h1 : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h2 : CompleteSpace E' := FiniteDimensional.complete ℝ E'
  have h3 : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hSadj : ((S : F →L[ℝ] E).adjoint).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := ((S.symm : E →L[ℝ] F).adjoint)) ?_ ?_
    · rw [← ContinuousLinearMap.adjoint_comp]; simp [ContinuousLinearMap.adjoint_id]
    · rw [← ContinuousLinearMap.adjoint_comp]; simp [ContinuousLinearMap.adjoint_id]
  have hS : ((S : F →L[ℝ] E)).IsInvertible := ⟨S, rfl⟩
  have key : ((L ∘L (S : F →L[ℝ] E)).adjoint ∘L (L ∘L (S : F →L[ℝ] E))) =
      (S : F →L[ℝ] E).adjoint ∘L ((L.adjoint ∘L L) ∘L (S : F →L[ℝ] E)) := by
    rw [ContinuousLinearMap.adjoint_comp]
    simp [ContinuousLinearMap.comp_assoc]
  change ContinuousLinearMap.inverse _ ∘L _ = _
  rw [key, hSadj.inverse_comp_of_left, hS.inverse_comp_of_right,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.inverse_equiv]
  simp only [ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc ((S : F →L[ℝ] E).adjoint).inverse
    ((S : F →L[ℝ] E).adjoint) L.adjoint, hSadj.inverse_comp_self]
  simp [pinv]

end Pinv

/-! ## Smoothness of the differential and of the metric in tangent coordinates

  `TangentSpace I x` is definitionally `E` but carries no norm, so `mfderiv` and
  `g.inner x` cannot be composed with `∘L` in statements.  We use Mathlib's
  invariant forms (`inTangentCoordinates`, the trivialization at `x₀`) for the
  smoothness leaves, and explicit definitional casts `diff`, `metricAt` for the
  pointwise algebra. -/

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- The differential `mfderiv u x`, read as a map `E →L E'` (definitional cast). -/
def diff (u : M → E') (x : M) : E →L[ℝ] E' := mfderiv I 𝓘(ℝ, E') u x

/-- The metric at `x`, read as a bilinear form on `E` (definitional cast). -/
def metricAt (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) (x : M) :
    E →L[ℝ] E →L[ℝ] ℝ := g.inner x

/-- Coordinate change from the model fibre to `T_xM ≅ E`, in the trivialization at `x₀`
  (definitional cast of `symmL`). -/
def tcoord (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] (x₀ x : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ x

omit [FiniteDimensional ℝ E] in
/-- **L6.** The differential in tangent coordinates at `x₀` is smooth near `x₀`
  (`ContMDiffAt.mfderiv_const`). -/
theorem contMDiffAt_inTangentCoordinates_mfderiv {u : M → E'} (hu : ContMDiff I 𝓘(ℝ, E') ∞ u)
    (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞
      (inTangentCoordinates I 𝓘(ℝ, E') id u (mfderiv I 𝓘(ℝ, E') u) x₀) x₀ :=
  (hu x₀).mfderiv_const (m := ∞) (n := ∞) (by simp)

omit [FiniteDimensional ℝ E] in
/-- **L6'.** Near `x₀`, `inTangentCoordinates` of the differential is `diff u x ∘L tcoord x₀ x`
  (the target-side coordinate change is the identity for a vector-space target). -/
theorem inTangentCoordinates_mfderiv_eq {u : M → E'} {x₀ x : M}
    (_hx : x ∈ (chartAt H x₀).source) :
    inTangentCoordinates I 𝓘(ℝ, E') id u (mfderiv I 𝓘(ℝ, E') u) x₀ x =
      diff (I := I) u x ∘L tcoord I x₀ x := by
  change ContinuousLinearMap.inCoordinates E (TangentSpace I) E' (TangentSpace 𝓘(ℝ, E')) x₀ x
      (u x₀) (u x) (mfderiv I 𝓘(ℝ, E') u x) = _
  rw [ContinuousLinearMap.inCoordinates]
  simp only [TangentBundle.continuousLinearMapAt_model_space, ContinuousLinearMap.one_def]
  ext v
  rfl

omit [FiniteDimensional ℝ E] in
/-- **L6''.** `tcoord I x₀ x` is a linear isomorphism for `x` in the chart at `x₀`. -/
theorem tcoord_isInvertible {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    (tcoord I x₀ x).IsInvertible := by
  have hb : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
  exact ⟨((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hb).symm,
    Trivialization.symm_continuousLinearEquivAt_eq' _ hb⟩

omit [FiniteDimensional ℝ E] in
/-- **L7.** The metric, read in the trivialization at `x₀`, is smooth near `x₀`
  (unfold `g.contMDiff` with `contMDiffAt_section`). -/
theorem contMDiffAt_metric_trivialization
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, g.inner x⟩).2) x₀ :=
  -- `(contMDiffAt_section x₀).1 (g.contMDiff x₀)`, up to unfolding `TotalSpace.mk'`.
  (contMDiffAt_section (F := E →L[ℝ] E →L[ℝ] ℝ) x₀).1 (g.contMDiff x₀)

omit [FiniteDimensional ℝ E] in
/-- **L7'.** Evaluation of the trivialized metric: for `x` in the chart at `x₀`,
  it is `metricAt g x (tcoord x₀ x a) (tcoord x₀ x b)`
  (`hom_trivializationAt_apply`, `inCoordinates_apply_eq₂`). -/
theorem metric_trivialization_apply
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) (a b : E) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, g.inner x⟩).2 a b =
      metricAt g x (tcoord I x₀ x a) (tcoord I x₀ x b) := by
  -- `hom_trivializationAt_apply`, then `inCoordinates_apply_eq₂` (the outer bundle is the
  -- trivial `ℝ`-bundle, whose `linearMapAt` is the identity); `x ∈ baseSet` is
  -- `FiberBundle.mem_baseSet_trivializationAt`-style from `hx`.
  have hb : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
  rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hb hb (Set.mem_univ _)]
  simp? [metricAt, tcoord]
  exact congrArg₂ (fun u v : TangentSpace I x => g.inner x u v)
    (Trivialization.symmL_apply (R := ℝ) _ hb a).symm
    (Trivialization.symmL_apply (R := ℝ) _ hb b).symm

end Coordinates

/-! ## The ambient metric -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

/-- The Euclidean inner product of `E'` as a real bilinear form (over `ℝ` the conjugate
  linearity of `innerSL` is trivial). -/
def innerBilin (E' : Type*) [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] :
    E' →L[ℝ] E' →L[ℝ] ℝ :=
  innerSL ℝ

/-- The ambient metric along `u` at `x`, as a bilinear form on `E'`:
  `G x a b = g_x (P a) (P b) + ⟪(1 - L P) a, (1 - L P) b⟫` with `L = diff u x`, `P = pinv L`. -/
def ambientMetric (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (u : M → E') (x : M) : E' →L[ℝ] E' →L[ℝ] ℝ :=
  let L : E →L[ℝ] E' := diff (I := I) u x
  let P : E' →L[ℝ] E := pinv L
  let R : E' →L[ℝ] E' := ContinuousLinearMap.id ℝ E' - L ∘L P
  (metricAt g x).bilinearComp P P + (innerBilin E').bilinearComp R R

theorem contDiff_clm_flip {A B C : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C] :
    ContDiff ℝ ∞ (fun f : A →L[ℝ] B →L[ℝ] C => f.flip) :=
  IsBoundedLinearMap.contDiff
    { map_add := fun f g => by ext b a; simp
      map_smul := fun c f => by ext b a; simp
      bound := ⟨1, one_pos, fun f => by simp⟩ }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- Smoothness of `x ↦ (f x).flip`. -/
theorem contMDiffAt_clm_flip {A B C : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : M → A →L[ℝ] B →L[ℝ] C} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(ℝ, A →L[ℝ] B →L[ℝ] C) ∞ f x₀) :
    ContMDiffAt I 𝓘(ℝ, B →L[ℝ] A →L[ℝ] C) ∞ (fun x => (f x).flip) x₀ :=
  contDiff_clm_flip.comp_contMDiffAt hf

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- Smoothness of `x ↦ (f x).bilinearComp (p x) (q x)`. -/
theorem contMDiffAt_bilinearComp {A B C A' B' : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup A'] [NormedSpace ℝ A'] [NormedAddCommGroup B'] [NormedSpace ℝ B']
    {f : M → A →L[ℝ] B →L[ℝ] C} {p : M → A' →L[ℝ] A} {q : M → B' →L[ℝ] B} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(ℝ, A →L[ℝ] B →L[ℝ] C) ∞ f x₀)
    (hp : ContMDiffAt I 𝓘(ℝ, A' →L[ℝ] A) ∞ p x₀)
    (hq : ContMDiffAt I 𝓘(ℝ, B' →L[ℝ] B) ∞ q x₀) :
    ContMDiffAt I 𝓘(ℝ, A' →L[ℝ] B' →L[ℝ] C) ∞
      (fun x => (f x).bilinearComp (p x) (q x)) x₀ :=
  contMDiffAt_clm_flip (I := I) ((contMDiffAt_clm_flip (I := I) (hf.clm_comp hp)).clm_comp hq)

/-- **L8 / S3.** Along a smooth immersion `u : M → E'`, there is a smooth family of
  positive-definite symmetric bilinear forms `G x` on `E'` pulling back to `g`:
  `G x (du_x v) (du_x w) = g_x v w`.  (Witness: `ambientMetric g u`.) -/
theorem exists_ambient_metric (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {u : M → E'} (hu : ContMDiff I 𝓘(ℝ, E') ∞ u)
    (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, E') u x)) :
    ∃ G : M → (E' →L[ℝ] E' →L[ℝ] ℝ),
      ContMDiff I 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ G ∧
      (∀ x a b, G x a b = G x b a) ∧
      (∀ x a, a ≠ 0 → 0 < G x a a) ∧
      (∀ x (v w : E), G x (diff (I := I) u x v) (diff (I := I) u x w) = metricAt g x v w) := by
  -- Witness `ambientMetric g u`.  Pullback: `pinv_comp` gives `P (L v) = v` and `R (L v) = 0`.
  -- Symmetry: `g.symm` and `real_inner_comm`.  Positivity: with `a ≠ 0`,
  -- `G x a a = metricAt g x (P a) (P a) + ‖R a‖²`; both terms are `≥ 0` (`g.pos`,
  -- `real_inner_self_nonneg`); if both vanish then `P a = 0` (from `g.pos`) and
  -- `R a = 0`, so `a = L (P a) + R a = 0`, contradiction.  Smoothness: it suffices to
  -- prove `ContMDiffAt` at each `x₀`; on the chart at `x₀` rewrite, using L6', L6'', L5,
  --   `diff u x = Lt x ∘L (tcoord x₀ x).inverse`, `pinv (diff u x) = tcoord x₀ x ∘L pinv (Lt x)`,
  -- where `Lt x := inTangentCoordinates … x₀ x` is smooth (L6), and
  --   `metricAt g x = (trivialized metric).bilinearComp (tcoord)⁻¹ (tcoord)⁻¹` (L7'),
  -- so `ambientMetric g u x = (trivialized metric x).bilinearComp (pinv (Lt x)) (pinv (Lt x))
  --   + (innerBilin E').bilinearComp (1 - Lt x ∘L pinv (Lt x)) (…)`, a smooth expression in
  -- the smooth `Lt x` (L6), the smooth trivialized metric (L7), and `pinv` (L4,
  -- `ContDiff.comp_contMDiff`);
  -- conclude with `ContMDiffAt.congr_of_eventuallyEq` on the chart source.
  have hinj' : ∀ x, Injective (diff (I := I) u x) := hinj
  have happ : ∀ (x : M) (a b : E'), ambientMetric g u x a b =
      metricAt g x (pinv (diff (I := I) u x) a) (pinv (diff (I := I) u x) b) +
        inner ℝ (a - diff (I := I) u x (pinv (diff (I := I) u x) a))
          (b - diff (I := I) u x (pinv (diff (I := I) u x) b)) := by
    intro x a b
    rfl
  have hPL : ∀ (x : M) (v : E), pinv (diff (I := I) u x) (diff (I := I) u x v) = v := by
    intro x v
    have := ContinuousLinearMap.ext_iff.1 (pinv_comp (hinj' x)) v
    simpa using this
  refine ⟨ambientMetric g u, ?_, ?_, ?_, ?_⟩
  · intro x₀
    set Lt : M → E →L[ℝ] E' :=
      inTangentCoordinates I 𝓘(ℝ, E') id u (mfderiv I 𝓘(ℝ, E') u) x₀ with hLtdef
    set gt : M → E →L[ℝ] E →L[ℝ] ℝ := fun x => (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, g.inner x⟩).2 with hgtdef
    have hx₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    obtain ⟨S₀, hS₀⟩ := tcoord_isInvertible (I := I) (x₀ := x₀) (x := x₀) hx₀
    have hLt₀ : Lt x₀ = diff (I := I) u x₀ ∘L (S₀ : E →L[ℝ] E) := by
      rw [hS₀, hLtdef]
      exact inTangentCoordinates_mfderiv_eq hx₀
    have hLtinj : Injective (Lt x₀) := by
      rw [hLt₀]
      exact (hinj' x₀).comp S₀.injective
    have hLtm : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ Lt x₀ :=
      contMDiffAt_inTangentCoordinates_mfderiv hu x₀
    have hPtm : ContMDiffAt I 𝓘(ℝ, E' →L[ℝ] E) ∞ (fun x => pinv (Lt x)) x₀ :=
      (contDiffAt_pinv hLtinj).comp_contMDiffAt hLtm
    have hgtm : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ gt x₀ :=
      contMDiffAt_metric_trivialization g x₀
    have hRm : ContMDiffAt I 𝓘(ℝ, E' →L[ℝ] E') ∞
        (fun x => ContinuousLinearMap.id ℝ E' - Lt x ∘L pinv (Lt x)) x₀ :=
      contMDiffAt_const.sub (hLtm.clm_comp hPtm)
    have hsmooth : ContMDiffAt I 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞
        (fun x => (gt x).bilinearComp (pinv (Lt x)) (pinv (Lt x)) +
          (innerBilin E').bilinearComp (ContinuousLinearMap.id ℝ E' - Lt x ∘L pinv (Lt x))
            (ContinuousLinearMap.id ℝ E' - Lt x ∘L pinv (Lt x))) x₀ :=
      (contMDiffAt_bilinearComp hgtm hPtm hPtm).add
        (contMDiffAt_bilinearComp contMDiffAt_const hRm hRm)
    refine hsmooth.congr_of_eventuallyEq ?_
    filter_upwards [chart_source_mem_nhds H x₀] with x hx
    obtain ⟨S, hS⟩ := tcoord_isInvertible (I := I) (x₀ := x₀) (x := x) hx
    have hLtx : Lt x = diff (I := I) u x ∘L (S : E →L[ℝ] E) := by
      rw [hS, hLtdef]
      exact inTangentCoordinates_mfderiv_eq hx
    have hPt : pinv (Lt x) = (S.symm : E →L[ℝ] E) ∘L pinv (diff (I := I) u x) := by
      rw [hLtx]
      exact pinv_comp_equiv (hinj' x) S
    have hTP : ∀ a : E', tcoord I x₀ x (pinv (Lt x) a) = pinv (diff (I := I) u x) a := by
      intro a
      rw [hPt, ← hS]
      simp
    have hLP : Lt x ∘L pinv (Lt x) = diff (I := I) u x ∘L pinv (diff (I := I) u x) := by
      rw [hPt, hLtx]
      ext a
      simp
    ext a b
    rw [happ, hLP]
    congr 1
    have hmt := metric_trivialization_apply g hx (pinv (Lt x) a) (pinv (Lt x) b)
    rw [hTP, hTP] at hmt
    exact hmt.symm
  · intro x a b
    rw [happ, happ, real_inner_comm]
    congr 1
    exact g.symm x _ _
  · intro x a ha
    rw [happ]
    have h1 : 0 ≤ metricAt g x (pinv (diff (I := I) u x) a) (pinv (diff (I := I) u x) a) := by
      rcases eq_or_ne (pinv (diff (I := I) u x) a) 0 with h | h
      · simp [h]
      · exact (g.pos x _ h).le
    have h2 : 0 ≤ inner ℝ (a - diff (I := I) u x (pinv (diff (I := I) u x) a))
        (a - diff (I := I) u x (pinv (diff (I := I) u x) a)) := real_inner_self_nonneg
    rcases eq_or_ne (pinv (diff (I := I) u x) a) 0 with h | h
    · have hR : a - diff (I := I) u x (pinv (diff (I := I) u x) a) = a := by simp [h]
      have : (0:ℝ) < inner ℝ a a := real_inner_self_pos.2 ha
      rw [hR]
      simpa [h] using this
    · have : 0 < metricAt g x (pinv (diff (I := I) u x) a) (pinv (diff (I := I) u x) a) :=
        g.pos x _ h
      linarith
  · intro x v w
    rw [happ, hPL, hPL]
    simp

end Main

end NashEmbedding

end
