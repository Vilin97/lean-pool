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
import Mathlib.Geometry.Manifold.Instances.Sphere
import LeanPool.NashEmbedding.NashEmbedding.Riemannian.Pullback
import LeanPool.NashEmbedding.NashEmbedding.Torus.Main

/-!
# Cross-check: the flat torus 𝕋² via `nashCompact` vs. `nashTorus`

Two independent Nash-embedding proofs meet on the same manifold.

* `nashTorus 2 flatMetric_isPosDefSmoothMetric` produces `IsInjRealizable (flatMetric 2)`
  directly on `ℝ²`, following Wassermann §7 (Günther's elliptic method).
* `nashCompact flatTorus2Metric` produces an ambient embedding
  `w : Circle × Circle → ℝᵍ` following Wassermann §13 (Whitney + ambient metric +
  periodize + `nashTorus` applied on `ℝᴺ`).

Composing `w` with the universal cover `torus2Wrap : ℝ² → Circle × Circle` and coercing
`EuclideanSpace ℝ (Fin q) → (Fin q → ℝ)` yields a second witness for
`IsInjRealizable (flatMetric 2)` — proved through the general machinery rather than
directly.  This is the sharpest test of the general reduction: it is the same theorem,
proved two ways, and both paths must terminate at witnesses of the same shape.

The geometric heart is L3 (`torus2Wrap_pullback`): `Circle.exp` is a local isometry
`(ℝ, ⟨·,·⟩) → (Circle, round metric)`, so the differential of `torus2Wrap` sends
standard basis vectors to unit tangent vectors on the two Circle factors, and the flat
product metric on `Circle × Circle` pulls back to the identity matrix on `ℝ²`.

The nine leaves were proved by Aristotle (project 1c05ddd8, 2026-08-30); the
assembly `torus2_matches_nashTorus` is by hand.  L7 is a general reusable fact
(`Realizes u g` + pointwise `PosDef g` ⇒ `HasFullRankDeriv u`).
-/

open scoped Manifold ContDiff Topology
open Bundle Function ContinuousLinearMap Complex Matrix

noncomputable
section

namespace NashEmbedding

/-! ## The round metric on `Circle` -/

section CircleMetric

/-- `Circle` is `sphere (0 : ℂ) 1`; the sphere framework needs
  `Fact (finrank ℝ ℂ = 1 + 1)`, and `Circle`'s `ChartedSpace` instance requires this.
  Scoped so importers of the file opt in via `open scoped NashEmbedding`. -/
scoped instance finrank_real_complex_fact' : Fact (Module.finrank ℝ ℂ = 1 + 1) :=
  Complex.finrank_real_complex_fact

/-- The coercion `Circle → ℂ`, bound with an explicit type annotation so that downstream
  typeclass resolution keeps seeing the target as `Circle` (not the unfolded
  `↥(Submonoid.unitSphere ℂ)`). -/
def circleCoe : Circle → ℂ := ((↑) : Circle → ℂ)

/-- Smoothness of `circleCoe` (via `contMDiff_coe_sphere`, with `Circle` matched
  through defeq). -/
theorem contMDiff_circleCoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ circleCoe :=
  contMDiff_coe_sphere

/-- **L1.** The coercion `Circle → ℂ` has injective differential everywhere
  (`injective_mvfderiv_subtypeVal_sphere` specialized to the ambient inner-product space `ℂ`). -/
theorem mfderiv_circleCoe_injective (v : Circle) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) circleCoe v) :=
  injective_mvfderiv_subtypeVal_sphere v

/-- The round metric on `Circle ⊂ ℂ`, induced by the inclusion. -/
def circleMetric :
    ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (TangentSpace (𝓡 1) : Circle → Type _) :=
  inducedMetric (E' := ℂ) contMDiff_circleCoe mfderiv_circleCoe_injective

end CircleMetric

/-! ## The flat product metric on `Circle × Circle` -/

section FlatTorus2

/-- The flat product metric on `Circle × Circle`, `circleMetric ⊕ circleMetric`. -/
def flatTorus2Metric :
    ContMDiffRiemannianMetric ((𝓡 1).prod (𝓡 1)) ∞
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (TangentSpace ((𝓡 1).prod (𝓡 1)) : Circle × Circle → Type _) :=
  prodMetric circleMetric circleMetric

end FlatTorus2

/-! ## The universal cover `ℝ² → Circle × Circle` -/

section Wrap

/-- The universal cover of `Circle × Circle` at level `2π`:
  `θ ↦ (Circle.exp θ₀, Circle.exp θ₁)`. -/
def torus2Wrap : (Fin 2 → ℝ) → Circle × Circle :=
  fun θ => (Circle.exp (θ 0), Circle.exp (θ 1))

/-- **L2a.** `torus2Wrap` is smooth as a map of manifolds. -/
theorem torus2Wrap_contMDiff :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) ∞ torus2Wrap :=
  (contMDiff_circleExp.comp (contDiff_apply ℝ ℝ 0).contMDiff).prodMk
    (contMDiff_circleExp.comp (contDiff_apply ℝ ℝ 1).contMDiff)

/-- **L2b.** `torus2Wrap θ = torus2Wrap θ'` iff `θ − θ' ∈ 2πℤ²`
  (`Circle.exp_eq_exp` on each factor). -/
theorem torus2Wrap_injective_mod_2pi :
    ∀ θ θ' : Fin 2 → ℝ, torus2Wrap θ = torus2Wrap θ' →
      ∃ k : Fin 2 → ℤ, θ - θ' = NashEmbedding.Sobolev.periodicShift 2 k := by
  intro θ θ' h
  obtain ⟨m₀, hm₀⟩ := Circle.exp_eq_exp.1 (congrArg Prod.fst h)
  obtain ⟨m₁, hm₁⟩ := Circle.exp_eq_exp.1 (congrArg Prod.snd h)
  refine ⟨![m₀, m₁], ?_⟩
  funext i
  fin_cases i <;> simp [NashEmbedding.Sobolev.periodicShift, hm₀, hm₁] <;> ring

end Wrap

/-! ## `torus2Wrap` is a local Riemannian isometry -/

section Isometry

open NashEmbedding.Sobolev

/-- The differential of `torus2Wrap` is the product of the differentials of `Circle.exp`
  on the two coordinates. -/
theorem mfderiv_torus2Wrap_apply (θ : Fin 2 → ℝ) (v : Fin 2 → ℝ) :
    mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ v =
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ 0) (v 0),
       mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ 1) (v 1)) := by
  have hproj : ∀ i : Fin 2, HasMFDerivAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) (fun θ : Fin 2 → ℝ => θ i) θ
      (ContinuousLinearMap.proj i) := fun i => (hasFDerivAt_apply i θ).hasMFDerivAt
  have hexp : ∀ i : Fin 2, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ i)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ i)) :=
    fun i => ((contMDiff_circleExp (m := ∞)).mdifferentiable (by simp) (θ i)).hasMFDerivAt
  have hc : ∀ i : Fin 2, HasMFDerivAt 𝓘(ℝ, Fin 2 → ℝ) (𝓡 1) (fun θ : Fin 2 → ℝ => Circle.exp (θ i))
      θ ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ i)).comp (ContinuousLinearMap.proj i)) :=
    fun i => (hexp i).comp θ (hproj i)
  have key := ((hc 0).prodMk (hc 1)).mfderiv
  have hwrap : torus2Wrap = fun θ : Fin 2 → ℝ => (Circle.exp (θ 0), Circle.exp (θ 1)) := rfl
  rw [hwrap, key]
  rfl

/- v4.31: `TangentSpace` is no longer unfolded at `instances` transparency, which breaks
type-class search and `rw` in goals that (by v4.28-era design) mix model-typed and
tangent-typed terms. We restore the old defeq semantics per declaration with the same
option Mathlib itself uses at this boundary (cf. `NormedSpace.fromTangentSpace`).
Migrating this file off the identification is tracked as post-registration debt. -/
/-- The differential of `circleCoe ∘ Circle.exp` at `t`, applied to `s : ℝ`:
  `s • (exp (i t) · i)`. -/
theorem mfderiv_circleCoe_exp_apply (t s : ℝ) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℂ) circleCoe (Circle.exp t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t s)
      = s • (Complex.exp (t * Complex.I) * Complex.I) := by
  have hexp : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) :=
    ((contMDiff_circleExp (m := ∞)).mdifferentiable (by simp) t).hasMFDerivAt
  have hcoe : HasMFDerivAt (𝓡 1) 𝓘(ℝ, ℂ) circleCoe (Circle.exp t)
      (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) circleCoe (Circle.exp t)) :=
    (contMDiff_circleCoe.mdifferentiable (by simp) (Circle.exp t)).hasMFDerivAt
  have hcomp := hcoe.comp t hexp
  have hfun : (circleCoe ∘ Circle.exp) = fun t : ℝ => Complex.exp (t * Complex.I) := by
    funext r
    exact Circle.coe_exp r
  rw [hfun] at hcomp
  let D : ℝ →L[ℝ] ℂ := (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) circleCoe (Circle.exp t)).comp
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t)
  have hfd : HasFDerivAt (fun t : ℝ => Complex.exp (t * Complex.I)) D t :=
    hasMFDerivAt_iff_hasFDerivAt.1 hcomp
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    have h_raw : HasDerivAt (⇑Complex.ofRealCLM) 1 t := Complex.ofRealCLM.hasDerivAt
    exact h_raw
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * (1 * Complex.I)) t := (h0.mul_const Complex.I).cexp
  have huniq := hfd.unique h2.hasFDerivAt
  -- `simpa` cannot match across the `TangentSpace`-vs-`ℂ` Eq-carrier; everything except
  -- `1 * I` is definitional, so rewrite that and let `exact` reconcile the rest.
  have happ := congrArg (fun L : ℝ →L[ℝ] ℂ => L s) huniq
  rw [one_mul] at happ
  exact happ

/-- The tangent vectors `s • (exp (i t) · i)` are unit vectors: their real inner products
  reduce to products of the scalars. -/
theorem inner_deriv_circle (t a b : ℝ) :
    (inner ℝ (a • (Complex.exp (t * Complex.I) * Complex.I))
      (b • (Complex.exp (t * Complex.I) * Complex.I)) : ℝ) = a * b := by
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp [Complex.norm_exp_ofReal_mul_I]

/-- **L3.** The pullback of `flatTorus2Metric` along `torus2Wrap` is the flat metric on
  `ℝ²`: at every `θ` and for any tangent vectors `v, v' : Fin 2 → ℝ`,
  `⟨v, v'⟩ = (flatTorus2Metric)_{torus2Wrap θ} (dtorus2Wrap v, dtorus2Wrap v')`.

  Proof idea.  On each factor, `mfderiv Circle.exp θᵢ (1 : ℝ) = i · exp(iθᵢ) ∈ ℂ`
  (chain rule `mfderiv coe ∘ mfderiv Circle.exp = fderiv (fun t => exp(i·t))`); the
  inner product in `ℂ` of `i·exp(iθᵢ)` with itself is `1`, and with the same for `j ≠ i`
  it is `0`.  Then `prodMetric_inner` splits into `circleMetric` on each factor, which by
  `inducedMetric_inner` unfolds to `⟨d(coe∘Circle.exp) e_i, d(coe∘Circle.exp) e_j⟩ = δᵢⱼ`. -/
theorem torus2Wrap_pullback (θ : Fin 2 → ℝ) (v v' : Fin 2 → ℝ) :
    (flatTorus2Metric.inner (torus2Wrap θ) :
        TangentSpace ((𝓡 1).prod (𝓡 1)) (torus2Wrap θ) →L[ℝ]
        TangentSpace ((𝓡 1).prod (𝓡 1)) (torus2Wrap θ) →L[ℝ] ℝ)
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ v)
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ v') =
    dotProduct v v' := by
  have main : metricAt (prodMetric circleMetric circleMetric) (torus2Wrap θ)
      ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ v :
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
      ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ v' :
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) = dotProduct v v' := by
    erw [prodMetric_inner, mfderiv_torus2Wrap_apply, mfderiv_torus2Wrap_apply]
    change (inner ℝ (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) circleCoe (Circle.exp (θ 0))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ 0) (v 0)))
        (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) circleCoe (Circle.exp (θ 0))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ 0) (v' 0))) : ℝ) +
        (inner ℝ (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) circleCoe (Circle.exp (θ 1))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ 1) (v 1)))
        (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) circleCoe (Circle.exp (θ 1))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ 1) (v' 1))) : ℝ) = _
    erw [mfderiv_circleCoe_exp_apply, mfderiv_circleCoe_exp_apply, mfderiv_circleCoe_exp_apply,
      mfderiv_circleCoe_exp_apply, inner_deriv_circle, inner_deriv_circle]
    simp [dotProduct, Fin.sum_univ_two]
  exact main

end Isometry

/-! ## Cross-check: `nashCompact` on `Circle × Circle` produces a `nashTorus` witness -/

section CrossCheck

open NashEmbedding.Sobolev

/-- **L4a.** Given `w : Circle × Circle → EuclideanSpace ℝ (Fin q)` from `nashCompact`, the
  composite `u := equiv ∘ w ∘ torus2Wrap : ℝ² → (Fin q → ℝ)` is smooth in the ordinary
  Fréchet sense (chain of smooth manifold maps + `mfderiv_eq_fderiv` on vector spaces). -/
theorem flatTorus_smooth {q : ℕ}
    (w : Circle × Circle → EuclideanSpace ℝ (Fin q))
    (hw : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w) :
    ContDiff ℝ ∞ (fun θ : Fin 2 → ℝ => (EuclideanSpace.equiv (Fin q) ℝ) (w (torus2Wrap θ))) := by
  rw [← contMDiff_iff_contDiff]
  exact (EuclideanSpace.equiv (Fin q) ℝ).contDiff.contMDiff.comp (hw.comp torus2Wrap_contMDiff)

/-- **L4b.** The composite `u = equiv ∘ w ∘ torus2Wrap` is `2πℤ²`-periodic (`Circle.exp`
  has period `2π` on each factor). -/
theorem flatTorus_periodic {q : ℕ}
    (w : Circle × Circle → EuclideanSpace ℝ (Fin q)) :
    IsPeriodic2Pi (fun θ : Fin 2 → ℝ => (EuclideanSpace.equiv (Fin q) ℝ) (w (torus2Wrap θ))) := by
  intro x k
  have h : ∀ i : Fin 2, Circle.exp ((x + periodicShift 2 k) i) = Circle.exp (x i) := fun i =>
    Circle.exp_eq_exp.2 ⟨k i, by simp [periodicShift]; ring⟩
  have hw2 : torus2Wrap (x + periodicShift 2 k) = torus2Wrap x := by
    simp only [torus2Wrap, h 0, h 1]
  exact congrArg _ (congrArg w hw2)

/-- Under the coercion `EuclideanSpace ℝ (Fin q) → (Fin q → ℝ)` the Euclidean inner product
  becomes the dot product. -/
theorem dotProduct_equiv {q : ℕ} (x y : EuclideanSpace ℝ (Fin q)) :
    dotProduct (EuclideanSpace.equiv (Fin q) ℝ x) (EuclideanSpace.equiv (Fin q) ℝ y)
      = inner ℝ x y := by
  simp [dotProduct, PiLp.inner_apply, mul_comm]

/-- The partial derivatives of the composite `equiv ∘ w ∘ torus2Wrap`, via the chain rule. -/
theorem partialDeriv_flatTorus {q : ℕ}
    (w : Circle × Circle → EuclideanSpace ℝ (Fin q))
    (hw : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w)
    (i : Fin 2) (θ : Fin 2 → ℝ) :
    partialDeriv i (fun θ : Fin 2 → ℝ => (EuclideanSpace.equiv (Fin q) ℝ) (w (torus2Wrap θ))) θ
      = (EuclideanSpace.equiv (Fin q) ℝ)
          (mfderiv ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w (torus2Wrap θ)
            (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ (Pi.single i 1))) := by
  have hwrap : HasMFDerivAt 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ) :=
    (torus2Wrap_contMDiff.mdifferentiable (by simp) θ).hasMFDerivAt
  have hw' : HasMFDerivAt ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w (torus2Wrap θ)
      (mfderiv ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w (torus2Wrap θ)) :=
    (hw.mdifferentiable (by simp) (torus2Wrap θ)).hasMFDerivAt
  have heq : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) 𝓘(ℝ, Fin q → ℝ)
      (EuclideanSpace.equiv (Fin q) ℝ) (w (torus2Wrap θ))
      ((EuclideanSpace.equiv (Fin q) ℝ).toContinuousLinearMap) :=
    hasMFDerivAt_iff_hasFDerivAt.2
      (EuclideanSpace.equiv (Fin q) ℝ).toContinuousLinearMap.hasFDerivAt
  have hcomp := (heq.comp (torus2Wrap θ) hw').comp θ hwrap
  have hfd : HasFDerivAt
      (fun θ : Fin 2 → ℝ => (EuclideanSpace.equiv (Fin q) ℝ) (w (torus2Wrap θ)))
      (((EuclideanSpace.equiv (Fin q) ℝ).toContinuousLinearMap.comp
        (mfderiv ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w (torus2Wrap θ))).comp
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ) :
          (Fin 2 → ℝ) →L[ℝ] (Fin q → ℝ)) θ := hasMFDerivAt_iff_hasFDerivAt.1 hcomp
  have hfderiv := hfd.fderiv
  rw [partialDeriv, hfderiv]
  rfl

/-- **L5.** The composite `u = equiv ∘ w ∘ torus2Wrap` realizes the flat metric on `ℝ²`:
  `∂ᵢu · ∂ⱼu = δᵢⱼ`.

  Proof idea.  `partialDeriv i u θ = fderiv u θ e_i`.  Under the coercion
  `EuclideanSpace.equiv`, the Euclidean inner product on `EuclideanSpace ℝ (Fin q)`
  matches `dotProduct` on `Fin q → ℝ`.  Chain rule and `mfderiv_eq_fderiv`:
  `fderiv u θ e_i = equiv (mfderiv w (torus2Wrap θ) (mfderiv torus2Wrap θ e_i))`.
  Then `PullsBackEuclidean g w` (with `g = flatTorus2Metric`) rewrites the ambient
  inner product as `flatTorus2Metric.inner (torus2Wrap θ) (dtorus2Wrap e_i) (dtorus2Wrap e_j)`,
  and `torus2Wrap_pullback` finishes with `dotProduct e_i e_j = δᵢⱼ = (flatMetric 2) θ i j`. -/
theorem flatTorus_realizes {q : ℕ}
    (w : Circle × Circle → EuclideanSpace ℝ (Fin q))
    (hw : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w)
    (hpull : PullsBackEuclidean flatTorus2Metric w) :
    Realizes (fun θ : Fin 2 → ℝ => (EuclideanSpace.equiv (Fin q) ℝ) (w (torus2Wrap θ)))
      (flatMetric 2) := by
  intro θ i j
  erw [partialDeriv_flatTorus w hw i θ, partialDeriv_flatTorus w hw j θ, dotProduct_equiv]
  have hp : (flatTorus2Metric.inner (torus2Wrap θ) :
        TangentSpace ((𝓡 1).prod (𝓡 1)) (torus2Wrap θ) →L[ℝ]
        TangentSpace ((𝓡 1).prod (𝓡 1)) (torus2Wrap θ) →L[ℝ] ℝ)
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ (Pi.single i 1))
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ (Pi.single j 1)) =
      inner ℝ
        (mfderiv ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w (torus2Wrap θ)
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ (Pi.single i 1)))
        (mfderiv ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w (torus2Wrap θ)
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓡 1).prod (𝓡 1)) torus2Wrap θ (Pi.single j 1))) :=
    hpull (torus2Wrap θ) _ _
  erw [← hp, torus2Wrap_pullback]
  simp [flatMetric, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm]

/-- **L6.** Injectivity mod `2πℤ²` for the composite: from `w` injective on `Circle × Circle`
  and `torus2Wrap_injective_mod_2pi`, plus injectivity of `EuclideanSpace.equiv`. -/
theorem flatTorus_injective_mod_2pi {q : ℕ}
    (w : Circle × Circle → EuclideanSpace ℝ (Fin q))
    (hwinj : Function.Injective w) :
    IsInjectiveMod2Pi
      (fun θ : Fin 2 → ℝ => (EuclideanSpace.equiv (Fin q) ℝ) (w (torus2Wrap θ))) := by
  intro x y hxy
  exact torus2Wrap_injective_mod_2pi x y
    (hwinj ((EuclideanSpace.equiv (Fin q) ℝ).injective hxy))

/-- **L7 (general reusable lemma).**  If `u` realizes `g` pointwise and `g x` is positive
  definite at every `x`, then the partials of `u` are linearly independent everywhere:
  a nontrivial combination `∑ᵢ cᵢ ∂ᵢu(x)` has squared norm `cᵀ · g x · c > 0`.

  Proof idea.  `Fintype.linearIndependent_iff`; a vanishing combination has vanishing
  dot-product with itself, which expands via `Realizes` into `cᵀ · g x · c`; `PosDef`
  forces `c = 0`. -/
theorem hasFullRankDeriv_of_realizes {n N : ℕ} {u : (Fin n → ℝ) → (Fin N → ℝ)}
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hreal : Realizes u g) (hpos : ∀ x, (g x).PosDef) : HasFullRankDeriv u := by
  intro x
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : c ⬝ᵥ ((g x).mulVec c) = 0 := by
    have h1 : (∑ i, c i • partialDeriv i u x) ⬝ᵥ (∑ j, c j • partialDeriv j u x) = 0 := by
      rw [hc]; simp
    rw [_root_.sum_dotProduct] at h1
    simp only [_root_.dotProduct_sum, smul_dotProduct, dotProduct_smul, hreal x,
      smul_eq_mul] at h1
    rw [dotProduct]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hc0 : c = 0 := by
    by_contra hne
    have hp := (hpos x).dotProduct_mulVec_pos hne
    simp only [star_trivial] at hp
    rw [key] at hp
    exact lt_irrefl _ hp
  intro i
  rw [hc0]
  rfl

/-- **The cross-check.**  Applying `nashCompact` to `flatTorus2Metric` and composing with the
  universal cover `ℝ² → Circle × Circle` yields an `IsInjRealizable` witness for the flat
  metric on `ℝ²` — the same conclusion that `nashTorus 2 flatMetric_isPosDefSmoothMetric`
  produces directly, via an independent path through the general-manifold machinery. -/
theorem torus2_matches_nashTorus : IsInjRealizable (flatMetric 2) := by
  obtain ⟨q, w, hw, hwinj, hwpull⟩ := nashCompact flatTorus2Metric
  set u : (Fin 2 → ℝ) → (Fin q → ℝ) :=
    fun θ => (EuclideanSpace.equiv (Fin q) ℝ) (w (torus2Wrap θ)) with hudef
  have hreal : Realizes u (flatMetric 2) := flatTorus_realizes w hw hwpull
  refine ⟨q, u, ?_, hreal⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact flatTorus_smooth w hw
  · exact flatTorus_periodic w
  · exact flatTorus_injective_mod_2pi w hwinj
  · exact hasFullRankDeriv_of_realizes hreal
      (fun x => flatMetric_isPosDefSmoothMetric.posDef x)

end CrossCheck

end NashEmbedding

end
