/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck
public import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.TimeDependentGram
/-!
# The intrinsic DeTurck vector field is the metric-raised gauge field

This internal file records the single pointwise identity connecting the two coordinate
descriptions of the intrinsic DeTurck gauge vector field:

- `intrinsicDeTurckVectorField g background t x`, defined by raising the traced DeTurck one-form
  through the time-slice metric via the Riesz map `CovariantDerivative.rieszMap` (the
  `RiemannianBundle` path), and
- `raisedGaugeField (g t) (intrinsicDeTurckOneForm g background t) bas x`, the coordinate-free
  metric-raised gauge field of `PoincareCurvature.ParametrizedInner` (the `VectorBundle` path)
  consumed by the compact-manifold gauge-flow raising capstone.

Both are the unique metric dual `♯` of the same one-form `intrinsicDeTurckOneForm g background t`, so
they coincide.  The identity is proved through the uniqueness characterisation
`raisedGaugeField_eq_of_forall_inner_eq`, which lets the metric-dual side be *produced* by the lemma
(so the two tangent-bundle instance paths — `rieszMap`'s `RiemannianBundle` and `raisedGaugeField`'s
`FiberBundle`/`VectorBundle` — never have to be reconciled by `isDefEq` inside a single subterm).  The
only remaining obligation is the pointwise pairing `(g t).inner x (rieszMap x ω) w = ω w`, which is the
defining Riesz identity `rieszMap_apply_inner` under `letI : RiemannianBundle TM := ⟨(g t).…⟩`.

This is the pointwise bridge (the later-30 `NEXT`) that turns the raising capstone's flow of
`raisedGaugeField (g t) (intrinsicDeTurckOneForm …) bas` into the flow of the genuine DeTurck vector
field.  It is proof-bearing preparatory infrastructure only; it does not complete roadmap point 4.
-/

@[expose] public section

@[expose] noncomputable section

open Bundle CovariantDerivative
open scoped Manifold ContDiff Topology
open PoincareCurvature.ParametrizedInner

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
attribute [local irreducible] raisedGaugeField in
/-- **The intrinsic DeTurck vector field is the metric-raised gauge field.**  At every point `x`,
raising the traced intrinsic DeTurck one-form through the time-`t` metric via the Riesz map coincides
with the coordinate-free metric-raised gauge field `raisedGaugeField (g t) (intrinsicDeTurckOneForm …)`
computed via the canonical trivialization and model basis `bas`.  Both are the unique metric dual of
`intrinsicDeTurckOneForm g background t`, identified through `raisedGaugeField_eq_of_forall_inner_eq`.

The pointwise metric-pairing obligation `(g t).inner x (rieszMap x ω) w = ω w` is proved first, in the
Riesz-map (`RiemannianBundle`) instance world with no `raisedGaugeField` present, so the two
tangent-bundle instance paths are never reconciled by `isDefEq` inside one subterm.  Feeding it to the
uniqueness lemma then *produces* the metric-dual identity. -/
theorem intrinsicDeTurckVectorField_eq_raisedGaugeField
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (x : M) :
    intrinsicDeTurckVectorField (I := I) (M := M) g background t x
      = @raisedGaugeField E _ _ H _ I 2 M _ _ E _ _ (TangentSpace I : M → Type _)
          (by exact inferInstance)
          (fun _ => by exact inferInstance)
          (fun _ => by exact inferInstance)
          (by exact TangentSpace.fiberBundle) (by exact TangentSpace.vectorBundle)
          (g t) (intrinsicDeTurckOneForm (I := I) (M := M) g background t) _ _ _ bas x := by
  have hv : ∀ w : TangentSpace I x,
      (g t).inner x (intrinsicDeTurckVectorField (I := I) (M := M) g background t x) w
        = intrinsicDeTurckOneForm (I := I) (M := M) g background t x w := by
    intro w
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    change inner ℝ
        (rieszMap (I := I) x (intrinsicDeTurckOneForm (I := I) (M := M) g background t x)) w
      = intrinsicDeTurckOneForm (I := I) (M := M) g background t x w
    exact rieszMap_apply_inner (I := I) x
      (intrinsicDeTurckOneForm (I := I) (M := M) g background t x) w
  exact @raisedGaugeField_eq_of_forall_inner_eq E _ _ H _ I 2 M _ _ E _ _
      (TangentSpace I : M → Type _)
      (by exact inferInstance)
      (fun _ => by exact inferInstance)
      (fun _ => by exact inferInstance)
      (by exact TangentSpace.fiberBundle) (by exact TangentSpace.vectorBundle)
      (g t) (intrinsicDeTurckOneForm (I := I) (M := M) g background t) _ _ _ bas x _ hv
attribute [local irreducible] raisedGaugeField in
/-- **The reverse (DeTurck gauge) vector field is the metric dual of the negated one-form.**  The
reverse intrinsic DeTurck gauge field `intrinsicDeTurckGaugeField g background t x =
-intrinsicDeTurckVectorField g background t x` (the field that drives the intrinsic DeTurck pullback
gauge) equals the coordinate-free metric-raised gauge field of the *negated* traced DeTurck one-form,
`raisedGaugeField (g t) (-intrinsicDeTurckOneForm g background t) bas x`.  This is
`intrinsicDeTurckVectorField_eq_raisedGaugeField` composed with `raisedGaugeField_neg` (the metric dual
is linear, so it negates with the one-form). -/
theorem neg_intrinsicDeTurckVectorField_eq_raisedGaugeField_neg
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (x : M) :
    -intrinsicDeTurckVectorField (I := I) (M := M) g background t x
      = @raisedGaugeField E _ _ H _ I 2 M _ _ E _ _ (TangentSpace I : M → Type _)
          (by exact inferInstance)
          (fun _ => by exact inferInstance)
          (fun _ => by exact inferInstance)
          (by exact TangentSpace.fiberBundle) (by exact TangentSpace.vectorBundle)
          (g t) (-intrinsicDeTurckOneForm (I := I) (M := M) g background t) _ _ _ bas x := by
  rw [intrinsicDeTurckVectorField_eq_raisedGaugeField g background t bas x]
  exact (@raisedGaugeField_neg E _ _ H _ I 2 M _ _ E _ _ (TangentSpace I : M → Type _)
    (by exact inferInstance)
    (fun _ => by exact inferInstance)
    (fun _ => by exact inferInstance)
    (by exact TangentSpace.fiberBundle) (by exact TangentSpace.vectorBundle)
    (g t) (intrinsicDeTurckOneForm (I := I) (M := M) g background t) _ _ _ bas x).symm
attribute [local irreducible] raisedGaugeField in
/-- **Smoothness-class-general form of the reverse DeTurck gauge-field identity.**  For a `C²` metric
family `g` (a `MetricFamily`) and *any* `C^m` metric family `g'` inducing the same fibre inner product
(`(g t).inner y v w = (g' t).inner y v w`), the reverse intrinsic DeTurck gauge field
`-intrinsicDeTurckVectorField g background t x` equals the metric-raised gauge field of the negated
DeTurck one-form computed with the `C^m` metric `g' t`, `raisedGaugeField (g' t) (-…) bas x`.

Proof: `neg_intrinsicDeTurckVectorField_eq_raisedGaugeField_neg` (the `C²` identity) composed with
`raisedGaugeField_congr_inner` (the metric-raised gauge field depends only on the inner product, not the
smoothness class).  Taking `m := ∞` this rewrites the reverse DeTurck gauge field as the raised field of
a `C^∞` metric — exactly the `ℝ → ContMDiffRiemannianMetric I ∞` shape consumed by the compact-manifold
gauge-flow raising capstone `exists_gaugeFlow_Ioo_of_timeDependent_raisingData` — closing the
`n = 2` ↔ `n = ∞` metric-regularity step of the smoothness-ladder reconciliation.  The `local
irreducible raisedGaugeField` keeps the final `.trans` from `whnf`-unfolding the local-frame/Gram-inverse
sum and looping on the tangent-bundle fibre-instance mismatch (the later-33 diamond technique). -/
theorem neg_intrinsicDeTurckVectorField_eq_raisedGaugeField_neg_of_inner_eq
    {m : WithTop ℕ∞} [ContMDiffVectorBundle m E (TangentSpace I : M → Type _) I]
    (g : MetricFamily (I := I) (M := M))
    (g' : ℝ → Bundle.ContMDiffRiemannianMetric I m E (TangentSpace I : M → Type _))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hinner : ∀ (y : M) (v w : TangentSpace I y), (g t).inner y v w = (g' t).inner y v w)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (x : M) :
    -intrinsicDeTurckVectorField (I := I) (M := M) g background t x
      = @raisedGaugeField E _ _ H _ I m M _ _ E _ _ (TangentSpace I : M → Type _)
          (by exact inferInstance)
          (fun _ => by exact inferInstance)
          (fun _ => by exact inferInstance)
          (by exact TangentSpace.fiberBundle) (by exact TangentSpace.vectorBundle)
          (g' t) (-intrinsicDeTurckOneForm (I := I) (M := M) g background t) _ _ _ bas x := by
  refine (neg_intrinsicDeTurckVectorField_eq_raisedGaugeField_neg g background t bas x).trans ?_
  exact @raisedGaugeField_congr_inner E _ _ H _ I 2 M _ _ E _ _
    (TangentSpace I : M → Type _)
    (by exact inferInstance)
    (fun _ => by exact inferInstance)
    (fun _ => by exact inferInstance)
    (by exact TangentSpace.fiberBundle) (by exact TangentSpace.vectorBundle)
    m ‹ContMDiffVectorBundle m E (TangentSpace I : M → Type _) I›
    (g t) (g' t) hinner
    (-intrinsicDeTurckOneForm (I := I) (M := M) g background t) _ _ _ bas x

end RicciFlow
