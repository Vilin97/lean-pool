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

public import LeanPool.PoincareGeometry.BonnetMyers.ParallelFieldContinuation

/-!
# Linear transport induced by global parallel fields

A globally continued orthonormal parallel frame should give more than a list
of vectors: it determines a genuine linear isometric equivalence between the
initial tangent fibre and every later tangent fibre.  This file builds that
map directly from the global fields.  It is the coordinate-free bridge needed
to evaluate a Ricci trace in the same moving frame used by the sine test.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicGeodesic.GlobalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- The linear isometry determined at time `s` by global parallel
continuations of an orthonormal basis. -/
noncomputable def globalParallelTransport
    {ι : Type*} [Fintype ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ s : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : Orthonormal ℝ (fun i ↦ (p i).field s)) :
    TM (curve γ t₀) →ₗᵢ[ℝ] TM (curve (shift γ t₀) s) := by
  let f : TM (curve γ t₀) →ₗ[ℝ] TM (curve (shift γ t₀) s) :=
    b.toBasis.constr ℝ (fun i ↦ (p i).field s)
  apply f.isometryOfOrthonormal (v := b.toBasis)
  · simpa only [OrthonormalBasis.coe_toBasis] using b.orthonormal
  · have hf : (f : TM (curve γ t₀) → TM (curve (shift γ t₀) s)) ∘ b.toBasis =
        fun i ↦ (p i).field s := by
      funext i
      exact b.toBasis.constr_basis ℝ (fun i ↦ (p i).field s) i
    rw [hf]
    exact horth

/-- The global transport isometry has the intended value on each initial
basis vector. -/
theorem globalParallelTransport_apply_basis
    {ι : Type*} [Fintype ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ s : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : Orthonormal ℝ (fun i ↦ (p i).field s)) (i : ι) :
    globalParallelTransport p horth (b i) = (p i).field s := by
  change (b.toBasis.constr ℝ (fun i ↦ (p i).field s)) (b i) = (p i).field s
  exact b.toBasis.constr_basis ℝ (fun i ↦ (p i).field s) i

/-- The linear isometric equivalence determined at time `s` by global
parallel continuations of an orthonormal basis. -/
noncomputable def globalParallelTransportEquiv
    {ι : Type*} [Fintype ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ s : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : Orthonormal ℝ (fun i ↦ (p i).field s)) :
    TM (curve γ t₀) ≃ₗᵢ[ℝ] TM (curve (shift γ t₀) s) := by
  let T := globalParallelTransport p horth
  have hdim : Module.finrank ℝ (TM (curve γ t₀)) =
      Module.finrank ℝ (TM (curve (shift γ t₀) s)) :=
    tangent_finrank_eq (I := I) (M := M) (curve γ t₀)
      (curve (shift γ t₀) s)
  let e : TM (curve γ t₀) ≃ₗ[ℝ] TM (curve (shift γ t₀) s) :=
    T.linearEquivOfInjective T.injective hdim
  apply e.isometryOfOrthonormal (v := b.toBasis)
  · simpa only [OrthonormalBasis.coe_toBasis] using b.orthonormal
  · have he : (e : TM (curve γ t₀) → TM (curve (shift γ t₀) s)) ∘ b.toBasis =
        fun i ↦ (p i).field s := by
      funext i
      change e (b i) = (p i).field s
      rw [show e (b i) = T.toLinearMap (b i) by
        exact LinearMap.linearEquivOfInjective_apply T.injective hdim (b i)]
      exact globalParallelTransport_apply_basis p horth i
    rw [he]
    exact horth

/-- The global transport equivalence sends each initial basis vector to its
specified global parallel continuation. -/
theorem globalParallelTransportEquiv_apply_basis
    {ι : Type*} [Fintype ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ s : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : Orthonormal ℝ (fun i ↦ (p i).field s)) (i : ι) :
    globalParallelTransportEquiv p horth (b i) = (p i).field s := by
  change globalParallelTransport p horth (b i) = (p i).field s
  exact globalParallelTransport_apply_basis p horth i

/-- The transported vectors packaged as an actual orthonormal basis of the
current tangent fibre. -/
noncomputable def globalParallelTransportBasis
    {ι : Type*} [Fintype ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ s : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : Orthonormal ℝ (fun i ↦ (p i).field s)) :
    OrthonormalBasis ι ℝ (TM (curve (shift γ t₀) s)) :=
  b.map (globalParallelTransportEquiv p horth)

@[simp] theorem globalParallelTransportBasis_apply
    {ι : Type*} [Fintype ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ s : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : Orthonormal ℝ (fun i ↦ (p i).field s)) (i : ι) :
    globalParallelTransportBasis p horth i = (p i).field s := by
  change globalParallelTransportEquiv p horth (b i) = (p i).field s
  exact globalParallelTransportEquiv_apply_basis p horth i

end IntrinsicGeodesic.GlobalGeodesic

end BonnetMyersEntry
