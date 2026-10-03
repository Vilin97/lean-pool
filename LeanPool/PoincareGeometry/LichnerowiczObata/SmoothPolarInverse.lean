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

public import LeanPool.PoincareGeometry.LichnerowiczObata.OpenRegionHomeomorph
public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothManifoldInverse
public import LeanPool.PoincareGeometry.LichnerowiczObata.SpherePolarTangent

/-! # Smooth inverses on the regular polar cylinder -/

@[expose] public noncomputable section
open TopologicalSpace
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Smooth ambient polar maps restrict smoothly to the unit angular sphere. -/
theorem contMDiffAt_sphere_polar_restriction {Φ : P × ℝ → M}
    (u : Metric.sphere (0 : P) 1) (r : ℝ)
    (hΦ : ContMDiffAt 𝓘(ℝ, P × ℝ) I ∞ Φ ((u : P), r)) :
    ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r) := by
  have hc : ContMDiffAt (𝓡 n) 𝓘(ℝ, P) ∞
      (Subtype.val : Metric.sphere (0 : P) 1 → P) u := contMDiff_coe_sphere u
  have hf : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) ∞
      (fun q : Metric.sphere (0 : P) 1 × ℝ => (q.1 : P)) (u, r) :=
    hc.comp (f := Prod.fst) (u, r) contMDiffAt_fst
  exact hΦ.comp (u, r) (hf.prodMk_space contMDiffAt_snd)

/-- A single partial homeomorphism for the full regular polar cylinder has
a smooth inverse everywhere there. The derivative assumptions refer
to the specified ambient parameter map, not to an independently chosen map. -/
theorem exists_smooth_polar_inverse
    (J : Opens ℝ) (U : Opens M)
    (Q : Metric.sphere (0 : P) 1 × J ≃ₜ U)
    (q₀ : Metric.sphere (0 : P) 1 × J) (Φ : P × ℝ → M)
    (hQ : ∀ q, (Q q : M) = Φ (q.1, q.2))
    (hDim : Module.finrank ℝ E = n + 1)
    (hSmooth : ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ J,
      ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r))
    (hjet : ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ J,
      MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ ((u : P), r) ∧
      Set.InjOn (mfderiv 𝓘(ℝ, P × ℝ) I Φ ((u : P), r))
        {q : P × ℝ | inner ℝ (u : P) q.1 = 0}) :
    ∃ e : OpenPartialHomeomorph (Metric.sphere (0 : P) 1 × ℝ) M,
      e.source = {q | q.2 ∈ J} ∧ e.target = U ∧
      (∀ q ∈ e.source, e q = Φ (q.1, q.2)) ∧
      ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ J,
        ContMDiffAt I ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ e.symm (Φ ((u : P), r)) := by
  obtain ⟨e, hsource, htarget, hforward⟩ := exists_polar_region_partialHomeomorph
    (Metric.sphere (0 : P) 1) J U Q q₀
    (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) hQ
  refine ⟨e, hsource, htarget, hforward, ?_⟩
  intro u r hr
  have hx : (u, r) ∈ e.source := by rw [hsource]; exact hr
  have he := hforward (u, r) hx
  obtain ⟨D, hD, hd⟩ := exists_sphere_polar_derivative_equiv u r hDim
    (hjet u r hr).1 (hjet u r hr).2
  apply contMDiffAt_local_inverse_of_equiv
    (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) e.symm (u, r) D hd (hSmooth u r hr)
  · rw [← he]
    exact e.symm.continuousAt (e.map_source hx)
  · rw [← he]
    exact e.left_inv hx
  · have ht : Φ ((u : P), r) ∈ e.target := by rw [← he]; exact e.map_source hx
    filter_upwards [e.open_target.mem_nhds ht] with y hy
    exact (hforward (e.symm y) (e.map_target hy)).symm.trans (e.right_inv hy)

/-- The inverse agrees with the original coordinate homeomorphism and is
smooth at every point of the open target, without choosing polar
coordinates in the conclusion. -/
theorem exists_smooth_polar_inverse_on_target
    (J : Opens ℝ) (U : Opens M)
    (Q : Metric.sphere (0 : P) 1 × J ≃ₜ U)
    (q₀ : Metric.sphere (0 : P) 1 × J) (Φ : P × ℝ → M)
    (hQ : ∀ q, (Q q : M) = Φ (q.1, q.2))
    (hDim : Module.finrank ℝ E = n + 1)
    (hSmooth : ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ J,
      ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r))
    (hjet : ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ J,
      MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ ((u : P), r) ∧
      Set.InjOn (mfderiv 𝓘(ℝ, P × ℝ) I Φ ((u : P), r))
        {q : P × ℝ | inner ℝ (u : P) q.1 = 0}) :
    ∃ e : OpenPartialHomeomorph (Metric.sphere (0 : P) 1 × ℝ) M,
      e.source = {q | q.2 ∈ J} ∧ e.target = U ∧
      (∀ q ∈ e.source, e q = Φ (q.1, q.2)) ∧
      (∀ y : U, e.symm (y : M) = ((Q.symm y).1, ((Q.symm y).2 : ℝ))) ∧
      ∀ y ∈ U, ContMDiffAt I ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ e.symm y := by
  obtain ⟨e, hs, ht, he, hd⟩ :=
    exists_smooth_polar_inverse J U Q q₀ Φ hQ hDim hSmooth hjet
  refine ⟨e, hs, ht, he, ?_, ?_⟩
  · intro y
    let q := Q.symm y
    have hq : (q.1, (q.2 : ℝ)) ∈ e.source := by
      rw [hs]
      exact q.2.property
    have hy : e (q.1, (q.2 : ℝ)) = (y : M) := by
      rw [he _ hq, ← hQ q]
      exact congrArg (fun x : U => (x : M)) (Q.apply_symm_apply y)
    rw [← hy]
    exact e.left_inv hq
  · intro y hy
    let q := Q.symm ⟨y, hy⟩
    have hq : Φ ((q.1 : P), (q.2 : ℝ)) = y := by
      rw [← hQ q]
      exact congrArg (fun x : U => (x : M)) (Q.apply_symm_apply ⟨y, hy⟩)
    rw [← hq]
    exact hd q.1 q.2 q.2.property

end LichnerowiczObata
