/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.PuncturedManifoldConnected
public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataCriticalIsolation

/-! # Connectedness of the Obata regular region -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The conserved-energy identity identifies the open regular region
exactly with the complement of the critical set. -/
theorem obata_regular_eq_compl_critical {K a : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hb : ∀ x, -a ≤ f x ∧ f x ≤ a)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2)) :
    {x : M | -a < f x ∧ f x < a} = {x : M | gradient (I := I) f x = 0}ᶜ := by
  ext x
  change (-a < f x ∧ f x < a) ↔ gradient (I := I) f x ≠ 0
  constructor
  · intro hx hz
    have he := hn x
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
    have hp : 0 < K * (a ^ 2 - f x ^ 2) := mul_pos hK (by nlinarith [hx.1, hx.2])
    linarith
  · intro hx
    have hp : 0 < ‖gradient (I := I) f x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    have he := hn x
    constructor
    · by_contra h
      have hf : f x = -a := le_antisymm (le_of_not_gt h) (hb x).1
      rw [hf] at he
      nlinarith
    · by_contra h
      have hf : f x = a := le_antisymm (hb x).2 (le_of_not_gt h)
      rw [hf] at he
      nlinarith

/-- In dimension at least two, the regular region of a nonconstant compact
Obata function is dense and preconnected. -/
theorem obata_regular_dense_preconnected [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    (hdim : 1 < Module.rank ℝ E) {K a : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w)
    (hb : ∀ x, -a ≤ f x ∧ f x ≤ a)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2)) :
    Dense {x : M | -a < f x ∧ f x < a} ∧ IsPreconnected {x : M | -a < f x ∧ f x < a} := by
  rw [obata_regular_eq_compl_critical hK hb hn]
  exact finite_compl_manifold_preconnected (I := I) hdim (finite_obata_critical_set hK hf hnon hH)

end LichnerowiczObata
