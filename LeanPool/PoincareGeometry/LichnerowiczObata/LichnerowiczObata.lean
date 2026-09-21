/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ClassicalSpectrum
public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataRoundDiffeomorph
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundSphereConverse
public import LeanPool.PoincareGeometry.LichnerowiczObata.StandardRoundDiffeomorph

/-! # Lichnerowicz--Obata: attainment, sharp bound, and round-sphere rigidity

The round metric is specified intrinsically by a smooth diffeomorphism whose
radius-scaled ambient inclusion preserves the tangent inner products. The
target uses Mathlib's standard sphere charts in Euclidean `(n+1)`-space.
-/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
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
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩
local instance : IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by decide)

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))
local notation "n" => (Module.finrank ℝ E)
local notation "A" => (EuclideanSpace ℝ (Fin (n + 1)))

/-- On a closed connected smooth Riemannian manifold of dimension `n ≥ 2`
with `Ric ≥ (n-1)K` and `K > 0`, the first positive smooth eigenvalue exists,
is at least `nK`, and equals `nK` exactly when the manifold is smoothly
isometric to the round sphere of radius `1 / sqrt K`.

The eigenfunction, minimality, smooth inverse, global metric identity, and
both directions of rigidity are conclusions, not auxiliary assumptions. -/
theorem lichnerowicz_obata
    (hdim : 2 ≤ n) {K : ℝ} (hK : 0 < K)
    (hRic : ∀ (x : M) (v : TM x),
      ((n : ℝ) - 1) * K * ‖v‖ ^ 2 ≤ (LC).ricciCurvature x v v) :
    ∃ μ : ℝ, 0 < μ ∧ (n : ℝ) * K ≤ μ ∧
      (∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ (∃ x y, f x ≠ f y) ∧
        ∀ x, laplacian LC f x = -μ * f x) ∧
      (∀ s : ℝ, 0 < s →
        (∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ (∃ x y, f x ≠ f y) ∧
          ∀ x, laplacian LC f x = -s * f x) → μ ≤ s) ∧
      (μ = (n : ℝ) * K ↔
        ∃ d : M ≃ₘ⟮I, 𝓡 n⟯ Metric.sphere (0 : A) 1,
          ∀ (x : M) (v w : TM x),
            inner ℝ (mvfderiv I (fun y : M => (1 / Real.sqrt K) • (d y : A)) x v)
              (mvfderiv I (fun y : M => (1 / Real.sqrt K) • (d y : A)) x w) = inner ℝ v w) := by
  obtain ⟨μ, hμ, hbound, heigen, hmin⟩ := exists_first_smooth_eigenvalue_with_ricci_bound hdim hRic
  refine ⟨μ, hμ, hbound, heigen, hmin, ?_⟩
  constructor
  · intro heq
    obtain ⟨f, hf, hn, hfμ⟩ := heigen
    rw [heq] at hfμ
    obtain ⟨p, hA, hd⟩ := extremal_eigenfunction_round_metric_diffeomorph hdim hK hRic hf hn hfμ
    let : Fact (Module.finrank ℝ (RoundAmbient (TM p)) = n + 1) := ⟨hA⟩
    let : FiniteDimensional ℝ (TM p) := inferInstanceAs (FiniteDimensional ℝ E)
    obtain ⟨d, hm⟩ := hd
    exact exists_standard_round_metric_diffeomorph d hm
  · rintro ⟨d, hm⟩
    let : Fact (Module.finrank ℝ A = n + 1) := ⟨by simp⟩
    obtain ⟨f, hf, hn, _, hfK⟩ := round_metric_diffeomorph_exists_extremal_eigenfunction hK d hm
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact le_antisymm (hmin ((n : ℝ) * K) (mul_pos hnpos hK) ⟨f, hf, hn, hfK⟩) hbound

end LichnerowiczObata
