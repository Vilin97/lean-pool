/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothEigenfunction

/-! # Attainment of the first smooth eigenvalue and the sharp Ricci bound -/

@[expose] public noncomputable section
open Bundle Set MeasureTheory Filter AlmostSchur
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
local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance : IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by decide)

local notation "W" => (EnergyCompletion (I := I) (M := M))
local notation "J" => (energyCompletionToL2 (I := I) (M := M))
local notation "ν" => (riemannianVolume (I := I) (M := M))
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

omit [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] in
/-- A nonzero realized mean-zero energy vector cannot have a constant representative. -/
theorem representative_nonconstant {u : W} (hu : J u ≠ 0) {g : M → ℝ}
    (hga : g =ᵐ[ν] J u) : ∃ x y, g x ≠ g y := by
  classical
  by_contra h
  push Not at h
  let c : M := Classical.choice ‹Nonempty M›
  have hconst : g = fun _ => g c := funext fun x => h x c
  have hint : (∫ x, g x ∂ν) = 0 :=
    (integral_congr_ae hga).trans (integral_energyCompletionToL2 u)
  have hvol : (ν univ).toReal ≠ 0 :=
    (ENNReal.toReal_pos (riemannianVolume_finite_positive (I := I)).1.ne'
      (riemannianVolume_finite_positive (I := I)).2.ne).ne'
  rw [hconst, integral_const] at hint
  have hc : g c = 0 := by
    change (ν univ).toReal * g c = 0 at hint
    exact (mul_eq_zero.mp hint).resolve_left hvol
  have hgzero : ∀ x, g x = 0 := fun x => (h x c).trans hc
  apply hu
  apply Lp.ext
  filter_upwards [hga, Lp.coeFn_zero (ℝ) 2 ν] with x hx hz
  exact hx.symm.trans ((hgzero x).trans hz.symm)

omit [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] in
/-- A nonconstant smooth eigenfunction determines a nonzero variational
eigenvector. Mean correction does not change its energy or test pairing. -/
theorem classical_eigenfunction_variational {s : ℝ} {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (hnonconst : ∃ x y, g x ≠ g y)
    (heig : ∀ x, laplacian LC g x = -s * g x) :
    ∃ u : W, J u ≠ 0 ∧ ∀ v : W, inner ℝ u v = s * inner ℝ (J u) (J v) := by
  let hg1 : ContMDiff I 𝓘(ℝ, ℝ) 1 g := hg.of_le (by decide)
  let q := meanCorrectedEnergyTest g hg1
  let u : W := energyToCompletion q
  have hq : q ≠ 0 := by
    intro heq
    obtain ⟨x, y, hxy⟩ := hnonconst
    have hx := congrArg (fun f : EnergySpace (I := I) (M := M) => f.val x) heq
    have hy := congrArg (fun f : EnergySpace (I := I) (M := M) => f.val y) heq
    change g x - riemannianMean (I := I) g = 0 at hx
    change g y - riemannianMean (I := I) g = 0 at hy
    exact hxy (by linarith)
  refine ⟨u, ?_, ?_⟩
  · intro hz
    apply hq
    apply (energyToCompletion (I := I) (M := M)).injective
    apply energyCompletionToL2_injective (I := I) (M := M)
    simpa only [map_zero] using hz
  · intro v
    have hgreen := integral_energyCompletionToL2_mul_laplacian LC
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion v g
      (hg.of_le (by decide))
    have hi : (∫ x, J v x * laplacian LC g x ∂ν) =
        -s * (∫ x, J v x * g x ∂ν) := by
      calc
        _ = ∫ x, -s * (J v x * g x) ∂ν := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [heig]
          ring
        _ = _ := integral_const_mul _ _
    rw [hi, ← realization_inner_meanCorrected v g hg1] at hgreen
    change -s * inner ℝ (J v) (J u) = -inner ℝ v u at hgreen
    have h1 : inner ℝ u v = inner ℝ v u := real_inner_comm _ _
    have h2 : inner ℝ (J v) (J u) = inner ℝ (J u) (J v) := real_inner_comm _ _
    rw [h1]
    rw [h2] at hgreen
    linarith

/-- Attainment and minimality of the first positive classical smooth eigenvalue.
All analytic existence and regularity bridges are proved. -/
theorem exists_first_smooth_eigenvalue (hd : 0 < Module.finrank ℝ E) :
    ∃ μ : ℝ, 0 < μ ∧
      (∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧ (∃ x y, g x ≠ g y) ∧
        ∀ x, laplacian LC g x = -μ * g x) ∧
      ∀ s : ℝ, 0 < s →
        (∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧ (∃ x y, g x ≠ g y) ∧
          ∀ x, laplacian LC g x = -s * g x) → μ ≤ s := by
  obtain ⟨μ, hμ, ⟨u, hu, hvar⟩, hmin⟩ := exists_first_variational_eigenpair (I := I) (M := M) hd
  obtain ⟨g, hg, hga, heig⟩ := exists_smooth_variational_eigenfunction hvar
  refine ⟨μ, hμ, ⟨g, hg, representative_nonconstant hu hga, heig⟩, ?_⟩
  intro s hs hgs
  obtain ⟨f, hf, hn, he⟩ := hgs
  exact hmin s hs (classical_eigenfunction_variational hf hn he)

/-- Lichnerowicz's first-eigenvalue theorem, including attainment, on the
actual closed connected Riemannian manifold. Global Obata rigidity remains separate. -/
theorem exists_first_smooth_eigenvalue_with_ricci_bound
    {K : ℝ} (hd : 2 ≤ Module.finrank ℝ E)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * K * ‖v‖ ^ 2 ≤ (LC).ricciCurvature x v v) :
    ∃ μ : ℝ, 0 < μ ∧ (Module.finrank ℝ E : ℝ) * K ≤ μ ∧
      (∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧ (∃ x y, g x ≠ g y) ∧
        ∀ x, laplacian LC g x = -μ * g x) ∧
      ∀ s : ℝ, 0 < s →
        (∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧ (∃ x y, g x ≠ g y) ∧
          ∀ x, laplacian LC g x = -s * g x) → μ ≤ s := by
  obtain ⟨μ, hμ, hg, hmin⟩ := exists_first_smooth_eigenvalue (I := I) (M := M) (by omega)
  obtain ⟨g, hgs, hgn, hge⟩ := hg
  exact ⟨μ, hμ, eigenvalue_lower_bound hd hRic (hgs.of_le (by decide)) hgn hge,
    ⟨g, hgs, hgn, hge⟩, hmin⟩

end LichnerowiczObata
