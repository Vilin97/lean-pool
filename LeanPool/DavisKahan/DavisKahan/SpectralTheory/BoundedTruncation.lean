/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralCutoff

/-! # Bounded Truncation -/

open TauCeti.DavisKahan.Sylvester

/-!
# Bounded truncations for the unbounded Sylvester argument

The truncation at radius `τ` is the Borel calculus of `λ · 1_{[-τ,τ]}` — the
bounded operator that agrees with `A` on the range of the cutoff `E_A([-τ,τ])`.

## Provenance

Until 2026-07-29 this was Spectra's `spectralCalculus` of the same symbol,
applied to the one-parameter unitary group of Stone's theorem, and the six
interface laws were read off that calculus.  The native replacement is
`TauCeti.LinearPMap.truncation`
(`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean`),
built from the Borel calculus of the *Cayley transform*.  Every interface law
becomes a one-liner:

* symmetry — the symbol is real;
* `eq_on_cutoff` — `truncation_eq_on_specProjection`;
* strong convergence — the truncation is `E_A([-τ,τ]) ∘ A` on the domain
  (spectral projections intertwine `A`), and the cutoffs converge strongly;
* the two form bounds — apply the semibound of `A` at the cutoff vector, which
  lies in `dom A`;
* commutation — the symbol absorbs its own indicator.
-/

open scoped InnerProductSpace Topology
open Filter

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta


universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The interval `[-τ, τ]` keeps the spectral parameter bounded by `max 0 τ`. -/
private theorem abs_le_max_zero_of_mem_Icc (τ : ℝ) :
    ∀ s ∈ Set.Icc (-τ) τ, |s| ≤ max 0 τ := fun _ hs =>
  le_trans (abs_le.mpr ⟨hs.1, hs.2⟩) (le_max_right 0 τ)

/-- The bounded truncation `A · E_A([-τ,τ])`. -/
noncomputable def spectraBoundedTruncation
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) : H →L[ℂ] H :=
  TauCeti.LinearPMap.truncation hA (Set.Icc (-τ) τ) measurableSet_Icc
    (abs_le_max_zero_of_mem_Icc τ)

/-- Bounded truncations are symmetric: the symbol is real. -/
theorem spectraBoundedTruncation_isSymmetric
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) :
    (spectraBoundedTruncation A hA τ).IsSymmetric :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
    (TauCeti.LinearPMap.isSelfAdjoint_truncation hA (Set.Icc (-τ) τ) measurableSet_Icc
      (abs_le_max_zero_of_mem_Icc τ))

/-- The truncation agrees with `A` on the cutoff range. -/
theorem spectraBoundedTruncation_eq_on_cutoff
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) (x : H) :
    ∃ hx : spectraSpectralCutoff A hA τ x ∈ A.domain,
      spectraBoundedTruncation A hA τ x = A ⟨spectraSpectralCutoff A hA τ x, hx⟩ := by
  obtain ⟨hx, hb⟩ := TauCeti.LinearPMap.truncation_eq_on_specProjection hA
    (Set.Icc (-τ) τ) measurableSet_Icc (abs_le_max_zero_of_mem_Icc τ) x
  exact ⟨hx, hb.symm⟩

/-- Bounded truncations converge strongly to `A` on its domain. -/
theorem spectraBoundedTruncation_tendsto_on_domain
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (x : A.domain) :
    Tendsto (fun τ : ℝ => spectraBoundedTruncation A hA τ (x : H)) atTop
      (𝓝 (A x)) := by
  have hval : ∀ τ : ℝ, spectraBoundedTruncation A hA τ (x : H)
      = TauCeti.LinearPMap.specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc
          (A x) := by
    intro τ
    obtain ⟨hx, hb⟩ := TauCeti.LinearPMap.truncation_eq_on_specProjection hA
      (Set.Icc (-τ) τ) measurableSet_Icc (abs_le_max_zero_of_mem_Icc τ) (x : H)
    rw [show spectraBoundedTruncation A hA τ (x : H) = A ⟨_, hx⟩ from hb.symm]
    exact TauCeti.LinearPMap.specProjection_apply_domain hA (Set.Icc (-τ) τ)
      measurableSet_Icc x
  simp only [hval]
  exact TauCeti.LinearPMap.tendsto_specProjection_Icc hA (A x)

/-- A lower semibound for `A` descends to the truncations. -/
theorem spectraBoundedTruncation_lowerBound
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) {c : ℝ} (hc : TauCeti.LinearPMap.SemiboundedBelow A c) {τ : ℝ} (x : H) :
    c * ‖spectraSpectralCutoff A hA τ x‖ ^ 2 ≤
      RCLike.re ⟪spectraBoundedTruncation A hA τ x, spectraSpectralCutoff A hA τ x⟫_ℂ := by
  obtain ⟨hx, hb⟩ := TauCeti.LinearPMap.truncation_eq_on_specProjection hA
    (Set.Icc (-τ) τ) measurableSet_Icc (abs_le_max_zero_of_mem_Icc τ) x
  rw [show spectraBoundedTruncation A hA τ x = A ⟨_, hx⟩ from hb.symm]
  exact hc ⟨spectraSpectralCutoff A hA τ x, hx⟩

/-- An upper semibound for `A` descends to the truncations. -/
theorem spectraBoundedTruncation_upperBound
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) {c : ℝ} (hc : TauCeti.LinearPMap.SemiboundedAbove A c) {τ : ℝ} (x : H) :
    RCLike.re ⟪spectraBoundedTruncation A hA τ x, spectraSpectralCutoff A hA τ x⟫_ℂ ≤
      c * ‖spectraSpectralCutoff A hA τ x‖ ^ 2 := by
  obtain ⟨hx, hb⟩ := TauCeti.LinearPMap.truncation_eq_on_specProjection hA
    (Set.Icc (-τ) τ) measurableSet_Icc (abs_le_max_zero_of_mem_Icc τ) x
  rw [show spectraBoundedTruncation A hA τ x = A ⟨_, hx⟩ from hb.symm]
  exact hc ⟨spectraSpectralCutoff A hA τ x, hx⟩

/-- The truncation absorbs its cutoff on both sides. -/
theorem spectraBoundedTruncation_commutes_cutoff
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) :
    spectraBoundedTruncation A hA τ ∘L spectraSpectralCutoff A hA τ =
        spectraBoundedTruncation A hA τ ∧
      spectraSpectralCutoff A hA τ ∘L spectraBoundedTruncation A hA τ =
        spectraBoundedTruncation A hA τ :=
  ⟨TauCeti.LinearPMap.truncation_mul_specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc
      (abs_le_max_zero_of_mem_Icc τ),
    TauCeti.LinearPMap.specProjection_mul_truncation hA (Set.Icc (-τ) τ) measurableSet_Icc
      (abs_le_max_zero_of_mem_Icc τ)⟩

/-- The implementation of the coherent bounded truncation interface. -/
noncomputable def spectraBoundedTruncationInterface
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) :
    BoundedTruncationInterface A hA
      (spectraSpectralCutoffInterface A hA) where
  truncation := spectraBoundedTruncation A hA
  isSymmetric := spectraBoundedTruncation_isSymmetric A hA
  eq_on_cutoff := spectraBoundedTruncation_eq_on_cutoff A hA
  tendsto_on_domain := spectraBoundedTruncation_tendsto_on_domain A hA
  lowerBound := by
    intro c hLower τ _ x
    exact spectraBoundedTruncation_lowerBound A hA hLower x
  upperBound := by
    intro c hUpper τ _ x
    exact spectraBoundedTruncation_upperBound A hA hUpper x
  commutes_cutoff := spectraBoundedTruncation_commutes_cutoff A hA

end ExactSinTheta
end DavisKahan
end TauCeti
