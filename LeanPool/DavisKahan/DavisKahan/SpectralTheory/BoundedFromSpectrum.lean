/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.BoundedRealization
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralSupport

/-!
# Boundedness from a bounded spectrum

A closed densely defined self-adjoint operator whose spectrum lies in the
bounded interval `[β, α]` is defined on the whole space and bounded, with the
sharp centered estimate `‖A - (β+α)/2‖ ≤ (α-β)/2`.

The proof assembles three facts about the native spectral measure
`TauCeti.LinearPMap.spectralPVM`:

* `specProjection_eq_zero_of_subset_resolventSet` — the spectral projection
  vanishes off the spectrum, so `E([β,α]ᶜ) = 0`;
* `ProjValMeasure.proj_compl` — complementation gives `E([β,α]) = 1`, so every
  vector lies in the spectral range of `[β, α]`;
* `mem_domain_of_mem_specRange_of_bounded` and
  `norm_sub_smul_le_of_mem_specRange` — a bounded spectral range sits inside
  `dom A`, and there `A - c` is bounded by the radius of the set around `c`.

Until 2026-07-29 this went through Spectra: the operator was realized as the
generator of its Yosida group and the four bricks were Spectra's.  The Stone
group is not needed — the spectral measure is constructed directly from the
Cayley transform, and `A` is its own generator.

This is the missing seam for the fully unbounded interval/exterior orientation
of Davis--Kahan Theorem 5.2: the interval block of the configuration is
secretly a bounded operator.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Boundedness from a bounded spectrum.**  A closed densely defined
self-adjoint operator with spectrum contained in `[β, α]` admits a bounded
realization on the whole space, centered within distance `(α - β)/2` of the
midpoint multiple of the identity. -/
theorem exists_boundedRealization_of_spectrum_subset_Icc
    {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A)
    {β α : ℝ} (hβα : β ≤ α)
    (hσ : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A ⊆
        Set.Icc β α) :
    ∃ R : BoundedRealization (𝕜 := ℂ) (E := H) A,
      ‖R.operator - (((β + α) / 2 : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ H‖ ≤ (α - β) / 2 := by
  classical
  have hBm : MeasurableSet (Set.Icc β α) := measurableSet_Icc
  -- every point outside `[β, α]` is a resolvent point
  have hres : ∀ lam ∈ (Set.Icc β α)ᶜ,
      (lam : ℂ) ∈ TauCeti.LinearPMap.resolventSet A := by
    intro lam hlam
    by_contra hnot
    exact hlam (hσ hnot)
  -- the spectral projection of the complement vanishes
  have hprojc :
      TauCeti.LinearPMap.specProjection hA (Set.Icc β α)ᶜ hBm.compl = 0 :=
    TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet hA _
      hBm.compl hres
  -- the interval carries the full projection
  have hprojid :
      TauCeti.LinearPMap.specProjection hA (Set.Icc β α) hBm
        = ContinuousLinearMap.id ℂ H := by
    have hc := (TauCeti.LinearPMap.spectralPVM hA).proj_compl (Set.Icc β α) hBm
    rw [show (TauCeti.LinearPMap.spectralPVM hA).proj (Set.Icc β α)ᶜ hBm.compl
        = TauCeti.LinearPMap.specProjection hA (Set.Icc β α)ᶜ hBm.compl from rfl,
      hprojc] at hc
    rw [show TauCeti.LinearPMap.specProjection hA (Set.Icc β α) hBm
        = (TauCeti.LinearPMap.spectralPVM hA).proj (Set.Icc β α) hBm from rfl]
    linear_combination (norm := module) hc
  have hfix : ∀ φ : H,
      TauCeti.LinearPMap.specProjection hA (Set.Icc β α) hBm φ = φ := by
    intro φ; rw [hprojid]; rfl
  have hrange : ∀ φ : H,
      φ ∈ TauCeti.LinearPMap.specRange hA (Set.Icc β α) hBm := fun φ =>
    (TauCeti.LinearPMap.mem_specRange_iff hA _ hBm φ).mpr (hfix φ)
  -- absolute and centered bounds on the interval
  have hbnd : ∀ s ∈ Set.Icc β α, |s| ≤ max |β| |α| := by
    intro s hs
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · exact le_trans
        (le_trans (neg_le_neg (le_max_left |β| |α|)) (neg_abs_le β)) hs.1
    · exact le_trans hs.2 (le_trans (le_abs_self α) (le_max_right |β| |α|))
  have hcr : ∀ s ∈ Set.Icc β α, |s - (β + α) / 2| ≤ (α - β) / 2 := by
    intro s hs
    rw [abs_le]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- every vector lies in the domain, with the centered pointwise estimate
  have hdomAll : ∀ φ : H, φ ∈ A.domain := fun φ =>
    TauCeti.LinearPMap.mem_domain_of_mem_specRange_of_bounded hA _ hBm hbnd
      (hrange φ)
  have hbound : ∀ φ : H,
      ‖A ⟨φ, hdomAll φ⟩ - (((β + α) / 2 : ℝ) : ℂ) • φ‖
        ≤ (α - β) / 2 * ‖φ‖ := fun φ =>
    TauCeti.LinearPMap.norm_sub_smul_le_of_mem_specRange hA _ hBm hbnd
      (by linarith) hcr (hrange φ) (hdomAll φ)
  -- the everywhere-defined linear realization
  let g : H →ₗ[ℂ] H :=
    { toFun := fun φ => A ⟨φ, hdomAll φ⟩
      map_add' := fun φ ψ => by
        have h : (⟨φ + ψ, hdomAll (φ + ψ)⟩ : A.domain) =
            ⟨φ, hdomAll φ⟩ + ⟨ψ, hdomAll ψ⟩ := rfl
        rw [h, A.map_add]
      map_smul' := fun c φ => by
        have h : (⟨c • φ, hdomAll (c • φ)⟩ : A.domain) =
            c • ⟨φ, hdomAll φ⟩ := rfl
        rw [h, A.map_smul]
        rfl }
  have hgφ : ∀ φ : H, g φ = A ⟨φ, hdomAll φ⟩ := fun _ => rfl
  have hsm : ∀ φ : H, (((β + α) / 2 : ℝ) : ℂ) • φ = ((β + α) / 2 : ℝ) • φ :=
    fun φ => (RCLike.real_smul_eq_coe_smul (K := ℂ) _ φ).symm
  -- continuity of the realization
  have hgbound : ∀ φ : H,
      ‖g φ‖ ≤ (|(β + α) / 2| + (α - β) / 2) * ‖φ‖ := by
    intro φ
    have h := hbound φ
    rw [← hgφ φ, hsm φ] at h
    have h2 : ‖((β + α) / 2 : ℝ) • φ‖ = |(β + α) / 2| * ‖φ‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    calc ‖g φ‖
        = ‖(g φ - ((β + α) / 2 : ℝ) • φ) + ((β + α) / 2 : ℝ) • φ‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖g φ - ((β + α) / 2 : ℝ) • φ‖ + ‖((β + α) / 2 : ℝ) • φ‖ :=
          norm_add_le _ _
      _ ≤ (α - β) / 2 * ‖φ‖ + |(β + α) / 2| * ‖φ‖ := by
          rw [h2]; exact add_le_add h le_rfl
      _ = (|(β + α) / 2| + (α - β) / 2) * ‖φ‖ := by ring
  let T : H →L[ℂ] H := g.mkContinuous _ hgbound
  have hTφ : ∀ φ : H, T φ = A ⟨φ, hdomAll φ⟩ := fun _ => rfl
  refine ⟨⟨T, ?_, ?_⟩, ?_⟩
  · -- the domain is everything
    exact Submodule.eq_top_iff'.mpr hdomAll
  · -- the realization agrees with `A` on the domain
    intro x
    rw [hTφ (x : H)]
  · -- the centered norm bound
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun φ => ?_
    have h := hbound φ
    rw [← hTφ φ, hsm φ] at h
    calc ‖(T - (((β + α) / 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ H) φ‖
        = ‖T φ - ((β + α) / 2 : ℝ) • φ‖ := by
          rw [sub_apply, smul_apply,
            ContinuousLinearMap.id_apply, hsm φ]
      _ ≤ (α - β) / 2 * ‖φ‖ := h

end ExactSinTheta
end DavisKahan
end TauCeti
