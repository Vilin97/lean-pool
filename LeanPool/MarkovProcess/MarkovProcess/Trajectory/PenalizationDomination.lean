/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FeynmanKacRealResolvent

/-!
# Penalization domination for killed resolvents

A resolvent family preserving measurable bounded functions, satisfying the resolvent identity,
and solving the same bounded-potential perturbation equation as the real Feynman--Kac resolvent
dominates the killed resolvent of every open set on which the potential vanishes. The process-side
inputs are conservativity, the Feller property, and Kolmogorov regularity on a locally compact
Polish space.

Main result: `IsFellerKernelSemigroup.killedResolvent_le_of_perturbed_resolventFamily`.
-/

noncomputable section PortComputability

open MeasureTheory Set
open scoped ENNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- A real resolvent family satisfying the kernel-resolvent perturbation identity for a bounded
nonnegative potential dominates the killed resolvent on every open set where that potential
vanishes. On the process side this requires conservativity, the Feller property, and Kolmogorov
regularity. The comparison family preserves measurability and boundedness, satisfies the
resolvent identity, and obeys the large-shift perturbation equation. -/
theorem IsFellerKernelSemigroup.killedResolvent_le_of_perturbed_resolventFamily
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {q : alpha → ℝ} (hq : Measurable q)
    (hqU : ∀ y ∈ U, q y = 0) {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (Y : ℝ → (alpha → ℝ) → alpha → ℝ)
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hY_perturbation : ∀ {lam : ℝ}, C < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y lam f = P.kernelResolventReal lam f -
        P.kernelResolventReal lam (fun y ↦ q y * Y lam f y))
    {f : alpha → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam (fun y ↦ ENNReal.ofReal (f y)) x ≤
      ENNReal.ofReal (Y lam f x) := by
  have hEq : IsConservative.feynmanKacResolventReal P hP q lam f = Y lam f := by
    apply MarkovProcess.perturbed_eq_of_resolventFamilies
      (fun mu ↦ P.kernelResolventReal mu)
      (fun mu ↦ IsConservative.feynmanKacResolventReal P hP q mu) Y
    · intro mu _hCmu hmu g k hgm hgk hgmBound hgkBound
      obtain ⟨E, hgE⟩ := hgmBound
      obtain ⟨F, hkF⟩ := hgkBound
      exact P.kernelResolventReal_add hmu hgm hgk hgE hkF
    · intro mu _hCmu hmu g hg E hgE
      exact P.norm_kernelResolventReal_le hmu hgE
    · exact hq
    · exact hq0
    · exact hqC
    · intro mu hmu g k hgm hgk hgmBound hgkBound
      obtain ⟨E, hgE⟩ := hgmBound
      obtain ⟨F, hkF⟩ := hgkBound
      exact IsConservative.feynmanKacResolventReal_add P hP hq hq0 hmu hgm hgk hgE hkF
    · intro mu _hmu g hg _hgb
      exact IsConservative.measurable_feynmanKacResolventReal P hP hq mu hg
    · exact hY_meas
    · intro mu hmu g _hg E hgE
      exact IsConservative.norm_feynmanKacResolventReal_le P hP hq0 hmu hgE
    · exact hY_bound
    · intro mu nu hmu hnu g hg hgb
      obtain ⟨E, hgE⟩ := hgb
      exact hFeller.feynmanKacResolventReal_resolvent_identity
        P hP hK hq hq0 hqC hmu hnu hg hgE
    · exact hY_resolvent
    · intro mu _hCmu hmu g hg hgb
      obtain ⟨E, hgE⟩ := hgb
      exact hFeller.feynmanKacResolventReal_perturbation
        P hP hK hq hq0 hqC hmu hg hgE
    · intro mu hCmu _hmu
      exact hY_perturbation hCmu
    · exact hlam
    · exact hf
    · exact hfD
  calc
    IsConservative.killedResolvent P hP U hU lam
        (fun y ↦ ENNReal.ofReal (f y)) x ≤
        IsConservative.feynmanKacResolvent P hP q lam
          (fun y ↦ ENNReal.ofReal (f y)) x :=
      IsConservative.killedResolvent_le_feynmanKacResolvent
        P hP hq hU hqU lam hf.ennreal_ofReal x
    _ = ENNReal.ofReal (IsConservative.feynmanKacResolventReal P hP q lam f x) :=
      (IsConservative.ofReal_feynmanKacResolventReal_eq_feynmanKacResolvent
        P hP hq hq0 hlam hf hf0 hfD x).symm
    _ = ENNReal.ofReal (Y lam f x) := by rw [hEq]

end

end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
