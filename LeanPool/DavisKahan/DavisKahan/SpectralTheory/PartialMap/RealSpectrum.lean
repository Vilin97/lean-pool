/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent

/-!
# The real resolvent of a partial map, and the ambient spectrum

`TauCeti.LinearPMap.realResolventSet` is defined without importing the ambient
spectral theory, so it remains available over every `RCLike` scalar field.  This
file identifies its complex specialization with the ambient spectrum.  The
bridge is intentionally kept above both foundations to avoid an import cycle.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Membership in the closed-operator real resolvent is exactly membership of
the real scalar in the canonical resolvent set.

The two predicates invert opposite shifts — `realResolventSet` asks for a bounded
two-sided inverse of `A - lam`, while `TauCeti.LinearPMap.resolventSet` asks for one of
`lam • I - A` — so they are *not* definitionally equal, and this was a `rfl` only while the
resolvent core used the `A - z` convention.  They do describe the same set: the two shifts
differ by a sign, and negating a bounded two-sided inverse gives a bounded two-sided inverse
of the negated map.  That negation is the whole content of the proof. -/
theorem mem_realResolventSet_iff_mem_spectraResolvent
    (A : E →ₗ.[ℂ] E) (lam : ℝ) :
    lam ∈ TauCeti.LinearPMap.realResolventSet A ↔
      (lam : ℂ) ∈ TauCeti.LinearPMap.resolventSet A := by
  rw [TauCeti.LinearPMap.mem_realResolventSet_iff, TauCeti.LinearPMap.mem_resolventSet_iff]
  constructor
  · rintro ⟨R, hleft, hright⟩
    refine ⟨-R, fun y => neg_mem (hright y).choose, fun y => ?_, fun x => ?_⟩
    · have h := (hright y).choose_spec
      have hneg : A
            (⟨(-R) y, neg_mem (hright y).choose⟩ : A.domain)
          = -(A ⟨R y, (hright y).choose⟩) :=
        _root_.LinearPMap.map_neg A ⟨R y, (hright y).choose⟩
      rw [hneg]
      simp only [_root_.neg_apply]
      linear_combination (norm := module) h
    · have h := hleft x
      have harg : (lam : ℂ) • (x : E) - A x
          = -(A x - (lam : ℂ) • (x : E)) := by module
      simp only [_root_.neg_apply, harg, map_neg, neg_neg]
      exact h
  · rintro ⟨R, hR⟩
    refine ⟨-R, fun x => ?_, fun y => ?_⟩
    · -- the scalar is abstracted so that the `RCLike` coercion of `realResolventSet` and the
      -- `ℂ` coercion of `IsResolventAt`, which are defeq but not syntactically equal, unify
      have hstep : ∀ c : ℂ, R (c • (x : E) - A x) = (x : E) →
          (-R) (A x - c • (x : E)) = (x : E) := by
        intro c hc
        have harg : A x - c • (x : E)
            = -(c • (x : E) - A x) := by module
        rw [_root_.neg_apply, harg, map_neg, hc, neg_neg]
      exact hstep _ (hR.apply_smul_sub x)
    · refine ⟨neg_mem (hR.mem_domain y), ?_⟩
      have h := hR.smul_sub_apply y
      have hneg : A
            (⟨(-R) y, neg_mem (hR.mem_domain y)⟩ : A.domain)
          = -(A ⟨R y, hR.mem_domain y⟩) :=
        _root_.LinearPMap.map_neg A ⟨R y, hR.mem_domain y⟩
      rw [hneg]
      simp only [_root_.neg_apply]
      linear_combination (norm := module) h

omit [CompleteSpace E] in
/-- The generic closed-operator real spectrum agrees with the genuine spectrum
after specializing the scalar field to `ℂ`.

Complementation of `mem_realResolventSet_iff_mem_spectraResolvent`; like it, this was a
`rfl` only under the `A - z` convention. -/
theorem realSpectrum_eq_spectraSpectrum (A : E →ₗ.[ℂ] E) :
    TauCeti.LinearPMap.realSpectrum A
      = Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A := by
  ext lam
  rw [Set.mem_preimage, TauCeti.LinearPMap.mem_spectrum_iff,
    TauCeti.LinearPMap.mem_realSpectrum_iff,
    mem_realResolventSet_iff_mem_spectraResolvent A lam]

/-! ## The spectrum of a self-adjoint operator is real

**Now proved natively, 2026-07-28.**  This lemma briefly had a canonical
statement and a proof borrowed from `Spectra.Resolvent.mem_resolventSet_of_im_ne_zero`,
because the native argument needs the `±i` deficiency-surjectivity of a
self-adjoint partial map.  That is now
`TauCeti.LinearPMap.mem_resolventSet_of_im_ne_zero` in
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean`,
proved from Mathlib's `LinearPMap` adjoint API — the estimate
`|Im z| ‖x‖ ≤ ‖(A - z)x‖`, closed range from closedness of `A`, dense range from
"no non-real eigenvalues" — so the borrowed proof and this file's last Spectra
import are both gone. -/

/-! # Real Spectrum -/

/-- **A self-adjoint partial map has real spectrum.** -/
theorem spectrum_subset_real_of_isSelfAdjoint {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) :
    TauCeti.LinearPMap.spectrum A ⊆ Complex.ofReal '' Set.univ :=
  TauCeti.LinearPMap.spectrum_subset_real hA

end DavisKahan
end TauCeti
