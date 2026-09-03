/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.SymmetryL2

/-!
# The `L²` inner product of symmetric elements is real

`inner_symmetric_im_eq_zero` says this for *functions*; Gram–Schmidt runs on `L²`, so the same fact
is needed for the inner product of `Lp` elements. The upgrade needs genuine measure-preservation of
`u ↦ -u` on the restricted measure, rather than an a.e. transport, because a change of variables
inside an integral is involved rather than a null-set argument.

With this, "the Gram–Schmidt coefficients are real" becomes a fact about the ambient space, which is
what lets the process stay inside `symmetricSubspace`.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ}

/-- Negation preserves Lebesgue measure restricted to the symmetric interval. -/
theorem measurePreserving_neg_Ioo (lam : ℝ) :
    MeasurePreserving (fun u : ℝ => -u) (volume.restrict (Set.Ioo (-lam) lam))
      (volume.restrict (Set.Ioo (-lam) lam)) := by
  have hpre : (fun u : ℝ => -u) ⁻¹' Set.Ioo (-lam) lam = Set.Ioo (-lam) lam := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor
    · exact fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩
    · exact fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Ioo (a := -lam) (b := lam))
  rwa [hpre] at h

/-- A reflection-invariant integral over the symmetric interval. -/
theorem integral_comp_neg_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (lam : ℝ) :
    ∫ u in Set.Ioo (-lam) lam, g (-u) = ∫ u in Set.Ioo (-lam) lam, g u :=
  (measurePreserving_neg_Ioo lam).integral_comp
    (MeasurableEquiv.neg ℝ).measurableEmbedding g

end ZetaZeros
