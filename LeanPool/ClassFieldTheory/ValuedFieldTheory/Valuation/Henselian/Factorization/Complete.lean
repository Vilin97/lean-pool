/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Assembly
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.PrincipalAdicCompleteness
/-!
# Hensel's lemma over a complete valued field

This file supplies the explicit endpoint from completeness and
nonarchimedeanness, using the principal element selected from the finitely many
initial error coefficients in the proof core.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- Hensel's lemma in the complete
nonarchimedean-valued-field setting.  A primitive polynomial over the
valuation ring whose reduction is a product of coprime factors lifts to a
factorization with the prescribed reductions and with the degree of the left
factor unchanged. -/
theorem henselFactorization_complete_exists_factorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {f : (absoluteValueValuationSubring v hnonarch)[X]}
    {gbar hbar : (IsLocalRing.ResidueField
      (absoluteValueValuationSubring v hnonarch))[X]}
    (hprim : f.map (IsLocalRing.residue
      (absoluteValueValuationSubring v hnonarch)) ≠ 0)
    (hfbar : f.map (IsLocalRing.residue
      (absoluteValueValuationSubring v hnonarch)) =
        gbar * hbar)
    (hcop : IsCoprime gbar hbar) :
    ∃ G H :
        (absoluteValueValuationSubring v hnonarch)[X],
      f = G * H ∧
        G.natDegree = gbar.natDegree ∧
          G.map (IsLocalRing.residue
            (absoluteValueValuationSubring v hnonarch)) =
              gbar ∧
            H.map (IsLocalRing.residue
              (absoluteValueValuationSubring v hnonarch)) =
                hbar := by
  let V := absoluteValueValuationSubring v hnonarch
  let hpre :
      ∀ π : V, π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V →
        IsPrecomplete (Ideal.span ({π} : Set V)) V := by
    intro π hπne hπmem
    exact principalPrecomplete_of_complete
      v hcomplete hnonarch hπne hπmem
  let hhaus :
      ∀ π : V, π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V →
        IsHausdorff (Ideal.span ({π} : Set V)) V := by
    intro π hπne hπmem
    exact principalHausdorff_of_nonzero_mem_maximalIdeal
      v hnonarch hπne hπmem
  rcases
      henselFactorization_exists_limit_factorization_of_residual_factors_valuationRing_principal
        (R := V) hpre hhaus
        (f := f) (gbar := gbar) (hbar := hbar)
        hprim hfbar hcop with
    ⟨G, H, hGdegree, _hHle, hfactor, hGmap, hHmap⟩
  exact ⟨G, H, hfactor, hGdegree, hGmap, hHmap⟩

end Valuations
end AlgebraicNumberTheory

end
