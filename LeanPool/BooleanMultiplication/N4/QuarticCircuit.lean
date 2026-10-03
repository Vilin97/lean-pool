/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticANF

/-!
# Circuit-facing low--low quartic exclusion

The coordinate and basis-change argument in `QuarticANF` is stated for
explicit affine-plus-rational factors.  This file removes those coordinates
from its interface and applies the result to the first useful child of the
normalized seed.  No circuit enumeration is involved.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Two low--low products with a nonzero seed quartic cannot acquire a new
target direction: if their sum is in `Aff + T`, it is already rational-low. -/
theorem lowLow_sum_mem_rationalLow_of_quartic_nonzero
    {g f : ANF 8}
    (hg : IsLowLowProduct g) (hf : IsLowLowProduct f)
    (hquartic : quarticProbeANF g ≠ 0)
    (hsum : g + f ∈ targetAmbient 8 (mulTarget 4)) :
    g + f ∈ rationalLowSpace := by
  rcases hg with ⟨u₀, v₀, hu₀, hv₀, rfl⟩
  rcases hf with ⟨u₁, v₁, hu₁, hv₁, rfl⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hu₀ with
    ⟨a₀, ell₀, α, hu₀Rep⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hv₀ with
    ⟨b₀, m₀, β, hv₀Rep⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hu₁ with
    ⟨a₁, ell₁, γ, hu₁Rep⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hv₁ with
    ⟨b₁, m₁, δ, hv₁Rep⟩
  rw [hu₀Rep, hv₀Rep] at hquartic
  rw [hu₀Rep, hv₀Rep, hu₁Rep, hv₁Rep] at hsum ⊢
  have hquartic' :
      quarticWedgeProbe (rationalTwo α) (rationalTwo β) ≠ 0 := by
    simpa only [lowProduct_quarticProjection] using hquartic
  exact lowLowProducts_mem_rationalLow_of_quartic_nonzero
    a₀ b₀ a₁ b₁ ell₀ m₀ ell₁ m₁ α β γ δ hquartic' hsum

/-- The normalized seed itself is a low--low product. -/
theorem NormalizedEight.seed_isLowLowProduct {C : Circuit 8 8}
    (h : NormalizedEight C) : IsLowLowProduct (C.gate 3) := by
  exact ⟨C.left 3, C.right 3, h.seed_left_mem_rationalLow,
    h.seed_right_mem_rationalLow, C.gate_eq 3⟩

/-- A useful first child of a normalized seed with nonzero quartic part cannot
be represented by a low--low product.  Both possible seed coefficients in the
old-state shift are handled algebraically. -/
theorem NormalizedEight.usefulSeedChild_not_lowLow
    {C : Circuit 8 8} (h : NormalizedEight C)
    (hquartic : quarticProbeANF (C.gate 3) ≠ 0)
    {target representative shift : ANF 8}
    (htarget : target ∈ targetAmbient 8 (mulTarget 4))
    (htargetOld : target ∉ circuitFlag C 4)
    (hshift : shift ∈ circuitFlag C 4)
    (htargetEq : target = shift + representative) :
    ¬ IsLowLowProduct representative := by
  intro hrepresentative
  have hlowFour : rationalLowSpace ≤ circuitFlag C 4 := by
    rw [h.wireSpace_four_eq]
    exact le_sup_left
  rcases exists_low_add_seed_of_mem_four h hshift with
    ⟨p, e, hp, hshiftEq⟩
  rcases f2_eq_zero_or_one e with rfl | rfl
  · have htargetEq' : target = p + representative := by
      simpa using htargetEq.trans (congrArg (fun z => z + representative) hshiftEq)
    have hrepresentativeAmbient :
        representative ∈ targetAmbient 8 (mulTarget 4) := by
      have htargetPlus :=
        add_mem_targetAmbient_of_mem_rationalLow htarget hp
      have heq : target + p = representative := by
        rw [htargetEq']
        simp [add_comm, add_left_comm]
      rwa [heq] at htargetPlus
    rcases hrepresentative with ⟨u, v, hu, hv, hrepresentativeEq⟩
    have hrepresentativeLow : representative ∈ rationalLowSpace := by
      rw [hrepresentativeEq]
      exact rationalLow_mul_mem_of_mem_targetAmbient hu hv
        (by simpa [hrepresentativeEq] using hrepresentativeAmbient)
    apply htargetOld
    apply hlowFour
    rw [htargetEq']
    exact Submodule.add_mem _ hp hrepresentativeLow
  · have htargetEq' :
        target = (p + C.gate 3) + representative := by
      simpa using htargetEq.trans (congrArg (fun z => z + representative) hshiftEq)
    have hcollisionAmbient :
        C.gate 3 + representative ∈ targetAmbient 8 (mulTarget 4) := by
      have htargetPlus :=
        add_mem_targetAmbient_of_mem_rationalLow htarget hp
      have heq : target + p = C.gate 3 + representative := by
        rw [htargetEq']
        calc
          ((p + C.gate 3) + representative) + p =
              (p + p) + (C.gate 3 + representative) := by ac_rfl
          _ = C.gate 3 + representative := by simp
      rwa [heq] at htargetPlus
    have hcollisionLow :
        C.gate 3 + representative ∈ rationalLowSpace :=
      lowLow_sum_mem_rationalLow_of_quartic_nonzero
        h.seed_isLowLowProduct hrepresentative hquartic hcollisionAmbient
    apply htargetOld
    apply hlowFour
    rw [htargetEq']
    simpa only [add_assoc] using Submodule.add_mem _ hp hcollisionLow

end

end N4
end UnrestrictedBooleanMul
