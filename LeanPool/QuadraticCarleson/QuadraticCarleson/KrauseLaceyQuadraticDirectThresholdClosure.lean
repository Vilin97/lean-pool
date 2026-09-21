/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectPositivePairing
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectExceptional

/-!
# Threshold closure for the direct quadratic action

This module keeps the ambient selected family `S` fixed while an output
family is split into regular and exceptional intervals. Its first results
are exact finite union identities for the genuine offset tail. The final
interface records the author's threshold argument: the low term is supplied
by the boxed fixed-offset `L²` estimate, while the high term is supplied by
the positive pairing estimate and maximal-exceptional packing.

No standard/nonstandard decomposition is used here.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectThresholdClosure

open KrauseLaceyQuadraticDirectAction
open KrauseLaceyQuadraticDirectPositivePairing


noncomputable
section

/-- Classical equality for interval indices in the threshold decomposition. -/
local instance : DecidableEq RealInterval := Classical.decEq _

/-- A fixed partial action is additive over disjoint output
subcollections; the grouped inputs remain those formed from the ambient
family `S`. -/
theorem offsetLocalizedActionOn_union
    (S L E : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell s : ℤ) (hLE : Disjoint L E) :
    offsetLocalizedActionOn S (L ∪ E) scale f ell s =
      offsetLocalizedActionOn S L scale f ell s +
        offsetLocalizedActionOn S E scale f ell s := by
  classical
  funext x
  unfold offsetLocalizedActionOn
  rw [Finset.filter_union]
  exact Finset.sum_union (Finset.disjoint_filter_filter hLE)

/-- The genuine maximal offset tail is subadditive over disjoint output
subcollections. -/
theorem offsetTailMaximalOn_union_le
    (S L E : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell₀ s : ℤ) (hLE : Disjoint L E) (x : ℝ) :
    offsetTailMaximalOn S (L ∪ E) scale f ell₀ s x ≤
      offsetTailMaximalOn S L scale f ell₀ s x +
        offsetTailMaximalOn S E scale f ell₀ s x := by
  unfold offsetTailMaximalOn
  apply iSup_le
  rintro ⟨ell, hell⟩
  rw [offsetLocalizedActionOn_union S L E scale f ell s hLE]
  calc
    ‖offsetLocalizedActionOn S L scale f ell s x +
        offsetLocalizedActionOn S E scale f ell s x‖ₑ ≤
        ‖offsetLocalizedActionOn S L scale f ell s x‖ₑ +
          ‖offsetLocalizedActionOn S E scale f ell s x‖ₑ := enorm_add_le _ _
    _ ≤ offsetTailMaximalOn S L scale f ell₀ s x +
          offsetTailMaximalOn S E scale f ell₀ s x := by
      exact add_le_add
        (le_iSup (fun q : {q : ℤ // ell₀ ≤ q} ↦
          ‖offsetLocalizedActionOn S L scale f q.1 s x‖ₑ) ⟨ell, hell⟩)
        (le_iSup (fun q : {q : ℤ // ell₀ ≤ q} ↦
          ‖offsetLocalizedActionOn S E scale f q.1 s x‖ₑ) ⟨ell, hell⟩)

/-- The positive pairing inherits the union subadditivity. Only
measurability of the exceptional summand is needed to split its lintegral. -/
theorem lintegral_offsetTailMaximalOn_union_le
    (S L E : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell₀ s : ℤ) (h : ℝ → ℂ) (hLE : Disjoint L E)
    (hE : AEMeasurable (fun x ↦
      offsetTailMaximalOn S E scale f ell₀ s x * ‖h x‖ₑ) volume) :
    (∫⁻ x, offsetTailMaximalOn S (L ∪ E) scale f ell₀ s x * ‖h x‖ₑ) ≤
      (∫⁻ x, offsetTailMaximalOn S L scale f ell₀ s x * ‖h x‖ₑ) +
        ∫⁻ x, offsetTailMaximalOn S E scale f ell₀ s x * ‖h x‖ₑ := by
  calc
    (∫⁻ x, offsetTailMaximalOn S (L ∪ E) scale f ell₀ s x * ‖h x‖ₑ) ≤
        ∫⁻ x, offsetTailMaximalOn S L scale f ell₀ s x * ‖h x‖ₑ +
          offsetTailMaximalOn S E scale f ell₀ s x * ‖h x‖ₑ := by
      apply lintegral_mono
      intro x
      calc
        offsetTailMaximalOn S (L ∪ E) scale f ell₀ s x * ‖h x‖ₑ ≤
            (offsetTailMaximalOn S L scale f ell₀ s x +
              offsetTailMaximalOn S E scale f ell₀ s x) * ‖h x‖ₑ :=
          mul_le_mul' (offsetTailMaximalOn_union_le S L E scale f ell₀ s hLE x) le_rfl
        _ = offsetTailMaximalOn S L scale f ell₀ s x * ‖h x‖ₑ +
            offsetTailMaximalOn S E scale f ell₀ s x * ‖h x‖ₑ := by ring
    _ = _ := by
      simpa only using
        (lintegral_add_right' (μ := volume)
          (fun x ↦ offsetTailMaximalOn S L scale f ell₀ s x * ‖h x‖ₑ) hE)

/-- The regular/exceptions split supplies the disjointness required by the
preceding union lemmas. -/
theorem directRegular_disjoint_exceptional
    (S : Finset RealInterval) (g : ℝ → ℂ) (p Λ : ℝ) :
    Disjoint (directRegularIntervals S g p Λ)
      (directExceptionalIntervals S g p Λ) := by
  unfold directRegularIntervals
  exact Finset.sdiff_disjoint

/-- Exact direct threshold subadditivity, specialized to the author's
regular/exceptional output partition. -/
theorem lintegral_offsetTailMaximalOn_directRegular_exceptional_le
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f g : ℝ → ℂ)
    (p Λ : ℝ) (ell₀ s : ℤ)
    (hE : AEMeasurable (fun x ↦ offsetTailMaximalOn S
      (directExceptionalIntervals S g p Λ) scale f ell₀ s x * ‖g x‖ₑ) volume) :
    (∫⁻ x, offsetTailMaximalOn S S scale f ell₀ s x * ‖g x‖ₑ) ≤
      (∫⁻ x, offsetTailMaximalOn S
        (directRegularIntervals S g p Λ) scale f ell₀ s x * ‖g x‖ₑ) +
        ∫⁻ x, offsetTailMaximalOn S
          (directExceptionalIntervals S g p Λ) scale f ell₀ s x * ‖g x‖ₑ := by
  have htail (x : ℝ) :
      offsetTailMaximalOn S S scale f ell₀ s x =
        offsetTailMaximalOn S
          (directRegularIntervals S g p Λ ∪ directExceptionalIntervals S g p Λ)
          scale f ell₀ s x := by
    congr 1
    exact (directRegular_union_exceptional S g p Λ).symm
  calc
    (∫⁻ x, offsetTailMaximalOn S S scale f ell₀ s x * ‖g x‖ₑ) =
        ∫⁻ x, offsetTailMaximalOn S
          (directRegularIntervals S g p Λ ∪ directExceptionalIntervals S g p Λ)
          scale f ell₀ s x * ‖g x‖ₑ := by
      apply lintegral_congr
      intro x
      rw [htail x]
    _ ≤ _ := lintegral_offsetTailMaximalOn_union_le S
      (directRegularIntervals S g p Λ) (directExceptionalIntervals S g p Λ)
      scale f ell₀ s g (directRegular_disjoint_exceptional S g p Λ) hE

/-- The high half of the direct threshold proof, now directly instantiated
with the concrete positive pairing estimate. Projection work may provide a
separate boxed `L²` estimate for the regular term. -/
theorem lintegral_offsetTailMaximalOn_exceptional_le_mass_average
    (S E : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (h : ℝ → ℂ) (hh : Integrable h) (ell₀ s : ℤ)
    (hscale : ∀ I ∈ E, I.length = (2 : ℝ) ^ (scale I + 2)) :
    (∫⁻ x, offsetTailMaximalOn S E scale f ell₀ s x * ‖h x‖ₑ) ≤
      ENNReal.ofReal (∑ I ∈ E, 8 * positiveDyadicAmplitudeBound *
        (∫ t, ‖offsetGroupedInput S scale f I s t‖) * intervalL1Average h I) :=
  lintegral_offsetTailMaximalOn_pairing_le_sum_local_averages
    S E scale f h hh ell₀ s hscale

/-- At the author's exceptional threshold, the maximal exceptional roots
occupy exactly the offset-decay fraction of the available `p`-mass. This is
the packing input for the high half of the threshold argument. -/
theorem directMaximalExceptional_length_le_directQuadratic_threshold
    {S : Finset RealInterval} {g : ℝ → ℂ} {p V : ℝ} {I₀ : RealInterval}
    (n : ℕ) (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hglobal : (∫ x in I₀.carrier, ‖g x‖ ^ p) ≤ V) :
    ∑ I ∈ directMaximalExceptionalIntervals S g p
        (directQuadraticExceptionalThreshold p n), I.length ≤
      directQuadraticDelta n ^ (p - 1) * V := by
  calc
    ∑ I ∈ directMaximalExceptionalIntervals S g p
        (directQuadraticExceptionalThreshold p n), I.length ≤
        (directQuadraticExceptionalThreshold p n)⁻¹ * V :=
      directMaximalExceptionalIntervals_length_le
        (Real.rpow_pos_of_pos (directQuadraticDelta_pos n) _) hgp hlam hsub hglobal
    _ = directQuadraticDelta n ^ (p - 1) * V := by
      rw [directQuadratic_exceptional_threshold_inv]

/-- Numeric threshold closure with the genuine direct split kept as a
separate hypothesis. The `hlow` premise is precisely the boxed L²
truncation estimate supplied by the projection step; `hhigh` is obtained
from the preceding exceptional pairing and maximal-exceptional packing. -/
theorem direct_threshold_closure_of_boxed_lowL2
    {ι : Type*} [DecidableEq ι] (P : Finset ι → ℝ) (S L E : Finset ι)
    {C p V : ℝ} (n : ℕ)
    (hunion : S = L ∪ E) (_hLE : Disjoint L E)
    (hlow : P L ≤ C * (directQuadraticDelta n *
      directQuadraticLowThreshold n ^ (1 - p / 2) * V))
    (hhigh : P E ≤ C * (directQuadraticLowThreshold n ^ (1 - p) *
      directQuadraticExceptionalThreshold p n * V))
    (hsubadd : P (L ∪ E) ≤ P L + P E) :
    P S ≤ 2 * C * directQuadraticDelta n ^ (p - 1) * V := by
  subst S
  exact directQuadratic_pairing_threshold_closure_at_scale P (L ∪ E) L E
    n hsubadd hlow hhigh


end
end KrauseLaceyQuadraticDirectThresholdClosure
end QuadraticCarleson
