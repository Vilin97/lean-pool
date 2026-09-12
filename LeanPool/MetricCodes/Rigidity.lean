/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.Weyl

/-!
# All-rank harmonic rigidity

Completion of the root complex and rigidity of harmonic highest-weight vectors.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

namespace UniversalBGGRootComplex

section


open scoped BigOperators

theorem rootVectorBracket_single_rootBracket
    {r : ℕ} (α β γ : PositiveRoot r) :
    rootVectorBracket (Finsupp.single α (1 : ℝ)) (rootBracket β γ) =
      ∑ δ : PositiveRoot r,
        rootStructureConstant β γ δ • rootBracket α δ := by
  classical
  simp only [rootVectorBracket, rootBracket, Finsupp.smul_single, smul_eq_mul, mul_one, map_sum,
    Finsupp.linearCombination_single, one_smul]

theorem rootStructureConstant_jacobi
    {r : ℕ} (α β γ ε : PositiveRoot r) :
    (∑ δ : PositiveRoot r,
        rootStructureConstant β γ δ * rootStructureConstant α δ ε) +
      (∑ δ : PositiveRoot r,
        rootStructureConstant γ α δ * rootStructureConstant β δ ε) +
      (∑ δ : PositiveRoot r,
        rootStructureConstant α β δ * rootStructureConstant γ δ ε) = 0 := by
  have h := rootVectorBracket_jacobi
    (Finsupp.single α (1 : ℝ))
    (Finsupp.single β (1 : ℝ))
    (Finsupp.single γ (1 : ℝ))
  simp only [rootVectorBracket_single_single, one_mul, one_smul] at h
  simp only [rootVectorBracket_single_rootBracket] at h
  have hcoeff := congrArg (fun z : RootVector r => z ε) h
  simpa only [Finsupp.coe_add, Finsupp.coe_finsetSum, Finsupp.coe_smul, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, rootBracket_apply, smul_eq_mul, Finsupp.coe_zero,
    Pi.zero_apply] using hcoeff

theorem actualExteriorRootCreation_anticommute
    {ι M : Type*} [LinearOrder ι]
    [AddCommGroup M] [Module ℝ M]
    (a b : ι) :
    actualExteriorRootCreation M a * actualExteriorRootCreation M b +
      actualExteriorRootCreation M b * actualExteriorRootCreation M a = 0 := by
  classical
  ext f S
  change
    actualExteriorRootCreation M a
        (actualExteriorRootCreation M b f) S +
      actualExteriorRootCreation M b
        (actualExteriorRootCreation M a f) S = 0
  by_cases hab : a = b
  · subst b
    by_cases ha : a ∈ S <;>
      simp [actualExteriorRootCreation_apply, ha]
  · have hba : b ≠ a := Ne.symm hab
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · have hbErase : b ∈ S.erase a := by simp only [Finset.mem_erase, ne_eq, hba,
                                             not_false_eq_true, hb, and_self]
        have haErase : a ∈ S.erase b := by simp only [Finset.mem_erase, ne_eq, hab,
                                             not_false_eq_true, ha, and_self]
        have hsign := realExteriorRootSign_erase_anticommute S ha hb hab
        have hset : (S.erase a).erase b = (S.erase b).erase a :=
          Finset.erase_right_comm
        simp only [actualExteriorRootCreation_apply, ha, hb,
          hbErase, haErase, ↓reduceIte, smul_smul]
        rw [hset, hsign, neg_smul]
        exact neg_add_cancel _
      · simp only [actualExteriorRootCreation_apply, ha, ↓reduceIte, Finset.mem_erase, ne_eq, hb,
          and_false, smul_zero, add_zero]
    · simp only [actualExteriorRootCreation_apply, ha, ↓reduceIte, Finset.mem_erase, ne_eq,
        and_false, smul_zero, ite_self, add_zero]

end

section


variable {ι M : Type*} [LinearOrder ι]
variable [AddCommGroup M] [Module ℝ M]

private theorem cubicExteriorExpansion_metriccodes2_a978fd60 {R : Type*} [Ring R]
    (G B A Z F D : R) :
    (G * (B * A)) * (Z * (F * D)) +
      (Z * (F * D)) * (G * (B * A)) =
      G * B * (A * Z + Z * A) * F * D -
      G * (B * Z + Z * B) * A * F * D +
      Z * F * (D * G + G * D) * B * A -
      Z * (F * G + G * F) * D * B * A +
      (G * Z + Z * G) * B * A * F * D +
      Z * G *
        (F * (D * B + B * D) * A -
          (F * B + B * F) * D * A +
          B * F * (D * A + A * D) -
          B * (F * A + A * F) * D) := by
  noncomm_ring

theorem actualExteriorRootCreation_contraction_contraction_cubic_anticommute
    (α β γ δ ε ζ : ι) :
    (actualExteriorRootCreation M γ *
        (actualExteriorRootContraction M β *
          actualExteriorRootContraction M α)) *
      (actualExteriorRootCreation M ζ *
        (actualExteriorRootContraction M ε *
          actualExteriorRootContraction M δ)) +
      (actualExteriorRootCreation M ζ *
        (actualExteriorRootContraction M ε *
          actualExteriorRootContraction M δ)) *
        (actualExteriorRootCreation M γ *
          (actualExteriorRootContraction M β *
            actualExteriorRootContraction M α)) =
      (if α = ζ then
        actualExteriorRootCreation M γ *
          (actualExteriorRootContraction M β *
            (actualExteriorRootContraction M ε *
              actualExteriorRootContraction M δ)) else 0) -
      (if β = ζ then
        actualExteriorRootCreation M γ *
          (actualExteriorRootContraction M α *
            (actualExteriorRootContraction M ε *
              actualExteriorRootContraction M δ)) else 0) +
      (if δ = γ then
        actualExteriorRootCreation M ζ *
          (actualExteriorRootContraction M ε *
            (actualExteriorRootContraction M β *
              actualExteriorRootContraction M α)) else 0) -
      (if ε = γ then
        actualExteriorRootCreation M ζ *
          (actualExteriorRootContraction M δ *
            (actualExteriorRootContraction M β *
              actualExteriorRootContraction M α)) else 0) := by
  let G : Module.End ℝ (Finset ι → M) := actualExteriorRootCreation M γ
  let B : Module.End ℝ (Finset ι → M) := actualExteriorRootContraction M β
  let A : Module.End ℝ (Finset ι → M) := actualExteriorRootContraction M α
  let Z : Module.End ℝ (Finset ι → M) := actualExteriorRootCreation M ζ
  let F : Module.End ℝ (Finset ι → M) := actualExteriorRootContraction M ε
  let D : Module.End ℝ (Finset ι → M) := actualExteriorRootContraction M δ
  change
    (G * (B * A)) * (Z * (F * D)) +
      (Z * (F * D)) * (G * (B * A)) =
      (if α = ζ then G * (B * (F * D)) else 0) -
      (if β = ζ then G * (A * (F * D)) else 0) +
      (if δ = γ then Z * (F * (B * A)) else 0) -
      (if ε = γ then Z * (D * (B * A)) else 0)
  have hαζ : A * Z + Z * A = if α = ζ then 1 else 0 :=
    actualExteriorRootContraction_creation_anticommute (M := M) α ζ
  have hβζ : B * Z + Z * B = if β = ζ then 1 else 0 :=
    actualExteriorRootContraction_creation_anticommute (M := M) β ζ
  have hδγ : D * G + G * D = if δ = γ then 1 else 0 :=
    actualExteriorRootContraction_creation_anticommute (M := M) δ γ
  have hεγ : F * G + G * F = if ε = γ then 1 else 0 :=
    actualExteriorRootContraction_creation_anticommute (M := M) ε γ
  have hγζ : G * Z + Z * G = 0 :=
    actualExteriorRootCreation_anticommute (M := M) γ ζ
  have hδβ : D * B + B * D = 0 :=
    actualExteriorRootContraction_anticommute (M := M) δ β
  have hεβ : F * B + B * F = 0 :=
    actualExteriorRootContraction_anticommute (M := M) ε β
  have hδα : D * A + A * D = 0 :=
    actualExteriorRootContraction_anticommute (M := M) δ α
  have hεα : F * A + A * F = 0 :=
    actualExteriorRootContraction_anticommute (M := M) ε α
  rw [cubicExteriorExpansion_metriccodes2_a978fd60, hαζ, hβζ, hδγ, hεγ,
    hγζ, hδβ, hεβ, hδα, hεα]
  split_ifs <;>
    simp only [mul_one, mul_zero, zero_mul, sub_zero, zero_sub, add_zero,
      zero_add, sub_self] <;>
    noncomm_ring

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem fullRootExteriorBracketAtom_swap
    {r n : ℕ} (α β γ : PositiveRoot r) :
    fullRootExteriorBracketAtom r n β α γ =
      -fullRootExteriorBracketAtom r n α β γ := by
  have h := actualExteriorRootContraction_anticommute
    (M := PolynomialSpace r n) α β
  have hswap :
      actualExteriorRootContraction (PolynomialSpace r n) α *
          actualExteriorRootContraction (PolynomialSpace r n) β =
        -(actualExteriorRootContraction (PolynomialSpace r n) β *
          actualExteriorRootContraction (PolynomialSpace r n) α) :=
    eq_neg_of_add_eq_zero_left h
  change
    actualExteriorRootCreation (PolynomialSpace r n) γ *
        (actualExteriorRootContraction (PolynomialSpace r n) α *
          actualExteriorRootContraction (PolynomialSpace r n) β) =
      -(actualExteriorRootCreation (PolynomialSpace r n) γ *
        (actualExteriorRootContraction (PolynomialSpace r n) β *
          actualExteriorRootContraction (PolynomialSpace r n) α))
  rw [hswap]
  exact LinearMap.comp_neg _ _

theorem fullRootExteriorBracket_weightedAtom_swap
    {r n : ℕ} (α β γ : PositiveRoot r) :
    rootStructureConstant β α γ •
        fullRootExteriorBracketAtom r n β α γ =
      rootStructureConstant α β γ •
        fullRootExteriorBracketAtom r n α β γ := by
  rw [rootStructureConstant_swap, fullRootExteriorBracketAtom_swap]
  simp only [smul_neg, neg_smul, neg_neg]

private def fullRootExteriorBracketUnordered (r n : ℕ) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
    ∑ γ : PositiveRoot r,
      rootStructureConstant α β γ •
        fullRootExteriorBracketAtom r n α β γ

theorem rootStructureConstant_eq_zero_of_incomparable
    {r : ℕ} (α β γ : PositiveRoot r)
    (hαβ : ¬ α < β) (hβα : ¬ β < α) :
    rootStructureConstant α β γ = 0 := by
  have hfirst : α.val.1 ≠ β.val.2 := by
    intro h
    apply hβα
    change β.val < α.val
    apply (Prod.lt_iff).2
    left
    constructor
    · simpa only [h] using β.property
    · exact le_of_lt (by simpa only [h] using α.property)
  have hsecond : β.val.1 ≠ α.val.2 := by
    intro h
    apply hαβ
    change α.val < β.val
    apply (Prod.lt_iff).2
    left
    constructor
    · simpa only [h] using α.property
    · exact le_of_lt (by simpa only [h] using β.property)
  simp only [rootStructureConstant, hfirst, false_and, ↓reduceIte, hsecond, sub_self]

theorem fullRootExteriorBracketUnordered_eq_two_smul
    (r n : ℕ) :
    fullRootExteriorBracketUnordered r n =
      (2 : ℝ) • fullRootExteriorBracket r n := by
  classical
  let F : PositiveRoot r → PositiveRoot r →
      Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
    fun α β => ∑ γ : PositiveRoot r,
      rootStructureConstant α β γ •
        fullRootExteriorBracketAtom r n α β γ
  have hswap : ∀ α β : PositiveRoot r, F β α = F α β := by
    intro α β
    dsimp [F]
    apply Finset.sum_congr rfl
    intro γ hγ
    exact fullRootExteriorBracket_weightedAtom_swap α β γ
  have hdiag : ∀ α : PositiveRoot r, F α α = 0 := by
    intro α
    dsimp [F]
    apply Finset.sum_eq_zero
    intro γ hγ
    have h := rootStructureConstant_swap α α γ
    have hz : rootStructureConstant α α γ = 0 := by linarith
    simp only [hz, zero_smul]
  have hincomparable : ∀ α β : PositiveRoot r,
      (¬ α < β) → (¬ β < α) → F α β = 0 := by
    intro α β hαβ hβα
    dsimp [F]
    apply Finset.sum_eq_zero
    intro γ hγ
    simp only [rootStructureConstant_eq_zero_of_incomparable α β γ hαβ hβα, zero_smul]
  change (∑ α : PositiveRoot r, ∑ β : PositiveRoot r, F α β) =
    (2 : ℝ) •
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if α < β then F α β else 0)
  have hsplit :
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r, F α β) =
        (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
          if α < β then F α β else 0) +
        (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
          if β < α then F α β else 0) := by
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro α hα
    apply Finset.sum_congr rfl
    intro β hβ
    by_cases hab : α < β
    · have hnot : ¬ β < α := fun h => (lt_asymm hab h).elim
      simp only [hab, ↓reduceIte, hnot, add_zero]
    · by_cases hba : β < α
      · simp only [hab, ↓reduceIte, hba, zero_add]
      · simp only [hincomparable α β hab hba, hab, ↓reduceIte, hba, add_zero]
  have hreverse :
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if β < α then F α β else 0) =
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if α < β then F α β else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α hα
    apply Finset.sum_congr rfl
    intro β hβ
    split_ifs with h
    · exact hswap α β
    · rfl
  rw [hsplit, hreverse]
  simp only [two_smul]

end

section


open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

theorem rootExteriorCoboundaryAtom_swap
    {r : ℕ} (α β γ : PositiveRoot r) :
    actualExteriorRootCreation M β *
        (actualExteriorRootCreation M α *
          actualExteriorRootContraction M γ) =
      -(actualExteriorRootCreation M α *
        (actualExteriorRootCreation M β *
          actualExteriorRootContraction M γ)) := by
  have h := actualExteriorRootCreation_anticommute
    (M := M) α β
  have hswap :
      actualExteriorRootCreation M β *
          actualExteriorRootCreation M α =
        -(actualExteriorRootCreation M α *
          actualExteriorRootCreation M β) :=
    eq_neg_of_add_eq_zero_right h
  rw [← mul_assoc, hswap]
  change
    (-(actualExteriorRootCreation M α).comp
      (actualExteriorRootCreation M β)).comp
      (actualExteriorRootContraction M γ) = _
  rw [LinearMap.neg_comp]
  rfl

theorem rootExteriorCoboundary_weightedAtom_swap
    {r : ℕ} (α β γ : PositiveRoot r) :
    rootStructureConstant β α γ •
        (actualExteriorRootCreation M β *
          (actualExteriorRootCreation M α *
            actualExteriorRootContraction M γ)) =
      rootStructureConstant α β γ •
        (actualExteriorRootCreation M α *
          (actualExteriorRootCreation M β *
            actualExteriorRootContraction M γ)) := by
  rw [rootStructureConstant_swap, rootExteriorCoboundaryAtom_swap]
  simp only [smul_neg, neg_smul, neg_neg]

theorem actualExteriorRootBracketCoboundary_eq_two_ordered_sum
    {r : ℕ} :
    actualExteriorRootBracketCoboundary (M := M)
        (rootStructureConstant (r := r)) =
      (2 : ℝ) •
        (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
          if α < β then
            ∑ γ : PositiveRoot r,
              rootStructureConstant α β γ •
                (actualExteriorRootCreation M α *
                  (actualExteriorRootCreation M β *
                    actualExteriorRootContraction M γ))
          else 0) := by
  classical
  let F : PositiveRoot r → PositiveRoot r →
      Module.End ℝ (Finset (PositiveRoot r) → M) :=
    fun α β => ∑ γ : PositiveRoot r,
      rootStructureConstant α β γ •
        (actualExteriorRootCreation M α *
          (actualExteriorRootCreation M β *
            actualExteriorRootContraction M γ))
  have hswap : ∀ α β : PositiveRoot r, F β α = F α β := by
    intro α β
    dsimp [F]
    apply Finset.sum_congr rfl
    intro γ _
    exact rootExteriorCoboundary_weightedAtom_swap (M := M) α β γ
  have hincomparable : ∀ α β : PositiveRoot r,
      (¬ α < β) → (¬ β < α) → F α β = 0 := by
    intro α β hαβ hβα
    dsimp [F]
    apply Finset.sum_eq_zero
    intro γ _
    simp only [rootStructureConstant_eq_zero_of_incomparable α β γ hαβ hβα, zero_smul]
  change (∑ α : PositiveRoot r, ∑ β : PositiveRoot r, F α β) =
    (2 : ℝ) •
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if α < β then F α β else 0)
  have hsplit :
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r, F α β) =
        (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
          if α < β then F α β else 0) +
        (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
          if β < α then F α β else 0) := by
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    by_cases hab : α < β
    · have hnot : ¬ β < α := fun h => (lt_asymm hab h).elim
      simp only [hab, ↓reduceIte, hnot, add_zero]
    · by_cases hba : β < α
      · simp only [hab, ↓reduceIte, hba, zero_add]
      · simp only [hincomparable α β hab hba, hab, ↓reduceIte, hba, add_zero]
  have hreverse :
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if β < α then F α β else 0) =
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if α < β then F α β else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    split_ifs with h
    · exact hswap α β
    · rfl
  rw [hsplit, hreverse]
  simp only [two_smul]

theorem actualOrderedRootBracketCoboundary_eq_ordered_sum
    {r : ℕ} :
    actualOrderedRootBracketCoboundary (M := M) (r := r) =
      ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if α < β then
          ∑ γ : PositiveRoot r,
            rootStructureConstant α β γ •
              (actualExteriorRootCreation M α *
                (actualExteriorRootCreation M β *
                  actualExteriorRootContraction M γ))
        else 0 := by
  unfold actualOrderedRootBracketCoboundary
  rw [actualExteriorRootBracketCoboundary_eq_two_ordered_sum,
    smul_smul]
  norm_num

theorem actualExteriorRootBracketCoboundary_zeroExtension_of_card_ne
    {r n k : ℕ} (f : RootPolynomialChain r n k)
    (S : Finset (PositiveRoot r)) (hS : S.card ≠ k + 1) :
    actualExteriorRootBracketCoboundary (M := PolynomialSpace r n)
      (rootStructureConstant (r := r))
      (rootPolynomialChainZeroExtension r n k f) S = 0 := by
  classical
  let : DecidableEq (PositiveRoot r) :=
    (positiveRootLinearOrder r).toDecidableEq
  unfold actualExteriorRootBracketCoboundary
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro α _
  apply Finset.sum_eq_zero
  intro β _
  apply Finset.sum_eq_zero
  intro γ _
  simp only [Module.End.mul_apply, actualExteriorRootCreation_apply,
    actualExteriorRootContraction_apply,
    rootPolynomialChainZeroExtension_apply]
  split_ifs with hα hβ hγ hcard <;> simp only [smul_zero, smul_eq_zero]
  exfalso
  apply hS
  have hcarderaseα := Finset.card_erase_add_one hα
  have hcarderaseβ := Finset.card_erase_add_one hβ
  have hcardinsert :
      (insert γ ((S.erase α).erase β)).card =
        ((S.erase α).erase β).card + 1 := by
    exact Finset.card_insert_of_notMem hγ
  omega

theorem actualOrderedRootBracketCoboundary_zeroExtension_of_card_ne
    {r n k : ℕ} (f : RootPolynomialChain r n k)
    (S : Finset (PositiveRoot r)) (hS : S.card ≠ k + 1) :
    actualOrderedRootBracketCoboundary (M := PolynomialSpace r n) (r := r)
      (rootPolynomialChainZeroExtension r n k f) S = 0 := by
  unfold actualOrderedRootBracketCoboundary
  simp only [LinearMap.smul_apply, Pi.smul_apply,
    actualExteriorRootBracketCoboundary_zeroExtension_of_card_ne f S hS, smul_zero]

theorem actualOrderedRootBracketCoboundary_zeroExtension_apply_of_single
    {r n k : ℕ} (f : RootPolynomialChain r n k)
    (S : RootWedge r (k + 1))
    (hsingle : ∀ (T : RootWedge r k) (p : PolynomialSpace r n),
      actualOrderedRootBracketCoboundary (M := PolynomialSpace r n) (r := r)
          (Pi.single T.val p) S.val =
        rootBracketBoundaryCoefficient S T • p) :
    actualOrderedRootBracketCoboundary (M := PolynomialSpace r n) (r := r)
        (rootPolynomialChainZeroExtension r n k f) S.val =
      rootBracketCoboundary r n k f S := by
  classical
  rw [rootPolynomialChainZeroExtension_eq_sum_single, map_sum,
    rootBracketCoboundary_apply]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro T _
  exact hsingle T (f T)

end

section


private theorem rootOrderCode_lt_of_first_lt_metriccodes2_356f06be {r : ℕ}
    (α β : PositiveRoot r) (hfirst : α.val.1 < β.val.1) :
    positiveRootOrderCode α < positiveRootOrderCode β := by
  change (finProdFinEquiv α.val).val < (finProdFinEquiv β.val).val
  rw [finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]
  have hfirst' : α.val.1.val < β.val.1.val := hfirst
  have hmul :
      (r + 1) * α.val.1.val + (r + 1) ≤
        (r + 1) * β.val.1.val := by
    simpa only [Nat.succ_eq_add_one, Nat.mul_add, mul_one] using
      Nat.mul_le_mul_left (r + 1) (Nat.succ_le_of_lt hfirst')
  have hbound : α.val.2.val < r + 1 := α.val.2.isLt
  omega

theorem positiveRootOrderCode_lt_iff_of_structureConstant_ne_zero
    {r : ℕ} (α β γ : PositiveRoot r)
    (h : rootStructureConstant α β γ ≠ 0) :
    positiveRootOrderCode α < positiveRootOrderCode β ↔ α < β := by
  rcases (rootStructureConstant_ne_zero_iff α β γ).mp h with
    ⟨hjoin, _⟩ | ⟨hjoin, _⟩
  · have hfirst : β.val.1 < α.val.1 := by
      rw [hjoin]
      exact β.property
    have hsecond : β.val.2 < α.val.2 := by
      rw [← hjoin]
      exact α.property
    have hcode : positiveRootOrderCode β < positiveRootOrderCode α :=
      rootOrderCode_lt_of_first_lt_metriccodes2_356f06be β α hfirst
    have hroot : β < α := by
      change β.val < α.val
      exact (Prod.lt_iff).2 (Or.inl ⟨hfirst, le_of_lt hsecond⟩)
    constructor
    · exact fun hbad => (not_lt_of_gt hcode hbad).elim
    · exact fun hbad => (not_lt_of_gt hroot hbad).elim
  · have hfirst : α.val.1 < β.val.1 := by
      rw [hjoin]
      exact α.property
    have hsecond : α.val.2 < β.val.2 := by
      rw [← hjoin]
      exact β.property
    have hcode : positiveRootOrderCode α < positiveRootOrderCode β :=
      rootOrderCode_lt_of_first_lt_metriccodes2_356f06be α β hfirst
    have hroot : α < β := by
      change α.val < β.val
      exact (Prod.lt_iff).2 (Or.inl ⟨hfirst, le_of_lt hsecond⟩)
    exact ⟨fun _ => hroot, fun _ => hcode⟩

end

section


open scoped BigOperators

attribute [local instance] Classical.propDecidable

open MetricCodes.Spherical.HigherHarmonicYoung

theorem fullRootExteriorActionAtom_mul_self_zero
    {r n : ℕ} (α : PositiveRoot r) :
    fullRootExteriorActionAtom r n α *
        fullRootExteriorActionAtom r n α = 0 := by
  let P := fullRootExteriorPolynomialAction r n α
  let C := actualExteriorRootContraction (PolynomialSpace r n) α
  have hcomm : P * C = C * P :=
    fullRootExteriorPolynomialAction_contraction_commute α α
  have hzero : C * C = 0 :=
    actualExteriorRootContraction_mul_self_zero α
  change (P * C) * (P * C) = 0
  calc
    (P * C) * (P * C) = P * (C * P) * C := by noncomm_ring
    _ = P * (P * C) * C := by rw [← hcomm]
    _ = P * P * (C * C) := by noncomm_ring
    _ = 0 := by rw [hzero]; simp only [mul_zero]

theorem fullRootExteriorActionAtom_pair
    {r n : ℕ} (α β : PositiveRoot r) :
    fullRootExteriorActionAtom r n α *
          fullRootExteriorActionAtom r n β +
        fullRootExteriorActionAtom r n β *
          fullRootExteriorActionAtom r n α =
      (fullRootExteriorPolynomialAction r n α *
        fullRootExteriorPolynomialAction r n β -
        fullRootExteriorPolynomialAction r n β *
          fullRootExteriorPolynomialAction r n α) *
        (actualExteriorRootContraction (PolynomialSpace r n) α *
          actualExteriorRootContraction (PolynomialSpace r n) β) := by
  let Pα := fullRootExteriorPolynomialAction r n α
  let Pβ := fullRootExteriorPolynomialAction r n β
  let Cα := actualExteriorRootContraction (PolynomialSpace r n) α
  let Cβ := actualExteriorRootContraction (PolynomialSpace r n) β
  have hαβ : Pβ * Cα = Cα * Pβ :=
    fullRootExteriorPolynomialAction_contraction_commute β α
  have hβα : Pα * Cβ = Cβ * Pα :=
    fullRootExteriorPolynomialAction_contraction_commute α β
  have hanti : Cα * Cβ + Cβ * Cα = 0 :=
    actualExteriorRootContraction_anticommute α β
  have hreverse : Cβ * Cα = -(Cα * Cβ) := by
    exact eq_neg_of_add_eq_zero_right hanti
  change
    (Pα * Cα) * (Pβ * Cβ) + (Pβ * Cβ) * (Pα * Cα) =
      (Pα * Pβ - Pβ * Pα) * (Cα * Cβ)
  have hfirst :
      (Pα * Cα) * (Pβ * Cβ) =
        (Pα * Pβ) * (Cα * Cβ) := by
    calc
      _ = Pα * (Cα * Pβ) * Cβ := by noncomm_ring
      _ = Pα * (Pβ * Cα) * Cβ := by rw [← hαβ]
      _ = _ := by noncomm_ring
  have hsecond :
      (Pβ * Cβ) * (Pα * Cα) =
        (Pβ * Pα) * (Cβ * Cα) := by
    calc
      _ = Pβ * (Cβ * Pα) * Cα := by noncomm_ring
      _ = Pβ * (Pα * Cβ) * Cα := by rw [← hβα]
      _ = _ := by noncomm_ring
  rw [hfirst, hsecond, hreverse, sub_mul]
  apply LinearMap.ext
  intro f
  funext S
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply, map_neg, Pi.add_apply,
    Pi.neg_apply, sub_eq_add_neg]

theorem fullRootExteriorAction_square_eq_unordered_structureConstants
    (r n : ℕ) :
    fullRootExteriorAction r n * fullRootExteriorAction r n =
      ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if positiveRootOrderCode α < positiveRootOrderCode β then
          ∑ γ : PositiveRoot r,
            rootStructureConstant α β γ •
              (fullRootExteriorPolynomialAction r n γ *
                (actualExteriorRootContraction (PolynomialSpace r n) α *
                  actualExteriorRootContraction (PolynomialSpace r n) β))
        else 0 := by
  classical
  have hcode : Function.Injective (positiveRootOrderCode (r := r)) := by
    intro α β h
    exact Subtype.ext
      ((finProdFinEquiv (m := r + 1) (n := r + 1)).injective h)
  unfold fullRootExteriorAction
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        fullRootExteriorActionAtom r n α *
          fullRootExteriorActionAtom r n β) =
      ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if α = β then 0
        else fullRootExteriorActionAtom r n α *
          fullRootExteriorActionAtom r n β := by
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      split_ifs with h
      · subst β
        exact fullRootExteriorActionAtom_mul_self_zero α
      · rfl
    _ = ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if positiveRootOrderCode α < positiveRootOrderCode β then
          fullRootExteriorActionAtom r n α *
            fullRootExteriorActionAtom r n β +
          fullRootExteriorActionAtom r n β *
            fullRootExteriorActionAtom r n α
        else 0 :=
      sum_offDiagonal_eq_sum_orderedPairs
        (positiveRootOrderCode (r := r)) hcode
        (fun α β => fullRootExteriorActionAtom r n α *
          fullRootExteriorActionAtom r n β)
    _ = ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if positiveRootOrderCode α < positiveRootOrderCode β then
          ∑ γ : PositiveRoot r,
            rootStructureConstant α β γ •
              (fullRootExteriorPolynomialAction r n γ *
                (actualExteriorRootContraction (PolynomialSpace r n) α *
                  actualExteriorRootContraction (PolynomialSpace r n) β))
        else 0 := by
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      split_ifs with h
      · rw [fullRootExteriorActionAtom_pair α β,
          fullRootExteriorPolynomialAction_commutator α β,
          Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro γ _
        rw [smul_mul_assoc]
      · rfl

theorem fullRootExteriorPolynomialAction_bracketAtom_commute
    {r n : ℕ} (δ α β γ : PositiveRoot r) :
    fullRootExteriorPolynomialAction r n δ *
        fullRootExteriorBracketAtom r n α β γ =
      fullRootExteriorBracketAtom r n α β γ *
        fullRootExteriorPolynomialAction r n δ := by
  let P := fullRootExteriorPolynomialAction r n δ
  let E := actualExteriorRootCreation (PolynomialSpace r n) γ
  let Cβ := actualExteriorRootContraction (PolynomialSpace r n) β
  let Cα := actualExteriorRootContraction (PolynomialSpace r n) α
  have hE : P * E = E * P :=
    fullRootExteriorPolynomialAction_creation_commute δ γ
  have hβ : P * Cβ = Cβ * P :=
    fullRootExteriorPolynomialAction_contraction_commute δ β
  have hα : P * Cα = Cα * P :=
    fullRootExteriorPolynomialAction_contraction_commute δ α
  change P * (E * (Cβ * Cα)) = (E * (Cβ * Cα)) * P
  calc
    P * (E * (Cβ * Cα)) = (P * E) * (Cβ * Cα) := by noncomm_ring
    _ = (E * P) * (Cβ * Cα) := by rw [hE]
    _ = E * (P * Cβ) * Cα := by noncomm_ring
    _ = E * (Cβ * P) * Cα := by rw [hβ]
    _ = E * Cβ * (P * Cα) := by noncomm_ring
    _ = E * Cβ * (Cα * P) := by rw [hα]
    _ = (E * (Cβ * Cα)) * P := by noncomm_ring

theorem fullRootExteriorActionAtom_bracketAtom_anticommute
    {r n : ℕ} (δ α β γ : PositiveRoot r) :
    fullRootExteriorActionAtom r n δ *
          fullRootExteriorBracketAtom r n α β γ +
        fullRootExteriorBracketAtom r n α β γ *
          fullRootExteriorActionAtom r n δ =
      if δ = γ then
        fullRootExteriorPolynomialAction r n γ *
          (actualExteriorRootContraction (PolynomialSpace r n) β *
            actualExteriorRootContraction (PolynomialSpace r n) α)
      else 0 := by
  classical
  let P := fullRootExteriorPolynomialAction r n δ
  let C := actualExteriorRootContraction (PolynomialSpace r n) δ
  let J := fullRootExteriorBracketAtom r n α β γ
  let Cβ := actualExteriorRootContraction (PolynomialSpace r n) β
  let Cα := actualExteriorRootContraction (PolynomialSpace r n) α
  have hcomm : P * J = J * P :=
    fullRootExteriorPolynomialAction_bracketAtom_commute δ α β γ
  have hcar : C * J + J * C =
      if δ = γ then Cβ * Cα else 0 := by
    by_cases h : δ = γ
    · subst γ
      simpa [C, J, Cβ, Cα, fullRootExteriorBracketAtom] using
        (actualExteriorRootContraction_creation_contraction_contraction_anticommute
          (M := PolynomialSpace r n) δ δ β α)
    · simpa [h, C, J, Cβ, Cα, fullRootExteriorBracketAtom] using
        (actualExteriorRootContraction_creation_contraction_contraction_anticommute
          (M := PolynomialSpace r n) δ γ β α)
  change
    (P * C) * J + J * (P * C) =
      if δ = γ then
        fullRootExteriorPolynomialAction r n γ * (Cβ * Cα) else 0
  calc
    (P * C) * J + J * (P * C) =
        P * (C * J) + (J * P) * C := by noncomm_ring
    _ = P * (C * J) + (P * J) * C := by rw [← hcomm]
    _ = P * (C * J + J * C) := by noncomm_ring
    _ = P * (if δ = γ then Cβ * Cα else 0) := by rw [hcar]
    _ = _ := by split_ifs with h <;> simp [h, P]

theorem fullRootExteriorAction_bracketAtom_anticommute
    {r n : ℕ} (α β γ : PositiveRoot r) :
    fullRootExteriorAction r n * fullRootExteriorBracketAtom r n α β γ +
        fullRootExteriorBracketAtom r n α β γ * fullRootExteriorAction r n =
      fullRootExteriorPolynomialAction r n γ *
        (actualExteriorRootContraction (PolynomialSpace r n) β *
          actualExteriorRootContraction (PolynomialSpace r n) α) := by
  classical
  unfold fullRootExteriorAction
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp_rw [fullRootExteriorActionAtom_bracketAtom_anticommute]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem fullRootExteriorAction_bracket_anticommute
    (r n : ℕ) :
    fullRootExteriorAction r n * fullRootExteriorBracket r n +
        fullRootExteriorBracket r n * fullRootExteriorAction r n =
      ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if α < β then
          ∑ γ : PositiveRoot r,
            rootStructureConstant α β γ •
              (fullRootExteriorPolynomialAction r n γ *
                (actualExteriorRootContraction (PolynomialSpace r n) β *
                  actualExteriorRootContraction (PolynomialSpace r n) α))
        else 0 := by
  classical
  unfold fullRootExteriorBracket
  simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul,
    mul_zero, zero_mul, mul_smul_comm, smul_mul_assoc]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro β _
  split_ifs with hαβ
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro γ _
    rw [← smul_add, fullRootExteriorAction_bracketAtom_anticommute]
  · simp only [add_zero]

theorem fullRootExteriorAction_square_add_mixed_eq_zero
    (r n : ℕ) :
    fullRootExteriorAction r n * fullRootExteriorAction r n +
        fullRootExteriorAction r n * fullRootExteriorBracket r n +
        fullRootExteriorBracket r n * fullRootExteriorAction r n = 0 := by
  classical
  rw [show fullRootExteriorAction r n * fullRootExteriorAction r n +
        fullRootExteriorAction r n * fullRootExteriorBracket r n +
        fullRootExteriorBracket r n * fullRootExteriorAction r n =
      fullRootExteriorAction r n * fullRootExteriorAction r n +
        (fullRootExteriorAction r n * fullRootExteriorBracket r n +
          fullRootExteriorBracket r n * fullRootExteriorAction r n)
      by abel]
  rw [fullRootExteriorAction_square_eq_unordered_structureConstants,
    fullRootExteriorAction_bracket_anticommute,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro α _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro β _
  by_cases hcode : positiveRootOrderCode α < positiveRootOrderCode β
  · by_cases hproduct : α < β
    · simp only [hcode, hproduct, ↓reduceIte]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro γ _
      rw [← smul_add, ← mul_add,
        actualExteriorRootContraction_anticommute]
      simp only [mul_zero, smul_zero]
    · simp only [hcode, hproduct, ↓reduceIte, add_zero]
      apply Finset.sum_eq_zero
      intro γ _
      have hconstant : rootStructureConstant α β γ = 0 := by
        by_contra hnonzero
        exact hproduct
          ((positiveRootOrderCode_lt_iff_of_structureConstant_ne_zero
            α β γ hnonzero).mp hcode)
      simp only [hconstant, zero_smul]
  · by_cases hproduct : α < β
    · simp only [hcode, hproduct, ↓reduceIte, zero_add]
      apply Finset.sum_eq_zero
      intro γ _
      have hconstant : rootStructureConstant α β γ = 0 := by
        by_contra hnonzero
        exact hcode
          ((positiveRootOrderCode_lt_iff_of_structureConstant_ne_zero
            α β γ hnonzero).mpr hproduct)
      simp only [hconstant, zero_smul]
    · simp only [hcode, ↓reduceIte, hproduct, add_zero]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The positive root exterior bridge decidable eq used in the spherical-code argument. -/
local instance positiveRootExteriorBridgeDecidableEq (r : ℕ) :
    DecidableEq (PositiveRoot r) :=
  (positiveRootLinearOrder r).toDecidableEq

theorem fullRootExteriorBracketAtom_single_apply
    {r n k : ℕ} (S : RootWedge r (k + 1)) (T : RootWedge r k)
    (α β γ : PositiveRoot r) (p : PolynomialSpace r n) :
    fullRootExteriorBracketAtom r n α β γ
        (Pi.single S.val p) T.val =
      if α ∈ S.val ∧ β ∈ S.val.erase α ∧
          γ ∉ (S.val.erase α).erase β ∧
          T.val = insert γ ((S.val.erase α).erase β) then
        (realExteriorRootSign S.val α *
          realExteriorRootSign (S.val.erase α) β *
          realExteriorRootSign T.val γ) • p
      else 0 := by
  classical
  have hsupport := rootExteriorBracketAtom_support_iff
    S.val T.val α β γ
  simp only [fullRootExteriorBracketAtom, Module.End.mul_apply,
    actualExteriorRootCreation_apply, actualExteriorRootContraction_apply,
    Pi.single_apply]
  by_cases hγ : γ ∈ T.val
  · by_cases hβ : β ∈ T.val.erase γ
    · have hnot : ¬ (α ∈ S.val ∧ β ∈ S.val.erase α ∧
          γ ∉ (S.val.erase α).erase β ∧
          T.val = insert γ ((S.val.erase α).erase β)) := by
        intro h
        exact (hsupport.mpr h).2.1 hβ
      rw [ite_eq_right hnot]
      simp only [hγ, hβ, ite_true, smul_zero]
    · by_cases hα : α ∈ insert β (T.val.erase γ)
      · have hnot : ¬ (α ∈ S.val ∧ β ∈ S.val.erase α ∧
            γ ∉ (S.val.erase α).erase β ∧
            T.val = insert γ ((S.val.erase α).erase β)) := by
          intro h
          exact (hsupport.mpr h).2.2.1 hα
        rw [ite_eq_right hnot]
        simp only [hγ, hβ, hα, ite_true, ite_false, smul_zero]
      · by_cases hW : insert α (insert β (T.val.erase γ)) = S.val
        · have hsrc : α ∈ S.val ∧ β ∈ S.val.erase α ∧
              γ ∉ (S.val.erase α).erase β ∧
              T.val = insert γ ((S.val.erase α).erase β) :=
            hsupport.mp ⟨hγ, hβ, hα, hW⟩
          have hSα : S.val.erase α = insert β (T.val.erase γ) := by
            rw [← hW, Finset.erase_insert hα]
          rw [ite_eq_left hsrc]
          simp only [hγ, hβ, hα, hW, ite_true, ite_false]
          rw [hSα, ← hW]
          simp only [smul_smul]
          congr 1
          ring
        · have hnot : ¬ (α ∈ S.val ∧ β ∈ S.val.erase α ∧
              γ ∉ (S.val.erase α).erase β ∧
              T.val = insert γ ((S.val.erase α).erase β)) := by
            intro h
            exact hW (hsupport.mpr h).2.2.2
          rw [ite_eq_right hnot]
          simp only [hγ, hβ, hα, hW, ite_true, ite_false,
            smul_zero]
  · have hnot : ¬ (α ∈ S.val ∧ β ∈ S.val.erase α ∧
        γ ∉ (S.val.erase α).erase β ∧
        T.val = insert γ ((S.val.erase α).erase β)) := by
      intro h
      exact hγ (hsupport.mpr h).1
    rw [ite_eq_right hnot]
    simp only [hγ, ite_false]

theorem fullRootExteriorBracket_single_apply
    {r n k : ℕ} (S : RootWedge r (k + 1)) (T : RootWedge r k)
    (p : PolynomialSpace r n) :
    fullRootExteriorBracket r n (Pi.single S.val p) T.val =
      rootBracketBoundaryCoefficient S T • p := by
  classical
  unfold fullRootExteriorBracket
  simp only [LinearMap.sum_apply, Finset.sum_apply, ite_apply, apply_ite,
    LinearMap.zero_apply, Pi.zero_apply, LinearMap.smul_apply,
    Pi.smul_apply]
  simp_rw [fullRootExteriorBracketAtom_single_apply]
  unfold rootBracketBoundaryCoefficient
  simp_rw [Finset.sum_smul, ite_smul, zero_smul, smul_ite,
    smul_zero, smul_smul]
  have houtα : ∀ α ∈ (Finset.univ : Finset (PositiveRoot r)),
      α ∉ S.val →
      (∑ β : PositiveRoot r,
        if α < β then
          ∑ γ : PositiveRoot r,
            if α ∈ S.val ∧ β ∈ S.val.erase α ∧
                γ ∉ (S.val.erase α).erase β ∧
                T.val = insert γ ((S.val.erase α).erase β) then
              (rootStructureConstant α β γ *
                (realExteriorRootSign S.val α *
                  realExteriorRootSign (S.val.erase α) β *
                  realExteriorRootSign T.val γ)) • p
            else 0
        else 0) = 0 := by
    intro α _ hα
    simp only [hα, not_false_eq_true, Finset.erase_eq_of_notMem, Finset.mem_erase, ne_eq, not_and,
      false_and, ↓reduceIte, Finset.sum_const_zero, ite_self]
  rw [← Finset.sum_subset (Finset.subset_univ S.val) houtα]
  apply Finset.sum_congr rfl
  intro α hα
  have houtβ : ∀ β ∈ (Finset.univ : Finset (PositiveRoot r)),
      β ∉ S.val.erase α →
      (if α < β then
        ∑ γ : PositiveRoot r,
          if α ∈ S.val ∧ β ∈ S.val.erase α ∧
              γ ∉ (S.val.erase α).erase β ∧
              T.val = insert γ ((S.val.erase α).erase β) then
            (rootStructureConstant α β γ *
              (realExteriorRootSign S.val α *
                realExteriorRootSign (S.val.erase α) β *
                realExteriorRootSign T.val γ)) • p
          else 0
      else 0) = 0 := by
    intro β _ hβ
    simp only [hβ, not_false_eq_true, Finset.erase_eq_of_notMem, Finset.mem_erase, ne_eq, not_and,
      false_and, and_false, ↓reduceIte, Finset.sum_const_zero, ite_self]
  rw [← Finset.sum_subset (Finset.subset_univ (S.val.erase α)) houtβ]
  apply Finset.sum_congr (by ext β; simp only [Finset.mem_erase, ne_eq])
  intro β hβ
  split_ifs with hlt
  · rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro γ _
    have hβ' : β ∈ S.val.erase α := by
      simpa only [Finset.mem_erase] using hβ
    have herase : S.val.erase α =
        @Finset.erase (PositiveRoot r)
          (fun a b => Subtype.instDecidableEq a b) S.val α := by
      ext z
      simp only [Finset.mem_erase]
    simp only [hα, hβ', true_and, ite_smul, zero_smul,
      Finset.ext_iff, Finset.mem_insert, Finset.mem_erase]
    split_ifs
    · rw [herase]
      congr 1
      ring
    · rfl
  · rfl

theorem fullRootExteriorBracket_zeroExtension_apply
    {r n k : ℕ}
    (f : RootPolynomialChain r n (k + 1))
    (T : RootWedge r k) :
    fullRootExteriorBracket r n
        (rootPolynomialChainZeroExtension r n (k + 1) f) T.val =
      rootBracketBoundary r n k f T := by
  classical
  rw [rootPolynomialChainZeroExtension_eq_sum_single,
    map_sum, Finset.sum_apply, rootBracketBoundary_apply]
  apply Finset.sum_congr rfl
  intro S _
  convert fullRootExteriorBracket_single_apply S T (f S) using 1
  apply congrArg (fun q : Finset (PositiveRoot r) → PolynomialSpace r n =>
    fullRootExteriorBracket r n q T.val)
  funext U
  simp only [Pi.single_apply, ite_eq_ite]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem two_smul_sum_mul_sum_eq_sum_anticommutator
    {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (A : ι → Module.End ℝ V) :
    (2 : ℝ) • ((∑ i, A i) * (∑ i, A i)) =
      ∑ i, ∑ j, (A i * A j + A j * A i) := by
  classical
  have hswap :
      (∑ i, ∑ j, A j * A i) =
        ∑ i, ∑ j, A i * A j := by
    rw [Finset.sum_comm]
  calc
    (2 : ℝ) • ((∑ i, A i) * (∑ i, A i)) =
        ((∑ i, A i) * (∑ i, A i)) +
          ((∑ i, A i) * (∑ i, A i)) := by
      simp only [two_smul]
    _ = (∑ i, ∑ j, A i * A j) +
          (∑ i, ∑ j, A j * A i) := by
      have hprod :
          (∑ i, A i) * (∑ i, A i) =
            ∑ i, ∑ j, A i * A j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      rw [hprod]
      rw [hswap]
    _ = ∑ i, ∑ j, (A i * A j + A j * A i) := by
      simp_rw [← Finset.sum_add_distrib]

theorem smul_operator_anticommutator
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a b : ℝ) (A B : Module.End ℝ V) :
    (a • A) * (b • B) + (b • B) * (a • A) =
      (a * b) • (A * B + B * A) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, map_smul, smul_smul, smul_add]
  module

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

private def fullRootExteriorCubicIncidenceOne (r n : ℕ) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
    ∑ γ : PositiveRoot r, ∑ δ : PositiveRoot r,
      ∑ ε : PositiveRoot r,
        (rootStructureConstant α β γ * rootStructureConstant δ ε α) •
          (actualExteriorRootCreation (PolynomialSpace r n) γ *
            (actualExteriorRootContraction (PolynomialSpace r n) β *
              (actualExteriorRootContraction (PolynomialSpace r n) ε *
                actualExteriorRootContraction (PolynomialSpace r n) δ)))

private def fullRootExteriorCubicIncidenceTwo (r n : ℕ) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
    ∑ γ : PositiveRoot r, ∑ δ : PositiveRoot r,
      ∑ ε : PositiveRoot r,
        (rootStructureConstant α β γ * rootStructureConstant δ ε β) •
          (actualExteriorRootCreation (PolynomialSpace r n) γ *
            (actualExteriorRootContraction (PolynomialSpace r n) α *
              (actualExteriorRootContraction (PolynomialSpace r n) ε *
                actualExteriorRootContraction (PolynomialSpace r n) δ)))

private def fullRootExteriorCubicIncidenceThree (r n : ℕ) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
    ∑ γ : PositiveRoot r, ∑ ε : PositiveRoot r,
      ∑ ζ : PositiveRoot r,
        (rootStructureConstant α β γ * rootStructureConstant γ ε ζ) •
          (actualExteriorRootCreation (PolynomialSpace r n) ζ *
            (actualExteriorRootContraction (PolynomialSpace r n) ε *
              (actualExteriorRootContraction (PolynomialSpace r n) β *
                actualExteriorRootContraction (PolynomialSpace r n) α)))

private def fullRootExteriorCubicIncidenceFour (r n : ℕ) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
    ∑ γ : PositiveRoot r, ∑ δ : PositiveRoot r,
      ∑ ζ : PositiveRoot r,
        (rootStructureConstant α β γ * rootStructureConstant δ γ ζ) •
          (actualExteriorRootCreation (PolynomialSpace r n) ζ *
            (actualExteriorRootContraction (PolynomialSpace r n) δ *
              (actualExteriorRootContraction (PolynomialSpace r n) β *
                actualExteriorRootContraction (PolynomialSpace r n) α)))

theorem fullRootExteriorBracketUnordered_square_eq_cubicIncidences
    (r n : ℕ) :
    (2 : ℝ) •
        (fullRootExteriorBracketUnordered r n *
          fullRootExteriorBracketUnordered r n) =
      fullRootExteriorCubicIncidenceOne r n -
        fullRootExteriorCubicIncidenceTwo r n +
        fullRootExteriorCubicIncidenceThree r n -
        fullRootExteriorCubicIncidenceFour r n := by
  classical
  let I := PositiveRoot r × PositiveRoot r × PositiveRoot r
  let A : I → Module.End ℝ (FullRootExteriorPolynomialChain r n) := fun x =>
    rootStructureConstant x.1 x.2.1 x.2.2 •
      fullRootExteriorBracketAtom r n x.1 x.2.1 x.2.2
  have hU :
      fullRootExteriorBracketUnordered r n = ∑ x : I, A x := by
    simp only [fullRootExteriorBracketUnordered, A, I, Fintype.sum_prod_type]
  rw [hU, two_smul_sum_mul_sum_eq_sum_anticommutator]
  simp only [I, Fintype.sum_prod_type] at *
  dsimp [A]
  simp_rw [smul_operator_anticommutator]
  simp only [fullRootExteriorBracketAtom]
  simp_rw [actualExteriorRootCreation_contraction_contraction_cubic_anticommute]
  simp only [smul_add, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, smul_ite, smul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', fullRootExteriorCubicIncidenceOne,
    fullRootExteriorCubicIncidenceTwo, fullRootExteriorCubicIncidenceThree,
    fullRootExteriorCubicIncidenceFour]

end

section


open scoped BigOperators

theorem actualExteriorRootContraction_triple_cyclic
    {r n : ℕ} (a b c : PositiveRoot r) :
    actualExteriorRootContraction (PolynomialSpace r n) a *
      (actualExteriorRootContraction (PolynomialSpace r n) b *
        actualExteriorRootContraction (PolynomialSpace r n) c) =
      actualExteriorRootContraction (PolynomialSpace r n) b *
        (actualExteriorRootContraction (PolynomialSpace r n) c *
          actualExteriorRootContraction (PolynomialSpace r n) a) := by
  have hab := actualExteriorRootContraction_anticommute
    (M := PolynomialSpace r n) a b
  have hac := actualExteriorRootContraction_anticommute
    (M := PolynomialSpace r n) a c
  calc
    _ =
        (actualExteriorRootContraction (PolynomialSpace r n) a *
          actualExteriorRootContraction (PolynomialSpace r n) b +
            actualExteriorRootContraction (PolynomialSpace r n) b *
              actualExteriorRootContraction (PolynomialSpace r n) a) *
                actualExteriorRootContraction (PolynomialSpace r n) c -
        actualExteriorRootContraction (PolynomialSpace r n) b *
          (actualExteriorRootContraction (PolynomialSpace r n) a *
            actualExteriorRootContraction (PolynomialSpace r n) c +
              actualExteriorRootContraction (PolynomialSpace r n) c *
                actualExteriorRootContraction (PolynomialSpace r n) a) +
        actualExteriorRootContraction (PolynomialSpace r n) b *
          (actualExteriorRootContraction (PolynomialSpace r n) c *
            actualExteriorRootContraction (PolynomialSpace r n) a) := by
      noncomm_ring
    _ = _ := by rw [hab, hac]; simp only [zero_mul, mul_zero, sub_self, zero_add]

private abbrev RootTriple_metriccodes2_177cedff (r : ℕ) :=
  PositiveRoot r × PositiveRoot r × PositiveRoot r

private def rootTripleCycle_metriccodes2_177cedff (r : ℕ) : RootTriple_metriccodes2_177cedff r ≃
  RootTriple_metriccodes2_177cedff r where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun x := (x.2.2, x.1, x.2.1)
  left_inv x := by rcases x with ⟨a, b, c⟩; rfl
  right_inv x := by rcases x with ⟨a, b, c⟩; rfl

private abbrev RootQuintuple_metriccodes2_177cedff (r : ℕ) :=
  PositiveRoot r × PositiveRoot r × PositiveRoot r ×
    PositiveRoot r × PositiveRoot r

private def rootIncidenceQuintupleReindex_metriccodes2_177cedff (r : ℕ) :
    RootQuintuple_metriccodes2_177cedff r ≃ RootQuintuple_metriccodes2_177cedff r where
  toFun x := (x.2.2.1, x.2.1, x.2.2.2.2, x.2.2.2.1, x.1)
  invFun x := (x.2.2.2.2, x.2.1, x.1, x.2.2.2.1, x.2.2.1)
  left_inv x := by rcases x with ⟨a, b, c, d, e⟩; rfl
  right_inv x := by rcases x with ⟨a, b, c, d, e⟩; rfl

theorem rootStructureConstant_exteriorJacobi_sum_zero
    {r n : ℕ} (γ : PositiveRoot r) :
    (∑ x : PositiveRoot r × PositiveRoot r × PositiveRoot r,
      (∑ a : PositiveRoot r,
        rootStructureConstant x.2.1 x.2.2 a *
          rootStructureConstant x.1 a γ) •
        (actualExteriorRootCreation (PolynomialSpace r n) γ *
          (actualExteriorRootContraction (PolynomialSpace r n) x.1 *
            (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
              actualExteriorRootContraction (PolynomialSpace r n) x.2.2)))) = 0 := by
  let J : RootTriple_metriccodes2_177cedff r → ℝ := fun x =>
    ∑ a : PositiveRoot r,
      rootStructureConstant x.2.1 x.2.2 a *
        rootStructureConstant x.1 a γ
  let V : RootTriple_metriccodes2_177cedff r → Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
    fun x => actualExteriorRootCreation (PolynomialSpace r n) γ *
      (actualExteriorRootContraction (PolynomialSpace r n) x.1 *
        (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
          actualExteriorRootContraction (PolynomialSpace r n) x.2.2))
  change (∑ x : RootTriple_metriccodes2_177cedff r, J x • V x) = 0
  have hV : ∀ x : RootTriple_metriccodes2_177cedff r,
      V (rootTripleCycle_metriccodes2_177cedff r x) = V x := by
    intro x
    change
      actualExteriorRootCreation (PolynomialSpace r n) γ *
          (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
            (actualExteriorRootContraction (PolynomialSpace r n) x.2.2 *
              actualExteriorRootContraction (PolynomialSpace r n) x.1)) =
        actualExteriorRootCreation (PolynomialSpace r n) γ *
          (actualExteriorRootContraction (PolynomialSpace r n) x.1 *
            (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
              actualExteriorRootContraction (PolynomialSpace r n) x.2.2))
    rw [actualExteriorRootContraction_triple_cyclic x.1 x.2.1 x.2.2]
  have hJ : ∀ x : RootTriple_metriccodes2_177cedff r,
      J x + J (rootTripleCycle_metriccodes2_177cedff r x) +
        J (rootTripleCycle_metriccodes2_177cedff r (rootTripleCycle_metriccodes2_177cedff r x))
          = 0 := by
    intro x
    exact rootStructureConstant_jacobi x.1 x.2.1 x.2.2 γ
  have hcycle :
      (∑ x : RootTriple_metriccodes2_177cedff r, J (rootTripleCycle_metriccodes2_177cedff r x) •
        V x) =
        ∑ x : RootTriple_metriccodes2_177cedff r, J x • V x := by
    calc
      _ = ∑ x : RootTriple_metriccodes2_177cedff r,
          J (rootTripleCycle_metriccodes2_177cedff r x) • V
            (rootTripleCycle_metriccodes2_177cedff r x) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hV]
      _ = _ := Equiv.sum_comp (rootTripleCycle_metriccodes2_177cedff r)
        (fun x => J x • V x)
  have hcycle2 :
      (∑ x : RootTriple_metriccodes2_177cedff r,
        J (rootTripleCycle_metriccodes2_177cedff r (rootTripleCycle_metriccodes2_177cedff r x))
          • V x) =
        ∑ x : RootTriple_metriccodes2_177cedff r, J x • V x := by
    calc
      _ = ∑ x : RootTriple_metriccodes2_177cedff r,
          J (rootTripleCycle_metriccodes2_177cedff r (rootTripleCycle_metriccodes2_177cedff r x)) •
            V (rootTripleCycle_metriccodes2_177cedff r (rootTripleCycle_metriccodes2_177cedff r
              x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hV, hV]
      _ = _ := Equiv.sum_comp
        ((rootTripleCycle_metriccodes2_177cedff r).trans (rootTripleCycle_metriccodes2_177cedff r))
          (fun x => J x • V x)
  have hsum :
      (∑ x : RootTriple_metriccodes2_177cedff r, J x • V x) +
        (∑ x : RootTriple_metriccodes2_177cedff r, J x • V x) +
          (∑ x : RootTriple_metriccodes2_177cedff r, J x • V x) = 0 := by
    calc
      _ = (∑ x : RootTriple_metriccodes2_177cedff r, J x • V x) +
            (∑ x : RootTriple_metriccodes2_177cedff r,
              J (rootTripleCycle_metriccodes2_177cedff r x) • V x) +
            (∑ x : RootTriple_metriccodes2_177cedff r,
              J (rootTripleCycle_metriccodes2_177cedff r (rootTripleCycle_metriccodes2_177cedff
                r x)) • V x) := by
        rw [hcycle, hcycle2]
      _ = ∑ x : RootTriple_metriccodes2_177cedff r,
          (J x + J (rootTripleCycle_metriccodes2_177cedff r x) +
            J (rootTripleCycle_metriccodes2_177cedff r (rootTripleCycle_metriccodes2_177cedff r
              x))) • V x := by
        simp_rw [add_smul, Finset.sum_add_distrib]
      _ = 0 := by
        simp_rw [hJ, zero_smul]
        simp only [Finset.sum_const_zero]
  have hthree :
      (3 : ℝ) • (∑ x : RootTriple_metriccodes2_177cedff r, J x • V x) = 0 := by
    simpa only [show (3 : ℝ) = 1 + 1 + 1 by norm_num, add_smul, one_smul] using hsum
  exact (smul_eq_zero.mp hthree).resolve_left (by norm_num)

theorem fullRootExteriorBracket_incidence_sum_zero
    (r n : ℕ) :
    (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
      ∑ γ : PositiveRoot r, ∑ δ : PositiveRoot r,
        ∑ ε : PositiveRoot r,
          (rootStructureConstant α β γ *
            rootStructureConstant δ ε α) •
              (actualExteriorRootCreation (PolynomialSpace r n) γ *
                (actualExteriorRootContraction (PolynomialSpace r n) β *
                  (actualExteriorRootContraction (PolynomialSpace r n) ε *
                    actualExteriorRootContraction (PolynomialSpace r n) δ)))) = 0 := by
  let F : RootQuintuple_metriccodes2_177cedff r →
      Module.End ℝ (FullRootExteriorPolynomialChain r n) := fun x =>
    (rootStructureConstant x.1 x.2.1 x.2.2.1 *
      rootStructureConstant x.2.2.2.1 x.2.2.2.2 x.1) •
        (actualExteriorRootCreation (PolynomialSpace r n) x.2.2.1 *
          (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
            (actualExteriorRootContraction (PolynomialSpace r n) x.2.2.2.2 *
              actualExteriorRootContraction (PolynomialSpace r n) x.2.2.2.1)))
  let G : RootQuintuple_metriccodes2_177cedff r →
      Module.End ℝ (FullRootExteriorPolynomialChain r n) := fun x =>
    (rootStructureConstant x.2.2.1 x.2.2.2.1 x.2.2.2.2 *
      rootStructureConstant x.2.1 x.2.2.2.2 x.1) •
        (actualExteriorRootCreation (PolynomialSpace r n) x.1 *
          (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
            (actualExteriorRootContraction (PolynomialSpace r n) x.2.2.1 *
              actualExteriorRootContraction (PolynomialSpace r n) x.2.2.2.1)))
  have hpoint : ∀ x : RootQuintuple_metriccodes2_177cedff r,
      F x = G (rootIncidenceQuintupleReindex_metriccodes2_177cedff r x) := by
    intro x
    rcases x with ⟨α, β, γ, δ, ε⟩
    change
      (rootStructureConstant α β γ * rootStructureConstant δ ε α) • _ =
        (rootStructureConstant ε δ α * rootStructureConstant β α γ) • _
    rw [rootStructureConstant_swap β α γ,
      rootStructureConstant_swap ε δ α]
    simp only [mul_neg, neg_mul, neg_neg, mul_comm,
      rootIncidenceQuintupleReindex_metriccodes2_177cedff, Equiv.coe_fn_mk]
  have hG : (∑ x : RootQuintuple_metriccodes2_177cedff r, G x) = 0 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro γ hγ
    have h := rootStructureConstant_exteriorJacobi_sum_zero
      (n := n) γ
    simp only [Fintype.sum_prod_type] at h
    simpa only [G, Finset.sum_smul] using h
  change (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
    ∑ γ : PositiveRoot r, ∑ δ : PositiveRoot r,
      ∑ ε : PositiveRoot r, F (α, β, γ, δ, ε)) = 0
  calc
    _ = ∑ x : RootQuintuple_metriccodes2_177cedff r, F x := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ x : RootQuintuple_metriccodes2_177cedff r, G x :=
      Fintype.sum_equiv (rootIncidenceQuintupleReindex_metriccodes2_177cedff r) F G hpoint
    _ = 0 := hG

end

section


open scoped BigOperators

private abbrev FiveRoots_metriccodes2_31abf157 (r : ℕ) :=
  PositiveRoot r × PositiveRoot r × PositiveRoot r ×
    PositiveRoot r × PositiveRoot r

private theorem sum_five_root_equiv_metriccodes2_31abf157
    {r : ℕ} {V : Type*} [AddCommMonoid V]
    (f g : FiveRoots_metriccodes2_31abf157 r → V) (e : FiveRoots_metriccodes2_31abf157 r ≃
      FiveRoots_metriccodes2_31abf157 r)
    (h : ∀ x, f x = g (e x)) :
    (∑ a : PositiveRoot r, ∑ b : PositiveRoot r,
      ∑ c : PositiveRoot r, ∑ d : PositiveRoot r,
        ∑ k : PositiveRoot r, f (a, b, c, d, k)) =
      ∑ a : PositiveRoot r, ∑ b : PositiveRoot r,
        ∑ c : PositiveRoot r, ∑ d : PositiveRoot r,
          ∑ k : PositiveRoot r, g (a, b, c, d, k) := by
  calc
    _ = ∑ x : FiveRoots_metriccodes2_31abf157 r, f x := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ x : FiveRoots_metriccodes2_31abf157 r, g x := Fintype.sum_equiv e f g h
    _ = _ := by
      simp only [Fintype.sum_prod_type]

private def rootFiveSwapFirstTwo_metriccodes2_31abf157 (r : ℕ) : FiveRoots_metriccodes2_31abf157
  r ≃ FiveRoots_metriccodes2_31abf157 r where
  toFun x := (x.2.1, x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2)
  invFun x := (x.2.1, x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2)
  left_inv x := by rcases x with ⟨a, b, c, d, e⟩; rfl
  right_inv x := by rcases x with ⟨a, b, c, d, e⟩; rfl

private def rootFiveSwapBracketTriples_metriccodes2_31abf157 (r : ℕ) :
    FiveRoots_metriccodes2_31abf157 r ≃ FiveRoots_metriccodes2_31abf157 r where
  toFun x := (x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.1, x.2.1)
  invFun x := (x.2.2.2.1, x.2.2.2.2, x.1, x.2.1, x.2.2.1)
  left_inv x := by rcases x with ⟨a, b, c, d, e⟩; rfl
  right_inv x := by rcases x with ⟨a, b, c, d, e⟩; rfl

theorem fullRootExteriorCubicIncidenceTwo_eq_neg
    (r n : ℕ) :
    fullRootExteriorCubicIncidenceTwo r n =
      -fullRootExteriorCubicIncidenceOne r n := by
  unfold fullRootExteriorCubicIncidenceOne
    fullRootExteriorCubicIncidenceTwo
  rw [← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_neg_distrib]
  apply sum_five_root_equiv_metriccodes2_31abf157
    (fun x : FiveRoots_metriccodes2_31abf157 r =>
      (rootStructureConstant x.1 x.2.1 x.2.2.1 *
        rootStructureConstant x.2.2.2.1 x.2.2.2.2 x.2.1) •
        (actualExteriorRootCreation (PolynomialSpace r n) x.2.2.1 *
          (actualExteriorRootContraction (PolynomialSpace r n) x.1 *
            (actualExteriorRootContraction (PolynomialSpace r n) x.2.2.2.2 *
              actualExteriorRootContraction (PolynomialSpace r n)
                x.2.2.2.1))))
    (fun x : FiveRoots_metriccodes2_31abf157 r =>
      -((rootStructureConstant x.1 x.2.1 x.2.2.1 *
        rootStructureConstant x.2.2.2.1 x.2.2.2.2 x.1) •
        (actualExteriorRootCreation (PolynomialSpace r n) x.2.2.1 *
          (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
            (actualExteriorRootContraction (PolynomialSpace r n) x.2.2.2.2 *
              actualExteriorRootContraction (PolynomialSpace r n)
                x.2.2.2.1)))))
    (rootFiveSwapFirstTwo_metriccodes2_31abf157 r)
  intro x
  rcases x with ⟨a, b, c, d, e⟩
  simp only [rootFiveSwapFirstTwo_metriccodes2_31abf157, Equiv.coe_fn_mk]
  rw [rootStructureConstant_swap a b c]
  module

theorem fullRootExteriorCubicIncidenceThree_eq
    (r n : ℕ) :
    fullRootExteriorCubicIncidenceThree r n =
      fullRootExteriorCubicIncidenceOne r n := by
  unfold fullRootExteriorCubicIncidenceOne
    fullRootExteriorCubicIncidenceThree
  apply sum_five_root_equiv_metriccodes2_31abf157
    (fun x : FiveRoots_metriccodes2_31abf157 r =>
      (rootStructureConstant x.1 x.2.1 x.2.2.1 *
        rootStructureConstant x.2.2.1 x.2.2.2.1 x.2.2.2.2) •
        (actualExteriorRootCreation (PolynomialSpace r n) x.2.2.2.2 *
          (actualExteriorRootContraction (PolynomialSpace r n)
            x.2.2.2.1 *
            (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
              actualExteriorRootContraction (PolynomialSpace r n) x.1))))
    (fun x : FiveRoots_metriccodes2_31abf157 r =>
      (rootStructureConstant x.1 x.2.1 x.2.2.1 *
        rootStructureConstant x.2.2.2.1 x.2.2.2.2 x.1) •
        (actualExteriorRootCreation (PolynomialSpace r n) x.2.2.1 *
          (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
            (actualExteriorRootContraction (PolynomialSpace r n)
              x.2.2.2.2 *
              actualExteriorRootContraction (PolynomialSpace r n)
                x.2.2.2.1))))
    (rootFiveSwapBracketTriples_metriccodes2_31abf157 r)
  intro x
  rcases x with ⟨a, b, c, d, e⟩
  simp only [rootFiveSwapBracketTriples_metriccodes2_31abf157, Equiv.coe_fn_mk, mul_comm]

theorem fullRootExteriorCubicIncidenceFour_eq_neg
    (r n : ℕ) :
    fullRootExteriorCubicIncidenceFour r n =
      -fullRootExteriorCubicIncidenceOne r n := by
  unfold fullRootExteriorCubicIncidenceOne
    fullRootExteriorCubicIncidenceFour
  rw [← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_neg_distrib]
  apply sum_five_root_equiv_metriccodes2_31abf157
    (fun x : FiveRoots_metriccodes2_31abf157 r =>
      (rootStructureConstant x.1 x.2.1 x.2.2.1 *
        rootStructureConstant x.2.2.2.1 x.2.2.1 x.2.2.2.2) •
        (actualExteriorRootCreation (PolynomialSpace r n) x.2.2.2.2 *
          (actualExteriorRootContraction (PolynomialSpace r n)
            x.2.2.2.1 *
            (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
              actualExteriorRootContraction (PolynomialSpace r n) x.1))))
    (fun x : FiveRoots_metriccodes2_31abf157 r =>
      -((rootStructureConstant x.1 x.2.1 x.2.2.1 *
        rootStructureConstant x.2.2.2.1 x.2.2.2.2 x.1) •
        (actualExteriorRootCreation (PolynomialSpace r n) x.2.2.1 *
          (actualExteriorRootContraction (PolynomialSpace r n) x.2.1 *
            (actualExteriorRootContraction (PolynomialSpace r n)
              x.2.2.2.2 *
              actualExteriorRootContraction (PolynomialSpace r n)
                x.2.2.2.1)))))
    (rootFiveSwapBracketTriples_metriccodes2_31abf157 r)
  intro x
  rcases x with ⟨a, b, c, d, e⟩
  simp only [rootFiveSwapBracketTriples_metriccodes2_31abf157, Equiv.coe_fn_mk]
  rw [rootStructureConstant_swap c d e]
  module

theorem fullRootExteriorCubicIncidenceOne_eq_zero
    (r n : ℕ) :
    fullRootExteriorCubicIncidenceOne r n = 0 := by
  exact fullRootExteriorBracket_incidence_sum_zero r n

theorem fullRootExteriorBracketUnordered_mul_self_zero
    (r n : ℕ) :
    fullRootExteriorBracketUnordered r n *
      fullRootExteriorBracketUnordered r n = 0 := by
  have h := fullRootExteriorBracketUnordered_square_eq_cubicIncidences r n
  rw [fullRootExteriorCubicIncidenceTwo_eq_neg,
    fullRootExteriorCubicIncidenceThree_eq,
    fullRootExteriorCubicIncidenceFour_eq_neg,
    fullRootExteriorCubicIncidenceOne_eq_zero] at h
  simp only [neg_zero, sub_zero, add_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

theorem fullRootExteriorBracket_mul_self_zero
    (r n : ℕ) :
    fullRootExteriorBracket r n * fullRootExteriorBracket r n = 0 := by
  have h := fullRootExteriorBracketUnordered_mul_self_zero r n
  rw [fullRootExteriorBracketUnordered_eq_two_smul] at h
  have hfour :
      (4 : ℝ) •
        (fullRootExteriorBracket r n * fullRootExteriorBracket r n) = 0 := by
    calc
      _ = ((2 : ℝ) • fullRootExteriorBracket r n) *
            ((2 : ℝ) • fullRootExteriorBracket r n) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul]
        norm_num
      _ = 0 := h
  exact (smul_eq_zero.mp hfour).resolve_left (by norm_num)

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The positive root graded mixed decidable eq used in the spherical-code argument. -/
local instance positiveRootGradedMixedDecidableEq (r : ℕ) :
    DecidableEq (PositiveRoot r) :=
  (positiveRootLinearOrder r).toDecidableEq

theorem fullRootExteriorAction_zeroExtension_of_card_ne
    {r n k : ℕ} (f : RootPolynomialChain r n (k + 1))
    (S : Finset (PositiveRoot r)) (hS : S.card ≠ k) :
    fullRootExteriorAction r n
        (rootPolynomialChainZeroExtension r n (k + 1) f) S = 0 := by
  classical
  unfold fullRootExteriorAction
  simp only [LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro α _
  unfold fullRootExteriorActionAtom
  simp only [Module.End.mul_apply, fullRootExteriorPolynomialAction_apply]
  by_cases hα : α ∈ S
  · simp only [actualExteriorRootContraction_apply, hα, ↓reduceIte, map_zero, ]
  · have hcard : (insert α S).card ≠ k + 1 := by
      rw [Finset.card_insert_of_notMem hα]
      omega
    simp only [actualExteriorRootContraction_apply, hα, ↓reduceIte,
      rootPolynomialChainZeroExtension_apply, not_false_eq_true, Finset.card_insert_of_notMem,
      Nat.add_right_cancel_iff, hS, ↓reduceDIte, smul_zero, map_zero, ]

theorem fullRootExteriorAction_zeroExtension_eq_zeroExtension
    {r n k : ℕ} (f : RootPolynomialChain r n (k + 1)) :
    fullRootExteriorAction r n
        (rootPolynomialChainZeroExtension r n (k + 1) f) =
      rootPolynomialChainZeroExtension r n k
        (rootActionBoundary r n k f) := by
  classical
  funext S
  by_cases hS : S.card = k
  · rw [rootPolynomialChainZeroExtension_apply, dite_eq_left hS]
    exact fullRootExteriorAction_zeroExtension_apply f ⟨S, hS⟩
  · rw [fullRootExteriorAction_zeroExtension_of_card_ne f S hS]
    simp only [rootPolynomialChainZeroExtension_apply, hS, ↓reduceDIte]

theorem fullRootExteriorBracketAtom_zeroExtension_of_card_ne
    {r n k : ℕ} (f : RootPolynomialChain r n (k + 1))
    (S : Finset (PositiveRoot r)) (hS : S.card ≠ k)
    (α β γ : PositiveRoot r) :
    fullRootExteriorBracketAtom r n α β γ
        (rootPolynomialChainZeroExtension r n (k + 1) f) S = 0 := by
  classical
  simp only [fullRootExteriorBracketAtom, Module.End.mul_apply,
    actualExteriorRootCreation_apply, actualExteriorRootContraction_apply]
  by_cases hγ : γ ∈ S
  · by_cases hβ : β ∈ S.erase γ
    · simp only [hγ, hβ, ite_true, smul_zero]
    · by_cases hα : α ∈ insert β (S.erase γ)
      · simp only [hγ, hβ, hα, ite_true, ite_false, smul_zero]
      · have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨γ, hγ⟩
        have hcard : (insert α (insert β (S.erase γ))).card ≠ k + 1 := by
          rw [Finset.card_insert_of_notMem hα,
            Finset.card_insert_of_notMem hβ,
            Finset.card_erase_of_mem hγ]
          omega
        simp only [hγ, hβ, hα, ite_true, ite_false,
          rootPolynomialChainZeroExtension_apply, dite_eq_right hcard,
          smul_zero]
  · simp only [hγ, ite_false]

theorem fullRootExteriorBracket_zeroExtension_of_card_ne
    {r n k : ℕ} (f : RootPolynomialChain r n (k + 1))
    (S : Finset (PositiveRoot r)) (hS : S.card ≠ k) :
    fullRootExteriorBracket r n
        (rootPolynomialChainZeroExtension r n (k + 1) f) S = 0 := by
  classical
  unfold fullRootExteriorBracket
  simp only [LinearMap.sum_apply, Finset.sum_apply, apply_ite,
    ]
  apply Finset.sum_eq_zero
  intro α _
  apply Finset.sum_eq_zero
  intro β _
  split_ifs with hαβ
  · simp only [LinearMap.sum_apply, Finset.sum_apply,
      LinearMap.smul_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro γ _
    simp only [fullRootExteriorBracketAtom_zeroExtension_of_card_ne f S hS α β γ, smul_zero]
  · rfl

theorem fullRootExteriorBracket_zeroExtension_eq_zeroExtension_of_apply
    {r n k : ℕ} (f : RootPolynomialChain r n (k + 1))
    (happly : ∀ T : RootWedge r k,
      fullRootExteriorBracket r n
          (rootPolynomialChainZeroExtension r n (k + 1) f) T.val =
        rootBracketBoundary r n k f T) :
    fullRootExteriorBracket r n
        (rootPolynomialChainZeroExtension r n (k + 1) f) =
      rootPolynomialChainZeroExtension r n k
        (rootBracketBoundary r n k f) := by
  classical
  funext S
  by_cases hS : S.card = k
  · rw [rootPolynomialChainZeroExtension_apply, dite_eq_left hS]
    exact happly ⟨S, hS⟩
  · rw [fullRootExteriorBracket_zeroExtension_of_card_ne f S hS]
    simp only [rootPolynomialChainZeroExtension_apply, hS, ↓reduceDIte]

theorem rootActionBracketBoundary_mixed_square_eq_zero_of_bridge
    {r n k : ℕ} (f : RootPolynomialChain r n (k + 2))
    (T : RootWedge r k)
    (hbridge : ∀ (j : ℕ) (g : RootPolynomialChain r n (j + 1))
      (U : RootWedge r j),
      fullRootExteriorBracket r n
          (rootPolynomialChainZeroExtension r n (j + 1) g) U.val =
        rootBracketBoundary r n j g U) :
    rootActionBoundary r n k
          (rootActionBoundary r n (k + 1) f) T +
        rootActionBoundary r n k
          (rootBracketBoundary r n (k + 1) f) T +
        rootBracketBoundary r n k
          (rootActionBoundary r n (k + 1) f) T = 0 := by
  classical
  have hB {j : ℕ} (g : RootPolynomialChain r n (j + 1)) :
      fullRootExteriorBracket r n
          (rootPolynomialChainZeroExtension r n (j + 1) g) =
        rootPolynomialChainZeroExtension r n j
          (rootBracketBoundary r n j g) :=
    fullRootExteriorBracket_zeroExtension_eq_zeroExtension_of_apply
      g (hbridge j g)
  have hfull := congrArg
    (fun L : Module.End ℝ (FullRootExteriorPolynomialChain r n) =>
      L (rootPolynomialChainZeroExtension r n (k + 2) f) T.val)
    (fullRootExteriorAction_square_add_mixed_eq_zero r n)
  simp only [LinearMap.add_apply, Pi.add_apply, Module.End.mul_apply,
    LinearMap.zero_apply, Pi.zero_apply] at hfull
  rw [fullRootExteriorAction_zeroExtension_eq_zeroExtension f,
    hB f] at hfull
  rw [fullRootExteriorAction_zeroExtension_apply,
    fullRootExteriorAction_zeroExtension_apply,
    hbridge] at hfull
  exact hfull

theorem fullRootExteriorBracket_zeroExtension_eq_zeroExtension
    {r n k : ℕ} (f : RootPolynomialChain r n (k + 1)) :
    fullRootExteriorBracket r n
        (rootPolynomialChainZeroExtension r n (k + 1) f) =
      rootPolynomialChainZeroExtension r n k
        (rootBracketBoundary r n k f) := by
  apply fullRootExteriorBracket_zeroExtension_eq_zeroExtension_of_apply
  intro T
  exact fullRootExteriorBracket_zeroExtension_apply f T

theorem rootActionBracketBoundary_mixed_square_eq_zero
    {r n k : ℕ} (f : RootPolynomialChain r n (k + 2))
    (T : RootWedge r k) :
    rootActionBoundary r n k
          (rootActionBoundary r n (k + 1) f) T +
        rootActionBoundary r n k
          (rootBracketBoundary r n (k + 1) f) T +
        rootBracketBoundary r n k
          (rootActionBoundary r n (k + 1) f) T = 0 := by
  apply rootActionBracketBoundary_mixed_square_eq_zero_of_bridge f T
  intro j g U
  exact fullRootExteriorBracket_zeroExtension_apply g U

theorem rootBracketBoundary_comp_self_apply_eq_zero
    {r n k : ℕ} (f : RootPolynomialChain r n (k + 2))
    (T : RootWedge r k) :
    rootBracketBoundary r n k
        (rootBracketBoundary r n (k + 1) f) T = 0 := by
  have hfull := congrArg
    (fun L : Module.End ℝ (FullRootExteriorPolynomialChain r n) =>
      L (rootPolynomialChainZeroExtension r n (k + 2) f) T.val)
    (fullRootExteriorBracket_mul_self_zero r n)
  simp only [Module.End.mul_apply, LinearMap.zero_apply,
    Pi.zero_apply] at hfull
  rw [fullRootExteriorBracket_zeroExtension_eq_zeroExtension f,
    fullRootExteriorBracket_zeroExtension_apply] at hfull
  exact hfull

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

private theorem lowerHodgeExteriorStructureAtom_apply_metriccodes2_30c2550d
    {r n : ℕ} (α β γ : PositiveRoot r)
    (f : FullRootExteriorPolynomialChain r n)
    (S : Finset (PositiveRoot r)) :
    (fullRootExteriorPolynomialAction r n γ *
      (actualExteriorRootCreation (PolynomialSpace r n) α *
        actualExteriorRootContraction (PolynomialSpace r n) β)) f S =
      if _hα : α ∈ S then
        if _hβ : β ∈ S.erase α then 0
        else (realExteriorRootSign S α *
            realExteriorRootSign (insert β (S.erase α)) β) •
          positiveRootOperator n γ (f (insert β (S.erase α)))
      else 0 := by
  classical
  by_cases hα : α ∈ S
  · by_cases hβ : β ∈ S.erase α
    · simp only [Module.End.mul_apply, fullRootExteriorPolynomialAction_apply,
        actualExteriorRootCreation_apply, actualExteriorRootContraction_apply,
        hα, hβ, ite_true, dite_true]
      split
      · simp only [smul_zero, map_zero]
      · next h =>
          exfalso
          apply h
          simpa only [Finset.mem_erase] using hβ
    · simp only [Module.End.mul_apply, fullRootExteriorPolynomialAction_apply,
        actualExteriorRootCreation_apply, actualExteriorRootContraction_apply,
        hα, hβ, ite_true, dite_true, dite_false, map_smul]
      split
      · next h =>
          exfalso
          apply hβ
          simpa only [Finset.mem_erase] using h
      · simp only [map_smul, smul_smul]
        congr 2
        · congr 1
          ext δ
          simp only [Finset.mem_insert, Finset.mem_erase, ne_eq]
        · congr 1
          ext δ
          simp only [Finset.mem_insert, Finset.mem_erase, ne_eq]
  · simp only [Module.End.mul_apply, fullRootExteriorPolynomialAction_apply,
      actualExteriorRootCreation_apply, hα, ite_false, dite_false, map_zero]

theorem fullRootExteriorLowerRootStructureIncidence_zeroExtension_apply
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    fullRootExteriorLowerRootStructureIncidence r n
        (rootPolynomialChainZeroExtension r n k
          (rootJointHarmonicPolynomialInclusion n lam k f)) S.val.val =
      -(((rootJointHarmonicActionLowerRootStructureCross n lam k f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) := by
  classical
  rw [rootJointHarmonicActionLowerRootStructureCross_apply_coe,
    ← Finset.sum_neg_distrib]
  unfold fullRootExteriorLowerRootStructureIncidence
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hα : α ∈ S.val.val
  · rw [dite_eq_left hα, ← Finset.sum_neg_distrib]
    have hkpos : 0 < k := by
      have hcardpos : 0 < S.val.val.card :=
        Finset.card_pos.mpr ⟨α, hα⟩
      simpa only [gt_iff_lt, S.val.property] using hcardpos
    apply Finset.sum_congr rfl
    intro β _
    by_cases hβ : β ∈ S.val.val
    · rw [dite_eq_left hβ]
      simp only [neg_zero]
      apply Finset.sum_eq_zero
      intro γ _
      by_cases heq : β = α
      · subst β
        simp only [rootStructureConstant_output_eq_right_zero, Module.End.mul_apply,
          fullRootExteriorPolynomialAction_apply, actualExteriorRootCreation_apply,
          actualExteriorRootContraction_apply, Finset.mem_erase, ne_eq, not_true_eq_false,
          false_and, ↓reduceIte, rootPolynomialChainZeroExtension_apply, not_false_eq_true,
          Finset.card_insert_of_notMem, smul_dite, smul_zero, positiveRootOperator_apply,
          polarization_apply, zero_smul]
      · have herase : β ∈ S.val.val.erase α := by
          simp only [Finset.mem_erase, ne_eq, heq, not_false_eq_true, hβ, and_self]
        rw [lowerHodgeExteriorStructureAtom_apply_metriccodes2_30c2550d]
        simp only [hα, ↓reduceDIte, herase, smul_zero]
    · rw [dite_eq_right hβ]
      have herase : β ∉ S.val.val.erase α := by
        exact fun h => hβ (Finset.mem_of_mem_erase h)
      by_cases hadm : ∀ i,
          0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i
      · rw [dite_eq_left hadm, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro γ _
        by_cases hγ : rootStructureConstant α γ β = 0
        · rw [dite_eq_left hγ]
          have hγ' : rootStructureConstant γ α β = 0 := by
            rw [rootStructureConstant_swap, hγ, neg_zero]
          simp only [hγ', Module.End.mul_apply, fullRootExteriorPolynomialAction_apply,
            actualExteriorRootCreation_apply, actualExteriorRootContraction_apply, Finset.mem_erase,
            ne_eq, rootPolynomialChainZeroExtension_apply, smul_dite, smul_zero, smul_ite,
            positiveRootOperator_apply, polarization_apply, zero_smul, neg_zero]
        · rw [dite_eq_right hγ, lowerHodgeExteriorStructureAtom_apply_metriccodes2_30c2550d]
          simp only [hα, herase, ↓reduceDIte]
          have hcard : (insert β (S.val.val.erase α)).card = k := by
            rw [Finset.card_insert_of_notMem herase,
              Finset.card_erase_of_mem hα, S.val.property]
            omega
          let W : RootWedge r k :=
            ⟨insert β (S.val.val.erase α), hcard⟩
          let U : AdmissibleRootWedge lam k := ⟨W, hadm⟩
          have hswap :
              rootAdmissibleSwap lam S α β hα hβ hadm = U := by
            apply Subtype.ext
            apply Subtype.ext
            rfl
          have hinclusion :
              rootPolynomialChainZeroExtension r n k
                  (rootJointHarmonicPolynomialInclusion n lam k f)
                  (insert β (S.val.val.erase α)) =
                ((f U).val : PolynomialSpace r n) := by
            change
              rootPolynomialChainZeroExtension r n k
                (rootJointHarmonicPolynomialInclusion n lam k f) W.val = _
            rw [rootPolynomialChainZeroExtension_wedge]
            change rootJointHarmonicPolynomialInclusion n lam k f U.val = _
            exact rootJointHarmonicPolynomialInclusion_apply_admissible lam f U
          rw [hinclusion, hswap, rootStructureConstant_swap α γ β]
          change
            (-rootStructureConstant α γ β) •
              ((realExteriorRootSign S.val.val α *
                realExteriorRootSign (insert β (S.val.val.erase α)) β) •
                positiveRootOperator n γ
                  ((f U).val : PolynomialSpace r n)) =
              -((rootSwapExteriorHodgeSign S α β *
                rootStructureConstant α γ β) •
                polarization r n (positiveRootSecond γ)
                  (positiveRootFirst γ) ((f U).val : PolynomialSpace r n))
          unfold rootSwapExteriorHodgeSign positiveRootOperator
          rw [smul_smul, ← neg_smul]
          congr 1
          ring
      · rw [dite_eq_right hadm]
        simp only [neg_zero]
        apply Finset.sum_eq_zero
        intro γ _
        rw [lowerHodgeExteriorStructureAtom_apply_metriccodes2_30c2550d]
        simp only [hα, herase, ↓reduceDIte]
        have hcard : (insert β (S.val.val.erase α)).card = k := by
          rw [Finset.card_insert_of_notMem herase,
            Finset.card_erase_of_mem hα, S.val.property]
          omega
        let W : RootWedge r k :=
          ⟨insert β (S.val.val.erase α), hcard⟩
        have hzero :
            rootJointHarmonicPolynomialInclusion n lam k f W = 0 := by
          simp only [rootJointHarmonicPolynomialInclusion, LinearMap.coe_mk, AddHom.coe_mk, hadm,
            ↓reduceDIte, W]
        change
          rootStructureConstant γ α β •
            ((realExteriorRootSign S.val.val α *
              realExteriorRootSign (insert β (S.val.val.erase α)) β) •
              positiveRootOperator n γ
                (rootPolynomialChainZeroExtension r n k
                  (rootJointHarmonicPolynomialInclusion n lam k f) W.val)) = 0
        rw [rootPolynomialChainZeroExtension_wedge, hzero, map_zero]
        simp only [smul_zero]
  · rw [dite_eq_right hα]
    simp only [neg_zero]
    apply Finset.sum_eq_zero
    intro β _
    apply Finset.sum_eq_zero
    intro γ _
    rw [lowerHodgeExteriorStructureAtom_apply_metriccodes2_30c2550d]
    simp only [hα, ↓reduceDIte, smul_zero]

section ExteriorTranspose

/-- The positive root hodge lower decidable eq used in the spherical-code argument. -/
local instance positiveRootHodgeLowerDecidableEq (r : ℕ) :
    DecidableEq (PositiveRoot r) :=
  (positiveRootLinearOrder r).toDecidableEq

theorem actualOrderedRootBracketCoboundaryAtom_single_transpose
    {r n k : ℕ} (S : RootWedge r (k + 1)) (T : RootWedge r k)
    (α β γ : PositiveRoot r) (p : PolynomialSpace r n) :
    (actualExteriorRootCreation (PolynomialSpace r n) α *
      (actualExteriorRootCreation (PolynomialSpace r n) β *
        actualExteriorRootContraction (PolynomialSpace r n) γ))
        (Pi.single T.val p) S.val =
      fullRootExteriorBracketAtom r n α β γ
        (Pi.single S.val p) T.val := by
  classical
  rw [fullRootExteriorBracketAtom_single_apply]
  simp only [Module.End.mul_apply, actualExteriorRootCreation_apply,
    actualExteriorRootContraction_apply, Pi.single_apply]
  by_cases hα : α ∈ S.val
  · by_cases hβ : β ∈ S.val.erase α
    · by_cases hγ : γ ∈ (S.val.erase α).erase β
      · simp only [hα, ↓reduceIte, hβ, hγ, smul_zero, not_true_eq_false, Finset.insert_eq_of_mem,
          false_and, and_false]
      · by_cases hT : T.val = insert γ ((S.val.erase α).erase β)
        · rw [hT]
          simp only [hα, ↓reduceIte, hβ, hγ, smul_smul, not_false_eq_true, and_self, mul_assoc]
        · simp only [hα, ↓reduceIte, hβ, hγ, Ne.symm hT, smul_zero, not_false_eq_true, hT,
            and_false]
    · simp only [hα, ↓reduceIte, hβ, smul_zero, not_false_eq_true, Finset.erase_eq_of_notMem,
        Finset.mem_erase, ne_eq, not_and, false_and, and_false]
  · simp only [hα, ↓reduceIte, not_false_eq_true, Finset.erase_eq_of_notMem, Finset.mem_erase,
      ne_eq, not_and, false_and]

theorem actualOrderedRootBracketCoboundary_single_apply
    {r n k : ℕ} (S : RootWedge r (k + 1)) (T : RootWedge r k)
    (p : PolynomialSpace r n) :
    actualOrderedRootBracketCoboundary
        (M := PolynomialSpace r n) (r := r)
          (Pi.single T.val p) S.val =
      rootBracketBoundaryCoefficient S T • p := by
  classical
  rw [← fullRootExteriorBracket_single_apply S T p,
    actualOrderedRootBracketCoboundary_eq_ordered_sum]
  unfold fullRootExteriorBracket
  simp only [LinearMap.sum_apply, Finset.sum_apply, ite_apply,
    apply_ite, LinearMap.zero_apply, Pi.zero_apply,
    LinearMap.smul_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  split_ifs with hαβ
  · apply Finset.sum_congr rfl
    intro γ _
    congr 1
    exact actualOrderedRootBracketCoboundaryAtom_single_transpose
      S T α β γ p
  · rfl

end ExteriorTranspose

theorem actualOrderedRootBracketCoboundary_zeroExtension_apply
    {r n k : ℕ} (f : RootPolynomialChain r n k)
    (S : RootWedge r (k + 1)) :
    actualOrderedRootBracketCoboundary
        (M := PolynomialSpace r n) (r := r)
          (rootPolynomialChainZeroExtension r n k f) S.val =
      rootBracketCoboundary r n k f S := by
  classical
  apply actualOrderedRootBracketCoboundary_zeroExtension_apply_of_single
  intro T p
  convert actualOrderedRootBracketCoboundary_single_apply S T p using 1
  apply congrArg (fun h : FullRootExteriorPolynomialChain r n =>
    actualOrderedRootBracketCoboundary
      (M := PolynomialSpace r n) (r := r) h S.val)
  funext U
  by_cases hU : U = T.val <;> simp [hU]

theorem actualOrderedRootBracketCoboundary_zeroExtension
    {r n k : ℕ} (f : RootPolynomialChain r n k) :
    actualOrderedRootBracketCoboundary
        (M := PolynomialSpace r n) (r := r)
          (rootPolynomialChainZeroExtension r n k f) =
      rootPolynomialChainZeroExtension r n (k + 1)
        (rootBracketCoboundary r n k f) := by
  classical
  funext S
  by_cases hS : S.card = k + 1
  · rw [rootPolynomialChainZeroExtension_apply, dite_eq_left hS]
    exact actualOrderedRootBracketCoboundary_zeroExtension_apply
      f ⟨S, hS⟩
  · rw [actualOrderedRootBracketCoboundary_zeroExtension_of_card_ne
      f S hS]
    simp only [rootPolynomialChainZeroExtension_apply, hS, ↓reduceDIte]

theorem rootJointHarmonicBracketActionMixed_add_lowerStructure_eq_zero
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    rootJointHarmonicBracketActionMixed n lam k +
      rootJointHarmonicActionLowerRootStructureCross n lam (k + 1) = 0 := by
  apply LinearMap.ext
  intro f
  funext S
  apply Subtype.ext
  apply Subtype.ext
  let g : RootPolynomialChain r n (k + 1) :=
    rootJointHarmonicPolynomialInclusion n lam (k + 1) f
  have hmixed := LinearMap.congr_fun
    (rootJointHarmonicPolynomialInclusion_bracketActionMixed_intertwines lam) f
  have hmixedS := congrFun hmixed S.val
  have hfull := congrArg
    (fun L : Module.End ℝ (FullRootExteriorPolynomialChain r n) =>
      L (rootPolynomialChainZeroExtension r n (k + 1) g) S.val.val)
    (fullRootExteriorAction_orderedBracketCoboundary_anticommute
      (r := r) (n := n))
  simp only [LinearMap.add_apply, Pi.add_apply,
    Module.End.mul_apply] at hfull
  rw [actualOrderedRootBracketCoboundary_zeroExtension g,
    fullRootExteriorAction_zeroExtension_eq_zeroExtension,
    fullRootExteriorAction_zeroExtension_eq_zeroExtension g,
    actualOrderedRootBracketCoboundary_zeroExtension,
    rootPolynomialChainZeroExtension_wedge,
    rootPolynomialChainZeroExtension_wedge] at hfull
  change
    (((rootJointHarmonicBracketActionMixed n lam k f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) +
      (((rootJointHarmonicActionLowerRootStructureCross n lam (k + 1) f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) = 0
  change
    rootJointHarmonicPolynomialInclusion n lam (k + 1)
        (rootJointHarmonicBracketActionMixed n lam k f) S.val =
      rootPolynomialBracketActionMixed r n k g S.val at hmixedS
  rw [rootJointHarmonicPolynomialInclusion_apply_admissible] at hmixedS
  rw [hmixedS]
  change
    rootBracketCoboundary r n k (rootActionBoundary r n k g) S.val +
        rootActionBoundary r n (k + 1)
          (rootBracketCoboundary r n (k + 1) g) S.val +
      (((rootJointHarmonicActionLowerRootStructureCross n lam (k + 1) f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) = 0
  rw [add_comm
    (rootBracketCoboundary r n k (rootActionBoundary r n k g) S.val)
    (rootActionBoundary r n (k + 1)
      (rootBracketCoboundary r n (k + 1) g) S.val), hfull]
  rw [fullRootExteriorLowerRootStructureIncidence_zeroExtension_apply lam f S]
  exact neg_add_cancel _

end

section


open scoped BigOperators

variable {ι M : Type*} [LinearOrder ι]
variable [AddCommGroup M] [Module ℝ M]

theorem actualExteriorRootCreation_creation_contraction_contraction_anticommute
    (a b c d : ι) :
    actualExteriorRootCreation M a *
          (actualExteriorRootCreation M b *
            (actualExteriorRootContraction M c *
              actualExteriorRootContraction M d)) +
        (actualExteriorRootCreation M b *
          (actualExteriorRootContraction M c *
            actualExteriorRootContraction M d)) *
          actualExteriorRootCreation M a =
      (if a = d then
        actualExteriorRootCreation M b *
          actualExteriorRootContraction M c else 0) -
      (if a = c then
        actualExteriorRootCreation M b *
          actualExteriorRootContraction M d else 0) := by
  have hac := actualExteriorRootContraction_creation_anticommute
    (M := M) c a
  have had := actualExteriorRootContraction_creation_anticommute
    (M := M) d a
  have hab := actualExteriorRootCreation_anticommute
    (M := M) a b
  calc
    _ =
        -(actualExteriorRootCreation M b *
          (actualExteriorRootContraction M c *
            actualExteriorRootCreation M a +
            actualExteriorRootCreation M a *
              actualExteriorRootContraction M c) *
              actualExteriorRootContraction M d) +
        actualExteriorRootCreation M b *
          actualExteriorRootContraction M c *
            (actualExteriorRootContraction M d *
              actualExteriorRootCreation M a +
              actualExteriorRootCreation M a *
                actualExteriorRootContraction M d) +
        (actualExteriorRootCreation M a *
          actualExteriorRootCreation M b +
          actualExteriorRootCreation M b *
            actualExteriorRootCreation M a) *
              actualExteriorRootContraction M c *
                actualExteriorRootContraction M d := by
          noncomm_ring
    _ = _ := by
      rw [hac, had, hab]
      by_cases hc : c = a
      · subst c
        by_cases hd : d = a
        · subst d
          simp only [↓reduceIte, mul_one, neg_add_cancel, zero_mul, add_zero, sub_self]
        · have hda : a ≠ d := Ne.symm hd
          simp only [↓reduceIte, mul_one, hd, mul_zero, add_zero, zero_mul, hda, zero_sub]
      · have hac' : a ≠ c := Ne.symm hc
        by_cases hd : d = a
        · subst d
          simp only [hc, ↓reduceIte, mul_zero, zero_mul, neg_zero, mul_one, zero_add, add_zero,
            hac', sub_zero]
        · have had' : a ≠ d := Ne.symm hd
          simp only [hc, ↓reduceIte, mul_zero, zero_mul, neg_zero, hd, add_zero, had', hac',
            sub_self]

end

section


open scoped BigOperators

attribute [local instance] Classical.propDecidable

open MetricCodes.Spherical.HigherHarmonicYoung

theorem fullRootExteriorUpperPolynomialAction_creation_commute
    {r n : ℕ} (α β : PositiveRoot r) :
    fullRootExteriorUpperPolynomialAction r n α *
        actualExteriorRootCreation (PolynomialSpace r n) β =
      actualExteriorRootCreation (PolynomialSpace r n) β *
        fullRootExteriorUpperPolynomialAction r n α := by
  apply LinearMap.ext
  intro f
  funext S
  simp only [Module.End.mul_apply,
    fullRootExteriorUpperPolynomialAction_apply,
    actualExteriorRootCreation_apply]
  split_ifs <;> simp

theorem fullRootExteriorUpperPolynomialAction_contraction_commute
    {r n : ℕ} (α β : PositiveRoot r) :
    fullRootExteriorUpperPolynomialAction r n α *
        actualExteriorRootContraction (PolynomialSpace r n) β =
      actualExteriorRootContraction (PolynomialSpace r n) β *
        fullRootExteriorUpperPolynomialAction r n α := by
  apply LinearMap.ext
  intro f
  funext S
  simp only [Module.End.mul_apply,
    fullRootExteriorUpperPolynomialAction_apply,
    actualExteriorRootContraction_apply]
  split_ifs <;> simp

private def fullRootExteriorUpperActionAtom (r n : ℕ) (α : PositiveRoot r) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  fullRootExteriorUpperPolynomialAction r n α *
    actualExteriorRootCreation (PolynomialSpace r n) α

theorem fullRootExteriorUpperPolynomialAction_bracketAtom_commute
    {r n : ℕ} (δ α β γ : PositiveRoot r) :
    fullRootExteriorUpperPolynomialAction r n δ *
        fullRootExteriorBracketAtom r n α β γ =
      fullRootExteriorBracketAtom r n α β γ *
        fullRootExteriorUpperPolynomialAction r n δ := by
  let P := fullRootExteriorUpperPolynomialAction r n δ
  let E := actualExteriorRootCreation (PolynomialSpace r n) γ
  let Cβ := actualExteriorRootContraction (PolynomialSpace r n) β
  let Cα := actualExteriorRootContraction (PolynomialSpace r n) α
  have hE : P * E = E * P :=
    fullRootExteriorUpperPolynomialAction_creation_commute δ γ
  have hβ : P * Cβ = Cβ * P :=
    fullRootExteriorUpperPolynomialAction_contraction_commute δ β
  have hα : P * Cα = Cα * P :=
    fullRootExteriorUpperPolynomialAction_contraction_commute δ α
  change P * (E * (Cβ * Cα)) = (E * (Cβ * Cα)) * P
  calc
    P * (E * (Cβ * Cα)) = (P * E) * (Cβ * Cα) := by noncomm_ring
    _ = (E * P) * (Cβ * Cα) := by rw [hE]
    _ = E * (P * Cβ) * Cα := by noncomm_ring
    _ = E * (Cβ * P) * Cα := by rw [hβ]
    _ = E * Cβ * (P * Cα) := by noncomm_ring
    _ = E * Cβ * (Cα * P) := by rw [hα]
    _ = (E * (Cβ * Cα)) * P := by noncomm_ring

theorem fullRootExteriorUpperActionAtom_bracketAtom_anticommute
    {r n : ℕ} (δ α β γ : PositiveRoot r) :
    fullRootExteriorUpperActionAtom r n δ *
        fullRootExteriorBracketAtom r n α β γ +
      fullRootExteriorBracketAtom r n α β γ *
        fullRootExteriorUpperActionAtom r n δ =
      (if δ = α then
        fullRootExteriorUpperPolynomialAction r n α *
          (actualExteriorRootCreation (PolynomialSpace r n) γ *
            actualExteriorRootContraction (PolynomialSpace r n) β)
        else 0) -
      (if δ = β then
        fullRootExteriorUpperPolynomialAction r n β *
          (actualExteriorRootCreation (PolynomialSpace r n) γ *
            actualExteriorRootContraction (PolynomialSpace r n) α)
        else 0) := by
  classical
  let P := fullRootExteriorUpperPolynomialAction r n δ
  let E := actualExteriorRootCreation (PolynomialSpace r n) δ
  let J := fullRootExteriorBracketAtom r n α β γ
  let Eγ := actualExteriorRootCreation (PolynomialSpace r n) γ
  let Cβ := actualExteriorRootContraction (PolynomialSpace r n) β
  let Cα := actualExteriorRootContraction (PolynomialSpace r n) α
  have hcomm : P * J = J * P :=
    fullRootExteriorUpperPolynomialAction_bracketAtom_commute δ α β γ
  have hcar : E * J + J * E =
      (if δ = α then Eγ * Cβ else 0) -
        (if δ = β then Eγ * Cα else 0) := by
    by_cases hδα : δ = α <;> by_cases hδβ : δ = β
    all_goals
      simpa [E, J, Eγ, Cβ, Cα, fullRootExteriorBracketAtom,
        hδα, hδβ] using
        actualExteriorRootCreation_creation_contraction_contraction_anticommute
          (M := PolynomialSpace r n) δ γ β α
  change
    (P * E) * J + J * (P * E) =
      (if δ = α then
        fullRootExteriorUpperPolynomialAction r n α * (Eγ * Cβ) else 0) -
      (if δ = β then
        fullRootExteriorUpperPolynomialAction r n β * (Eγ * Cα) else 0)
  calc
    (P * E) * J + J * (P * E) =
        P * (E * J) + (J * P) * E := by noncomm_ring
    _ = P * (E * J) + (P * J) * E := by rw [← hcomm]
    _ = P * (E * J + J * E) := by noncomm_ring
    _ = P * ((if δ = α then Eγ * Cβ else 0) -
        (if δ = β then Eγ * Cα else 0)) := by rw [hcar]
    _ = _ := by
      split_ifs <;> simp_all [P, mul_sub]

theorem fullRootExteriorActionCoboundary_bracketAtom_anticommute
    {r n : ℕ} (α β γ : PositiveRoot r) :
    fullRootExteriorActionCoboundary r n *
        fullRootExteriorBracketAtom r n α β γ +
      fullRootExteriorBracketAtom r n α β γ *
        fullRootExteriorActionCoboundary r n =
      fullRootExteriorUpperPolynomialAction r n α *
        (actualExteriorRootCreation (PolynomialSpace r n) γ *
          actualExteriorRootContraction (PolynomialSpace r n) β) -
      fullRootExteriorUpperPolynomialAction r n β *
        (actualExteriorRootCreation (PolynomialSpace r n) γ *
          actualExteriorRootContraction (PolynomialSpace r n) α) := by
  classical
  change
    (∑ δ : PositiveRoot r, fullRootExteriorUpperActionAtom r n δ) *
        fullRootExteriorBracketAtom r n α β γ +
      fullRootExteriorBracketAtom r n α β γ *
        (∑ δ : PositiveRoot r, fullRootExteriorUpperActionAtom r n δ) = _
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp_rw [fullRootExteriorUpperActionAtom_bracketAtom_anticommute,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem fullRootExteriorActionCoboundary_bracket_anticommute
    (r n : ℕ) :
    fullRootExteriorActionCoboundary r n *
        fullRootExteriorBracket r n +
      fullRootExteriorBracket r n *
        fullRootExteriorActionCoboundary r n =
      ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if α < β then
          ∑ γ : PositiveRoot r,
            rootStructureConstant α β γ •
              (fullRootExteriorUpperPolynomialAction r n α *
                (actualExteriorRootCreation (PolynomialSpace r n) γ *
                  actualExteriorRootContraction (PolynomialSpace r n) β) -
               fullRootExteriorUpperPolynomialAction r n β *
                (actualExteriorRootCreation (PolynomialSpace r n) γ *
                  actualExteriorRootContraction (PolynomialSpace r n) α))
        else 0 := by
  classical
  unfold fullRootExteriorBracket
  simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul,
    mul_zero, zero_mul, mul_smul_comm, smul_mul_assoc]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro β _
  split_ifs with hαβ
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro γ _
    rw [← smul_add,
      fullRootExteriorActionCoboundary_bracketAtom_anticommute]
  · simp only [add_zero]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem fullRootExteriorUpperStructureAtom_apply
    {r n : ℕ} (α β γ : PositiveRoot r)
    (f : FullRootExteriorPolynomialChain r n)
    (S : Finset (PositiveRoot r)) :
    (fullRootExteriorUpperPolynomialAction r n γ *
      (actualExteriorRootCreation (PolynomialSpace r n) α *
        actualExteriorRootContraction (PolynomialSpace r n) β)) f S =
      if _hα : α ∈ S then
        if _hβ : β ∈ S.erase α then 0
        else (realExteriorRootSign S α *
            realExteriorRootSign (insert β (S.erase α)) β) •
          positiveRootUpperOperator n γ (f (insert β (S.erase α)))
      else 0 := by
  classical
  by_cases hα : α ∈ S
  · by_cases hβ : β ∈ S.erase α
    · simp only [Module.End.mul_apply, fullRootExteriorUpperPolynomialAction_apply,
        actualExteriorRootCreation_apply, actualExteriorRootContraction_apply,
        hα, hβ, ite_true, dite_true]
      split
      · simp only [smul_zero, map_zero]
      · next h =>
          exfalso
          apply h
          simpa only [Finset.mem_erase] using hβ
    · simp only [Module.End.mul_apply, fullRootExteriorUpperPolynomialAction_apply,
        actualExteriorRootCreation_apply, actualExteriorRootContraction_apply,
        hα, hβ, ite_true, dite_true, dite_false, map_smul]
      split
      · next h =>
          exfalso
          apply hβ
          simpa only [Finset.mem_erase] using h
      · simp only [map_smul, smul_smul]
        congr 2
        · congr 1
          ext δ
          simp only [Finset.mem_insert, Finset.mem_erase, ne_eq]
        · congr 1
          ext δ
          simp only [Finset.mem_insert, Finset.mem_erase, ne_eq]
  · simp only [Module.End.mul_apply, fullRootExteriorUpperPolynomialAction_apply,
      actualExteriorRootCreation_apply, hα, ite_false, dite_false, map_zero]

theorem rootJointHarmonicActionUpperRootStructureCross_apply_coe
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    (((rootJointHarmonicActionUpperRootStructureCross n lam k f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
      ∑ α : PositiveRoot r,
        if hα : α ∈ S.val.val then
          ∑ β : PositiveRoot r,
            if hβ : β ∈ S.val.val then 0
            else if hadm : ∀ i,
                0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i then
              ∑ γ : PositiveRoot r,
                if _hγ : rootStructureConstant β γ α = 0 then 0
                else (rootSwapExteriorHodgeSign S α β *
                    rootStructureConstant β γ α) •
                  polarization r n (positiveRootFirst γ) (positiveRootSecond γ)
                    ((f (rootAdmissibleSwap lam S α β hα hβ hadm)).val :
                      PolynomialSpace r n)
            else 0
        else 0 := by
  classical
  rw [rootJointHarmonicActionUpperRootStructureCross_apply]
  simp only [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with hα
  · simp only [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro β _
    split_ifs with hβ hadm
    · simp only [ZeroMemClass.coe_zero]
    · simp only [Submodule.coe_sum]
      apply Finset.sum_congr rfl
      intro γ _
      split_ifs with hγ
      · simp only [ZeroMemClass.coe_zero]
      · simp only [Submodule.coe_smul]
        rw [rootSwapUpperStructureEdge_coe]
    · simp only [ZeroMemClass.coe_zero]
  · simp only [ZeroMemClass.coe_zero]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

private def rootJointHarmonicActionBracketMixed {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1) :=
  (weightedExteriorActionCoboundary n lam k).comp
      (weightedRootBracketBoundary n lam k) +
    (weightedRootBracketBoundary n lam (k + 1)).comp
      (weightedExteriorActionCoboundary n lam (k + 1))

private def rootJointHarmonicFullMixedHodge {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1) :=
  (weightedExteriorActionCoboundary n lam k).comp
      (weightedRootBracketBoundary n lam k) +
    (weightedRootBracketCoboundary n lam k).comp
      (weightedExteriorActionDifferential n lam k) +
    (weightedExteriorActionDifferential n lam (k + 1)).comp
      (weightedRootBracketCoboundary n lam (k + 1)) +
    (weightedRootBracketBoundary n lam (k + 1)).comp
      (weightedExteriorActionCoboundary n lam (k + 1))

theorem rootJointHarmonicFullMixedHodge_eq_halves
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    rootJointHarmonicFullMixedHodge n lam k =
      rootJointHarmonicActionBracketMixed n lam k +
        ((weightedRootBracketCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedRootBracketCoboundary n lam (k + 1))) := by
  unfold rootJointHarmonicFullMixedHodge rootJointHarmonicActionBracketMixed
  abel

theorem rootJointHarmonicFullMixedHodge_eq_actionBracket_add_bracketAction
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    rootJointHarmonicFullMixedHodge n lam k =
      rootJointHarmonicActionBracketMixed n lam k +
        rootJointHarmonicBracketActionMixed n lam k := by
  rw [rootJointHarmonicFullMixedHodge_eq_halves]
  unfold rootJointHarmonicBracketActionMixed
  with_reducible rfl

theorem rootJointHarmonicFullMixedHodge_add_offDiagonal_eq_zero_of_halves
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (hupper : rootJointHarmonicActionBracketMixed n lam k +
      rootJointHarmonicActionUpperRootStructureCross n lam (k + 1) = 0)
    (hlower : rootJointHarmonicBracketActionMixed n lam k +
      rootJointHarmonicActionLowerRootStructureCross n lam (k + 1) = 0) :
    rootJointHarmonicFullMixedHodge n lam k +
      rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1) = 0 := by
  rw [rootJointHarmonicFullMixedHodge_eq_actionBracket_add_bracketAction]
  unfold rootJointHarmonicActionHodgeOffDiagonal
  calc
    (rootJointHarmonicActionBracketMixed n lam k +
        rootJointHarmonicBracketActionMixed n lam k) +
      (rootJointHarmonicActionUpperRootStructureCross n lam (k + 1) +
        rootJointHarmonicActionLowerRootStructureCross n lam (k + 1)) =
      (rootJointHarmonicActionBracketMixed n lam k +
        rootJointHarmonicActionUpperRootStructureCross n lam (k + 1)) +
      (rootJointHarmonicBracketActionMixed n lam k +
        rootJointHarmonicActionLowerRootStructureCross n lam (k + 1)) :=
      add_add_add_comm _ _ _ _
    _ = 0 := by rw [hupper, hlower, add_zero]

end

section


open MetricCodes.Spherical.HigherHarmonicYoung

private def rootPolynomialActionBracketMixed (r n k : ℕ) :
    RootPolynomialChain r n (k + 1) →ₗ[ℝ]
      RootPolynomialChain r n (k + 1) :=
  (rootActionCoboundary r n k).comp (rootBracketBoundary r n k) +
    (rootBracketBoundary r n (k + 1)).comp
      (rootActionCoboundary r n (k + 1))

theorem rootJointHarmonicPolynomialInclusion_actionBracketMixed_intertwines
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    (rootJointHarmonicPolynomialInclusion n lam (k + 1)).comp
        (rootJointHarmonicActionBracketMixed n lam k) =
      (rootPolynomialActionBracketMixed r n k).comp
        (rootJointHarmonicPolynomialInclusion n lam (k + 1)) := by
  apply LinearMap.ext
  intro f
  have hfirst := LinearMap.congr_fun
    (rootJointHarmonicPolynomialInclusion_actionCoboundary_intertwines
      (n := n) (k := k) lam)
    (weightedRootBracketBoundary n lam k f)
  have hsecond := congrArg (rootActionCoboundary r n k)
    (LinearMap.congr_fun
      (rootJointHarmonicPolynomialInclusion_bracket_intertwines
        (n := n) (k := k) lam) f)
  have hthird := LinearMap.congr_fun
    (rootJointHarmonicPolynomialInclusion_bracket_intertwines
      (n := n) (k := k + 1) lam)
    (weightedExteriorActionCoboundary n lam (k + 1) f)
  have hfourth := congrArg (rootBracketBoundary r n (k + 1))
    (LinearMap.congr_fun
      (rootJointHarmonicPolynomialInclusion_actionCoboundary_intertwines
        (n := n) (k := k + 1) lam) f)
  simp only [LinearMap.comp_apply, rootJointHarmonicActionBracketMixed,
    rootPolynomialActionBracketMixed, LinearMap.add_apply]
  rw [map_add]
  simp only [LinearMap.comp_apply] at hfirst hsecond hthird hfourth
  exact congrArg₂ (· + ·) (hfirst.trans hsecond) (hthird.trans hfourth)

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

attribute [local instance] Classical.propDecidable

private def fullRootExteriorUpperRootStructureIncidence (r n : ℕ) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  ∑ α : PositiveRoot r, ∑ β : PositiveRoot r, ∑ γ : PositiveRoot r,
    rootStructureConstant β γ α •
      (fullRootExteriorUpperPolynomialAction r n γ *
        (actualExteriorRootCreation (PolynomialSpace r n) α *
          actualExteriorRootContraction (PolynomialSpace r n) β))

theorem rootStructureConstant_output_eq_left_zero {r : ℕ}
    (α β : PositiveRoot r) : rootStructureConstant α β α = 0 := by
  calc
    rootStructureConstant α β α = -rootStructureConstant β α α :=
      rootStructureConstant_swap β α α
    _ = 0 := by rw [rootStructureConstant_output_eq_right_zero, neg_zero]

theorem sum_root_pairs_eq_ordered_add_reverse
    {r : ℕ} {V : Type*} [AddCommGroup V]
    (F : PositiveRoot r → PositiveRoot r → V)
    (hzero : ∀ α β, ¬ α < β → ¬ β < α → F α β = 0) :
    (∑ α : PositiveRoot r, ∑ β : PositiveRoot r, F α β) =
      ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if α < β then F α β + F β α else 0 := by
  classical
  have hsplit :
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r, F α β) =
        (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
          if α < β then F α β else 0) +
        (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
          if β < α then F α β else 0) := by
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    by_cases hαβ : α < β
    · have hβα : ¬ β < α := (lt_asymm hαβ)
      simp only [hαβ, ↓reduceIte, hβα, add_zero]
    · by_cases hβα : β < α
      · simp only [hαβ, ↓reduceIte, hβα, zero_add]
      · simp only [hzero α β hαβ hβα, hαβ, ↓reduceIte, hβα, add_zero]
  have hreverse :
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if β < α then F α β else 0) =
      (∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
        if α < β then F β α else 0) := by
    rw [Finset.sum_comm]
  rw [hsplit, hreverse, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro β _
  split_ifs <;> simp

theorem fullRootExteriorActionCoboundary_bracket_eq_neg_upperStructure
    (r n : ℕ) :
    fullRootExteriorActionCoboundary r n * fullRootExteriorBracket r n +
      fullRootExteriorBracket r n * fullRootExteriorActionCoboundary r n =
      -fullRootExteriorUpperRootStructureIncidence r n := by
  classical
  rw [fullRootExteriorActionCoboundary_bracket_anticommute]
  let F : PositiveRoot r → PositiveRoot r →
      Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
    fun α β => ∑ γ : PositiveRoot r,
      rootStructureConstant α β γ •
        (fullRootExteriorUpperPolynomialAction r n β *
          (actualExteriorRootCreation (PolynomialSpace r n) γ *
            actualExteriorRootContraction (PolynomialSpace r n) α))
  have hzero : ∀ α β : PositiveRoot r,
      ¬ α < β → ¬ β < α → F α β = 0 := by
    intro α β hαβ hβα
    dsimp [F]
    apply Finset.sum_eq_zero
    intro γ _
    rw [rootStructureConstant_eq_zero_of_incomparable α β γ hαβ hβα]
    simp only [zero_smul]
  have hsplit := sum_root_pairs_eq_ordered_add_reverse F hzero
  have hincidence : fullRootExteriorUpperRootStructureIncidence r n =
      ∑ α : PositiveRoot r, ∑ β : PositiveRoot r, F α β := by
    unfold fullRootExteriorUpperRootStructureIncidence
    dsimp [F]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.sum_comm]
  rw [hincidence, hsplit, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro β _
  split_ifs with hαβ
  · dsimp [F]
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro γ _
    rw [rootStructureConstant_swap β α γ]
    module
  · simp only [neg_zero]

theorem fullRootExteriorUpperRootStructureIncidence_zeroExtension_apply
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    fullRootExteriorUpperRootStructureIncidence r n
        (rootPolynomialChainZeroExtension r n k
          (rootJointHarmonicPolynomialInclusion n lam k f)) S.val.val =
      (((rootJointHarmonicActionUpperRootStructureCross n lam k f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) := by
  classical
  rw [rootJointHarmonicActionUpperRootStructureCross_apply_coe]
  unfold fullRootExteriorUpperRootStructureIncidence
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hα : α ∈ S.val.val
  · rw [dite_eq_left hα]
    have hkpos : 0 < k := by
      have hcardpos : 0 < S.val.val.card := Finset.card_pos.mpr ⟨α, hα⟩
      simpa only [gt_iff_lt, S.val.property] using hcardpos
    apply Finset.sum_congr rfl
    intro β _
    by_cases hβ : β ∈ S.val.val
    · rw [dite_eq_left hβ]
      apply Finset.sum_eq_zero
      intro γ _
      by_cases heq : β = α
      · subst β
        simp only [rootStructureConstant_output_eq_left_zero, Module.End.mul_apply,
          fullRootExteriorUpperPolynomialAction_apply, actualExteriorRootCreation_apply,
          actualExteriorRootContraction_apply, Finset.mem_erase, ne_eq, not_true_eq_false,
          false_and, ↓reduceIte, rootPolynomialChainZeroExtension_apply, not_false_eq_true,
          Finset.card_insert_of_notMem, smul_dite, smul_zero, positiveRootUpperOperator_apply,
          polarization_apply, zero_smul]
      · have herase : β ∈ S.val.val.erase α := by
          simp only [Finset.mem_erase, ne_eq, heq, not_false_eq_true, hβ, and_self]
        rw [fullRootExteriorUpperStructureAtom_apply]
        simp only [hα, ↓reduceDIte, herase, smul_zero]
    · rw [dite_eq_right hβ]
      have herase : β ∉ S.val.val.erase α := by
        exact fun h => hβ (Finset.mem_of_mem_erase h)
      by_cases hadm : ∀ i,
          0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i
      · rw [dite_eq_left hadm]
        apply Finset.sum_congr rfl
        intro γ _
        by_cases hγ : rootStructureConstant β γ α = 0
        · rw [dite_eq_left hγ]
          simp only [hγ, Module.End.mul_apply, fullRootExteriorUpperPolynomialAction_apply,
            actualExteriorRootCreation_apply, actualExteriorRootContraction_apply, Finset.mem_erase,
            ne_eq, rootPolynomialChainZeroExtension_apply, smul_dite, smul_zero, smul_ite,
            positiveRootUpperOperator_apply, polarization_apply, zero_smul]
        · rw [dite_eq_right hγ, fullRootExteriorUpperStructureAtom_apply]
          simp only [hα, herase]
          have hcard : (insert β (S.val.val.erase α)).card = k := by
            rw [Finset.card_insert_of_notMem herase,
              Finset.card_erase_of_mem hα, S.val.property]
            omega
          let W : RootWedge r k :=
            ⟨insert β (S.val.val.erase α), hcard⟩
          let U : AdmissibleRootWedge lam k := ⟨W, hadm⟩
          have hswap :
              rootAdmissibleSwap lam S α β hα hβ hadm = U := by
            apply Subtype.ext
            apply Subtype.ext
            rfl
          have hinclusion :
              rootPolynomialChainZeroExtension r n k
                  (rootJointHarmonicPolynomialInclusion n lam k f)
                  (insert β (S.val.val.erase α)) =
                ((f U).val : PolynomialSpace r n) := by
            change
              rootPolynomialChainZeroExtension r n k
                (rootJointHarmonicPolynomialInclusion n lam k f) W.val = _
            rw [rootPolynomialChainZeroExtension_wedge]
            change rootJointHarmonicPolynomialInclusion n lam k f U.val = _
            exact rootJointHarmonicPolynomialInclusion_apply_admissible lam f U
          rw [hinclusion, hswap]
          change
            rootStructureConstant β γ α •
              ((realExteriorRootSign S.val.val α *
                realExteriorRootSign (insert β (S.val.val.erase α)) β) •
                positiveRootUpperOperator n γ
                  ((f U).val : PolynomialSpace r n)) =
            (rootSwapExteriorHodgeSign S α β *
              rootStructureConstant β γ α) •
              polarization r n (positiveRootFirst γ)
                (positiveRootSecond γ) ((f U).val : PolynomialSpace r n)
          unfold rootSwapExteriorHodgeSign positiveRootUpperOperator
          rw [smul_smul]
          congr 1
          ring
      · rw [dite_eq_right hadm]
        apply Finset.sum_eq_zero
        intro γ _
        rw [fullRootExteriorUpperStructureAtom_apply]
        simp only [hα, herase]
        have hcard : (insert β (S.val.val.erase α)).card = k := by
          rw [Finset.card_insert_of_notMem herase,
            Finset.card_erase_of_mem hα, S.val.property]
          omega
        let W : RootWedge r k :=
          ⟨insert β (S.val.val.erase α), hcard⟩
        have hzero :
            rootJointHarmonicPolynomialInclusion n lam k f W = 0 := by
          simp only [rootJointHarmonicPolynomialInclusion, LinearMap.coe_mk, AddHom.coe_mk, hadm,
            ↓reduceDIte, W]
        change
          rootStructureConstant β γ α •
            ((realExteriorRootSign S.val.val α *
              realExteriorRootSign (insert β (S.val.val.erase α)) β) •
              positiveRootUpperOperator n γ
                (rootPolynomialChainZeroExtension r n k
                  (rootJointHarmonicPolynomialInclusion n lam k f) W.val)) = 0
        rw [rootPolynomialChainZeroExtension_wedge, hzero, map_zero]
        simp only [smul_zero]
  · rw [dite_eq_right hα]
    apply Finset.sum_eq_zero
    intro β _
    apply Finset.sum_eq_zero
    intro γ _
    rw [fullRootExteriorUpperStructureAtom_apply]
    simp only [hα, ↓reduceDIte, smul_zero]

theorem rootJointHarmonicActionBracketMixed_add_upperStructure_eq_zero
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    rootJointHarmonicActionBracketMixed n lam k +
      rootJointHarmonicActionUpperRootStructureCross n lam (k + 1) = 0 := by
  apply LinearMap.ext
  intro f
  funext S
  apply Subtype.ext
  apply Subtype.ext
  let g : RootPolynomialChain r n (k + 1) :=
    rootJointHarmonicPolynomialInclusion n lam (k + 1) f
  have hmixed := LinearMap.congr_fun
    (rootJointHarmonicPolynomialInclusion_actionBracketMixed_intertwines lam) f
  have hmixedS := congrFun hmixed S.val
  have hfull := congrArg
    (fun L : Module.End ℝ (FullRootExteriorPolynomialChain r n) =>
      L (rootPolynomialChainZeroExtension r n (k + 1) g) S.val.val)
    (fullRootExteriorActionCoboundary_bracket_eq_neg_upperStructure r n)
  simp only [LinearMap.add_apply, Pi.add_apply, Module.End.mul_apply,
    LinearMap.neg_apply, Pi.neg_apply] at hfull
  rw [fullRootExteriorBracket_zeroExtension_eq_zeroExtension g,
    ← rootActionCoboundary_zeroExtension,
    ← rootActionCoboundary_zeroExtension g,
    fullRootExteriorBracket_zeroExtension_eq_zeroExtension,
    rootPolynomialChainZeroExtension_wedge,
    rootPolynomialChainZeroExtension_wedge] at hfull
  change
    (((rootJointHarmonicActionBracketMixed n lam k f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) +
      (((rootJointHarmonicActionUpperRootStructureCross n lam (k + 1) f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) = 0
  change
    rootJointHarmonicPolynomialInclusion n lam (k + 1)
        (rootJointHarmonicActionBracketMixed n lam k f) S.val =
      rootPolynomialActionBracketMixed r n k g S.val at hmixedS
  rw [rootJointHarmonicPolynomialInclusion_apply_admissible] at hmixedS
  rw [hmixedS]
  change
    rootActionCoboundary r n k (rootBracketBoundary r n k g) S.val +
        rootBracketBoundary r n (k + 1)
          (rootActionCoboundary r n (k + 1) g) S.val +
      (((rootJointHarmonicActionUpperRootStructureCross n lam (k + 1) f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) = 0
  rw [hfull]
  rw [fullRootExteriorUpperRootStructureIncidence_zeroExtension_apply lam f S]
  exact neg_add_cancel _

end

section


open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootChevalleyEilenbergBoundary_comp_self_of_actionBracket
    (r n k : ℕ)
    (ha :
      (rootActionBoundary r n k).comp
          (rootActionBoundary r n (k + 1)) +
        (rootActionBoundary r n k).comp
          (rootBracketBoundary r n (k + 1)) +
        (rootBracketBoundary r n k).comp
          (rootActionBoundary r n (k + 1)) = 0)
    (hb :
      (rootBracketBoundary r n k).comp
        (rootBracketBoundary r n (k + 1)) = 0) :
    (rootChevalleyEilenbergBoundary r n k).comp
      (rootChevalleyEilenbergBoundary r n (k + 1)) = 0 := by
  change
    (rootActionBoundary r n k + rootBracketBoundary r n k).comp
      (rootActionBoundary r n (k + 1) +
        rootBracketBoundary r n (k + 1)) = 0
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
  have hreassoc :
      (rootActionBoundary r n k).comp
          (rootActionBoundary r n (k + 1)) +
        (rootActionBoundary r n k).comp
          (rootBracketBoundary r n (k + 1)) +
        ((rootBracketBoundary r n k).comp
          (rootActionBoundary r n (k + 1)) +
          (rootBracketBoundary r n k).comp
            (rootBracketBoundary r n (k + 1))) =
      ((rootActionBoundary r n k).comp
          (rootActionBoundary r n (k + 1)) +
        (rootActionBoundary r n k).comp
          (rootBracketBoundary r n (k + 1)) +
        (rootBracketBoundary r n k).comp
          (rootActionBoundary r n (k + 1))) +
        (rootBracketBoundary r n k).comp
          (rootBracketBoundary r n (k + 1)) := by
    abel
  rw [hreassoc, ha, hb, add_zero]

theorem weightedChevalleyEilenbergDifferential_comp_self_of_unweighted
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (h : (rootChevalleyEilenbergBoundary r n k).comp
      (rootChevalleyEilenbergBoundary r n (k + 1)) = 0) :
    (weightedChevalleyEilenbergDifferential n lam k).comp
      (weightedChevalleyEilenbergDifferential n lam (k + 1)) = 0 := by
  apply LinearMap.ext
  intro f
  apply (rootJointHarmonicPolynomialInclusion_injective lam)
  change
    rootJointHarmonicPolynomialInclusion n lam k
        (weightedChevalleyEilenbergDifferential n lam k
          (weightedChevalleyEilenbergDifferential n lam (k + 1) f)) =
      rootJointHarmonicPolynomialInclusion n lam k 0
  rw [map_zero]
  have hfirst := LinearMap.congr_fun
    (rootJointHarmonicPolynomialInclusion_chevalley_intertwines
      (n := n) (k := k) lam)
      (weightedChevalleyEilenbergDifferential n lam (k + 1) f)
  change
    rootJointHarmonicPolynomialInclusion n lam k
        (weightedChevalleyEilenbergDifferential n lam k
          (weightedChevalleyEilenbergDifferential n lam (k + 1) f)) =
      rootChevalleyEilenbergBoundary r n k
        (rootJointHarmonicPolynomialInclusion n lam (k + 1)
          (weightedChevalleyEilenbergDifferential n lam (k + 1) f))
    at hfirst
  have hsecond := LinearMap.congr_fun
    (rootJointHarmonicPolynomialInclusion_chevalley_intertwines
      (n := n) (k := k + 1) lam) f
  change
    rootJointHarmonicPolynomialInclusion n lam (k + 1)
        (weightedChevalleyEilenbergDifferential n lam (k + 1) f) =
      rootChevalleyEilenbergBoundary r n (k + 1)
        (rootJointHarmonicPolynomialInclusion n lam (k + 2) f)
    at hsecond
  change
    rootJointHarmonicPolynomialInclusion n lam k
        (weightedChevalleyEilenbergDifferential n lam k
          (weightedChevalleyEilenbergDifferential n lam (k + 1) f)) = 0
  rw [hfirst, hsecond]
  exact LinearMap.congr_fun h
    (rootJointHarmonicPolynomialInclusion n lam (k + 2) f)

end

end UniversalBGGRootComplex

section


private theorem core_inner_comm_metriccodes2_16f8f8ca {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (x y : V) :
    c.inner x y = c.inner y x := by
  simpa only [Real.ringHom_apply] using c.conj_inner_symm y x

private theorem core_inner_add_right_metriccodes2_16f8f8ca {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (x y z : V) :
    c.inner x (y + z) = c.inner x y + c.inner x z := by
  rw [core_inner_comm_metriccodes2_16f8f8ca c x (y + z), c.add_left,
    core_inner_comm_metriccodes2_16f8f8ca c y x, core_inner_comm_metriccodes2_16f8f8ca c z x]

theorem fischerCore_injective_of_coercive_add_adjoint_squares
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (cE : InnerProductSpace.Core ℝ E)
    (cF : InnerProductSpace.Core ℝ F)
    (cG : InnerProductSpace.Core ℝ G)
    (L : F →ₗ[ℝ] F)
    (B : F →ₗ[ℝ] E) (Bstar : E →ₗ[ℝ] F)
    (C : G →ₗ[ℝ] F) (Cstar : F →ₗ[ℝ] G)
    (hBstar : ∀ x : E, ∀ y : F,
      cF.inner (Bstar x) y = cE.inner x (B y))
    (hCstar : ∀ x : F, ∀ y : G,
      cG.inner (Cstar x) y = cF.inner x (C y))
    (hL : ∀ x : F, x ≠ 0 → 0 < cF.inner x (L x)) :
    Function.Injective
      (L + Bstar.comp B + C.comp Cstar) := by
  intro x y hxy
  apply sub_eq_zero.mp
  let z : F := x - y
  have hz : (L + Bstar.comp B + C.comp Cstar) z = 0 := by
    change (L + Bstar.comp B + C.comp Cstar) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  by_contra hnonzero
  have henergy :
      cF.inner z (L z) +
        cE.inner (B z) (B z) +
        cG.inner (Cstar z) (Cstar z) = 0 := by
    have hzero :
        cF.inner z ((L + Bstar.comp B + C.comp Cstar) z) = 0 := by
      rw [hz]
      rw [core_inner_comm_metriccodes2_16f8f8ca]
      simpa only [zero_smul, Real.ringHom_apply, zero_mul] using cF.smul_left z z (0 : ℝ)
    simp only [LinearMap.add_apply, LinearMap.comp_apply,
      core_inner_add_right_metriccodes2_16f8f8ca] at hzero
    have hB : cF.inner z (Bstar (B z)) =
        cE.inner (B z) (B z) := by
      rw [core_inner_comm_metriccodes2_16f8f8ca cF z (Bstar (B z))]
      exact hBstar (B z) z
    have hC : cF.inner z (C (Cstar z)) =
        cG.inner (Cstar z) (Cstar z) :=
      (hCstar z (Cstar z)).symm
    rwa [hB, hC] at hzero
  have hpositive : 0 < cF.inner z (L z) := hL z hnonzero
  have hBnonneg : 0 ≤ cE.inner (B z) (B z) := by
    simpa only [RCLike.re_to_real] using cE.re_inner_nonneg (B z)
  have hCnonneg : 0 ≤ cG.inner (Cstar z) (Cstar z) := by
    simpa only [RCLike.re_to_real] using cG.re_inner_nonneg (Cstar z)
  linarith

end

namespace UniversalBGGRootComplex

section


open MetricCodes.Spherical.HigherHarmonicYoung

private def weightedChevalleyEilenbergCoboundary {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1) :=
  weightedExteriorActionCoboundary n lam k +
    weightedRootBracketCoboundary n lam k

private theorem ceFischerCore_inner_comm_metriccodes2_1a8ab4cc
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (x y : V) :
    c.inner x y = c.inner y x := by
  simpa only [Real.ringHom_apply] using c.conj_inner_symm y x

private theorem ceFischerCore_add_right_metriccodes2_1a8ab4cc
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (x y z : V) :
    c.inner x (y + z) = c.inner x y + c.inner x z := by
  rw [ceFischerCore_inner_comm_metriccodes2_1a8ab4cc c x (y + z), c.add_left,
    ceFischerCore_inner_comm_metriccodes2_1a8ab4cc c y x,
    ceFischerCore_inner_comm_metriccodes2_1a8ab4cc c z x]

theorem weightedChevalleyEilenberg_fischer_adjoint
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam (k + 1))
    (q : RootJointHarmonicChain n lam k) :
    (rootJointHarmonicChainFischerCore n lam k).inner
        (weightedChevalleyEilenbergDifferential n lam k p) q =
      (rootJointHarmonicChainFischerCore n lam (k + 1)).inner
        p (weightedChevalleyEilenbergCoboundary n lam k q) := by
  unfold weightedChevalleyEilenbergDifferential weightedChevalleyEilenbergCoboundary
  simp only [LinearMap.add_apply]
  rw [(rootJointHarmonicChainFischerCore n lam k).add_left,
    weightedExteriorActionDifferential_fischer_adjoint,
    weightedRootBracketBoundary_fischer_adjoint,
    ← ceFischerCore_add_right_metriccodes2_1a8ab4cc]

theorem weightedChevalleyEilenberg_fischer_adjoint_reverse
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (q : RootJointHarmonicChain n lam k)
    (p : RootJointHarmonicChain n lam (k + 1)) :
    (rootJointHarmonicChainFischerCore n lam (k + 1)).inner
        (weightedChevalleyEilenbergCoboundary n lam k q) p =
      (rootJointHarmonicChainFischerCore n lam k).inner
        q (weightedChevalleyEilenbergDifferential n lam k p) := by
  calc
    _ = (rootJointHarmonicChainFischerCore n lam (k + 1)).inner
          p (weightedChevalleyEilenbergCoboundary n lam k q) :=
      ceFischerCore_inner_comm_metriccodes2_1a8ab4cc _ _ _
    _ = (rootJointHarmonicChainFischerCore n lam k).inner
          (weightedChevalleyEilenbergDifferential n lam k p) q :=
      (weightedChevalleyEilenberg_fischer_adjoint lam p q).symm
    _ = _ := ceFischerCore_inner_comm_metriccodes2_1a8ab4cc _ _ _

theorem weightedRootBracketBoundary_fischer_adjoint_reverse
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (q : RootJointHarmonicChain n lam k)
    (p : RootJointHarmonicChain n lam (k + 1)) :
    (rootJointHarmonicChainFischerCore n lam (k + 1)).inner
        (weightedRootBracketCoboundary n lam k q) p =
      (rootJointHarmonicChainFischerCore n lam k).inner
        q (weightedRootBracketBoundary n lam k p) := by
  calc
    _ = (rootJointHarmonicChainFischerCore n lam (k + 1)).inner
          p (weightedRootBracketCoboundary n lam k q) :=
      ceFischerCore_inner_comm_metriccodes2_1a8ab4cc _ _ _
    _ = (rootJointHarmonicChainFischerCore n lam k).inner
          (weightedRootBracketBoundary n lam k p) q :=
      (weightedRootBracketBoundary_fischer_adjoint lam p q).symm
    _ = _ := ceFischerCore_inner_comm_metriccodes2_1a8ab4cc _ _ _

theorem bgg_chain_range_eq_ker_of_coercive_add_adjoint_squares
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (d : RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam k)
    (dStar : RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1))
    (e : RootJointHarmonicChain n lam (k + 1 + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1))
    (eStar : RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1 + 1))
    (L : RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1))
    (B : RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam k)
    (Bstar : RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1))
    (C : RootJointHarmonicChain n lam (k + 1 + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1))
    (Cstar : RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1 + 1))
    (hdStar : ∀ x : RootJointHarmonicChain n lam k,
      ∀ y : RootJointHarmonicChain n lam (k + 1),
      (rootJointHarmonicChainFischerCore n lam (k + 1)).inner (dStar x) y =
        (rootJointHarmonicChainFischerCore n lam k).inner x (d y))
    (heStar : ∀ x : RootJointHarmonicChain n lam (k + 1),
      ∀ y : RootJointHarmonicChain n lam (k + 1 + 1),
      (rootJointHarmonicChainFischerCore n lam (k + 1 + 1)).inner (eStar x) y =
        (rootJointHarmonicChainFischerCore n lam (k + 1)).inner x (e y))
    (hBstar : ∀ x : RootJointHarmonicChain n lam k,
      ∀ y : RootJointHarmonicChain n lam (k + 1),
      (rootJointHarmonicChainFischerCore n lam (k + 1)).inner (Bstar x) y =
        (rootJointHarmonicChainFischerCore n lam k).inner x (B y))
    (hCstar : ∀ x : RootJointHarmonicChain n lam (k + 1),
      ∀ y : RootJointHarmonicChain n lam (k + 1 + 1),
      (rootJointHarmonicChainFischerCore n lam (k + 1 + 1)).inner (Cstar x) y =
        (rootJointHarmonicChainFischerCore n lam (k + 1)).inner x (C y))
    (hchain : d.comp e = 0)
    (hdecomposition :
      dStar.comp d + e.comp eStar =
        L + Bstar.comp B + C.comp Cstar)
    (hL : ∀ x : RootJointHarmonicChain n lam (k + 1), x ≠ 0 →
      0 < (rootJointHarmonicChainFischerCore n lam (k + 1)).inner x (L x)) :
    LinearMap.range e = LinearMap.ker d := by
  apply bgg_range_eq_ker_of_fischerCore_hodgeLaplacian_injective
    (rootJointHarmonicChainFischerCore n lam k)
    (rootJointHarmonicChainFischerCore n lam (k + 1))
    (rootJointHarmonicChainFischerCore n lam (k + 1 + 1))
    d dStar e eStar hdStar heStar hchain
  rw [hdecomposition]
  exact fischerCore_injective_of_coercive_add_adjoint_squares
    (rootJointHarmonicChainFischerCore n lam k)
    (rootJointHarmonicChainFischerCore n lam (k + 1))
    (rootJointHarmonicChainFischerCore n lam (k + 1 + 1))
    L B Bstar C Cstar hBstar hCstar hL

theorem weightedChevalleyEilenberg_exact_of_hodge_diagonal
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam)
    (L : RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1))
    (hchain :
      (weightedChevalleyEilenbergDifferential n lam k).comp
        (weightedChevalleyEilenbergDifferential n lam (k + 1)) = 0)
    (hmixed :
      ((weightedExteriorActionCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedExteriorActionCoboundary n lam (k + 1))) +
      ((weightedExteriorActionCoboundary n lam k).comp
          (weightedRootBracketBoundary n lam k) +
        (weightedRootBracketCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedRootBracketCoboundary n lam (k + 1)) +
        (weightedRootBracketBoundary n lam (k + 1)).comp
          (weightedExteriorActionCoboundary n lam (k + 1))) = L)
    (hLge : ∀ f : RootJointHarmonicChain n lam (k + 1),
      (rootJointHarmonicChainFischerCore n lam (k + 1)).inner f
        (rootJointHarmonicIncludedDescendingFischerLaplacian
          n lam (k + 1) f) ≤
      (rootJointHarmonicChainFischerCore n lam (k + 1)).inner f (L f)) :
    LinearMap.range
        (weightedChevalleyEilenbergDifferential n lam (k + 1)) =
      LinearMap.ker
        (weightedChevalleyEilenbergDifferential n lam k) := by
  apply bgg_chain_range_eq_ker_of_coercive_add_adjoint_squares lam
    (weightedChevalleyEilenbergDifferential n lam k)
    (weightedChevalleyEilenbergCoboundary n lam k)
    (weightedChevalleyEilenbergDifferential n lam (k + 1))
    (weightedChevalleyEilenbergCoboundary n lam (k + 1))
    L
    (weightedRootBracketBoundary n lam k)
    (weightedRootBracketCoboundary n lam k)
    (weightedRootBracketBoundary n lam (k + 1))
    (weightedRootBracketCoboundary n lam (k + 1))
  · exact weightedChevalleyEilenberg_fischer_adjoint_reverse lam
  · exact weightedChevalleyEilenberg_fischer_adjoint_reverse lam
  · exact weightedRootBracketBoundary_fischer_adjoint_reverse lam
  · exact weightedRootBracketBoundary_fischer_adjoint_reverse lam
  · exact hchain
  · apply LinearMap.ext
    intro f
    have h := LinearMap.congr_fun hmixed f
    simp only [LinearMap.add_apply, LinearMap.comp_apply,
      weightedChevalleyEilenbergCoboundary,
      weightedChevalleyEilenbergDifferential, map_add] at h ⊢
    rw [← h]
    abel
  · intro f hf
    exact lt_of_lt_of_le
      (rootJointHarmonicIncludedDescendingFischerLaplacian_energy_pos
        lam hdom (by omega) f hf)
      (hLge f)

end

section


open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootJointHarmonic_action_plus_mixed_hodge_eq_diagonal_of_cross_cancellation
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (haction :
      (weightedExteriorActionCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedExteriorActionCoboundary n lam (k + 1)) =
        rootJointHarmonicHodgeDiagonal n lam (k + 1) +
          rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1))
    (hmixed :
      rootJointHarmonicFullMixedHodge n lam k +
        rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1) = 0) :
    ((weightedExteriorActionCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedExteriorActionCoboundary n lam (k + 1))) +
      rootJointHarmonicFullMixedHodge n lam k =
        rootJointHarmonicHodgeDiagonal n lam (k + 1) := by
  rw [haction]
  calc
    (rootJointHarmonicHodgeDiagonal n lam (k + 1) +
        rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1)) +
        rootJointHarmonicFullMixedHodge n lam k =
      rootJointHarmonicHodgeDiagonal n lam (k + 1) +
        (rootJointHarmonicFullMixedHodge n lam k +
          rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1)) := by
            abel
    _ = rootJointHarmonicHodgeDiagonal n lam (k + 1) := by
      rw [hmixed, add_zero]

theorem weightedChevalleyEilenberg_mixed_hodge_eq_diagonal_of_root_cross_halves
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (haction :
      (weightedExteriorActionCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedExteriorActionCoboundary n lam (k + 1)) =
        rootJointHarmonicHodgeDiagonal n lam (k + 1) +
          rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1))
    (hupper :
      rootJointHarmonicActionBracketMixed n lam k +
        rootJointHarmonicActionUpperRootStructureCross n lam (k + 1) = 0)
    (hlower :
      rootJointHarmonicBracketActionMixed n lam k +
        rootJointHarmonicActionLowerRootStructureCross n lam (k + 1) = 0) :
    ((weightedExteriorActionCoboundary n lam k).comp
        (weightedExteriorActionDifferential n lam k) +
      (weightedExteriorActionDifferential n lam (k + 1)).comp
        (weightedExteriorActionCoboundary n lam (k + 1))) +
      ((weightedExteriorActionCoboundary n lam k).comp
          (weightedRootBracketBoundary n lam k) +
        (weightedRootBracketCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedRootBracketCoboundary n lam (k + 1)) +
        (weightedRootBracketBoundary n lam (k + 1)).comp
          (weightedExteriorActionCoboundary n lam (k + 1))) =
      rootJointHarmonicHodgeDiagonal n lam (k + 1) := by
  rw [← rootJointHarmonicFullMixedHodge.eq_def]
  exact rootJointHarmonic_action_plus_mixed_hodge_eq_diagonal_of_cross_cancellation
    lam haction
      (rootJointHarmonicFullMixedHodge_add_offDiagonal_eq_zero_of_halves
        lam hupper hlower)

end

section


open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootActionBracketBoundary_mixed_comp_self_zero
    (r n k : ℕ) :
    (rootActionBoundary r n k).comp
        (rootActionBoundary r n (k + 1)) +
      (rootActionBoundary r n k).comp
        (rootBracketBoundary r n (k + 1)) +
      (rootBracketBoundary r n k).comp
        (rootActionBoundary r n (k + 1)) = 0 := by
  apply LinearMap.ext
  intro f
  funext T
  exact rootActionBracketBoundary_mixed_square_eq_zero f T

theorem rootBracketBoundary_comp_self_zero (r n k : ℕ) :
    (rootBracketBoundary r n k).comp
      (rootBracketBoundary r n (k + 1)) = 0 := by
  apply LinearMap.ext
  intro f
  funext T
  exact rootBracketBoundary_comp_self_apply_eq_zero f T

theorem rootChevalleyEilenbergBoundary_comp_self_zero (r n k : ℕ) :
    (rootChevalleyEilenbergBoundary r n k).comp
      (rootChevalleyEilenbergBoundary r n (k + 1)) = 0 :=
  rootChevalleyEilenbergBoundary_comp_self_of_actionBracket r n k
    (rootActionBracketBoundary_mixed_comp_self_zero r n k)
    (rootBracketBoundary_comp_self_zero r n k)

theorem weightedChevalleyEilenbergDifferential_comp_self_zero
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    (weightedChevalleyEilenbergDifferential n lam k).comp
      (weightedChevalleyEilenbergDifferential n lam (k + 1)) = 0 :=
  weightedChevalleyEilenbergDifferential_comp_self_of_unweighted lam
    (rootChevalleyEilenbergBoundary_comp_self_zero r n k)

theorem weightedChevalleyEilenberg_exact_of_hodge_root_identities
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam)
    (haction :
      (weightedExteriorActionCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedExteriorActionCoboundary n lam (k + 1)) =
        rootJointHarmonicHodgeDiagonal n lam (k + 1) +
          rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1))
    (hupper :
      rootJointHarmonicActionBracketMixed n lam k +
        rootJointHarmonicActionUpperRootStructureCross n lam (k + 1) = 0)
    (hlower :
      rootJointHarmonicBracketActionMixed n lam k +
        rootJointHarmonicActionLowerRootStructureCross n lam (k + 1) = 0) :
    LinearMap.range
        (weightedChevalleyEilenbergDifferential n lam (k + 1)) =
      LinearMap.ker
        (weightedChevalleyEilenbergDifferential n lam k) := by
  apply weightedChevalleyEilenberg_exact_of_hodge_diagonal
    lam hdom (rootJointHarmonicHodgeDiagonal n lam (k + 1))
  · exact weightedChevalleyEilenbergDifferential_comp_self_zero lam
  · exact weightedChevalleyEilenberg_mixed_hodge_eq_diagonal_of_root_cross_halves
      lam haction hupper hlower
  · exact rootJointHarmonicHodgeDiagonal_energy_ge_included lam

end

end UniversalBGGRootComplex

end HigherHarmonicYoung

end Spherical

end MetricCodes

section


namespace MetricCodes.Spherical.HigherHarmonicYoung.UniversalBGGRootComplex

open MetricCodes.Spherical.HigherHarmonicYoung

theorem weightedChevalleyEilenberg_exact
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam) :
    LinearMap.range
        (weightedChevalleyEilenbergDifferential n lam (k + 1)) =
      LinearMap.ker
        (weightedChevalleyEilenbergDifferential n lam k) := by
  exact weightedChevalleyEilenberg_exact_of_hodge_root_identities lam hdom
    (weightedExteriorActionHodge_eq_diagonal_add_offDiagonal lam)
    (rootJointHarmonicActionBracketMixed_add_upperStructure_eq_zero lam)
    (rootJointHarmonicBracketActionMixed_add_lowerStructure_eq_zero lam)

end MetricCodes.Spherical.HigherHarmonicYoung.UniversalBGGRootComplex

namespace MetricCodes.Spherical.HigherHarmonicYoung

open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHarmonicYoung.UniversalBGGRootComplex

theorem weyl_dimension_eq_finrank_harmonicYoung
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    Weyl.dimension n lam =
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℝ) := by
  apply weyl_dimension_eq_finrank_harmonicYoung_of_chevalleyExactness hn lam
  intro k _
  exact weightedChevalleyEilenberg_exact lam hdom

end MetricCodes.Spherical.HigherHarmonicYoung

end

namespace MetricCodes

namespace Spherical

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherHarmonicYoung.AllRankFischerGramWeylRecurrence

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowRaiseLowerTensorTrace
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem loweredInternalYoungWeight_raiseWeight
    {r : ℕ} (low : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    loweredInternalYoungWeight (raiseWeight low row) row = low := by
  funext j
  by_cases hj : j = row
  · subst j
    simp only [loweredInternalYoungWeight, raiseWeight, Function.update_self, add_tsub_cancel_right]
  · simp only [loweredInternalYoungWeight, raiseWeight, Function.update_self, add_tsub_cancel_right,
      ne_eq, hj, not_false_eq_true, Function.update_of_ne]

theorem finrank_raiseWeight_eq_finrank_mul_weylEdgeRatio
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (row : Fin (r + 1))
    (hlow : FiniteInterlacing n low mu)
    (hhigh : FiniteInterlacing n (raiseWeight low row) mu) :
    (Module.finrank ℝ
      (HarmonicYoungSpace (n := n) (raiseWeight low row)) : ℝ) =
      (Module.finrank ℝ
        (HarmonicYoungSpace (n := n) low) : ℝ) *
        weylEdgeRatio n low row := by
  calc
    (Module.finrank ℝ
      (HarmonicYoungSpace (n := n) (raiseWeight low row)) : ℝ) =
        HigherHierarchy.Weyl.dimension n (raiseWeight low row) :=
      (weyl_dimension_eq_finrank_harmonicYoung
        hhigh.1 (raiseWeight low row) hhigh.antitone_ambient).symm
    _ = HigherHierarchy.Weyl.dimension n low *
          weylEdgeRatio n low row :=
      weylDimension_raiseWeight row hlow
    _ = (Module.finrank ℝ
          (HarmonicYoungSpace (n := n) low) : ℝ) *
          weylEdgeRatio n low row := by
      rw [weyl_dimension_eq_finrank_harmonicYoung
        hlow.1 low hlow.antitone_ambient]

theorem arbitraryRowRaiseTensorGramScalar_eq_lowerGram_mul_weylEdgeRatio
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (row : Fin (r + 1))
    (hlow : FiniteInterlacing n low mu)
    (hhigh : FiniteInterlacing n (raiseWeight low row) mu) :
    arbitraryRowRaiseTensorGramScalar (n := n)
        (raiseWeight low row) row =
      internalRowLowerGramScalar (raiseWeight low row) row *
        weylEdgeRatio n low row := by
  unfold arbitraryRowRaiseTensorGramScalar
  rw [loweredInternalYoungWeight_raiseWeight,
    finrank_raiseWeight_eq_finrank_mul_weylEdgeRatio
      low mu row hlow hhigh]
  have hstable : 2 * r + 4 ≤ n := hlow.1
  have hdimension :
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) low) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (finrank_harmonicYoung_pos_of_antitone
        (by omega : 2 * (r + 1) ≤ n) low hlow.antitone_ambient)
  field_simp [hdimension]

end HigherHarmonicYoung.AllRankFischerGramWeylRecurrence

end

section


open scoped BigOperators

namespace HigherYoungArbitraryRankColumnHighestCoefficientDescent

open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine
open MetricCodes.Spherical.HigherYoungAllRankSourceCoefficientStraightening

private def sourceMatrixTranspose (m : ℕ) :
    SourceMatrix m ≃ₐ[ℂ] SourceMatrix m :=
  MvPolynomial.renameEquiv ℂ (Equiv.prodComm (Fin m) (Fin m))

private def sourceExponentTranspose {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) : Fin m × Fin m →₀ ℕ :=
  Finsupp.mapDomain (Equiv.prodComm (Fin m) (Fin m)) d

@[simp] theorem sourceMatrixTranspose_X {m : ℕ}
    (i j : Fin m) :
    sourceMatrixTranspose m (MvPolynomial.X (i, j)) =
      MvPolynomial.X (j, i) := by
  simp only [sourceMatrixTranspose, MvPolynomial.renameEquiv_apply, Equiv.coe_prodComm,
    MvPolynomial.rename_X, Prod.swap_prod_mk]

theorem sourceMatrixTranspose_pderiv {m : ℕ}
    (i j : Fin m) (p : SourceMatrix m) :
    sourceMatrixTranspose m (MvPolynomial.pderiv (i, j) p) =
      MvPolynomial.pderiv (j, i) (sourceMatrixTranspose m p) := by
  simpa only [sourceMatrixTranspose, MvPolynomial.renameEquiv_apply, Equiv.coe_prodComm,
    Equiv.prodComm_apply,
    Prod.swap_prod_mk] using (MvPolynomial.pderiv_rename (Equiv.prodComm (Fin m) (Fin
      m)).injective (i, j) p).symm

theorem sourceMatrixTranspose_columnRoot {m : ℕ}
    (i j : Fin m) (p : SourceMatrix m) :
    sourceMatrixTranspose m (sourceColumnRoot i j p) =
      sourceRowRoot i j (sourceMatrixTranspose m p) := by
  rw [sourceColumnRoot_apply, sourceRowRoot_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul, sourceMatrixTranspose_X,
    sourceMatrixTranspose_pderiv]

@[simp] theorem sourceExponentTranspose_apply {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i j : Fin m) :
    sourceExponentTranspose d (i, j) = d (j, i) := by
  have h := Finsupp.mapDomain_apply
    (Equiv.prodComm (Fin m) (Fin m)).injective d (j, i)
  simpa only [sourceExponentTranspose, Equiv.coe_prodComm, Equiv.prodComm_apply,
    Prod.swap_prod_mk] using h

@[simp] theorem sourceExponentTranspose_transpose {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) :
    sourceExponentTranspose (sourceExponentTranspose d) = d := by
  ext ⟨i, j⟩
  simp only [sourceExponentTranspose_apply]

theorem sourceMatrixTranspose_coeff {m : ℕ}
    (p : SourceMatrix m) (d : Fin m × Fin m →₀ ℕ) :
    (sourceMatrixTranspose m p).coeff (sourceExponentTranspose d) =
      p.coeff d := by
  exact MvPolynomial.coeff_rename_mapDomain
    (Equiv.prodComm (Fin m) (Fin m))
    (Equiv.prodComm (Fin m) (Fin m)).injective p d

theorem exists_lowerTriangular_coeff_ne_zero_of_columnHighest
    {m : ℕ} (p : SourceMatrix m) (hp : p ≠ 0)
    (hhighest : ∀ i j : Fin m, i < j → sourceColumnRoot i j p = 0) :
    ∃ d : Fin m × Fin m →₀ ℕ,
      p.coeff d ≠ 0 ∧
        ∀ i j : Fin m, i < j → d (i, j) = 0 := by
  classical
  let q := sourceMatrixTranspose m p
  have hq : q ≠ 0 := by
    intro hzero
    apply hp
    exact (sourceMatrixTranspose m).injective
      (by simpa only [map_zero, EmbeddingLike.map_eq_zero_iff, q] using hzero)
  have hrow : ∀ i j : Fin m, i < j → sourceRowRoot i j q = 0 := by
    intro i j hij
    dsimp [q]
    rw [← sourceMatrixTranspose_columnRoot,
      hhighest i j hij, map_zero]
  have hex : ∃ e : Fin m × Fin m →₀ ℕ,
      belowDiagonalMass e = 0 ∧ q.coeff e ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hq
      (eq_zero_of_upperRoots_of_massZero_coeff q hrow hnone)
  obtain ⟨e, he, hcoeff⟩ := hex
  refine ⟨sourceExponentTranspose e, ?_, ?_⟩
  · intro hzero
    apply hcoeff
    dsimp [q]
    rw [← sourceMatrixTranspose_coeff p
      (sourceExponentTranspose e),
      sourceExponentTranspose_transpose] at hzero
    exact hzero
  · intro i j hij
    rw [sourceExponentTranspose_apply]
    exact belowDiagonal_entry_eq_zero_of_mass_eq_zero e he j i hij

end HigherYoungArbitraryRankColumnHighestCoefficientDescent

end

section


open scoped BigOperators

namespace HigherYoungArbitraryRankTriangularMarginDominance

open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine

private def sourceMarginPrefix {m : ℕ} (f : Fin m → ℕ) (k : ℕ) : ℕ :=
  ∑ i : Fin m, if i.val < k then f i else 0

theorem sourceColumnPrefix_le_sourceRowPrefix_of_upper
    {m : ℕ} (d : Fin m × Fin m →₀ ℕ)
    (hupper : ∀ i j : Fin m, j < i → d (i, j) = 0)
    (k : ℕ) :
    sourceMarginPrefix (sourceColumnDegree d) k ≤
      sourceMarginPrefix (sourceRowDegree d) k := by
  classical
  unfold sourceMarginPrefix sourceColumnDegree sourceRowDegree
  have hleft :
      (∑ j : Fin m, if j.val < k then ∑ i : Fin m, d (i, j) else 0) =
        ∑ j : Fin m, ∑ i : Fin m,
          if j.val < k then d (i, j) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < k <;> simp [hj]
  rw [hleft, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < k
  · simp only [hi, ite_true]
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> omega
  · simp only [hi, ite_false]
    apply Nat.le_zero.mpr
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val < k
    · simp [hj, hupper i j (show j < i by
        change j.val < i.val
        omega)]
    · simp only [hj, ↓reduceIte]

theorem sourceRowPrefix_le_sourceColumnPrefix_of_lower
    {m : ℕ} (d : Fin m × Fin m →₀ ℕ)
    (hlower : ∀ i j : Fin m, i < j → d (i, j) = 0)
    (k : ℕ) :
    sourceMarginPrefix (sourceRowDegree d) k ≤
      sourceMarginPrefix (sourceColumnDegree d) k := by
  classical
  unfold sourceMarginPrefix sourceRowDegree sourceColumnDegree
  have hleft :
      (∑ i : Fin m, if i.val < k then ∑ j : Fin m, d (i, j) else 0) =
        ∑ i : Fin m, ∑ j : Fin m,
          if i.val < k then d (i, j) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < k <;> simp [hi]
  rw [hleft, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j.val < k
  · simp only [hj, ite_true]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> omega
  · simp only [hj, ite_false]
    apply Nat.le_zero.mpr
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.val < k
    · simp [hi, hlower i j (show i < j by
        change i.val < j.val
        omega)]
    · simp only [hi, ↓reduceIte]

theorem sourceMarginPrefix_succ
    {m : ℕ} (f : Fin m → ℕ) (i : Fin m) :
    sourceMarginPrefix f (i.val + 1) =
      sourceMarginPrefix f i.val + f i := by
  classical
  unfold sourceMarginPrefix
  have hterm (j : Fin m) :
      (if j.val < i.val + 1 then f j else 0) =
        (if j.val < i.val then f j else 0) +
          if i = j then f j else 0 := by
    by_cases hlt : j.val < i.val
    · have hne : i ≠ j := by
        intro h
        subst j
        omega
      simp only [show j.val < i.val + 1 by omega, ↓reduceIte, hlt, hne, add_zero]
    · by_cases heq : i = j
      · subst j
        simp only [lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceIte, lt_self_iff_false, zero_add]
      · have hge : i.val + 1 ≤ j.val := by
          have hneq : i.val ≠ j.val := fun h => heq (Fin.ext h)
          omega
        simp only [show ¬j.val < i.val + 1 by omega, ↓reduceIte, hlt, heq, add_zero]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Fin.val_fin_lt, Finset.mem_univ, ↓reduceIte]

theorem sourceMargins_eq_of_upper_and_lower
    {m : ℕ} (lam nu : Fin m → ℕ)
    (dUpper dLower : Fin m × Fin m →₀ ℕ)
    (hupper : ∀ i j : Fin m, j < i → dUpper (i, j) = 0)
    (hlower : ∀ i j : Fin m, i < j → dLower (i, j) = 0)
    (hupperRow : ∀ i : Fin m, sourceRowDegree dUpper i = lam i)
    (hupperColumn : ∀ i : Fin m, sourceColumnDegree dUpper i = nu i)
    (hlowerRow : ∀ i : Fin m, sourceRowDegree dLower i = lam i)
    (hlowerColumn : ∀ i : Fin m, sourceColumnDegree dLower i = nu i) :
    lam = nu := by
  have hprefix (k : ℕ) :
      sourceMarginPrefix lam k = sourceMarginPrefix nu k := by
    apply le_antisymm
    · simpa only [sourceMarginPrefix, hlowerRow, hlowerColumn] using
        sourceRowPrefix_le_sourceColumnPrefix_of_lower dLower hlower k
    · simpa only [sourceMarginPrefix, hupperColumn, hupperRow] using
        sourceColumnPrefix_le_sourceRowPrefix_of_upper dUpper hupper k
  funext i
  have hprev := hprefix i.val
  have hnext := hprefix (i.val + 1)
  rw [sourceMarginPrefix_succ, sourceMarginPrefix_succ] at hnext
  omega

end HigherYoungArbitraryRankTriangularMarginDominance

end

namespace HigherHarmonicYoung

section


open scoped BigOperators

namespace ArbitraryRankColumnWeightProjection

open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine

private def columnVariableWeight (m : ℕ) :
    (Fin m × Fin m) → (Fin m → ℕ) :=
  fun z => Pi.single z.2 1

theorem columnVariableWeight_weight {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) :
    Finsupp.weight (columnVariableWeight m) d =
      fun j : Fin m => sourceColumnDegree d j := by
  classical
  ext j
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype d
      (fun z a => a • columnVariableWeight m z)
      (by intro z; simp only [zero_nsmul])]
  simp only [columnVariableWeight, nsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply,
    Nat.cast_id, Pi.single_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, sourceColumnDegree]

private def columnWeightComponent {m : ℕ} (ν : Fin m → ℕ)
    (p : SourceMatrix m) : SourceMatrix m :=
  MvPolynomial.weightedHomogeneousComponent
    (columnVariableWeight m) ν p

@[simp] theorem coeff_columnWeightComponent {m : ℕ}
    (ν : Fin m → ℕ) (p : SourceMatrix m)
    (d : Fin m × Fin m →₀ ℕ) :
    (columnWeightComponent ν p).coeff d =
      if (fun j : Fin m => sourceColumnDegree d j) = ν
      then p.coeff d else 0 := by
  classical
  rw [columnWeightComponent,
    MvPolynomial.coeff_weightedHomogeneousComponent,
    columnVariableWeight_weight]

theorem columnWeightComponent_ne_zero_of_coeff_ne_zero {m : ℕ}
    (p : SourceMatrix m) (d : Fin m × Fin m →₀ ℕ)
    (hd : p.coeff d ≠ 0) :
    columnWeightComponent
      (fun j : Fin m => sourceColumnDegree d j) p ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff d) hzero
  exact hd (by simpa only [coeff_columnWeightComponent, ↓reduceIte,
                 MvPolynomial.coeff_zero] using hcoeff)

end ArbitraryRankColumnWeightProjection

end

section


namespace ArbitraryRankColumnWeightCartan

open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankColumnWeightProjection

theorem sourceColumnRoot_self_columnWeightComponent {m : ℕ}
    (ν : Fin m → ℕ) (p : SourceMatrix m) (i : Fin m) :
    sourceColumnRoot i i (columnWeightComponent ν p) =
      (ν i : ℂ) • columnWeightComponent ν p := by
  classical
  ext d
  rw [coeff_sourceColumnRoot_self, MvPolynomial.coeff_smul,
    coeff_columnWeightComponent]
  by_cases hd : (fun j : Fin m => sourceColumnDegree d j) = ν
  · have hi : sourceColumnDegree d i = ν i := congrFun hd i
    simp only [hi, hd, ↓reduceIte, nsmul_eq_mul, smul_eq_mul]
  · simp only [hd, ↓reduceIte, nsmul_zero, smul_eq_mul, mul_zero]

end ArbitraryRankColumnWeightCartan

end

section


open scoped BigOperators

namespace ArbitraryRankColumnWeightRowRoot

open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankColumnWeightProjection
open MetricCodes.Spherical.TwoRowYoungBidegreeDecomposition

theorem sourceColumnDegree_add {m : ℕ}
    (d e : Fin m × Fin m →₀ ℕ) (column : Fin m) :
    sourceColumnDegree (d + e) column =
      sourceColumnDegree d column + sourceColumnDegree e column := by
  simp only [sourceColumnDegree, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]

theorem sourceColumnDegree_single {m : ℕ}
    (row column target : Fin m) (degree : ℕ) :
    sourceColumnDegree (Finsupp.single (row, column) degree) target =
      if column = target then degree else 0 := by
  classical
  by_cases h : column = target
  · subst target
    simp only [sourceColumnDegree, Finsupp.single_apply, Prod.mk.injEq, and_true, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
  · simp only [sourceColumnDegree, ne_eq, Prod.mk.injEq, h, and_false, not_false_eq_true,
      Finsupp.single_eq_of_ne', Finset.sum_const_zero, ↓reduceIte]

theorem sourceColumnDegree_rowTransfer {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ)
    (source target column test : Fin m)
    (hoccupied : 0 < d (source, column)) :
    sourceColumnDegree
        (d - Finsupp.single (source, column) 1 +
          Finsupp.single (target, column) 1) test =
      sourceColumnDegree d test := by
  have hle : (Finsupp.single (source, column) 1 :
      Fin m × Fin m →₀ ℕ) ≤ d :=
    Finsupp.single_le_iff.mpr hoccupied
  have hcancel :
      d - Finsupp.single (source, column) 1 +
          Finsupp.single (source, column) 1 = d :=
    tsub_add_cancel_of_le hle
  have hbalance :
      (d - Finsupp.single (source, column) 1 +
          Finsupp.single (target, column) 1) +
        Finsupp.single (source, column) 1 =
      d + Finsupp.single (target, column) 1 := by
    calc
      (d - Finsupp.single (source, column) 1 +
          Finsupp.single (target, column) 1) +
          Finsupp.single (source, column) 1 =
        (d - Finsupp.single (source, column) 1 +
          Finsupp.single (source, column) 1) +
          Finsupp.single (target, column) 1 := by ac_rfl
      _ = d + Finsupp.single (target, column) 1 := by rw [hcancel]
  have hdegree := congrArg (fun e => sourceColumnDegree e test) hbalance
  rw [sourceColumnDegree_add
    (d - Finsupp.single (source, column) 1 +
      Finsupp.single (target, column) 1)
    (Finsupp.single (source, column) 1) test,
    sourceColumnDegree_add d
      (Finsupp.single (target, column) 1) test,
    sourceColumnDegree_single, sourceColumnDegree_single] at hdegree
  exact Nat.add_right_cancel hdegree

theorem columnWeightComponent_X_mul_pderiv_row {m : ℕ}
    (ν : Fin m → ℕ) (p : SourceMatrix m)
    (source target column : Fin m) :
    MvPolynomial.X (target, column) *
        MvPolynomial.pderiv (source, column)
          (columnWeightComponent ν p) =
      columnWeightComponent ν
        (MvPolynomial.X (target, column) *
          MvPolynomial.pderiv (source, column) p) := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hrows : target = source
  · subst target
    rw [coeff_columnWeightComponent, coeff_X_mul_pderiv,
      coeff_X_mul_pderiv, coeff_columnWeightComponent]
    split <;> simp
  · have hne : (target, column) ≠ (source, column) := by
      intro heq
      exact hrows (Prod.mk.inj heq).1
    rw [coeff_columnWeightComponent,
      coeff_X_mul_pderiv_ne _ _ _ hne,
      coeff_X_mul_pderiv_ne _ _ _ hne]
    by_cases hoccupied : d (target, column) = 0
    · simp only [hoccupied, ↓reduceIte, ite_self]
    · simp only [hoccupied, ↓reduceIte]
      have hweight :
          (fun test : Fin m =>
            sourceColumnDegree
              (d - Finsupp.single (target, column) 1 +
                Finsupp.single (source, column) 1) test) =
          fun test : Fin m => sourceColumnDegree d test := by
        funext test
        exact sourceColumnDegree_rowTransfer d target source column test
          (Nat.pos_of_ne_zero hoccupied)
      rw [coeff_columnWeightComponent, hweight]
      split <;> simp

theorem sourceRowRoot_columnWeightComponent {m : ℕ}
    (ν : Fin m → ℕ) (p : SourceMatrix m)
    (source target : Fin m) :
    sourceRowRoot target source (columnWeightComponent ν p) =
      columnWeightComponent ν (sourceRowRoot target source p) := by
  rw [sourceRowRoot_apply, sourceRowRoot_apply]
  simp_rw [columnWeightComponent_X_mul_pderiv_row]
  change
    (∑ column : Fin m,
      MvPolynomial.weightedHomogeneousComponent
        (columnVariableWeight m) ν
        (MvPolynomial.X (target, column) *
          MvPolynomial.pderiv (source, column) p)) =
      MvPolynomial.weightedHomogeneousComponent
        (columnVariableWeight m) ν
        (∑ column : Fin m,
          MvPolynomial.X (target, column) *
            MvPolynomial.pderiv (source, column) p)
  rw [map_sum]

theorem columnWeightComponent_rowHighest {m : ℕ}
    (ν : Fin m → ℕ) (p : SourceMatrix m)
    (hhighest : ∀ i j : Fin m, i < j → sourceRowRoot i j p = 0) :
    ∀ i j : Fin m, i < j →
      sourceRowRoot i j (columnWeightComponent ν p) = 0 := by
  intro i j hij
  rw [sourceRowRoot_columnWeightComponent,
    hhighest i j hij]
  change MvPolynomial.weightedHomogeneousComponent
      (columnVariableWeight m) ν 0 = 0
  exact map_zero _

theorem columnWeightComponent_rowCartan {m : ℕ}
    (ν lam : Fin m → ℕ) (p : SourceMatrix m)
    (hcartan : ∀ i : Fin m,
      sourceRowRoot i i p = (lam i : ℂ) • p) :
    ∀ i : Fin m,
      sourceRowRoot i i (columnWeightComponent ν p) =
        (lam i : ℂ) • columnWeightComponent ν p := by
  intro i
  rw [sourceRowRoot_columnWeightComponent, hcartan i]
  change MvPolynomial.weightedHomogeneousComponent
      (columnVariableWeight m) ν ((lam i : ℂ) • p) = _
  rw [map_smul]
  rfl

end ArbitraryRankColumnWeightRowRoot

end

section


open scoped BigOperators

namespace ArbitraryRankColumnWeightRootShift

open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankColumnWeightProjection

theorem columnWeight_shift_sub_single_add
    {m : ℕ} (d : Fin m × Fin m →₀ ℕ)
    (k i j : Fin m) (hd : d (k, i) ≠ 0) :
    (fun t : Fin m =>
      sourceColumnDegree
        (d - Finsupp.single (k, i) 1 + Finsupp.single (k, j) 1) t) +
      Pi.single i 1 =
        (fun t : Fin m => sourceColumnDegree d t) +
          Pi.single j 1 := by
  classical
  rw [← columnVariableWeight_weight, ← columnVariableWeight_weight,
    map_add, Finsupp.weight_single]
  simp only [one_smul, columnVariableWeight]
  have hsub := Finsupp.weight_sub_single_add
    (w := columnVariableWeight m) hd
  change
    (Finsupp.weight (columnVariableWeight m)
        (d - Finsupp.single (k, i) 1) + Pi.single j 1) +
      Pi.single i 1 =
        Finsupp.weight (columnVariableWeight m) d + Pi.single j 1
  calc
    _ = (Finsupp.weight (columnVariableWeight m)
          (d - Finsupp.single (k, i) 1) + Pi.single i 1) +
            Pi.single j 1 := by abel
    _ = _ := by
      simpa only [add_left_inj, columnVariableWeight] using hsub

theorem coeff_sourceColumnRoot_columnWeightComponent
    {m : ℕ} (ν : Fin m → ℕ) (p : SourceMatrix m)
    (i j : Fin m) (hij : i ≠ j)
    (d : Fin m × Fin m →₀ ℕ) :
    (sourceColumnRoot i j (columnWeightComponent ν p)).coeff d =
      if ν + Pi.single i 1 =
          (fun t : Fin m => sourceColumnDegree d t) + Pi.single j 1
      then (sourceColumnRoot i j p).coeff d else 0 := by
  classical
  by_cases hweight : ν + Pi.single i 1 =
      (fun t : Fin m => sourceColumnDegree d t) + Pi.single j 1
  · rw [ite_eq_left hweight, sourceColumnRoot_apply, sourceColumnRoot_apply,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hne : (k, i) ≠ (k, j) := by
      intro heq
      exact hij (congrArg Prod.snd heq)
    rw [coeff_X_mul_pderiv_ne (columnWeightComponent ν p)
      (k, i) (k, j) hne d,
      coeff_X_mul_pderiv_ne p (k, i) (k, j) hne d]
    by_cases hk : d (k, i) = 0
    · simp only [hk, ↓reduceIte]
    · rw [ite_eq_right hk, ite_eq_right hk,
        coeff_columnWeightComponent]
      have hshift := columnWeight_shift_sub_single_add d k i j hk
      have hdegree :
          (fun t : Fin m =>
            sourceColumnDegree
              (d - Finsupp.single (k, i) 1 +
                Finsupp.single (k, j) 1) t) = ν := by
        apply add_right_cancel
        exact hshift.trans hweight.symm
      simp only [hdegree, ↓reduceIte, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  · rw [ite_eq_right hweight, sourceColumnRoot_apply,
      MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro k _
    have hne : (k, i) ≠ (k, j) := by
      intro heq
      exact hij (congrArg Prod.snd heq)
    rw [coeff_X_mul_pderiv_ne (columnWeightComponent ν p)
      (k, i) (k, j) hne d]
    by_cases hk : d (k, i) = 0
    · simp only [hk, ↓reduceIte]
    · rw [ite_eq_right hk, coeff_columnWeightComponent]
      have hshift := columnWeight_shift_sub_single_add d k i j hk
      have hdegree :
          (fun t : Fin m =>
            sourceColumnDegree
              (d - Finsupp.single (k, i) 1 +
                Finsupp.single (k, j) 1) t) ≠ ν := by
        intro heq
        apply hweight
        rw [← heq]
        exact hshift
      simp only [hdegree, ↓reduceIte, nsmul_zero]

theorem columnWeightComponent_columnHighest
    {m : ℕ} (ν : Fin m → ℕ) (p : SourceMatrix m)
    (i j : Fin m) (hij : i < j)
    (hhighest : sourceColumnRoot i j p = 0) :
    sourceColumnRoot i j (columnWeightComponent ν p) = 0 := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_sourceColumnRoot_columnWeightComponent ν p i j
    (ne_of_lt hij) d, hhighest]
  simp only [MvPolynomial.coeff_zero, ite_self]

theorem columnWeightComponent_columnHighest_all
    {m : ℕ} (ν : Fin m → ℕ) (p : SourceMatrix m)
    (hhighest : ∀ i j : Fin m, i < j → sourceColumnRoot i j p = 0)
    (i j : Fin m) (hij : i < j) :
    sourceColumnRoot i j (columnWeightComponent ν p) = 0 :=
  columnWeightComponent_columnHighest ν p i j hij (hhighest i j hij)

end ArbitraryRankColumnWeightRootShift

namespace ArbitraryRankIsotropicSupportCartanWeight

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine
open MetricCodes.Spherical.HigherYoungAllRankSourceCoefficientStraightening
open MetricCodes.Spherical.HigherYoungArbitraryRankColumnHighestCoefficientDescent
open MetricCodes.Spherical.HigherYoungArbitraryRankTriangularMarginDominance
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankColumnWeightProjection
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankColumnWeightCartan
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankColumnWeightRowRoot
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankColumnWeightRootShift

theorem exists_upperTriangular_coeff_ne_zero_of_rowHighest
    {m : ℕ} (p : SourceMatrix m) (hp : p ≠ 0)
    (hhighest : ∀ i j : Fin m, i < j → sourceRowRoot i j p = 0) :
    ∃ d : Fin m × Fin m →₀ ℕ,
      p.coeff d ≠ 0 ∧
        ∀ i j : Fin m, j < i → d (i, j) = 0 := by
  classical
  by_contra hnone
  apply hp
  apply eq_zero_of_upperRoots_of_massZero_coeff p hhighest
  intro d hmass
  by_contra hd
  apply hnone
  exact ⟨d, hd, fun i j hji =>
    belowDiagonal_entry_eq_zero_of_mass_eq_zero d hmass i j hji⟩

theorem source_rowWeight_eq_columnWeight_of_biHighest
    {m : ℕ} (lam nu : Fin m → ℕ)
    (p : SourceMatrix m) (hp : p ≠ 0)
    (hrow : ∀ i : Fin m,
      sourceRowRoot i i p = (lam i : ℂ) • p)
    (hcolumn : ∀ i : Fin m,
      sourceColumnRoot i i p = (nu i : ℂ) • p)
    (hrowHighest : ∀ i j : Fin m,
      i < j → sourceRowRoot i j p = 0)
    (hcolumnHighest : ∀ i j : Fin m,
      i < j → sourceColumnRoot i j p = 0) :
    lam = nu := by
  obtain ⟨dUpper, hdUpper, hupper⟩ :=
    exists_upperTriangular_coeff_ne_zero_of_rowHighest p hp hrowHighest
  obtain ⟨dLower, hdLower, hlower⟩ :=
    exists_lowerTriangular_coeff_ne_zero_of_columnHighest
      p hp hcolumnHighest
  exact sourceMargins_eq_of_upper_and_lower lam nu dUpper dLower
    hupper hlower
    (sourceRowDegree_eq_of_coeff_ne_zero p lam hrow dUpper hdUpper)
    (sourceColumnDegree_eq_of_coeff_ne_zero p nu hcolumn dUpper hdUpper)
    (sourceRowDegree_eq_of_coeff_ne_zero p lam hrow dLower hdLower)
    (sourceColumnDegree_eq_of_coeff_ne_zero p nu hcolumn dLower hdLower)

theorem sourceColumnDegree_eq_rowWeight_of_coeff_ne_zero_of_biHighest
    {m : ℕ} (lam : Fin m → ℕ)
    (p : SourceMatrix m)
    (hrow : ∀ i : Fin m,
      sourceRowRoot i i p = (lam i : ℂ) • p)
    (hrowHighest : ∀ i j : Fin m,
      i < j → sourceRowRoot i j p = 0)
    (hcolumnHighest : ∀ i j : Fin m,
      i < j → sourceColumnRoot i j p = 0)
    (d : Fin m × Fin m →₀ ℕ)
    (hd : p.coeff d ≠ 0) :
    (fun i : Fin m => sourceColumnDegree d i) = lam := by
  let nu : Fin m → ℕ := fun i => sourceColumnDegree d i
  let q : SourceMatrix m := columnWeightComponent nu p
  have hq : q ≠ 0 :=
    columnWeightComponent_ne_zero_of_coeff_ne_zero p d hd
  have hrowq : ∀ i : Fin m,
      sourceRowRoot i i q = (lam i : ℂ) • q :=
    columnWeightComponent_rowCartan nu lam p hrow
  have hcolumnq : ∀ i : Fin m,
      sourceColumnRoot i i q = (nu i : ℂ) • q :=
    sourceColumnRoot_self_columnWeightComponent nu p
  have hrowHighestq : ∀ i j : Fin m,
      i < j → sourceRowRoot i j q = 0 :=
    columnWeightComponent_rowHighest nu p hrowHighest
  have hcolumnHighestq : ∀ i j : Fin m,
      i < j → sourceColumnRoot i j q = 0 :=
    columnWeightComponent_columnHighest_all nu p hcolumnHighest
  exact (source_rowWeight_eq_columnWeight_of_biHighest lam nu q hq
    hrowq hcolumnq hrowHighestq hcolumnHighestq).symm

theorem sourceColumnRoot_self_eq_rowWeight_of_biHighest
    {m : ℕ} (lam : Fin m → ℕ)
    (p : SourceMatrix m)
    (hrow : ∀ i : Fin m,
      sourceRowRoot i i p = (lam i : ℂ) • p)
    (hrowHighest : ∀ i j : Fin m,
      i < j → sourceRowRoot i j p = 0)
    (hcolumnHighest : ∀ i j : Fin m,
      i < j → sourceColumnRoot i j p = 0)
    (i : Fin m) :
    sourceColumnRoot i i p = (lam i : ℂ) • p := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_sourceColumnRoot_self, MvPolynomial.coeff_smul]
  by_cases hd : p.coeff d = 0
  · simp only [hd, nsmul_zero, smul_eq_mul, mul_zero]
  · have hdegree := congrFun
      (sourceColumnDegree_eq_rowWeight_of_coeff_ne_zero_of_biHighest
        lam p hrow hrowHighest hcolumnHighest d hd) i
    simp only [hdegree, nsmul_eq_mul, smul_eq_mul]

end ArbitraryRankIsotropicSupportCartanWeight

end

end HigherHarmonicYoung

section


open scoped BigOperators

namespace HigherYoungFullComplexSpanRowEquations

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem rowDerivation_polynomialComplexification
    {r n : ℕ} (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    rowDerivation i j (polynomialComplexification p) =
      polynomialComplexification (polarization r n i j p) := by
  rw [rowDerivation_apply, polarization_apply]
  change
    (∑ k : Fin n,
      MvPolynomial.X (variableIndex i k) *
        MvPolynomial.pderiv (variableIndex j k)
          (MvPolynomial.map Complex.ofRealHom p)) =
      MvPolynomial.map Complex.ofRealHom
        (∑ k : Fin n,
          MvPolynomial.X (variableIndex i k) *
            MvPolynomial.pderiv (variableIndex j k) p)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, MvPolynomial.map_X, MvPolynomial.pderiv_map]

theorem rowDerivation_self_of_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (i : Fin (r + 1)) :
    rowDerivation i i f = (lam i : ℂ) • f := by
  unfold fullYoungComplexPolynomialSpan polynomialComplexSpan at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro f hf
    rcases hf with ⟨p, hp, rfl⟩
    rw [rowDerivation_polynomialComplexification, polarization_self]
    have hweight := ((mem_harmonicYoungSubmodule lam p).mp hp).2.1 i
    rw [hweight, map_smul]
    apply MvPolynomial.ext
    intro d
    simp only [polynomialComplexification_apply, MvPolynomial.coeff_smul, Complex.real_smul,
      Complex.ofReal_natCast, smul_eq_mul]
  · simp only [map_zero, smul_zero]
  · intro p q _ _ hp hq
    rw [map_add, hp, hq, smul_add]
  · intro c p _ hp
    rw [(rowDerivation i i).map_smul, hp]
    module

theorem rowDerivation_upper_of_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (i j : Fin (r + 1)) (hij : i < j) :
    rowDerivation i j f = 0 := by
  unfold fullYoungComplexPolynomialSpan polynomialComplexSpan at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro f hf
    rcases hf with ⟨p, hp, rfl⟩
    rw [rowDerivation_polynomialComplexification,
      ((mem_harmonicYoungSubmodule lam p).mp hp).2.2.2 i j hij,
      map_zero]
  · simp only [map_zero, ]
  · intro p q _ _ hp hq
    rw [map_add, hp, hq, add_zero]
  · intro c p _ hp
    rw [(rowDerivation i j).map_smul, hp, smul_zero]

end HigherYoungFullComplexSpanRowEquations

end

section


open scoped BigOperators

namespace HigherYoungFullComplexSpanTraceFree

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem complexTraceOperator_polynomialComplexification
    {r n : ℕ} (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    complexTraceOperator i j (polynomialComplexification p) =
      polynomialComplexification (traceOperator r n i j p) := by
  rw [traceOperator_apply]
  change
    (∑ k : Fin n,
      MvPolynomial.pderiv (variableIndex i k)
        (MvPolynomial.pderiv (variableIndex j k)
          (MvPolynomial.map Complex.ofRealHom p))) =
      MvPolynomial.map Complex.ofRealHom
        (∑ k : Fin n,
          MvPolynomial.pderiv (variableIndex i k)
            (MvPolynomial.pderiv (variableIndex j k) p))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [MvPolynomial.pderiv_map, MvPolynomial.pderiv_map]

theorem complexTraceOperator_of_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (i j : Fin (r + 1)) :
    complexTraceOperator i j f = 0 := by
  unfold fullYoungComplexPolynomialSpan polynomialComplexSpan at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro f hf
    rcases hf with ⟨p, hp, rfl⟩
    rw [complexTraceOperator_polynomialComplexification,
      ((mem_harmonicYoungSubmodule lam p).mp hp).2.2.1 i j,
      map_zero]
  · simp only [complexTraceOperator, map_zero, Finset.sum_const_zero]
  · intro p q _ _ hp hq
    simp only [complexTraceOperator, map_add,
      Finset.sum_add_distrib] at hp hq ⊢
    rw [hp, hq, add_zero]
  · intro c p _ hp
    simp only [complexTraceOperator,
      (MvPolynomial.pderiv _).map_smul] at hp ⊢
    rw [← Finset.smul_sum, hp, smul_zero]

end HigherYoungFullComplexSpanTraceFree

namespace HigherYoungFullComplexSpanHomogeneity

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem isHomogeneous_of_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan (n := n) lam) :
    f.IsHomogeneous (∑ i, lam i) := by
  unfold fullYoungComplexPolynomialSpan polynomialComplexSpan at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro f hf
    obtain ⟨p, hp, rfl⟩ := hf
    exact (((mem_harmonicYoungSubmodule lam p).mp hp).1).map
      Complex.ofRealHom
  · exact MvPolynomial.isHomogeneous_zero
      (Fin ((r + 1) * n)) ℂ (∑ i, lam i)
  · intro f g _ _ hf hg
    exact hf.add hg
  · intro c f _ hf
    exact (MvPolynomial.homogeneousSubmodule
      (Fin ((r + 1) * n)) ℂ (∑ i, lam i)).smul_mem c hf

end HigherYoungFullComplexSpanHomogeneity

namespace HigherYoungOrthogonalPositiveRootKernelIsotropicSupport

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientCartanIsotropicEigenvalues
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
open MetricCodes.Spherical.HigherYoungFullComplexSpanHomogeneity
open MetricCodes.Spherical.HigherYoungMaximalCartanNullSubstitutionRange

theorem exists_nullSubstitution_of_mem_fullYoungComplexPolynomialSpan_maximalCartan
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan (n := n) lam)
    (hcartan : totalAmbientCartan h f =
      ((2 * (∑ i, lam i) : ℕ) : ℂ) • f) :
    ∃ q : MvPolynomial (Fin (r + 1) × Fin (r + 1)) ℂ,
      nullSubstitution h q = f :=
  maximalTotalAmbientCartan_mem_nullSubstitution_range h f
    (∑ i, lam i)
    (isHomogeneous_of_mem_fullYoungComplexPolynomialSpan lam hf)
    hcartan

end HigherYoungOrthogonalPositiveRootKernelIsotropicSupport

end

section


open scoped BigOperators

namespace HigherYoungArbitraryRankHarmonicHoweHighestRigidity

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankIsotropicSupportCartanWeight
open MetricCodes.Spherical.HigherYoungAllRankIsotropicHighestMultiplicityOne
open MetricCodes.Spherical.HigherYoungAmbientCartanIsotropicEigenvalues
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungFullComplexSpanRowEquations
open MetricCodes.Spherical.HigherYoungOrthogonalPositiveRootKernelIsotropicSupport
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem sourceColumnRoot_upper_of_positiveRootKernel
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (p : SourceMatrix (r + 1))
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation hn α (nullSubstitution hn p) = 0)
    (i j : Fin (r + 1)) (hij : i < j) :
    sourceColumnRoot i j p = 0 := by
  have hroot := hroots (.difference i j hij)
  change ambientPositiveRoot hn i j (nullSubstitution hn p) = 0 at hroot
  rw [ambientPositiveRoot_nullSubstitution_sourceColumnRoot] at hroot
  have himage : nullSubstitution hn (sourceColumnRoot i j p) = 0 := by
    exact (smul_eq_zero.mp hroot).resolve_left (by norm_num)
  apply nullSubstitution_injective hn
  simpa only [sourceColumnRoot_apply, map_sum, map_mul, nullSubstitution_X, map_zero] using himage

theorem sourceRowRoot_self_of_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (p : SourceMatrix (r + 1))
    (hp : nullSubstitution hn p ∈ fullYoungComplexPolynomialSpan lam)
    (i : Fin (r + 1)) :
    sourceRowRoot i i p = (lam i : ℂ) • p := by
  apply nullSubstitution_injective hn
  rw [map_smul, ← rowDerivation_nullSubstitution_sourceRowRoot,
    rowDerivation_self_of_mem_fullYoungComplexPolynomialSpan lam hp i]

theorem sourceRowRoot_upper_of_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (p : SourceMatrix (r + 1))
    (hp : nullSubstitution hn p ∈ fullYoungComplexPolynomialSpan lam)
    (i j : Fin (r + 1)) (hij : i < j) :
    sourceRowRoot i j p = 0 := by
  apply nullSubstitution_injective hn
  rw [map_zero, ← rowDerivation_nullSubstitution_sourceRowRoot,
    rowDerivation_upper_of_mem_fullYoungComplexPolynomialSpan lam hp i j hij]

theorem mem_ambientIsotropicHighestSubmodule_of_isotropic_positiveRootKernel
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (hsupport : ∃ p : SourceMatrix (r + 1), nullSubstitution hn p = f)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation hn α f = 0)
    (hsourceCartan : ∀ (p : SourceMatrix (r + 1)),
      (∀ i : Fin (r + 1),
        sourceRowRoot i i p = (lam i : ℂ) • p) →
      (∀ i j : Fin (r + 1), i < j → sourceRowRoot i j p = 0) →
      (∀ i j : Fin (r + 1), i < j → sourceColumnRoot i j p = 0) →
      ∀ i : Fin (r + 1), sourceColumnRoot i i p = (lam i : ℂ) • p) :
    f ∈ ambientIsotropicHighestSubmodule hn lam := by
  obtain ⟨p, rfl⟩ := hsupport
  have hrow : ∀ i : Fin (r + 1),
      sourceRowRoot i i p = (lam i : ℂ) • p :=
    sourceRowRoot_self_of_mem_fullYoungComplexPolynomialSpan hn lam p hf
  have hrowUpper : ∀ i j : Fin (r + 1),
      i < j → sourceRowRoot i j p = 0 :=
    sourceRowRoot_upper_of_mem_fullYoungComplexPolynomialSpan hn lam p hf
  have hcolumnUpper : ∀ i j : Fin (r + 1),
      i < j → sourceColumnRoot i j p = 0 :=
    sourceColumnRoot_upper_of_positiveRootKernel hn p hroots
  have hcolumn : ∀ i : Fin (r + 1),
      sourceColumnRoot i i p = (lam i : ℂ) • p :=
    hsourceCartan p hrow hrowUpper hcolumnUpper
  rw [ambientIsotropicHighestSubmodule_eq_map_source]
  exact ⟨p, (mem_sourceMatrixHighestSubmodule lam p).mpr
    ⟨hrow, hcolumn, hrowUpper⟩, rfl⟩

theorem mem_ambientIsotropicHighestSubmodule_of_positiveRootKernel_and_support
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (hsupport : ∃ p : SourceMatrix (r + 1), nullSubstitution hn p = f)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation hn α f = 0) :
    f ∈ ambientIsotropicHighestSubmodule hn lam := by
  apply mem_ambientIsotropicHighestSubmodule_of_isotropic_positiveRootKernel
    hn lam hf hsupport hroots
  intro p hrow hrowUpper hcolumnUpper i
  exact sourceColumnRoot_self_eq_rowWeight_of_biHighest
    lam p hrow hrowUpper hcolumnUpper i

theorem mem_ambientIsotropicHighestSubmodule_of_positiveRootKernel_maximalCartan
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation hn α f = 0)
    (hcartan : totalAmbientCartan hn f =
      ((2 * (∑ i, lam i) : ℕ) : ℂ) • f) :
    f ∈ ambientIsotropicHighestSubmodule hn lam := by
  exact mem_ambientIsotropicHighestSubmodule_of_positiveRootKernel_and_support
    hn lam hf
    (exists_nullSubstitution_of_mem_fullYoungComplexPolynomialSpan_maximalCartan
      hn lam hf hcartan)
    hroots

end HigherYoungArbitraryRankHarmonicHoweHighestRigidity

namespace HigherYoungAllRankHarmonicHighestCartanEulerIdentity

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientCartanIsotropicEigenvalues
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence

private def totalYoungRowEuler {r n : ℕ} :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  ∑ a : Fin (r + 1), rowDerivation a a

private def antiholomorphicEulerDefect {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  ∑ a : Fin (r + 1), ∑ p : Fin (r + 1),
    conjugateIsotropicVariable h a p • antiholomorphicDerivative h a p

private def unusedCoordinateEulerDefect {r n : ℕ} :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  ∑ a : Fin (r + 1),
    ∑ t ∈ Finset.univ.filter
      (fun t : Fin n => 2 * (r + 1) ≤ t.val),
        (MvPolynomial.X (variableIndex a t) :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) •
          (MvPolynomial.pderiv (variableIndex a t) :
            Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
              (MvPolynomial (Fin ((r + 1) * n)) ℂ))

@[simp] theorem totalYoungRowEuler_apply {r n : ℕ}
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    totalYoungRowEuler f = ∑ a : Fin (r + 1), rowDerivation a a f := by
  change (Derivation.coeFnAddMonoidHom
    (∑ a : Fin (r + 1), rowDerivation a a)) f = _
  rw [map_sum, Finset.sum_apply]
  rfl

theorem totalYoungRowEuler_of_rowCartan {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hrow : ∀ a : Fin (r + 1),
      rowDerivation a a f = (lam a : ℂ) • f) :
    totalYoungRowEuler f = ((∑ a : Fin (r + 1), lam a : ℕ) : ℂ) • f := by
  rw [totalYoungRowEuler_apply]
  simp_rw [hrow]
  rw [← Finset.sum_smul]
  norm_cast

theorem totalYoungRowEuler_X {r n : ℕ}
    (a : Fin (r + 1)) (t : Fin n) :
    totalYoungRowEuler
      (MvPolynomial.X (variableIndex a t) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) =
      MvPolynomial.X (variableIndex a t) := by
  classical
  rw [totalYoungRowEuler_apply]
  simp only [rowDerivation_apply, MvPolynomial.pderiv_X,
    Pi.single_apply, DeterminantVectors.variableIndex_eq_iff,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single t]
    · simp only [and_self, ↓reduceIte]
    · intro u hu htu
      simp only [Ne.symm htu, and_false, ↓reduceIte]
    · simp only [Finset.mem_univ, not_true_eq_false, and_self, ↓reduceIte, MvPolynomial.X_ne_zero,
        imp_self]
  · intro b hb hab
    apply Finset.sum_eq_zero
    intro u hu
    simp only [Ne.symm hab, false_and, ↓reduceIte]
  · simp only [Finset.mem_univ, not_true_eq_false, true_and, Finset.sum_ite_eq, ↓reduceIte,
      MvPolynomial.X_ne_zero, imp_self]

@[simp] theorem antiholomorphicEulerDefect_apply {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    antiholomorphicEulerDefect h f =
      ∑ a : Fin (r + 1), ∑ p : Fin (r + 1),
        conjugateIsotropicVariable h a p *
          antiholomorphicDerivative h a p f := by
  change (Derivation.coeFnAddMonoidHom
    (∑ a : Fin (r + 1), ∑ p : Fin (r + 1),
      conjugateIsotropicVariable h a p •
        antiholomorphicDerivative h a p)) f = _
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_sum, Finset.sum_apply]
  rfl

theorem antiholomorphicDerivative_X_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p b q : Fin (r + 1)) :
    antiholomorphicDerivative h a p
      (MvPolynomial.X (variableIndex b (evenCoordinate h q))) =
      if a = b ∧ p = q then 1 else 0 := by
  classical
  change
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (MvPolynomial.X (variableIndex b (evenCoordinate h q))) +
      MvPolynomial.C Complex.I *
        MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
          (MvPolynomial.X (variableIndex b (evenCoordinate h q))) = _
  by_cases hab : a = b
  · subst b
    by_cases hpq : p = q
    · subst q
      simp only [MvPolynomial.pderiv_X, Pi.single_eq_same, ne_eq,
        DeterminantVectors.variableIndex_eq_iff, evenCoordinate_ne_oddCoordinate, and_false,
        not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, and_self, ↓reduceIte]
    · simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff,
        evenCoordinate_inj, Ne.symm hpq, and_false, not_false_eq_true, Pi.single_eq_of_ne,
        evenCoordinate_ne_oddCoordinate, mul_zero, add_zero, hpq, ↓reduceIte]
  · simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff, Ne.symm hab,
      evenCoordinate_inj, false_and, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, hab,
      ↓reduceIte]

theorem antiholomorphicDerivative_X_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p b q : Fin (r + 1)) :
    antiholomorphicDerivative h a p
      (MvPolynomial.X (variableIndex b (oddCoordinate h q))) =
      if a = b ∧ p = q then MvPolynomial.C Complex.I else 0 := by
  classical
  change
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (MvPolynomial.X (variableIndex b (oddCoordinate h q))) +
      MvPolynomial.C Complex.I *
        MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
          (MvPolynomial.X (variableIndex b (oddCoordinate h q))) = _
  by_cases hab : a = b
  · subst b
    by_cases hpq : p = q
    · subst q
      simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff,
        evenCoordinate_ne_oddCoordinate, and_false, not_false_eq_true, Pi.single_eq_of_ne',
        Pi.single_eq_same, mul_one, zero_add, and_self, ↓reduceIte]
    · simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff,
        evenCoordinate_ne_oddCoordinate, and_false, not_false_eq_true, Pi.single_eq_of_ne',
        oddCoordinate_inj, mul_zero, add_zero, hpq, ↓reduceIte]
  · simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff, Ne.symm hab,
      false_and, not_false_eq_true, Pi.single_eq_of_ne, oddCoordinate_inj, mul_zero, add_zero, hab,
      ↓reduceIte]

theorem antiholomorphicDerivative_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p b : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    antiholomorphicDerivative h a p
      (MvPolynomial.X (variableIndex b t)) = 0 := by
  have he : evenCoordinate h p ≠ t := by
    intro heq
    have hv := congrArg Fin.val heq
    have hp := p.isLt
    simp only [evenCoordinate_val] at hv
    omega
  have ho : oddCoordinate h p ≠ t := by
    intro heq
    have hv := congrArg Fin.val heq
    have hp := p.isLt
    simp only [oddCoordinate_val] at hv
    omega
  change
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (MvPolynomial.X (variableIndex b t)) +
      MvPolynomial.C Complex.I *
        MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
          (MvPolynomial.X (variableIndex b t)) = 0
  simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff, Ne.symm he,
    and_false, not_false_eq_true, Pi.single_eq_of_ne, Ne.symm ho, mul_zero, add_zero]

@[simp] theorem unusedCoordinateEulerDefect_apply {r n : ℕ}
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    unusedCoordinateEulerDefect (r := r) (n := n) f =
      ∑ a : Fin (r + 1),
        ∑ t ∈ Finset.univ.filter
          (fun t : Fin n => 2 * (r + 1) ≤ t.val),
            MvPolynomial.X (variableIndex a t) *
              MvPolynomial.pderiv (variableIndex a t) f := by
  change (Derivation.coeFnAddMonoidHom
    (∑ a : Fin (r + 1),
      ∑ t ∈ Finset.univ.filter
        (fun t : Fin n => 2 * (r + 1) ≤ t.val),
          (MvPolynomial.X (variableIndex a t) :
            MvPolynomial (Fin ((r + 1) * n)) ℂ) •
            (MvPolynomial.pderiv (variableIndex a t) :
              Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
                (MvPolynomial (Fin ((r + 1) * n)) ℂ)))) f = _
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro t ht
  rfl

theorem antiholomorphicEulerDefect_X_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    antiholomorphicEulerDefect h
      (MvPolynomial.X (variableIndex a (evenCoordinate h p))) =
      conjugateIsotropicVariable h a p := by
  classical
  rw [antiholomorphicEulerDefect_apply]
  simp_rw [antiholomorphicDerivative_X_even]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single p]
    · simp only [and_self, ↓reduceIte, mul_one]
    · intro q hq hpq
      simp only [hpq, and_false, ↓reduceIte, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, and_self, ↓reduceIte, mul_one,
        IsEmpty.forall_iff]
  · intro b hb hab
    apply Finset.sum_eq_zero
    intro q hq
    simp only [hab, false_and, ↓reduceIte, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, true_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', ↓reduceIte, IsEmpty.forall_iff]

theorem antiholomorphicEulerDefect_X_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    antiholomorphicEulerDefect h
      (MvPolynomial.X (variableIndex a (oddCoordinate h p))) =
      conjugateIsotropicVariable h a p * MvPolynomial.C Complex.I := by
  classical
  rw [antiholomorphicEulerDefect_apply]
  simp_rw [antiholomorphicDerivative_X_odd]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single p]
    · simp only [and_self, ↓reduceIte]
    · intro q hq hpq
      simp only [hpq, and_false, ↓reduceIte, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, and_self, ↓reduceIte, mul_eq_zero, map_eq_zero,
        Complex.I_ne_zero, or_false, IsEmpty.forall_iff]
  · intro b hb hab
    apply Finset.sum_eq_zero
    intro q hq
    simp only [hab, false_and, ↓reduceIte, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, true_and, mul_ite, mul_zero, Finset.sum_ite_eq',
      ↓reduceIte, mul_eq_zero, map_eq_zero, Complex.I_ne_zero, or_false, IsEmpty.forall_iff]

theorem antiholomorphicEulerDefect_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    antiholomorphicEulerDefect h
      (MvPolynomial.X (variableIndex a t)) = 0 := by
  rw [antiholomorphicEulerDefect_apply]
  simp only [antiholomorphicDerivative_X_unused h _ _ _ t ht, mul_zero, Finset.sum_const_zero]

theorem unusedCoordinateEulerDefect_X {r n : ℕ}
    (a : Fin (r + 1)) (t : Fin n) :
    unusedCoordinateEulerDefect (r := r) (n := n)
      (MvPolynomial.X (variableIndex a t)) =
      if 2 * (r + 1) ≤ t.val then
        MvPolynomial.X (variableIndex a t) else 0 := by
  classical
  rw [unusedCoordinateEulerDefect_apply]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply,
    DeterminantVectors.variableIndex_eq_iff, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a]
  · by_cases ht : 2 * (r + 1) ≤ t.val
    · rw [ite_eq_left ht, Finset.sum_eq_single t]
      · simp only [and_self, ↓reduceIte]
      · intro u hu htu
        simp only [Ne.symm htu, and_false, ↓reduceIte]
      · simp only [Finset.mem_filter, Finset.mem_univ, ht, and_self, not_true_eq_false, ↓reduceIte,
          MvPolynomial.X_ne_zero, imp_self]
    · rw [ite_eq_right ht]
      apply Finset.sum_eq_zero
      intro u hu
      have htu : t ≠ u := by
        intro heq
        subst u
        exact ht (Finset.mem_filter.mp hu).2
      simp only [htu, and_false, ↓reduceIte]
  · intro b hb hab
    apply Finset.sum_eq_zero
    intro u hu
    simp only [Ne.symm hab, false_and, ↓reduceIte]
  · simp only [Finset.mem_univ, not_true_eq_false, true_and, Finset.sum_ite_eq, Finset.mem_filter,
      ite_eq_right_iff, MvPolynomial.X_ne_zero, imp_false, not_le, IsEmpty.forall_iff]

theorem totalAmbientCartan_X_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    totalAmbientCartan h
      (MvPolynomial.X (variableIndex a (evenCoordinate h p))) =
      isotropicVariable h a p - conjugateIsotropicVariable h a p := by
  have hdecomp :
      (MvPolynomial.X (variableIndex a (evenCoordinate h p)) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) =
      ((2 : ℂ)⁻¹) •
        (isotropicVariable h a p + conjugateIsotropicVariable h a p) := by
    simpa only [isotropicVariable, MvPolynomial.C_mul', conjugateIsotropicVariable,
      add_add_sub_cancel,
      smul_add] using
      (isotropic_inverse_even_identity
          (MvPolynomial.X (variableIndex a (evenCoordinate h p)) : MvPolynomial (Fin ((r + 1) *
            n)) ℂ)
          (MvPolynomial.X (variableIndex a (oddCoordinate h p)))).symm
  rw [hdecomp, (totalAmbientCartan h).map_smul, map_add,
    totalAmbientCartan_isotropicVariable,
    totalAmbientCartan_conjugateIsotropicVariable]
  module

theorem totalAmbientCartan_X_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    totalAmbientCartan h
      (MvPolynomial.X (variableIndex a (oddCoordinate h p))) =
      (-Complex.I) •
        (isotropicVariable h a p + conjugateIsotropicVariable h a p) := by
  have hdecomp :
      (MvPolynomial.X (variableIndex a (oddCoordinate h p)) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) =
      (-(Complex.I / 2)) • isotropicVariable h a p +
        (Complex.I / 2) • conjugateIsotropicVariable h a p := by
    simpa only [isotropicVariable, MvPolynomial.C_mul', smul_add, neg_smul,
      conjugateIsotropicVariable] using
      (isotropic_inverse_odd_identity
          (MvPolynomial.X (variableIndex a (evenCoordinate h p)) : MvPolynomial (Fin ((r + 1) *
            n)) ℂ)
          (MvPolynomial.X (variableIndex a (oddCoordinate h p)))).symm
  rw [hdecomp, map_add, (totalAmbientCartan h).map_smul,
    (totalAmbientCartan h).map_smul,
    totalAmbientCartan_isotropicVariable,
    totalAmbientCartan_conjugateIsotropicVariable]
  module

theorem antiholomorphicEulerDefect_eq_zero
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hanti : ∀ a p : Fin (r + 1),
      antiholomorphicDerivative h a p f = 0) :
    antiholomorphicEulerDefect h f = 0 := by
  rw [antiholomorphicEulerDefect_apply]
  simp only [hanti, mul_zero, Finset.sum_const_zero]

theorem unusedCoordinateEulerDefect_eq_zero
    {r n : ℕ}
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hunused : ∀ a : Fin (r + 1), ∀ t : Fin n,
      2 * (r + 1) ≤ t.val →
        MvPolynomial.pderiv (variableIndex a t) f = 0) :
    unusedCoordinateEulerDefect (r := r) (n := n) f = 0 := by
  rw [unusedCoordinateEulerDefect_apply]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro t ht
  rw [hunused a t (Finset.mem_filter.mp ht).2]
  simp only [mul_zero]

theorem totalYoungRowEuler_sub_totalAmbientCartan_eq_defects
    {r n : ℕ} (h : 2 * (r + 1) ≤ n) :
    (2 : ℂ) • (totalYoungRowEuler :
      Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
        (MvPolynomial (Fin ((r + 1) * n)) ℂ)) -
      totalAmbientCartan h =
      (2 : ℂ) • antiholomorphicEulerDefect h +
        (2 : ℂ) • unusedCoordinateEulerDefect (r := r) (n := n) := by
  classical
  apply MvPolynomial.derivation_ext
  intro v
  obtain ⟨⟨a, t⟩, rfl⟩ :=
    (finProdFinEquiv (m := r + 1) (n := n)).surjective v
  change
    (2 : ℂ) • totalYoungRowEuler
        (MvPolynomial.X (variableIndex a t)) -
      totalAmbientCartan h (MvPolynomial.X (variableIndex a t)) =
      (2 : ℂ) • antiholomorphicEulerDefect h
        (MvPolynomial.X (variableIndex a t)) +
        (2 : ℂ) • unusedCoordinateEulerDefect (r := r) (n := n)
          (MvPolynomial.X (variableIndex a t))
  by_cases ht : t.val < 2 * (r + 1)
  · let p := ambientPairIndex t ht
    by_cases he : t.val % 2 = 0
    · have hpair : evenCoordinate h p = t := by
        apply Fin.ext
        change 2 * (t.val / 2) = t.val
        omega
      have hnot : ¬ 2 * (r + 1) ≤ (evenCoordinate h p).val := by
        simp only [evenCoordinate_val]
        have hp := p.isLt
        omega
      rw [← hpair, totalYoungRowEuler_X, totalAmbientCartan_X_even,
        antiholomorphicEulerDefect_X_even,
        unusedCoordinateEulerDefect_X, ite_eq_right hnot]
      simp only [smul_zero, add_zero]
      simp only [isotropicVariable, MvPolynomial.C_mul', conjugateIsotropicVariable,
        add_sub_sub_cancel]
      module
    · have hpair : oddCoordinate h p = t := by
        apply Fin.ext
        change 2 * (t.val / 2) + 1 = t.val
        have hrem : t.val % 2 = 1 := by omega
        omega
      have hnot : ¬ 2 * (r + 1) ≤ (oddCoordinate h p).val := by
        simp only [oddCoordinate_val]
        have hp := p.isLt
        omega
      rw [← hpair, totalYoungRowEuler_X, totalAmbientCartan_X_odd,
        antiholomorphicEulerDefect_X_odd,
        unusedCoordinateEulerDefect_X, ite_eq_right hnot]
      simp only [smul_zero, add_zero]
      have hI :
          (MvPolynomial.C Complex.I :
            MvPolynomial (Fin ((r + 1) * n)) ℂ) ^ 2 = -1 := by
        rw [pow_two, ← map_mul, Complex.I_mul_I, map_neg, map_one]
      simp only [isotropicVariable, conjugateIsotropicVariable,
        Algebra.smul_def, MvPolynomial.algebraMap_eq, map_neg, map_ofNat]
      linear_combination
        (2 : MvPolynomial (Fin ((r + 1) * n)) ℂ) *
          MvPolynomial.X (variableIndex a (oddCoordinate h p)) * hI
  · have htge : 2 * (r + 1) ≤ t.val := Nat.le_of_not_gt ht
    rw [totalYoungRowEuler_X, totalAmbientCartan_X_unused h a t htge,
      antiholomorphicEulerDefect_X_unused h a t htge,
      unusedCoordinateEulerDefect_X, ite_eq_left htge]
    simp only [sub_zero, smul_zero, zero_add]

theorem totalAmbientCartan_eq_maximal_of_rowCartan_antiholomorphic_unused
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hrow : ∀ a : Fin (r + 1),
      rowDerivation a a f = (lam a : ℂ) • f)
    (hanti : ∀ a p : Fin (r + 1),
      antiholomorphicDerivative h a p f = 0)
    (hunused : ∀ a : Fin (r + 1), ∀ t : Fin n,
      2 * (r + 1) ≤ t.val →
        MvPolynomial.pderiv (variableIndex a t) f = 0) :
    totalAmbientCartan h f =
      ((2 * (∑ a : Fin (r + 1), lam a) : ℕ) : ℂ) • f := by
  have hidentity := congrArg
    (fun D : Derivation ℂ
      (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) => D f)
      (totalYoungRowEuler_sub_totalAmbientCartan_eq_defects h)
  change
    (2 : ℂ) • totalYoungRowEuler f - totalAmbientCartan h f =
      (2 : ℂ) • antiholomorphicEulerDefect h f +
        (2 : ℂ) • unusedCoordinateEulerDefect (r := r) (n := n) f at hidentity
  rw [totalYoungRowEuler_of_rowCartan lam f hrow,
    antiholomorphicEulerDefect_eq_zero h f hanti,
    unusedCoordinateEulerDefect_eq_zero f hunused] at hidentity
  have heq : totalAmbientCartan h f =
      (2 : ℂ) • (((∑ a : Fin (r + 1), lam a : ℕ) : ℂ) • f) := by
    have hzero :
        (2 : ℂ) • (((∑ a : Fin (r + 1), lam a : ℕ) : ℂ) • f) -
          totalAmbientCartan h f = 0 := by
      simpa only [smul_zero, add_zero] using hidentity
    exact (sub_eq_zero.mp hzero).symm
  simpa only [smul_smul, Nat.cast_mul, Nat.cast_ofNat] using heq

end HigherYoungAllRankHarmonicHighestCartanEulerIdentity

end

section


open scoped BigOperators

namespace HigherYoungAllRankHarmonicHighestUnusedDerivativeVanishing

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel

theorem isotropicMatrix_det_ne_zero
    {r n : ℕ} (h : 2 * (r + 1) ≤ n) :
    Matrix.det (Matrix.of fun a p : Fin (r + 1) =>
      isotropicVariable h a p) ≠ 0 := by
  intro hzero
  have heval := congrArg (MvPolynomial.eval diagonalEvaluation) hzero
  rw [(MvPolynomial.eval diagonalEvaluation).map_det, map_zero] at heval
  have hmatrix :
      (Matrix.of fun a p : Fin (r + 1) =>
        MvPolynomial.eval diagonalEvaluation (isotropicVariable h a p)) =
        (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
    ext a p
    simp only [Matrix.of_apply]
    simp only [eval_isotropicVariable, Matrix.one_apply]
  change Matrix.det (Matrix.of fun a p : Fin (r + 1) =>
    MvPolynomial.eval diagonalEvaluation (isotropicVariable h a p)) = 0 at heval
  rw [hmatrix, Matrix.det_one] at heval
  exact one_ne_zero heval

theorem isotropicMatrix_transpose_mulVec_injective
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (v : Fin (r + 1) → MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hv : Matrix.mulVec
      (Matrix.transpose (Matrix.of fun a p : Fin (r + 1) =>
        isotropicVariable h a p))
      v = 0) :
    v = 0 := by
  by_contra hne
  have hdet := (Matrix.exists_mulVec_eq_zero_iff).mp ⟨v, hne, hv⟩
  rw [Matrix.det_transpose] at hdet
  exact isotropicMatrix_det_ne_zero h hdet

theorem isotropicMatrix_unusedDerivative_eq_zero_of_shortRoot
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hantiholomorphic : ∀ a p : Fin (r + 1),
      antiholomorphicDerivative h a p f = 0)
    (t : Fin n)
    (hshort : ∀ p : Fin (r + 1), ambientShortPositiveRoot h p t f = 0)
    (p : Fin (r + 1)) :
    (∑ a : Fin (r + 1),
      isotropicVariable h a p *
        MvPolynomial.pderiv (variableIndex a t) f) = 0 := by
  have hp := hshort p
  rw [ambientShortPositiveRoot_apply] at hp
  have hanti (a : Fin (r + 1)) :
      MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f = 0 :=
    hantiholomorphic a p
  simpa only [hanti, mul_zero, sub_zero] using hp

theorem unused_pderiv_eq_zero_of_antiholomorphic_and_shortRoot
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hantiholomorphic : ∀ a p : Fin (r + 1),
      antiholomorphicDerivative h a p f = 0)
    (hshort : ∀ (p : Fin (r + 1)) (t : Fin n),
      2 * (r + 1) ≤ t.val → ambientShortPositiveRoot h p t f = 0)
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    MvPolynomial.pderiv (variableIndex a t) f = 0 := by
  let v : Fin (r + 1) → MvPolynomial (Fin ((r + 1) * n)) ℂ :=
    fun b => MvPolynomial.pderiv (variableIndex b t) f
  have hv : Matrix.mulVec
      (Matrix.transpose (fun b p : Fin (r + 1) => isotropicVariable h b p))
      v = 0 := by
    funext p
    change (∑ b : Fin (r + 1),
      isotropicVariable h b p *
        MvPolynomial.pderiv (variableIndex b t) f) = 0
    exact isotropicMatrix_unusedDerivative_eq_zero_of_shortRoot
      h f hantiholomorphic t (fun p => hshort p t ht) p
  exact congrFun (isotropicMatrix_transpose_mulVec_injective h v hv) a

theorem unused_pderiv_eq_zero_of_antiholomorphic_and_positiveRootKernel
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hantiholomorphic : ∀ a p : Fin (r + 1),
      antiholomorphicDerivative h a p f = 0)
    (hroot : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h α f = 0)
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    MvPolynomial.pderiv (variableIndex a t) f = 0 :=
  unused_pderiv_eq_zero_of_antiholomorphic_and_shortRoot h f
    hantiholomorphic
    (fun p t ht => hroot (.short p t ht)) a t ht

end HigherYoungAllRankHarmonicHighestUnusedDerivativeVanishing

end

section


open scoped BigOperators

namespace HigherYoungAllRankHarmonicHighestRootEnergyIdentity

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition

private def unusedAmbientCoordinates {r n : ℕ} : Finset (Fin n) :=
  Finset.univ.filter (fun t : Fin n => 2 * (r + 1) ≤ t.val)

@[simp] theorem mem_unusedAmbientCoordinates {r n : ℕ}
    (t : Fin n) :
    t ∈ unusedAmbientCoordinates (r := r) (n := n) ↔ 2 * (r + 1) ≤ t.val := by
  simp only [unusedAmbientCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]

theorem shortRoot_unusedDerivative
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (b p : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    MvPolynomial.pderiv (variableIndex b t)
        (ambientShortPositiveRoot h p t f) =
      (∑ a : Fin (r + 1),
        (isotropicVariable h a p *
          MvPolynomial.pderiv (variableIndex b t)
            (MvPolynomial.pderiv (variableIndex a t) f) -
        MvPolynomial.X (variableIndex a t) *
          MvPolynomial.pderiv (variableIndex b t)
            (antiholomorphicDerivative h a p f))) -
        antiholomorphicDerivative h b p f := by
  classical
  rw [ambientShortPositiveRoot_apply, map_sum]
  change
    (∑ a : Fin (r + 1),
      MvPolynomial.pderiv (variableIndex b t)
        (isotropicVariable h a p *
            MvPolynomial.pderiv (variableIndex a t) f -
          MvPolynomial.X (variableIndex a t) *
            antiholomorphicDerivative h a p f)) = _
  simp_rw [map_sub, MvPolynomial.pderiv_mul,
    pderiv_outside_isotropicVariable h b _ p t ht,
    zero_mul, zero_add, MvPolynomial.pderiv_X]
  simp only [Pi.single_apply, DeterminantVectors.variableIndex_eq_iff,
    and_true, ite_mul, one_mul, zero_mul]
  calc
    _ = ∑ a : Fin (r + 1),
          ((isotropicVariable h a p *
            MvPolynomial.pderiv (variableIndex b t)
              (MvPolynomial.pderiv (variableIndex a t) f) -
            MvPolynomial.X (variableIndex a t) *
              MvPolynomial.pderiv (variableIndex b t)
                (antiholomorphicDerivative h a p f)) -
            if a = b then antiholomorphicDerivative h a p f else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem shortRoot_unusedDerivative_sum
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (b p : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    (∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
      MvPolynomial.pderiv (variableIndex b t)
        (ambientShortPositiveRoot h p t f)) =
      (∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
        ∑ a : Fin (r + 1),
          (isotropicVariable h a p *
            MvPolynomial.pderiv (variableIndex b t)
              (MvPolynomial.pderiv (variableIndex a t) f) -
          MvPolynomial.X (variableIndex a t) *
            MvPolynomial.pderiv (variableIndex b t)
              (antiholomorphicDerivative h a p f))) -
        (unusedAmbientCoordinates (r := r) (n := n)).card •
          antiholomorphicDerivative h b p f := by
  classical
  calc
    _ = ∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
          ((∑ a : Fin (r + 1),
            (isotropicVariable h a p *
              MvPolynomial.pderiv (variableIndex b t)
                (MvPolynomial.pderiv (variableIndex a t) f) -
            MvPolynomial.X (variableIndex a t) *
              MvPolynomial.pderiv (variableIndex b t)
                (antiholomorphicDerivative h a p f))) -
            antiholomorphicDerivative h b p f) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact shortRoot_unusedDerivative h b p t
        ((mem_unusedAmbientCoordinates t).mp ht) f
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

theorem shortRoot_unusedDerivative_sum_eq_card_smul_of_rootKernel
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (b p : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hroot : ∀ t : Fin n, 2 * (r + 1) ≤ t.val →
      ambientShortPositiveRoot h p t f = 0) :
    (∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
      ∑ a : Fin (r + 1),
        (isotropicVariable h a p *
          MvPolynomial.pderiv (variableIndex b t)
            (MvPolynomial.pderiv (variableIndex a t) f) -
        MvPolynomial.X (variableIndex a t) *
          MvPolynomial.pderiv (variableIndex b t)
            (antiholomorphicDerivative h a p f))) =
      (unusedAmbientCoordinates (r := r) (n := n)).card •
        antiholomorphicDerivative h b p f := by
  have hzero :
      (∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
        MvPolynomial.pderiv (variableIndex b t)
          (ambientShortPositiveRoot h p t f)) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [hroot t ((mem_unusedAmbientCoordinates t).mp ht), map_zero]
  rw [shortRoot_unusedDerivative_sum h b p f] at hzero
  exact sub_eq_zero.mp hzero

end HigherYoungAllRankHarmonicHighestRootEnergyIdentity

end

namespace HigherYoungIsotropicComplexTraceDecomposition

section


open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors

private def holomorphicDerivative {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ)) -
    (MvPolynomial.C Complex.I :
      MvPolynomial (Fin ((r + 1) * n)) ℂ) •
      MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))

@[simp] theorem holomorphicDerivative_apply {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    holomorphicDerivative h a p f =
      MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f -
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f := by
  rfl

@[simp] theorem antiholomorphicDerivative_apply {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    antiholomorphicDerivative h a p f =
      MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f := by
  rfl

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestRootEnergyIdentity
open MetricCodes.Spherical.HigherYoungFullComplexSpanTraceFree
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem occupiedEven_disjoint_occupiedOdd
    {r n : ℕ} (h : 2 * (r + 1) ≤ n) :
    Disjoint
      (Finset.univ.image (evenCoordinate h))
      (Finset.univ.image (oddCoordinate h)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht he
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp ht
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp he
  exact evenCoordinate_ne_oddCoordinate h p q (hp.trans hq.symm)

theorem occupiedCoordinates_eq_even_union_odd
    {r n : ℕ} (h : 2 * (r + 1) ≤ n) :
    Finset.univ.filter (fun t : Fin n => t.val < 2 * (r + 1)) =
      Finset.univ.image (evenCoordinate h) ∪
        Finset.univ.image (oddCoordinate h) := by
  classical
  ext t
  constructor
  · intro ht
    have hlt : t.val < 2 * (r + 1) :=
      (Finset.mem_filter.mp ht).2
    let p : Fin (r + 1) := ⟨t.val / 2, by omega⟩
    by_cases he : t.val % 2 = 0
    · have hp : evenCoordinate h p = t := by
        apply Fin.ext
        change 2 * (t.val / 2) = t.val
        omega
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩)
    · have hp : oddCoordinate h p = t := by
        apply Fin.ext
        change 2 * (t.val / 2) + 1 = t.val
        have hrem : t.val % 2 = 1 := by omega
        omega
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩)
  · intro ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ t, ?_⟩
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
      have hp := p.isLt
      simp only [evenCoordinate_val]
      omega
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
      have hp := p.isLt
      simp only [oddCoordinate_val]
      omega

theorem sum_occupied_eq_even_odd
    {r n : ℕ} {A : Type*} [AddCommMonoid A]
    (h : 2 * (r + 1) ≤ n) (g : Fin n → A) :
    (∑ t ∈ Finset.univ.filter
      (fun t : Fin n => t.val < 2 * (r + 1)), g t) =
      ∑ p : Fin (r + 1),
        (g (evenCoordinate h p) + g (oddCoordinate h p)) := by
  classical
  rw [occupiedCoordinates_eq_even_union_odd h,
    Finset.sum_union (occupiedEven_disjoint_occupiedOdd h)]
  have heven : Set.InjOn (evenCoordinate h)
      (↑(Finset.univ : Finset (Fin (r + 1))) : Set (Fin (r + 1))) := by
    intro p _ q _ hpq
    exact (evenCoordinate_inj h p q).mp hpq
  have hodd : Set.InjOn (oddCoordinate h)
      (↑(Finset.univ : Finset (Fin (r + 1))) : Set (Fin (r + 1))) := by
    intro p _ q _ hpq
    exact (oddCoordinate_inj h p q).mp hpq
  rw [Finset.sum_image heven, Finset.sum_image hodd,
    ← Finset.sum_add_distrib]

theorem sum_univ_eq_even_odd_add_unused
    {r n : ℕ} {A : Type*} [AddCommMonoid A]
    (h : 2 * (r + 1) ≤ n) (g : Fin n → A) :
    (∑ t : Fin n, g t) =
      (∑ p : Fin (r + 1),
        (g (evenCoordinate h p) + g (oddCoordinate h p))) +
      ∑ t ∈ unusedAmbientCoordinates (r := r) (n := n), g t := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    Finset.univ (fun t : Fin n => t.val < 2 * (r + 1)) g
  have hunused :
      Finset.univ.filter
        (fun t : Fin n => ¬t.val < 2 * (r + 1)) =
        unusedAmbientCoordinates (r := r) (n := n) := by
    ext t
    simp only [not_lt, Finset.mem_filter, Finset.mem_univ, true_and, unusedAmbientCoordinates]
  rw [hunused, sum_occupied_eq_even_odd h g] at hsplit
  exact hsplit.symm

theorem occupiedMixedTrace_eq_holomorphic_antiholomorphic
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a b p : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
          (MvPolynomial.pderiv (variableIndex b (evenCoordinate h p)) f) +
        MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
          (MvPolynomial.pderiv (variableIndex b (oddCoordinate h p)) f) =
      ((2 : ℂ)⁻¹) •
        (holomorphicDerivative h a p (antiholomorphicDerivative h b p f) +
          antiholomorphicDerivative h a p (holomorphicDerivative h b p f)) := by
  simp only [holomorphicDerivative_apply, antiholomorphicDerivative_apply,
    map_add, map_sub, MvPolynomial.pderiv_C_mul,
    MvPolynomial.smul_eq_C_mul]
  have hI : (MvPolynomial.C Complex.I :
      MvPolynomial (Fin ((r + 1) * n)) ℂ) ^ 2 = -1 := by
    rw [pow_two, ← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hhalf :
      (MvPolynomial.C ((2 : ℂ)⁻¹) :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) * 2 = 1 := by
    rw [← map_ofNat (MvPolynomial.C :
      ℂ →+* MvPolynomial (Fin ((r + 1) * n)) ℂ) 2,
      ← map_mul]
    norm_num
  linear_combination
    -(MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (MvPolynomial.pderiv (variableIndex b (evenCoordinate h p)) f) +
      MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
        (MvPolynomial.pderiv (variableIndex b (oddCoordinate h p)) f)) * hhalf +
    (2 * MvPolynomial.C ((2 : ℂ)⁻¹) *
      MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
        (MvPolynomial.pderiv (variableIndex b (oddCoordinate h p)) f)) * hI

theorem complexTraceOperator_eq_isotropicDerivative_add_unused
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a b : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    complexTraceOperator a b f =
      ((2 : ℂ)⁻¹) •
        (∑ p : Fin (r + 1),
          (holomorphicDerivative h a p
            (antiholomorphicDerivative h b p f) +
            antiholomorphicDerivative h a p
              (holomorphicDerivative h b p f))) +
        ∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
          MvPolynomial.pderiv (variableIndex a t)
            (MvPolynomial.pderiv (variableIndex b t) f) := by
  unfold complexTraceOperator
  rw [sum_univ_eq_even_odd_add_unused h]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact occupiedMixedTrace_eq_holomorphic_antiholomorphic h a b p f

theorem unusedMixedHessian_eq_neg_isotropicDerivative_of_traceFree
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a b : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (htrace : complexTraceOperator a b f = 0) :
    (∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
      MvPolynomial.pderiv (variableIndex a t)
        (MvPolynomial.pderiv (variableIndex b t) f)) =
      -(((2 : ℂ)⁻¹) •
        (∑ p : Fin (r + 1),
          (holomorphicDerivative h a p
            (antiholomorphicDerivative h b p f) +
            antiholomorphicDerivative h a p
              (holomorphicDerivative h b p f)))) := by
  rw [complexTraceOperator_eq_isotropicDerivative_add_unused h a b f]
    at htrace
  exact eq_neg_of_add_eq_zero_right htrace

theorem unusedMixedHessian_of_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (a b : Fin (r + 1)) :
    (∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
      MvPolynomial.pderiv (variableIndex a t)
        (MvPolynomial.pderiv (variableIndex b t) f)) =
      -(((2 : ℂ)⁻¹) •
        (∑ p : Fin (r + 1),
          (holomorphicDerivative h a p
            (antiholomorphicDerivative h b p f) +
            antiholomorphicDerivative h a p
              (holomorphicDerivative h b p f)))) := by
  apply unusedMixedHessian_eq_neg_isotropicDerivative_of_traceFree
  exact complexTraceOperator_of_mem_fullYoungComplexPolynomialSpan
    lam hf a b

end

end HigherYoungIsotropicComplexTraceDecomposition

section


open scoped BigOperators

namespace HigherYoungAllRankAntiHolomorphicRootCommutators

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors

theorem complex_pderiv_commute
    {N : ℕ} (i j : Fin N) (f : MvPolynomial (Fin N) ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.derivation_C, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f a hf =>
      simp only [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, map_add, hf]
      split <;> split <;> simp_all <;> ring

theorem pderiv_rowDerivation
    {r n : ℕ} (a i j : Fin (r + 1)) (k : Fin n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    MvPolynomial.pderiv (variableIndex a k) (rowDerivation i j f) =
      (if a = i then MvPolynomial.pderiv (variableIndex j k) f else 0) +
        rowDerivation i j (MvPolynomial.pderiv (variableIndex a k) f) := by
  classical
  simp only [rowDerivation_apply, map_sum, MvPolynomial.pderiv_mul,
    Finset.sum_add_distrib]
  apply congrArg₂ (fun x y : MvPolynomial (Fin ((r + 1) * n)) ℂ => x + y)
  · by_cases hai : a = i
    · subst a
      simp only [MvPolynomial.pderiv_X, Pi.single_apply, DeterminantVectors.variableIndex_eq_iff,
        true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff, hai,
        false_and, not_false_eq_true, Pi.single_eq_of_ne', zero_mul, Finset.sum_const_zero,
        ↓reduceIte]
  · apply Finset.sum_congr rfl
    intro l _
    rw [complex_pderiv_commute]

theorem rowDerivation_antiholomorphicDerivative_commutator
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a b c p : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    rowDerivation a b (antiholomorphicDerivative h c p f) -
        antiholomorphicDerivative h c p (rowDerivation a b f) =
      if a = c then -antiholomorphicDerivative h b p f else 0 := by
  classical
  change
    rowDerivation a b
        (MvPolynomial.pderiv (variableIndex c (evenCoordinate h p)) f +
          MvPolynomial.C Complex.I *
            MvPolynomial.pderiv (variableIndex c (oddCoordinate h p)) f) -
      (MvPolynomial.pderiv (variableIndex c (evenCoordinate h p))
          (rowDerivation a b f) +
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex c (oddCoordinate h p))
            (rowDerivation a b f)) =
      if a = c then
        -(MvPolynomial.pderiv (variableIndex b (evenCoordinate h p)) f +
          MvPolynomial.C Complex.I *
            MvPolynomial.pderiv (variableIndex b (oddCoordinate h p)) f)
      else 0
  rw [(rowDerivation a b).map_add, (rowDerivation a b).leibniz,
    pderiv_rowDerivation c a b (evenCoordinate h p) f,
    pderiv_rowDerivation c a b (oddCoordinate h p) f]
  have hconstant :
      rowDerivation a b (MvPolynomial.C Complex.I :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) = 0 := by
    exact (rowDerivation a b).map_algebraMap Complex.I
  rw [hconstant]
  by_cases hac : a = c
  · subst c
    simp only [ite_true, Algebra.smul_def,
      Algebra.algebraMap_self_apply]
    ring
  · have hca : c ≠ a := Ne.symm hac
    simp only [hac, hca, ite_false, Algebra.smul_def,
      Algebra.algebraMap_self_apply]
    ring

theorem rowDerivation_antiholomorphicDerivative_matching
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a b p : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    rowDerivation a b (antiholomorphicDerivative h a p f) -
        antiholomorphicDerivative h a p (rowDerivation a b f) =
      -antiholomorphicDerivative h b p f := by
  simpa only [HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply,
    rowDerivation_apply, map_add, Derivation.leibniz, smul_eq_mul, MvPolynomial.derivation_C,
      mul_zero, add_zero,
    map_sum, MvPolynomial.pderiv_X, neg_add_rev, ↓reduceIte] using
    rowDerivation_antiholomorphicDerivative_commutator h a b a p f

end HigherYoungAllRankAntiHolomorphicRootCommutators

end

section


open scoped BigOperators

namespace HigherYoungAllRankShortRootAntiHolomorphicMixedTraceCancellation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestRootEnergyIdentity
open MetricCodes.Spherical.HigherYoungIsotropicComplexTraceDecomposition
open MetricCodes.Spherical.HigherYoungAllRankAntiHolomorphicRootCommutators

theorem occupiedRowEuler_eq_isotropicDerivatives
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a b q : Fin (r + 1))
    (g : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    MvPolynomial.X (variableIndex a (evenCoordinate h q)) *
          MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) g +
        MvPolynomial.X (variableIndex a (oddCoordinate h q)) *
          MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) g =
      ((2 : ℂ)⁻¹) •
        (isotropicVariable h a q * holomorphicDerivative h b q g +
          conjugateIsotropicVariable h a q *
            antiholomorphicDerivative h b q g) := by
  simp only [holomorphicDerivative, antiholomorphicDerivative,
    isotropicVariable, conjugateIsotropicVariable,
    Derivation.add_apply, Derivation.sub_apply,
    Derivation.smul_apply, Algebra.smul_def]
  have hI : (MvPolynomial.C Complex.I :
      MvPolynomial (Fin ((r + 1) * n)) ℂ) ^ 2 = -1 := by
    rw [pow_two, ← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hhalf :
      (MvPolynomial.C ((2 : ℂ)⁻¹) :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) * 2 = 1 := by
    rw [← map_ofNat (MvPolynomial.C :
      ℂ →+* MvPolynomial (Fin ((r + 1) * n)) ℂ) 2,
      ← map_mul]
    norm_num
  change
    MvPolynomial.X (variableIndex a (evenCoordinate h q)) *
          MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) g +
        MvPolynomial.X (variableIndex a (oddCoordinate h q)) *
          MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) g =
      MvPolynomial.C ((2 : ℂ)⁻¹) *
        ((MvPolynomial.X (variableIndex a (evenCoordinate h q)) +
            MvPolynomial.C Complex.I *
              MvPolynomial.X (variableIndex a (oddCoordinate h q))) *
          (MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) g -
            MvPolynomial.C Complex.I *
              MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) g) +
          (MvPolynomial.X (variableIndex a (evenCoordinate h q)) -
            MvPolynomial.C Complex.I *
              MvPolynomial.X (variableIndex a (oddCoordinate h q))) *
            (MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) g +
              MvPolynomial.C Complex.I *
                MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) g))
  linear_combination
    -(MvPolynomial.X (variableIndex a (evenCoordinate h q)) *
        MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) g +
      MvPolynomial.X (variableIndex a (oddCoordinate h q)) *
        MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) g) * hhalf +
    (2 * MvPolynomial.C ((2 : ℂ)⁻¹) *
      MvPolynomial.X (variableIndex a (oddCoordinate h q)) *
      MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) g) * hI

theorem rowDerivation_eq_isotropicDerivatives_add_unused
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a b : Fin (r + 1))
    (g : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    rowDerivation a b g =
      ((2 : ℂ)⁻¹) •
        (∑ q : Fin (r + 1),
          (isotropicVariable h a q * holomorphicDerivative h b q g +
            conjugateIsotropicVariable h a q *
              antiholomorphicDerivative h b q g)) +
        ∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
          MvPolynomial.X (variableIndex a t) *
            MvPolynomial.pderiv (variableIndex b t) g := by
  rw [rowDerivation_apply, sum_univ_eq_even_odd_add_unused h]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact occupiedRowEuler_eq_isotropicDerivatives h a b q g

end HigherYoungAllRankShortRootAntiHolomorphicMixedTraceCancellation

end

section


open scoped BigOperators

namespace HigherYoungAllRankHarmonicRootEnergyTraceRowCancellation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestRootEnergyIdentity
open MetricCodes.Spherical.HigherYoungIsotropicComplexTraceDecomposition
open MetricCodes.Spherical.HigherYoungAllRankShortRootAntiHolomorphicMixedTraceCancellation
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

private theorem energy_trace_row_algebra_metriccodes2_0c475dba
    {ι κ τ S : Type*} [Fintype ι] [Fintype κ]
    [CommRing S]
    (U : Finset τ) (p : κ) (half : S)
    (z zbar : ι → κ → S)
    (H V : ι → τ → S)
    (HBA ABH : ι → κ → S)
    (HA AB : ι → κ → S)
    (row : ι → S)
    (hh : ∀ a : ι,
      (∑ t ∈ U, H a t) =
        -(half * ∑ q : κ, (HBA a q + ABH a q)))
    (hr : ∀ a : ι,
      row a = half * (∑ q : κ,
        (z a q * HA a q + zbar a q * AB a q)) +
          ∑ t ∈ U, V a t) :
    (∑ t ∈ U, ∑ a : ι, (z a p * H a t - V a t)) =
      -(∑ a : ι, row a) +
        half * (∑ q : κ, ∑ a : ι,
          (z a q * HA a q + zbar a q * AB a q -
            z a p * HBA a q - z a p * ABH a q)) := by
  classical
  calc
    (∑ t ∈ U, ∑ a : ι, (z a p * H a t - V a t)) =
        ∑ a : ι,
          (z a p * (∑ t ∈ U, H a t) - ∑ t ∈ U, V a t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = ∑ a : ι,
        (-row a + half * ∑ q : κ,
          (z a q * HA a q + zbar a q * AB a q -
            z a p * HBA a q - z a p * ABH a q)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hh a, hr a]
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp_rw [← Finset.mul_sum]
      simp_rw [Finset.sum_add_distrib]
      ring
    _ = -(∑ a : ι, row a) +
        half * (∑ q : κ, ∑ a : ι,
          (z a q * HA a q + zbar a q * AB a q -
            z a p * HBA a q - z a p * ABH a q)) := by
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum, Finset.sum_comm]

theorem shortRoot_mixedRemainder_eq_neg_rowDerivation_add_isotropic_traces
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (b p : Fin (r + 1)) :
    (∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
      ∑ a : Fin (r + 1),
        (isotropicVariable h a p *
          MvPolynomial.pderiv (variableIndex b t)
            (MvPolynomial.pderiv (variableIndex a t) f) -
          MvPolynomial.X (variableIndex a t) *
            MvPolynomial.pderiv (variableIndex b t)
              (antiholomorphicDerivative h a p f))) =
      -(∑ a : Fin (r + 1),
        rowDerivation a b (antiholomorphicDerivative h a p f)) +
        ((2 : ℂ)⁻¹) •
          (∑ q : Fin (r + 1), ∑ a : Fin (r + 1),
            (isotropicVariable h a q *
              holomorphicDerivative h b q
                (antiholomorphicDerivative h a p f) +
              conjugateIsotropicVariable h a q *
                antiholomorphicDerivative h b q
                  (antiholomorphicDerivative h a p f) -
              isotropicVariable h a p *
                holomorphicDerivative h b q
                  (antiholomorphicDerivative h a q f) -
              isotropicVariable h a p *
                antiholomorphicDerivative h b q
                  (holomorphicDerivative h a q f))) := by
  classical
  let P := MvPolynomial (Fin ((r + 1) * n)) ℂ
  let half : P := MvPolynomial.C ((2 : ℂ)⁻¹)
  have hh (a : Fin (r + 1)) :
      (∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
        MvPolynomial.pderiv (variableIndex b t)
          (MvPolynomial.pderiv (variableIndex a t) f)) =
        -(half * ∑ q : Fin (r + 1),
          (holomorphicDerivative h b q
            (antiholomorphicDerivative h a q f) +
            antiholomorphicDerivative h b q
              (holomorphicDerivative h a q f))) := by
    simpa only [antiholomorphicDerivative_apply, holomorphicDerivative_apply, map_add,
      Derivation.leibniz,
      smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero, map_sub,
        MvPolynomial.smul_eq_C_mul] using
      (unusedMixedHessian_of_mem_fullYoungComplexPolynomialSpan h lam hf b a)
  have hr (a : Fin (r + 1)) :
      rowDerivation a b (antiholomorphicDerivative h a p f) =
        half * (∑ q : Fin (r + 1),
          (isotropicVariable h a q *
            holomorphicDerivative h b q
              (antiholomorphicDerivative h a p f) +
            conjugateIsotropicVariable h a q *
              antiholomorphicDerivative h b q
                (antiholomorphicDerivative h a p f))) +
          ∑ t ∈ unusedAmbientCoordinates (r := r) (n := n),
            MvPolynomial.X (variableIndex a t) *
              MvPolynomial.pderiv (variableIndex b t)
                (antiholomorphicDerivative h a p f) := by
    simpa only [antiholomorphicDerivative_apply, rowDerivation_apply, map_add,
      Derivation.leibniz, smul_eq_mul,
      MvPolynomial.derivation_C, mul_zero, add_zero, holomorphicDerivative_apply,
        MvPolynomial.smul_eq_C_mul] using
      (rowDerivation_eq_isotropicDerivatives_add_unused h a b (antiholomorphicDerivative h a p f))
  have hidentity := energy_trace_row_algebra_metriccodes2_0c475dba
    (unusedAmbientCoordinates (r := r) (n := n)) p half
    (fun a q => isotropicVariable h a q)
    (fun a q => conjugateIsotropicVariable h a q)
    (fun a t => MvPolynomial.pderiv (variableIndex b t)
      (MvPolynomial.pderiv (variableIndex a t) f))
    (fun a t => MvPolynomial.X (variableIndex a t) *
      MvPolynomial.pderiv (variableIndex b t)
        (antiholomorphicDerivative h a p f))
    (fun a q => holomorphicDerivative h b q
      (antiholomorphicDerivative h a q f))
    (fun a q => antiholomorphicDerivative h b q
      (holomorphicDerivative h a q f))
    (fun a q => holomorphicDerivative h b q
      (antiholomorphicDerivative h a p f))
    (fun a q => antiholomorphicDerivative h b q
      (antiholomorphicDerivative h a p f))
    (fun a => rowDerivation a b (antiholomorphicDerivative h a p f))
    hh hr
  simpa only [antiholomorphicDerivative_apply, map_add, Derivation.leibniz, smul_eq_mul,
    MvPolynomial.derivation_C, mul_zero, add_zero, Finset.sum_sub_distrib, rowDerivation_apply,
    holomorphicDerivative_apply, map_sub, MvPolynomial.smul_eq_C_mul] using hidentity

end HigherYoungAllRankHarmonicRootEnergyTraceRowCancellation

end

section


open scoped BigOperators

namespace HigherYoungAmbientDifferenceRootAntiHolomorphicDerivativeCommutator

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors

private theorem complexPolynomial_pderiv_commute_metriccodes2_3f70f505
    {N : ℕ} (i j : Fin N) (f : MvPolynomial (Fin N) ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.derivation_C, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f a hf =>
      simp only [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, map_add, hf]
      split <;> split <;> simp_all <;> ring

private def differenceHolomorphicDerivative_metriccodes2_3f70f505 {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) -
    (MvPolynomial.C Complex.I : MvPolynomial (Fin ((r + 1) * n)) ℂ) •
      MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))

private theorem pderiv_even_conjugateIsotropicVariable_metriccodes2_3f70f505
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (conjugateIsotropicVariable h i j) =
      if a = i ∧ p = j then 1 else 0 := by
  classical
  simp [conjugateIsotropicVariable, Pi.single_apply, DeterminantVectors.variableIndex_eq_iff,
    evenCoordinate_inj, evenCoordinate_ne_oddCoordinate,
    eq_comm]

private theorem pderiv_odd_conjugateIsotropicVariable_metriccodes2_3f70f505
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
        (conjugateIsotropicVariable h i j) =
      if a = i ∧ p = j then -MvPolynomial.C Complex.I else 0 := by
  classical
  simp only [conjugateIsotropicVariable, map_sub, MvPolynomial.pderiv_X, ne_eq,
    DeterminantVectors.variableIndex_eq_iff, eq_comm, evenCoordinate_ne_oddCoordinate, and_false,
    not_false_eq_true, Pi.single_eq_of_ne, Derivation.leibniz, Pi.single_apply, oddCoordinate_inj,
    smul_eq_mul, mul_ite, mul_one, mul_zero, MvPolynomial.derivation_C, add_zero, zero_sub]
  split_ifs <;> simp

private theorem antiholomorphicDerivative_conjugateIsotropicVariable_metriccodes2_3f70f505
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    antiholomorphicDerivative h a p (conjugateIsotropicVariable h i j) =
      if a = i ∧ p = j then 2 else 0 := by
  change MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
      (conjugateIsotropicVariable h i j) +
    MvPolynomial.C Complex.I *
      MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
        (conjugateIsotropicVariable h i j) = _
  rw [pderiv_even_conjugateIsotropicVariable_metriccodes2_3f70f505,
    pderiv_odd_conjugateIsotropicVariable_metriccodes2_3f70f505]
  split_ifs with hp
  · simp only [mul_neg, ← map_mul, Complex.I_mul_I, MvPolynomial.C_neg, MvPolynomial.C_1, neg_neg]
    norm_num
  · simp only [mul_zero, add_zero]

private theorem
  antiholomorphicDerivative_differenceHolomorphicDerivative_commute_metriccodes2_3f70f505
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a p b q : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    antiholomorphicDerivative h a p (differenceHolomorphicDerivative_metriccodes2_3f70f505 h b q
      f) =
      differenceHolomorphicDerivative_metriccodes2_3f70f505 h b q (antiholomorphicDerivative h a
        p f) := by
  change
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) f -
          MvPolynomial.C Complex.I *
            MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) f) +
      MvPolynomial.C Complex.I *
        MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
          (MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) f -
            MvPolynomial.C Complex.I *
              MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) f) =
      MvPolynomial.pderiv (variableIndex b (evenCoordinate h q))
        (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
          MvPolynomial.C Complex.I *
            MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f) -
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex b (oddCoordinate h q))
            (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
              MvPolynomial.C Complex.I *
                MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f)
  simp only [map_sub, map_add, MvPolynomial.pderiv_C_mul]
  rw [complexPolynomial_pderiv_commute_metriccodes2_3f70f505
      (variableIndex a (evenCoordinate h p))
      (variableIndex b (evenCoordinate h q)) f,
    complexPolynomial_pderiv_commute_metriccodes2_3f70f505
      (variableIndex a (evenCoordinate h p))
      (variableIndex b (oddCoordinate h q)) f,
    complexPolynomial_pderiv_commute_metriccodes2_3f70f505
      (variableIndex a (oddCoordinate h p))
      (variableIndex b (evenCoordinate h q)) f,
    complexPolynomial_pderiv_commute_metriccodes2_3f70f505
      (variableIndex a (oddCoordinate h p))
      (variableIndex b (oddCoordinate h q)) f]
  ring

theorem antiholomorphicDerivative_antiholomorphicDerivative_commute
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a p b q : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    antiholomorphicDerivative h a p (antiholomorphicDerivative h b q f) =
      antiholomorphicDerivative h b q (antiholomorphicDerivative h a p f) := by
  change
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) f +
          MvPolynomial.C Complex.I *
            MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) f) +
      MvPolynomial.C Complex.I *
        MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
          (MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) f +
            MvPolynomial.C Complex.I *
              MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) f) =
      MvPolynomial.pderiv (variableIndex b (evenCoordinate h q))
        (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
          MvPolynomial.C Complex.I *
            MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f) +
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex b (oddCoordinate h q))
            (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
              MvPolynomial.C Complex.I *
                MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f)
  simp only [map_add, MvPolynomial.pderiv_C_mul]
  rw [complexPolynomial_pderiv_commute_metriccodes2_3f70f505
      (variableIndex a (evenCoordinate h p))
      (variableIndex b (evenCoordinate h q)) f,
    complexPolynomial_pderiv_commute_metriccodes2_3f70f505
      (variableIndex a (evenCoordinate h p))
      (variableIndex b (oddCoordinate h q)) f,
    complexPolynomial_pderiv_commute_metriccodes2_3f70f505
      (variableIndex a (oddCoordinate h p))
      (variableIndex b (evenCoordinate h q)) f,
    complexPolynomial_pderiv_commute_metriccodes2_3f70f505
      (variableIndex a (oddCoordinate h p))
      (variableIndex b (oddCoordinate h q)) f]
  ring

private theorem ambientPositiveRoot_apply_holomorphic_antiholomorphic_metriccodes2_3f70f505
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p q : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ambientPositiveRoot h p q f =
      ∑ a : Fin (r + 1),
        (isotropicVariable h a p * differenceHolomorphicDerivative_metriccodes2_3f70f505 h a q f -
          conjugateIsotropicVariable h a q *
            antiholomorphicDerivative h a p f) := by
  rw [ambientPositiveRoot_apply]
  rfl

theorem ambientPositiveRoot_antiholomorphicDerivative_commutator_apply
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p q b s : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ambientPositiveRoot h p q (antiholomorphicDerivative h b s f) -
      antiholomorphicDerivative h b s (ambientPositiveRoot h p q f) =
      if s = q then (2 : ℂ) • antiholomorphicDerivative h b p f else 0 := by
  classical
  rw [ambientPositiveRoot_apply_holomorphic_antiholomorphic_metriccodes2_3f70f505,
    ambientPositiveRoot_apply_holomorphic_antiholomorphic_metriccodes2_3f70f505, map_sum,
    ← Finset.sum_sub_distrib]
  have hterm (a : Fin (r + 1)) :
      (isotropicVariable h a p *
          differenceHolomorphicDerivative_metriccodes2_3f70f505 h a q
            (antiholomorphicDerivative h b s f) -
        conjugateIsotropicVariable h a q *
          antiholomorphicDerivative h a p
            (antiholomorphicDerivative h b s f)) -
        antiholomorphicDerivative h b s
          (isotropicVariable h a p * differenceHolomorphicDerivative_metriccodes2_3f70f505 h a q f -
            conjugateIsotropicVariable h a q *
              antiholomorphicDerivative h a p f) =
      if a = b ∧ s = q then
        (2 : ℂ) • antiholomorphicDerivative h b p f
      else 0 := by
    rw [map_sub, (antiholomorphicDerivative h b s).leibniz,
      (antiholomorphicDerivative h b s).leibniz,
      antiholomorphicDerivative_isotropicVariable,
      antiholomorphicDerivative_conjugateIsotropicVariable_metriccodes2_3f70f505,
      antiholomorphicDerivative_differenceHolomorphicDerivative_commute_metriccodes2_3f70f505,
      antiholomorphicDerivative_antiholomorphicDerivative_commute]
    by_cases hab : a = b
    · subst a
      by_cases hsq : s = q
      · subst s
        simp only [HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply,
          map_add, Derivation.leibniz, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero,
          and_self, ↓reduceIte, sub_sub_sub_cancel_left, add_sub_cancel_left, Algebra.smul_def,
          MvPolynomial.algebraMap_eq]
        rw [map_ofNat (MvPolynomial.C :
          ℂ →+* MvPolynomial (Fin ((r + 1) * n)) ℂ) 2]
        ring
      · simp only [HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply,
          map_add, Derivation.leibniz, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero,
          hsq, and_false, ↓reduceIte, sub_self]
    · simp only [HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply,
        map_add, Derivation.leibniz, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero,
        Ne.symm hab, false_and, ↓reduceIte, sub_self, hab]
  simp_rw [hterm]
  by_cases hsq : s = q <;> simp [hsq]

theorem ambientPositiveRoot_antiholomorphicDerivative_of_rootKernel
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p q b : Fin (r + 1)) (_hpq : p ≠ q)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : ambientPositiveRoot h p q f = 0) :
    ambientPositiveRoot h p q (antiholomorphicDerivative h b q f) =
      (2 : ℂ) • antiholomorphicDerivative h b p f := by
  have hcomm :=
    ambientPositiveRoot_antiholomorphicDerivative_commutator_apply
      h p q b q f
  simpa only [HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply,
    map_add, Derivation.leibniz, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero,
    smul_add, hf, map_zero, sub_zero, ↓reduceIte] using hcomm

end HigherYoungAmbientDifferenceRootAntiHolomorphicDerivativeCommutator

namespace HigherYoungAmbientSumRootHolomorphicDerivativeCommutator

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungAmbientPositiveRootGeneratorAction
open MetricCodes.Spherical.HigherYoungIsotropicComplexTraceDecomposition

attribute [-simp] antiholomorphicDerivative_apply holomorphicDerivative_apply

theorem holomorphicDerivative_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    holomorphicDerivative h a p (isotropicVariable h i j) =
      if a = i ∧ p = j then 2 else 0 := by
  rw [holomorphicDerivative_apply, pderiv_even_isotropicVariable,
    pderiv_odd_isotropicVariable]
  split_ifs with heq
  · simp only [← map_mul, Complex.I_mul_I, MvPolynomial.C_neg, MvPolynomial.C_1, sub_neg_eq_add]
    norm_num
  · simp only [mul_zero, sub_self]

theorem complexPolynomial_pderiv_commute {ι : Type*}
    (i j : ι) (f : MvPolynomial ι ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.derivation_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp =>
      simp only [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, map_add, hp]
      split <;> split <;> simp_all <;> ring

theorem antiholomorphicDerivative_holomorphicDerivative_commute
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a p b q : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    antiholomorphicDerivative h a p (holomorphicDerivative h b q f) =
      holomorphicDerivative h b q (antiholomorphicDerivative h a p f) := by
  change
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) f -
          MvPolynomial.C Complex.I *
            MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) f) +
      MvPolynomial.C Complex.I *
        MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
          (MvPolynomial.pderiv (variableIndex b (evenCoordinate h q)) f -
            MvPolynomial.C Complex.I *
              MvPolynomial.pderiv (variableIndex b (oddCoordinate h q)) f) =
      MvPolynomial.pderiv (variableIndex b (evenCoordinate h q))
        (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
          MvPolynomial.C Complex.I *
            MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f) -
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex b (oddCoordinate h q))
            (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
              MvPolynomial.C Complex.I *
                MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f)
  simp only [map_sub, map_add, MvPolynomial.pderiv_C_mul]
  rw [complexPolynomial_pderiv_commute
      (variableIndex a (evenCoordinate h p))
      (variableIndex b (evenCoordinate h q)) f,
    complexPolynomial_pderiv_commute
      (variableIndex a (evenCoordinate h p))
      (variableIndex b (oddCoordinate h q)) f,
    complexPolynomial_pderiv_commute
      (variableIndex a (oddCoordinate h p))
      (variableIndex b (evenCoordinate h q)) f,
    complexPolynomial_pderiv_commute
      (variableIndex a (oddCoordinate h p))
      (variableIndex b (oddCoordinate h q)) f]
  ring

@[simp] theorem ambientSumPositiveRoot_self {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p : Fin (r + 1)) :
    ambientSumPositiveRoot h p p = 0 := by
  simp only [ambientSumPositiveRoot, sub_self, Finset.sum_const_zero]

theorem ambientSumPositiveRoot_apply_antiholomorphic {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ambientSumPositiveRoot h p q f =
      ∑ a : Fin (r + 1),
        (isotropicVariable h a p * antiholomorphicDerivative h a q f -
          isotropicVariable h a q * antiholomorphicDerivative h a p f) := by
  change (Derivation.coeFnAddMonoidHom
    (∑ a : Fin (r + 1),
      (isotropicVariable h a p • antiholomorphicDerivative h a q -
        isotropicVariable h a q • antiholomorphicDerivative h a p))) f = _
  rw [map_sum, Finset.sum_apply]
  rfl

theorem ambientSumPositiveRoot_holomorphicDerivative_commutator_apply
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p q b s : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ambientSumPositiveRoot h p q (holomorphicDerivative h b s f) -
      holomorphicDerivative h b s (ambientSumPositiveRoot h p q f) =
      (if s = q then (2 : ℂ) • antiholomorphicDerivative h b p f else 0) -
        (if s = p then (2 : ℂ) • antiholomorphicDerivative h b q f else 0) := by
  classical
  rw [ambientSumPositiveRoot_apply_antiholomorphic,
    ambientSumPositiveRoot_apply_antiholomorphic, map_sum]
  rw [← Finset.sum_sub_distrib]
  have hterm (a : Fin (r + 1)) :
      (isotropicVariable h a p *
          antiholomorphicDerivative h a q (holomorphicDerivative h b s f) -
        isotropicVariable h a q *
          antiholomorphicDerivative h a p (holomorphicDerivative h b s f)) -
        holomorphicDerivative h b s
          (isotropicVariable h a p * antiholomorphicDerivative h a q f -
            isotropicVariable h a q * antiholomorphicDerivative h a p f) =
      (if a = b ∧ s = q then
        (2 : ℂ) • antiholomorphicDerivative h b p f else 0) -
      (if a = b ∧ s = p then
        (2 : ℂ) • antiholomorphicDerivative h b q f else 0) := by
    rw [map_sub, (holomorphicDerivative h b s).leibniz,
      (holomorphicDerivative h b s).leibniz,
      antiholomorphicDerivative_holomorphicDerivative_commute,
      antiholomorphicDerivative_holomorphicDerivative_commute,
      holomorphicDerivative_isotropicVariable,
      holomorphicDerivative_isotropicVariable]
    by_cases hab : a = b
    · subst a
      by_cases hsq : s = q <;> by_cases hsp : s = p <;>
        simp_all only [sub_self, smul_eq_mul, and_self, ↓reduceIte,
          Algebra.smul_def, MvPolynomial.algebraMap_eq, and_false, mul_zero,
          add_zero, sub_sub_sub_cancel_left, add_sub_cancel_left, sub_zero,
          sub_sub_sub_cancel_right, sub_add_cancel_left, zero_sub, neg_inj] <;>
        rw [map_ofNat (MvPolynomial.C :
          ℂ →+* MvPolynomial (Fin ((r + 1) * n)) ℂ) 2] <;> ring
    · simp only [smul_eq_mul, Ne.symm hab, false_and, ↓reduceIte, mul_zero, add_zero, sub_self, hab]
  simp_rw [hterm]
  simp only [ite_and, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem ambientSumPositiveRoot_holomorphicDerivative_commutator
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p q b : Fin (r + 1)) (hpq : p ≠ q)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ambientSumPositiveRoot h p q (holomorphicDerivative h b q f) -
      holomorphicDerivative h b q (ambientSumPositiveRoot h p q f) =
      (2 : ℂ) • antiholomorphicDerivative h b p f := by
  rw [ambientSumPositiveRoot_holomorphicDerivative_commutator_apply]
  simp only [↓reduceIte, Ne.symm hpq, sub_zero]

theorem ambientSumPositiveRoot_holomorphicDerivative_of_rootKernel
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p q b : Fin (r + 1)) (hpq : p ≠ q)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : ambientSumPositiveRoot h p q f = 0) :
    ambientSumPositiveRoot h p q (holomorphicDerivative h b q f) =
      (2 : ℂ) • antiholomorphicDerivative h b p f := by
  have hcomm := ambientSumPositiveRoot_holomorphicDerivative_commutator
    h p q b hpq f
  simpa only [hf, map_zero, sub_zero] using hcomm

end HigherYoungAmbientSumRootHolomorphicDerivativeCommutator

end

section


open scoped BigOperators

namespace HigherYoungAmbientSumRootAllHighestHolomorphicEvaluation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungIsotropicComplexTraceDecomposition
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungAmbientSumRootHolomorphicDerivativeCommutator

theorem ambientSumPositiveRoot_swap {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q : Fin (r + 1)) :
    ambientSumPositiveRoot h p q = -ambientSumPositiveRoot h q p := by
  classical
  unfold ambientSumPositiveRoot
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  abel

theorem ambientSumPositiveRoot_eq_zero_of_all_positive_root_highest
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h α f = 0)
    (p q : Fin (r + 1)) :
    ambientSumPositiveRoot h p q f = 0 := by
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · exact hroots (.sum p q hpq)
  · subst q
    simp only [ambientSumPositiveRoot_self, Derivation.coe_zero, Pi.zero_apply]
  · have hroot : ambientSumPositiveRoot h q p f = 0 :=
      hroots (.sum q p hqp)
    have hswap := DFunLike.congr_fun (ambientSumPositiveRoot_swap h p q) f
    simpa only [Derivation.coe_neg, Pi.neg_apply, hroot, neg_zero] using hswap

theorem ambientSumPositiveRoot_holomorphicDerivative_of_all_positive_root_highest
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h α f = 0)
    (p q b : Fin (r + 1)) :
    ambientSumPositiveRoot h p q (holomorphicDerivative h b q f) =
      if p = q then 0 else
        (2 : ℂ) • antiholomorphicDerivative h b p f := by
  classical
  by_cases hpq : p = q
  · subst q
    simp only [ambientSumPositiveRoot_self, holomorphicDerivative_apply, Derivation.coe_zero,
      Pi.zero_apply, ↓reduceIte]
  · rw [ite_eq_right hpq]
    exact ambientSumPositiveRoot_holomorphicDerivative_of_rootKernel
      h p q b hpq f
      (ambientSumPositiveRoot_eq_zero_of_all_positive_root_highest
        h f hroots p q)

theorem sum_ambientSumPositiveRoot_holomorphicDerivative_of_all_positive_root_highest
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h α f = 0)
    (p b : Fin (r + 1)) :
    (∑ q : Fin (r + 1),
      ambientSumPositiveRoot h p q (holomorphicDerivative h b q f)) =
      ((2 * r : ℕ) : ℂ) • antiholomorphicDerivative h b p f := by
  classical
  simp_rw [ambientSumPositiveRoot_holomorphicDerivative_of_all_positive_root_highest
    h f hroots p _ b]
  have hcount :
      (∑ q : Fin (r + 1), if p = q then (0 : ℂ) else 2) =
        (r : ℂ) * 2 := by
    calc
      (∑ q : Fin (r + 1), if p = q then (0 : ℂ) else 2) =
          ∑ q ∈ Finset.univ.erase p,
            (if p = q then (0 : ℂ) else 2) := by
            simp
      _ = ∑ _q ∈ Finset.univ.erase p, (2 : ℂ) := by
            apply Finset.sum_congr rfl
            intro q hq
            have hneq : p ≠ q :=
              Ne.symm (Finset.ne_of_mem_erase hq)
            simp only [hneq, ↓reduceIte]
      _ = (r : ℂ) * 2 := by
            rw [Finset.sum_const,
              Finset.card_erase_of_mem (Finset.mem_univ p)]
            simp only [Finset.card_univ, Fintype.card_fin, add_tsub_cancel_right, nsmul_eq_mul]
  calc
    (∑ q : Fin (r + 1),
        if p = q then 0 else
          (2 : ℂ) • antiholomorphicDerivative h b p f) =
      (∑ q : Fin (r + 1), if p = q then (0 : ℂ) else 2) •
        antiholomorphicDerivative h b p f := by
          rw [Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro q _
          split_ifs <;> simp
    _ = ((2 * r : ℕ) : ℂ) • antiholomorphicDerivative h b p f := by
          rw [hcount]
          congr 1
          push_cast
          ring

end HigherYoungAmbientSumRootAllHighestHolomorphicEvaluation

end

section


namespace HigherYoungAllRankHarmonicHighestRootCoercivity

open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestRootEnergyIdentity

theorem card_unusedAmbientCoordinates {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) :
    (unusedAmbientCoordinates (r := r) (n := n)).card = n - 2 * (r + 1) := by
  rcases lt_or_eq_of_le h with hlt | heq
  · let first : Fin n := ⟨2 * (r + 1), hlt⟩
    have hinterval : unusedAmbientCoordinates (r := r) (n := n) = Finset.Ici first := by
      ext t
      simp only [mem_unusedAmbientCoordinates, Finset.mem_Ici]
      change 2 * (r + 1) ≤ t.val ↔ first.val ≤ t.val
      rfl
    rw [hinterval, Fin.card_Ici]
  · have hempty : unusedAmbientCoordinates (r := r) (n := n) = ∅ := by
      ext t
      simp only [unusedAmbientCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false, not_le]
      omega
    rw [hempty, Finset.card_empty]
    omega

theorem two_le_card_unusedAmbientCoordinates {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (hstable : 2 * (r + 1) + 2 ≤ n) :
    2 ≤ (unusedAmbientCoordinates (r := r) (n := n)).card := by
  rw [card_unusedAmbientCoordinates h]
  omega

theorem triangularResidual_eq_rowTail_add_columnTail {r : ℕ}
    (b p : Fin (r + 1)) :
    2 * (r + 1) - 2 - b.val - p.val =
      (r - b.val) + (r - p.val) := by
  have hb := b.isLt
  have hp := p.isLt
  omega

private def harmonicHighestTriangularCoefficient {r : ℕ}
    (n : ℕ)
    (lam mu : Fin (r + 1) → ℕ)
    (b p : Fin (r + 1)) : ℕ :=
  (unusedAmbientCoordinates (r := r) (n := n)).card + lam b + mu p +
    (2 * (r + 1) - 2 - b.val - p.val)

theorem harmonicHighestTriangularCoefficient_eq_tails {r n : ℕ}
    (lam mu : Fin (r + 1) → ℕ)
    (b p : Fin (r + 1)) :
    harmonicHighestTriangularCoefficient n lam mu b p =
      (unusedAmbientCoordinates (r := r) (n := n)).card + lam b + mu p +
        (r - b.val) + (r - p.val) := by
  rw [harmonicHighestTriangularCoefficient,
    triangularResidual_eq_rowTail_add_columnTail]
  omega

theorem two_le_harmonicHighestTriangularCoefficient {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (hstable : 2 * (r + 1) + 2 ≤ n)
    (lam mu : Fin (r + 1) → ℕ)
    (b p : Fin (r + 1)) :
    2 ≤ harmonicHighestTriangularCoefficient n lam mu b p := by
  have hcard := two_le_card_unusedAmbientCoordinates h hstable
  unfold harmonicHighestTriangularCoefficient
  omega

theorem harmonicHighestTriangularCoefficient_ne_zero {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (hstable : 2 * (r + 1) + 2 ≤ n)
    (lam mu : Fin (r + 1) → ℕ)
    (b p : Fin (r + 1)) :
    harmonicHighestTriangularCoefficient n lam mu b p ≠ 0 := by
  have hpositive :=
    two_le_harmonicHighestTriangularCoefficient h hstable lam mu b p
  omega

theorem harmonicHighestTriangularCoefficient_complex_ne_zero {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (hstable : 2 * (r + 1) + 2 ≤ n)
    (lam mu : Fin (r + 1) → ℕ)
    (b p : Fin (r + 1)) :
    (harmonicHighestTriangularCoefficient n lam mu b p : ℂ) ≠ 0 := by
  exact_mod_cast
    harmonicHighestTriangularCoefficient_ne_zero h hstable lam mu b p

end HigherYoungAllRankHarmonicHighestRootCoercivity

end

section


open scoped BigOperators

namespace HigherYoungAllRankHarmonicHighestTriangularScalarBookkeeping

open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestRootCoercivity
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestRootEnergyIdentity

theorem sum_ite_lt_scalar {r : ℕ} (b : Fin (r + 1)) (c : ℂ) :
    (∑ a : Fin (r + 1), if a < b then c else 0) =
      (b.val : ℂ) * c := by
  classical
  rw [← Finset.sum_filter]
  have hfilter :
      Finset.univ.filter (fun a : Fin (r + 1) => a < b) =
        Finset.Iio b := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
  rw [hfilter, Finset.sum_const, Fin.card_Iio]
  simp only [nsmul_eq_mul]

theorem sum_ite_gt_scalar {r : ℕ} (p : Fin (r + 1)) (c : ℂ) :
    (∑ q : Fin (r + 1), if p < q then c else 0) =
      ((r - p.val : ℕ) : ℂ) * c := by
  classical
  rw [← Finset.sum_filter]
  have hfilter :
      Finset.univ.filter (fun q : Fin (r + 1) => p < q) =
        Finset.Ioi p := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
  rw [hfilter, Finset.sum_const, Fin.card_Ioi]
  simp only [add_tsub_cancel_right, nsmul_eq_mul]

theorem sum_rowHighest_scalar {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (b : Fin (r + 1)) :
    (∑ a : Fin (r + 1),
      if a < b then -(1 : ℂ)
      else if a = b then (lam b : ℂ) - 1 else 0) =
      (lam b : ℂ) - 1 - (b.val : ℂ) := by
  classical
  calc
    _ = (∑ a : Fin (r + 1), if a < b then -(1 : ℂ) else 0) +
          (∑ a : Fin (r + 1),
            if a = b then (lam b : ℂ) - 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hab : a < b
      · simp only [hab, ↓reduceIte, ne_of_lt hab, add_zero]
      · simp only [hab, ↓reduceIte, zero_add]
    _ = _ := by
      rw [sum_ite_lt_scalar]
      simp only [mul_neg, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      ring

theorem sum_differenceHighest_scalar {r : ℕ}
    (mu : Fin (r + 1) → ℕ) (p : Fin (r + 1)) :
    (∑ q : Fin (r + 1),
      if q < p then 0
      else if q = p then (2 * mu p : ℕ) + (2 : ℂ)
      else (2 : ℂ)) =
      (2 * mu p : ℕ) + 2 + 2 * ((r - p.val : ℕ) : ℂ) := by
  classical
  calc
    _ = (∑ q : Fin (r + 1),
          if q = p then (2 * mu p : ℕ) + (2 : ℂ) else 0) +
        (∑ q : Fin (r + 1), if p < q then (2 : ℂ) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      rcases lt_trichotomy q p with hlt | heq | hgt
      · simp only [hlt, ↓reduceIte, hlt.ne, not_lt_of_gt hlt, add_zero]
      · subst q
        simp only [lt_self_iff_false, ↓reduceIte, Nat.cast_mul, Nat.cast_ofNat, add_zero]
      · simp only [not_lt_of_gt hgt, ↓reduceIte, hgt.ne', hgt, zero_add]
    _ = _ := by
      rw [sum_ite_gt_scalar]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        add_right_inj]
      ring

theorem harmonicHighestTriangularCoefficient_complex_eq
    {r n : ℕ}
    (lam mu : Fin (r + 1) → ℕ) (b p : Fin (r + 1)) :
    ((harmonicHighestTriangularCoefficient n lam mu b p : ℕ) : ℂ) =
      ((unusedAmbientCoordinates (r := r) (n := n)).card : ℂ) +
      ((lam b : ℂ) - 1 - (b.val : ℂ)) +
      ((2 : ℂ)⁻¹) *
        (((2 * mu p : ℕ) : ℂ) + 2 +
          2 * ((r - p.val : ℕ) : ℂ) + 2 * (r : ℂ)) := by
  rw [harmonicHighestTriangularCoefficient_eq_tails]
  have hb : b.val ≤ r := by omega
  have hp : p.val ≤ r := by omega
  push_cast
  rw [Nat.cast_sub hb, Nat.cast_sub hp]
  norm_num
  ring

end HigherYoungAllRankHarmonicHighestTriangularScalarBookkeeping

namespace HigherYoungAllRankAntiHolomorphicTriangularSums

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
open MetricCodes.Spherical.HigherYoungFullComplexSpanRowEquations
open MetricCodes.Spherical.HigherYoungAllRankAntiHolomorphicRootCommutators
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestTriangularScalarBookkeeping

theorem rowDerivation_antiholomorphic_sum_of_later_rows
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (b p : Fin (r + 1))
    (hrowLater : ∀ a : Fin (r + 1), b < a →
      antiholomorphicDerivative h a p f = 0) :
    (∑ a : Fin (r + 1),
      rowDerivation a b (antiholomorphicDerivative h a p f)) =
      ((lam b : ℂ) - 1 - (b.val : ℂ)) •
        antiholomorphicDerivative h b p f := by
  classical
  have hterm (a : Fin (r + 1)) :
      rowDerivation a b (antiholomorphicDerivative h a p f) =
        (if a < b then -(1 : ℂ)
          else if a = b then (lam b : ℂ) - 1 else 0) •
            antiholomorphicDerivative h b p f := by
    rcases lt_trichotomy a b with hab | hab | hab
    · have hupper :=
        rowDerivation_upper_of_mem_fullYoungComplexPolynomialSpan
          lam hf a b hab
      have hcomm :=
        rowDerivation_antiholomorphicDerivative_matching h a b p f
      rw [hupper, map_zero, sub_zero] at hcomm
      simpa only [HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply,
        rowDerivation_apply, map_add, Derivation.leibniz, smul_eq_mul, MvPolynomial.derivation_C,
        mul_zero, zero_add, hab, ↓reduceIte, smul_add, neg_smul, one_smul,
        neg_add] using hcomm
    · subst a
      have hrow :=
        rowDerivation_self_of_mem_fullYoungComplexPolynomialSpan lam hf b
      have hcomm :=
        rowDerivation_antiholomorphicDerivative_matching h b b p f
      rw [hrow, (antiholomorphicDerivative h b p).map_smul] at hcomm
      simp only [lt_self_iff_false, ite_false, ite_true]
      calc
        _ = (lam b : ℂ) • antiholomorphicDerivative h b p f -
              antiholomorphicDerivative h b p f := by
          linear_combination hcomm
        _ = _ := by
          module
    · have hzero := hrowLater a hab
      rw [hzero, map_zero]
      simp only [not_lt_of_gt hab, ↓reduceIte, ne_of_gt hab,
        HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply, smul_add,
        zero_smul, add_zero]
  calc
    (∑ a : Fin (r + 1),
      rowDerivation a b (antiholomorphicDerivative h a p f)) =
        ∑ a : Fin (r + 1),
          (if a < b then -(1 : ℂ)
            else if a = b then (lam b : ℂ) - 1 else 0) •
              antiholomorphicDerivative h b p f := by
          apply Finset.sum_congr rfl
          intro a _
          exact hterm a
    _ = (∑ a : Fin (r + 1),
          if a < b then -(1 : ℂ)
          else if a = b then (lam b : ℂ) - 1 else 0) •
            antiholomorphicDerivative h b p f := by
          rw [Finset.sum_smul]
    _ = _ := by
          rw [sum_rowHighest_scalar]

end HigherYoungAllRankAntiHolomorphicTriangularSums

namespace HigherYoungAllRankActualHighestCasimirRigidity

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientDifferenceRootAntiHolomorphicDerivativeCommutator
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestTriangularScalarBookkeeping

theorem ambientPositiveRoot_antiholomorphic_sum_of_earlier_columns
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (mu : Fin (r + 1) → ℕ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h α f = 0)
    (hcartan : ∀ p : Fin (r + 1),
      ambientCartan h p f = ((2 * mu p : ℕ) : ℂ) • f)
    (b p : Fin (r + 1))
    (hcolEarlier : ∀ q : Fin (r + 1), q < p →
      antiholomorphicDerivative h b q f = 0) :
    (∑ q : Fin (r + 1),
      ambientPositiveRoot h p q
        (antiholomorphicDerivative h b q f)) =
      (((2 * mu p : ℕ) : ℂ) + 2 +
        2 * ((r - p.val : ℕ) : ℂ)) •
          antiholomorphicDerivative h b p f := by
  classical
  have hterm (q : Fin (r + 1)) :
      ambientPositiveRoot h p q
          (antiholomorphicDerivative h b q f) =
        (if q < p then 0
          else if q = p then ((2 * mu p : ℕ) : ℂ) + 2
          else (2 : ℂ)) • antiholomorphicDerivative h b p f := by
    rcases lt_trichotomy q p with hqp | hqp | hqp
    · rw [hcolEarlier q hqp, map_zero]
      simp only [hqp, ↓reduceIte,
        HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply, smul_add,
        zero_smul, add_zero]
    · subst q
      have hcomm :
        ambientCartan h p (antiholomorphicDerivative h b p f) -
          antiholomorphicDerivative h b p (ambientCartan h p f) =
            (2 : ℂ) • antiholomorphicDerivative h b p f := by
        simpa only [ambientCartan,
          HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply,
          map_add, Derivation.leibniz, smul_eq_mul, MvPolynomial.derivation_C, mul_zero,
            add_zero, smul_add, ↓reduceIte] using
          ambientPositiveRoot_antiholomorphicDerivative_commutator_apply h p p b p f
      rw [hcartan p, (antiholomorphicDerivative h b p).map_smul] at hcomm
      simp only [lt_self_iff_false, ite_false, ite_true]
      rw [add_smul]
      simpa only [HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply,
        map_add, Derivation.leibniz, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_comm,
        zero_add, Nat.cast_mul, Nat.cast_ofNat, smul_add,
        ambientCartan] using (sub_eq_iff_eq_add.mp hcomm)
    · have hroot := hroots (.difference p q hqp)
      have hdiff := ambientPositiveRoot_antiholomorphicDerivative_of_rootKernel
        h p q b (ne_of_lt hqp) f hroot
      simpa only [HigherYoungIsotropicComplexTraceDecomposition.antiholomorphicDerivative_apply,
        map_add, Derivation.leibniz, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero,
        not_lt_of_gt hqp, ↓reduceIte, ne_of_gt hqp, smul_add] using hdiff
  calc
    (∑ q : Fin (r + 1),
      ambientPositiveRoot h p q
        (antiholomorphicDerivative h b q f)) =
        ∑ q : Fin (r + 1),
          (if q < p then 0
            else if q = p then ((2 * mu p : ℕ) : ℂ) + 2
            else (2 : ℂ)) • antiholomorphicDerivative h b p f := by
          apply Finset.sum_congr rfl
          intro q _
          exact hterm q
    _ = (∑ q : Fin (r + 1),
          if q < p then 0
          else if q = p then ((2 * mu p : ℕ) : ℂ) + 2
          else (2 : ℂ)) • antiholomorphicDerivative h b p f := by
          rw [Finset.sum_smul]
    _ = _ := by
          rw [sum_differenceHighest_scalar mu p]

end HigherYoungAllRankActualHighestCasimirRigidity

end

section


namespace HigherYoungFiniteDescendingAscendingInduction

theorem fin_descending_ascending_induction
    {m : ℕ} {P : Fin m → Fin m → Prop}
    (hstep : ∀ b p : Fin m,
      (∀ a : Fin m, b < a → ∀ q : Fin m, P a q) →
      (∀ q : Fin m, q < p → P b q) → P b p) :
    ∀ b p : Fin m, P b p := by
  intro b
  induction hd : m - b.val using Nat.strong_induction_on generalizing b with
  | h d ih =>
      intro p
      induction hp : p.val using Nat.strong_induction_on generalizing p with
      | h e ihe =>
          apply hstep b p
          · intro a hba q
            apply ih (m - a.val) (by omega) a rfl q
          · intro q hqp
            apply ihe q.val (by omega) q rfl

end HigherYoungFiniteDescendingAscendingInduction

end

section


open scoped BigOperators

namespace HigherYoungAllRankActualHighestAntiHolomorphicRecurrence

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
open MetricCodes.Spherical.HigherYoungIsotropicComplexTraceDecomposition
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungAmbientSumRootHolomorphicDerivativeCommutator
open MetricCodes.Spherical.HigherYoungAmbientDifferenceRootAntiHolomorphicDerivativeCommutator
open MetricCodes.Spherical.HigherYoungAmbientSumRootAllHighestHolomorphicEvaluation
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestRootEnergyIdentity
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestRootCoercivity
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestTriangularScalarBookkeeping
open MetricCodes.Spherical.HigherYoungAllRankHarmonicRootEnergyTraceRowCancellation
open MetricCodes.Spherical.HigherYoungAllRankAntiHolomorphicTriangularSums
open MetricCodes.Spherical.HigherYoungAllRankActualHighestCasimirRigidity
open MetricCodes.Spherical.HigherYoungFiniteDescendingAscendingInduction

private theorem ambientPositiveRoot_apply_isotropicDerivatives_metriccodes2_4c407e12
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p q : Fin (r + 1))
    (g : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ambientPositiveRoot h p q g =
      ∑ a : Fin (r + 1),
        (isotropicVariable h a p * holomorphicDerivative h a q g -
          conjugateIsotropicVariable h a q *
            antiholomorphicDerivative h a p g) := by
  rw [ambientPositiveRoot_apply]
  rfl

private theorem mixedIsotropicRemainder_eq_negative_root_actions_metriccodes2_4c407e12
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (b p q : Fin (r + 1)) :
    (∑ a : Fin (r + 1),
      (isotropicVariable h a q *
          holomorphicDerivative h b q
            (antiholomorphicDerivative h a p f) +
        conjugateIsotropicVariable h a q *
          antiholomorphicDerivative h b q
            (antiholomorphicDerivative h a p f) -
        isotropicVariable h a p *
          holomorphicDerivative h b q
            (antiholomorphicDerivative h a q f) -
        isotropicVariable h a p *
          antiholomorphicDerivative h b q
            (holomorphicDerivative h a q f))) =
      -(ambientSumPositiveRoot h p q
          (holomorphicDerivative h b q f) +
        ambientPositiveRoot h p q
          (antiholomorphicDerivative h b q f)) := by
  classical
  rw [ambientSumPositiveRoot_apply_antiholomorphic,
    ambientPositiveRoot_apply_isotropicDerivatives_metriccodes2_4c407e12,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← antiholomorphicDerivative_holomorphicDerivative_commute
        h a p b q f,
      antiholomorphicDerivative_antiholomorphicDerivative_commute
        h b q a p f,
      ← antiholomorphicDerivative_holomorphicDerivative_commute
        h a q b q f,
      antiholomorphicDerivative_holomorphicDerivative_commute
        h b q a q f]
  ring

theorem harmonicHighestRoot_antiholomorphic_operator_recurrence
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h α f = 0)
    (b p : Fin (r + 1)) :
    (((unusedAmbientCoordinates (r := r) (n := n)).card + r : ℕ) : ℂ) •
          antiholomorphicDerivative h b p f +
        (∑ a : Fin (r + 1),
          rowDerivation a b (antiholomorphicDerivative h a p f)) +
        ((2 : ℂ)⁻¹) •
          (∑ q : Fin (r + 1),
            ambientPositiveRoot h p q
              (antiholomorphicDerivative h b q f)) = 0 := by
  classical
  have henergy :=
    shortRoot_unusedDerivative_sum_eq_card_smul_of_rootKernel
      h b p f (fun t ht => hroots (.short p t ht))
  rw [shortRoot_mixedRemainder_eq_neg_rowDerivation_add_isotropic_traces
        h lam hf b p] at henergy
  have hdouble :
      (∑ q : Fin (r + 1),
        ∑ a : Fin (r + 1),
          (isotropicVariable h a q *
              holomorphicDerivative h b q
                (antiholomorphicDerivative h a p f) +
            conjugateIsotropicVariable h a q *
              antiholomorphicDerivative h b q
                (antiholomorphicDerivative h a p f) -
            isotropicVariable h a p *
              holomorphicDerivative h b q
                (antiholomorphicDerivative h a q f) -
            isotropicVariable h a p *
              antiholomorphicDerivative h b q
                (holomorphicDerivative h a q f))) =
        -((∑ q : Fin (r + 1),
            ambientSumPositiveRoot h p q
              (holomorphicDerivative h b q f)) +
          (∑ q : Fin (r + 1),
            ambientPositiveRoot h p q
              (antiholomorphicDerivative h b q f))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl
      (fun q _ => mixedIsotropicRemainder_eq_negative_root_actions_metriccodes2_4c407e12 h f b p q)
  rw [hdouble,
    sum_ambientSumPositiveRoot_holomorphicDerivative_of_all_positive_root_highest
      h f hroots p b,
    ← Nat.cast_smul_eq_nsmul ℂ] at henergy
  have hhalf :
      ((2 : ℂ)⁻¹) * (((2 * r : ℕ) : ℂ)) = (r : ℂ) := by
    push_cast
    ring
  rw [smul_neg, smul_add, smul_smul, hhalf] at henergy
  have hcard :
      (((unusedAmbientCoordinates (r := r) (n := n)).card + r : ℕ) : ℂ) =
        ((unusedAmbientCoordinates (r := r) (n := n)).card : ℂ) + (r : ℂ) := by
    push_cast
    rfl
  rw [hcard, add_smul]
  linear_combination -henergy

theorem antiholomorphicDerivative_eq_zero_of_positiveRootKernel_nonnegativeCartan
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (hstable : 2 * (r + 1) + 2 ≤ n)
    (lam mu : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h α f = 0)
    (hcartan : ∀ p : Fin (r + 1),
      ambientCartan h p f = ((2 * mu p : ℕ) : ℂ) • f) :
    ∀ b p : Fin (r + 1), antiholomorphicDerivative h b p f = 0 := by
  apply fin_descending_ascending_induction
  intro b p hrowLater hcolEarlier
  have hrec := harmonicHighestRoot_antiholomorphic_operator_recurrence
    h lam hf hroots b p
  rw [rowDerivation_antiholomorphic_sum_of_later_rows
        h lam hf b p (fun a ha => hrowLater a ha p),
      ambientPositiveRoot_antiholomorphic_sum_of_earlier_columns
        h mu f hroots hcartan b p hcolEarlier] at hrec
  have hcoefficient :
      (harmonicHighestTriangularCoefficient n lam mu b p : ℂ) •
        antiholomorphicDerivative h b p f = 0 := by
    have hcard :
        (((unusedAmbientCoordinates (r := r) (n := n)).card + r : ℕ) : ℂ) =
          ((unusedAmbientCoordinates (r := r) (n := n)).card : ℂ) + (r : ℂ) := by
      push_cast
      rfl
    rw [hcard] at hrec
    calc
      (harmonicHighestTriangularCoefficient n lam mu b p : ℂ) •
          antiholomorphicDerivative h b p f =
        (((unusedAmbientCoordinates (r := r) (n := n)).card : ℂ) + (r : ℂ) +
          ((lam b : ℂ) - 1 - (b.val : ℂ)) +
          ((2 : ℂ)⁻¹) *
            (((2 * mu p : ℕ) : ℂ) + 2 +
              2 * ((r - p.val : ℕ) : ℂ))) •
            antiholomorphicDerivative h b p f := by
              congr 1
              rw [harmonicHighestTriangularCoefficient_complex_eq]
              field_simp
              ring
      _ = 0 := by
            rw [add_smul, add_smul, mul_smul]
            exact hrec
  exact (smul_eq_zero.mp hcoefficient).resolve_left
    (harmonicHighestTriangularCoefficient_complex_ne_zero
      h hstable lam mu b p)

end HigherYoungAllRankActualHighestAntiHolomorphicRecurrence

end

section


namespace HigherYoungAllRankShortNegativeRootNilpotence

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

private def ambientShortNegativeRoot {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p : Fin (r + 1)) (t : Fin n) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  -complexAmbientRotation (r := r) (evenCoordinate h p) t +
    Complex.I • complexAmbientRotation (r := r) (oddCoordinate h p) t

end HigherYoungAllRankShortNegativeRootNilpotence

end

namespace HigherYoungAllRankHighestShortRootWeightNonnegative

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungArbitraryRankDominantHighestLinePreservation
open MetricCodes.Spherical.HigherYoungAllRankShortNegativeRootNilpotence
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

private def complexDerivationCommutator {r n : ℕ}
    (D₁ D₂ : Derivation ℂ
      (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ)) :
    Derivation ℂ
      (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  Derivation.mk'
    (D₁.toLinearMap.comp D₂.toLinearMap -
      D₂.toLinearMap.comp D₁.toLinearMap)
    fun p q => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        Derivation.coeFn_coe, map_add, Derivation.leibniz, smul_eq_mul]
      ring

private instance complexDerivationBracket {r n : ℕ} :
    Bracket
      (Derivation ℂ
        (MvPolynomial (Fin ((r + 1) * n)) ℂ)
        (MvPolynomial (Fin ((r + 1) * n)) ℂ))
      (Derivation ℂ
        (MvPolynomial (Fin ((r + 1) * n)) ℂ)
        (MvPolynomial (Fin ((r + 1) * n)) ℂ)) :=
  ⟨complexDerivationCommutator⟩

@[simp] private theorem complexDerivationBracket_apply {r n : ℕ}
    (D₁ D₂ : Derivation ℂ
      (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ⁅D₁, D₂⁆ f = D₁ (D₂ f) - D₂ (D₁ f) := rfl

theorem complexAmbientCoordinateDerivation_X
    {r n : ℕ} (a b : Fin n) (i : Fin (r + 1)) (k : Fin n) :
    complexAmbientCoordinateDerivation (r := r) a b
        (MvPolynomial.X (variableIndex i k) :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) =
      if b = k then MvPolynomial.X (variableIndex i a) else 0 := by
  classical
  rw [complexAmbientCoordinateDerivation_apply]
  by_cases hbk : b = k
  · subst k
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, DeterminantVectors.variableIndex_eq_iff,
      and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  · have hkb : k ≠ b := Ne.symm hbk
    simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff, hkb,
      and_false, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, Finset.sum_const_zero, hbk,
      ↓reduceIte]

@[simp] theorem complexAmbientRotation_X
    {r n : ℕ} (a b : Fin n) (i : Fin (r + 1)) (k : Fin n) :
    complexAmbientRotation (r := r) a b
        (MvPolynomial.X (variableIndex i k) :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) =
      (if b = k then MvPolynomial.X (variableIndex i a) else 0) -
        (if a = k then MvPolynomial.X (variableIndex i b) else 0) := by
  change
    complexAmbientCoordinateDerivation (r := r) a b
        (MvPolynomial.X (variableIndex i k)) -
      complexAmbientCoordinateDerivation (r := r) b a
        (MvPolynomial.X (variableIndex i k)) = _
  rw [complexAmbientCoordinateDerivation_X,
    complexAmbientCoordinateDerivation_X]

theorem complexAmbientRotation_commutator_same_right
    {r n : ℕ} (a b t : Fin n)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    ⁅complexAmbientRotation (r := r) a t,
      complexAmbientRotation (r := r) b t⁆ =
      complexAmbientRotation (r := r) b a := by
  classical
  have hcoordinate (i : Fin (r + 1)) (k : Fin n) :
      ⁅complexAmbientRotation (r := r) a t,
        complexAmbientRotation (r := r) b t⁆
          (MvPolynomial.X (variableIndex i k)) =
        complexAmbientRotation (r := r) b a
          (MvPolynomial.X (variableIndex i k)) := by
    simp only [complexDerivationBracket_apply, complexAmbientRotation_X]
    split_ifs <;> simp_all [complexAmbientRotation_X, eq_comm]
  apply MvPolynomial.derivation_ext
  intro x
  let i := ((finProdFinEquiv (m := r + 1) (n := n)).symm x).1
  let k := ((finProdFinEquiv (m := r + 1) (n := n)).symm x).2
  have hx : variableIndex i k = x :=
    (finProdFinEquiv (m := r + 1) (n := n)).apply_symm_apply x
  simpa only [hx] using hcoordinate i k

theorem ambientShortPositiveRoot_negative_commutator
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (p : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ⁅ambientShortPositiveRoot hn p t,
      ambientShortNegativeRoot hn p t⁆ =
      ambientCartan hn p := by
  have heo : evenCoordinate hn p ≠ oddCoordinate hn p :=
    evenCoordinate_ne_oddCoordinate hn p p
  have het : evenCoordinate hn p ≠ t := by
    intro h
    have hx := congrArg Fin.val h
    simp only [evenCoordinate_val] at hx
    have hp := p.isLt
    omega
  have hot : oddCoordinate hn p ≠ t := by
    intro h
    have hx := congrArg Fin.val h
    simp only [oddCoordinate_val] at hx
    have hp := p.isLt
    omega
  rw [ambientShortPositiveRoot_eq_complexRotations,
    ambientShortNegativeRoot, ambientCartan_eq_twice_I_complexRotation]
  calc
    ⁅complexAmbientRotation (r := r) (evenCoordinate hn p) t +
        Complex.I • complexAmbientRotation (r := r) (oddCoordinate hn p) t,
      -complexAmbientRotation (r := r) (evenCoordinate hn p) t +
        Complex.I • complexAmbientRotation (r := r) (oddCoordinate hn p) t⁆ =
        ((2 : ℂ) * Complex.I) •
          ⁅complexAmbientRotation (r := r) (evenCoordinate hn p) t,
            complexAmbientRotation (r := r) (oddCoordinate hn p) t⁆ := by
      apply Derivation.ext
      intro f
      simp only [complexDerivationBracket_apply, Derivation.add_apply,
        Derivation.neg_apply, Derivation.smul_apply,
        map_add, map_neg, Derivation.map_smul]
      module
    _ = _ := by
      rw [complexAmbientRotation_commutator_same_right
        (evenCoordinate hn p) (oddCoordinate hn p) t heo het hot]

end

section


open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungArbitraryRankDominantHighestLinePreservation
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungAllRankShortNegativeRootNilpotence
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem ambientShortPositiveRoot_youngComplexPair
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (p : Fin (r + 1)) (t : Fin n)
    (u v : HarmonicYoungSpace (n := n) lam) :
    ambientShortPositiveRoot hn p t (youngComplexPair lam u v) =
      youngComplexPair lam
        (youngAmbientRotation lam (evenCoordinate hn p) t u -
          youngAmbientRotation lam (oddCoordinate hn p) t v)
        (youngAmbientRotation lam (evenCoordinate hn p) t v +
          youngAmbientRotation lam (oddCoordinate hn p) t u) := by
  rw [ambientShortPositiveRoot_eq_complexRotations]
  change
    complexAmbientRotation (r := r) (evenCoordinate hn p) t
        (youngComplexPair lam u v) +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate hn p) t (youngComplexPair lam u v) = _
  rw [complexAmbientRotation_youngComplexPair,
    complexAmbientRotation_youngComplexPair,
    complex_smul_youngComplexPair]
  simp only [Complex.I_re, Complex.I_im, zero_smul, one_smul,
    zero_sub]
  rw [← youngComplexPair_add]
  simp only [add_zero, youngComplexPair_add, sub_eq_add_neg]

theorem ambientShortNegativeRoot_youngComplexPair
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (p : Fin (r + 1)) (t : Fin n)
    (u v : HarmonicYoungSpace (n := n) lam) :
    ambientShortNegativeRoot hn p t (youngComplexPair lam u v) =
      youngComplexPair lam
        (-youngAmbientRotation lam (evenCoordinate hn p) t u -
          youngAmbientRotation lam (oddCoordinate hn p) t v)
        (-youngAmbientRotation lam (evenCoordinate hn p) t v +
          youngAmbientRotation lam (oddCoordinate hn p) t u) := by
  unfold ambientShortNegativeRoot
  change
    -complexAmbientRotation (r := r) (evenCoordinate hn p) t
        (youngComplexPair lam u v) +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate hn p) t (youngComplexPair lam u v) = _
  rw [complexAmbientRotation_youngComplexPair,
    complexAmbientRotation_youngComplexPair]
  rw [← neg_one_smul ℂ]
  rw [complex_smul_youngComplexPair,
    complex_smul_youngComplexPair]
  simp only [Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.one_re, Complex.one_im, neg_zero, zero_smul, one_smul,
    neg_smul, sub_zero, zero_add, zero_sub]
  rw [← youngComplexPair_add]
  simp only [add_zero, youngComplexPair_add, sub_eq_add_neg]

theorem shortRootYoungPair_inner_adjoint
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (p : Fin (r + 1)) (t : Fin n)
    (u v x y : HarmonicYoungSpace (n := n) lam) :
    ⟪youngAmbientRotation lam (evenCoordinate hn p) t u -
          youngAmbientRotation lam (oddCoordinate hn p) t v, x⟫_ℝ +
      ⟪youngAmbientRotation lam (evenCoordinate hn p) t v +
          youngAmbientRotation lam (oddCoordinate hn p) t u, y⟫_ℝ =
      ⟪u, -youngAmbientRotation lam (evenCoordinate hn p) t x -
          youngAmbientRotation lam (oddCoordinate hn p) t y⟫_ℝ +
        ⟪v, -youngAmbientRotation lam (evenCoordinate hn p) t y +
          youngAmbientRotation lam (oddCoordinate hn p) t x⟫_ℝ := by
  have hsubL (a b c : HarmonicYoungSpace (n := n) lam) :
      ⟪a - b, c⟫_ℝ = ⟪a, c⟫_ℝ - ⟪b, c⟫_ℝ := by
    simp_rw [young_inner_eq_polynomialInner]
    exact SpherePacking.fischer_polynomialInner_sub_left
      ((r + 1) * n) a b c
  have haddL (a b c : HarmonicYoungSpace (n := n) lam) :
      ⟪a + b, c⟫_ℝ = ⟪a, c⟫_ℝ + ⟪b, c⟫_ℝ := by
    simp_rw [young_inner_eq_polynomialInner]
    exact SpherePacking.Fischer.polynomialInner_add_left
      ((r + 1) * n) a b c
  have hsubR (a b c : HarmonicYoungSpace (n := n) lam) :
      ⟪a, b - c⟫_ℝ = ⟪a, b⟫_ℝ - ⟪a, c⟫_ℝ := by
    simp_rw [young_inner_eq_polynomialInner]
    exact MetricCodes.Spherical.AssociatedOverlap.polynomialInner_sub_right
      ((r + 1) * n) a b c
  have haddR (a b c : HarmonicYoungSpace (n := n) lam) :
      ⟪a, b + c⟫_ℝ = ⟪a, b⟫_ℝ + ⟪a, c⟫_ℝ := by
    simp_rw [young_inner_eq_polynomialInner]
    exact SpherePacking.Fischer.polynomialInner_add_right
      ((r + 1) * n) a b c
  have hnegR (a b : HarmonicYoungSpace (n := n) lam) :
      ⟪a, -b⟫_ℝ = -⟪a, b⟫_ℝ := by
    simp_rw [young_inner_eq_polynomialInner]
    simpa only [NegMemClass.coe_neg, neg_smul, one_smul, neg_mul, one_mul] using
      SpherePacking.Fischer.polynomialInner_smul_right ((r + 1) * n) (-1 : ℝ) a b
  rw [hsubL, haddL, hsubR, haddR, hnegR, hnegR,
    youngAmbientRotation_inner, youngAmbientRotation_inner,
    youngAmbientRotation_inner, youngAmbientRotation_inner]
  ring

theorem shortRootHighest_signedWeight_nonnegative
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan (n := n) lam)
    (hfzero : f ≠ 0)
    (p : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val)
    (hroot : ambientShortPositiveRoot hn p t f = 0)
    (mu : ℤ)
    (hcartan : ambientCartan hn p f =
      ((2 : ℂ) * (mu : ℂ)) • f) :
    0 ≤ mu := by
  have hparts := realPart_imaginaryPart_mem_of_mem_polynomialComplexSpan
    (harmonicYoungSubmodule lam) f hf
  let u : HarmonicYoungSpace (n := n) lam :=
    ⟨polynomialRealPart f, hparts.1⟩
  let v : HarmonicYoungSpace (n := n) lam :=
    ⟨polynomialImaginaryPart f, hparts.2⟩
  have hfPair : f = youngComplexPair lam u v := by
    apply complexPolynomial_eq_of_real_imaginary
    · exact (polynomialRealPart_youngComplexPair lam u v).symm
    · exact (polynomialImaginaryPart_youngComplexPair lam u v).symm
  let x := -youngAmbientRotation lam (evenCoordinate hn p) t u -
    youngAmbientRotation lam (oddCoordinate hn p) t v
  let y := -youngAmbientRotation lam (evenCoordinate hn p) t v +
    youngAmbientRotation lam (oddCoordinate hn p) t u
  have hcomm := congrArg (fun D => D f)
    (ambientShortPositiveRoot_negative_commutator hn p t ht)
  simp only [complexDerivationBracket_apply] at hcomm
  rw [hroot, map_zero, sub_zero, hcartan] at hcomm
  rw [hfPair, ambientShortNegativeRoot_youngComplexPair,
    ambientShortPositiveRoot_youngComplexPair] at hcomm
  change
    youngComplexPair lam
      (youngAmbientRotation lam (evenCoordinate hn p) t x -
        youngAmbientRotation lam (oddCoordinate hn p) t y)
      (youngAmbientRotation lam (evenCoordinate hn p) t y +
        youngAmbientRotation lam (oddCoordinate hn p) t x) =
      ((2 : ℂ) * (mu : ℂ)) • youngComplexPair lam u v at hcomm
  have hreal := congrArg polynomialRealPart hcomm
  have himag := congrArg polynomialImaginaryPart hcomm
  rw [polynomialRealPart_youngComplexPair,
    polynomialRealPart_complex_smul,
    polynomialRealPart_youngComplexPair,
    polynomialImaginaryPart_youngComplexPair] at hreal
  rw [polynomialImaginaryPart_youngComplexPair,
    polynomialImaginaryPart_complex_smul,
    polynomialImaginaryPart_youngComplexPair,
    polynomialRealPart_youngComplexPair] at himag
  have hrealVec :
      youngAmbientRotation lam (evenCoordinate hn p) t x -
        youngAmbientRotation lam (oddCoordinate hn p) t y =
        (2 * (mu : ℝ)) • u := by
    apply Subtype.ext
    simpa [u, Complex.mul_re] using hreal
  have himagVec :
      youngAmbientRotation lam (evenCoordinate hn p) t y +
        youngAmbientRotation lam (oddCoordinate hn p) t x =
        (2 * (mu : ℝ)) • v := by
    apply Subtype.ext
    simpa [v, Complex.mul_im] using himag
  have hadj := shortRootYoungPair_inner_adjoint hn lam p t x y u v
  change
    ⟪youngAmbientRotation lam (evenCoordinate hn p) t x -
        youngAmbientRotation lam (oddCoordinate hn p) t y, u⟫_ℝ +
      ⟪youngAmbientRotation lam (evenCoordinate hn p) t y +
        youngAmbientRotation lam (oddCoordinate hn p) t x, v⟫_ℝ =
      ⟪x, x⟫_ℝ + ⟪y, y⟫_ℝ at hadj
  have hsmulL (a b : HarmonicYoungSpace (n := n) lam) (c : ℝ) :
      ⟪c • a, b⟫_ℝ = c * ⟪a, b⟫_ℝ := by
    simp_rw [young_inner_eq_polynomialInner]
    exact SpherePacking.Fischer.polynomialInner_smul_left
      ((r + 1) * n) c a b
  rw [hrealVec, himagVec, hsmulL, hsmulL] at hadj
  have hnonzero : u ≠ 0 ∨ v ≠ 0 := by
    by_cases hu : u = 0
    · right
      intro hv
      apply hfzero
      rw [hfPair]
      exact (youngComplexPair_eq_zero_iff lam u v).mpr ⟨hu, hv⟩
    · exact Or.inl hu
  have hnormpos : 0 < ⟪u, u⟫_ℝ + ⟪v, v⟫_ℝ := by
    rcases hnonzero with hu | hv
    · exact add_pos_of_pos_of_nonneg (real_inner_self_pos.mpr hu)
        (real_inner_self_nonneg : 0 ≤ ⟪v, v⟫_ℝ)
    · exact add_pos_of_nonneg_of_pos
        (real_inner_self_nonneg : 0 ≤ ⟪u, u⟫_ℝ)
        (real_inner_self_pos.mpr hv)
  have hnormnonneg : 0 ≤ ⟪x, x⟫_ℝ + ⟪y, y⟫_ℝ :=
    add_nonneg
      (real_inner_self_nonneg : 0 ≤ ⟪x, x⟫_ℝ)
      (real_inner_self_nonneg : 0 ≤ ⟪y, y⟫_ℝ)
  have hmureal : (0 : ℝ) ≤ (mu : ℝ) := by
    nlinarith
  exact_mod_cast hmureal

theorem positiveRootHighest_signedWeight_nonnegative
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (hstrict : 2 * (r + 1) < n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan (n := n) lam)
    (hfzero : f ≠ 0)
    (mu : Fin (r + 1) → ℤ)
    (hroot : ∀ alpha : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation hn alpha f = 0)
    (hcartan : ∀ p : Fin (r + 1),
      ambientCartan hn p f = ((2 : ℂ) * (mu p : ℂ)) • f)
    (p : Fin (r + 1)) :
    0 ≤ mu p := by
  let t : Fin n := ⟨2 * (r + 1), hstrict⟩
  have ht : 2 * (r + 1) ≤ t.val := le_rfl
  exact shortRootHighest_signedWeight_nonnegative hn lam hf hfzero p t ht
    (hroot (.short p t ht)) (mu p) (hcartan p)

theorem positiveRootHighest_exists_naturalCartanEigenvalues
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (hstrict : 2 * (r + 1) < n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan (n := n) lam)
    (mu : Fin (r + 1) → ℤ)
    (hroot : ∀ alpha : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation hn alpha f = 0)
    (hcartan : ∀ p : Fin (r + 1),
      ambientCartan hn p f = ((2 : ℂ) * (mu p : ℂ)) • f) :
    ∃ nu : Fin (r + 1) → ℕ,
      ∀ p : Fin (r + 1),
        ambientCartan hn p f = ((2 * nu p : ℕ) : ℂ) • f := by
  by_cases hfzero : f = 0
  · refine ⟨fun _ => 0, ?_⟩
    intro p
    simp only [hfzero, map_zero, mul_zero, CharP.cast_eq_zero, smul_zero]
  · have hnonneg (p : Fin (r + 1)) : 0 ≤ mu p :=
      positiveRootHighest_signedWeight_nonnegative hn hstrict lam hf hfzero
        mu hroot hcartan p
    refine ⟨fun p => (mu p).toNat, ?_⟩
    intro p
    rw [hcartan p]
    have hp : ((mu p).toNat : ℤ) = mu p :=
      Int.toNat_of_nonneg (hnonneg p)
    have hcast : ((mu p : ℤ) : ℂ) = (((mu p).toNat : ℕ) : ℂ) := by
      exact_mod_cast hp.symm
    simp only [hcast, Nat.cast_mul, Nat.cast_ofNat]

end

end HigherYoungAllRankHighestShortRootWeightNonnegative

section


namespace HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightProjection

open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence

private def ambientSignedVariableWeight {r n : ℕ}
    (v : Fin ((r + 1) * n)) : Fin (r + 1) → ℤ :=
  let t := ((finProdFinEquiv (m := r + 1) (n := n)).symm v).2
  if ht : t.val < 2 * (r + 1) then
    if t.val % 2 = 0 then
      Pi.single (ambientPairIndex t ht) (1 : ℤ)
    else
      Pi.single (ambientPairIndex t ht) (-1 : ℤ)
  else 0

@[simp] theorem ambientSignedVariableWeight_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    ambientSignedVariableWeight (r := r) (n := n)
      (variableIndex a (evenCoordinate h p)) =
      Pi.single p (1 : ℤ) := by
  have hcut : (evenCoordinate h p).val < 2 * (r + 1) := by
    simp only [evenCoordinate, Order.lt_two_iff, zero_le, mul_lt_mul_iff_right₀,
      Order.lt_add_one_iff]
    have hp := p.isLt
    omega
  simp only [ambientSignedVariableWeight, variableIndex,
    Equiv.symm_apply_apply, dite_eq_left hcut]
  simp only [evenCoordinate_val, Nat.mul_mod_right, ↓reduceIte, ambientPairIndex_even]

@[simp] theorem ambientSignedVariableWeight_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    ambientSignedVariableWeight (r := r) (n := n)
      (variableIndex a (oddCoordinate h p)) =
      Pi.single p (-1 : ℤ) := by
  have hcut : (oddCoordinate h p).val < 2 * (r + 1) := by
    simp only [oddCoordinate]
    have hp := p.isLt
    omega
  simp only [ambientSignedVariableWeight, variableIndex,
    Equiv.symm_apply_apply, dite_eq_left hcut]
  simp only [oddCoordinate_val, Nat.mul_add_mod_self_left, Nat.mod_succ, one_ne_zero, ↓reduceIte,
    ambientPairIndex_odd, Int.reduceNeg]

@[simp] theorem ambientSignedVariableWeight_unused {r n : ℕ}
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientSignedVariableWeight (r := r) (n := n) (variableIndex a t) = 0 := by
  simp only [ambientSignedVariableWeight, variableIndex, Equiv.symm_apply_apply, not_lt_of_ge ht,
    ↓reduceDIte]

private def ambientSignedWeightComponent {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (mu : Fin (r + 1) → ℤ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  isotropicCoordinateEquiv h
    (MvPolynomial.weightedHomogeneousComponent
      (ambientSignedVariableWeight (r := r) (n := n)) mu
      ((isotropicCoordinateEquiv h).symm f))

@[simp] theorem coeff_isotropicInverse_ambientSignedWeightComponent
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (mu : Fin (r + 1) → ℤ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (d : Fin ((r + 1) * n) →₀ ℕ) :
    (((isotropicCoordinateEquiv h).symm
      (ambientSignedWeightComponent h mu f))).coeff d =
      if Finsupp.weight (ambientSignedVariableWeight (r := r) (n := n)) d = mu
      then (((isotropicCoordinateEquiv h).symm f)).coeff d
      else 0 := by
  classical
  simp only [ambientSignedWeightComponent, AlgEquiv.symm_apply_apply,
    MvPolynomial.coeff_weightedHomogeneousComponent]

end HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightProjection

namespace HigherYoungArbitraryRankAmbientSignedWeightGeneratorCartan

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightProjection
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence
open MetricCodes.Spherical.HigherYoungAmbientCartanIsotropicEigenvalues

theorem ambientCartan_isotropicCoordinateGenerator
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p : Fin (r + 1)) (v : Fin ((r + 1) * n)) :
    ambientCartan h p (isotropicCoordinateGenerator h v) =
      ((2 : ℂ) * ((ambientSignedVariableWeight (r := r) (n := n) v p : ℤ) : ℂ)) •
        isotropicCoordinateGenerator h v := by
  classical
  obtain ⟨⟨a, t⟩, rfl⟩ :=
    (finProdFinEquiv (m := r + 1) (n := n)).surjective v
  change
    ambientCartan h p (isotropicCoordinateGenerator h (variableIndex a t)) =
      ((2 : ℂ) *
        ((ambientSignedVariableWeight (r := r) (n := n) (variableIndex a t) p : ℤ) : ℂ)) •
        isotropicCoordinateGenerator h (variableIndex a t)
  by_cases ht : t.val < 2 * (r + 1)
  · by_cases he : t.val % 2 = 0
    · have hgen :
          isotropicCoordinateGenerator h (variableIndex a t) =
            isotropicVariable h a (ambientPairIndex t ht) := by
        simp only [isotropicCoordinateGenerator, variableIndex, Equiv.symm_apply_apply, ht,
          ↓reduceDIte, he]
      have hweight :
          ambientSignedVariableWeight (r := r) (n := n) (variableIndex a t) =
            Pi.single (ambientPairIndex t ht) (1 : ℤ) := by
        simp only [ambientSignedVariableWeight, variableIndex, Equiv.symm_apply_apply, ht,
          ↓reduceDIte, he, ↓reduceIte]
      rw [hgen, hweight, ambientCartan_isotropicVariable]
      by_cases hpq : p = ambientPairIndex t ht
      · subst p
        simp only [↓reduceIte, Pi.single_eq_same, Int.cast_one, mul_one]
      · simp only [hpq, ↓reduceIte, ne_eq, not_false_eq_true, Pi.single_eq_of_ne, Int.cast_zero,
          mul_zero, zero_smul]
    · have hgen :
          isotropicCoordinateGenerator h (variableIndex a t) =
            conjugateIsotropicVariable h a (ambientPairIndex t ht) := by
        simp only [isotropicCoordinateGenerator, variableIndex, Equiv.symm_apply_apply, ht,
          ↓reduceDIte, he]
      have hweight :
          ambientSignedVariableWeight (r := r) (n := n) (variableIndex a t) =
            Pi.single (ambientPairIndex t ht) (-1 : ℤ) := by
        simp only [ambientSignedVariableWeight, variableIndex, Equiv.symm_apply_apply, ht,
          ↓reduceDIte, he, ↓reduceIte, Int.reduceNeg]
      rw [hgen, hweight, ambientCartan_conjugateIsotropicVariable]
      by_cases hpq : p = ambientPairIndex t ht
      · subst p
        simp only [↓reduceIte, neg_smul, Int.reduceNeg, Pi.single_eq_same, Int.cast_neg,
          Int.cast_one, mul_neg, mul_one]
      · simp only [hpq, ↓reduceIte, Int.reduceNeg, ne_eq, not_false_eq_true, Pi.single_eq_of_ne,
          Int.cast_zero, mul_zero, zero_smul]
  · have htu : 2 * (r + 1) ≤ t.val := Nat.le_of_not_gt ht
    rw [isotropicCoordinateGenerator_unused h a t htu,
      ambientSignedVariableWeight_unused a t htu,
      ambientCartan_X_unused h p a t htu]
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_smul]

end HigherYoungArbitraryRankAmbientSignedWeightGeneratorCartan

end

section


open scoped BigOperators

namespace HigherYoungArbitraryRankSignedDiagonalDerivation

open MetricCodes.Spherical.HigherYoungMaximalCartanNullSubstitutionRange

private def signedDiagonalDerivation {ι : Type*} {m : ℕ}
    (w : ι → Fin m → ℤ) (p : Fin m) :
    Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ) :=
  MvPolynomial.mkDerivation ℂ
    (fun i => ((2 : ℂ) * ((w i p : ℤ) : ℂ)) • MvPolynomial.X i)

@[simp] theorem signedDiagonalDerivation_X {ι : Type*} {m : ℕ}
    (w : ι → Fin m → ℤ) (p : Fin m) (i : ι) :
    signedDiagonalDerivation w p (MvPolynomial.X i) =
      ((2 : ℂ) * ((w i p : ℤ) : ℂ)) • MvPolynomial.X i := by
  simp only [signedDiagonalDerivation, MvPolynomial.mkDerivation_X]

theorem signedDiagonalDerivation_eq_sum
    {ι : Type*} [Fintype ι] {m : ℕ}
    (w : ι → Fin m → ℤ) (p : Fin m) :
    signedDiagonalDerivation w p =
      ∑ i : ι, ((2 : ℂ) * ((w i p : ℤ) : ℂ)) •
        ((MvPolynomial.X i : MvPolynomial ι ℂ) •
          (MvPolynomial.pderiv i :
            Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ))) := by
  classical
  apply MvPolynomial.derivation_ext
  intro j
  rw [signedDiagonalDerivation_X]
  change _ = (Derivation.coeFnAddMonoidHom
    (∑ i : ι, ((2 : ℂ) * ((w i p : ℤ) : ℂ)) •
      ((MvPolynomial.X i : MvPolynomial ι ℂ) •
        (MvPolynomial.pderiv i :
          Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ)))))
      (MvPolynomial.X j)
  rw [map_sum, Finset.sum_apply]
  simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, MvPolynomial.pderiv_X,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem signedDiagonalDerivation_apply
    {ι : Type*} [Fintype ι] {m : ℕ}
    (w : ι → Fin m → ℤ) (p : Fin m)
    (q : MvPolynomial ι ℂ) :
    signedDiagonalDerivation w p q =
      ∑ i : ι, ((2 : ℂ) * ((w i p : ℤ) : ℂ)) •
        (MvPolynomial.X i * MvPolynomial.pderiv i q) := by
  rw [signedDiagonalDerivation_eq_sum]
  change (Derivation.coeFnAddMonoidHom
    (∑ i : ι, ((2 : ℂ) * ((w i p : ℤ) : ℂ)) •
      ((MvPolynomial.X i : MvPolynomial ι ℂ) •
        (MvPolynomial.pderiv i :
          Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ))))) q = _
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]

theorem signedWeight_apply
    {ι : Type*} [Fintype ι] {m : ℕ}
    (w : ι → Fin m → ℤ) (d : ι →₀ ℕ) (p : Fin m) :
    Finsupp.weight w d p =
      ∑ i : ι, (d i : ℤ) * w i p := by
  classical
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype d (fun i a => a • w i)
      (by intro i; simp only [zero_nsmul])]
  simp only [nsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply]

theorem coeff_signedDiagonalDerivation
    {ι : Type*} [Finite ι] {m : ℕ}
    (w : ι → Fin m → ℤ) (p : Fin m)
    (q : MvPolynomial ι ℂ) (d : ι →₀ ℕ) :
    (signedDiagonalDerivation w p q).coeff d =
      ((2 : ℂ) * ((Finsupp.weight w d p : ℤ) : ℂ)) * q.coeff d := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [signedDiagonalDerivation_apply]
  simp_rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    coeff_X_mul_pderiv, smul_eq_mul]
  rw [signedWeight_apply]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem signedDiagonal_weightedHomogeneousComponent
    {ι : Type*} [Finite ι] {m : ℕ}
    (w : ι → Fin m → ℤ) (p : Fin m) (mu : Fin m → ℤ)
    (q : MvPolynomial ι ℂ) :
    signedDiagonalDerivation w p
        (MvPolynomial.weightedHomogeneousComponent w mu q) =
      ((2 : ℂ) * ((mu p : ℤ) : ℂ)) •
        MvPolynomial.weightedHomogeneousComponent w mu q := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  ext d
  rw [coeff_signedDiagonalDerivation, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hd : Finsupp.weight w d = mu
  · have hdp : Finsupp.weight w d p = mu p := congrFun hd p
    simp only [hdp, hd, ↓reduceIte, smul_eq_mul]
  · simp only [hd, ↓reduceIte, mul_zero, smul_eq_mul]

end HigherYoungArbitraryRankSignedDiagonalDerivation

end

section


namespace HigherYoungAllRankActualSignedWeightCartanEigen

open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightProjection
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungArbitraryRankAmbientSignedWeightGeneratorCartan
open MetricCodes.Spherical.HigherYoungArbitraryRankSignedDiagonalDerivation

theorem conjugatedAmbientCartan_eq_signedDiagonal
    {r n : ℕ} (h : 2 * (r + 1) ≤ n) (p : Fin (r + 1)) :
    conjugatedPolynomialDerivation (isotropicCoordinateEquiv h)
        (ambientCartan h p) =
      signedDiagonalDerivation (ambientSignedVariableWeight (r := r) (n := n)) p := by
  apply MvPolynomial.derivation_ext
  intro v
  rw [conjugatedPolynomialDerivation_X, isotropicCoordinateEquiv_X,
    ambientCartan_isotropicCoordinateGenerator, map_smul,
    ← isotropicCoordinateEquiv_X, AlgEquiv.symm_apply_apply,
    signedDiagonalDerivation_X]

theorem ambientCartan_ambientSignedWeightComponent
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (mu : Fin (r + 1) → ℤ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (p : Fin (r + 1)) :
    ambientCartan h p (ambientSignedWeightComponent h mu f) =
      ((2 : ℂ) * (mu p : ℂ)) • ambientSignedWeightComponent h mu f := by
  unfold ambientSignedWeightComponent
  rw [← conjugatedPolynomialDerivation_intertwine,
    conjugatedAmbientCartan_eq_signedDiagonal,
    signedDiagonal_weightedHomogeneousComponent, map_smul]

end HigherYoungAllRankActualSignedWeightCartanEigen

end

section


open scoped BigOperators

namespace HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightYoungPreservation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightProjection
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition

theorem youngComplexPolynomialSpan_top_eq_full
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    youngComplexPolynomialSpan lam
        (⊤ : Submodule ℝ (HarmonicYoungSpace (n := n) lam)) =
      fullYoungComplexPolynomialSpan lam := by
  simp only [youngComplexPolynomialSpan, youngRealPolynomialImage, Submodule.map_top,
    Submodule.range_subtype, fullYoungComplexPolynomialSpan]

theorem ambientCartan_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (p : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : f ∈ fullYoungComplexPolynomialSpan lam) :
    ambientCartan h p f ∈ fullYoungComplexPolynomialSpan lam := by
  rw [← youngComplexPolynomialSpan_top_eq_full] at hf ⊢
  exact ambientCartan_youngComplexPolynomialSpan_mem h lam ⊤
    (fun _ _ _ => Submodule.mem_top) p f hf

/-- The ambient signed weight support used in the spherical-code argument. -/
def ambientSignedWeightSupport {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    Finset (Fin (r + 1) → ℤ) :=
  (((isotropicCoordinateEquiv h).symm f).support).image
    (Finsupp.weight (ambientSignedVariableWeight (r := r) (n := n)))

theorem ambientSignedWeightComponent_eq_zero_of_not_mem_support
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (mu : Fin (r + 1) → ℤ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hmu : mu ∉ ambientSignedWeightSupport h f) :
    ambientSignedWeightComponent h mu f = 0 := by
  classical
  rw [ambientSignedWeightComponent,
    MvPolynomial.weightedHomogeneousComponent_eq_zero_of_notMem]
  · exact map_zero _
  · simpa only [Finset.mem_image, MvPolynomial.mem_support_iff, ne_eq, not_exists, not_and,
      ambientSignedWeightSupport] using hmu

theorem sum_ambientSignedWeightComponent
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ∑ mu ∈ ambientSignedWeightSupport h f,
      ambientSignedWeightComponent h mu f = f := by
  classical
  apply (isotropicCoordinateEquiv h).symm.injective
  apply MvPolynomial.ext
  intro d
  simp only [map_sum, MvPolynomial.coeff_sum,
    coeff_isotropicInverse_ambientSignedWeightComponent]
  by_cases hd : (((isotropicCoordinateEquiv h).symm f)).coeff d = 0
  · simp only [hd, ite_self, Finset.sum_const_zero]
  · have hweight : Finsupp.weight (ambientSignedVariableWeight (r := r) (n := n)) d ∈
        ambientSignedWeightSupport h f := by
      exact Finset.mem_image.mpr
        ⟨d, MvPolynomial.mem_support_iff.mpr hd, rfl⟩
    simp [hweight]

end HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightYoungPreservation

namespace HigherYoungFiniteJointWeightProjectorInvariant

theorem jointEigenComponent_mem_of_invariant_sum
    {K V α ι : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    (T : ι → V →ₗ[K] V)
    (W : Submodule K V)
    (hW : ∀ (i : ι) (x : V), x ∈ W → T i x ∈ W)
    (S : Finset α) (v : α → V) (eigen : α → ι → K)
    (heigen : ∀ a ∈ S, ∀ i : ι, T i (v a) = eigen a i • v a)
    (hseparated : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      ∃ i : ι, eigen a i ≠ eigen b i)
    (hsum : (∑ a ∈ S, v a) ∈ W)
    (a : α) (ha : a ∈ S) :
    v a ∈ W := by
  classical
  have hmain : ∀ (k : ℕ) (U : Finset α) (u : α → V),
      U.card = k →
      (∀ c ∈ U, ∀ i : ι, T i (u c) = eigen c i • u c) →
      (∀ c ∈ U, ∀ d ∈ U, c ≠ d →
        ∃ i : ι, eigen c i ≠ eigen d i) →
      (∑ c ∈ U, u c) ∈ W →
      ∀ c ∈ U, u c ∈ W := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro U u hcard hueigen huseparated husum c hc
      by_cases hempty : U.erase c = ∅
      · have hsingleton : U = {c} := by
          rcases (Finset.erase_eq_empty_iff U c).mp hempty with hz | hz
          · simp only [hz, Finset.notMem_empty] at hc
          · exact hz
        simpa only [hsingleton, Finset.sum_singleton] using husum
      · obtain ⟨d, hdErase⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hdc : d ≠ c := (Finset.mem_erase.mp hdErase).1
        have hd : d ∈ U := (Finset.mem_erase.mp hdErase).2
        obtain ⟨i, hi⟩ := huseparated c hc d hd (Ne.symm hdc)
        let u' : α → V :=
          fun b => (eigen b i - eigen d i) • u b
        have hfiltered :
            T i (∑ b ∈ U, u b) -
              eigen d i • (∑ b ∈ U, u b) ∈ W :=
          W.sub_mem (hW i _ husum) (W.smul_mem _ husum)
        have hrewrite :
            T i (∑ b ∈ U, u b) -
                eigen d i • (∑ b ∈ U, u b) =
              ∑ b ∈ U.erase d, u' b := by
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          calc
            (∑ b ∈ U, (T i (u b) - eigen d i • u b)) =
                ∑ b ∈ U, u' b := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  rw [hueigen b hb i]
                  exact (sub_smul (eigen b i) (eigen d i) (u b)).symm
            _ = ∑ b ∈ U.erase d, u' b := by
                  rw [← Finset.sum_erase_add U u' hd]
                  simp only [sub_self, zero_smul, add_zero, u']
        have hsum' : (∑ b ∈ U.erase d, u' b) ∈ W :=
          hrewrite ▸ hfiltered
        have heigen' : ∀ b ∈ U.erase d, ∀ j : ι,
            T j (u' b) = eigen b j • u' b := by
          intro b hb j
          dsimp [u']
          rw [map_smul, hueigen b (Finset.mem_of_mem_erase hb) j]
          simp only [smul_smul, mul_comm]
        have hseparated' : ∀ b ∈ U.erase d, ∀ e ∈ U.erase d,
            b ≠ e → ∃ j : ι, eigen b j ≠ eigen e j := by
          intro b hb e he hbe
          exact huseparated b (Finset.mem_of_mem_erase hb)
            e (Finset.mem_of_mem_erase he) hbe
        have hcard' : (U.erase d).card < k := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem hd
        have hc' : c ∈ U.erase d :=
          Finset.mem_erase.mpr ⟨Ne.symm hdc, hc⟩
        have hcomponent : u' c ∈ W :=
          ih _ hcard' (U.erase d) u' rfl heigen' hseparated'
            hsum' c hc'
        have hscalar : eigen c i - eigen d i ≠ 0 :=
          sub_ne_zero.mpr hi
        have hrescaled := W.smul_mem (eigen c i - eigen d i)⁻¹ hcomponent
        simpa [u', smul_smul, hscalar] using hrescaled
  exact hmain S.card S v rfl heigen hseparated hsum a ha

end HigherYoungFiniteJointWeightProjectorInvariant

namespace HigherYoungAllRankActualSignedWeightYoungPreservation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightProjection
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightYoungPreservation
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
open MetricCodes.Spherical.HigherYoungFiniteJointWeightProjectorInvariant
open MetricCodes.Spherical.HigherYoungAllRankActualSignedWeightCartanEigen

theorem ambientSignedWeightComponent_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (mu : Fin (r + 1) → ℤ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : f ∈ fullYoungComplexPolynomialSpan lam) :
    ambientSignedWeightComponent h mu f ∈
      fullYoungComplexPolynomialSpan lam := by
  classical
  by_cases hmu : mu ∈ ambientSignedWeightSupport h f
  · apply jointEigenComponent_mem_of_invariant_sum
      (fun p : Fin (r + 1) => (ambientCartan h p).toLinearMap)
      (fullYoungComplexPolynomialSpan lam)
      (fun p g hg => ambientCartan_mem_fullYoungComplexPolynomialSpan
        h lam p g hg)
      (ambientSignedWeightSupport h f)
      (fun nu => ambientSignedWeightComponent h nu f)
      (fun nu p => (2 : ℂ) * ((nu p : ℤ) : ℂ))
      (fun nu _ p => ambientCartan_ambientSignedWeightComponent h nu f p)
      (by
        intro a _ b _ hab
        have hdiff : ∃ p : Fin (r + 1), a p ≠ b p := by
          by_contra hnone
          push Not at hnone
          exact hab (funext hnone)
        obtain ⟨p, hp⟩ := hdiff
        refine ⟨p, ?_⟩
        intro heq
        apply hp
        have hcast : (a p : ℂ) = (b p : ℂ) := by
          exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) heq
        exact_mod_cast hcast)
      (by rw [sum_ambientSignedWeightComponent h f]; exact hf)
      mu hmu
  · rw [ambientSignedWeightComponent_eq_zero_of_not_mem_support h mu f hmu]
    exact (fullYoungComplexPolynomialSpan lam).zero_mem

end HigherYoungAllRankActualSignedWeightYoungPreservation

end

section


open scoped BigOperators

namespace HigherYoungArbitraryRankAmbientSignedWeightRootShift

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightProjection
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel

theorem derivation_isWeightedHomogeneous_of_variable_shift
    {σ M : Type*} [AddCommGroup M]
    (w : σ → M) (delta : M)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hD : ∀ i : σ,
      (D (MvPolynomial.X i)).IsWeightedHomogeneous w (w i + delta))
    {mu : M} {p : MvPolynomial σ ℂ}
    (hp : p.IsWeightedHomogeneous w mu) :
    (D p).IsWeightedHomogeneous w (mu + delta) := by
  classical
  have hrepr : D = MvPolynomial.mkDerivation ℂ
      (fun i : σ => D (MvPolynomial.X i)) := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [MvPolynomial.mkDerivation_X]
  change D p ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ w (mu + delta)
  rw [p.as_sum, map_sum]
  apply (MvPolynomial.weightedHomogeneousSubmodule ℂ w (mu + delta)).sum_mem
  intro d hd
  rw [hrepr, MvPolynomial.mkDerivation_monomial]
  apply (MvPolynomial.weightedHomogeneousSubmodule ℂ w (mu + delta)).smul_mem
  apply (MvPolynomial.weightedHomogeneousSubmodule ℂ w (mu + delta)).sum_mem
  intro i hi
  have hi0 : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hdweight : Finsupp.weight w d = mu :=
    hp (MvPolynomial.mem_support_iff.mp hd)
  have hshift :
      Finsupp.weight w (d - Finsupp.single i 1) + (w i + delta) =
        mu + delta := by
    rw [← add_assoc, Finsupp.weight_sub_single_add hi0, hdweight]
  have hmono := MvPolynomial.isWeightedHomogeneous_monomial w
    (d - Finsupp.single i 1) (d i : ℂ) rfl
  have hproduct := hmono.mul (hD i)
  rw [hshift] at hproduct
  simpa only [smul_eq_mul, MvPolynomial.mem_weightedHomogeneousSubmodule] using hproduct

theorem derivation_weightedHomogeneousComponent_shift
    {σ M : Type*} [AddCommGroup M]
    (w : σ → M) (delta : M)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hD : ∀ i : σ,
      (D (MvPolynomial.X i)).IsWeightedHomogeneous w (w i + delta))
    (mu : M) (p : MvPolynomial σ ℂ) :
    D (MvPolynomial.weightedHomogeneousComponent w mu p) =
      MvPolynomial.weightedHomogeneousComponent w (mu + delta) (D p) := by
  classical
  rw [p.as_sum, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hmono := MvPolynomial.isWeightedHomogeneous_monomial w
    d (p.coeff d) rfl
  have hDmono := derivation_isWeightedHomogeneous_of_variable_shift
    w delta D hD hmono
  rw [MvPolynomial.weightedHomogeneousComponent_of_mem hmono,
    MvPolynomial.weightedHomogeneousComponent_of_mem hDmono]
  by_cases heq : mu = Finsupp.weight w d
  · simp only [heq, ↓reduceIte]
  · have hshift : mu + delta ≠ Finsupp.weight w d + delta := by
      intro h
      exact heq (add_right_cancel h)
    simp only [heq, ↓reduceIte, map_zero, hshift]

private def orthogonalPositiveRootSignedCharge
    {r n : ℕ} (alpha : OrthogonalPositiveRoot r n) : Fin (r + 1) → ℤ :=
  match alpha with
  | .difference p q _ => Pi.single p 1 - Pi.single q 1
  | .sum p q _ => Pi.single p 1 + Pi.single q 1
  | .short p _ _ => Pi.single p 1

theorem smul_X_isWeightedHomogeneous
    {σ M : Type*} [AddCommGroup M]
    (w : σ → M) (i : σ) (c : ℂ) :
    (c • MvPolynomial.X i : MvPolynomial σ ℂ).IsWeightedHomogeneous
      w (w i) :=
  (MvPolynomial.weightedHomogeneousSubmodule ℂ w (w i)).smul_mem c
    (MvPolynomial.isWeightedHomogeneous_X ℂ w i)

theorem isotropicOrthogonalPositiveRoot_X_even_isWeightedHomogeneous
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (alpha : OrthogonalPositiveRoot r n)
    (a j : Fin (r + 1)) :
    (isotropicOrthogonalPositiveRootDerivation h alpha
      (MvPolynomial.X (variableIndex a (evenCoordinate h j)))).IsWeightedHomogeneous
      (ambientSignedVariableWeight (r := r) (n := n))
        (ambientSignedVariableWeight (r := r) (n := n)
          (variableIndex a (evenCoordinate h j)) +
            orthogonalPositiveRootSignedCharge alpha) := by
  cases alpha with
  | difference p q hpq =>
      rw [conjugatedDifferenceRoot_X_even h p q hpq a j]
      split_ifs with hq
      · subst j
        have hx := smul_X_isWeightedHomogeneous
          (ambientSignedVariableWeight (r := r) (n := n))
          (variableIndex a (evenCoordinate h p)) (2 : ℂ)
        have hweight :
            ambientSignedVariableWeight (r := r) (n := n)
                (variableIndex a (evenCoordinate h q)) +
              orthogonalPositiveRootSignedCharge
                (.difference p q hpq : OrthogonalPositiveRoot r n) =
              ambientSignedVariableWeight (r := r) (n := n)
                (variableIndex a (evenCoordinate h p)) := by
          simp only [ambientSignedVariableWeight_even,
            orthogonalPositiveRootSignedCharge]
          abel
        rw [hweight]
        exact hx
      · exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  | sum p q hpq =>
      rw [conjugatedSumRoot_X_even h p q hpq a j]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  | short p t ht =>
      rw [conjugatedShortRoot_X_even h p t ht a j]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _

theorem isotropicOrthogonalPositiveRoot_X_odd_isWeightedHomogeneous
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (alpha : OrthogonalPositiveRoot r n)
    (a j : Fin (r + 1)) :
    (isotropicOrthogonalPositiveRootDerivation h alpha
      (MvPolynomial.X (variableIndex a (oddCoordinate h j)))).IsWeightedHomogeneous
      (ambientSignedVariableWeight (r := r) (n := n))
        (ambientSignedVariableWeight (r := r) (n := n)
          (variableIndex a (oddCoordinate h j)) +
            orthogonalPositiveRootSignedCharge alpha) := by
  cases alpha with
  | difference p q hpq =>
      rw [conjugatedDifferenceRoot_X_odd h p q hpq a j]
      split_ifs with hp
      · subst j
        have hx := smul_X_isWeightedHomogeneous
          (ambientSignedVariableWeight (r := r) (n := n))
          (variableIndex a (oddCoordinate h q)) (-2 : ℂ)
        have hweight :
            ambientSignedVariableWeight (r := r) (n := n)
                (variableIndex a (oddCoordinate h p)) +
              orthogonalPositiveRootSignedCharge
                (.difference p q hpq : OrthogonalPositiveRoot r n) =
              ambientSignedVariableWeight (r := r) (n := n)
                (variableIndex a (oddCoordinate h q)) := by
          simp only [ambientSignedVariableWeight_odd,
            orthogonalPositiveRootSignedCharge, Pi.single_neg]
          abel
        rw [hweight]
        exact hx
      · exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  | sum p q hpq =>
      rw [conjugatedSumRoot_X_odd h p q hpq a j]
      by_cases hq : q = j
      · subst j
        have hp : p ≠ q := ne_of_lt hpq
        simp only [↓reduceIte, hp, sub_zero]
        have hx := smul_X_isWeightedHomogeneous
          (ambientSignedVariableWeight (r := r) (n := n))
          (variableIndex a (evenCoordinate h p)) (2 : ℂ)
        have hweight :
            ambientSignedVariableWeight (r := r) (n := n)
                (variableIndex a (oddCoordinate h q)) +
              orthogonalPositiveRootSignedCharge
                (.sum p q hpq : OrthogonalPositiveRoot r n) =
              ambientSignedVariableWeight (r := r) (n := n)
                (variableIndex a (evenCoordinate h p)) := by
          simp only [ambientSignedVariableWeight_even,
            ambientSignedVariableWeight_odd,
            orthogonalPositiveRootSignedCharge, Pi.single_neg]
          abel
        rw [hweight]
        exact hx
      · by_cases hp : p = j
        · subst j
          simp only [hq, ↓reduceIte, zero_sub]
          have hx := smul_X_isWeightedHomogeneous
            (ambientSignedVariableWeight (r := r) (n := n))
            (variableIndex a (evenCoordinate h q)) (-2 : ℂ)
          have hneg :
              -((2 : ℂ) •
                (MvPolynomial.X (variableIndex a (evenCoordinate h q)) :
                  MvPolynomial (Fin ((r + 1) * n)) ℂ)) =
              (-2 : ℂ) •
                (MvPolynomial.X (variableIndex a (evenCoordinate h q)) :
                  MvPolynomial (Fin ((r + 1) * n)) ℂ) := by
            module
          have hweight :
              ambientSignedVariableWeight (r := r) (n := n)
                  (variableIndex a (oddCoordinate h p)) +
                orthogonalPositiveRootSignedCharge
                  (.sum p q hpq : OrthogonalPositiveRoot r n) =
                ambientSignedVariableWeight (r := r) (n := n)
                  (variableIndex a (evenCoordinate h q)) := by
            simp only [ambientSignedVariableWeight_even,
              ambientSignedVariableWeight_odd,
              orthogonalPositiveRootSignedCharge, Pi.single_neg]
            abel
          rw [hneg, hweight]
          exact hx
        · simp only [hq, hp, ite_false, sub_zero]
          exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  | short p t ht =>
      rw [conjugatedShortRoot_X_odd h p t ht a j]
      split_ifs with hp
      · subst j
        have hx := smul_X_isWeightedHomogeneous
          (ambientSignedVariableWeight (r := r) (n := n)) (variableIndex a t) (-2 : ℂ)
        have hweight :
            ambientSignedVariableWeight (r := r) (n := n)
                (variableIndex a (oddCoordinate h p)) +
              orthogonalPositiveRootSignedCharge
                (.short p t ht : OrthogonalPositiveRoot r n) =
              ambientSignedVariableWeight (r := r) (n := n) (variableIndex a t) := by
          simp only [ambientSignedVariableWeight_odd,
            ambientSignedVariableWeight_unused a t ht,
            orthogonalPositiveRootSignedCharge, Pi.single_neg]
          abel
        rw [hweight]
        exact hx
      · exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _

theorem isotropicOrthogonalPositiveRoot_X_unused_isWeightedHomogeneous
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (alpha : OrthogonalPositiveRoot r n)
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    (isotropicOrthogonalPositiveRootDerivation h alpha
      (MvPolynomial.X (variableIndex a t))).IsWeightedHomogeneous
      (ambientSignedVariableWeight (r := r) (n := n))
        (ambientSignedVariableWeight (r := r) (n := n) (variableIndex a t) +
          orthogonalPositiveRootSignedCharge alpha) := by
  cases alpha with
  | difference p q hpq =>
      rw [conjugatedDifferenceRoot_X_unused h p q hpq a t ht]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  | sum p q hpq =>
      rw [conjugatedSumRoot_X_unused h p q hpq a t ht]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  | short p u hu =>
      rw [conjugatedShortRoot_X_unused h p u t hu ht a]
      split_ifs with hut
      · have hx := MvPolynomial.isWeightedHomogeneous_X ℂ
          (ambientSignedVariableWeight (r := r) (n := n))
          (variableIndex a (evenCoordinate h p))
        convert hx using 1
        simp only [ambientSignedVariableWeight_unused a t ht, orthogonalPositiveRootSignedCharge,
          zero_add, ambientSignedVariableWeight_even]
      · exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _

theorem isotropicOrthogonalPositiveRoot_X_isWeightedHomogeneous
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (alpha : OrthogonalPositiveRoot r n)
    (v : Fin ((r + 1) * n)) :
    (isotropicOrthogonalPositiveRootDerivation h alpha (MvPolynomial.X v)).IsWeightedHomogeneous
      (ambientSignedVariableWeight (r := r) (n := n))
        (ambientSignedVariableWeight (r := r) (n := n) v +
          orthogonalPositiveRootSignedCharge alpha) := by
  obtain ⟨⟨a, t⟩, rfl⟩ :=
    (finProdFinEquiv (m := r + 1) (n := n)).surjective v
  change (isotropicOrthogonalPositiveRootDerivation h alpha
      (MvPolynomial.X (variableIndex a t))).IsWeightedHomogeneous
    (ambientSignedVariableWeight (r := r) (n := n))
    (ambientSignedVariableWeight (r := r) (n := n) (variableIndex a t) +
      orthogonalPositiveRootSignedCharge alpha)
  by_cases ht : t.val < 2 * (r + 1)
  · let j := ambientPairIndex t ht
    by_cases he : t.val % 2 = 0
    · have hpair : evenCoordinate h j = t := by
        apply Fin.ext
        change 2 * (t.val / 2) = t.val
        omega
      have hweight := isotropicOrthogonalPositiveRoot_X_even_isWeightedHomogeneous
        h alpha a j
      rw [hpair] at hweight
      exact hweight
    · have hpair : oddCoordinate h j = t := by
        apply Fin.ext
        change 2 * (t.val / 2) + 1 = t.val
        have hrem : t.val % 2 = 1 := by omega
        omega
      have hweight := isotropicOrthogonalPositiveRoot_X_odd_isWeightedHomogeneous
        h alpha a j
      rw [hpair] at hweight
      exact hweight
  · exact isotropicOrthogonalPositiveRoot_X_unused_isWeightedHomogeneous
      h alpha a t (Nat.le_of_not_gt ht)

end HigherYoungArbitraryRankAmbientSignedWeightRootShift

end

section


open scoped BigOperators

namespace HigherYoungArbitraryRankActualSignedWeightRootPreservation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightProjection
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungArbitraryRankAmbientSignedWeightRootShift

theorem orthogonalPositiveRoot_ambientSignedWeightComponent_shift
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (alpha : OrthogonalPositiveRoot r n)
    (mu : Fin (r + 1) → ℤ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    orthogonalPositiveRootDerivation h alpha
        (ambientSignedWeightComponent h mu f) =
      ambientSignedWeightComponent h
        (mu + orthogonalPositiveRootSignedCharge alpha)
        (orthogonalPositiveRootDerivation h alpha f) := by
  let e := isotropicCoordinateEquiv h
  let D := isotropicOrthogonalPositiveRootDerivation h alpha
  let p := e.symm f
  have hintertwine (q : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
      e (D q) = orthogonalPositiveRootDerivation h alpha (e q) :=
    isotropicOrthogonalPositiveRootDerivation_intertwine h alpha q
  have hD : ∀ v : Fin ((r + 1) * n),
      (D (MvPolynomial.X v)).IsWeightedHomogeneous
        (ambientSignedVariableWeight (r := r) (n := n))
        (ambientSignedVariableWeight (r := r) (n := n) v +
          orthogonalPositiveRootSignedCharge alpha) :=
    isotropicOrthogonalPositiveRoot_X_isWeightedHomogeneous h alpha
  have hinverse :
      e.symm (orthogonalPositiveRootDerivation h alpha f) = D p := by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    rw [hintertwine]
    simp only [AlgEquiv.apply_symm_apply, p]
  change
    orthogonalPositiveRootDerivation h alpha
      (e (MvPolynomial.weightedHomogeneousComponent
        (ambientSignedVariableWeight (r := r) (n := n)) mu p)) =
      e (MvPolynomial.weightedHomogeneousComponent
        (ambientSignedVariableWeight (r := r) (n := n))
        (mu + orthogonalPositiveRootSignedCharge alpha)
        (e.symm (orthogonalPositiveRootDerivation h alpha f)))
  rw [← hintertwine, hinverse]
  congr 1
  exact derivation_weightedHomogeneousComponent_shift
    (ambientSignedVariableWeight (r := r) (n := n))
    (orthogonalPositiveRootSignedCharge alpha) D hD mu p

theorem ambientSignedWeightComponent_positiveRootHighest
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (mu : Fin (r + 1) → ℤ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hroots : ∀ alpha : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h alpha f = 0) :
    ∀ alpha : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h alpha
        (ambientSignedWeightComponent h mu f) = 0 := by
  intro alpha
  rw [orthogonalPositiveRoot_ambientSignedWeightComponent_shift
    h alpha mu f, hroots alpha]
  simp only [ambientSignedWeightComponent, map_zero]

end HigherYoungArbitraryRankActualSignedWeightRootPreservation

namespace HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightDecomposition

open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightProjection

/-- The ambient signed weight support used in the spherical-code argument. -/
def ambientSignedWeightSupport {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    Finset (Fin (r + 1) → ℤ) :=
  (((isotropicCoordinateEquiv h).symm f).support).image
    (Finsupp.weight (ambientSignedVariableWeight (r := r) (n := n)))

theorem weight_mem_ambientSignedWeightSupport_of_coeff_ne_zero
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (d : Fin ((r + 1) * n) →₀ ℕ)
    (hd : (((isotropicCoordinateEquiv h).symm f)).coeff d ≠ 0) :
    Finsupp.weight (ambientSignedVariableWeight (r := r) (n := n)) d ∈
      ambientSignedWeightSupport h f := by
  exact Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.mpr hd)

theorem sum_ambientSignedWeightComponent_eq
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    (∑ mu ∈ ambientSignedWeightSupport h f,
      ambientSignedWeightComponent h mu f) = f := by
  classical
  apply (isotropicCoordinateEquiv h).symm.injective
  rw [map_sum]
  ext d
  simp_rw [MvPolynomial.coeff_sum,
    coeff_isotropicInverse_ambientSignedWeightComponent]
  by_cases hd : (((isotropicCoordinateEquiv h).symm f)).coeff d = 0
  · simp only [hd, ite_self, Finset.sum_const_zero]
  · have hweight :=
      weight_mem_ambientSignedWeightSupport_of_coeff_ne_zero h f d hd
    simp only [Finset.sum_ite_eq, hweight, ↓reduceIte]

end HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightDecomposition

end

section


open scoped BigOperators

namespace HigherYoungAllRankActualHighestAntiHolomorphicVanishing

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightProjection
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankAmbientSignedWeightDecomposition
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
open MetricCodes.Spherical.HigherYoungAllRankActualHighestAntiHolomorphicRecurrence
open MetricCodes.Spherical.HigherYoungAllRankHighestShortRootWeightNonnegative
open MetricCodes.Spherical.HigherYoungAllRankActualSignedWeightCartanEigen
open MetricCodes.Spherical.HigherYoungAllRankActualSignedWeightYoungPreservation
open MetricCodes.Spherical.HigherYoungArbitraryRankActualSignedWeightRootPreservation

theorem antiholomorphicDerivative_eq_zero_of_fullYoung_positiveRootHighest
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (hstable : 2 * (r + 1) + 2 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan (n := n) lam)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h α f = 0) :
    ∀ a p : Fin (r + 1), antiholomorphicDerivative h a p f = 0 := by
  intro a p
  rw [← sum_ambientSignedWeightComponent_eq h f, map_sum]
  apply Finset.sum_eq_zero
  intro mu hmu
  have hyoung : ambientSignedWeightComponent h mu f ∈
      fullYoungComplexPolynomialSpan (n := n) lam :=
    ambientSignedWeightComponent_mem_fullYoungComplexPolynomialSpan
      h lam mu f hf
  have hhighest : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation h α
        (ambientSignedWeightComponent h mu f) = 0 :=
    ambientSignedWeightComponent_positiveRootHighest h mu f hroots
  have heigen : ∀ q : Fin (r + 1),
      ambientCartan h q (ambientSignedWeightComponent h mu f) =
        ((2 : ℂ) * (mu q : ℂ)) •
          ambientSignedWeightComponent h mu f :=
    ambientCartan_ambientSignedWeightComponent h mu f
  obtain ⟨nu, hnu⟩ := positiveRootHighest_exists_naturalCartanEigenvalues
    h (by omega) lam hyoung mu hhighest heigen
  exact antiholomorphicDerivative_eq_zero_of_positiveRootKernel_nonnegativeCartan
    h hstable lam nu hyoung hhighest hnu a p

end HigherYoungAllRankActualHighestAntiHolomorphicVanishing

end

section


open scoped BigOperators

namespace HigherYoungAllRankActualHighestKernelRigidity

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherYoungAmbientCartanIsotropicEigenvalues
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungArbitraryRankHarmonicHoweHighestRigidity
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestCartanEulerIdentity
open MetricCodes.Spherical.HigherYoungAllRankHarmonicHighestUnusedDerivativeVanishing
open MetricCodes.Spherical.HigherYoungAllRankActualHighestAntiHolomorphicVanishing
open MetricCodes.Spherical.HigherYoungFullComplexSpanRowEquations
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem totalAmbientCartan_eq_maximal_of_positiveRootKernel_antiholomorphic
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation hn α f = 0)
    (hanti : ∀ a p : Fin (r + 1),
      antiholomorphicDerivative hn a p f = 0) :
    totalAmbientCartan hn f =
      ((2 * (∑ i, lam i) : ℕ) : ℂ) • f := by
  apply totalAmbientCartan_eq_maximal_of_rowCartan_antiholomorphic_unused
    hn lam f
  · exact rowDerivation_self_of_mem_fullYoungComplexPolynomialSpan lam hf
  · exact hanti
  · intro a t ht
    exact unused_pderiv_eq_zero_of_antiholomorphic_and_positiveRootKernel
      hn f hanti hroots a t ht

theorem mem_ambientIsotropicHighestSubmodule_of_positiveRootKernel_antiholomorphic
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation hn α f = 0)
    (hanti : ∀ a p : Fin (r + 1),
      antiholomorphicDerivative hn a p f = 0) :
    f ∈ ambientIsotropicHighestSubmodule hn lam := by
  exact mem_ambientIsotropicHighestSubmodule_of_positiveRootKernel_maximalCartan
    hn lam hf hroots
    (totalAmbientCartan_eq_maximal_of_positiveRootKernel_antiholomorphic
      hn lam hf hroots hanti)

theorem mem_ambientIsotropicHighestSubmodule_of_positiveRootKernel
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (hstable : 2 * (r + 1) + 2 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan lam)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation hn α f = 0) :
    f ∈ ambientIsotropicHighestSubmodule hn lam := by
  exact mem_ambientIsotropicHighestSubmodule_of_positiveRootKernel_antiholomorphic
    hn lam hf hroots
    (antiholomorphicDerivative_eq_zero_of_fullYoung_positiveRootHighest
      hn hstable lam hf hroots)

end HigherYoungAllRankActualHighestKernelRigidity

end

end Spherical

end MetricCodes

end MetricCodesNoncomputable
