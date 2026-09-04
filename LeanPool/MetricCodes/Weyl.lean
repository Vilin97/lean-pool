/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.RootComplex

/-!
# Weyl and root-complex identities

Euler groupings, orthogonal denominator formulas, and all-rank Weyl evaluations.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section


open scoped BigOperators

namespace HigherYoungRootFamilyEulerGrouping

theorem sum_card_grade_eq_signed_subtype_sum
    {α : Type*} [Fintype α]
    (P : Finset α → Prop) [DecidablePred P]
    (F : Finset α → ℤ) :
    (∑ k ∈ Finset.range (Fintype.card α + 1),
      (-1 : ℤ) ^ k *
        ∑ S : {S : Finset α // S.card = k ∧ P S}, F S.val) =
      ∑ S : Finset α,
        (-1 : ℤ) ^ S.card * if P S then F S else 0 := by
  classical
  have hsubtype (k : ℕ) :
      (∑ S : {S : Finset α // S.card = k ∧ P S}, F S.val) =
        ∑ S : Finset α, if S.card = k ∧ P S then F S else 0 := by
    calc
      (∑ S : {S : Finset α // S.card = k ∧ P S}, F S.val) =
          ∑ S ∈ Finset.univ.filter (fun S : Finset α => S.card = k ∧ P S),
            F S :=
        (Finset.sum_subtype
          (Finset.univ.filter (fun S : Finset α => S.card = k ∧ P S))
          (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, implies_true]) F).symm
      _ = _ := Finset.sum_filter _ _
  simp_rw [hsubtype, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hP : P S
  · simp only [Int.reduceNeg, hP, and_true, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
      Order.lt_add_one_iff, Finset.card_le_univ, ↓reduceIte]
  · simp only [Int.reduceNeg, hP, and_false, ↓reduceIte, mul_zero, Finset.sum_const_zero]

end HigherYoungRootFamilyEulerGrouping

end

namespace HigherHarmonicYoung

namespace UniversalBGGRootComplex

section


open scoped BigOperators
open MetricCodes.Spherical.HigherYoungRootFamilyEulerGrouping

theorem rootExteriorEulerCharacteristic_eq_rootFamilyEulerCharacteristic
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    rootExteriorEulerCharacteristic n lam =
      rootFamilyEulerCharacteristic n lam := by
  classical
  let P : Finset (PositiveRoot r) → Prop :=
    fun S => ∀ i, 0 ≤ signedRootWeight lam S i
  let F : Finset (PositiveRoot r) → ℤ :=
    fun S => signedJointHarmonicWeightDimension n (signedRootWeight lam S)
  let e (k : ℕ) : AdmissibleRootWedge lam k ≃
      {S : Finset (PositiveRoot r) // S.card = k ∧ P S} :=
    { toFun := fun S => ⟨S.val.val, S.val.property, S.property⟩
      invFun := fun S => ⟨⟨S.val, S.property.1⟩, S.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hgrade (k : ℕ) :
      (Module.finrank ℝ (RootJointHarmonicChain n lam k) : ℤ) =
        ∑ S : {S : Finset (PositiveRoot r) // S.card = k ∧ P S}, F S.val := by
    rw [finrank_rootJointHarmonicChain]
    push_cast
    calc
      (∑ S : AdmissibleRootWedge lam k,
        (Module.finrank ℝ
          (JointHarmonicWeightSpace n (rootWedgeWeight lam S)) : ℤ)) =
        ∑ S : AdmissibleRootWedge lam k,
          signedJointHarmonicWeightDimension n
            (signedRootWeight lam S.val.val) := by
          apply Finset.sum_congr rfl
          intro S _
          exact (signedJointHarmonicWeightDimension_signedRootWeight lam S).symm
      _ = _ := (e k).sum_comp (fun S => F S.val)
  unfold rootExteriorEulerCharacteristic rootFamilyEulerCharacteristic
  simp_rw [hgrade]
  rw [sum_card_grade_eq_signed_subtype_sum P F]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hP : P S
  · simp only [Int.reduceNeg, hP, ↓reduceIte, F]
  · simp only [Int.reduceNeg, hP, ↓reduceIte, mul_zero, signedJointHarmonicWeightDimension,
      ↓reduceDIte, P, F]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

private def weightedExteriorRootEdgeAdjoint {r k : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i) :
    JointHarmonicWeightSpace n (rootWedgeWeight lam T) →ₗ[ℝ]
      JointHarmonicWeightSpace n
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) :=
  (weightedPositiveRootOperatorStar n
    (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α
    (rootAdmissibleInsert_first_pos lam T α hα hadm)).comp
      (jointHarmonicWeightCast n (rootWedgeWeight lam T)
        (lowerRootWeight
          (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α)
        (rootAdmissibleInsert_lowerRootWeight
          lam T α hα hadm).symm).toLinearMap

@[simp] theorem weightedExteriorRootEdgeAdjoint_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (q : JointHarmonicWeightSpace n (rootWedgeWeight lam T)) :
    (((weightedExteriorRootEdgeAdjoint n lam T α hα hadm q).val :
      youngMultihomogeneousSubmodule n
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm))) :
      PolynomialSpace r n) =
        polarization r n (positiveRootFirst α) (positiveRootSecond α)
          (q.val : PolynomialSpace r n) := by
  change
    (((weightedPositiveRootOperatorStar n
      (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α
      (rootAdmissibleInsert_first_pos lam T α hα hadm)
      (jointHarmonicWeightCast n (rootWedgeWeight lam T)
        (lowerRootWeight
          (rootWedgeWeight lam
            (rootAdmissibleInsert lam T α hα hadm)) α)
        (rootAdmissibleInsert_lowerRootWeight
          lam T α hα hadm).symm q)).val :
      youngMultihomogeneousSubmodule n
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm))) :
      PolynomialSpace r n) = _
  rw [weightedPositiveRootOperatorStar_coe,
    jointHarmonicWeightCast_coe]

@[simp] theorem weightedExteriorRootEdge_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (p : JointHarmonicWeightSpace n
      (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm))) :
    (((weightedExteriorRootEdge n lam T α hα hadm p).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam T)) :
      PolynomialSpace r n) =
        polarization r n (positiveRootSecond α) (positiveRootFirst α)
          (p.val : PolynomialSpace r n) := by
  change
    (((jointHarmonicWeightCast n
      (lowerRootWeight
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α)
      (rootWedgeWeight lam T)
      (rootAdmissibleInsert_lowerRootWeight lam T α hα hadm)
      (weightedPositiveRootOperator n
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α
        (rootAdmissibleInsert_first_pos lam T α hα hadm) p)).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam T)) :
      PolynomialSpace r n) = _
  rw [jointHarmonicWeightCast_coe]
  rfl

theorem weightedExteriorRootEdge_fischer_adjoint {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (p : JointHarmonicWeightSpace n
      (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)))
    (q : JointHarmonicWeightSpace n (rootWedgeWeight lam T)) :
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam T)).inner
        (weightedExteriorRootEdge n lam T α hα hadm p) q =
      (jointHarmonicWeightFischerCore n
        (rootWedgeWeight lam
          (rootAdmissibleInsert lam T α hα hadm))).inner
        p (weightedExteriorRootEdgeAdjoint n lam T α hα hadm q) := by
  rw [jointHarmonicWeightFischerCore_inner,
    jointHarmonicWeightFischerCore_inner,
    weightedExteriorRootEdge_coe,
    weightedExteriorRootEdgeAdjoint_coe]
  exact polynomialInner_polarization_harmonicLift
    (positiveRootSecond α) (positiveRootFirst α)
    (p.val : PolynomialSpace r n)
    (q.val : PolynomialSpace r n)

private def weightedExteriorRootEdgeAdjointAt {r k : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (S : AdmissibleRootWedge lam (k + 1))
    (hS : rootAdmissibleInsert lam T α hα hadm = S) :
    JointHarmonicWeightSpace n (rootWedgeWeight lam T) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) :=
  (jointHarmonicWeightCast n
    (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm))
    (rootWedgeWeight lam S)
    (congrArg (rootWedgeWeight lam) hS)).toLinearMap.comp
      (weightedExteriorRootEdgeAdjoint n lam T α hα hadm)

/-- The weighted exterior action coboundary used in the spherical-code argument. -/
def weightedExteriorActionCoboundary {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1) := by
  classical
  refine
    { toFun := fun f S =>
        ∑ T : AdmissibleRootWedge lam k,
          ∑ α : PositiveRoot r,
            if hα : α ∈ T.val.val then 0
            else if hadm : ∀ i, 0 ≤ signedRootWeight lam
                (insert α T.val.val) i then
              if hS : rootAdmissibleInsert lam T α hα hadm = S then
                realExteriorRootSign (insert α T.val.val) α •
                  weightedExteriorRootEdgeAdjointAt n lam T α hα hadm
                    S hS (f T)
              else 0
            else 0
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    funext S
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs with hα hadm hS
    · simp only [add_zero]
    · simp only [map_add, smul_add]
    · simp only [add_zero]
    · simp only [add_zero]
  · intro c f
    funext S
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs with hα hadm hS
    · simp only [smul_zero]
    · simp only [map_smul, smul_smul, mul_comm]
    · simp only [smul_zero]
    · simp only [smul_zero]

@[simp] theorem weightedExteriorActionCoboundary_apply {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (q : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam (k + 1)) :
    weightedExteriorActionCoboundary n lam k q S =
      ∑ T : AdmissibleRootWedge lam k,
        ∑ α : PositiveRoot r,
          if hα : α ∈ T.val.val then 0
          else if hadm : ∀ i, 0 ≤ signedRootWeight lam
              (insert α T.val.val) i then
            if hS : rootAdmissibleInsert lam T α hα hadm = S then
              realExteriorRootSign (insert α T.val.val) α •
                weightedExteriorRootEdgeAdjointAt n lam T α hα hadm
                  S hS (q T)
            else 0
          else 0 := by
  unfold weightedExteriorActionCoboundary DFunLike.coe LinearMap.instFunLike
  with_reducible rfl

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

private def rootAdmissibleErase {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (α : PositiveRoot r) (hα : α ∈ S.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i) :
    AdmissibleRootWedge lam k := by
  refine ⟨⟨S.val.val.erase α, ?_⟩, hadm⟩
  have hcard := S.val.property
  rw [Finset.card_erase_of_mem hα]
  omega

@[simp] theorem rootAdmissibleErase_val {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (α : PositiveRoot r) (hα : α ∈ S.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i) :
    (rootAdmissibleErase lam S α hα hadm).val.val =
      S.val.val.erase α := rfl

theorem rootAdmissibleInsert_mem_of_eq {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (S : AdmissibleRootWedge lam (k + 1))
    (hS : rootAdmissibleInsert lam T α hα hadm = S) :
    α ∈ S.val.val := by
  have hset : insert α T.val.val = S.val.val :=
    congrArg (fun U : AdmissibleRootWedge lam (k + 1) => U.val.val) hS
  rw [← hset]
  exact Finset.mem_insert_self α T.val.val

theorem rootAdmissibleInsert_erase_nonneg_of_eq {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (S : AdmissibleRootWedge lam (k + 1))
    (hS : rootAdmissibleInsert lam T α hα hadm = S) :
    ∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i := by
  have hset : insert α T.val.val = S.val.val :=
    congrArg (fun U : AdmissibleRootWedge lam (k + 1) => U.val.val) hS
  have herase : S.val.val.erase α = T.val.val := by
    rw [← hset, Finset.erase_insert hα]
  simpa only [herase] using T.property

theorem rootAdmissibleInsert_eq_iff_erase {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (S : AdmissibleRootWedge lam (k + 1))
    (hαS : α ∈ S.val.val)
    (herase : ∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i) :
    rootAdmissibleInsert lam T α hα hadm = S ↔
      T = rootAdmissibleErase lam S α hαS herase := by
  constructor
  · intro hS
    have hset : insert α T.val.val = S.val.val :=
      congrArg (fun U : AdmissibleRootWedge lam (k + 1) => U.val.val) hS
    apply Subtype.ext
    apply Subtype.ext
    change T.val.val = S.val.val.erase α
    rw [← hset, Finset.erase_insert hα]
  · intro hT
    apply Subtype.ext
    apply Subtype.ext
    change insert α T.val.val = S.val.val
    rw [hT, rootAdmissibleErase_val, Finset.insert_erase hαS]

@[simp] theorem weightedExteriorRootEdgeAdjointAt_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (S : AdmissibleRootWedge lam (k + 1))
    (hS : rootAdmissibleInsert lam T α hα hadm = S)
    (q : JointHarmonicWeightSpace n (rootWedgeWeight lam T)) :
    (((weightedExteriorRootEdgeAdjointAt n lam T α hα hadm S hS q).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
        polarization r n (positiveRootFirst α) (positiveRootSecond α)
          (q.val : PolynomialSpace r n) := by
  unfold weightedExteriorRootEdgeAdjointAt
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    jointHarmonicWeightCast_coe, weightedExteriorRootEdgeAdjoint_coe]

private def weightedExteriorRootEdgeAdjointErase {r k : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (α : PositiveRoot r) (hα : α ∈ S.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i) :
    JointHarmonicWeightSpace n
        (rootWedgeWeight lam (rootAdmissibleErase lam S α hα hadm)) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) := by
  let T := rootAdmissibleErase lam S α hα hadm
  have hnot : α ∉ T.val.val := by
    change α ∉ S.val.val.erase α
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
  have hins : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i := by
    simpa [T, Finset.insert_erase hα] using S.property
  have heq : rootAdmissibleInsert lam T α hnot hins = S := by
    apply Subtype.ext
    apply Subtype.ext
    change insert α (S.val.val.erase α) = S.val.val
    exact Finset.insert_erase hα
  exact weightedExteriorRootEdgeAdjointAt n lam T α hnot hins S heq

@[simp] theorem weightedExteriorRootEdgeAdjointErase_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (α : PositiveRoot r) (hα : α ∈ S.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i)
    (q : JointHarmonicWeightSpace n
      (rootWedgeWeight lam (rootAdmissibleErase lam S α hα hadm))) :
    (((weightedExteriorRootEdgeAdjointErase n lam S α hα hadm q).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
        polarization r n (positiveRootFirst α) (positiveRootSecond α)
          (q.val : PolynomialSpace r n) := by
  unfold weightedExteriorRootEdgeAdjointErase
  exact weightedExteriorRootEdgeAdjointAt_coe lam _ _ _ _ _ _ q

theorem weightedExteriorActionCoboundary_apply_erase {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (q : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam (k + 1)) :
    weightedExteriorActionCoboundary n lam k q S =
      ∑ α : PositiveRoot r,
        if hα : α ∈ S.val.val then
          if hadm : ∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i then
            realExteriorRootSign S.val.val α •
              weightedExteriorRootEdgeAdjointErase n lam S α hα hadm
                (q (rootAdmissibleErase lam S α hα hadm))
          else 0
        else 0 := by
  classical
  rw [weightedExteriorActionCoboundary_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hαS : α ∈ S.val.val
  · simp only [dite_eq_left hαS]
    by_cases herase : ∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i
    · simp only [dite_eq_left herase]
      let T₀ : AdmissibleRootWedge lam k :=
        rootAdmissibleErase lam S α hαS herase
      rw [Finset.sum_eq_single T₀]
      · have hnot : α ∉ T₀.val.val := by
          change α ∉ S.val.val.erase α
          simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
        have hins : ∀ i, 0 ≤ signedRootWeight lam
            (insert α T₀.val.val) i := by
          simpa [T₀, Finset.insert_erase hαS] using S.property
        have heq : rootAdmissibleInsert lam T₀ α hnot hins = S :=
          (rootAdmissibleInsert_eq_iff_erase lam T₀ α hnot hins S
            hαS herase).2 rfl
        simp only [dite_eq_right hnot, dite_eq_left hins, dite_eq_left heq]
        have hsign : realExteriorRootSign (insert α T₀.val.val) α =
            realExteriorRootSign S.val.val α := by
          congr 1
          change insert α (S.val.val.erase α) = S.val.val
          exact Finset.insert_erase hαS
        rw [hsign]
        congr 1
      · intro T _ hT
        split_ifs with hmem hadm hins
        · rfl
        · exact False.elim
            (hT ((rootAdmissibleInsert_eq_iff_erase lam T α hmem hadm S
              hαS herase).1 hins))
        · rfl
        · rfl
      · simp only [Finset.mem_univ, not_true_eq_false, dite_eq_left_iff, dite_eq_right_iff,
          smul_eq_zero, IsEmpty.forall_iff]
    · simp only [dite_eq_right herase]
      apply Finset.sum_eq_zero
      intro T _
      split_ifs with hmem hadm hins
      · rfl
      · exact False.elim
          (herase (rootAdmissibleInsert_erase_nonneg_of_eq lam T α
            hmem hadm S hins))
      · rfl
      · rfl
  · simp only [dite_eq_right hαS]
    apply Finset.sum_eq_zero
    intro T _
    split_ifs with hmem hadm hins
    · rfl
    · exact False.elim
        (hαS (rootAdmissibleInsert_mem_of_eq lam T α hmem hadm S hins))
    · rfl
    · rfl

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

private theorem actionFischerCore_inner_comm_metriccodes2_209634ef
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (p q : V) :
    c.inner p q = c.inner q p := by
  simpa only [Real.ringHom_apply] using c.conj_inner_symm q p

private theorem actionFischerCore_zero_left_metriccodes2_209634ef
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (p : V) :
    c.inner 0 p = 0 := by
  have h := c.add_left (0 : V) 0 p
  simp only [zero_add] at h
  linarith

private theorem actionFischerCore_zero_right_metriccodes2_209634ef
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (p : V) :
    c.inner p 0 = 0 := by
  rw [actionFischerCore_inner_comm_metriccodes2_209634ef,
    actionFischerCore_zero_left_metriccodes2_209634ef]

private theorem actionFischerCore_sum_left_metriccodes2_209634ef
    {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V)
    (p : ι → V) (q : V) :
    c.inner (∑ i, p i) q = ∑ i, c.inner (p i) q := by
  classical
  have h (s : Finset ι) :
      c.inner (∑ i ∈ s, p i) q = ∑ i ∈ s, c.inner (p i) q := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, actionFischerCore_zero_left_metriccodes2_209634ef]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, c.add_left, ih]
  simpa only using h Finset.univ

private theorem actionFischerCore_sum_right_metriccodes2_209634ef
    {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V)
    (p : V) (q : ι → V) :
    c.inner p (∑ i, q i) = ∑ i, c.inner p (q i) := by
  rw [actionFischerCore_inner_comm_metriccodes2_209634ef,
    actionFischerCore_sum_left_metriccodes2_209634ef]
  apply Finset.sum_congr rfl
  intro i _
  exact actionFischerCore_inner_comm_metriccodes2_209634ef c (q i) p

private theorem actionFischerCore_smul_left_metriccodes2_209634ef
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V)
    (a : ℝ) (p q : V) :
    c.inner (a • p) q = a * c.inner p q := by
  simpa only [Real.ringHom_apply] using c.smul_left p q a

private theorem actionFischerCore_smul_right_metriccodes2_209634ef
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V)
    (a : ℝ) (p q : V) :
    c.inner p (a • q) = a * c.inner p q := by
  rw [actionFischerCore_inner_comm_metriccodes2_209634ef,
    actionFischerCore_smul_left_metriccodes2_209634ef,
    actionFischerCore_inner_comm_metriccodes2_209634ef c q p]

private theorem weightedExteriorActionRoot_transpose_sum_metriccodes2_209634ef
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam (k + 1))
    (q : RootJointHarmonicChain n lam k)
    (T : AdmissibleRootWedge lam k) (α : PositiveRoot r) :
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam T)).inner
      (if hα : α ∈ T.val.val then 0
        else if hadm : ∀ i, 0 ≤ signedRootWeight lam
            (insert α T.val.val) i then
          realExteriorRootSign (insert α T.val.val) α •
            weightedExteriorRootEdge n lam T α hα hadm
              (p (rootAdmissibleInsert lam T α hα hadm))
        else 0) (q T) =
      ∑ S : AdmissibleRootWedge lam (k + 1),
        (jointHarmonicWeightFischerCore n
          (rootWedgeWeight lam S)).inner (p S)
          (if hα : α ∈ T.val.val then 0
            else if hadm : ∀ i, 0 ≤ signedRootWeight lam
                (insert α T.val.val) i then
              if hS : rootAdmissibleInsert lam T α hα hadm = S then
                realExteriorRootSign (insert α T.val.val) α •
                  weightedExteriorRootEdgeAdjointAt n lam T α hα hadm
                    S hS (q T)
              else 0
            else 0) := by
  classical
  by_cases hα : α ∈ T.val.val
  · simp only [dite_eq_left hα]
    calc
      _ = 0 := actionFischerCore_zero_left_metriccodes2_209634ef
        (jointHarmonicWeightFischerCore n (rootWedgeWeight lam T)) (q T)
      _ = _ := by
        symm
        apply Finset.sum_eq_zero
        intro S _
        exact actionFischerCore_zero_right_metriccodes2_209634ef
          (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)) (p S)
  · by_cases hadm :
      ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i
    · simp only [dite_eq_right hα, dite_eq_left hadm]
      rw [Finset.sum_eq_single
        (rootAdmissibleInsert lam T α hα hadm)]
      · simp only [dite_true]
        have hstar :
            weightedExteriorRootEdgeAdjointAt n lam T α hα hadm
                (rootAdmissibleInsert lam T α hα hadm) rfl =
              weightedExteriorRootEdgeAdjoint n lam T α hα hadm := by
          apply LinearMap.ext
          intro q
          apply Subtype.ext
          apply Subtype.ext
          exact (weightedExteriorRootEdgeAdjointAt_coe
            lam T α hα hadm
            (rootAdmissibleInsert lam T α hα hadm) rfl q).trans
              (weightedExteriorRootEdgeAdjoint_coe
                lam T α hα hadm q).symm
        rw [hstar]
        calc
          _ = realExteriorRootSign (insert α T.val.val) α *
              (jointHarmonicWeightFischerCore n
                (rootWedgeWeight lam T)).inner
                  (weightedExteriorRootEdge n lam T α hα hadm
                    (p (rootAdmissibleInsert lam T α hα hadm))) (q T) :=
            actionFischerCore_smul_left_metriccodes2_209634ef
              (jointHarmonicWeightFischerCore n
                (rootWedgeWeight lam T))
              (realExteriorRootSign (insert α T.val.val) α)
              (weightedExteriorRootEdge n lam T α hα hadm
                (p (rootAdmissibleInsert lam T α hα hadm))) (q T)
          _ = realExteriorRootSign (insert α T.val.val) α *
              (jointHarmonicWeightFischerCore n
                (rootWedgeWeight lam
                  (rootAdmissibleInsert lam T α hα hadm))).inner
                  (p (rootAdmissibleInsert lam T α hα hadm))
                  (weightedExteriorRootEdgeAdjoint n lam T α hα hadm
                    (q T)) :=
            congrArg (fun z : ℝ =>
              realExteriorRootSign (insert α T.val.val) α * z)
              (weightedExteriorRootEdge_fischer_adjoint
                lam T α hα hadm
                  (p (rootAdmissibleInsert lam T α hα hadm)) (q T))
          _ = _ :=
            (actionFischerCore_smul_right_metriccodes2_209634ef
              (jointHarmonicWeightFischerCore n
                (rootWedgeWeight lam
                  (rootAdmissibleInsert lam T α hα hadm)))
              (realExteriorRootSign (insert α T.val.val) α)
              (p (rootAdmissibleInsert lam T α hα hadm))
              (weightedExteriorRootEdgeAdjoint n lam T α hα hadm
                (q T))).symm
      · intro S _ hS
        have hne : rootAdmissibleInsert lam T α hα hadm ≠ S :=
          Ne.symm hS
        rw [dite_eq_right hne]
        exact actionFischerCore_zero_right_metriccodes2_209634ef
          (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)) (p S)
      · simp only [Finset.mem_univ, not_true_eq_false, ↓reduceDIte, IsEmpty.forall_iff]
    · simp only [dite_eq_right hα, dite_eq_right hadm]
      calc
        _ = 0 := actionFischerCore_zero_left_metriccodes2_209634ef
          (jointHarmonicWeightFischerCore n (rootWedgeWeight lam T)) (q T)
        _ = _ := by
          symm
          apply Finset.sum_eq_zero
          intro S _
          exact actionFischerCore_zero_right_metriccodes2_209634ef
            (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)) (p S)

theorem weightedExteriorActionDifferential_fischer_adjoint
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam (k + 1))
    (q : RootJointHarmonicChain n lam k) :
    (rootJointHarmonicChainFischerCore n lam k).inner
        (weightedExteriorActionDifferential n lam k p) q =
      (rootJointHarmonicChainFischerCore n lam (k + 1)).inner
        p (weightedExteriorActionCoboundary n lam k q) := by
  classical
  rw [rootJointHarmonicChainFischerCore_inner,
    rootJointHarmonicChainFischerCore_inner]
  simp_rw [weightedExteriorActionDifferential_apply,
    weightedExteriorActionCoboundary_apply]
  calc
    _ = ∑ T : AdmissibleRootWedge lam k,
        ∑ α : PositiveRoot r,
          (jointHarmonicWeightFischerCore n
            (rootWedgeWeight lam T)).inner
              (if hα : α ∈ T.val.val then 0
                else if hadm : ∀ i, 0 ≤ signedRootWeight lam
                    (insert α T.val.val) i then
                  realExteriorRootSign (insert α T.val.val) α •
                    weightedExteriorRootEdge n lam T α hα hadm
                      (p (rootAdmissibleInsert lam T α hα hadm))
                else 0) (q T) := by
      apply Finset.sum_congr rfl
      intro T _
      exact actionFischerCore_sum_left_metriccodes2_209634ef
        (jointHarmonicWeightFischerCore n
          (rootWedgeWeight lam T)) _ (q T)
    _ = ∑ T : AdmissibleRootWedge lam k,
        ∑ α : PositiveRoot r,
        ∑ S : AdmissibleRootWedge lam (k + 1),
          (jointHarmonicWeightFischerCore n
            (rootWedgeWeight lam S)).inner (p S)
            (if hα : α ∈ T.val.val then 0
              else if hadm : ∀ i, 0 ≤ signedRootWeight lam
                  (insert α T.val.val) i then
                if hS : rootAdmissibleInsert lam T α hα hadm = S then
                  realExteriorRootSign (insert α T.val.val) α •
                    weightedExteriorRootEdgeAdjointAt n lam T α hα hadm
                      S hS (q T)
                else 0
              else 0) := by
      apply Finset.sum_congr rfl
      intro T _
      apply Finset.sum_congr rfl
      intro α _
      exact weightedExteriorActionRoot_transpose_sum_metriccodes2_209634ef lam p q T α
    _ = ∑ S : AdmissibleRootWedge lam (k + 1),
        ∑ T : AdmissibleRootWedge lam k,
        ∑ α : PositiveRoot r,
          (jointHarmonicWeightFischerCore n
            (rootWedgeWeight lam S)).inner (p S)
            (if hα : α ∈ T.val.val then 0
              else if hadm : ∀ i, 0 ≤ signedRootWeight lam
                  (insert α T.val.val) i then
                if hS : rootAdmissibleInsert lam T α hα hadm = S then
                  realExteriorRootSign (insert α T.val.val) α •
                    weightedExteriorRootEdgeAdjointAt n lam T α hα hadm
                      S hS (q T)
                else 0
              else 0) := by
      calc
        _ = ∑ T : AdmissibleRootWedge lam k,
            ∑ S : AdmissibleRootWedge lam (k + 1),
            ∑ α : PositiveRoot r,
              (jointHarmonicWeightFischerCore n
                (rootWedgeWeight lam S)).inner (p S)
                (if hα : α ∈ T.val.val then 0
                  else if hadm : ∀ i, 0 ≤ signedRootWeight lam
                      (insert α T.val.val) i then
                    if hS : rootAdmissibleInsert lam T α hα hadm = S then
                      realExteriorRootSign (insert α T.val.val) α •
                        weightedExteriorRootEdgeAdjointAt n lam T α hα hadm
                          S hS (q T)
                    else 0
                  else 0) := by
          apply Finset.sum_congr rfl
          intro T _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      calc
        _ = ∑ T : AdmissibleRootWedge lam k,
            (jointHarmonicWeightFischerCore n
              (rootWedgeWeight lam S)).inner (p S)
              (∑ α : PositiveRoot r,
                if hα : α ∈ T.val.val then 0
                else if hadm : ∀ i, 0 ≤ signedRootWeight lam
                    (insert α T.val.val) i then
                  if hS : rootAdmissibleInsert lam T α hα hadm = S then
                    realExteriorRootSign (insert α T.val.val) α •
                      weightedExteriorRootEdgeAdjointAt n lam T α hα hadm
                        S hS (q T)
                  else 0
                else 0) := by
          apply Finset.sum_congr rfl
          intro T _
          exact (actionFischerCore_sum_right_metriccodes2_209634ef
            (jointHarmonicWeightFischerCore n
              (rootWedgeWeight lam S)) (p S) _).symm
        _ = _ :=
          (actionFischerCore_sum_right_metriccodes2_209634ef
            (jointHarmonicWeightFischerCore n
              (rootWedgeWeight lam S)) (p S) _).symm

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem weightedExteriorActionCoboundary_apply_erase_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (q : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam (k + 1)) :
    (((weightedExteriorActionCoboundary n lam k q S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
        ∑ α : PositiveRoot r,
          if hα : α ∈ S.val.val then
            if hadm : ∀ i,
                0 ≤ signedRootWeight lam (S.val.val.erase α) i then
              realExteriorRootSign S.val.val α •
                polarization r n (positiveRootFirst α) (positiveRootSecond α)
                  (((q (rootAdmissibleErase lam S α hα hadm)).val :
                    youngMultihomogeneousSubmodule n
                      (rootWedgeWeight lam
                        (rootAdmissibleErase lam S α hα hadm))) :
                    PolynomialSpace r n)
            else 0
          else 0 := by
  classical
  rw [weightedExteriorActionCoboundary_apply_erase]
  simp only [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with hα hadm
  · simp only [Submodule.coe_smul]
    rw [weightedExteriorRootEdgeAdjointErase_coe]
  · simp only [ZeroMemClass.coe_zero]
  · simp only [ZeroMemClass.coe_zero]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

private theorem degreeZeroFischerCore_inner_comm_metriccodes2_89cbd172
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (p q : V) :
    c.inner p q = c.inner q p := by
  simpa only [Real.ringHom_apply] using c.conj_inner_symm q p

private theorem degreeZero_realExteriorRootSign_singleton_metriccodes2_89cbd172
    {ι : Type*} [LinearOrder ι] (a : ι) :
    realExteriorRootSign ({a} : Finset ι) a = 1 := by
  simp only [realExteriorRootSign, exteriorRootSign, Int.reduceNeg, Finset.filter_singleton,
    lt_self_iff_false, ↓reduceIte, Finset.card_empty, pow_zero, Int.cast_one]

private def activeAdmissibleRootWedge {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (α : ActivePositiveRoot lam) :
    AdmissibleRootWedge lam 1 := by
  refine ⟨rootWedgeSingleton α.val, ?_⟩
  intro i
  simp only [rootWedgeSingleton, signedRootWeight,
    rootFamilyCharge_singleton]
  by_cases hsecond : i = positiveRootSecond α.val
  · subst i
    rw [rootCharge_second]
    have hpos := α.property
    omega
  · unfold rootCharge
    split_ifs <;> omega

@[simp] theorem activeAdmissibleRootWedge_val {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (α : ActivePositiveRoot lam) :
    (activeAdmissibleRootWedge lam α).val.val = {α.val} := rfl

theorem rootJointHarmonicDegreeZeroEquiv_coe {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam 0) :
    (((rootJointHarmonicDegreeZeroEquiv n lam p).val :
      youngMultihomogeneousSubmodule n lam) : PolynomialSpace r n) =
      (((p (emptyAdmissibleRootWedge lam)).val :
        youngMultihomogeneousSubmodule n
          (rootWedgeWeight lam (emptyAdmissibleRootWedge lam))) :
        PolynomialSpace r n) := by
  change
    (((jointHarmonicWeightCast n
      (rootWedgeWeight lam (emptyAdmissibleRootWedge lam)) lam
      (rootWedgeWeight_degree_zero lam (emptyAdmissibleRootWedge lam))
      (p (emptyAdmissibleRootWedge lam))).val :
      youngMultihomogeneousSubmodule n lam) : PolynomialSpace r n) = _
  exact jointHarmonicWeightCast_coe
    (rootWedgeWeight lam (emptyAdmissibleRootWedge lam)) lam
    (rootWedgeWeight_degree_zero lam (emptyAdmissibleRootWedge lam))
    (p (emptyAdmissibleRootWedge lam))

theorem weightedExteriorActionCoboundary_degreeZero_active_coe
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam 0)
    (α : ActivePositiveRoot lam) :
    (((weightedExteriorActionCoboundary n lam 0 p
      (activeAdmissibleRootWedge lam α)).val :
      youngMultihomogeneousSubmodule n
        (rootWedgeWeight lam (activeAdmissibleRootWedge lam α))) :
      PolynomialSpace r n) =
        polarization r n (positiveRootFirst α.val)
          (positiveRootSecond α.val)
            (((rootJointHarmonicDegreeZeroEquiv n lam p).val :
              youngMultihomogeneousSubmodule n lam) :
              PolynomialSpace r n) := by
  classical
  rw [weightedExteriorActionCoboundary_apply_erase_coe]
  rw [Finset.sum_eq_single α.val
    (fun β _ hβ => by
      have hnot : β ∉ (activeAdmissibleRootWedge lam α).val.val := by
        simpa only [activeAdmissibleRootWedge_val, Finset.mem_singleton] using hβ
      simp only [dite_eq_right hnot])
    (fun hnot => (hnot (Finset.mem_univ α.val)).elim)]
  have hmem : α.val ∈ (activeAdmissibleRootWedge lam α).val.val := by
    simp only [activeAdmissibleRootWedge_val, Finset.mem_singleton]
  rw [dite_eq_left hmem]
  have hadm : ∀ i, 0 ≤ signedRootWeight lam
      ((activeAdmissibleRootWedge lam α).val.val.erase α.val) i := by
    intro i
    simp only [activeAdmissibleRootWedge_val, signedRootWeight,
      Finset.erase_singleton, rootFamilyCharge_empty, add_zero, Nat.cast_nonneg]
  simp only [dite_eq_left hadm]
  have hsign :
      realExteriorRootSign (activeAdmissibleRootWedge lam α).val.val α.val = 1 := by
    simpa only [activeAdmissibleRootWedge_val] using
      degreeZero_realExteriorRootSign_singleton_metriccodes2_89cbd172 α.val
  rw [hsign, one_smul]
  have hempty := admissibleRootWedge_zero_eq_empty lam
    (rootAdmissibleErase lam (activeAdmissibleRootWedge lam α)
      α.val (by simp only [Nat.reduceAdd, activeAdmissibleRootWedge_val, Finset.mem_singleton])
        hadm)
  rw [hempty]
  rw [rootJointHarmonicDegreeZeroEquiv_coe]

theorem weightedExteriorActionCoboundary_degreeZero_eq_zero_iff
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam 0) :
    weightedExteriorActionCoboundary n lam 0 p = 0 ↔
      rootDegreeZeroPositiveCochain n lam p = 0 := by
  constructor
  · intro hp
    funext α
    apply Subtype.ext
    apply Subtype.ext
    change
      polarization r n (positiveRootFirst α.val)
        (positiveRootSecond α.val)
          (((rootJointHarmonicDegreeZeroEquiv n lam p).val :
            youngMultihomogeneousSubmodule n lam) : PolynomialSpace r n) = 0
    rw [← weightedExteriorActionCoboundary_degreeZero_active_coe]
    rw [congrFun hp (activeAdmissibleRootWedge lam α)]
    simp only [Pi.zero_apply, ZeroMemClass.coe_zero]
  · intro hp
    funext S
    obtain ⟨α, hsingleton, hactive⟩ :=
      admissibleRootWedge_one_exists_active lam S
    let β : ActivePositiveRoot lam := ⟨α, hactive⟩
    have hS : S = activeAdmissibleRootWedge lam β := by
      apply Subtype.ext
      apply Subtype.ext
      exact hsingleton
    subst S
    apply Subtype.ext
    apply Subtype.ext
    rw [weightedExteriorActionCoboundary_degreeZero_active_coe]
    have hcoord := congrFun hp β
    rw [rootDegreeZeroPositiveCochain_apply] at hcoord
    rw [← activePositiveRootRaise_coe lam β
      (rootJointHarmonicDegreeZeroEquiv n lam p), hcoord]
    simp only [Pi.zero_apply, ZeroMemClass.coe_zero]

theorem ker_weightedExteriorActionCoboundary_degreeZero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    LinearMap.ker (weightedExteriorActionCoboundary n lam 0) =
      LinearMap.ker (rootDegreeZeroPositiveCochain n lam) := by
  ext p
  exact weightedExteriorActionCoboundary_degreeZero_eq_zero_iff lam p

theorem rootDegreeZeroPositiveCochain_finrank_ker_add_finrank_ce_range
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    Module.finrank ℝ (LinearMap.ker (rootDegreeZeroPositiveCochain n lam)) +
      Module.finrank ℝ
        (LinearMap.range (weightedChevalleyEilenbergDifferential n lam 0)) =
      Module.finrank ℝ (RootJointHarmonicChain n lam 0) := by
  let : InnerProductSpace.Core ℝ (RootJointHarmonicChain n lam 0) :=
    rootJointHarmonicChainFischerCore n lam 0
  let : NormedAddCommGroup (RootJointHarmonicChain n lam 0) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ (RootJointHarmonicChain n lam 0) :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ
        (RootJointHarmonicChain n lam 0))
  let : InnerProductSpace.Core ℝ (RootJointHarmonicChain n lam (0 + 1)) :=
    rootJointHarmonicChainFischerCore n lam (0 + 1)
  let : NormedAddCommGroup (RootJointHarmonicChain n lam (0 + 1)) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ (RootJointHarmonicChain n lam (0 + 1)) :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ
        (RootJointHarmonicChain n lam (0 + 1)))
  have hadjoint :
      weightedExteriorActionCoboundary n lam 0 =
        (weightedExteriorActionDifferential n lam 0).adjoint := by
    apply (LinearMap.eq_adjoint_iff
      (weightedExteriorActionCoboundary n lam 0)
      (weightedExteriorActionDifferential n lam 0)).mpr
    intro x y
    change
      (rootJointHarmonicChainFischerCore n lam (0 + 1)).inner
        (weightedExteriorActionCoboundary n lam 0 x) y =
      (rootJointHarmonicChainFischerCore n lam 0).inner x
        (weightedExteriorActionDifferential n lam 0 y)
    rw [degreeZeroFischerCore_inner_comm_metriccodes2_89cbd172
      (rootJointHarmonicChainFischerCore n lam (0 + 1)),
      degreeZeroFischerCore_inner_comm_metriccodes2_89cbd172
        (rootJointHarmonicChainFischerCore n lam 0)]
    exact (weightedExteriorActionDifferential_fischer_adjoint lam y x).symm
  have hrank :
      Module.finrank ℝ
        (LinearMap.range (weightedExteriorActionCoboundary n lam 0)) =
      Module.finrank ℝ
        (LinearMap.range (weightedExteriorActionDifferential n lam 0)) := by
    rw [hadjoint]
    exact LinearMap.finrank_range_adjoint
      (weightedExteriorActionDifferential n lam 0)
  have h := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := RootJointHarmonicChain n lam 0)
    (V₂ := RootJointHarmonicChain n lam (0 + 1))
      (weightedExteriorActionCoboundary n lam 0)
  rw [hrank, ker_weightedExteriorActionCoboundary_degreeZero lam] at h
  rw [weightedChevalleyEilenbergDifferential_degree_zero]
  omega

end

end UniversalBGGRootComplex

end HigherHarmonicYoung

section


open scoped BigOperators

namespace HigherWeylBinomialDeterminant

/-- The orthogonal complete symmetric coefficient used in the spherical-code argument. -/
def orthogonalCompleteSymmetricCoefficient (n : ℕ) (k : ℤ) : ℤ :=
  if 0 ≤ k then
    (((n + k.toNat - 1).choose k.toNat : ℕ) : ℤ)
  else 0

/-- The orthogonal jacobi trudi matrix used in the spherical-code argument. -/
def orthogonalJacobiTrudiMatrix {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ :=
  fun i j =>
    orthogonalCompleteSymmetricCoefficient n
        ((lam i : ℤ) - (i.val : ℤ) + (j.val : ℤ)) -
      orthogonalCompleteSymmetricCoefficient n
        ((lam i : ℤ) - (i.val : ℤ) - (j.val : ℤ) - 2)

/-- The orthogonal jacobi trudi dimension used in the spherical-code argument. -/
def orthogonalJacobiTrudiDimension {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) : ℤ :=
  (orthogonalJacobiTrudiMatrix n lam).det

@[simp] theorem orthogonalCompleteSymmetricCoefficient_nat
    (n k : ℕ) :
    orthogonalCompleteSymmetricCoefficient n (k : ℤ) =
      (((n + k - 1).choose k : ℕ) : ℤ) := by
  simp only [orthogonalCompleteSymmetricCoefficient, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast]

@[simp] theorem orthogonalCompleteSymmetricCoefficient_of_neg
    (n : ℕ) {k : ℤ} (hk : k < 0) :
    orthogonalCompleteSymmetricCoefficient n k = 0 := by
  simp only [orthogonalCompleteSymmetricCoefficient, not_le.mpr hk, ↓reduceIte]

end HigherWeylBinomialDeterminant

namespace HigherWeylGramAlternantCoefficient

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankMixedTraceRegularity

private def weylTargetExponent {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : Fin (r + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => lam i + r - i.val

@[simp] theorem weylTargetExponent_apply {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    weylTargetExponent lam i = lam i + r - i.val := by
  simp only [weylTargetExponent, Finsupp.equivFunOnFinite_symm_apply_apply]

private def reversePermutationExponent {r : ℕ}
    (σ : Equiv.Perm (Fin (r + 1))) : Fin (r + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => r - (σ i).val

@[simp] theorem reversePermutationExponent_apply {r : ℕ}
    (σ : Equiv.Perm (Fin (r + 1))) (i : Fin (r + 1)) :
    reversePermutationExponent σ i = r - (σ i).val := by
  simp only [reversePermutationExponent, Finsupp.equivFunOnFinite_symm_apply_apply]

private def boundedExponent {r B : ℕ}
    (d : Fin (r + 1) → Fin (B + 1)) : Fin (r + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (d i).val

@[simp] theorem boundedExponent_apply {r B : ℕ}
    (d : Fin (r + 1) → Fin (B + 1))
    (i : Fin (r + 1)) :
    boundedExponent d i = (d i).val := by
  simp only [boundedExponent, Finsupp.equivFunOnFinite_symm_apply_apply]

theorem boundedExponent_injective {r B : ℕ} :
    Function.Injective
      (boundedExponent (r := r) (B := B)) := by
  intro d e h
  funext i
  apply Fin.ext
  exact congrFun (congrArg DFunLike.coe h) i

private def ambientBinomialPolynomial {r : ℕ}
    (n B : ℕ) : MvPolynomial (Fin (r + 1)) ℤ :=
  ∑ d : Fin (r + 1) → Fin (B + 1),
    MvPolynomial.monomial (boundedExponent d)
      (∏ i : Fin (r + 1),
        (((n + (d i).val - 1).choose (d i).val : ℕ) : ℤ))

theorem coeff_ambientBinomialPolynomial_of_le {r n B : ℕ}
    (m : Fin (r + 1) →₀ ℕ)
    (hm : ∀ i, m i ≤ B) :
    MvPolynomial.coeff m (ambientBinomialPolynomial (r := r) n B) =
      ∏ i : Fin (r + 1),
        (((n + m i - 1).choose (m i) : ℕ) : ℤ) := by
  classical
  let d : Fin (r + 1) → Fin (B + 1) :=
    fun i => ⟨m i, by have := hm i; omega⟩
  have hd : boundedExponent d = m := by
    ext i
    simp only [boundedExponent_apply, d]
  unfold ambientBinomialPolynomial
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single d]
  · simp only [hd, MvPolynomial.coeff_monomial, ↓reduceIte, d]
  · intro e _ he
    rw [MvPolynomial.coeff_monomial, ite_eq_right]
    intro h
    exact he (boundedExponent_injective (h.trans hd.symm))
  · simp only [Finset.mem_univ, not_true_eq_false, MvPolynomial.coeff_monomial, ite_eq_right_iff,
      IsEmpty.forall_iff]

private def gramPairExponent {r : ℕ}
    (z : UpperGramPair r) : Fin (r + 1) →₀ ℕ :=
  Finsupp.single z.val.1 1 + Finsupp.single z.val.2 1

@[simp] theorem gramPairExponent_apply {r : ℕ}
    (z : UpperGramPair r) (i : Fin (r + 1)) :
    gramPairExponent z i = gramPairRowDegree z i := by
  classical
  simp only [gramPairExponent, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, eq_comm,
    gramPairRowDegree]

private def gramFamilyExponent {r : ℕ}
    (s : Finset (UpperGramPair r)) : Fin (r + 1) →₀ ℕ :=
  ∑ z ∈ s, gramPairExponent z

@[simp] theorem gramFamilyExponent_apply {r : ℕ}
    (s : Finset (UpperGramPair r)) (i : Fin (r + 1)) :
    gramFamilyExponent s i = gramFamilyRowDegree s i := by
  simp only [gramFamilyExponent, Finsupp.coe_finsetSum, Finset.sum_apply, gramPairExponent_apply,
    gramFamilyRowDegree]

private def gramEquationPolynomial (r : ℕ) :
    MvPolynomial (Fin (r + 1)) ℤ :=
  ∏ z : UpperGramPair r,
    (1 - MvPolynomial.X z.val.1 * MvPolynomial.X z.val.2)

theorem gramPairMonomial {r : ℕ} (z : UpperGramPair r) :
    (MvPolynomial.X z.val.1 * MvPolynomial.X z.val.2 :
      MvPolynomial (Fin (r + 1)) ℤ) =
        MvPolynomial.monomial (gramPairExponent z) 1 := by
  simp only [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, gramPairExponent]

theorem gramFamilyMonomial {r : ℕ}
    (s : Finset (UpperGramPair r)) :
    (∏ z ∈ s,
      (MvPolynomial.X z.val.1 * MvPolynomial.X z.val.2 :
        MvPolynomial (Fin (r + 1)) ℤ)) =
      MvPolynomial.monomial (gramFamilyExponent s) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, gramFamilyExponent, Finset.sum_empty,
               MvPolynomial.monomial_zero', eq_intCast, Int.cast_one]
  | @insert z s hz ih =>
      rw [Finset.prod_insert hz, gramPairMonomial, ih]
      simp only [gramFamilyExponent, MvPolynomial.monomial_mul, mul_one, hz, not_false_eq_true,
        Finset.sum_insert]

theorem gramEquationPolynomial_eq_sum (r : ℕ) :
    gramEquationPolynomial r =
      ∑ s ∈ (Finset.univ : Finset (UpperGramPair r)).powerset,
        MvPolynomial.monomial (gramFamilyExponent s)
          ((-1 : ℤ) ^ s.card) := by
  classical
  unfold gramEquationPolynomial
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.prod_const_one, mul_one]
  rw [gramFamilyMonomial]
  have hneg : (-1 : MvPolynomial (Fin (r + 1)) ℤ) =
      MvPolynomial.C (-1 : ℤ) := by simp only [Int.reduceNeg, eq_intCast, Int.cast_neg,
                                      Int.cast_one]
  rw [hneg]
  rw [← map_pow, MvPolynomial.C_mul_monomial, mul_one]

theorem coeff_ambientBinomialPolynomial_mul_gramEquationPolynomial
    {r n B : ℕ} (m : Fin (r + 1) →₀ ℕ)
    (hm : ∀ i, m i ≤ B) :
    MvPolynomial.coeff m
        (ambientBinomialPolynomial (r := r) n B *
          gramEquationPolynomial r) =
      fullGramKoszulCoefficient n (fun i => m i) := by
  classical
  rw [gramEquationPolynomial_eq_sum, Finset.mul_sum,
    MvPolynomial.coeff_sum]
  unfold fullGramKoszulCoefficient gramKoszulCoefficient
  apply Finset.sum_congr rfl
  intro s _
  rw [MvPolynomial.coeff_mul_monomial']
  by_cases hs : gramFamilyExponent s ≤ m
  · rw [ite_eq_left hs,
      coeff_ambientBinomialPolynomial_of_le]
    · have hsrow : ∀ i, gramFamilyRowDegree s i ≤ m i := by
        intro i
        simpa only [gramFamilyExponent_apply] using hs i
      unfold shiftedYoungAmbientCoefficient
      simp only [ite_eq_left (hsrow _)]
      push_cast
      rw [mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simp only [Pi.sub_apply, gramFamilyExponent_apply]
    · intro i
      have hbound := hm i
      have hsub : (m - gramFamilyExponent s) i ≤ m i := by
        simp only [Finsupp.coe_tsub, Pi.sub_apply, gramFamilyExponent_apply, tsub_le_iff_right,
          le_add_iff_nonneg_right, zero_le]
      omega
  · rw [ite_eq_right hs]
    have hnot : ¬ ∀ i, gramFamilyRowDegree s i ≤ m i := by
      intro h
      apply hs
      intro i
      simpa only [gramFamilyExponent_apply] using h i
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    rw [shiftedYoungAmbientCoefficient_eq_zero_of_not_le
      (fun i => m i) _ i (Nat.lt_of_not_ge hi)]
    simp only [Int.reduceNeg, CharP.cast_eq_zero, mul_zero]

end HigherWeylGramAlternantCoefficient

namespace HigherWeylReversedAlternantCoefficient

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankMixedTraceRegularity
open MetricCodes.Spherical.HigherWeylGramAlternantCoefficient

private def reversedWeylPolynomial (r : ℕ) :
    MvPolynomial (Fin (r + 1)) ℤ :=
  Matrix.det (Matrix.of fun i j : Fin (r + 1) =>
    (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^ (r - j.val))

theorem reversePermutationMonomial {r : ℕ}
    (σ : Equiv.Perm (Fin (r + 1))) :
    (∏ i : Fin (r + 1),
      (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
        (r - (σ i).val)) =
      MvPolynomial.monomial (reversePermutationExponent σ) 1 := by
  classical
  rw [MvPolynomial.prod_X_pow]
  have h : Finsupp.indicator (Finset.univ : Finset (Fin (r + 1)))
      (fun i _ => r - (σ i).val) =
      reversePermutationExponent σ := by
    ext i
    simp only [Finsupp.indicator_apply, Finset.mem_univ, ↓reduceDIte,
      reversePermutationExponent_apply]
  rw [h]

theorem reversedWeylPolynomial_eq_sum (r : ℕ) :
    reversedWeylPolynomial r =
      ∑ σ : Equiv.Perm (Fin (r + 1)),
        MvPolynomial.monomial (reversePermutationExponent σ)
          (Equiv.Perm.sign σ : ℤ) := by
  classical
  unfold reversedWeylPolynomial
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  change MvPolynomial.C (Equiv.Perm.sign σ : ℤ) *
    (∏ i : Fin (r + 1),
      (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
        (r - (σ i).val)) = _
  rw [reversePermutationMonomial]
  rw [MvPolynomial.C_mul_monomial, mul_one]

theorem reversePermutationExponent_le_weylTargetExponent_iff
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (σ : Equiv.Perm (Fin (r + 1))) :
    reversePermutationExponent σ ≤ weylTargetExponent lam ↔
      ∀ i, 0 ≤ weylShift lam σ i := by
  constructor
  · intro h i
    have hi := h i
    have hi' := i.isLt
    have hσ := (σ i).isLt
    simp only [reversePermutationExponent_apply, weylTargetExponent_apply, tsub_le_iff_right,
      weylShift, ge_iff_le] at hi ⊢
    omega
  · intro h i
    have hi := h i
    have hi' := i.isLt
    have hσ := (σ i).isLt
    simp only [weylShift, reversePermutationExponent_apply, weylTargetExponent_apply,
      tsub_le_iff_right, ge_iff_le] at hi ⊢
    omega

theorem weylTargetExponent_sub_reversePermutationExponent_apply
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (σ : Equiv.Perm (Fin (r + 1)))
    (hσ : reversePermutationExponent σ ≤ weylTargetExponent lam)
    (i : Fin (r + 1)) :
    (weylTargetExponent lam - reversePermutationExponent σ) i =
      (weylShift lam σ i).toNat := by
  have h := hσ i
  have hi := i.isLt
  have hσi := (σ i).isLt
  simp only [reversePermutationExponent_apply, weylTargetExponent_apply, tsub_le_iff_right,
    Finsupp.coe_tsub, Pi.sub_apply, weylShift] at h ⊢
  omega

theorem coeff_ambient_mul_gram_mul_reversedWeylPolynomial
    {r n B : ℕ} (lam : Fin (r + 1) → ℕ)
    (hB : ∀ i, weylTargetExponent lam i ≤ B) :
    MvPolynomial.coeff (weylTargetExponent lam)
        ((ambientBinomialPolynomial (r := r) n B *
          gramEquationPolynomial r) * reversedWeylPolynomial r) =
      alternatingGramKoszulCoefficient n lam := by
  classical
  rw [reversedWeylPolynomial_eq_sum, Finset.mul_sum,
    MvPolynomial.coeff_sum]
  unfold alternatingGramKoszulCoefficient
  apply Finset.sum_congr rfl
  intro σ _
  rw [MvPolynomial.coeff_mul_monomial']
  by_cases hσ : reversePermutationExponent σ ≤ weylTargetExponent lam
  · rw [ite_eq_left hσ,
      coeff_ambientBinomialPolynomial_mul_gramEquationPolynomial]
    · have hnonneg : ∀ i, 0 ≤ weylShift lam σ i :=
        (reversePermutationExponent_le_weylTargetExponent_iff
          lam σ).mp hσ
      rw [signedFullGramKoszulCoefficient, ite_eq_left hnonneg]
      have hweights :
          (fun i => (weylTargetExponent lam -
            reversePermutationExponent σ) i) =
            (fun i => (weylShift lam σ i).toNat) := by
        funext i
        exact weylTargetExponent_sub_reversePermutationExponent_apply
          lam σ hσ i
      rw [hweights]
      ring
    · intro i
      have hb := hB i
      have hle : (weylTargetExponent lam -
          reversePermutationExponent σ) i ≤
            weylTargetExponent lam i := by simp only [Finsupp.coe_tsub, Pi.sub_apply,
                                             weylTargetExponent_apply,
                                             reversePermutationExponent_apply, tsub_le_iff_right,
                                             le_add_iff_nonneg_right, zero_le]
      omega
  · rw [ite_eq_right hσ]
    have hnegative : ¬ ∀ i, 0 ≤ weylShift lam σ i :=
      mt (reversePermutationExponent_le_weylTargetExponent_iff
        lam σ).mpr hσ
    simp only [signedFullGramKoszulCoefficient, hnegative, ↓reduceIte, mul_zero]

end HigherWeylReversedAlternantCoefficient

namespace HigherWeylQuadraticDeterminantCoefficient

open MetricCodes.Spherical.HigherWeylGramAlternantCoefficient
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankMixedTraceRegularity

theorem coeff_ambientBinomialPolynomial_mul_monomial
    {r n B : ℕ} (m s : Fin (r + 1) →₀ ℕ)
    (hm : ∀ i, m i ≤ B) :
    MvPolynomial.coeff m
        (ambientBinomialPolynomial (r := r) n B *
          MvPolynomial.monomial s (1 : ℤ)) =
      ∏ i : Fin (r + 1),
        orthogonalCompleteSymmetricCoefficient n
          ((m i : ℤ) - (s i : ℤ)) := by
  classical
  rw [MvPolynomial.coeff_mul_monomial']
  by_cases hs : s ≤ m
  · rw [ite_eq_left hs, mul_one,
      coeff_ambientBinomialPolynomial_of_le]
    · apply Finset.prod_congr rfl
      intro i _
      have hsi : s i ≤ m i := hs i
      have hcast : ((m i : ℤ) - (s i : ℤ)) = ((m i - s i : ℕ) : ℤ) := by
        omega
      rw [hcast, orthogonalCompleteSymmetricCoefficient_nat]
      simp only [Finsupp.coe_tsub, Pi.sub_apply]
    · intro i
      have hbound := hm i
      simp only [Finsupp.coe_tsub, Pi.sub_apply, tsub_le_iff_right, ge_iff_le]
      omega
  · rw [ite_eq_right hs]
    have hnot : ¬ ∀ i, s i ≤ m i := by
      intro h
      exact hs h
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply orthogonalCompleteSymmetricCoefficient_of_neg
    omega

theorem weylTargetExponent_sub_lowPower
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) :
    ((weylTargetExponent lam i : ℤ) - (r - j.val : ℕ)) =
      (lam i : ℤ) - (i.val : ℤ) + (j.val : ℤ) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [weylTargetExponent_apply]
  omega

theorem weylTargetExponent_sub_highPower
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) :
    ((weylTargetExponent lam i : ℤ) - (r + j.val + 2 : ℕ)) =
      (lam i : ℤ) - (i.val : ℤ) - (j.val : ℤ) - 2 := by
  have hi := i.isLt
  simp only [weylTargetExponent_apply]
  omega

theorem coeff_ambientBinomialPolynomial_mul_axisDifferenceProduct
    {r n B : ℕ} (m : Fin (r + 1) →₀ ℕ)
    (hm : ∀ i, m i ≤ B)
    (a b : Fin (r + 1) → ℕ) :
    MvPolynomial.coeff m
        (ambientBinomialPolynomial (r := r) n B *
          ∏ i : Fin (r + 1),
            ((MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^ a i -
              (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^ b i)) =
      ∏ i : Fin (r + 1),
        (orthogonalCompleteSymmetricCoefficient n
          ((m i : ℤ) - (a i : ℤ)) -
         orthogonalCompleteSymmetricCoefficient n
          ((m i : ℤ) - (b i : ℤ))) := by
  classical
  rw [Finset.prod_sub, Finset.mul_sum, MvPolynomial.coeff_sum,
    Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ⊆ (Finset.univ : Finset (Fin (r + 1))) :=
    Finset.mem_powerset.mp ht
  have hpoly :
      (∏ i ∈ Finset.univ \ t,
        (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^ a i) *
        (∏ i ∈ t,
          (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^ b i) =
        MvPolynomial.monomial
          (Finsupp.indicator (Finset.univ \ t) (fun i _ => a i) +
            Finsupp.indicator t (fun i _ => b i)) (1 : ℤ) := by
    rw [MvPolynomial.prod_X_pow, MvPolynomial.prod_X_pow,
      MvPolynomial.monomial_mul, mul_one]
  have hsign :
      (-1 : MvPolynomial (Fin (r + 1)) ℤ) ^ t.card =
        MvPolynomial.C ((-1 : ℤ) ^ t.card) := by simp only [Int.reduceNeg, eq_intCast, Int.cast_pow,
                                                   Int.cast_neg, Int.cast_one]
  rw [hsign]
  rw [mul_assoc (MvPolynomial.C _) _ _, hpoly]
  rw [mul_left_comm (ambientBinomialPolynomial (r := r) n B),
    MvPolynomial.coeff_C_mul,
    coeff_ambientBinomialPolynomial_mul_monomial m _ hm]
  rw [mul_assoc]
  congr 1
  rw [← Finset.prod_sdiff ht']
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i hi
    have hnot : i ∉ t := (Finset.mem_sdiff.mp hi).2
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.indicator_apply, hi, ↓reduceDIte, hnot,
      add_zero]
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.indicator_apply, Finset.mem_sdiff,
      Finset.mem_univ, hi, not_true_eq_false, and_false, ↓reduceDIte, zero_add]

theorem coeff_ambientBinomialPolynomial_mul_det_separable
    {r n B : ℕ} (m : Fin (r + 1) →₀ ℕ)
    (a b : Fin (r + 1) → Fin (r + 1) → ℕ)
    (hm : ∀ i, m i ≤ B) :
    MvPolynomial.coeff m
        (ambientBinomialPolynomial (r := r) n B *
          Matrix.det (Matrix.of fun i j : Fin (r + 1) =>
            (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^ a i j -
              (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^ b i j)) =
      Matrix.det (Matrix.of fun i j : Fin (r + 1) =>
        orthogonalCompleteSymmetricCoefficient n
          ((m i : ℤ) - (a i j : ℤ)) -
        orthogonalCompleteSymmetricCoefficient n
          ((m i : ℤ) - (b i j : ℤ))) := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply',
    Finset.mul_sum, MvPolynomial.coeff_sum,
    ← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  change
    MvPolynomial.coeff m
      (ambientBinomialPolynomial (r := r) n B *
        (MvPolynomial.C (Equiv.Perm.sign σ : ℤ) *
          ∏ i : Fin (r + 1),
            ((MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
                a i (σ i) -
              (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
                b i (σ i)))) =
      (Equiv.Perm.sign σ : ℤ) *
        ∏ i : Fin (r + 1),
          (orthogonalCompleteSymmetricCoefficient n
              ((m i : ℤ) - (a i (σ i) : ℤ)) -
            orthogonalCompleteSymmetricCoefficient n
              ((m i : ℤ) - (b i (σ i) : ℤ)))
  rw [mul_left_comm (ambientBinomialPolynomial (r := r) n B),
    MvPolynomial.coeff_C_mul,
    coeff_ambientBinomialPolynomial_mul_axisDifferenceProduct m hm
      (fun i => a i (σ i)) (fun i => b i (σ i))]

theorem coeff_ambientBinomialPolynomial_mul_orthogonalDenominator
    {r n B : ℕ} (lam : Fin (r + 1) → ℕ)
    (hB : ∀ i, weylTargetExponent lam i ≤ B) :
    MvPolynomial.coeff (weylTargetExponent lam)
        (ambientBinomialPolynomial (r := r) n B *
          Matrix.det (Matrix.of fun i j : Fin (r + 1) =>
            (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
                (r - j.val) -
              (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
                (r + j.val + 2))) =
      orthogonalJacobiTrudiDimension n lam := by
  rw [coeff_ambientBinomialPolynomial_mul_det_separable
    (weylTargetExponent lam)
    (fun _ j => r - j.val)
    (fun _ j => r + j.val + 2) hB]
  unfold orthogonalJacobiTrudiDimension orthogonalJacobiTrudiMatrix
  congr 1
  apply Matrix.ext
  intro i j
  simp only [Matrix.of_apply]
  rw [weylTargetExponent_sub_lowPower,
    weylTargetExponent_sub_highPower]

theorem gramEquationPolynomial_eq_upperPairProduct (r : ℕ) :
    gramEquationPolynomial r =
      ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ici i,
        (1 - MvPolynomial.X i * MvPolynomial.X j :
          MvPolynomial (Fin (r + 1)) ℤ) := by
  classical
  let pairs : Finset (Fin (r + 1) × Fin (r + 1)) :=
    (Finset.univ.product Finset.univ).filter (fun z => z.1 ≤ z.2)
  unfold gramEquationPolynomial
  calc
    _ = ∏ z ∈ pairs,
          (1 - MvPolynomial.X z.1 * MvPolynomial.X z.2 :
            MvPolynomial (Fin (r + 1)) ℤ) := by
          symm
          apply Finset.prod_subtype pairs
          intro z
          simp only [Finset.product_eq_sprod, Finset.univ_product_univ, Finset.mem_filter,
            Finset.mem_univ, true_and, pairs]
    _ = ∏ i ∈ (Finset.univ : Finset (Fin (r + 1))),
          ∏ j ∈ Finset.Ici i,
            (1 - MvPolynomial.X i * MvPolynomial.X j :
              MvPolynomial (Fin (r + 1)) ℤ) := by
          apply Finset.prod_finset_product pairs Finset.univ
            (fun i : Fin (r + 1) => Finset.Ici i)
          intro z
          simp only [Finset.product_eq_sprod, Finset.univ_product_univ, Finset.mem_filter,
            Finset.mem_univ, true_and, Finset.mem_Ici, pairs]
    _ = _ := by simp only

end HigherWeylQuadraticDeterminantCoefficient

namespace HigherWeylGramOrthogonalJacobiTrudi

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.OrthogonalDenominator
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherWeylGramAlternantCoefficient
open MetricCodes.Spherical.HigherWeylReversedAlternantCoefficient
open MetricCodes.Spherical.HigherWeylQuadraticDeterminantCoefficient

theorem alternatingGramKoszulCoefficient_eq_orthogonalJacobiTrudiDimension
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    alternatingGramKoszulCoefficient n lam =
      orthogonalJacobiTrudiDimension n lam := by
  classical
  let B : ℕ := ∑ i : Fin (r + 1), weylTargetExponent lam i
  have hB : ∀ i, weylTargetExponent lam i ≤ B := by
    intro i
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hdenominator :
      Matrix.det (fun i j : Fin (r + 1) =>
        (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
            (r - j.val) -
          (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
            (r + j.val + 2)) =
        reversedWeylPolynomial r * gramEquationPolynomial r := by
    rw [gramEquationPolynomial_eq_upperPairProduct]
    exact det_orthogonal_denominator
      (fun i : Fin (r + 1) =>
        (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ))
  calc
    alternatingGramKoszulCoefficient n lam =
        MvPolynomial.coeff (weylTargetExponent lam)
          ((ambientBinomialPolynomial (r := r) n B *
            gramEquationPolynomial r) * reversedWeylPolynomial r) :=
      (coeff_ambient_mul_gram_mul_reversedWeylPolynomial lam hB).symm
    _ = MvPolynomial.coeff (weylTargetExponent lam)
          (ambientBinomialPolynomial (r := r) n B *
            Matrix.det (fun i j : Fin (r + 1) =>
              (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
                  (r - j.val) -
                (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
                  (r + j.val + 2))) := by
      rw [hdenominator]
      congr 1
      ring
    _ = orthogonalJacobiTrudiDimension n lam :=
      coeff_ambientBinomialPolynomial_mul_orthogonalDenominator lam hB

end HigherWeylGramOrthogonalJacobiTrudi

namespace HigherWeylGeneralRowNormalization

private def risingFactorProduct (M q : ℕ) : ℝ :=
  ∏ a ∈ Finset.range q, (((M + a + 1 : ℕ) : ℝ))

theorem risingFactorProduct_eq_ascFactorial (M q : ℕ) :
    risingFactorProduct M q =
      (((M + 1).ascFactorial q : ℕ) : ℝ) := by
  rw [Nat.ascFactorial_eq_prod_range]
  push_cast
  unfold risingFactorProduct
  apply Finset.prod_congr rfl
  intro a _
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem risingFactorProduct_pos (M q : ℕ) :
    0 < risingFactorProduct M q := by
  unfold risingFactorProduct
  exact Finset.prod_pos fun a _ => by positivity

theorem factorial_mul_risingFactorProduct (M q : ℕ) :
    (M.factorial : ℝ) * risingFactorProduct M q =
      ((M + q).factorial : ℝ) := by
  rw [risingFactorProduct_eq_ascFactorial]
  exact_mod_cast Nat.factorial_mul_ascFactorial M q

theorem normalized_choose_rising
    (M k t q : ℕ) (ht : t ≤ q) :
    ((((M + k + q).choose (k + t) : ℕ) : ℝ) /
        risingFactorProduct (M + k) q) /
      ((((M + q).choose t : ℕ) : ℝ) /
        risingFactorProduct M q) =
      (((M + k).choose k : ℝ) /
        ((k + t).choose k : ℝ)) := by
  have hlarge : k + t ≤ M + k + q := by omega
  have hbase : t ≤ M + q := by omega
  have hsmall : k ≤ M + k := by omega
  have ht' : k ≤ k + t := by omega
  rw [Nat.cast_choose ℝ hlarge,
    Nat.cast_choose ℝ hbase,
    Nat.cast_choose ℝ hsmall,
    Nat.cast_choose ℝ ht']
  have hlargeSub : M + k + q - (k + t) = M + q - t := by omega
  have hsmallSub : M + k - k = M := by omega
  have htSub : k + t - k = t := by omega
  rw [hlargeSub, hsmallSub, htSub]
  have htop := factorial_mul_risingFactorProduct (M + k) q
  have hbottom := factorial_mul_risingFactorProduct M q
  have hfactorial (a : ℕ) : (a.factorial : ℝ) ≠ 0 := by positivity
  have htopDen : risingFactorProduct (M + k) q ≠ 0 :=
    (risingFactorProduct_pos (M + k) q).ne'
  have hbottomDen : risingFactorProduct M q ≠ 0 :=
    (risingFactorProduct_pos M q).ne'
  rw [← htop, ← hbottom]
  field_simp [hfactorial, htopDen, hbottomDen]

theorem normalized_choose_rising_with_linear
    (M k t q : ℕ) (ht : t ≤ q)
    (a b : ℝ) (hb : b ≠ 0) :
    (((((M + k + q).choose (k + t) : ℕ) : ℝ) * a /
        risingFactorProduct (M + k) q) /
      ((((M + q).choose t : ℕ) : ℝ) * b /
        risingFactorProduct M q)) =
      (a / b) * (((M + k).choose k : ℝ) /
        ((k + t).choose k : ℝ)) := by
  have hB : ((((M + q).choose t : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show t ≤ M + q by omega)).ne'
  have hD : risingFactorProduct (M + k) q ≠ 0 :=
    (risingFactorProduct_pos (M + k) q).ne'
  have hD₀ : risingFactorProduct M q ≠ 0 :=
    (risingFactorProduct_pos M q).ne'
  calc
    _ = (a / b) *
        (((((M + k + q).choose (k + t) : ℕ) : ℝ) /
          risingFactorProduct (M + k) q) /
        ((((M + q).choose t : ℕ) : ℝ) /
          risingFactorProduct M q)) := by
      field_simp [hB, hD, hD₀, hb]
    _ = _ := by rw [normalized_choose_rising M k t q ht]

end HigherWeylGeneralRowNormalization

end

section


namespace HigherWeylGeneralRowFactor

open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherWeylGeneralRowNormalization

private def orthogonalRowScale {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) : ℝ :=
  (orthogonalCompleteSymmetricCoefficient n
      ((lam i + Weyl.rowTail i : ℕ) : ℤ) : ℝ) *
    (2 * (lam i : ℝ) + (n : ℝ) -
      2 * ((i.val + 1 : ℕ) : ℝ)) /
    risingFactorProduct (Weyl.tailLength n r i + lam i) (2 * r + 2)

theorem baselineLinear_ne_zero {r n : ℕ}
    (hn : 2 * r + 4 ≤ n) (i : Fin (r + 1)) :
    (n : ℝ) - 2 * ((i.val + 1 : ℕ) : ℝ) ≠ 0 :=
  (Weyl.linearDenominator_pos hn i).ne'

theorem orthogonalRowScale_div_zero_eq_rowFactor
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    orthogonalRowScale n lam i /
        orthogonalRowScale n (fun _ : Fin (r + 1) => 0) i =
      Weyl.rowFactor n lam i := by
  let M := Weyl.tailLength n r i
  let k := lam i
  let t := Weyl.rowTail i
  let q := 2 * r + 2
  let a : ℝ := 2 * (lam i : ℝ) + (n : ℝ) -
    2 * ((i.val + 1 : ℕ) : ℝ)
  let b : ℝ := (n : ℝ) - 2 * ((i.val + 1 : ℕ) : ℝ)
  have ht : t ≤ q := by
    dsimp [t, q]
    unfold Weyl.rowTail
    omega
  have hb : b ≠ 0 := baselineLinear_ne_zero hn i
  have hupper : M + k + q = n + (k + t) - 1 := by
    dsimp [M, k, q, t]
    unfold Weyl.tailLength Weyl.rowTail
    have hi := i.isLt
    omega
  have hbase : M + q = n + t - 1 := by
    dsimp [M, q, t]
    unfold Weyl.tailLength Weyl.rowTail
    have hi := i.isLt
    omega
  have h := normalized_choose_rising_with_linear
    M k t q ht a b hb
  rw [hupper, hbase] at h
  rw [Weyl.rowFactor_eq_binomial]
  unfold orthogonalRowScale
  simp only [orthogonalCompleteSymmetricCoefficient_nat,
    Nat.cast_zero, zero_add, mul_zero]
  simpa [M, k, t, q, a, b, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

end HigherWeylGeneralRowFactor

end

section


open scoped BigOperators

namespace HigherWeylDescendingRowFactors

open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherWeylGeneralRowNormalization

theorem descendingFactorProduct_eq_risingFactorProduct
    (M q : ℕ) :
    (∏ a ∈ Finset.range q,
      (((M + q : ℕ) : ℝ) - (a : ℝ))) =
        risingFactorProduct M q := by
  calc
    _ = ∏ a ∈ Finset.range q,
          (((M + (q - 1 - a) + 1 : ℕ) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro a ha
      have ha' : a < q := Finset.mem_range.mp ha
      have hle : a ≤ M + q := by omega
      rw [← Nat.cast_sub hle]
      congr 1
      omega
    _ = ∏ a ∈ Finset.range q,
          (((M + a + 1 : ℕ) : ℝ)) :=
      Finset.prod_range_reflect
        (fun a : ℕ => (((M + a + 1 : ℕ) : ℝ))) q
    _ = _ := rfl

theorem descendingRowFactors_eq_risingFactorProduct
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    (∏ a ∈ Finset.range (2 * r + 2),
      ((n : ℝ) + (lam i : ℝ) - (i.val : ℝ) + (r : ℝ) - 1 -
        (a : ℝ))) =
      risingFactorProduct (Weyl.tailLength n r i + lam i)
        (2 * r + 2) := by
  let M := Weyl.tailLength n r i + lam i
  let q := 2 * r + 2
  have hi := i.isLt
  have htail : i.val + r + 3 ≤ n := by omega
  have htop : M + q = n + lam i + r - i.val - 1 := by
    dsimp [M, q]
    unfold Weyl.tailLength
    omega
  calc
    _ = ∏ a ∈ Finset.range q,
          (((M + q : ℕ) : ℝ) - (a : ℝ)) := by
      apply Finset.prod_congr rfl
      intro a _
      rw [htop]
      rw [Nat.cast_sub (show 1 ≤ n + lam i + r - i.val by omega),
        Nat.cast_sub (show i.val ≤ n + lam i + r by omega)]
      push_cast
      ring
    _ = risingFactorProduct M q :=
      descendingFactorProduct_eq_risingFactorProduct M q
    _ = _ := rfl

end HigherWeylDescendingRowFactors

end

section


namespace HigherWeylShiftedSquarePairNormalization

open MetricCodes.Spherical.HigherHierarchy

theorem shifted_square_pair_ratio_eq_pairFactor
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {i j : Fin (r + 1)} (hij : i < j) :
    ((((lam i : ℝ) - (i.val : ℝ)) *
          (((lam i : ℝ) - (i.val : ℝ)) + (n : ℝ) - 2) -
        ((lam j : ℝ) - (j.val : ℝ)) *
          (((lam j : ℝ) - (j.val : ℝ)) + (n : ℝ) - 2)) /
      (((-(i.val : ℝ)) * ((-(i.val : ℝ)) + (n : ℝ) - 2)) -
        ((-(j.val : ℝ)) * ((-(j.val : ℝ)) + (n : ℝ) - 2)))) =
      Weyl.pairFactor n lam i j := by
  have hindex : (j.val : ℝ) - (i.val : ℝ) ≠ 0 := by
    have hlt : (i.val : ℝ) < (j.val : ℝ) := by
      exact_mod_cast hij
    linarith
  have hsum : (n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2 ≠ 0 :=
    (Weyl.sumDenominator_pos hn i j).ne'
  have hbase :
      ((-(i.val : ℝ)) * ((-(i.val : ℝ)) + (n : ℝ) - 2)) -
        ((-(j.val : ℝ)) * ((-(j.val : ℝ)) + (n : ℝ) - 2)) =
      ((j.val : ℝ) - (i.val : ℝ)) *
        ((n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2) := by
    ring
  rw [hbase]
  unfold Weyl.pairFactor
  field_simp [hindex, hsum]
  ; ring

end HigherWeylShiftedSquarePairNormalization

end

section


open scoped BigOperators

namespace HigherWeylAllRankCommonInvariantPolynomial

open Polynomial

private def commonInvariantPolynomial (n : ℝ) (r k : ℕ) : Polynomial ℝ :=
  ∏ q ∈ Finset.range k,
    (X + C (((r : ℝ) - (q : ℝ)) * (n - (r : ℝ) - 2 + (q : ℝ))))

theorem commonInvariantPolynomial_natDegree (n : ℝ) (r k : ℕ) :
    (commonInvariantPolynomial n r k).natDegree = k := by
  classical
  unfold commonInvariantPolynomial
  rw [Polynomial.natDegree_prod_of_monic]
  · calc
      _ = ∑ _q ∈ Finset.range k, 1 := by
        apply Finset.sum_congr rfl
        intro q hq
        exact Polynomial.natDegree_X_add_C _
      _ = k := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  · intro q hq
    exact Polynomial.monic_X_add_C _

theorem commonInvariantPolynomial_eval (n z : ℝ) (r k : ℕ) :
    (commonInvariantPolynomial n r k).eval (z * (z + n - 2)) =
      (∏ q ∈ Finset.range k, (z + (r : ℝ) - (q : ℝ))) *
        (∏ q ∈ Finset.range k,
          (n + z - (r : ℝ) - 2 + (q : ℝ))) := by
  classical
  unfold commonInvariantPolynomial
  simp_rw [Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  ring

theorem commonInvariantPolynomial_mul_natDegree_le
    (n : ℝ) (r j : ℕ) (hj : j ≤ r)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ j) :
    (commonInvariantPolynomial n r (r - j) * p).natDegree ≤ r := by
  calc
    _ ≤ (commonInvariantPolynomial n r (r - j)).natDegree +
        p.natDegree := Polynomial.natDegree_mul_le
    _ ≤ (r - j) + j := by
      rw [commonInvariantPolynomial_natDegree]
      omega
    _ = r := Nat.sub_add_cancel hj

end HigherWeylAllRankCommonInvariantPolynomial

namespace HigherWeylMiddleProductClosedForm

private def middleProducts (n z : ℝ) : ℕ → (ℝ × ℝ)
  | 0 => ((n + z - 2) * (n + z - 1), (z - 1) * z)
  | j + 1 =>
      ((middleProducts n z j).1 *
          ((n + z - (j : ℝ) - 3) * (n + z + (j : ℝ))),
       (middleProducts n z j).2 *
          ((z - (j : ℝ) - 2) * (z + (j : ℝ) + 1)))

private def centeredProduct (x : ℝ) (j : ℕ) : ℝ :=
  ∏ s ∈ Finset.range (2 * j + 2),
    (x + (j : ℝ) - (s : ℝ))

@[simp] theorem centeredProduct_zero (x : ℝ) :
    centeredProduct x 0 = (x - 1) * x := by
  norm_num [centeredProduct, Finset.prod_range_succ]
  ring

theorem centeredProduct_succ (x : ℝ) (j : ℕ) :
    centeredProduct x (j + 1) =
      centeredProduct x j *
        ((x - (j : ℝ) - 2) * (x + (j : ℝ) + 1)) := by
  let f : ℕ → ℝ := fun s => x + (j : ℝ) + 1 - (s : ℝ)
  have hshift :
      (∏ s ∈ Finset.range (2 * j + 2), f (s + 1)) =
        centeredProduct x j := by
    unfold centeredProduct
    apply Finset.prod_congr rfl
    intro s _
    simp only [Nat.cast_add, Nat.cast_one, add_sub_add_right_eq_sub, f]
  change
    (∏ s ∈ Finset.range (2 * (j + 1) + 2),
      (x + ((j + 1 : ℕ) : ℝ) - (s : ℝ))) =
      centeredProduct x j *
        ((x - (j : ℝ) - 2) * (x + (j : ℝ) + 1))
  have hlen : 2 * (j + 1) + 2 = (2 * j + 3) + 1 := by omega
  rw [hlen]
  have hfactor :
      (fun s : ℕ => x + ((j + 1 : ℕ) : ℝ) - (s : ℝ)) = f := by
    funext s
    simp only [Nat.cast_add, Nat.cast_one, sub_left_inj, f]
    ring
  rw [hfactor, Finset.prod_range_succ' f (2 * j + 3)]
  have hmid : 2 * j + 3 = (2 * j + 2) + 1 := by omega
  rw [hmid, Finset.prod_range_succ
    (fun s : ℕ => f (s + 1)) (2 * j + 2), hshift]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_sub_add_right_eq_sub,
    CharP.cast_eq_zero, sub_zero, f]
  ring

theorem middleProducts_fst_eq_centeredProduct
    (n z : ℝ) (j : ℕ) :
    (middleProducts n z j).1 =
      centeredProduct (n + z - 1) j := by
  induction j with
  | zero =>
      rw [middleProducts, centeredProduct_zero]
      ring
  | succ j ih =>
      rw [middleProducts, ih, centeredProduct_succ]
      ring

theorem middleProducts_snd_eq_centeredProduct
    (n z : ℝ) (j : ℕ) :
    (middleProducts n z j).2 = centeredProduct z j := by
  induction j with
  | zero => simp only [middleProducts, centeredProduct_zero]
  | succ j ih =>
      rw [middleProducts, ih, centeredProduct_succ]

theorem middleProducts_fst_eq_prod
    (n z : ℝ) (j : ℕ) :
    (middleProducts n z j).1 =
      ∏ s ∈ Finset.range (2 * j + 2),
        (n + z + (j : ℝ) - 1 - (s : ℝ)) := by
  rw [middleProducts_fst_eq_centeredProduct]
  unfold centeredProduct
  apply Finset.prod_congr rfl
  intro s _
  ring

theorem middleProducts_snd_eq_prod
    (n z : ℝ) (j : ℕ) :
    (middleProducts n z j).2 =
      ∏ s ∈ Finset.range (2 * j + 2),
        (z + (j : ℝ) - (s : ℝ)) := by
  rw [middleProducts_snd_eq_centeredProduct]
  rfl

end HigherWeylMiddleProductClosedForm

namespace HigherWeylAllRankReflectedPrefixSuffixFactor

open MetricCodes.Spherical.HigherWeylAllRankCommonInvariantPolynomial
open MetricCodes.Spherical.HigherWeylMiddleProductClosedForm

theorem prod_prefix_suffix_sub_factor
    {R : Type*} [CommRing R] (f d : ℕ → R) (k m : ℕ) :
    (∏ q ∈ Finset.range k, f q) *
        (∏ q ∈ Finset.range (m + k), d (k + q)) -
      (∏ q ∈ Finset.range (k + m), f q) *
        (∏ q ∈ Finset.range k, d (k + m + q)) =
      (∏ q ∈ Finset.range k, f q) *
        (∏ q ∈ Finset.range k, d (k + m + q)) *
        ((∏ q ∈ Finset.range m, d (k + q)) -
          (∏ q ∈ Finset.range m, f (k + q))) := by
  rw [Finset.prod_range_add (fun q => d (k + q)) m k,
    Finset.prod_range_add f k m]
  simp only [add_assoc]
  ring

theorem orthogonal_reflected_prefix_suffix_factor
    (n z : ℝ) (r j : ℕ) (hj : j ≤ r) :
    ((∏ q ∈ Finset.range (r - j),
        (z + (r : ℝ) - (q : ℝ))) *
      (∏ q ∈ Finset.range (2 * r + 2 - (r - j)),
        (n + z + (r : ℝ) - 1 - ((r - j + q : ℕ) : ℝ))) -
     (∏ q ∈ Finset.range (r + j + 2),
        (z + (r : ℝ) - (q : ℝ))) *
      (∏ q ∈ Finset.range (2 * r + 2 - (r + j + 2)),
        (n + z + (r : ℝ) - 1 - ((r + j + 2 + q : ℕ) : ℝ)))) =
      ((∏ q ∈ Finset.range (r - j),
          (z + (r : ℝ) - (q : ℝ))) *
        (∏ q ∈ Finset.range (r - j),
          (n + z - (r : ℝ) - 2 + (q : ℝ)))) *
      ((∏ q ∈ Finset.range (2 * j + 2),
          (n + z + (j : ℝ) - 1 - (q : ℝ))) -
        (∏ q ∈ Finset.range (2 * j + 2),
          (z + (j : ℝ) - (q : ℝ)))) := by
  let k := r - j
  let m := 2 * j + 2
  have hcast : (k : ℝ) = (r : ℝ) - (j : ℝ) := by
    dsimp [k]
    rw [Nat.cast_sub hj]
  have hlen₁ : 2 * r + 2 - (r - j) = m + k := by
    dsimp [m, k]
    omega
  have hlen₂ : r + j + 2 = k + m := by
    dsimp [m, k]
    omega
  have hlen₃ : 2 * r + 2 - (r + j + 2) = k := by
    dsimp [k]
    omega
  have houter :
      (∏ q ∈ Finset.range k,
        (n + z + (r : ℝ) - 1 - ((k + m + q : ℕ) : ℝ))) =
      (∏ q ∈ Finset.range k,
        (n + z - (r : ℝ) - 2 + (q : ℝ))) := by
    calc
      _ = ∏ q ∈ Finset.range k,
          (n + z - (r : ℝ) - 2 + ((k - 1 - q : ℕ) : ℝ)) := by
        apply Finset.prod_congr rfl
        intro q hq
        have hqk : q < k := Finset.mem_range.mp hq
        have hsub : ((k - 1 - q : ℕ) : ℝ) =
            (k : ℝ) - 1 - q := by
          rw [Nat.cast_sub (show q ≤ k - 1 by omega),
            Nat.cast_sub (show 1 ≤ k by omega)]
          norm_num
        rw [hsub]
        dsimp [m]
        push_cast
        rw [hcast]
        ring
      _ = _ := Finset.prod_range_reflect
        (fun q : ℕ => n + z - (r : ℝ) - 2 + (q : ℝ)) k
  have hmiddleD :
      (∏ q ∈ Finset.range m,
        (n + z + (r : ℝ) - 1 - ((k + q : ℕ) : ℝ))) =
      (∏ q ∈ Finset.range m,
        (n + z + (j : ℝ) - 1 - (q : ℝ))) := by
    apply Finset.prod_congr rfl
    intro q hq
    push_cast
    rw [hcast]
    ring
  have hmiddleF :
      (∏ q ∈ Finset.range m,
        (z + (r : ℝ) - ((k + q : ℕ) : ℝ))) =
      (∏ q ∈ Finset.range m,
        (z + (j : ℝ) - (q : ℝ))) := by
    apply Finset.prod_congr rfl
    intro q hq
    push_cast
    rw [hcast]
    ring
  rw [hlen₃, hlen₁, hlen₂]
  change
    (∏ q ∈ Finset.range k, (z + (r : ℝ) - (q : ℝ))) *
        (∏ q ∈ Finset.range (m + k),
          (n + z + (r : ℝ) - 1 - ((k + q : ℕ) : ℝ))) -
      (∏ q ∈ Finset.range (k + m),
        (z + (r : ℝ) - (q : ℝ))) *
        (∏ q ∈ Finset.range k,
          (n + z + (r : ℝ) - 1 - ((k + m + q : ℕ) : ℝ))) = _
  rw [prod_prefix_suffix_sub_factor
    (fun q => z + (r : ℝ) - (q : ℝ))
    (fun q => n + z + (r : ℝ) - 1 - (q : ℝ)) k m,
    houter, hmiddleD, hmiddleF]

theorem orthogonal_reflected_prefix_suffix_eq_invariant_middle
    (n z : ℝ) (r j : ℕ) (hj : j ≤ r) :
    ((∏ q ∈ Finset.range (r - j),
        (z + (r : ℝ) - (q : ℝ))) *
      (∏ q ∈ Finset.range (2 * r + 2 - (r - j)),
        (n + z + (r : ℝ) - 1 - ((r - j + q : ℕ) : ℝ))) -
     (∏ q ∈ Finset.range (r + j + 2),
        (z + (r : ℝ) - (q : ℝ))) *
      (∏ q ∈ Finset.range (2 * r + 2 - (r + j + 2)),
        (n + z + (r : ℝ) - 1 - ((r + j + 2 + q : ℕ) : ℝ)))) =
      (commonInvariantPolynomial n r (r - j)).eval
          (z * (z + n - 2)) *
        ((middleProducts n z j).1 -
          (middleProducts n z j).2) := by
  rw [orthogonal_reflected_prefix_suffix_factor n z r j hj,
    commonInvariantPolynomial_eval,
    middleProducts_fst_eq_prod,
    middleProducts_snd_eq_prod]

end HigherWeylAllRankReflectedPrefixSuffixFactor

namespace HigherWeylAllRankJacobiTrudiWeylEvaluation

open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherWeylShiftedSquarePairNormalization
open MetricCodes.Spherical.HigherWeylGeneralRowFactor
open MetricCodes.Spherical.HigherWeylGeneralRowNormalization
open MetricCodes.Spherical.HigherWeylDescendingRowFactors
open MetricCodes.Spherical.HigherWeylAllRankCommonInvariantPolynomial
open MetricCodes.Spherical.HigherWeylAllRankReflectedPrefixSuffixFactor
open MetricCodes.Spherical.HigherWeylMiddleProductClosedForm
open MetricCodes.Spherical.HigherHierarchy

theorem orthogonalCompleteSymmetricCoefficient_succ
    {n : ℕ} (hn : 0 < n) (k : ℤ) :
    (k + 1) * orthogonalCompleteSymmetricCoefficient n (k + 1) =
      ((n : ℤ) + k) * orthogonalCompleteSymmetricCoefficient n k := by
  by_cases hk : 0 ≤ k
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by omega,
      orthogonalCompleteSymmetricCoefficient_nat,
      orthogonalCompleteSymmetricCoefficient_nat]
    have h := Nat.add_one_mul_choose_eq (n + m - 1) m
    have hfirst : n + m - 1 + 1 = n + m := by omega
    have hsecond : n + (m + 1) - 1 = n + m := by omega
    rw [hfirst] at h
    rw [hsecond]
    have h' := h.symm
    rw [Nat.mul_comm] at h'
    exact_mod_cast h'
  · have hkneg : k < 0 := lt_of_not_ge hk
    by_cases hnext : k + 1 = 0
    · rw [hnext]
      simp only [orthogonalCompleteSymmetricCoefficient, Std.le_refl, ↓reduceIte, Int.toNat_zero,
        add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, not_le.mpr hkneg, mul_zero]
    · have hnextneg : k + 1 < 0 := by omega
      rw [orthogonalCompleteSymmetricCoefficient_of_neg n hkneg,
        orthogonalCompleteSymmetricCoefficient_of_neg n hnextneg]
      ring

theorem orthogonalCompleteSymmetricCoefficient_descend
    {n : ℕ} (hn : 0 < n) (z : ℤ) (r k : ℕ) :
    (∏ q ∈ Finset.range k,
      ((n : ℤ) + z + (r : ℤ) - 1 - (q : ℤ))) *
        orthogonalCompleteSymmetricCoefficient n
          (z + (r : ℤ) - (k : ℤ)) =
      (∏ q ∈ Finset.range k,
        (z + (r : ℤ) - (q : ℤ))) *
          orthogonalCompleteSymmetricCoefficient n
            (z + (r : ℤ)) := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.prod_empty, CharP.cast_eq_zero, sub_zero, one_mul]
  | succ k ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      have hstep :
          ((n : ℤ) + z + (r : ℤ) - 1 - (k : ℤ)) *
              orthogonalCompleteSymmetricCoefficient n
                (z + (r : ℤ) - ((k + 1 : ℕ) : ℤ)) =
            (z + (r : ℤ) - (k : ℤ)) *
              orthogonalCompleteSymmetricCoefficient n
                (z + (r : ℤ) - (k : ℤ)) := by
        convert (orthogonalCompleteSymmetricCoefficient_succ hn
          (z + (r : ℤ) - (k : ℤ) - 1)).symm using 1 <;>
          push_cast <;> ring_nf
      calc
        _ = (∏ q ∈ Finset.range k,
            ((n : ℤ) + z + (r : ℤ) - 1 - (q : ℤ))) *
              (((n : ℤ) + z + (r : ℤ) - 1 - (k : ℤ)) *
                orthogonalCompleteSymmetricCoefficient n
                  (z + (r : ℤ) - ((k + 1 : ℕ) : ℤ))) := by ring
        _ = (∏ q ∈ Finset.range k,
            ((n : ℤ) + z + (r : ℤ) - 1 - (q : ℤ))) *
              ((z + (r : ℤ) - (k : ℤ)) *
                orthogonalCompleteSymmetricCoefficient n
                  (z + (r : ℤ) - (k : ℤ))) := by rw [hstep]
        _ = (z + (r : ℤ) - (k : ℤ)) *
              ((∏ q ∈ Finset.range k,
                ((n : ℤ) + z + (r : ℤ) - 1 - (q : ℤ))) *
                orthogonalCompleteSymmetricCoefficient n
                  (z + (r : ℤ) - (k : ℤ))) := by ring
        _ = (z + (r : ℤ) - (k : ℤ)) *
              ((∏ q ∈ Finset.range k,
                (z + (r : ℤ) - (q : ℤ))) *
                orthogonalCompleteSymmetricCoefficient n
                  (z + (r : ℤ))) := by rw [ih]
        _ = _ := by ring

theorem orthogonalCompleteSymmetricCoefficient_descend_commonDenominator
    {n : ℕ} (hn : 0 < n) (z : ℤ) (r L k : ℕ) (hk : k ≤ L) :
    (∏ q ∈ Finset.range L,
      ((n : ℤ) + z + (r : ℤ) - 1 - (q : ℤ))) *
        orthogonalCompleteSymmetricCoefficient n
          (z + (r : ℤ) - (k : ℤ)) =
      orthogonalCompleteSymmetricCoefficient n (z + (r : ℤ)) *
        (∏ q ∈ Finset.range k,
          (z + (r : ℤ) - (q : ℤ))) *
        (∏ q ∈ Finset.range (L - k),
          ((n : ℤ) + z + (r : ℤ) - 1 - ((k + q : ℕ) : ℤ))) := by
  have hsplit :
      (∏ q ∈ Finset.range L,
        ((n : ℤ) + z + (r : ℤ) - 1 - (q : ℤ))) =
        (∏ q ∈ Finset.range k,
          ((n : ℤ) + z + (r : ℤ) - 1 - (q : ℤ))) *
        (∏ q ∈ Finset.range (L - k),
          ((n : ℤ) + z + (r : ℤ) - 1 - ((k + q : ℕ) : ℤ))) := by
    convert Finset.prod_range_add
      (fun q : ℕ => ((n : ℤ) + z + (r : ℤ) - 1 - (q : ℤ)))
      k (L - k) using 1 ;
      simp [Nat.add_sub_of_le hk]
  rw [hsplit]
  have hdesc := orthogonalCompleteSymmetricCoefficient_descend
    hn z r k
  linear_combination
    (∏ q ∈ Finset.range (L - k),
      ((n : ℤ) + z + (r : ℤ) - 1 - ((k + q : ℕ) : ℤ))) * hdesc

theorem orthogonalCompleteSymmetricCoefficient_descend_commonDenominator_sub
    {n : ℕ} (hn : 0 < n) (z : ℤ) (r L k₁ k₂ : ℕ)
    (hk₁ : k₁ ≤ L) (hk₂ : k₂ ≤ L) :
    (∏ q ∈ Finset.range L,
      ((n : ℤ) + z + (r : ℤ) - 1 - (q : ℤ))) *
        (orthogonalCompleteSymmetricCoefficient n
          (z + (r : ℤ) - (k₁ : ℤ)) -
         orthogonalCompleteSymmetricCoefficient n
          (z + (r : ℤ) - (k₂ : ℤ))) =
      orthogonalCompleteSymmetricCoefficient n (z + (r : ℤ)) *
        ((∏ q ∈ Finset.range k₁,
            (z + (r : ℤ) - (q : ℤ))) *
          (∏ q ∈ Finset.range (L - k₁),
            ((n : ℤ) + z + (r : ℤ) - 1 - ((k₁ + q : ℕ) : ℤ))) -
         (∏ q ∈ Finset.range k₂,
            (z + (r : ℤ) - (q : ℤ))) *
          (∏ q ∈ Finset.range (L - k₂),
            ((n : ℤ) + z + (r : ℤ) - 1 - ((k₂ + q : ℕ) : ℤ)))) := by
  have h₁ := orthogonalCompleteSymmetricCoefficient_descend_commonDenominator
    hn z r L k₁ hk₁
  have h₂ := orthogonalCompleteSymmetricCoefficient_descend_commonDenominator
    hn z r L k₂ hk₂
  linear_combination h₁ - h₂

theorem orthogonalCompleteSymmetricCoefficient_reflected_commonDenominator
    {n : ℕ} (hn : 0 < n) (z : ℤ) (r j : ℕ) (hj : j ≤ r) :
    (∏ q ∈ Finset.range (2 * r + 2),
      ((n : ℤ) + z + (r : ℤ) - 1 - (q : ℤ))) *
        (orthogonalCompleteSymmetricCoefficient n (z + (j : ℤ)) -
         orthogonalCompleteSymmetricCoefficient n (z - (j : ℤ) - 2)) =
      orthogonalCompleteSymmetricCoefficient n (z + (r : ℤ)) *
        ((∏ q ∈ Finset.range (r - j),
            (z + (r : ℤ) - (q : ℤ))) *
          (∏ q ∈ Finset.range (2 * r + 2 - (r - j)),
            ((n : ℤ) + z + (r : ℤ) - 1 -
              ((r - j + q : ℕ) : ℤ))) -
         (∏ q ∈ Finset.range (r + j + 2),
            (z + (r : ℤ) - (q : ℤ))) *
          (∏ q ∈ Finset.range (2 * r + 2 - (r + j + 2)),
            ((n : ℤ) + z + (r : ℤ) - 1 -
              ((r + j + 2 + q : ℕ) : ℤ)))) := by
  have hfirst : r - j ≤ 2 * r + 2 := by omega
  have hsecond : r + j + 2 ≤ 2 * r + 2 := by omega
  have hindex₁ : z + (r : ℤ) - ((r - j : ℕ) : ℤ) =
      z + (j : ℤ) := by
    rw [Nat.cast_sub hj]
    ring
  have hindex₂ : z + (r : ℤ) - ((r + j + 2 : ℕ) : ℤ) =
      z - (j : ℤ) - 2 := by
    push_cast
    ring
  have h := orthogonalCompleteSymmetricCoefficient_descend_commonDenominator_sub
    hn z r (2 * r + 2) (r - j) (r + j + 2) hfirst hsecond
  rw [hindex₁, hindex₂] at h
  exact h

theorem orthogonalJacobiTrudiDimension_zero
    {r n : ℕ} :
    orthogonalJacobiTrudiDimension n
      (fun _ : Fin (r + 1) => 0) = 1 := by
  classical
  have hupper :
      (orthogonalJacobiTrudiMatrix n
        (fun _ : Fin (r + 1) => 0)).BlockTriangular id := by
    intro i j hij
    change
      orthogonalCompleteSymmetricCoefficient n
          ((0 : ℤ) - (i.val : ℤ) + (j.val : ℤ)) -
        orthogonalCompleteSymmetricCoefficient n
          ((0 : ℤ) - (i.val : ℤ) - (j.val : ℤ) - 2) = 0
    have hji : j.val < i.val := hij
    have hfirst : (0 : ℤ) - (i.val : ℤ) + (j.val : ℤ) < 0 := by
      omega
    have hsecond :
        (0 : ℤ) - (i.val : ℤ) - (j.val : ℤ) - 2 < 0 := by
      omega
    rw [orthogonalCompleteSymmetricCoefficient_of_neg n hfirst,
      orthogonalCompleteSymmetricCoefficient_of_neg n hsecond]
    ring
  unfold orthogonalJacobiTrudiDimension
  rw [Matrix.det_of_isUpperTriangular hupper]
  apply Finset.prod_eq_one
  intro i _
  change
    orthogonalCompleteSymmetricCoefficient n
        ((0 : ℤ) - (i.val : ℤ) + (i.val : ℤ)) -
      orthogonalCompleteSymmetricCoefficient n
        ((0 : ℤ) - (i.val : ℤ) - (i.val : ℤ) - 2) = 1
  have hneg : (0 : ℤ) - (i.val : ℤ) - (i.val : ℤ) - 2 < 0 := by
    omega
  rw [orthogonalCompleteSymmetricCoefficient_of_neg n hneg]
  norm_num [orthogonalCompleteSymmetricCoefficient]

private def middlePolynomials (n : ℝ) : ℕ → (Polynomial ℝ × Polynomial ℝ)
  | 0 =>
      (Polynomial.C (n - 1),
        Polynomial.C 2 * Polynomial.X +
          Polynomial.C ((n - 2) * (n - 1)))
  | j + 1 =>
      let q := (middlePolynomials n j).1
      let s := (middlePolynomials n j).2
      let a := Polynomial.X + Polynomial.C ((n ^ 2 - 3 * n -
        2 * (j : ℝ) ^ 2 - 6 * (j : ℝ) - 2) / 2)
      (a * q + Polynomial.C ((n - 1) / 2) * s,
        Polynomial.C ((n - 1) / 2) *
          (Polynomial.C 4 * Polynomial.X +
            Polynomial.C ((n - 2) ^ 2)) * q + a * s)

theorem middleProducts_sub_add (n z : ℝ) (j : ℕ) :
    (middleProducts n z j).1 - (middleProducts n z j).2 =
        (2 * z + n - 2) *
          (middlePolynomials n j).1.eval (z * (z + n - 2)) ∧
      (middleProducts n z j).1 + (middleProducts n z j).2 =
        (middlePolynomials n j).2.eval (z * (z + n - 2)) := by
  induction j with
  | zero =>
      simp only [middleProducts, middlePolynomials, map_sub, map_one, map_mul, Polynomial.eval_sub,
        Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X]
      constructor <;> ring
  | succ j ih =>
      simp only [middleProducts, middlePolynomials,
        Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      constructor
      · linear_combination
          (((n + z - (j : ℝ) - 3) * (n + z + (j : ℝ)) +
              ((z - (j : ℝ) - 2) * (z + (j : ℝ) + 1))) / 2) * ih.1 +
            (((n + z - (j : ℝ) - 3) * (n + z + (j : ℝ)) -
              ((z - (j : ℝ) - 2) * (z + (j : ℝ) + 1))) / 2) * ih.2
      · linear_combination
          (((n + z - (j : ℝ) - 3) * (n + z + (j : ℝ)) -
              ((z - (j : ℝ) - 2) * (z + (j : ℝ) + 1))) / 2) * ih.1 +
            (((n + z - (j : ℝ) - 3) * (n + z + (j : ℝ)) +
              ((z - (j : ℝ) - 2) * (z + (j : ℝ) + 1))) / 2) * ih.2

theorem middlePolynomials_natDegree (n : ℝ) (j : ℕ) :
    (middlePolynomials n j).1.natDegree ≤ j ∧
      (middlePolynomials n j).2.natDegree ≤ j + 1 := by
  induction j with
  | zero =>
      change (Polynomial.C (n - 1)).natDegree ≤ 0 ∧
        (Polynomial.C 2 * Polynomial.X +
          Polynomial.C ((n - 2) * (n - 1))).natDegree ≤ 1
      constructor
      · exact (Polynomial.natDegree_C (n - 1)).le
      · apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · exact (Polynomial.natDegree_C_mul_le 2 Polynomial.X).trans
            (by rw [Polynomial.natDegree_X])
        · rw [Polynomial.natDegree_C]
          omega
  | succ j ih =>
      simp only [middlePolynomials]
      constructor
      · calc
          _ ≤ max
              ((Polynomial.X + Polynomial.C ((n ^ 2 - 3 * n -
                2 * (j : ℝ) ^ 2 - 6 * (j : ℝ) - 2) / 2)) *
                  (middlePolynomials n j).1).natDegree
              (Polynomial.C ((n - 1) / 2) *
                (middlePolynomials n j).2).natDegree :=
            Polynomial.natDegree_add_le _ _
          _ ≤ j + 1 := by
            apply max_le
            · calc
                _ ≤ (Polynomial.X + Polynomial.C ((n ^ 2 - 3 * n -
                  2 * (j : ℝ) ^ 2 - 6 * (j : ℝ) - 2) / 2)).natDegree +
                    (middlePolynomials n j).1.natDegree :=
                  Polynomial.natDegree_mul_le
                _ ≤ 1 + j := by
                  have ha : (Polynomial.X + Polynomial.C ((n ^ 2 - 3 * n -
                      2 * (j : ℝ) ^ 2 - 6 * (j : ℝ) - 2) / 2)).natDegree ≤ 1 := by
                    exact (Polynomial.natDegree_add_le _ _).trans
                      (by simp only [Polynomial.natDegree_X, Polynomial.natDegree_C, zero_le,
                            sup_of_le_left, Std.le_refl])
                  omega
                _ = j + 1 := by omega
            · exact (Polynomial.natDegree_C_mul_le _ _).trans ih.2
      · calc
          _ ≤ max
              (Polynomial.C ((n - 1) / 2) *
                (Polynomial.C 4 * Polynomial.X +
                  Polynomial.C ((n - 2) ^ 2)) *
                (middlePolynomials n j).1).natDegree
              ((Polynomial.X + Polynomial.C ((n ^ 2 - 3 * n -
                2 * (j : ℝ) ^ 2 - 6 * (j : ℝ) - 2) / 2)) *
                (middlePolynomials n j).2).natDegree :=
            Polynomial.natDegree_add_le _ _
          _ ≤ j + 1 + 1 := by
            apply max_le
            · calc
                _ ≤ (Polynomial.C ((n - 1) / 2) *
                  (Polynomial.C 4 * Polynomial.X +
                    Polynomial.C ((n - 2) ^ 2))).natDegree +
                    (middlePolynomials n j).1.natDegree :=
                  Polynomial.natDegree_mul_le
                _ ≤ 1 + j := by
                  have ha : (Polynomial.C ((n - 1) / 2) *
                      (Polynomial.C 4 * Polynomial.X +
                        Polynomial.C ((n - 2) ^ 2))).natDegree ≤ 1 := by
                    apply (Polynomial.natDegree_C_mul_le _ _).trans
                    exact (Polynomial.natDegree_add_le _ _).trans
                      (by simp only [ne_eq, map_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
                            Polynomial.natDegree_mul_X, Polynomial.natDegree_C, zero_add, map_pow,
                            map_sub, Polynomial.natDegree_pow, Polynomial.natDegree_sub_C, mul_zero,
                            zero_le, sup_of_le_left, Std.le_refl])
                  omega
                _ ≤ j + 1 + 1 := by omega
            · calc
                _ ≤ (Polynomial.X + Polynomial.C ((n ^ 2 - 3 * n -
                  2 * (j : ℝ) ^ 2 - 6 * (j : ℝ) - 2) / 2)).natDegree +
                    (middlePolynomials n j).2.natDegree :=
                  Polynomial.natDegree_mul_le
                _ ≤ 1 + (j + 1) := by
                  have ha : (Polynomial.X + Polynomial.C ((n ^ 2 - 3 * n -
                      2 * (j : ℝ) ^ 2 - 6 * (j : ℝ) - 2) / 2)).natDegree ≤ 1 := by
                    exact (Polynomial.natDegree_add_le _ _).trans
                      (by simp only [Polynomial.natDegree_X, Polynomial.natDegree_C, zero_le,
                            sup_of_le_left, Std.le_refl])
                  omega
                _ = j + 1 + 1 := by omega

private def orthogonalColumnPolynomial (n : ℝ) (r : ℕ)
    (j : Fin (r + 1)) : Polynomial ℝ :=
  commonInvariantPolynomial n r (r - j.val) *
    (middlePolynomials n j.val).1

theorem orthogonalColumnPolynomial_natDegree_le
    (n : ℝ) (r : ℕ) (j : Fin (r + 1)) :
    (orthogonalColumnPolynomial n r j).natDegree ≤ r := by
  unfold orthogonalColumnPolynomial
  apply commonInvariantPolynomial_mul_natDegree_le
  · omega
  · exact (middlePolynomials_natDegree n j.val).1

private def shiftedSquare {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) : ℝ :=
  ((lam i : ℝ) - (i.val : ℝ)) *
    (((lam i : ℝ) - (i.val : ℝ)) + (n : ℝ) - 2)

theorem eval_matrixOfPolynomials_fixedRank
    {r : ℕ} (v : Fin (r + 1) → ℝ)
    (p : Fin (r + 1) → Polynomial ℝ)
    (hdegree : ∀ j, (p j).natDegree ≤ r) :
    Matrix.of (fun i j : Fin (r + 1) => (p j).eval (v i)) =
      Matrix.vandermonde v *
        Matrix.of (fun i j : Fin (r + 1) => (p j).coeff i.val) := by
  classical
  ext i j
  simp_rw [Matrix.mul_apply, Polynomial.eval, Matrix.of_apply,
    Polynomial.eval₂_eq_sum]
  simp only [Matrix.vandermonde]
  have hsupp : (p j).support ⊆ Finset.range (r + 1) :=
    Polynomial.supp_subset_range
      (Nat.lt_of_le_of_lt (hdegree j) (Nat.lt_succ_self r))
  rw [Polynomial.sum_eq_of_subset _ (fun k => zero_mul ((v i) ^ k)) hsupp,
    ← Fin.sum_univ_eq_sum_range]
  congr
  ext k
  rw [mul_comm, Matrix.of_apply, RingHom.id_apply]

theorem det_shiftedSquare_evaluation_div_zero_of_degree_le
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (p : Fin (r + 1) → Polynomial ℝ)
    (hdegree : ∀ j, (p j).natDegree ≤ r)
    (hzero : Matrix.det (fun i j : Fin (r + 1) =>
      (p j).eval
        (shiftedSquare n (fun _ : Fin (r + 1) => 0) i)) ≠ 0) :
    Matrix.det (fun i j : Fin (r + 1) =>
        (p j).eval (shiftedSquare n lam i)) /
      Matrix.det (fun i j : Fin (r + 1) =>
        (p j).eval
          (shiftedSquare n (fun _ : Fin (r + 1) => 0) i)) =
      ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
        Weyl.pairFactor n lam i j := by
  classical
  let C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    Matrix.of (fun i j : Fin (r + 1) => (p j).coeff i.val)
  have heval (v : Fin (r + 1) → ℝ) :
      Matrix.det (fun i j : Fin (r + 1) => (p j).eval (v i)) =
        (Matrix.vandermonde v).det * C.det := by
    change
      (Matrix.of (fun i j : Fin (r + 1) => (p j).eval (v i))).det = _
    rw [eval_matrixOfPolynomials_fixedRank v p hdegree,
      Matrix.det_mul]
  have hC : C.det ≠ 0 := by
    intro h
    apply hzero
    rw [heval, h, mul_zero]
  rw [heval, heval, mul_div_mul_right _ _ hC,
    Matrix.det_vandermonde, Matrix.det_vandermonde,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  have hpair := shifted_square_pair_ratio_eq_pairFactor hn lam hij
  change
    (shiftedSquare n lam j - shiftedSquare n lam i) /
      (shiftedSquare n (fun _ : Fin (r + 1) => 0) j -
        shiftedSquare n (fun _ : Fin (r + 1) => 0) i) = _
  have hflip :
      (shiftedSquare n lam j - shiftedSquare n lam i) /
          (shiftedSquare n (fun _ : Fin (r + 1) => 0) j -
            shiftedSquare n (fun _ : Fin (r + 1) => 0) i) =
        (shiftedSquare n lam i - shiftedSquare n lam j) /
          (shiftedSquare n (fun _ : Fin (r + 1) => 0) i -
            shiftedSquare n (fun _ : Fin (r + 1) => 0) j) := by
    rw [show shiftedSquare n lam j - shiftedSquare n lam i =
      -(shiftedSquare n lam i - shiftedSquare n lam j) by ring]
    rw [show shiftedSquare n (fun _ : Fin (r + 1) => 0) j -
        shiftedSquare n (fun _ : Fin (r + 1) => 0) i =
      -(shiftedSquare n (fun _ : Fin (r + 1) => 0) i -
        shiftedSquare n (fun _ : Fin (r + 1) => 0) j) by ring]
    exact neg_div_neg_eq _ _
  rw [hflip]
  simpa only [shiftedSquare, CharP.cast_eq_zero, zero_sub, neg_mul, sub_neg_eq_add] using hpair

theorem det_rowScaled_polynomial_evaluation
    {r : ℕ} (scale T : Fin (r + 1) → ℝ)
    (p : Fin (r + 1) → Polynomial ℝ) :
    Matrix.det (fun i j : Fin (r + 1) =>
        scale i * (p j).eval (T i)) =
      (∏ i : Fin (r + 1), scale i) *
        Matrix.det (fun i j : Fin (r + 1) => (p j).eval (T i)) := by
  change
    (Matrix.of (fun i j : Fin (r + 1) =>
      scale i * (p j).eval (T i))).det = _
  exact Matrix.det_mul_column scale
    (Matrix.of (fun i j : Fin (r + 1) => (p j).eval (T i)))

theorem polynomial_evaluation_det_ne_zero_of_rowScaled
    {r : ℕ} (scale T : Fin (r + 1) → ℝ)
    (p : Fin (r + 1) → Polynomial ℝ)
    (hdet : Matrix.det (fun i j : Fin (r + 1) =>
      scale i * (p j).eval (T i)) ≠ 0) :
    Matrix.det (fun i j : Fin (r + 1) => (p j).eval (T i)) ≠ 0 := by
  intro hzero
  apply hdet
  rw [det_rowScaled_polynomial_evaluation, hzero, mul_zero]

theorem det_rowScaled_shiftedSquare_evaluation_eq
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (p : Fin (r + 1) → Polynomial ℝ)
    (hdegree : ∀ j, (p j).natDegree ≤ r)
    (scale scaleZero : Fin (r + 1) → ℝ)
    (hscaleZero : ∀ i, scaleZero i ≠ 0)
    (hzero : Matrix.det (fun i j : Fin (r + 1) =>
      scaleZero i *
        (p j).eval
          (shiftedSquare n (fun _ : Fin (r + 1) => 0) i)) = 1) :
    Matrix.det (fun i j : Fin (r + 1) =>
        scale i * (p j).eval (shiftedSquare n lam i)) =
      ((∏ i : Fin (r + 1), scale i) /
        (∏ i : Fin (r + 1), scaleZero i)) *
        ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
          Weyl.pairFactor n lam i j := by
  classical
  let T : Fin (r + 1) → ℝ := shiftedSquare n lam
  let U : Fin (r + 1) → ℝ :=
    shiftedSquare n (fun _ : Fin (r + 1) => 0)
  let D : ℝ := Matrix.det (fun i j : Fin (r + 1) => (p j).eval (T i))
  let E : ℝ := Matrix.det (fun i j : Fin (r + 1) => (p j).eval (U i))
  let P : ℝ := ∏ i : Fin (r + 1), scale i
  let Q : ℝ := ∏ i : Fin (r + 1), scaleZero i
  let R : ℝ :=
    ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
      Weyl.pairFactor n lam i j
  have hscaled :
      Matrix.det (fun i j : Fin (r + 1) =>
        scaleZero i * (p j).eval (U i)) ≠ 0 := by
    have hscaled_eq :
        Matrix.det (fun i j : Fin (r + 1) =>
          scaleZero i * (p j).eval (U i)) = 1 := by
      simpa only using hzero
    rw [hscaled_eq]
    norm_num
  have hE : E ≠ 0 :=
    polynomial_evaluation_det_ne_zero_of_rowScaled
      scaleZero U p hscaled
  have hQ : Q ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hscaleZero i
  have hQE : Q * E = 1 := by
    simpa only using (det_rowScaled_polynomial_evaluation scaleZero U p).symm.trans hzero
  have hDE : D / E = R := by
    exact det_shiftedSquare_evaluation_div_zero_of_degree_le
      hn lam p hdegree hE
  have hD : D = R * E := (div_eq_iff hE).mp hDE
  rw [det_rowScaled_polynomial_evaluation]
  change P * D = (P / Q) * R
  rw [hD]
  calc
    P * (R * E) = (P * R) / Q := by
      apply (eq_div_iff hQ).2
      calc
        P * (R * E) * Q = P * R * (Q * E) := by ring
        _ = P * R := by rw [hQE, mul_one]
    _ = (P / Q) * R := by ring

theorem pairProduct_Ioi_eq_conditional
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
      Weyl.pairFactor n lam i j) =
      ∏ i : Fin (r + 1), ∏ j : Fin (r + 1),
        if i < j then Weyl.pairFactor n lam i j else 1 := by
  classical
  apply Finset.prod_congr rfl
  intro i _
  have hfilter :
      (Finset.univ : Finset (Fin (r + 1))).filter (fun j => i < j) =
        Finset.Ioi i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
  rw [← hfilter, Finset.prod_filter]

theorem rowRatio_mul_pairProduct_eq_weyl_dimension
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (scale scaleZero : Fin (r + 1) → ℝ)
    (hrow : ∀ i, scale i / scaleZero i = Weyl.rowFactor n lam i) :
    ((∏ i : Fin (r + 1), scale i) /
      (∏ i : Fin (r + 1), scaleZero i)) *
      (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
        Weyl.pairFactor n lam i j) =
      Weyl.dimension n lam := by
  classical
  rw [← Finset.prod_div_distrib]
  simp_rw [hrow]
  rw [pairProduct_Ioi_eq_conditional]
  rfl

theorem orthogonalRowScale_zero_ne_zero
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (i : Fin (r + 1)) :
    orthogonalRowScale n (fun _ : Fin (r + 1) => 0) i ≠ 0 := by
  have hnpos : 0 < n := by omega
  have hbin :
      0 < (((n + Weyl.rowTail i - 1).choose
        (Weyl.rowTail i) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos
      (show Weyl.rowTail i ≤ n + Weyl.rowTail i - 1 by omega)
  have hlinear :
      0 < (n : ℝ) - 2 * ((i.val + 1 : ℕ) : ℝ) :=
    Weyl.linearDenominator_pos hn i
  have hrising :
      0 < risingFactorProduct (Weyl.tailLength n r i)
        (2 * r + 2) :=
    risingFactorProduct_pos _ _
  unfold orthogonalRowScale
  simp only [orthogonalCompleteSymmetricCoefficient_nat,
    Nat.cast_zero, zero_add, add_zero, mul_zero]
  exact (div_pos (mul_pos hbin hlinear) hrising).ne'

theorem orthogonalJacobiTrudiDimension_eq_weyl_of_row_evaluation
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (p : Fin (r + 1) → Polynomial ℝ)
    (hdegree : ∀ j, (p j).natDegree ≤ r)
    (hentry : ∀ i j : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam i j : ℤ) : ℝ) =
        orthogonalRowScale n lam i *
          (p j).eval (shiftedSquare n lam i))
    (hentryZero : ∀ i j : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n
        (fun _ : Fin (r + 1) => 0) i j : ℤ) : ℝ) =
        orthogonalRowScale n (fun _ : Fin (r + 1) => 0) i *
          (p j).eval
            (shiftedSquare n (fun _ : Fin (r + 1) => 0) i)) :
    (orthogonalJacobiTrudiDimension n lam : ℝ) =
      Weyl.dimension n lam := by
  classical
  let zeroWeight : Fin (r + 1) → ℕ := fun _ => 0
  have hdet (mu : Fin (r + 1) → ℕ)
      (hmu : ∀ i j : Fin (r + 1),
        ((orthogonalJacobiTrudiMatrix n mu i j : ℤ) : ℝ) =
          orthogonalRowScale n mu i *
            (p j).eval (shiftedSquare n mu i)) :
      (orthogonalJacobiTrudiDimension n mu : ℝ) =
        Matrix.det (fun i j : Fin (r + 1) =>
          orthogonalRowScale n mu i *
            (p j).eval (shiftedSquare n mu i)) := by
    unfold orthogonalJacobiTrudiDimension
    rw [Int.cast_det]
    congr 1
    funext i j
    exact hmu i j
  have hzero : Matrix.det (fun i j : Fin (r + 1) =>
      orthogonalRowScale n zeroWeight i *
        (p j).eval (shiftedSquare n zeroWeight i)) = 1 := by
    calc
      _ = (orthogonalJacobiTrudiDimension n zeroWeight : ℝ) :=
        (hdet zeroWeight (by simpa only [zeroWeight] using hentryZero)).symm
      _ = 1 := by rw [orthogonalJacobiTrudiDimension_zero]; norm_num
  calc
    (orthogonalJacobiTrudiDimension n lam : ℝ) =
        Matrix.det (fun i j : Fin (r + 1) =>
          orthogonalRowScale n lam i *
            (p j).eval (shiftedSquare n lam i)) :=
      hdet lam hentry
    _ = ((∏ i : Fin (r + 1), orthogonalRowScale n lam i) /
          (∏ i : Fin (r + 1), orthogonalRowScale n zeroWeight i)) *
          ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
            Weyl.pairFactor n lam i j :=
      det_rowScaled_shiftedSquare_evaluation_eq hn lam p hdegree
        (orthogonalRowScale n lam) (orthogonalRowScale n zeroWeight)
        (by intro i; exact orthogonalRowScale_zero_ne_zero hn i)
        (by simpa only [zeroWeight] using hzero)
    _ = Weyl.dimension n lam :=
      rowRatio_mul_pairProduct_eq_weyl_dimension lam
        (orthogonalRowScale n lam)
        (orthogonalRowScale n zeroWeight)
        (fun i => by
          simpa only [zeroWeight] using orthogonalRowScale_div_zero_eq_rowFactor hn lam i)

theorem orthogonalJacobiTrudiMatrix_reflected_commonDenominator_real
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (i j : Fin (r + 1)) :
    (∏ q ∈ Finset.range (2 * r + 2),
        ((n : ℝ) + (lam i : ℝ) - (i.val : ℝ) + (r : ℝ) - 1 -
          (q : ℝ))) *
        (orthogonalJacobiTrudiMatrix n lam i j : ℝ) =
      (orthogonalCompleteSymmetricCoefficient n
          ((lam i + Weyl.rowTail i : ℕ) : ℤ) : ℝ) *
        ((∏ q ∈ Finset.range (r - j.val),
            ((lam i : ℝ) - (i.val : ℝ) + (r : ℝ) - (q : ℝ))) *
          (∏ q ∈ Finset.range (2 * r + 2 - (r - j.val)),
            ((n : ℝ) + (lam i : ℝ) - (i.val : ℝ) +
              (r : ℝ) - 1 - ((r - j.val + q : ℕ) : ℝ))) -
         (∏ q ∈ Finset.range (r + j.val + 2),
            ((lam i : ℝ) - (i.val : ℝ) + (r : ℝ) - (q : ℝ))) *
          (∏ q ∈ Finset.range (2 * r + 2 - (r + j.val + 2)),
            ((n : ℝ) + (lam i : ℝ) - (i.val : ℝ) +
              (r : ℝ) - 1 - ((r + j.val + 2 + q : ℕ) : ℝ)))) := by
  let z : ℤ := (lam i : ℤ) - (i.val : ℤ)
  have hj : j.val ≤ r := by have := j.isLt; omega
  have hanchor :
      z + (r : ℤ) = ((lam i + Weyl.rowTail i : ℕ) : ℤ) := by
    dsimp [z]
    unfold Weyl.rowTail
    have hi := i.isLt
    omega
  have hentry :
      orthogonalCompleteSymmetricCoefficient n (z + (j.val : ℤ)) -
          orthogonalCompleteSymmetricCoefficient n
            (z - (j.val : ℤ) - 2) =
        orthogonalJacobiTrudiMatrix n lam i j := by
    simp only [orthogonalJacobiTrudiMatrix, z]
  have h := orthogonalCompleteSymmetricCoefficient_reflected_commonDenominator
    (show 0 < n by omega) z r j.val hj
  have hreal :
      (∏ q ∈ Finset.range (2 * r + 2),
        ((n : ℝ) + (z : ℝ) + (r : ℝ) - 1 - (q : ℝ))) *
          ((orthogonalCompleteSymmetricCoefficient n (z + (j.val : ℤ)) -
            orthogonalCompleteSymmetricCoefficient n
              (z - (j.val : ℤ) - 2) : ℤ) : ℝ) =
        (orthogonalCompleteSymmetricCoefficient n (z + (r : ℤ)) : ℝ) *
          ((∏ q ∈ Finset.range (r - j.val),
              ((z : ℝ) + (r : ℝ) - (q : ℝ))) *
            (∏ q ∈ Finset.range (2 * r + 2 - (r - j.val)),
              ((n : ℝ) + (z : ℝ) + (r : ℝ) - 1 -
                ((r - j.val + q : ℕ) : ℝ))) -
           (∏ q ∈ Finset.range (r + j.val + 2),
              ((z : ℝ) + (r : ℝ) - (q : ℝ))) *
            (∏ q ∈ Finset.range (2 * r + 2 - (r + j.val + 2)),
              ((n : ℝ) + (z : ℝ) + (r : ℝ) - 1 -
                ((r + j.val + 2 + q : ℕ) : ℝ)))) := by
    exact_mod_cast h
  rw [hanchor, hentry] at hreal
  have hz : (z : ℝ) = (lam i : ℝ) - (i.val : ℝ) := by
    dsimp [z]
    push_cast
    rfl
  rw [hz] at hreal
  simpa only [sub_eq_add_neg, add_assoc] using hreal

theorem orthogonalJacobiTrudiMatrix_entry_of_factored_transport
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (i j : Fin (r + 1))
    (hfact :
      (∏ a ∈ Finset.range (2 * r + 2),
        ((n : ℝ) + (lam i : ℝ) - (i.val : ℝ) + (r : ℝ) - 1 -
          (a : ℝ))) *
        (orthogonalJacobiTrudiMatrix n lam i j : ℝ) =
      (orthogonalCompleteSymmetricCoefficient n
          ((lam i + Weyl.rowTail i : ℕ) : ℤ) : ℝ) *
        (2 * (lam i : ℝ) + (n : ℝ) -
          2 * ((i.val + 1 : ℕ) : ℝ)) *
        (commonInvariantPolynomial (n : ℝ) r (r - j.val) *
          (middlePolynomials (n : ℝ) j.val).1).eval
            (shiftedSquare n lam i)) :
    (orthogonalJacobiTrudiMatrix n lam i j : ℝ) =
      orthogonalRowScale n lam i *
        (commonInvariantPolynomial (n : ℝ) r (r - j.val) *
          (middlePolynomials (n : ℝ) j.val).1).eval
            (shiftedSquare n lam i) := by
  rw [descendingRowFactors_eq_risingFactorProduct hn lam i] at hfact
  have hD :
      risingFactorProduct (Weyl.tailLength n r i + lam i)
        (2 * r + 2) ≠ 0 :=
    (risingFactorProduct_pos _ _).ne'
  unfold orthogonalRowScale
  field_simp [hD]
  nlinarith [hfact]

private def orthogonalReflectedBracket (n z : ℝ) (r j : ℕ) : ℝ :=
  ((∏ q ∈ Finset.range (r - j),
      (z + (r : ℝ) - (q : ℝ))) *
    (∏ q ∈ Finset.range (2 * r + 2 - (r - j)),
      (n + z + (r : ℝ) - 1 - ((r - j + q : ℕ) : ℝ))) -
   (∏ q ∈ Finset.range (r + j + 2),
      (z + (r : ℝ) - (q : ℝ))) *
    (∏ q ∈ Finset.range (2 * r + 2 - (r + j + 2)),
      (n + z + (r : ℝ) - 1 - ((r + j + 2 + q : ℕ) : ℝ))))

theorem orthogonalReflectedBracket_eq_commonPolynomial
    (n z : ℝ) (r j : ℕ) (hj : j ≤ r) :
    orthogonalReflectedBracket n z r j =
      (commonInvariantPolynomial n r (r - j)).eval
        (z * (z + n - 2)) *
      ((middleProducts n z j).1 - (middleProducts n z j).2) := by
  exact orthogonal_reflected_prefix_suffix_eq_invariant_middle n z r j hj

theorem orthogonalJacobiTrudiMatrix_entry_of_real_transport
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (i j : Fin (r + 1))
    (htransport :
      (∏ a ∈ Finset.range (2 * r + 2),
        ((n : ℝ) + (lam i : ℝ) - (i.val : ℝ) + (r : ℝ) - 1 -
          (a : ℝ))) *
        (orthogonalJacobiTrudiMatrix n lam i j : ℝ) =
      (orthogonalCompleteSymmetricCoefficient n
          ((lam i + Weyl.rowTail i : ℕ) : ℤ) : ℝ) *
        orthogonalReflectedBracket (n : ℝ)
          ((lam i : ℝ) - (i.val : ℝ)) r j.val) :
    (orthogonalJacobiTrudiMatrix n lam i j : ℝ) =
      orthogonalRowScale n lam i *
        (commonInvariantPolynomial (n : ℝ) r (r - j.val) *
          (middlePolynomials (n : ℝ) j.val).1).eval
            (shiftedSquare n lam i) := by
  apply orthogonalJacobiTrudiMatrix_entry_of_factored_transport hn lam i j
  rw [orthogonalReflectedBracket_eq_commonPolynomial
    (n : ℝ) ((lam i : ℝ) - (i.val : ℝ)) r j.val
    (show j.val ≤ r by omega)] at htransport
  rw [(middleProducts_sub_add
    (n : ℝ) ((lam i : ℝ) - (i.val : ℝ)) j.val).1] at htransport
  have hz :
      ((lam i : ℝ) - (i.val : ℝ)) *
        (((lam i : ℝ) - (i.val : ℝ)) + (n : ℝ) - 2) =
      shiftedSquare n lam i := rfl
  rw [hz] at htransport
  rw [Polynomial.eval_mul]
  convert htransport using 1 ; push_cast ; ring

theorem orthogonalJacobiTrudiMatrix_entry_eq_rowScale_columnPolynomial
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (i j : Fin (r + 1)) :
    (orthogonalJacobiTrudiMatrix n lam i j : ℝ) =
      orthogonalRowScale n lam i *
        (orthogonalColumnPolynomial (n : ℝ) r j).eval
          (shiftedSquare n lam i) := by
  unfold orthogonalColumnPolynomial
  apply orthogonalJacobiTrudiMatrix_entry_of_real_transport hn lam i j
  have h := orthogonalJacobiTrudiMatrix_reflected_commonDenominator_real
    hn lam i j
  simpa only [orthogonalReflectedBracket, sub_eq_add_neg, add_assoc] using h

theorem orthogonalJacobiTrudiDimension_eq_weyl
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) :
    (orthogonalJacobiTrudiDimension n lam : ℝ) =
      Weyl.dimension n lam := by
  apply orthogonalJacobiTrudiDimension_eq_weyl_of_row_evaluation
    hn lam (orthogonalColumnPolynomial (n : ℝ) r)
  · intro j
    exact orthogonalColumnPolynomial_natDegree_le (n : ℝ) r j
  · intro i j
    exact orthogonalJacobiTrudiMatrix_entry_eq_rowScale_columnPolynomial
      hn lam i j
  · intro i j
    exact orthogonalJacobiTrudiMatrix_entry_eq_rowScale_columnPolynomial
      hn (fun _ : Fin (r + 1) => 0) i j

end HigherWeylAllRankJacobiTrudiWeylEvaluation

end

section


namespace HigherWeylAllRankAlternatingCharacter

open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherWeylGramOrthogonalJacobiTrudi
open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation

theorem weyl_dimension_eq_alternatingGramKoszulCoefficient
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) :
    Weyl.dimension n lam =
      (alternatingGramKoszulCoefficient n lam : ℝ) := by
  calc
    Weyl.dimension n lam =
        (orthogonalJacobiTrudiDimension n lam : ℝ) :=
      (orthogonalJacobiTrudiDimension_eq_weyl hn lam).symm
    _ = (alternatingGramKoszulCoefficient n lam : ℝ) := by
      rw [alternatingGramKoszulCoefficient_eq_orthogonalJacobiTrudiDimension]

end HigherWeylAllRankAlternatingCharacter

end

namespace HigherHarmonicYoung

section


open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherWeylAllRankAlternatingCharacter
open MetricCodes.Spherical.HigherHarmonicYoung.UniversalBGGRootComplex

theorem weyl_dimension_eq_finrank_harmonicYoung_of_rootExact
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (d : ∀ k,
      RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
        RootJointHarmonicChain n lam k)
    (hexact : ∀ k, k < Fintype.card (PositiveRoot r) →
      LinearMap.range (d (k + 1)) = LinearMap.ker (d k))
    (hzero :
      Module.finrank ℝ
          (LinearMap.ker (rootDegreeZeroPositiveCochain n lam)) +
        Module.finrank ℝ (LinearMap.range (d 0)) =
          Module.finrank ℝ (RootJointHarmonicChain n lam 0)) :
    Weyl.dimension n lam =
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℝ) := by
  have hbgg :
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℤ) =
        alternatingJointHarmonicWeightDimension n lam := by
    calc
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℤ) =
          rootExteriorEulerCharacteristic n lam :=
        finrank_harmonicYoung_eq_rootExteriorEulerCharacteristic_of_rootExact
          lam d hexact hzero
      _ = rootFamilyEulerCharacteristic n lam :=
        rootExteriorEulerCharacteristic_eq_rootFamilyEulerCharacteristic lam
      _ = alternatingJointHarmonicWeightDimension n lam :=
        rootFamilyEulerCharacteristic_eq_alternatingJointHarmonicWeightDimension lam
  have hgram : alternatingJointHarmonicWeightDimension n lam =
      alternatingGramKoszulCoefficient n lam :=
    alternatingJointHarmonicWeightDimension_eq_alternatingGramKoszul_of_stable
      (by omega) lam
  calc
    Weyl.dimension n lam =
        (alternatingGramKoszulCoefficient n lam : ℝ) :=
      weyl_dimension_eq_alternatingGramKoszulCoefficient hn lam
    _ = (alternatingJointHarmonicWeightDimension n lam : ℝ) := by
      rw [hgram]
    _ = (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℝ) := by
      exact_mod_cast hbgg.symm

theorem weyl_dimension_eq_finrank_harmonicYoung_of_chevalleyExact
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hexact : ∀ k, k < Fintype.card (PositiveRoot r) →
      LinearMap.range
          (weightedChevalleyEilenbergDifferential n lam (k + 1)) =
        LinearMap.ker
          (weightedChevalleyEilenbergDifferential n lam k))
    (hzero :
      Module.finrank ℝ
          (LinearMap.ker (rootDegreeZeroPositiveCochain n lam)) +
        Module.finrank ℝ
          (LinearMap.range
            (weightedChevalleyEilenbergDifferential n lam 0)) =
          Module.finrank ℝ (RootJointHarmonicChain n lam 0)) :
    Weyl.dimension n lam =
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℝ) :=
  weyl_dimension_eq_finrank_harmonicYoung_of_rootExact hn lam
    (weightedChevalleyEilenbergDifferential n lam) hexact hzero

theorem weyl_dimension_eq_finrank_harmonicYoung_of_chevalleyExactness
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hexact : ∀ k, k < Fintype.card (PositiveRoot r) →
      LinearMap.range
          (weightedChevalleyEilenbergDifferential n lam (k + 1)) =
        LinearMap.ker
          (weightedChevalleyEilenbergDifferential n lam k)) :
    Weyl.dimension n lam =
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℝ) :=
  weyl_dimension_eq_finrank_harmonicYoung_of_chevalleyExact hn lam hexact
    (rootDegreeZeroPositiveCochain_finrank_ker_add_finrank_ce_range lam)

end

namespace UniversalBGGRootComplex

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem weightedExteriorActionDifferential_apply_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam (k + 1))
    (T : AdmissibleRootWedge lam k) :
    (((weightedExteriorActionDifferential n lam k p T).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam T)) :
      PolynomialSpace r n) =
        ∑ α : PositiveRoot r,
          if hα : α ∈ T.val.val then 0
          else if hadm : ∀ i,
              0 ≤ signedRootWeight lam (insert α T.val.val) i then
            realExteriorRootSign (insert α T.val.val) α •
              polarization r n (positiveRootSecond α) (positiveRootFirst α)
                (((p (rootAdmissibleInsert lam T α hα hadm)).val :
                  youngMultihomogeneousSubmodule n
                    (rootWedgeWeight lam
                      (rootAdmissibleInsert lam T α hα hadm))) :
                  PolynomialSpace r n)
          else 0 := by
  classical
  rw [weightedExteriorActionDifferential_apply]
  simp only [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with hα hadm
  · simp only [ZeroMemClass.coe_zero]
  · simp only [Submodule.coe_smul]
    rw [weightedExteriorRootEdge_coe]
  · simp only [ZeroMemClass.coe_zero]

end

section


open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BGGRootComplex

/-- The positive root upper operator used in the spherical-code argument. -/
def positiveRootUpperOperator {r : ℕ} (n : ℕ) (α : PositiveRoot r) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  polarization r n (positiveRootFirst α) (positiveRootSecond α)

@[simp] theorem positiveRootUpperOperator_apply {r n : ℕ}
    (α : PositiveRoot r) (p : PolynomialSpace r n) :
    positiveRootUpperOperator n α p =
      polarization r n (positiveRootFirst α) (positiveRootSecond α) p := rfl

theorem positiveRootUpper_lower_commutator_apply {r n : ℕ}
    (α β : PositiveRoot r) (p : PolynomialSpace r n) :
    positiveRootUpperOperator n α (positiveRootOperator n β p) -
        positiveRootOperator n β (positiveRootUpperOperator n α p) =
      (if positiveRootSecond α = positiveRootSecond β then
        polarization r n (positiveRootFirst α) (positiveRootFirst β) p
      else 0) -
        (if positiveRootFirst β = positiveRootFirst α then
          polarization r n (positiveRootSecond β) (positiveRootSecond α) p
        else 0) := by
  have h := polarization_polarization_commutator
    (positiveRootFirst α) (positiveRootSecond α)
    (positiveRootSecond β) (positiveRootFirst β) p
  change
    polarization r n (positiveRootFirst α) (positiveRootSecond α)
        (polarization r n (positiveRootSecond β) (positiveRootFirst β) p) -
      polarization r n (positiveRootSecond β) (positiveRootFirst β)
        (polarization r n (positiveRootFirst α) (positiveRootSecond α) p) = _
  rw [h]
  abel

theorem positiveRootUpper_lower_commutator {r n : ℕ}
    (α β : PositiveRoot r) :
    (positiveRootUpperOperator n α).comp (positiveRootOperator n β) -
        (positiveRootOperator n β).comp (positiveRootUpperOperator n α) =
      (if positiveRootSecond α = positiveRootSecond β then
        polarization r n (positiveRootFirst α) (positiveRootFirst β)
      else 0) -
        (if positiveRootFirst β = positiveRootFirst α then
          polarization r n (positiveRootSecond β) (positiveRootSecond α)
      else 0) := by
  classical
  apply LinearMap.ext
  intro p
  by_cases hsecond : positiveRootSecond α = positiveRootSecond β
  · by_cases hfirst : positiveRootFirst β = positiveRootFirst α
    · simpa only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      positiveRootOperator_apply,
        polarization_apply, map_sum, positiveRootUpperOperator_apply, hsecond,
          Derivation.leibniz, smul_eq_mul,
        MvPolynomial.pderiv_X, ↓reduceIte, hfirst, polarization_self, rowEuler_apply] using
        positiveRootUpper_lower_commutator_apply α β p
    · simpa only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
        positiveRootOperator_apply, polarization_apply, map_sum, positiveRootUpperOperator_apply,
        hsecond, Derivation.leibniz, smul_eq_mul, MvPolynomial.pderiv_X, ↓reduceIte, hfirst,
        sub_zero] using positiveRootUpper_lower_commutator_apply α β p
  · by_cases hfirst : positiveRootFirst β = positiveRootFirst α
    · simpa only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      positiveRootOperator_apply,
        polarization_apply, map_sum, positiveRootUpperOperator_apply, Derivation.leibniz,
          smul_eq_mul,
        MvPolynomial.pderiv_X, hsecond, ↓reduceIte, hfirst, zero_sub, LinearMap.neg_apply] using
        positiveRootUpper_lower_commutator_apply α β p
    · simpa only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      positiveRootOperator_apply,
        polarization_apply, map_sum, positiveRootUpperOperator_apply, Derivation.leibniz,
          smul_eq_mul,
        MvPolynomial.pderiv_X, hsecond, ↓reduceIte, hfirst, sub_self, LinearMap.zero_apply] using
        positiveRootUpper_lower_commutator_apply α β p

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem positiveRoot_sum_sub_smul {r : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (f g : PositiveRoot r → ℝ) (v : PositiveRoot r → V) :
    (∑ γ : PositiveRoot r, (f γ - g γ) • v γ) =
      (∑ γ : PositiveRoot r, f γ • v γ) -
        (∑ γ : PositiveRoot r, g γ • v γ) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro γ _
  exact sub_smul (f γ) (g γ) (v γ)

theorem rootStructureConstant_upper_cross {r : ℕ}
    (α β γ : PositiveRoot r) :
    rootStructureConstant β γ α =
      (if positiveRootSecond α = positiveRootSecond β ∧
          γ.val = (positiveRootFirst α, positiveRootFirst β)
        then (1 : ℝ) else 0) -
      (if positiveRootFirst α = positiveRootFirst β ∧
          γ.val = (positiveRootSecond β, positiveRootSecond α)
        then (1 : ℝ) else 0) := by
  unfold rootStructureConstant positiveRootFirst positiveRootSecond
  have hfirst :
      (β.val.1 = γ.val.2 ∧ α.val = (γ.val.1, β.val.2)) ↔
        (α.val.2 = β.val.2 ∧ γ.val = (α.val.1, β.val.1)) := by
    simp only [Prod.ext_iff]
    aesop
  have hsecond :
      (γ.val.1 = β.val.2 ∧ α.val = (β.val.1, γ.val.2)) ↔
        (α.val.1 = β.val.1 ∧ γ.val = (β.val.2, α.val.2)) := by
    simp only [Prod.ext_iff]
    aesop
  simp only [hfirst, hsecond]

theorem rootStructureConstant_lower_cross {r : ℕ}
    (α β γ : PositiveRoot r) :
    rootStructureConstant α γ β =
      (if positiveRootSecond α = positiveRootSecond β ∧
          γ.val = (positiveRootFirst β, positiveRootFirst α)
        then (1 : ℝ) else 0) -
      (if positiveRootFirst α = positiveRootFirst β ∧
          γ.val = (positiveRootSecond α, positiveRootSecond β)
        then (1 : ℝ) else 0) := by
  unfold rootStructureConstant positiveRootFirst positiveRootSecond
  have hfirst :
      (α.val.1 = γ.val.2 ∧ β.val = (γ.val.1, α.val.2)) ↔
        (α.val.2 = β.val.2 ∧ γ.val = (β.val.1, α.val.1)) := by
    simp only [Prod.ext_iff]
    aesop
  have hsecond :
      (γ.val.1 = α.val.2 ∧ β.val = (α.val.1, γ.val.2)) ↔
        (α.val.1 = β.val.1 ∧ γ.val = (α.val.2, β.val.2)) := by
    simp only [Prod.ext_iff]
    aesop
  simp only [hfirst, hsecond]

theorem sum_positiveRootUpperOperator_eq_polarization_of_pair
    {r n : ℕ} (i j : Fin (r + 1)) :
    (∑ γ : PositiveRoot r,
      (if γ.val = (i, j) then (1 : ℝ) else 0) •
        positiveRootUpperOperator n γ) =
      if i < j then polarization r n i j else 0 := by
  classical
  by_cases hij : i < j
  · let γ₀ : PositiveRoot r := ⟨(i, j), hij⟩
    have hγ : ∀ γ : PositiveRoot r,
        γ.val = (i, j) ↔ γ = γ₀ := by
      intro γ
      constructor
      · intro h
        apply Subtype.ext
        exact h
      · intro h
        subst γ
        rfl
    simp_rw [hγ]
    simp only [positiveRootUpperOperator, positiveRootFirst, positiveRootSecond, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hij, γ₀]
  · have hγ : ∀ γ : PositiveRoot r, γ.val ≠ (i, j) := by
      intro γ heq
      apply hij
      simpa only [heq] using γ.property
    simp only [hγ, ↓reduceIte, zero_smul, Finset.sum_const_zero, hij]

theorem sum_positiveRootOperator_eq_polarization_of_pair
    {r n : ℕ} (i j : Fin (r + 1)) :
    (∑ γ : PositiveRoot r,
      (if γ.val = (i, j) then (1 : ℝ) else 0) •
        positiveRootOperator n γ) =
      if i < j then polarization r n j i else 0 := by
  classical
  by_cases hij : i < j
  · let γ₀ : PositiveRoot r := ⟨(i, j), hij⟩
    have hγ : ∀ γ : PositiveRoot r,
        γ.val = (i, j) ↔ γ = γ₀ := by
      intro γ
      constructor
      · intro h
        apply Subtype.ext
        exact h
      · intro h
        subst γ
        rfl
    simp_rw [hγ]
    simp only [positiveRootOperator, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, hij, γ₀]
  · have hγ : ∀ γ : PositiveRoot r, γ.val ≠ (i, j) := by
      intro γ heq
      apply hij
      simpa only [heq] using γ.property
    simp only [hγ, ↓reduceIte, zero_smul, Finset.sum_const_zero, hij]

theorem rootStructureConstant_upper_cross_sum {r n : ℕ}
    (α β : PositiveRoot r) :
    (∑ γ : PositiveRoot r,
      rootStructureConstant β γ α • positiveRootUpperOperator n γ) =
      (if positiveRootSecond α = positiveRootSecond β ∧
          positiveRootFirst α < positiveRootFirst β then
        polarization r n (positiveRootFirst α) (positiveRootFirst β)
      else 0) -
      (if positiveRootFirst α = positiveRootFirst β ∧
          positiveRootSecond β < positiveRootSecond α then
        polarization r n (positiveRootSecond β) (positiveRootSecond α)
      else 0) := by
  classical
  simp_rw [rootStructureConstant_upper_cross]
  rw [positiveRoot_sum_sub_smul
    (fun γ : PositiveRoot r =>
      if positiveRootSecond α = positiveRootSecond β ∧
        γ.val = (positiveRootFirst α, positiveRootFirst β)
      then (1 : ℝ) else 0)
    (fun γ : PositiveRoot r =>
      if positiveRootFirst α = positiveRootFirst β ∧
        γ.val = (positiveRootSecond β, positiveRootSecond α)
      then (1 : ℝ) else 0)
    (fun γ : PositiveRoot r => positiveRootUpperOperator n γ)]
  congr 1
  · by_cases h : positiveRootSecond α = positiveRootSecond β
    · simp only [h, true_and]
      rw [sum_positiveRootUpperOperator_eq_polarization_of_pair]
    · simp only [h, false_and, ↓reduceIte, zero_smul, Finset.sum_const_zero]
  · by_cases h : positiveRootFirst α = positiveRootFirst β
    · simp only [h, true_and]
      rw [sum_positiveRootUpperOperator_eq_polarization_of_pair]
    · simp only [h, false_and, ↓reduceIte, zero_smul, Finset.sum_const_zero]

theorem rootStructureConstant_lower_cross_sum {r n : ℕ}
    (α β : PositiveRoot r) :
    (∑ γ : PositiveRoot r,
      rootStructureConstant α γ β • positiveRootOperator n γ) =
      (if positiveRootSecond α = positiveRootSecond β ∧
          positiveRootFirst β < positiveRootFirst α then
        polarization r n (positiveRootFirst α) (positiveRootFirst β)
      else 0) -
      (if positiveRootFirst α = positiveRootFirst β ∧
          positiveRootSecond α < positiveRootSecond β then
        polarization r n (positiveRootSecond β) (positiveRootSecond α)
      else 0) := by
  classical
  simp_rw [rootStructureConstant_lower_cross]
  rw [positiveRoot_sum_sub_smul
    (fun γ : PositiveRoot r =>
      if positiveRootSecond α = positiveRootSecond β ∧
        γ.val = (positiveRootFirst β, positiveRootFirst α)
      then (1 : ℝ) else 0)
    (fun γ : PositiveRoot r =>
      if positiveRootFirst α = positiveRootFirst β ∧
        γ.val = (positiveRootSecond α, positiveRootSecond β)
      then (1 : ℝ) else 0)
    (fun γ : PositiveRoot r => positiveRootOperator n γ)]
  congr 1
  · by_cases h : positiveRootSecond α = positiveRootSecond β
    · simp only [h, true_and]
      rw [sum_positiveRootOperator_eq_polarization_of_pair]
    · simp only [h, false_and, ↓reduceIte, zero_smul, Finset.sum_const_zero]
  · by_cases h : positiveRootFirst α = positiveRootFirst β
    · simp only [h, true_and]
      rw [sum_positiveRootOperator_eq_polarization_of_pair]
    · simp only [h, false_and, ↓reduceIte, zero_smul, Finset.sum_const_zero]

private def positiveRootCartanOperator {r : ℕ} (n : ℕ) (α : PositiveRoot r) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  polarization r n (positiveRootFirst α) (positiveRootFirst α) -
    polarization r n (positiveRootSecond α) (positiveRootSecond α)

theorem positiveRootUpper_lower_commutator_eq_cartan_add_bracket
    {r n : ℕ} (α β : PositiveRoot r) :
    (positiveRootUpperOperator n α).comp (positiveRootOperator n β) -
        (positiveRootOperator n β).comp (positiveRootUpperOperator n α) =
      (if α = β then positiveRootCartanOperator n α else 0) +
        (∑ γ : PositiveRoot r,
          rootStructureConstant β γ α • positiveRootUpperOperator n γ) +
        (∑ γ : PositiveRoot r,
          rootStructureConstant α γ β • positiveRootOperator n γ) := by
  rw [positiveRootUpper_lower_commutator,
    rootStructureConstant_upper_cross_sum,
    rootStructureConstant_lower_cross_sum]
  by_cases hsecond : positiveRootSecond α = positiveRootSecond β
  · by_cases hfirst : positiveRootFirst α = positiveRootFirst β
    · have heq : α = β := by
        apply Subtype.ext
        apply Prod.ext
        · exact hfirst
        · exact hsecond
      subst β
      simp only [↓reduceIte, polarization_self, positiveRootCartanOperator, lt_self_iff_false,
        and_false, sub_self, add_zero]
    · have hne : α ≠ β := by
        intro h
        exact hfirst (congrArg positiveRootFirst h)
      rcases lt_or_gt_of_ne hfirst with hlt | hgt
      · simp only [hsecond, ↓reduceIte, (ne_of_lt hlt).symm, sub_zero, hne, hlt, and_self, hfirst,
          lt_self_iff_false, zero_add, hlt.not_gt, and_false, sub_self, add_zero]
      · simp only [hsecond, ↓reduceIte, ne_of_lt hgt, sub_zero, hne, hgt.not_gt, and_false, hfirst,
          lt_self_iff_false, and_self, sub_self, add_zero, hgt, zero_add]
  · by_cases hfirst : positiveRootFirst α = positiveRootFirst β
    · have hne : α ≠ β := by
        intro h
        exact hsecond (congrArg positiveRootSecond h)
      rcases lt_or_gt_of_ne hsecond with hlt | hgt
      · simp only [hsecond, ↓reduceIte, hfirst, zero_sub, hne, lt_self_iff_false, and_self,
          hlt.not_gt, and_false, sub_self, add_zero, hlt, zero_add]
      · simp only [hsecond, ↓reduceIte, hfirst, zero_sub, hne, lt_self_iff_false, and_self, hgt,
          zero_add, hgt.not_gt, and_false, sub_self, add_zero]
    · have hne : α ≠ β := by
        intro h
        exact hfirst (congrArg positiveRootFirst h)
      simp only [hsecond, ↓reduceIte, Ne.symm hfirst, sub_self, hne, false_and, hfirst, add_zero]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The root admissible swap used in the spherical-code argument. -/
def rootAdmissibleSwap {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i) :
    AdmissibleRootWedge lam k := by
  refine ⟨⟨insert β (S.val.val.erase α), ?_⟩, hadm⟩
  have hβ' : β ∉ S.val.val.erase α := by
    intro h
    exact hβ (Finset.mem_of_mem_erase h)
  have hk : 0 < k := by
    rw [← S.val.property]
    exact Finset.card_pos.mpr ⟨α, hα⟩
  simp only [hβ', not_false_eq_true, Finset.card_insert_of_notMem, Finset.card_erase_of_mem hα,
    S.val.property, Nat.sub_add_cancel hk]

theorem signedRootWeight_admissibleSwap {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (i : Fin (r + 1)) :
    signedRootWeight lam
        (rootAdmissibleSwap lam S α β hα hβ hadm).val.val i =
      signedRootWeight lam S.val.val i - rootCharge α i +
        rootCharge β i := by
  change signedRootWeight lam (insert β (S.val.val.erase α)) i = _
  rw [signedRootWeight_insert lam (S.val.val.erase α) β
    (fun h => hβ (Finset.mem_of_mem_erase h)) i,
    signedRootWeight_erase lam S.val.val α hα i]

theorem rootAdmissibleSwap_upper_charge {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β γ : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hstructure : rootStructureConstant β γ α ≠ 0)
    (i : Fin (r + 1)) :
    (rootWedgeWeight lam
      (rootAdmissibleSwap lam S α β hα hβ hadm) i : ℤ) +
      rootCharge γ i =
      (rootWedgeWeight lam S i : ℤ) := by
  rw [rootWedgeWeight_cast, rootWedgeWeight_cast,
    signedRootWeight_admissibleSwap]
  have hcharge :=
    rootCharge_eq_add_of_structureConstant_ne_zero β γ α hstructure i
  omega

theorem rootAdmissibleSwap_lower_charge {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β γ : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hstructure : rootStructureConstant α γ β ≠ 0)
    (i : Fin (r + 1)) :
    (rootWedgeWeight lam
      (rootAdmissibleSwap lam S α β hα hβ hadm) i : ℤ) -
      rootCharge γ i =
      (rootWedgeWeight lam S i : ℤ) := by
  rw [rootWedgeWeight_cast, rootWedgeWeight_cast,
    signedRootWeight_admissibleSwap]
  have hcharge :=
    rootCharge_eq_add_of_structureConstant_ne_zero α γ β hstructure i
  omega

theorem rootAdmissibleSwap_upper_second_pos {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β γ : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hstructure : rootStructureConstant β γ α ≠ 0) :
    0 < rootWedgeWeight lam
      (rootAdmissibleSwap lam S α β hα hβ hadm)
        (positiveRootSecond γ) := by
  have hcharge := rootAdmissibleSwap_upper_charge lam S α β γ hα hβ
    hadm hstructure (positiveRootSecond γ)
  rw [rootCharge_second] at hcharge
  omega

theorem rootAdmissibleSwap_lower_first_pos {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β γ : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hstructure : rootStructureConstant α γ β ≠ 0) :
    0 < rootWedgeWeight lam
      (rootAdmissibleSwap lam S α β hα hβ hadm)
        (positiveRootFirst γ) := by
  have hcharge := rootAdmissibleSwap_lower_charge lam S α β γ hα hβ
    hadm hstructure (positiveRootFirst γ)
  rw [rootCharge_first] at hcharge
  omega

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem weightedExteriorActionCoboundary_differential_apply_coe
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) :
    (((weightedExteriorActionCoboundary n lam k
      (weightedExteriorActionDifferential n lam k f) S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
        ∑ α : PositiveRoot r,
          if hα : α ∈ S.val.val then
            if herase : ∀ i,
                0 ≤ signedRootWeight lam (S.val.val.erase α) i then
              ∑ β : PositiveRoot r,
                if hβ : β ∈
                    (rootAdmissibleErase lam S α hα herase).val.val then 0
                else if hins : ∀ i,
                    0 ≤ signedRootWeight lam
                      (insert β
                        (rootAdmissibleErase lam S α hα herase).val.val) i
                  then
                    (realExteriorRootSign S.val.val α *
                      realExteriorRootSign
                        (insert β
                          (rootAdmissibleErase lam S α hα herase).val.val)
                        β) •
                      polarization r n
                        (positiveRootFirst α) (positiveRootSecond α)
                          (polarization r n
                            (positiveRootSecond β) (positiveRootFirst β)
                              (((f (rootAdmissibleInsert lam
                                (rootAdmissibleErase lam S α hα herase)
                                β hβ hins)).val :
                                youngMultihomogeneousSubmodule n
                                  (rootWedgeWeight lam
                                    (rootAdmissibleInsert lam
                                      (rootAdmissibleErase lam S α hα herase)
                                      β hβ hins))) :
                                PolynomialSpace r n))
                else 0
            else 0
          else 0 := by
  classical
  rw [weightedExteriorActionCoboundary_apply_erase_coe]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with hα herase
  · rw [weightedExteriorActionDifferential_apply_coe]
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro β _
    split_ifs with hβ hins
    · simp only [map_zero, smul_zero]
    · rw [map_smul, smul_smul]
    · simp only [map_zero, smul_zero]
  · rfl
  · rfl

theorem weightedExteriorActionDifferential_coboundary_apply_coe
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) :
    (((weightedExteriorActionDifferential n lam (k + 1)
      (weightedExteriorActionCoboundary n lam (k + 1) f) S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
        ∑ β : PositiveRoot r,
          if hβ : β ∈ S.val.val then 0
          else if hins : ∀ i,
              0 ≤ signedRootWeight lam (insert β S.val.val) i then
            ∑ α : PositiveRoot r,
              if hα : α ∈
                  (rootAdmissibleInsert lam S β hβ hins).val.val then
                if herase : ∀ i,
                    0 ≤ signedRootWeight lam
                      (((rootAdmissibleInsert lam S β hβ hins).val.val).erase α) i
                  then
                    (realExteriorRootSign (insert β S.val.val) β *
                      realExteriorRootSign
                        (rootAdmissibleInsert lam S β hβ hins).val.val α) •
                      polarization r n
                        (positiveRootSecond β) (positiveRootFirst β)
                          (polarization r n
                            (positiveRootFirst α) (positiveRootSecond α)
                              (((f (rootAdmissibleErase lam
                                (rootAdmissibleInsert lam S β hβ hins)
                                α hα herase)).val :
                                youngMultihomogeneousSubmodule n
                                  (rootWedgeWeight lam
                                    (rootAdmissibleErase lam
                                      (rootAdmissibleInsert lam S β hβ hins)
                                      α hα herase))) :
                                PolynomialSpace r n))
                else 0
              else 0
          else 0 := by
  classical
  rw [weightedExteriorActionDifferential_apply_coe]
  apply Finset.sum_congr rfl
  intro β _
  split_ifs with hβ hins
  · rfl
  · rw [weightedExteriorActionCoboundary_apply_erase_coe]
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs with hα herase
    · rw [map_smul, smul_smul]
    · simp only [map_zero, smul_zero]
    · simp only [map_zero, smul_zero]
  · rfl

private def rootPolynomialActionCoboundaryDifferentialIncidence
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1))
    (α β : PositiveRoot r) : PolynomialSpace r n :=
  if hα : α ∈ S.val.val then
    if herase : ∀ i,
        0 ≤ signedRootWeight lam (S.val.val.erase α) i then
      if hβ : β ∈
          (rootAdmissibleErase lam S α hα herase).val.val then 0
      else if hins : ∀ i,
          0 ≤ signedRootWeight lam
            (insert β
              (rootAdmissibleErase lam S α hα herase).val.val) i
        then
          (realExteriorRootSign S.val.val α *
            realExteriorRootSign
              (insert β
                (rootAdmissibleErase lam S α hα herase).val.val)
              β) •
            polarization r n
              (positiveRootFirst α) (positiveRootSecond α)
                (polarization r n
                  (positiveRootSecond β) (positiveRootFirst β)
                    (((f (rootAdmissibleInsert lam
                      (rootAdmissibleErase lam S α hα herase)
                      β hβ hins)).val :
                      youngMultihomogeneousSubmodule n
                        (rootWedgeWeight lam
                          (rootAdmissibleInsert lam
                            (rootAdmissibleErase lam S α hα herase)
                            β hβ hins))) :
                      PolynomialSpace r n))
      else 0
    else 0
  else 0

private def rootPolynomialActionDifferentialCoboundaryIncidence
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1))
    (β α : PositiveRoot r) : PolynomialSpace r n :=
  if hβ : β ∈ S.val.val then 0
  else if hins : ∀ i,
      0 ≤ signedRootWeight lam (insert β S.val.val) i then
    if hα : α ∈
        (rootAdmissibleInsert lam S β hβ hins).val.val then
      if herase : ∀ i,
          0 ≤ signedRootWeight lam
            (((rootAdmissibleInsert lam S β hβ hins).val.val).erase α) i
        then
          (realExteriorRootSign (insert β S.val.val) β *
            realExteriorRootSign
              (rootAdmissibleInsert lam S β hβ hins).val.val α) •
            polarization r n
              (positiveRootSecond β) (positiveRootFirst β)
                (polarization r n
                  (positiveRootFirst α) (positiveRootSecond α)
                    (((f (rootAdmissibleErase lam
                      (rootAdmissibleInsert lam S β hβ hins)
                      α hα herase)).val :
                      youngMultihomogeneousSubmodule n
                        (rootWedgeWeight lam
                          (rootAdmissibleErase lam
                            (rootAdmissibleInsert lam S β hβ hins)
                            α hα herase))) :
                      PolynomialSpace r n))
      else 0
    else 0
  else 0

theorem weightedExteriorActionCoboundary_differential_apply_coe_eq_incidence_sum
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) :
    (((weightedExteriorActionCoboundary n lam k
      (weightedExteriorActionDifferential n lam k f) S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
        ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
          rootPolynomialActionCoboundaryDifferentialIncidence lam f S α β := by
  classical
  rw [weightedExteriorActionCoboundary_differential_apply_coe]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with hα herase
  · apply Finset.sum_congr rfl
    intro β _
    simp only [rootPolynomialActionCoboundaryDifferentialIncidence,
      dite_eq_left hα, dite_eq_left herase]
  · simp only [rootPolynomialActionCoboundaryDifferentialIncidence, hα, ↓reduceDIte, herase,
      Finset.sum_const_zero]
  · simp only [rootPolynomialActionCoboundaryDifferentialIncidence, hα, ↓reduceDIte,
      Finset.sum_const_zero]

theorem weightedExteriorActionDifferential_coboundary_apply_coe_eq_incidence_sum
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) :
    (((weightedExteriorActionDifferential n lam (k + 1)
      (weightedExteriorActionCoboundary n lam (k + 1) f) S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
        ∑ β : PositiveRoot r, ∑ α : PositiveRoot r,
          rootPolynomialActionDifferentialCoboundaryIncidence lam f S β α := by
  classical
  rw [weightedExteriorActionDifferential_coboundary_apply_coe]
  apply Finset.sum_congr rfl
  intro β _
  split_ifs with hβ hins
  · simp only [rootPolynomialActionDifferentialCoboundaryIncidence, hβ, ↓reduceDIte,
      Finset.sum_const_zero]
  · apply Finset.sum_congr rfl
    intro α _
    simp only [rootPolynomialActionDifferentialCoboundaryIncidence,
      dite_eq_right hβ, dite_eq_left hins]
  · simp only [rootPolynomialActionDifferentialCoboundaryIncidence, hβ, ↓reduceDIte, hins,
      Finset.sum_const_zero]

theorem sum_rootIncidence_eq_diagonal_add_offDiagonal
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (F : ι → ι → M) :
    (∑ a : ι, ∑ b : ι, F a b) =
      (∑ a : ι, F a a) +
        ∑ a : ι, ∑ b : ι, if a = b then 0 else F a b := by
  classical
  calc
    (∑ a : ι, ∑ b : ι, F a b) =
        ∑ a : ι, ∑ b : ι,
          ((if a = b then F a b else 0) +
            (if a = b then 0 else F a b)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ = (∑ a : ι, ∑ b : ι, if a = b then F a b else 0) +
        (∑ a : ι, ∑ b : ι, if a = b then 0 else F a b) := by
      simp_rw [Finset.sum_add_distrib]
    _ = _ := by simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem sum_rootIncidence_pair_eq_diagonal_add_offDiagonal
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (F G : ι → ι → M) :
    (∑ a : ι, ∑ b : ι, F a b) +
        (∑ b : ι, ∑ a : ι, G b a) =
      (∑ a : ι, (F a a + G a a)) +
        ∑ a : ι, ∑ b : ι,
          if a = b then 0 else (F a b + G b a) := by
  classical
  rw [Finset.sum_comm (f := fun b a => G b a)]
  calc
    (∑ a : ι, ∑ b : ι, F a b) +
        (∑ a : ι, ∑ b : ι, G b a) =
      ∑ a : ι, ∑ b : ι, (F a b + G b a) := by
        simp_rw [Finset.sum_add_distrib]
    _ = _ := sum_rootIncidence_eq_diagonal_add_offDiagonal
      (fun a b => F a b + G b a)

private def rootPolynomialActionHodgeDiagonalIncidence
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) : PolynomialSpace r n :=
  ∑ α : PositiveRoot r,
    (rootPolynomialActionCoboundaryDifferentialIncidence lam f S α α +
      rootPolynomialActionDifferentialCoboundaryIncidence lam f S α α)

private def rootPolynomialActionHodgeOffDiagonalIncidence
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) : PolynomialSpace r n :=
  ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
    if α = β then 0
    else
      (rootPolynomialActionCoboundaryDifferentialIncidence lam f S α β +
        rootPolynomialActionDifferentialCoboundaryIncidence lam f S β α)

theorem weightedExteriorActionHodge_apply_coe_eq_diagonal_add_offDiagonal
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) :
    (((((weightedExteriorActionCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedExteriorActionCoboundary n lam (k + 1))) f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
      rootPolynomialActionHodgeDiagonalIncidence lam f S +
        rootPolynomialActionHodgeOffDiagonalIncidence lam f S := by
  rw [LinearMap.add_apply, Pi.add_apply, Submodule.coe_add, Submodule.coe_add,
    LinearMap.comp_apply, LinearMap.comp_apply]
  rw [weightedExteriorActionCoboundary_differential_apply_coe_eq_incidence_sum,
    weightedExteriorActionDifferential_coboundary_apply_coe_eq_incidence_sum]
  exact sum_rootIncidence_pair_eq_diagonal_add_offDiagonal
    (rootPolynomialActionCoboundaryDifferentialIncidence lam f S)
    (rootPolynomialActionDifferentialCoboundaryIncidence lam f S)

end

section


open MetricCodes.Spherical.HigherHarmonicYoung

theorem activeRootRaisedWeight_cast {r : ℕ}
    (μ : Fin (r + 1) → ℕ)
    (γ : ActivePositiveRoot μ)
    (i : Fin (r + 1)) :
    ((activeRootRaisedWeight μ γ i : ℕ) : ℤ) =
      (μ i : ℤ) + rootCharge γ.val i := by
  by_cases hfirst : i = positiveRootFirst γ.val
  · subst i
    have hne := positiveRootFirst_ne_second γ.val
    simp only [activeRootRaisedWeight, activeRootBaseWeight, ne_eq, hne, not_false_eq_true,
      Function.update_of_ne, Function.update_self, Nat.cast_add, Nat.cast_one, rootCharge,
      ↓reduceIte]
  · by_cases hsecond : i = positiveRootSecond γ.val
    · subst i
      have hne := (positiveRootFirst_ne_second γ.val).symm
      simp only [activeRootRaisedWeight, activeRootBaseWeight, ne_eq, hne, not_false_eq_true,
        Function.update_of_ne, Function.update_self, rootCharge, ↓reduceIte, Int.reduceNeg]
      exact Int.ofNat_sub (show 1 ≤ μ (positiveRootSecond γ.val) by
        exact γ.property)
    · simp only [activeRootRaisedWeight, activeRootBaseWeight, ne_eq, hfirst, not_false_eq_true,
        Function.update_of_ne, hsecond, rootCharge, ↓reduceIte, add_zero]

theorem rootSwapUpperStructureEdge_weight {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β γ : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hstructure : rootStructureConstant β γ α ≠ 0) :
    activeRootRaisedWeight
        (rootWedgeWeight lam (rootAdmissibleSwap lam S α β hα hβ hadm))
        ⟨γ, rootAdmissibleSwap_upper_second_pos lam S α β γ hα hβ
          hadm hstructure⟩ =
      rootWedgeWeight lam S := by
  funext i
  have hupper := rootAdmissibleSwap_upper_charge lam S α β γ
    hα hβ hadm hstructure i
  have hcast := activeRootRaisedWeight_cast
    (rootWedgeWeight lam (rootAdmissibleSwap lam S α β hα hβ hadm))
    (⟨γ, rootAdmissibleSwap_upper_second_pos lam S α β γ hα hβ
      hadm hstructure⟩ :
        ActivePositiveRoot
          (rootWedgeWeight lam
            (rootAdmissibleSwap lam S α β hα hβ hadm))) i
  exact_mod_cast hcast.trans hupper

theorem rootSwapLowerStructureEdge_weight {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β γ : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hstructure : rootStructureConstant α γ β ≠ 0) :
    lowerRootWeight
        (rootWedgeWeight lam
          (rootAdmissibleSwap lam S α β hα hβ hadm)) γ =
      rootWedgeWeight lam S := by
  funext i
  have hlower := rootAdmissibleSwap_lower_charge lam S α β γ
    hα hβ hadm hstructure i
  have hcast := lowerRootWeight_cast
    (rootWedgeWeight lam (rootAdmissibleSwap lam S α β hα hβ hadm)) γ
    (rootAdmissibleSwap_lower_first_pos lam S α β γ hα hβ hadm
      hstructure) i
  exact_mod_cast hcast.trans hlower

/-- The root swap upper structure edge used in the spherical-code argument. -/
def rootSwapUpperStructureEdge {r k : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β γ : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hstructure : rootStructureConstant β γ α ≠ 0) :
    JointHarmonicWeightSpace n
        (rootWedgeWeight lam
          (rootAdmissibleSwap lam S α β hα hβ hadm)) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) :=
  (jointHarmonicWeightCast n
    (activeRootRaisedWeight
      (rootWedgeWeight lam (rootAdmissibleSwap lam S α β hα hβ hadm))
      ⟨γ, rootAdmissibleSwap_upper_second_pos lam S α β γ hα hβ
        hadm hstructure⟩)
    (rootWedgeWeight lam S)
    (rootSwapUpperStructureEdge_weight lam S α β γ hα hβ hadm
      hstructure)).toLinearMap.comp
    (activePositiveRootRaise n
      (rootWedgeWeight lam (rootAdmissibleSwap lam S α β hα hβ hadm))
      ⟨γ, rootAdmissibleSwap_upper_second_pos lam S α β γ hα hβ
        hadm hstructure⟩)

private def rootSwapLowerStructureEdge {r k : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β γ : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hstructure : rootStructureConstant α γ β ≠ 0) :
    JointHarmonicWeightSpace n
        (rootWedgeWeight lam
          (rootAdmissibleSwap lam S α β hα hβ hadm)) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) :=
  (jointHarmonicWeightCast n
    (lowerRootWeight
      (rootWedgeWeight lam (rootAdmissibleSwap lam S α β hα hβ hadm)) γ)
    (rootWedgeWeight lam S)
    (rootSwapLowerStructureEdge_weight lam S α β γ hα hβ hadm
      hstructure)).toLinearMap.comp
    (weightedPositiveRootOperator n
      (rootWedgeWeight lam (rootAdmissibleSwap lam S α β hα hβ hadm)) γ
      (rootAdmissibleSwap_lower_first_pos lam S α β γ hα hβ hadm
        hstructure))

@[simp] theorem rootSwapUpperStructureEdge_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β γ : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hstructure : rootStructureConstant β γ α ≠ 0)
    (p : JointHarmonicWeightSpace n
      (rootWedgeWeight lam
        (rootAdmissibleSwap lam S α β hα hβ hadm))) :
    (((rootSwapUpperStructureEdge n lam S α β γ hα hβ hadm hstructure p).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) =
      polarization r n (positiveRootFirst γ) (positiveRootSecond γ)
    (p.val : PolynomialSpace r n) := by
  unfold rootSwapUpperStructureEdge
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    jointHarmonicWeightCast_coe, activePositiveRootRaise_coe]

@[simp] theorem rootSwapLowerStructureEdge_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α β γ : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hstructure : rootStructureConstant α γ β ≠ 0)
    (p : JointHarmonicWeightSpace n
      (rootWedgeWeight lam
        (rootAdmissibleSwap lam S α β hα hβ hadm))) :
    (((rootSwapLowerStructureEdge n lam S α β γ hα hβ hadm hstructure p).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) =
      polarization r n (positiveRootSecond γ) (positiveRootFirst γ)
    (p.val : PolynomialSpace r n) := by
  unfold rootSwapLowerStructureEdge
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    jointHarmonicWeightCast_coe, weightedPositiveRootOperator_coe]
  rfl

end

section


open scoped BigOperators

theorem sum_mul_rootCharge {r : ℕ}
    (u : Fin (r + 1) → ℤ) (α : PositiveRoot r) :
    (∑ i, u i * rootCharge α i) =
      u (positiveRootFirst α) - u (positiveRootSecond α) := by
  classical
  simp only [rootCharge, mul_ite, mul_one, mul_neg, mul_zero]
  have hsplit (i : Fin (r + 1)) :
      (if i = positiveRootFirst α then u i
        else if i = positiveRootSecond α then -u i else 0) =
        (if i = positiveRootFirst α then u i else 0) +
          (if i = positiveRootSecond α then -u i else 0) := by
    by_cases hi : i = positiveRootFirst α
    · subst i
      simp only [↓reduceIte, positiveRootFirst_ne_second α, add_zero]
    · simp only [hi, ↓reduceIte, zero_add]
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact (sub_eq_add_neg _ _).symm

theorem sum_mul_rootFamilyCharge {r : ℕ}
    (u : Fin (r + 1) → ℤ) (S : Finset (PositiveRoot r)) :
    (∑ i, u i * rootFamilyCharge S i) =
      ∑ α ∈ S,
        (u (positiveRootFirst α) - u (positiveRootSecond α)) := by
  classical
  simp_rw [rootFamilyCharge, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_mul_rootCharge]

theorem exists_rootFamilyCharge_ne_zero_of_nonempty {r : ℕ}
    (S : Finset (PositiveRoot r)) (hS : S.Nonempty) :
    ∃ i : Fin (r + 1), rootFamilyCharge S i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hpair := sum_mul_rootFamilyCharge
    (fun i : Fin (r + 1) => (i.val : ℤ)) S
  have hzero :
      (∑ α ∈ S,
        (((positiveRootFirst α).val : ℤ) -
          ((positiveRootSecond α).val : ℤ))) = 0 := by
    simpa only [Finset.sum_sub_distrib, h, mul_zero, Finset.sum_const_zero] using hpair.symm
  have hpositive :
      0 < ∑ α ∈ S,
        (((positiveRootSecond α).val : ℤ) -
          ((positiveRootFirst α).val : ℤ)) := by
    apply Finset.sum_pos
    · intro α _
      exact sub_pos.mpr (by
        exact_mod_cast positiveRootFirst_lt_second α)
    · exact hS
  have hcancel :
      (∑ α ∈ S,
        (((positiveRootFirst α).val : ℤ) -
          ((positiveRootSecond α).val : ℤ))) +
      (∑ α ∈ S,
        (((positiveRootSecond α).val : ℤ) -
          ((positiveRootFirst α).val : ℤ))) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro α _
    omega
  omega

theorem sum_signedRootWeight_root_difference {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (S : Finset (PositiveRoot r)) :
    (∑ α ∈ S,
      (signedRootWeight lam S (positiveRootFirst α) -
        signedRootWeight lam S (positiveRootSecond α))) =
      (∑ α ∈ S,
        ((lam (positiveRootFirst α) : ℤ) -
          (lam (positiveRootSecond α) : ℤ))) +
        ∑ i : Fin (r + 1),
          rootFamilyCharge S i * rootFamilyCharge S i := by
  classical
  calc
    (∑ α ∈ S,
      (signedRootWeight lam S (positiveRootFirst α) -
        signedRootWeight lam S (positiveRootSecond α))) =
        ∑ i : Fin (r + 1),
          signedRootWeight lam S i * rootFamilyCharge S i :=
      (sum_mul_rootFamilyCharge (signedRootWeight lam S) S).symm
    _ = (∑ i : Fin (r + 1),
          (lam i : ℤ) * rootFamilyCharge S i) +
        ∑ i : Fin (r + 1),
          rootFamilyCharge S i * rootFamilyCharge S i := by
      simp_rw [signedRootWeight, add_mul, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_mul_rootFamilyCharge (fun i => (lam i : ℤ)) S]

theorem exists_signedRootWeight_descending_of_antitone {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (S : Finset (PositiveRoot r)) (hS : S.Nonempty) :
    ∃ α ∈ S,
      signedRootWeight lam S (positiveRootSecond α) <
        signedRootWeight lam S (positiveRootFirst α) := by
  classical
  obtain ⟨i, hi⟩ := exists_rootFamilyCharge_ne_zero_of_nonempty S hS
  have hdominant :
      0 ≤ ∑ α ∈ S,
        ((lam (positiveRootFirst α) : ℤ) -
          (lam (positiveRootSecond α) : ℤ)) := by
    apply Finset.sum_nonneg
    intro α _
    exact sub_nonneg.mpr (by
      exact_mod_cast hdom (positiveRootFirst_lt_second α).le)
  have hsquares :
      0 < ∑ j : Fin (r + 1),
        rootFamilyCharge S j * rootFamilyCharge S j := by
    apply (Finset.sum_pos_iff_of_nonneg
      (fun j _ => mul_self_nonneg (rootFamilyCharge S j))).mpr
    exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  have hpositive :
      0 < ∑ α ∈ S,
        (signedRootWeight lam S (positiveRootFirst α) -
          signedRootWeight lam S (positiveRootSecond α)) := by
    rw [sum_signedRootWeight_root_difference lam S]
    omega
  by_contra h
  push Not at h
  have hnonpositive :
      (∑ α ∈ S,
        (signedRootWeight lam S (positiveRootFirst α) -
          signedRootWeight lam S (positiveRootSecond α))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro α hα
    exact sub_nonpos.mpr (h α hα)
  omega

theorem exists_rootWedgeWeight_descending_of_antitone {r k : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hk : 0 < k) (S : AdmissibleRootWedge lam k) :
    ∃ α ∈ S.val.val,
      rootWedgeWeight lam S (positiveRootSecond α) <
        rootWedgeWeight lam S (positiveRootFirst α) := by
  have hnonempty : S.val.val.Nonempty :=
    Finset.card_pos.mp (by simpa only [S.val.property] using hk)
  obtain ⟨α, hα, hstrict⟩ :=
    exists_signedRootWeight_descending_of_antitone
      lam hdom S.val.val hnonempty
  refine ⟨α, hα, ?_⟩
  exact_mod_cast (show
    (rootWedgeWeight lam S (positiveRootSecond α) : ℤ) <
      (rootWedgeWeight lam S (positiveRootFirst α) : ℤ) by
      simpa only [rootWedgeWeight_cast] using hstrict)

end

section


open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung

theorem weightedPositiveRootOperator_fischer_energy_gap
    {r n : ℕ} (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r)
    (hμ : 0 < μ (positiveRootFirst α))
    (p : JointHarmonicWeightSpace n μ) :
    (jointHarmonicWeightFischerCore n (lowerRootWeight μ α)).inner
        (weightedPositiveRootOperator n μ α hμ p)
        (weightedPositiveRootOperator n μ α hμ p) =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (polarization r n (positiveRootFirst α) (positiveRootSecond α)
          (p.val : PolynomialSpace r n))
        (polarization r n (positiveRootFirst α) (positiveRootSecond α)
          (p.val : PolynomialSpace r n)) +
      ((μ (positiveRootFirst α) : ℝ) -
        (μ (positiveRootSecond α) : ℝ)) *
          (jointHarmonicWeightFischerCore n μ).inner p p := by
  have hfirst := youngMultihomogeneous_rowEuler μ p.val
    (positiveRootFirst α)
  have hsecond := youngMultihomogeneous_rowEuler μ p.val
    (positiveRootSecond α)
  have hcomm := FullRankClebsch.oppositePolarization_commutator
    (positiveRootFirst α) (positiveRootSecond α)
    (p.val : PolynomialSpace r n)
  rw [hfirst, hsecond] at hcomm
  have hpair := congrArg
    (fun q : PolynomialSpace r n =>
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        q (p.val : PolynomialSpace r n)) hcomm
  have hlower :
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (polarization r n (positiveRootFirst α) (positiveRootSecond α)
          (polarization r n (positiveRootSecond α) (positiveRootFirst α)
            (p.val : PolynomialSpace r n)))
        (p.val : PolynomialSpace r n) =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (polarization r n (positiveRootSecond α) (positiveRootFirst α)
          (p.val : PolynomialSpace r n))
        (polarization r n (positiveRootSecond α) (positiveRootFirst α)
          (p.val : PolynomialSpace r n)) :=
    polynomialInner_polarization_harmonicLift
      (positiveRootFirst α) (positiveRootSecond α)
      (polarization r n (positiveRootSecond α) (positiveRootFirst α)
        (p.val : PolynomialSpace r n))
      (p.val : PolynomialSpace r n)
  have hupper :
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (polarization r n (positiveRootSecond α) (positiveRootFirst α)
          (polarization r n (positiveRootFirst α) (positiveRootSecond α)
            (p.val : PolynomialSpace r n)))
        (p.val : PolynomialSpace r n) =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (polarization r n (positiveRootFirst α) (positiveRootSecond α)
          (p.val : PolynomialSpace r n))
        (polarization r n (positiveRootFirst α) (positiveRootSecond α)
          (p.val : PolynomialSpace r n)) :=
    polynomialInner_polarization_harmonicLift
      (positiveRootSecond α) (positiveRootFirst α)
      (polarization r n (positiveRootFirst α) (positiveRootSecond α)
        (p.val : PolynomialSpace r n))
      (p.val : PolynomialSpace r n)
  rw [SpherePacking.Fischer.polynomialInner_add_left,
    SpherePacking.Fischer.polynomialInner_add_left,
    SpherePacking.Fischer.polynomialInner_smul_left,
    SpherePacking.Fischer.polynomialInner_smul_left,
    hlower, hupper] at hpair
  rw [jointHarmonicWeightFischerCore_inner,
    jointHarmonicWeightFischerCore_inner]
  change
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (polarization r n (positiveRootSecond α) (positiveRootFirst α)
          (p.val : PolynomialSpace r n))
        (polarization r n (positiveRootSecond α) (positiveRootFirst α)
          (p.val : PolynomialSpace r n)) = _
  linear_combination hpair

theorem weightedPositiveRootOperator_fischer_energy_ge_gap
    {r n : ℕ} (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r)
    (hμ : 0 < μ (positiveRootFirst α))
    (p : JointHarmonicWeightSpace n μ) :
    ((μ (positiveRootFirst α) : ℝ) -
      (μ (positiveRootSecond α) : ℝ)) *
        (jointHarmonicWeightFischerCore n μ).inner p p ≤
      (jointHarmonicWeightFischerCore n (lowerRootWeight μ α)).inner
        (weightedPositiveRootOperator n μ α hμ p)
        (weightedPositiveRootOperator n μ α hμ p) := by
  rw [weightedPositiveRootOperator_fischer_energy_gap μ α hμ p]
  have hnonneg := SpherePacking.Fischer.polynomialInner_self_nonneg
    ((r + 1) * n)
    (polarization r n (positiveRootFirst α) (positiveRootSecond α)
      (p.val : PolynomialSpace r n))
  linarith

private abbrev IncludedDescendingPositiveRoot {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k) :=
  {α : PositiveRoot r //
    α ∈ S.val.val ∧
      rootWedgeWeight lam S (positiveRootSecond α) <
        rootWedgeWeight lam S (positiveRootFirst α)}

theorem includedDescendingPositiveRoot_nonempty_of_antitone
    {r k : ℕ} (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam) (hk : 0 < k)
    (S : AdmissibleRootWedge lam k) :
    Nonempty (IncludedDescendingPositiveRoot lam S) := by
  obtain ⟨α, hα, hstrict⟩ :=
    exists_rootWedgeWeight_descending_of_antitone lam hdom hk S
  exact ⟨⟨α, hα, hstrict⟩⟩

theorem includedDescendingPositiveRoot_first_pos
    {r k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : IncludedDescendingPositiveRoot lam S) :
    0 < rootWedgeWeight lam S (positiveRootFirst α.val) := by
  omega

private def includedDescendingPositiveRootOperator
    {r k : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : IncludedDescendingPositiveRoot lam S) :
    JointHarmonicWeightSpace n (rootWedgeWeight lam S) →ₗ[ℝ]
      JointHarmonicWeightSpace n
        (lowerRootWeight (rootWedgeWeight lam S) α.val) :=
  weightedPositiveRootOperator n (rootWedgeWeight lam S) α.val
    (includedDescendingPositiveRoot_first_pos lam S α)

private def includedDescendingPositiveRootOperatorStar
    {r k : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : IncludedDescendingPositiveRoot lam S) :
    JointHarmonicWeightSpace n
        (lowerRootWeight (rootWedgeWeight lam S) α.val) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) :=
  weightedPositiveRootOperatorStar n (rootWedgeWeight lam S) α.val
    (includedDescendingPositiveRoot_first_pos lam S α)

theorem includedDescendingPositiveRoot_fischer_adjoint
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : IncludedDescendingPositiveRoot lam S)
    (p : JointHarmonicWeightSpace n
      (lowerRootWeight (rootWedgeWeight lam S) α.val))
    (q : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner
      (includedDescendingPositiveRootOperatorStar n lam S α p) q =
        (jointHarmonicWeightFischerCore n
          (lowerRootWeight (rootWedgeWeight lam S) α.val)).inner p
            (includedDescendingPositiveRootOperator n lam S α q) := by
  rw [jointHarmonicWeightFischerCore_inner,
    jointHarmonicWeightFischerCore_inner]
  exact polynomialInner_polarization_harmonicLift
    (positiveRootFirst α.val) (positiveRootSecond α.val)
    (p.val : PolynomialSpace r n) (q.val : PolynomialSpace r n)

private def includedDescendingPositiveRootFischerLaplacian
    {r k : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k) :
    JointHarmonicWeightSpace n (rootWedgeWeight lam S) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) :=
  finiteFischerRootLaplacian
    (ι := IncludedDescendingPositiveRoot lam S)
    (V := JointHarmonicWeightSpace n (rootWedgeWeight lam S))
    (fun α : IncludedDescendingPositiveRoot lam S =>
      JointHarmonicWeightSpace n
        (lowerRootWeight (rootWedgeWeight lam S) α.val))
    (includedDescendingPositiveRootOperator n lam S)
    (includedDescendingPositiveRootOperatorStar n lam S)

theorem includedDescendingPositiveRootFischerLaplacian_energy
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner p
      (includedDescendingPositiveRootFischerLaplacian n lam S p) =
        ∑ α : IncludedDescendingPositiveRoot lam S,
          (jointHarmonicWeightFischerCore n
            (lowerRootWeight (rootWedgeWeight lam S) α.val)).inner
              (includedDescendingPositiveRootOperator n lam S α p)
              (includedDescendingPositiveRootOperator n lam S α p) := by
  exact finiteFischerRootLaplacian_energy
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S))
    (fun α : IncludedDescendingPositiveRoot lam S =>
      JointHarmonicWeightSpace n
        (lowerRootWeight (rootWedgeWeight lam S) α.val))
    (fun α => jointHarmonicWeightFischerCore n
      (lowerRootWeight (rootWedgeWeight lam S) α.val))
    (includedDescendingPositiveRootOperator n lam S)
    (includedDescendingPositiveRootOperatorStar n lam S)
    (includedDescendingPositiveRoot_fischer_adjoint lam S) p

theorem includedDescendingPositiveRootFischerLaplacian_energy_ge_self
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : IncludedDescendingPositiveRoot lam S)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner p p ≤
      (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner p
        (includedDescendingPositiveRootFischerLaplacian n lam S p) := by
  rw [includedDescendingPositiveRootFischerLaplacian_energy lam S p]
  have hterm :
      (jointHarmonicWeightFischerCore n
        (lowerRootWeight (rootWedgeWeight lam S) α.val)).inner
          (includedDescendingPositiveRootOperator n lam S α p)
          (includedDescendingPositiveRootOperator n lam S α p) ≤
        ∑ β : IncludedDescendingPositiveRoot lam S,
          (jointHarmonicWeightFischerCore n
            (lowerRootWeight (rootWedgeWeight lam S) β.val)).inner
              (includedDescendingPositiveRootOperator n lam S β p)
              (includedDescendingPositiveRootOperator n lam S β p) := by
    exact Finset.single_le_sum
      (fun β _ => by
        simpa only [RCLike.re_to_real] using
          (jointHarmonicWeightFischerCore n (lowerRootWeight (rootWedgeWeight lam S)
            β.val)).re_inner_nonneg
            (includedDescendingPositiveRootOperator n lam S β p))
      (Finset.mem_univ α)
  have hnat :
      rootWedgeWeight lam S (positiveRootSecond α.val) + 1 ≤
        rootWedgeWeight lam S (positiveRootFirst α.val) := by
    omega
  have hreal :
      ((rootWedgeWeight lam S (positiveRootSecond α.val) + 1 : ℕ) : ℝ) ≤
        (rootWedgeWeight lam S (positiveRootFirst α.val) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hreal
  have hgap :
      (1 : ℝ) ≤ (rootWedgeWeight lam S (positiveRootFirst α.val) : ℝ) -
        (rootWedgeWeight lam S (positiveRootSecond α.val) : ℝ) := by
    linarith
  have hself :
      0 ≤ (jointHarmonicWeightFischerCore n
        (rootWedgeWeight lam S)).inner p p := by
    simpa only [RCLike.re_to_real] using
      (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).re_inner_nonneg p
  have hone := mul_le_mul_of_nonneg_right hgap hself
  have hroot := weightedPositiveRootOperator_fischer_energy_ge_gap
    (rootWedgeWeight lam S) α.val
    (includedDescendingPositiveRoot_first_pos lam S α) p
  exact le_trans (by simpa only [one_mul] using hone) (le_trans hroot hterm)

/--
The root joint harmonic included descending fischer laplacian used in the spherical-code
argument.
-/
def rootJointHarmonicIncludedDescendingFischerLaplacian {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootJointHarmonicChain n lam k :=
  LinearMap.pi fun S : AdmissibleRootWedge lam k =>
    (includedDescendingPositiveRootFischerLaplacian n lam S).comp
      (LinearMap.proj S :
        RootJointHarmonicChain n lam k →ₗ[ℝ]
          JointHarmonicWeightSpace n (rootWedgeWeight lam S))

@[simp] theorem rootJointHarmonicIncludedDescendingFischerLaplacian_apply
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    rootJointHarmonicIncludedDescendingFischerLaplacian n lam k f S =
      includedDescendingPositiveRootFischerLaplacian n lam S (f S) := rfl

theorem rootJointHarmonicIncludedDescendingFischerLaplacian_energy_ge_self
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam) (hk : 0 < k)
    (f : RootJointHarmonicChain n lam k) :
    (rootJointHarmonicChainFischerCore n lam k).inner f f ≤
      (rootJointHarmonicChainFischerCore n lam k).inner f
        (rootJointHarmonicIncludedDescendingFischerLaplacian n lam k f) := by
  rw [rootJointHarmonicChainFischerCore_inner,
    rootJointHarmonicChainFischerCore_inner]
  apply Finset.sum_le_sum
  intro S _
  exact includedDescendingPositiveRootFischerLaplacian_energy_ge_self
    lam S
      (Classical.choice
        (includedDescendingPositiveRoot_nonempty_of_antitone
          lam hdom hk S)) (f S)

theorem rootJointHarmonicIncludedDescendingFischerLaplacian_energy_pos
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam) (hk : 0 < k)
    (f : RootJointHarmonicChain n lam k) (hf : f ≠ 0) :
    0 < (rootJointHarmonicChainFischerCore n lam k).inner f
      (rootJointHarmonicIncludedDescendingFischerLaplacian n lam k f) := by
  have hnonneg := (rootJointHarmonicChainFischerCore n lam k).re_inner_nonneg f
  have hnonzero :
      (rootJointHarmonicChainFischerCore n lam k).inner f f ≠ 0 := by
    intro h
    exact hf ((rootJointHarmonicChainFischerCore n lam k).definite f h)
  have hpositive :
      0 < (rootJointHarmonicChainFischerCore n lam k).inner f f :=
    lt_of_le_of_ne (by simpa only [rootJointHarmonicChainFischerCore_inner, map_sum,
                         RCLike.re_to_real] using hnonneg) (Ne.symm hnonzero)
  exact lt_of_lt_of_le hpositive
    (rootJointHarmonicIncludedDescendingFischerLaplacian_energy_ge_self
      lam hdom hk f)

end

section


open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung

private abbrev IncludedNondescendingPositiveRoot {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k) :=
  {α : PositiveRoot r //
    α ∈ S.val.val ∧
      0 < rootWedgeWeight lam S (positiveRootFirst α) ∧
        rootWedgeWeight lam S (positiveRootFirst α) ≤
          rootWedgeWeight lam S (positiveRootSecond α)}

private abbrev ExcludedActivePositiveRoot {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k) :=
  {α : PositiveRoot r //
    α ∉ S.val.val ∧
      0 < rootWedgeWeight lam S (positiveRootSecond α)}

private def includedNondescendingPositiveRootOperator
    {r k : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : IncludedNondescendingPositiveRoot lam S) :
    JointHarmonicWeightSpace n (rootWedgeWeight lam S) →ₗ[ℝ]
      JointHarmonicWeightSpace n
        (lowerRootWeight (rootWedgeWeight lam S) α.val) :=
  weightedPositiveRootOperator n (rootWedgeWeight lam S) α.val
    α.property.2.1

private def includedNondescendingPositiveRootOperatorStar
    {r k : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : IncludedNondescendingPositiveRoot lam S) :
    JointHarmonicWeightSpace n
        (lowerRootWeight (rootWedgeWeight lam S) α.val) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) :=
  weightedPositiveRootOperatorStar n (rootWedgeWeight lam S) α.val
    α.property.2.1

theorem includedNondescendingPositiveRoot_fischer_adjoint
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : IncludedNondescendingPositiveRoot lam S)
    (p : JointHarmonicWeightSpace n
      (lowerRootWeight (rootWedgeWeight lam S) α.val))
    (q : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner
        (includedNondescendingPositiveRootOperatorStar n lam S α p) q =
      (jointHarmonicWeightFischerCore n
        (lowerRootWeight (rootWedgeWeight lam S) α.val)).inner
          p (includedNondescendingPositiveRootOperator n lam S α q) := by
  rw [jointHarmonicWeightFischerCore_inner,
    jointHarmonicWeightFischerCore_inner]
  exact polynomialInner_polarization_harmonicLift
    (positiveRootFirst α.val) (positiveRootSecond α.val)
    (p.val : PolynomialSpace r n) (q.val : PolynomialSpace r n)

private def includedNondescendingPositiveRootFischerLaplacian
    {r k : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k) :
    JointHarmonicWeightSpace n (rootWedgeWeight lam S) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) :=
  finiteFischerRootLaplacian
    (ι := IncludedNondescendingPositiveRoot lam S)
    (V := JointHarmonicWeightSpace n (rootWedgeWeight lam S))
    (fun α : IncludedNondescendingPositiveRoot lam S =>
      JointHarmonicWeightSpace n
        (lowerRootWeight (rootWedgeWeight lam S) α.val))
    (includedNondescendingPositiveRootOperator n lam S)
    (includedNondescendingPositiveRootOperatorStar n lam S)

private def excludedActivePositiveRootOperator
    {r k : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : ExcludedActivePositiveRoot lam S) :
    JointHarmonicWeightSpace n (rootWedgeWeight lam S) →ₗ[ℝ]
      JointHarmonicWeightSpace n
        (activeRootRaisedWeight (rootWedgeWeight lam S)
          ⟨α.val, α.property.2⟩) :=
  activePositiveRootRaise n (rootWedgeWeight lam S)
    ⟨α.val, α.property.2⟩

private def excludedActivePositiveRootOperatorStar
    {r k : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : ExcludedActivePositiveRoot lam S) :
    JointHarmonicWeightSpace n
        (activeRootRaisedWeight (rootWedgeWeight lam S)
          ⟨α.val, α.property.2⟩) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) :=
  activePositiveRootLower n (rootWedgeWeight lam S)
    ⟨α.val, α.property.2⟩

theorem excludedActivePositiveRoot_fischer_adjoint
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (α : ExcludedActivePositiveRoot lam S)
    (p : JointHarmonicWeightSpace n
      (activeRootRaisedWeight (rootWedgeWeight lam S)
        ⟨α.val, α.property.2⟩))
    (q : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner
      (excludedActivePositiveRootOperatorStar n lam S α p) q =
      (jointHarmonicWeightFischerCore n
        (activeRootRaisedWeight (rootWedgeWeight lam S)
          ⟨α.val, α.property.2⟩)).inner
        p (excludedActivePositiveRootOperator n lam S α q) :=
  activePositiveRoot_fischer_adjoint
    (rootWedgeWeight lam S) ⟨α.val, α.property.2⟩ p q

private def excludedActivePositiveRootFischerLaplacian
    {r k : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k) :
    JointHarmonicWeightSpace n (rootWedgeWeight lam S) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) :=
  finiteFischerRootLaplacian
    (ι := ExcludedActivePositiveRoot lam S)
    (V := JointHarmonicWeightSpace n (rootWedgeWeight lam S))
    (fun α : ExcludedActivePositiveRoot lam S =>
      JointHarmonicWeightSpace n
        (activeRootRaisedWeight (rootWedgeWeight lam S)
          ⟨α.val, α.property.2⟩))
    (excludedActivePositiveRootOperator n lam S)
    (excludedActivePositiveRootOperatorStar n lam S)

/-- The root joint harmonic hodge diagonal used in the spherical-code argument. -/
def rootJointHarmonicHodgeDiagonal {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootJointHarmonicChain n lam k :=
  LinearMap.pi fun S : AdmissibleRootWedge lam k =>
    (includedDescendingPositiveRootFischerLaplacian n lam S +
      includedNondescendingPositiveRootFischerLaplacian n lam S +
      excludedActivePositiveRootFischerLaplacian n lam S).comp
        (LinearMap.proj S)

@[simp] theorem rootJointHarmonicHodgeDiagonal_apply {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    rootJointHarmonicHodgeDiagonal n lam k f S =
      includedDescendingPositiveRootFischerLaplacian n lam S (f S) +
        includedNondescendingPositiveRootFischerLaplacian n lam S (f S) +
        excludedActivePositiveRootFischerLaplacian n lam S (f S) := rfl

theorem includedNondescendingPositiveRootFischerLaplacian_energy
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner p
      (includedNondescendingPositiveRootFischerLaplacian n lam S p) =
        ∑ α : IncludedNondescendingPositiveRoot lam S,
          (jointHarmonicWeightFischerCore n
            (lowerRootWeight (rootWedgeWeight lam S) α.val)).inner
              (includedNondescendingPositiveRootOperator n lam S α p)
              (includedNondescendingPositiveRootOperator n lam S α p) := by
  exact finiteFischerRootLaplacian_energy
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S))
    (fun α : IncludedNondescendingPositiveRoot lam S =>
      JointHarmonicWeightSpace n
        (lowerRootWeight (rootWedgeWeight lam S) α.val))
    (fun α => jointHarmonicWeightFischerCore n
      (lowerRootWeight (rootWedgeWeight lam S) α.val))
    (includedNondescendingPositiveRootOperator n lam S)
    (includedNondescendingPositiveRootOperatorStar n lam S)
    (includedNondescendingPositiveRoot_fischer_adjoint lam S) p

theorem includedNondescendingPositiveRootFischerLaplacian_energy_nonneg
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    0 ≤ (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner p
      (includedNondescendingPositiveRootFischerLaplacian n lam S p) := by
  rw [includedNondescendingPositiveRootFischerLaplacian_energy]
  apply Finset.sum_nonneg
  intro α _
  exact (jointHarmonicWeightFischerCore n
    (lowerRootWeight (rootWedgeWeight lam S) α.val)).re_inner_nonneg
      (includedNondescendingPositiveRootOperator n lam S α p)

theorem excludedActivePositiveRootFischerLaplacian_energy
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner p
      (excludedActivePositiveRootFischerLaplacian n lam S p) =
        ∑ α : ExcludedActivePositiveRoot lam S,
          (jointHarmonicWeightFischerCore n
            (activeRootRaisedWeight (rootWedgeWeight lam S)
              ⟨α.val, α.property.2⟩)).inner
                (excludedActivePositiveRootOperator n lam S α p)
                (excludedActivePositiveRootOperator n lam S α p) := by
  exact finiteFischerRootLaplacian_energy
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S))
    (fun α : ExcludedActivePositiveRoot lam S =>
      JointHarmonicWeightSpace n
        (activeRootRaisedWeight (rootWedgeWeight lam S)
          ⟨α.val, α.property.2⟩))
    (fun α => jointHarmonicWeightFischerCore n
      (activeRootRaisedWeight (rootWedgeWeight lam S)
        ⟨α.val, α.property.2⟩))
    (excludedActivePositiveRootOperator n lam S)
    (excludedActivePositiveRootOperatorStar n lam S)
    (excludedActivePositiveRoot_fischer_adjoint lam S) p

theorem excludedActivePositiveRootFischerLaplacian_energy_nonneg
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    0 ≤ (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner p
      (excludedActivePositiveRootFischerLaplacian n lam S p) := by
  rw [excludedActivePositiveRootFischerLaplacian_energy]
  apply Finset.sum_nonneg
  intro α _
  exact (jointHarmonicWeightFischerCore n
    (activeRootRaisedWeight (rootWedgeWeight lam S)
      ⟨α.val, α.property.2⟩)).re_inner_nonneg
        (excludedActivePositiveRootOperator n lam S α p)

theorem rootJointHarmonicHodgeDiagonal_energy_ge_included
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k) :
    (rootJointHarmonicChainFischerCore n lam k).inner f
      (rootJointHarmonicIncludedDescendingFischerLaplacian n lam k f) ≤
      (rootJointHarmonicChainFischerCore n lam k).inner f
        (rootJointHarmonicHodgeDiagonal n lam k f) := by
  rw [rootJointHarmonicChainFischerCore_inner,
    rootJointHarmonicChainFischerCore_inner]
  apply Finset.sum_le_sum
  intro S _
  rw [rootJointHarmonicIncludedDescendingFischerLaplacian_apply,
    rootJointHarmonicHodgeDiagonal_apply,
    jointHarmonicWeightFischerCore_inner,
    jointHarmonicWeightFischerCore_inner]
  change
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        ((f S).val : PolynomialSpace r n)
        (((includedDescendingPositiveRootFischerLaplacian n lam S
          (f S)).val : youngMultihomogeneousSubmodule n
            (rootWedgeWeight lam S)) : PolynomialSpace r n) ≤
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        ((f S).val : PolynomialSpace r n)
        ((((includedDescendingPositiveRootFischerLaplacian n lam S (f S)).val :
            youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
              PolynomialSpace r n) +
          (((includedNondescendingPositiveRootFischerLaplacian n lam S
              (f S)).val : youngMultihomogeneousSubmodule n
                (rootWedgeWeight lam S)) : PolynomialSpace r n) +
          (((excludedActivePositiveRootFischerLaplacian n lam S
              (f S)).val : youngMultihomogeneousSubmodule n
                (rootWedgeWeight lam S)) : PolynomialSpace r n))
  rw [SpherePacking.Fischer.polynomialInner_add_right,
    SpherePacking.Fischer.polynomialInner_add_right]
  have hnonneg :=
    includedNondescendingPositiveRootFischerLaplacian_energy_nonneg
      lam S (f S)
  have hexcluded :=
    excludedActivePositiveRootFischerLaplacian_energy_nonneg
      lam S (f S)
  rw [jointHarmonicWeightFischerCore_inner] at hnonneg hexcluded
  linarith

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The root swap exterior hodge sign used in the spherical-code argument. -/
def rootSwapExteriorHodgeSign {r k : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (S : AdmissibleRootWedge lam k)
    (α β : PositiveRoot r) : ℝ :=
  realExteriorRootSign S.val.val α *
    realExteriorRootSign (insert β (S.val.val.erase α)) β

/--
The root joint harmonic action upper root structure cross used in the spherical-code argument.
-/
def rootJointHarmonicActionUpperRootStructureCross {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootJointHarmonicChain n lam k := by
  classical
  refine LinearMap.pi fun S : AdmissibleRootWedge lam k => ?_
  exact ∑ α : PositiveRoot r,
    if hα : α ∈ S.val.val then
      ∑ β : PositiveRoot r,
        if hβ : β ∈ S.val.val then 0
        else if hadm : ∀ i,
            0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i then
          ∑ γ : PositiveRoot r,
            if hγ : rootStructureConstant β γ α = 0 then 0
            else (rootSwapExteriorHodgeSign S α β *
                rootStructureConstant β γ α) •
              (rootSwapUpperStructureEdge n lam S α β γ hα hβ hadm hγ).comp
                (LinearMap.proj
                  (rootAdmissibleSwap lam S α β hα hβ hadm))
        else 0
    else 0

/--
The root joint harmonic action lower root structure cross used in the spherical-code argument.
-/
def rootJointHarmonicActionLowerRootStructureCross {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootJointHarmonicChain n lam k := by
  classical
  refine LinearMap.pi fun S : AdmissibleRootWedge lam k => ?_
  exact ∑ α : PositiveRoot r,
    if hα : α ∈ S.val.val then
      ∑ β : PositiveRoot r,
        if hβ : β ∈ S.val.val then 0
        else if hadm : ∀ i,
            0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i then
          ∑ γ : PositiveRoot r,
            if hγ : rootStructureConstant α γ β = 0 then 0
            else (rootSwapExteriorHodgeSign S α β *
                rootStructureConstant α γ β) •
              (rootSwapLowerStructureEdge n lam S α β γ hα hβ hadm hγ).comp
                (LinearMap.proj
                  (rootAdmissibleSwap lam S α β hα hβ hadm))
        else 0
    else 0

/-- The root joint harmonic action hodge off diagonal used in the spherical-code argument. -/
def rootJointHarmonicActionHodgeOffDiagonal {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootJointHarmonicChain n lam k :=
  rootJointHarmonicActionUpperRootStructureCross n lam k +
    rootJointHarmonicActionLowerRootStructureCross n lam k

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootJointHarmonicActionUpperRootStructureCross_apply
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    rootJointHarmonicActionUpperRootStructureCross n lam k f S =
      ∑ α : PositiveRoot r,
        if hα : α ∈ S.val.val then
          ∑ β : PositiveRoot r,
            if hβ : β ∈ S.val.val then 0
            else if hadm : ∀ i,
                0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i then
              ∑ γ : PositiveRoot r,
                if hγ : rootStructureConstant β γ α = 0 then 0
                else (rootSwapExteriorHodgeSign S α β *
                    rootStructureConstant β γ α) •
                  rootSwapUpperStructureEdge n lam S α β γ hα hβ hadm hγ
                    (f (rootAdmissibleSwap lam S α β hα hβ hadm))
            else 0
        else 0 := by
  classical
  unfold rootJointHarmonicActionUpperRootStructureCross
  change
    (∑ α : PositiveRoot r,
      if hα : α ∈ S.val.val then
        ∑ β : PositiveRoot r,
          if hβ : β ∈ S.val.val then 0
          else if hadm : ∀ i,
              0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i then
            ∑ γ : PositiveRoot r,
              if hγ : rootStructureConstant β γ α = 0 then 0
              else (rootSwapExteriorHodgeSign S α β *
                  rootStructureConstant β γ α) •
                (rootSwapUpperStructureEdge n lam S α β γ hα hβ hadm hγ).comp
                  (LinearMap.proj
                    (rootAdmissibleSwap lam S α β hα hβ hadm))
          else 0
      else 0) f = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with hα
  · rw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro β _
    split_ifs with hβ hadm
    · rfl
    · rw [LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro γ _
      split_ifs with hγ
      · rfl
      · rfl
    · rfl
  · rfl

theorem rootJointHarmonicActionLowerRootStructureCross_apply
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    rootJointHarmonicActionLowerRootStructureCross n lam k f S =
      ∑ α : PositiveRoot r,
        if hα : α ∈ S.val.val then
          ∑ β : PositiveRoot r,
            if hβ : β ∈ S.val.val then 0
            else if hadm : ∀ i,
                0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i then
              ∑ γ : PositiveRoot r,
                if hγ : rootStructureConstant α γ β = 0 then 0
                else (rootSwapExteriorHodgeSign S α β *
                    rootStructureConstant α γ β) •
                  rootSwapLowerStructureEdge n lam S α β γ hα hβ hadm hγ
                    (f (rootAdmissibleSwap lam S α β hα hβ hadm))
            else 0
        else 0 := by
  classical
  unfold rootJointHarmonicActionLowerRootStructureCross
  change
    (∑ α : PositiveRoot r,
      if hα : α ∈ S.val.val then
        ∑ β : PositiveRoot r,
          if hβ : β ∈ S.val.val then 0
          else if hadm : ∀ i,
              0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i then
            ∑ γ : PositiveRoot r,
              if hγ : rootStructureConstant α γ β = 0 then 0
              else (rootSwapExteriorHodgeSign S α β *
                  rootStructureConstant α γ β) •
                (rootSwapLowerStructureEdge n lam S α β γ hα hβ hadm hγ).comp
                  (LinearMap.proj
                    (rootAdmissibleSwap lam S α β hα hβ hadm))
          else 0
      else 0) f = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with hα
  · rw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro β _
    split_ifs with hβ hadm
    · rfl
    · rw [LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro γ _
      split_ifs with hγ
      · rfl
      · rfl
    · rfl
  · rfl

theorem includedDescendingPositiveRootFischerLaplacian_apply_coe
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (((includedDescendingPositiveRootFischerLaplacian n lam S p).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) =
      ∑ α : IncludedDescendingPositiveRoot lam S,
        polarization r n (positiveRootFirst α.val)
          (positiveRootSecond α.val)
          (polarization r n (positiveRootSecond α.val)
            (positiveRootFirst α.val) (p.val : PolynomialSpace r n)) := by
  classical
  unfold includedDescendingPositiveRootFischerLaplacian
    finiteFischerRootLaplacian
  rw [LinearMap.sum_apply]
  change
    (↑((∑ α : IncludedDescendingPositiveRoot lam S,
      includedDescendingPositiveRootOperatorStar n lam S α
        (includedDescendingPositiveRootOperator n lam S α p)).val) :
      PolynomialSpace r n) = _
  change
    ((youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)).subtype
      ((jointHarmonicWeightSubmodule n (rootWedgeWeight lam S)).subtype
        (∑ α : IncludedDescendingPositiveRoot lam S,
          includedDescendingPositiveRootOperatorStar n lam S α
            (includedDescendingPositiveRootOperator n lam S α p)))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rfl

theorem includedNondescendingPositiveRootFischerLaplacian_apply_coe
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (((includedNondescendingPositiveRootFischerLaplacian n lam S p).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) =
      ∑ α : IncludedNondescendingPositiveRoot lam S,
        polarization r n (positiveRootFirst α.val)
          (positiveRootSecond α.val)
          (polarization r n (positiveRootSecond α.val)
            (positiveRootFirst α.val) (p.val : PolynomialSpace r n)) := by
  classical
  unfold includedNondescendingPositiveRootFischerLaplacian
    finiteFischerRootLaplacian
  rw [LinearMap.sum_apply]
  change
    ((youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)).subtype
      ((jointHarmonicWeightSubmodule n (rootWedgeWeight lam S)).subtype
        (∑ α : IncludedNondescendingPositiveRoot lam S,
          includedNondescendingPositiveRootOperatorStar n lam S α
            (includedNondescendingPositiveRootOperator n lam S α p)))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rfl

theorem excludedActivePositiveRootFischerLaplacian_apply_coe
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (((excludedActivePositiveRootFischerLaplacian n lam S p).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) =
      ∑ α : ExcludedActivePositiveRoot lam S,
        polarization r n (positiveRootSecond α.val)
          (positiveRootFirst α.val)
          (polarization r n (positiveRootFirst α.val)
            (positiveRootSecond α.val) (p.val : PolynomialSpace r n)) := by
  classical
  unfold excludedActivePositiveRootFischerLaplacian
    finiteFischerRootLaplacian
  rw [LinearMap.sum_apply]
  change
    ((youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)).subtype
      ((jointHarmonicWeightSubmodule n (rootWedgeWeight lam S)).subtype
        (∑ α : ExcludedActivePositiveRoot lam S,
          excludedActivePositiveRootOperatorStar n lam S α
            (excludedActivePositiveRootOperator n lam S α p)))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rfl

theorem rootJointHarmonicHodgeDiagonal_apply_coe
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    (((rootJointHarmonicHodgeDiagonal n lam k f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) =
      (∑ α : IncludedDescendingPositiveRoot lam S,
        polarization r n (positiveRootFirst α.val)
          (positiveRootSecond α.val)
          (polarization r n (positiveRootSecond α.val)
            (positiveRootFirst α.val) ((f S).val : PolynomialSpace r n))) +
      (∑ α : IncludedNondescendingPositiveRoot lam S,
        polarization r n (positiveRootFirst α.val)
          (positiveRootSecond α.val)
          (polarization r n (positiveRootSecond α.val)
            (positiveRootFirst α.val) ((f S).val : PolynomialSpace r n))) +
      (∑ α : ExcludedActivePositiveRoot lam S,
        polarization r n (positiveRootSecond α.val)
          (positiveRootFirst α.val)
          (polarization r n (positiveRootFirst α.val)
            (positiveRootSecond α.val) ((f S).val : PolynomialSpace r n))) := by
  rw [rootJointHarmonicHodgeDiagonal_apply]
  change
    (((includedDescendingPositiveRootFischerLaplacian n lam S (f S)).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) +
      (((includedNondescendingPositiveRootFischerLaplacian n lam S (f S)).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
          PolynomialSpace r n) +
      (((excludedActivePositiveRootFischerLaplacian n lam S (f S)).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
          PolynomialSpace r n) = _
  rw [includedDescendingPositiveRootFischerLaplacian_apply_coe,
    includedNondescendingPositiveRootFischerLaplacian_apply_coe,
    excludedActivePositiveRootFischerLaplacian_apply_coe]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem sum_rootSubtype_eq_indicator
    {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (P : ι → Prop) [DecidablePred P] (F : ι → M) :
    (∑ a : {a : ι // P a}, F a.val) =
      ∑ a : ι, if P a then F a else 0 := by
  classical
  calc
    (∑ a : {a : ι // P a}, F a.val) =
        ∑ a ∈ Finset.univ.filter P, F a :=
      (Finset.sum_subtype (Finset.univ.filter P) (by simp only [Finset.mem_filter, Finset.mem_univ,
                                                       true_and, implies_true]) F).symm
    _ = _ := Finset.sum_filter _ _

theorem rootPolynomialIncludedActionHodgeDiagonal_eq_subtype_sums
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (∑ α : PositiveRoot r,
      if α ∈ S.val.val then
        if 0 < rootWedgeWeight lam S (positiveRootFirst α) then
          polarization r n (positiveRootFirst α) (positiveRootSecond α)
            (polarization r n (positiveRootSecond α) (positiveRootFirst α)
              (p.val : PolynomialSpace r n))
        else 0
      else 0) =
      (∑ α : IncludedDescendingPositiveRoot lam S,
        polarization r n (positiveRootFirst α.val)
          (positiveRootSecond α.val)
          (polarization r n (positiveRootSecond α.val)
            (positiveRootFirst α.val) (p.val : PolynomialSpace r n))) +
      (∑ α : IncludedNondescendingPositiveRoot lam S,
        polarization r n (positiveRootFirst α.val)
          (positiveRootSecond α.val)
          (polarization r n (positiveRootSecond α.val)
            (positiveRootFirst α.val) (p.val : PolynomialSpace r n))) := by
  classical
  let F : PositiveRoot r → PolynomialSpace r n := fun α =>
    polarization r n (positiveRootFirst α) (positiveRootSecond α)
      (polarization r n (positiveRootSecond α) (positiveRootFirst α)
        (p.val : PolynomialSpace r n))
  let P : PositiveRoot r → Prop := fun α =>
    α ∈ S.val.val ∧
      rootWedgeWeight lam S (positiveRootSecond α) <
        rootWedgeWeight lam S (positiveRootFirst α)
  let Q : PositiveRoot r → Prop := fun α =>
    α ∈ S.val.val ∧
      0 < rootWedgeWeight lam S (positiveRootFirst α) ∧
        rootWedgeWeight lam S (positiveRootFirst α) ≤
          rootWedgeWeight lam S (positiveRootSecond α)
  change
    (∑ α : PositiveRoot r,
      if α ∈ S.val.val then
        if 0 < rootWedgeWeight lam S (positiveRootFirst α) then F α
        else 0
      else 0) =
      (∑ α : {α : PositiveRoot r // P α}, F α.val) +
        (∑ α : {α : PositiveRoot r // Q α}, F α.val)
  rw [sum_rootSubtype_eq_indicator P F,
    sum_rootSubtype_eq_indicator Q F, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hmem : α ∈ S.val.val
  · by_cases hpos : 0 < rootWedgeWeight lam S (positiveRootFirst α)
    · by_cases hdesc :
        rootWedgeWeight lam S (positiveRootSecond α) <
          rootWedgeWeight lam S (positiveRootFirst α)
      · have hnon : ¬ rootWedgeWeight lam S (positiveRootFirst α) ≤
            rootWedgeWeight lam S (positiveRootSecond α) := by omega
        simp only [hmem, ↓reduceIte, hpos, hdesc, and_self, hnon, and_false, add_zero, P, Q]
      · have hnon : rootWedgeWeight lam S (positiveRootFirst α) ≤
            rootWedgeWeight lam S (positiveRootSecond α) := by omega
        simp only [hmem, ↓reduceIte, hpos, hdesc, and_false, hnon, and_self, zero_add, P, Q]
    · have hdesc : ¬ rootWedgeWeight lam S (positiveRootSecond α) <
          rootWedgeWeight lam S (positiveRootFirst α) := by omega
      simp only [hmem, ↓reduceIte, hpos, hdesc, and_false, false_and, add_zero, P, Q]
  · simp only [hmem, ↓reduceIte, false_and, add_zero, P, Q]

theorem rootPolynomialExcludedActionHodgeDiagonal_eq_subtype_sum
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (∑ α : PositiveRoot r,
      if α ∈ S.val.val then 0
      else if 0 < rootWedgeWeight lam S (positiveRootSecond α) then
        polarization r n (positiveRootSecond α) (positiveRootFirst α)
          (polarization r n (positiveRootFirst α) (positiveRootSecond α)
            (p.val : PolynomialSpace r n))
      else 0) =
      ∑ α : ExcludedActivePositiveRoot lam S,
        polarization r n (positiveRootSecond α.val)
          (positiveRootFirst α.val)
          (polarization r n (positiveRootFirst α.val)
            (positiveRootSecond α.val) (p.val : PolynomialSpace r n)) := by
  classical
  let F : PositiveRoot r → PolynomialSpace r n := fun α =>
    polarization r n (positiveRootSecond α) (positiveRootFirst α)
      (polarization r n (positiveRootFirst α) (positiveRootSecond α)
        (p.val : PolynomialSpace r n))
  let P : PositiveRoot r → Prop := fun α =>
    α ∉ S.val.val ∧
      0 < rootWedgeWeight lam S (positiveRootSecond α)
  change
    (∑ α : PositiveRoot r,
      if α ∈ S.val.val then 0
      else if 0 < rootWedgeWeight lam S (positiveRootSecond α) then F α
      else 0) =
      ∑ α : {α : PositiveRoot r // P α}, F α.val
  rw [sum_rootSubtype_eq_indicator P F]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hmem : α ∈ S.val.val
  · simp only [hmem, ↓reduceIte, not_true_eq_false, false_and, P]
  · by_cases hpos : 0 < rootWedgeWeight lam S (positiveRootSecond α)
    · simp only [hmem, ↓reduceIte, hpos, not_false_eq_true, and_self, P]
    · simp only [hmem, ↓reduceIte, hpos, not_false_eq_true, and_false, P]

end

section


open MetricCodes.Spherical.HigherHarmonicYoung

/-- The root joint harmonic polynomial inclusion used in the spherical-code argument. -/
def rootJointHarmonicPolynomialInclusion {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootPolynomialChain r n k where
  toFun f S :=
    if h : ∀ i, 0 ≤ signedRootWeight lam S.val i then
      ((f ⟨S, h⟩).val : PolynomialSpace r n)
    else 0
  map_add' f g := by
    funext S
    dsimp
    split_ifs <;> simp
  map_smul' c f := by
    funext S
    dsimp
    split_ifs <;> simp

@[simp] theorem rootJointHarmonicPolynomialInclusion_apply_admissible
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    rootJointHarmonicPolynomialInclusion n lam k f S.val =
      ((f S).val : PolynomialSpace r n) := by
  simp only [rootJointHarmonicPolynomialInclusion, LinearMap.coe_mk, AddHom.coe_mk, S.property,
    implies_true, ↓reduceDIte]

theorem rootJointHarmonicPolynomialInclusion_injective
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    Function.Injective (rootJointHarmonicPolynomialInclusion n lam k) := by
  intro f g hfg
  funext S
  apply Subtype.ext
  apply Subtype.ext
  have h := congrFun hfg S.val
  simpa only [rootJointHarmonicPolynomialInclusion_apply_admissible]
    using h

theorem positiveRootOperator_eq_zero_of_inadmissible_target
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (T : RootWedge r k)
    (hT : ¬∀ i, 0 ≤ signedRootWeight lam T.val i)
    (α : PositiveRoot r) (hα : α ∉ T.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val) i)
    (p : JointHarmonicWeightSpace n
      (rootWedgeWeight lam
        ⟨rootWedgeInsert T α hα, hadm⟩)) :
    positiveRootOperator n α (p.val : PolynomialSpace r n) = 0 := by
  classical
  push Not at hT
  obtain ⟨i, hi⟩ := hT
  have hins := signedRootWeight_insert lam T.val α hα i
  have hsource := hadm i
  have hfirst : i = positiveRootFirst α := by
    by_contra hne
    have hcharge : rootCharge α i ≤ 0 := by
      unfold rootCharge
      rw [ite_eq_right hne]
      split_ifs <;> omega
    omega
  subst i
  rw [rootCharge_first] at hins
  have hdegree :
      rootWedgeWeight lam
        ⟨rootWedgeInsert T α hα, hadm⟩
          (positiveRootFirst α) = 0 := by
    have hcast := rootWedgeWeight_cast lam
      (⟨rootWedgeInsert T α hα, hadm⟩ :
        AdmissibleRootWedge lam (k + 1))
      (positiveRootFirst α)
    change
      (rootWedgeWeight lam
        (⟨rootWedgeInsert T α hα, hadm⟩ :
          AdmissibleRootWedge lam (k + 1))
        (positiveRootFirst α) : ℤ) =
        signedRootWeight lam (insert α T.val)
          (positiveRootFirst α) at hcast
    omega
  exact youngMultihomogeneous_polarization_eq_zero_of_rowDegree_zero
    (rootWedgeWeight lam ⟨rootWedgeInsert T α hα, hadm⟩)
    p.val (positiveRootSecond α) (positiveRootFirst α) hdegree

private theorem weightedExteriorRootEdge_polynomial_metriccodes2_04385d3c {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (p : JointHarmonicWeightSpace n
      (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm))) :
    (((weightedExteriorRootEdge n lam T α hα hadm p).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam T)) :
      PolynomialSpace r n) =
        positiveRootOperator n α (p.val : PolynomialSpace r n) := by
  change
    (((jointHarmonicWeightCast n
      (lowerRootWeight
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α)
      (rootWedgeWeight lam T)
      (rootAdmissibleInsert_lowerRootWeight lam T α hα hadm)
      (weightedPositiveRootOperator n
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α
        (rootAdmissibleInsert_first_pos lam T α hα hadm) p)).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam T)) :
      PolynomialSpace r n) = _
  rw [jointHarmonicWeightCast_coe]
  rfl

theorem rootJointHarmonicPolynomialInclusion_action_intertwines
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    (rootJointHarmonicPolynomialInclusion n lam k).comp
        (weightedExteriorActionDifferential n lam k) =
      (rootActionBoundary r n k).comp
        (rootJointHarmonicPolynomialInclusion n lam (k + 1)) := by
  classical
  apply LinearMap.ext
  intro f
  funext T
  simp only [LinearMap.comp_apply]
  by_cases hT : ∀ i, 0 ≤ signedRootWeight lam T.val i
  · let U : AdmissibleRootWedge lam k := ⟨T, hT⟩
    change
      (if h : ∀ i, 0 ≤ signedRootWeight lam T.val i then
        (((weightedExteriorActionDifferential n lam k f
            (⟨T, h⟩ : AdmissibleRootWedge lam k)).val :
          youngMultihomogeneousSubmodule n
            (rootWedgeWeight lam (⟨T, h⟩ : AdmissibleRootWedge lam k))) :
          PolynomialSpace r n)
      else 0) = _
    rw [dite_eq_left hT]
    change
      (((weightedExteriorActionDifferential n lam k f U).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam U)) :
          PolynomialSpace r n) =
        rootActionBoundary r n k
          (rootJointHarmonicPolynomialInclusion n lam (k + 1) f) T
    rw [weightedExteriorActionDifferential_apply,
      rootActionBoundary_apply]
    simp only [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs with hα hadm
    · simp only [ZeroMemClass.coe_zero]
    · simp only [Submodule.coe_smul,
        weightedExteriorRootEdge_polynomial_metriccodes2_04385d3c]
      change _ =
        realExteriorRootSign (insert α T.val) α •
          positiveRootOperator n α
            (if h : ∀ i, 0 ≤ signedRootWeight lam
              (insert α T.val) i then
              ((f ⟨rootWedgeInsert T α hα, h⟩).val :
                PolynomialSpace r n)
            else 0)
      rw [dite_eq_left hadm]
      rfl
    · change (0 : PolynomialSpace r n) =
        realExteriorRootSign (insert α T.val) α •
          positiveRootOperator n α
            (if h : ∀ i, 0 ≤ signedRootWeight lam
              (insert α T.val) i then
              ((f ⟨rootWedgeInsert T α hα, h⟩).val :
                PolynomialSpace r n)
            else 0)
      rw [dite_eq_right hadm, map_zero, smul_zero]
  · change
      (if h : ∀ i, 0 ≤ signedRootWeight lam T.val i then
        (((weightedExteriorActionDifferential n lam k f
            (⟨T, h⟩ : AdmissibleRootWedge lam k)).val :
          youngMultihomogeneousSubmodule n
            (rootWedgeWeight lam (⟨T, h⟩ : AdmissibleRootWedge lam k))) :
          PolynomialSpace r n)
      else 0) =
        rootActionBoundary r n k
          (rootJointHarmonicPolynomialInclusion n lam (k + 1) f) T
    rw [dite_eq_right hT]
    rw [rootActionBoundary_apply]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro α _
    split_ifs with hα
    · rfl
    · by_cases hadm : ∀ i, 0 ≤ signedRootWeight lam
          (insert α T.val) i
      · have hzero := positiveRootOperator_eq_zero_of_inadmissible_target
          lam T hT α hα hadm
          (f ⟨rootWedgeInsert T α hα, hadm⟩)
        simp only [rootJointHarmonicPolynomialInclusion, LinearMap.coe_mk, AddHom.coe_mk,
          rootWedgeInsert_val, hadm, implies_true, ↓reduceDIte, hzero, smul_zero]
      · simp only [rootJointHarmonicPolynomialInclusion, LinearMap.coe_mk, AddHom.coe_mk,
          rootWedgeInsert_val, hadm, ↓reduceDIte, map_zero, smul_zero]

theorem rootJointHarmonicPolynomialInclusion_bracket_intertwines
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    (rootJointHarmonicPolynomialInclusion n lam k).comp
        (weightedRootBracketBoundary n lam k) =
      (rootBracketBoundary r n k).comp
        (rootJointHarmonicPolynomialInclusion n lam (k + 1)) := by
  classical
  apply LinearMap.ext
  intro f
  funext T
  simp only [LinearMap.comp_apply]
  let P : RootWedge r (k + 1) → Prop :=
    fun S => ∀ i, 0 ≤ signedRootWeight lam S.val i
  let F : RootWedge r (k + 1) → PolynomialSpace r n :=
    fun S =>
      if h : P S then
        rootBracketBoundaryCoefficient S T •
          ((f (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1))).val :
            PolynomialSpace r n)
      else 0
  by_cases hT : ∀ i, 0 ≤ signedRootWeight lam T.val i
  · let U : AdmissibleRootWedge lam k := ⟨T, hT⟩
    change
      (if h : ∀ i, 0 ≤ signedRootWeight lam T.val i then
        (((weightedRootBracketBoundary n lam k f
            (⟨T, h⟩ : AdmissibleRootWedge lam k)).val :
          youngMultihomogeneousSubmodule n
            (rootWedgeWeight lam (⟨T, h⟩ :
              AdmissibleRootWedge lam k))) : PolynomialSpace r n)
      else 0) = _
    rw [dite_eq_left hT, weightedRootBracketBoundary_apply,
      rootBracketBoundary_apply]
    simp only [Submodule.coe_sum]
    have hleft :
        (∑ S : AdmissibleRootWedge lam (k + 1),
          (((if h : rootBracketBoundaryCoefficient S.val U.val = 0 then 0
              else rootBracketBoundaryCoefficient S.val U.val •
                weightedRootBracketEdge n lam S U h (f S)).val :
            youngMultihomogeneousSubmodule n (rootWedgeWeight lam U)) :
            PolynomialSpace r n)) =
          ∑ S : AdmissibleRootWedge lam (k + 1), F S.val := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hcoeff : rootBracketBoundaryCoefficient S.val U.val = 0
      · have hcoeff' : rootBracketBoundaryCoefficient S.val T = 0 := by
          simpa only using hcoeff
        simp only [hcoeff, ↓reduceDIte, ZeroMemClass.coe_zero, S.property, implies_true, hcoeff',
          zero_smul, F, P]
      · simp only [hcoeff, ↓reduceDIte, SetLike.val_smul, weightedRootBracketEdge_coe, S.property,
          implies_true, U, F, P]
    rw [hleft]
    change
      (∑ S : {S : RootWedge r (k + 1) // P S}, F S.val) =
        ∑ S : RootWedge r (k + 1),
          rootBracketBoundaryCoefficient S T •
            (rootJointHarmonicPolynomialInclusion n lam (k + 1) f S)
    calc
      (∑ S : {S : RootWedge r (k + 1) // P S}, F S.val) =
          ∑ S ∈ Finset.univ.filter P, F S :=
        (Finset.sum_subtype (Finset.univ.filter P) (by simp only [Finset.mem_filter,
                                                         Finset.mem_univ, true_and,
                                                           implies_true]) F).symm
      _ = ∑ S : RootWedge r (k + 1), F S := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : P S
        · rw [ite_eq_left hS]
        · rw [ite_eq_right hS]
          simp only [hS, ↓reduceDIte, F]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : P S
        · change
            (if h : P S then
              rootBracketBoundaryCoefficient S T •
                ((f (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1))).val :
                  PolynomialSpace r n)
            else 0) =
              rootBracketBoundaryCoefficient S T •
                (if h : P S then
                  ((f (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1))).val :
                    PolynomialSpace r n)
                else 0)
          simp only [dite_eq_left hS]
        · simp only [hS, ↓reduceDIte, rootJointHarmonicPolynomialInclusion, LinearMap.coe_mk,
            AddHom.coe_mk, smul_zero, F, P]
  · change
      (if h : ∀ i, 0 ≤ signedRootWeight lam T.val i then
        (((weightedRootBracketBoundary n lam k f
            (⟨T, h⟩ : AdmissibleRootWedge lam k)).val :
          youngMultihomogeneousSubmodule n
            (rootWedgeWeight lam (⟨T, h⟩ :
              AdmissibleRootWedge lam k))) : PolynomialSpace r n)
      else 0) = _
    rw [dite_eq_right hT, rootBracketBoundary_apply]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro S _
    by_cases hS : ∀ i, 0 ≤ signedRootWeight lam S.val i
    · have hcoeff : rootBracketBoundaryCoefficient S T = 0 := by
        by_contra hnonzero
        apply hT
        intro i
        rw [← signedRootWeight_eq_of_bracketBoundaryCoefficient_ne_zero
          lam S T hnonzero i]
        exact hS i
      simp only [hcoeff, zero_smul]
    · simp only [rootJointHarmonicPolynomialInclusion, LinearMap.coe_mk, AddHom.coe_mk, hS,
        ↓reduceDIte, smul_zero]

theorem rootJointHarmonicPolynomialInclusion_chevalley_intertwines
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    (rootJointHarmonicPolynomialInclusion n lam k).comp
        (weightedChevalleyEilenbergDifferential n lam k) =
      (rootChevalleyEilenbergBoundary r n k).comp
        (rootJointHarmonicPolynomialInclusion n lam (k + 1)) := by
  rw [weightedChevalleyEilenbergDifferential,
    rootChevalleyEilenbergBoundary,
    LinearMap.comp_add, LinearMap.add_comp,
    rootJointHarmonicPolynomialInclusion_action_intertwines,
    rootJointHarmonicPolynomialInclusion_bracket_intertwines]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The positive root order code used in the spherical-code argument. -/
def positiveRootOrderCode {r : ℕ} (α : PositiveRoot r) :
    Fin ((r + 1) * (r + 1)) :=
  (finProdFinEquiv (m := r + 1) (n := r + 1)) α.val

theorem sum_offDiagonal_eq_sum_orderedPairs
    {ι κ M : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder κ]
    [AddCommMonoid M] (key : ι → κ) (hkey : Function.Injective key)
    (F : ι → ι → M) :
    (∑ a : ι, ∑ b : ι, if a = b then 0 else F a b) =
      ∑ a : ι, ∑ b : ι,
        if key a < key b then F a b + F b a else 0 := by
  classical
  have hsplit : ∀ a b : ι,
      (if a = b then 0 else F a b) =
        (if key a < key b then F a b else 0) +
          (if key b < key a then F a b else 0) := by
    intro a b
    rcases lt_trichotomy (key a) (key b) with hab | hab | hab
    · have hne : a ≠ b := by
        intro hab'
        exact (lt_irrefl _ (hab' ▸ hab))
      simp only [hne, ↓reduceIte, hab, not_lt_of_gt hab, add_zero]
    · have hab' : a = b := hkey hab
      subst b
      simp only [↓reduceIte, lt_self_iff_false, add_zero]
    · have hne : a ≠ b := by
        intro hab'
        exact (lt_irrefl _ (hab' ▸ hab))
      simp only [hne, ↓reduceIte, not_lt_of_gt hab, hab, zero_add]
  have hswap :
      (∑ a : ι, ∑ b : ι, if key b < key a then F a b else 0) =
        ∑ a : ι, ∑ b : ι, if key a < key b then F b a else 0 := by
    rw [Finset.sum_comm]
  calc
    (∑ a : ι, ∑ b : ι, if a = b then 0 else F a b) =
        ∑ a : ι, ∑ b : ι,
          ((if key a < key b then F a b else 0) +
            (if key b < key a then F a b else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact hsplit a b
    _ = (∑ a : ι, ∑ b : ι, if key a < key b then F a b else 0) +
        (∑ a : ι, ∑ b : ι, if key b < key a then F a b else 0) := by
      simp_rw [Finset.sum_add_distrib]
    _ = (∑ a : ι, ∑ b : ι, if key a < key b then F a b else 0) +
        (∑ a : ι, ∑ b : ι, if key a < key b then F b a else 0) := by
      rw [hswap]
    _ = ∑ a : ι, ∑ b : ι,
        if key a < key b then F a b + F b a else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

variable {ι M : Type*} [LinearOrder ι]
variable [AddCommGroup M] [Module ℝ M]

theorem realExteriorRootSign_mul_self (S : Finset ι) (a : ι) :
    realExteriorRootSign S a * realExteriorRootSign S a = 1 := by
  unfold realExteriorRootSign exteriorRootSign
  push_cast
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The actual exterior root contraction used in the spherical-code argument. -/
def actualExteriorRootContraction (M : Type*)
    [AddCommGroup M] [Module ℝ M] (a : ι) :
    Module.End ℝ (Finset ι → M) where
  toFun f S :=
    if a ∈ S then 0
    else realExteriorRootSign (insert a S) a • f (insert a S)
  map_add' f g := by
    funext S
    by_cases h : a ∈ S <;> simp [h, smul_add]
  map_smul' c f := by
    funext S
    by_cases h : a ∈ S <;> simp [h, smul_smul, mul_comm]

/-- The actual exterior root creation used in the spherical-code argument. -/
def actualExteriorRootCreation (M : Type*)
    [AddCommGroup M] [Module ℝ M] (a : ι) :
    Module.End ℝ (Finset ι → M) where
  toFun f S :=
    if a ∈ S then realExteriorRootSign S a • f (S.erase a)
    else 0
  map_add' f g := by
    funext S
    by_cases h : a ∈ S <;> simp [h, smul_add]
  map_smul' c f := by
    funext S
    by_cases h : a ∈ S <;> simp [h, smul_smul, mul_comm]

@[simp] theorem actualExteriorRootContraction_apply (a : ι)
    (f : Finset ι → M) (S : Finset ι) :
    actualExteriorRootContraction M a f S =
      if a ∈ S then 0
      else realExteriorRootSign (insert a S) a • f (insert a S) := rfl

@[simp] theorem actualExteriorRootCreation_apply (a : ι)
    (f : Finset ι → M) (S : Finset ι) :
    actualExteriorRootCreation M a f S =
      if a ∈ S then realExteriorRootSign S a • f (S.erase a)
      else 0 := rfl

theorem realExteriorRootSign_insert_insert_anticommute
    (S : Finset ι) (a b : ι)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) :
    realExteriorRootSign (insert a S) a *
        realExteriorRootSign (insert b (insert a S)) b =
      -(realExteriorRootSign (insert b S) b *
        realExteriorRootSign (insert a (insert b S)) a) := by
  let U : Finset ι := insert b (insert a S)
  have hUa : a ∈ U := by simp only [Finset.mem_insert, true_or, or_true, U]
  have hUb : b ∈ U := by simp only [Finset.mem_insert, true_or, U]
  have heraseb : U.erase b = insert a S := by
    ext z
    simp only [U, Finset.mem_erase, Finset.mem_insert]
    aesop
  have herasea : U.erase a = insert b S := by
    ext z
    simp only [U, Finset.mem_erase, Finset.mem_insert]
    aesop
  have hanti := realExteriorRootSign_erase_anticommute
    U hUb hUa hab.symm
  rw [heraseb, herasea] at hanti
  have hUa' : realExteriorRootSign U a =
      realExteriorRootSign (insert a (insert b S)) a := by
    congr 1
    exact Finset.insert_comm b a S
  rw [hUa'] at hanti
  linarith

theorem realExteriorRootSign_insert_erase_anticommute
    (S : Finset ι) (a b : ι)
    (ha : a ∉ S) (hb : b ∈ S) (hab : a ≠ b) :
    realExteriorRootSign (insert a S) a *
        realExteriorRootSign (insert a S) b =
      -(realExteriorRootSign S b *
        realExteriorRootSign (insert a (S.erase b)) a) := by
  let U : Finset ι := insert a S
  have hUa : a ∈ U := by simp only [Finset.mem_insert, true_or, U]
  have hUb : b ∈ U := by simp only [Finset.mem_insert, hb, or_true, U]
  have herasea : U.erase a = S := by
    simpa [U] using ha
  have heraseb : U.erase b = insert a (S.erase b) := by
    ext z
    simp only [U, Finset.mem_erase, Finset.mem_insert]
    aesop
  have hanti := realExteriorRootSign_erase_anticommute
    U hUa hUb hab
  rw [herasea, heraseb] at hanti
  have hsquareS := realExteriorRootSign_mul_self S b
  have hsquareU := realExteriorRootSign_mul_self U b
  dsimp [U] at hanti hsquareU
  calc
    realExteriorRootSign (insert a S) a *
        realExteriorRootSign (insert a S) b =
        (realExteriorRootSign (insert a S) a *
          realExteriorRootSign S b) *
            (realExteriorRootSign S b *
              realExteriorRootSign (insert a S) b) := by
      calc
        _ = realExteriorRootSign (insert a S) a *
              (realExteriorRootSign S b * realExteriorRootSign S b) *
                realExteriorRootSign (insert a S) b := by
          rw [hsquareS]
          ring
        _ = _ := by ring
    _ = -(realExteriorRootSign (insert a S) b *
          realExteriorRootSign (insert a (S.erase b)) a) *
            (realExteriorRootSign S b *
              realExteriorRootSign (insert a S) b) := by
      rw [hanti]
    _ = -(realExteriorRootSign S b *
          realExteriorRootSign (insert a (S.erase b)) a) *
            (realExteriorRootSign (insert a S) b *
              realExteriorRootSign (insert a S) b) := by ring
    _ = -(realExteriorRootSign S b *
        realExteriorRootSign (insert a (S.erase b)) a) := by
      rw [hsquareU]
      ring

theorem actualExteriorRootContraction_anticommute (a b : ι) :
    actualExteriorRootContraction M a *
        actualExteriorRootContraction M b +
      actualExteriorRootContraction M b *
        actualExteriorRootContraction M a = 0 := by
  classical
  ext f S
  change
    actualExteriorRootContraction M a
        (actualExteriorRootContraction M b f) S +
      actualExteriorRootContraction M b
        (actualExteriorRootContraction M a f) S = 0
  by_cases hab : a = b
  · subst b
    by_cases ha : a ∈ S <;>
      simp [actualExteriorRootContraction_apply, ha]
  · have hba : b ≠ a := Ne.symm hab
    by_cases ha : a ∈ S
    · simp only [actualExteriorRootContraction_apply, ha, ↓reduceIte, Finset.mem_insert, hab,
        or_true, smul_zero, ite_self, add_zero]
    · by_cases hb : b ∈ S
      · simp only [actualExteriorRootContraction_apply, ha, ↓reduceIte, Finset.mem_insert, hba, hb,
          or_true, smul_zero, add_zero]
      · have hsign :=
          realExteriorRootSign_insert_insert_anticommute
            S a b ha hb hab
        have hset : insert b (insert a S) = insert a (insert b S) :=
          Finset.insert_comm b a S
        simp only [actualExteriorRootContraction_apply,
          Finset.mem_insert, ha, hb, hab, hba,
          false_or, ↓reduceIte, smul_smul]
        rw [hset]
        rw [hset] at hsign
        rw [hsign, neg_smul]
        exact neg_add_cancel _

theorem actualExteriorRootContraction_creation_anticommute
    (a b : ι) :
    actualExteriorRootContraction M a *
        actualExteriorRootCreation M b +
      actualExteriorRootCreation M b *
        actualExteriorRootContraction M a =
      if a = b then 1 else 0 := by
  classical
  ext f S
  by_cases hab : a = b
  · subst b
    simp only []
    change
      actualExteriorRootContraction M a
          (actualExteriorRootCreation M a f) S +
        actualExteriorRootCreation M a
          (actualExteriorRootContraction M a f) S = f S
    by_cases ha : a ∈ S
    · simp only [actualExteriorRootContraction_apply, ha, ↓reduceIte,
        actualExteriorRootCreation_apply, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
        Finset.insert_erase ha, smul_smul, realExteriorRootSign_mul_self, one_smul, zero_add]
    · simp only [actualExteriorRootContraction_apply, ha, ↓reduceIte,
        actualExteriorRootCreation_apply, Finset.mem_insert, or_false, Finset.erase_insert ha,
        smul_smul, realExteriorRootSign_mul_self, one_smul, add_zero]
  · have hba : b ≠ a := Ne.symm hab
    simp only [ite_eq_right hab, LinearMap.zero_apply]
    change
      actualExteriorRootContraction M a
          (actualExteriorRootCreation M b f) S +
        actualExteriorRootCreation M b
          (actualExteriorRootContraction M a f) S = 0
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S <;>
        simp [actualExteriorRootContraction_apply,
          actualExteriorRootCreation_apply, ha, hb,
          Finset.mem_erase, hab]
    · by_cases hb : b ∈ S
      · have hsign := realExteriorRootSign_insert_erase_anticommute
          S a b ha hb hab
        have herase : (insert a S).erase b = insert a (S.erase b) :=
          Finset.erase_insert_of_ne hab
        simp only [actualExteriorRootContraction_apply,
          actualExteriorRootCreation_apply, Finset.mem_insert,
          Finset.mem_erase, ha, hb, hba,
          false_or, ↓reduceIte, smul_smul]
        rw [herase, hsign, neg_smul]
        simp only [and_false, ↓reduceIte, smul_smul]
        exact neg_add_cancel
          ((realExteriorRootSign S b *
            realExteriorRootSign (insert a (S.erase b)) a) •
              f (insert a (S.erase b)))
      · simp only [actualExteriorRootContraction_apply, ha, ↓reduceIte,
          actualExteriorRootCreation_apply, Finset.mem_insert, hba, hb, or_self, smul_zero,
          add_zero]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootAdmissibleErase_nonnegative_iff_first_pos
    {r k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (α : PositiveRoot r) (hα : α ∈ S.val.val) :
    (∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i) ↔
      0 < rootWedgeWeight lam S (positiveRootFirst α) := by
  constructor
  · intro h
    have hfirst := h (positiveRootFirst α)
    rw [signedRootWeight_erase lam S.val.val α hα,
      rootCharge_first] at hfirst
    have hcast := rootWedgeWeight_cast lam S (positiveRootFirst α)
    omega
  · intro hpos i
    rw [signedRootWeight_erase lam S.val.val α hα]
    by_cases hfirst : i = positiveRootFirst α
    · subst i
      rw [rootCharge_first]
      have hcast := rootWedgeWeight_cast lam S (positiveRootFirst α)
      omega
    · unfold rootCharge
      rw [ite_eq_right hfirst]
      split_ifs <;> have hnonneg := S.property i <;> omega

theorem rootAdmissibleInsert_nonnegative_iff_second_pos
    {r k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (β : PositiveRoot r) (hβ : β ∉ S.val.val) :
    (∀ i, 0 ≤ signedRootWeight lam (insert β S.val.val) i) ↔
      0 < rootWedgeWeight lam S (positiveRootSecond β) := by
  constructor
  · intro h
    have hsecond := h (positiveRootSecond β)
    rw [signedRootWeight_insert lam S.val.val β hβ,
      rootCharge_second] at hsecond
    have hcast := rootWedgeWeight_cast lam S (positiveRootSecond β)
    omega
  · intro hpos i
    rw [signedRootWeight_insert lam S.val.val β hβ]
    by_cases hsecond : i = positiveRootSecond β
    · subst i
      rw [rootCharge_second]
      have hcast := rootWedgeWeight_cast lam S (positiveRootSecond β)
      omega
    · unfold rootCharge
      split_ifs with hfirst <;>
        have hnonneg := S.property i <;> omega

theorem rootSwapExteriorActionPathSigns_anticommute
    {r : ℕ} (S : Finset (PositiveRoot r))
    (α β : PositiveRoot r) (hα : α ∈ S) (hβ : β ∉ S) :
    realExteriorRootSign (insert β S) β *
        realExteriorRootSign (insert β S) α =
      -(realExteriorRootSign S α *
        realExteriorRootSign (insert β (S.erase α)) β) := by
  have hne : β ≠ α := by
    intro h
    subst β
    exact hβ hα
  classical
  convert realExteriorRootSign_insert_erase_anticommute S β α hβ hα hne using 1
  · congr 1
    · apply congrArg (fun U : Finset (PositiveRoot r) =>
        realExteriorRootSign U β)
      ext z
      simp only [Finset.mem_insert]
    · apply congrArg (fun U : Finset (PositiveRoot r) =>
        realExteriorRootSign U α)
      ext z
      simp only [Finset.mem_insert]
  · congr 1
    congr 1
    apply congrArg (fun U : Finset (PositiveRoot r) =>
      realExteriorRootSign U β)
    ext z
    simp only [Finset.mem_insert, Finset.mem_erase, ne_eq]

theorem rootSwap_twoActionPaths_eq_signed_commutator
    {r n : ℕ} (S : Finset (PositiveRoot r))
    (α β : PositiveRoot r) (hα : α ∈ S) (hβ : β ∉ S)
    (p : PolynomialSpace r n) :
    (realExteriorRootSign S α *
        realExteriorRootSign (insert β (S.erase α)) β) •
          positiveRootUpperOperator n α (positiveRootOperator n β p) +
      (realExteriorRootSign (insert β S) β *
        realExteriorRootSign (insert β S) α) •
          positiveRootOperator n β (positiveRootUpperOperator n α p) =
      (realExteriorRootSign S α *
        realExteriorRootSign (insert β (S.erase α)) β) •
          (((positiveRootUpperOperator n α).comp
            (positiveRootOperator n β) -
          (positiveRootOperator n β).comp
            (positiveRootUpperOperator n α)) p) := by
  rw [rootSwapExteriorActionPathSigns_anticommute S α β hα hβ]
  change
    (realExteriorRootSign S α *
        realExteriorRootSign (insert β (S.erase α)) β) •
          positiveRootUpperOperator n α (positiveRootOperator n β p) +
      (-(realExteriorRootSign S α *
        realExteriorRootSign (insert β (S.erase α)) β)) •
          positiveRootOperator n β (positiveRootUpperOperator n α p) =
      (realExteriorRootSign S α *
        realExteriorRootSign (insert β (S.erase α)) β) •
        (positiveRootUpperOperator n α (positiveRootOperator n β p) -
          positiveRootOperator n β (positiveRootUpperOperator n α p))
  rw [neg_smul, smul_sub, sub_eq_add_neg]

theorem rootSwap_twoActionPaths_eq_signed_structureRoots
    {r n : ℕ} (S : Finset (PositiveRoot r))
    (α β : PositiveRoot r) (hα : α ∈ S) (hβ : β ∉ S)
    (p : PolynomialSpace r n) :
    (realExteriorRootSign S α *
        realExteriorRootSign (insert β (S.erase α)) β) •
          positiveRootUpperOperator n α (positiveRootOperator n β p) +
      (realExteriorRootSign (insert β S) β *
        realExteriorRootSign (insert β S) α) •
          positiveRootOperator n β (positiveRootUpperOperator n α p) =
      (realExteriorRootSign S α *
        realExteriorRootSign (insert β (S.erase α)) β) •
        ((∑ γ : PositiveRoot r,
          rootStructureConstant β γ α • positiveRootUpperOperator n γ) p +
        (∑ γ : PositiveRoot r,
          rootStructureConstant α γ β • positiveRootOperator n γ) p) := by
  rw [rootSwap_twoActionPaths_eq_signed_commutator S α β hα hβ]
  rw [positiveRootUpper_lower_commutator_eq_cartan_add_bracket]
  have hne : α ≠ β := by
    intro h
    subst β
    exact hβ hα
  simp only [hne, ↓reduceIte, zero_add, LinearMap.add_apply, LinearMap.coe_sum, LinearMap.coe_smul,
    Finset.sum_apply, Pi.smul_apply, positiveRootUpperOperator_apply, polarization_apply,
    positiveRootOperator_apply, smul_add]

theorem rootPolynomialActionCoboundaryDifferentialIncidence_diag
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1))
    (α : PositiveRoot r) :
    rootPolynomialActionCoboundaryDifferentialIncidence lam f S α α =
      if α ∈ S.val.val then
        if 0 < rootWedgeWeight lam S (positiveRootFirst α) then
          polarization r n (positiveRootFirst α) (positiveRootSecond α)
            (polarization r n (positiveRootSecond α) (positiveRootFirst α)
              ((f S).val : PolynomialSpace r n))
        else 0
      else 0 := by
  classical
  by_cases hα : α ∈ S.val.val
  · by_cases hpos : 0 < rootWedgeWeight lam S (positiveRootFirst α)
    · have herase : ∀ i,
          0 ≤ signedRootWeight lam (S.val.val.erase α) i :=
        (rootAdmissibleErase_nonnegative_iff_first_pos lam S α hα).2 hpos
      have hnot : α ∉ (rootAdmissibleErase lam S α hα herase).val.val := by
        simp only [rootAdmissibleErase_val, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
          not_false_eq_true]
      have hins : ∀ i,
          0 ≤ signedRootWeight lam
            (insert α (rootAdmissibleErase lam S α hα herase).val.val) i := by
        simpa only [rootAdmissibleErase_val, Finset.insert_erase hα] using S.property
      have hround :
          rootAdmissibleInsert lam
            (rootAdmissibleErase lam S α hα herase) α hnot hins = S := by
        apply Subtype.ext
        apply Subtype.ext
        exact Finset.insert_erase hα
      have hsign :
          realExteriorRootSign S.val.val α *
              realExteriorRootSign
                (insert α
                  (rootAdmissibleErase lam S α hα herase).val.val) α = 1 := by
        simpa only [rootAdmissibleErase_val,
          Finset.insert_erase hα] using realExteriorRootSign_mul_self S.val.val α
      simp only [rootPolynomialActionCoboundaryDifferentialIncidence,
        dite_eq_left hα, dite_eq_left herase, dite_eq_right hnot, dite_eq_left hins,
        hsign, one_smul, ite_eq_left hα, ite_eq_left hpos]
      rw [hround]
    · have herase : ¬∀ i,
          0 ≤ signedRootWeight lam (S.val.val.erase α) i := by
        simpa only [rootAdmissibleErase_nonnegative_iff_first_pos lam S α hα, not_lt,
          nonpos_iff_eq_zero] using hpos
      simp only [rootPolynomialActionCoboundaryDifferentialIncidence, hα, ↓reduceDIte, herase,
        ↓reduceIte, hpos]
  · simp only [rootPolynomialActionCoboundaryDifferentialIncidence, hα, ↓reduceDIte, ↓reduceIte]

theorem rootPolynomialActionDifferentialCoboundaryIncidence_diag
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1))
    (α : PositiveRoot r) :
    rootPolynomialActionDifferentialCoboundaryIncidence lam f S α α =
      if α ∈ S.val.val then 0
      else if 0 < rootWedgeWeight lam S (positiveRootSecond α) then
        polarization r n (positiveRootSecond α) (positiveRootFirst α)
          (polarization r n (positiveRootFirst α) (positiveRootSecond α)
            ((f S).val : PolynomialSpace r n))
      else 0 := by
  classical
  by_cases hα : α ∈ S.val.val
  · simp only [rootPolynomialActionDifferentialCoboundaryIncidence, hα, ↓reduceDIte, ↓reduceIte]
  · by_cases hpos : 0 < rootWedgeWeight lam S (positiveRootSecond α)
    · have hins : ∀ i,
          0 ≤ signedRootWeight lam (insert α S.val.val) i :=
        (rootAdmissibleInsert_nonnegative_iff_second_pos lam S α hα).2 hpos
      have hmem : α ∈ (rootAdmissibleInsert lam S α hα hins).val.val := by
        simp only [rootAdmissibleInsert_val, Finset.mem_insert, true_or]
      have herase : ∀ i,
          0 ≤ signedRootWeight lam
            (((rootAdmissibleInsert lam S α hα hins).val.val).erase α) i := by
        simpa only [rootAdmissibleInsert_val, Finset.erase_insert hα] using S.property
      have hround :
          rootAdmissibleErase lam
            (rootAdmissibleInsert lam S α hα hins) α hmem herase = S := by
        apply Subtype.ext
        apply Subtype.ext
        exact Finset.erase_insert hα
      have hsign :
          realExteriorRootSign (insert α S.val.val) α *
              realExteriorRootSign
                (rootAdmissibleInsert lam S α hα hins).val.val α = 1 := by
        exact realExteriorRootSign_mul_self (insert α S.val.val) α
      simp only [rootPolynomialActionDifferentialCoboundaryIncidence,
        dite_eq_right hα, dite_eq_left hins, dite_eq_left hmem, dite_eq_left herase,
        hsign, one_smul, ite_eq_right hα, ite_eq_left hpos]
      rw [hround]
    · have hins : ¬∀ i,
          0 ≤ signedRootWeight lam (insert α S.val.val) i := by
        simpa only [rootAdmissibleInsert_nonnegative_iff_second_pos lam S α hα, not_lt,
          nonpos_iff_eq_zero] using hpos
      simp only [rootPolynomialActionDifferentialCoboundaryIncidence, hα, ↓reduceDIte, hins,
        ↓reduceIte, hpos]

theorem rootPolynomialActionHodgeDiagonalIncidence_eq_positive_root_sums
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) :
    rootPolynomialActionHodgeDiagonalIncidence lam f S =
      (∑ α : PositiveRoot r,
        if α ∈ S.val.val then
          if 0 < rootWedgeWeight lam S (positiveRootFirst α) then
            polarization r n (positiveRootFirst α) (positiveRootSecond α)
              (polarization r n (positiveRootSecond α) (positiveRootFirst α)
                ((f S).val : PolynomialSpace r n))
          else 0
        else 0) +
      (∑ α : PositiveRoot r,
        if α ∈ S.val.val then 0
        else if 0 < rootWedgeWeight lam S (positiveRootSecond α) then
          polarization r n (positiveRootSecond α) (positiveRootFirst α)
            (polarization r n (positiveRootFirst α) (positiveRootSecond α)
              ((f S).val : PolynomialSpace r n))
        else 0) := by
  classical
  unfold rootPolynomialActionHodgeDiagonalIncidence
  simp_rw [rootPolynomialActionCoboundaryDifferentialIncidence_diag,
    rootPolynomialActionDifferentialCoboundaryIncidence_diag]
  rw [Finset.sum_add_distrib]

theorem rootPolynomialActionHodgeDiagonalIncidence_eq_hodgeDiagonal_apply_coe
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) :
    rootPolynomialActionHodgeDiagonalIncidence lam f S =
      (((rootJointHarmonicHodgeDiagonal n lam (k + 1) f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) := by
  rw [rootPolynomialActionHodgeDiagonalIncidence_eq_positive_root_sums,
    rootPolynomialIncludedActionHodgeDiagonal_eq_subtype_sums lam S (f S),
    rootPolynomialExcludedActionHodgeDiagonal_eq_subtype_sum lam S (f S),
    rootJointHarmonicHodgeDiagonal_apply_coe]

theorem weightedExteriorActionHodge_apply_coe_eq_hodgeDiagonal_add_offDiagonal
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) :
    (((((weightedExteriorActionCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedExteriorActionCoboundary n lam (k + 1))) f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
      (((rootJointHarmonicHodgeDiagonal n lam (k + 1) f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) +
      rootPolynomialActionHodgeOffDiagonalIncidence lam f S := by
  rw [weightedExteriorActionHodge_apply_coe_eq_diagonal_add_offDiagonal,
    rootPolynomialActionHodgeDiagonalIncidence_eq_hodgeDiagonal_apply_coe]

end

section


open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootAdmissibleSwap_first_eq_and_source_first_zero_of_inadmissible_erase
    {r k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (α β : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hbad : ¬∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i) :
    positiveRootFirst α = positiveRootFirst β ∧
      rootWedgeWeight lam
        (rootAdmissibleSwap lam S α β hα hβ hadm)
        (positiveRootFirst β) = 0 := by
  have hnotpos : ¬0 < rootWedgeWeight lam S (positiveRootFirst α) := by
    intro hpos
    exact hbad
      ((rootAdmissibleErase_nonnegative_iff_first_pos lam S α hα).2 hpos)
  have hsource : rootWedgeWeight lam S (positiveRootFirst α) = 0 := by
    omega
  have hcastS := rootWedgeWeight_cast lam S (positiveRootFirst α)
  have hcastU := rootWedgeWeight_cast lam
    (rootAdmissibleSwap lam S α β hα hβ hadm)
    (positiveRootFirst α)
  have hswap := signedRootWeight_admissibleSwap
    lam S α β hα hβ hadm (positiveRootFirst α)
  rw [rootCharge_first] at hswap
  have hfirst : positiveRootFirst α = positiveRootFirst β := by
    by_contra hne
    have hcharge : rootCharge β (positiveRootFirst α) ≤ 0 := by
      unfold rootCharge
      rw [ite_eq_right hne]
      split_ifs <;> omega
    omega
  refine ⟨hfirst, ?_⟩
  have hcharge : rootCharge β (positiveRootFirst α) = 1 := by
    rw [hfirst, rootCharge_first]
  have hzero : rootWedgeWeight lam
      (rootAdmissibleSwap lam S α β hα hβ hadm)
      (positiveRootFirst α) = 0 := by
    omega
  simpa only [hfirst] using hzero

theorem rootAdmissibleSwap_upper_lower_eq_zero_of_inadmissible_erase
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (α β : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hbad : ¬∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i)
    (p : JointHarmonicWeightSpace n
      (rootWedgeWeight lam
        (rootAdmissibleSwap lam S α β hα hβ hadm))) :
    positiveRootUpperOperator n α
      (positiveRootOperator n β (p.val : PolynomialSpace r n)) = 0 := by
  obtain ⟨_, hzero⟩ :=
    rootAdmissibleSwap_first_eq_and_source_first_zero_of_inadmissible_erase
      lam S α β hα hβ hadm hbad
  have hpolarization :=
    youngMultihomogeneous_polarization_eq_zero_of_rowDegree_zero
      (rootWedgeWeight lam
        (rootAdmissibleSwap lam S α β hα hβ hadm))
      p.val (positiveRootSecond β) (positiveRootFirst β) hzero
  change positiveRootUpperOperator n α
    (polarization r n (positiveRootSecond β)
      (positiveRootFirst β) (p.val : PolynomialSpace r n)) = 0
  rw [hpolarization, map_zero]

theorem rootAdmissibleSwap_second_eq_and_source_second_zero_of_inadmissible_insert
    {r k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (α β : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hbad : ¬∀ i, 0 ≤ signedRootWeight lam (insert β S.val.val) i) :
    positiveRootSecond α = positiveRootSecond β ∧
      rootWedgeWeight lam
        (rootAdmissibleSwap lam S α β hα hβ hadm)
        (positiveRootSecond α) = 0 := by
  have hnotpos : ¬0 < rootWedgeWeight lam S (positiveRootSecond β) := by
    intro hpos
    exact hbad
      ((rootAdmissibleInsert_nonnegative_iff_second_pos lam S β hβ).2 hpos)
  have hsource : rootWedgeWeight lam S (positiveRootSecond β) = 0 := by
    omega
  have hcastS := rootWedgeWeight_cast lam S (positiveRootSecond β)
  have hcastU := rootWedgeWeight_cast lam
    (rootAdmissibleSwap lam S α β hα hβ hadm)
    (positiveRootSecond β)
  have hswap := signedRootWeight_admissibleSwap
    lam S α β hα hβ hadm (positiveRootSecond β)
  rw [rootCharge_second] at hswap
  have hsecond : positiveRootSecond α = positiveRootSecond β := by
    by_contra hne
    have hcharge : 0 ≤ rootCharge α (positiveRootSecond β) := by
      unfold rootCharge
      split_ifs with hfirst hsecond
      · omega
      · exact False.elim (hne hsecond.symm)
      · omega
    omega
  refine ⟨hsecond, ?_⟩
  have hcharge : rootCharge α (positiveRootSecond β) = -1 := by
    rw [← hsecond, rootCharge_second]
  rw [hsecond]
  omega

theorem rootAdmissibleSwap_lower_upper_eq_zero_of_inadmissible_insert
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (α β : PositiveRoot r)
    (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i)
    (hbad : ¬∀ i, 0 ≤ signedRootWeight lam (insert β S.val.val) i)
    (p : JointHarmonicWeightSpace n
      (rootWedgeWeight lam
        (rootAdmissibleSwap lam S α β hα hβ hadm))) :
    positiveRootOperator n β
      (positiveRootUpperOperator n α (p.val : PolynomialSpace r n)) = 0 := by
  obtain ⟨_, hzero⟩ :=
    rootAdmissibleSwap_second_eq_and_source_second_zero_of_inadmissible_insert
      lam S α β hα hβ hadm hbad
  have hpolarization :=
    youngMultihomogeneous_polarization_eq_zero_of_rowDegree_zero
      (rootWedgeWeight lam
        (rootAdmissibleSwap lam S α β hα hβ hadm))
      p.val (positiveRootFirst α) (positiveRootSecond α) hzero
  change positiveRootOperator n β
    (polarization r n (positiveRootFirst α)
      (positiveRootSecond α) (p.val : PolynomialSpace r n)) = 0
  rw [hpolarization, map_zero]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootPolynomialActionCoboundaryDifferentialIncidence_swap
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1))
    (α β : PositiveRoot r) (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i) :
    rootPolynomialActionCoboundaryDifferentialIncidence lam f S α β =
      (realExteriorRootSign S.val.val α *
        realExteriorRootSign (insert β (S.val.val.erase α)) β) •
        positiveRootUpperOperator n α
          (positiveRootOperator n β
            (((f (rootAdmissibleSwap lam S α β hα hβ hadm)).val :
              youngMultihomogeneousSubmodule n
                (rootWedgeWeight lam
                  (rootAdmissibleSwap lam S α β hα hβ hadm))) :
              PolynomialSpace r n)) := by
  classical
  by_cases herase : ∀ i, 0 ≤ signedRootWeight lam (S.val.val.erase α) i
  · have hβ' : β ∉ (rootAdmissibleErase lam S α hα herase).val.val := by
      intro h
      exact hβ (Finset.mem_of_mem_erase h)
    have hins : ∀ i,
        0 ≤ signedRootWeight lam
          (insert β (rootAdmissibleErase lam S α hα herase).val.val) i := by
      simpa only [rootAdmissibleErase_val] using hadm
    have hswap :
        rootAdmissibleInsert lam
          (rootAdmissibleErase lam S α hα herase) β hβ' hins =
        rootAdmissibleSwap lam S α β hα hβ hadm := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    unfold rootPolynomialActionCoboundaryDifferentialIncidence
    rw [dite_eq_left hα, dite_eq_left herase, dite_eq_right hβ', dite_eq_left hins, hswap]
    rfl
  · have hzero :=
      rootAdmissibleSwap_upper_lower_eq_zero_of_inadmissible_erase
        lam S α β hα hβ hadm herase
        (f (rootAdmissibleSwap lam S α β hα hβ hadm))
    unfold rootPolynomialActionCoboundaryDifferentialIncidence
    rw [dite_eq_left hα, dite_eq_right herase, hzero, smul_zero]

theorem rootPolynomialActionDifferentialCoboundaryIncidence_swap
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1))
    (α β : PositiveRoot r) (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i) :
    rootPolynomialActionDifferentialCoboundaryIncidence lam f S β α =
      (realExteriorRootSign (insert β S.val.val) β *
        realExteriorRootSign (insert β S.val.val) α) •
        positiveRootOperator n β
          (positiveRootUpperOperator n α
            (((f (rootAdmissibleSwap lam S α β hα hβ hadm)).val :
              youngMultihomogeneousSubmodule n
                (rootWedgeWeight lam
                  (rootAdmissibleSwap lam S α β hα hβ hadm))) :
              PolynomialSpace r n)) := by
  classical
  have hne : β ≠ α := by
    intro heq
    subst β
    exact hβ hα
  by_cases hins : ∀ i, 0 ≤ signedRootWeight lam (insert β S.val.val) i
  · have hα' : α ∈ (rootAdmissibleInsert lam S β hβ hins).val.val := by
      simp only [rootAdmissibleInsert_val, Finset.mem_insert, hα, or_true]
    have hset :
        (insert β S.val.val).erase α = insert β (S.val.val.erase α) := by
      ext γ
      simp only [Finset.mem_erase, Finset.mem_insert]
      aesop
    have herase : ∀ i,
        0 ≤ signedRootWeight lam
          (((rootAdmissibleInsert lam S β hβ hins).val.val).erase α) i := by
      simpa only [rootAdmissibleInsert_val, hset] using hadm
    have hswap :
        rootAdmissibleErase lam
          (rootAdmissibleInsert lam S β hβ hins) α hα' herase =
        rootAdmissibleSwap lam S α β hα hβ hadm := by
      apply Subtype.ext
      apply Subtype.ext
      exact hset
    unfold rootPolynomialActionDifferentialCoboundaryIncidence
    rw [dite_eq_right hβ, dite_eq_left hins, dite_eq_left hα', dite_eq_left herase, hswap]
    rfl
  · have hzero :=
      rootAdmissibleSwap_lower_upper_eq_zero_of_inadmissible_insert
        lam S α β hα hβ hadm hins
        (f (rootAdmissibleSwap lam S α β hα hβ hadm))
    unfold rootPolynomialActionDifferentialCoboundaryIncidence
    rw [dite_eq_right hβ, dite_eq_right hins, hzero, smul_zero]

theorem rootPolynomialActionIncidence_pair_eq_structureRoots
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1))
    (α β : PositiveRoot r) (hα : α ∈ S.val.val) (hβ : β ∉ S.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i) :
    rootPolynomialActionCoboundaryDifferentialIncidence lam f S α β +
        rootPolynomialActionDifferentialCoboundaryIncidence lam f S β α =
      (∑ γ : PositiveRoot r,
        if _hγ : rootStructureConstant β γ α = 0 then 0
        else (rootSwapExteriorHodgeSign S α β *
            rootStructureConstant β γ α) •
          polarization r n (positiveRootFirst γ) (positiveRootSecond γ)
            (((f (rootAdmissibleSwap lam S α β hα hβ hadm)).val :
              youngMultihomogeneousSubmodule n
                (rootWedgeWeight lam
                  (rootAdmissibleSwap lam S α β hα hβ hadm))) :
              PolynomialSpace r n)) +
      (∑ γ : PositiveRoot r,
        if _hγ : rootStructureConstant α γ β = 0 then 0
        else (rootSwapExteriorHodgeSign S α β *
            rootStructureConstant α γ β) •
          polarization r n (positiveRootSecond γ) (positiveRootFirst γ)
            (((f (rootAdmissibleSwap lam S α β hα hβ hadm)).val :
              youngMultihomogeneousSubmodule n
                (rootWedgeWeight lam
                  (rootAdmissibleSwap lam S α β hα hβ hadm))) :
              PolynomialSpace r n)) := by
  classical
  rw [rootPolynomialActionCoboundaryDifferentialIncidence_swap
      lam f S α β hα hβ hadm,
    rootPolynomialActionDifferentialCoboundaryIncidence_swap
      lam f S α β hα hβ hadm,
    rootSwap_twoActionPaths_eq_signed_structureRoots S.val.val α β hα hβ]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_add, Finset.smul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro γ _
    by_cases hγ : rootStructureConstant β γ α = 0
    · simp only [hγ, positiveRootUpperOperator_apply, polarization_apply, zero_smul, smul_zero,
        ↓reduceDIte]
    · rw [dite_eq_right hγ, smul_smul]
      change
        (realExteriorRootSign S.val.val α *
          realExteriorRootSign (insert β (S.val.val.erase α)) β *
          rootStructureConstant β γ α) •
            positiveRootUpperOperator n γ _ = _
      rfl
  · apply Finset.sum_congr rfl
    intro γ _
    by_cases hγ : rootStructureConstant α γ β = 0
    · simp only [hγ, positiveRootOperator_apply, polarization_apply, zero_smul, smul_zero,
        ↓reduceDIte]
    · rw [dite_eq_right hγ, smul_smul]
      change
        (realExteriorRootSign S.val.val α *
          realExteriorRootSign (insert β (S.val.val.erase α)) β *
          rootStructureConstant α γ β) •
            positiveRootOperator n γ _ = _
      rfl

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootJointHarmonicActionUpperRootStructureCross_polynomial_apply
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

theorem rootJointHarmonicActionLowerRootStructureCross_polynomial_apply
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    (((rootJointHarmonicActionLowerRootStructureCross n lam k f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
      ∑ α : PositiveRoot r,
        if hα : α ∈ S.val.val then
          ∑ β : PositiveRoot r,
            if hβ : β ∈ S.val.val then 0
            else if hadm : ∀ i,
                0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i then
              ∑ γ : PositiveRoot r,
                if _hγ : rootStructureConstant α γ β = 0 then 0
                else (rootSwapExteriorHodgeSign S α β *
                    rootStructureConstant α γ β) •
                  polarization r n (positiveRootSecond γ) (positiveRootFirst γ)
                    ((f (rootAdmissibleSwap lam S α β hα hβ hadm)).val :
                      PolynomialSpace r n)
            else 0
        else 0 := by
  classical
  rw [rootJointHarmonicActionLowerRootStructureCross_apply]
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
        rw [rootSwapLowerStructureEdge_coe]
    · simp only [ZeroMemClass.coe_zero]
  · simp only [ZeroMemClass.coe_zero]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootPolynomialActionHodgeOffDiagonalIncidence_eq_offDiagonal_apply_coe_aux
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) :
    rootPolynomialActionHodgeOffDiagonalIncidence lam f S =
      (((rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1) f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) := by
  classical
  change rootPolynomialActionHodgeOffDiagonalIncidence lam f S =
    (((rootJointHarmonicActionUpperRootStructureCross n lam (k + 1) f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) +
    (((rootJointHarmonicActionLowerRootStructureCross n lam (k + 1) f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n)
  rw [rootJointHarmonicActionUpperRootStructureCross_polynomial_apply,
    rootJointHarmonicActionLowerRootStructureCross_polynomial_apply,
    ← Finset.sum_add_distrib]
  unfold rootPolynomialActionHodgeOffDiagonalIncidence
  apply Finset.sum_congr rfl
  intro α _
  by_cases hα : α ∈ S.val.val
  · simp only [dite_eq_left hα]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro β _
    by_cases heq : α = β
    · subst β
      simp only [↓reduceIte, hα, ↓reduceDIte, add_zero]
    · simp only [heq, ↓reduceIte]
      by_cases hβ : β ∈ S.val.val
      · simp only [dite_eq_left hβ, zero_add]
        simp only [rootPolynomialActionCoboundaryDifferentialIncidence, hα, ↓reduceDIte,
          rootAdmissibleErase_val, Finset.mem_erase, ne_eq, Ne.symm heq, not_false_eq_true, hβ,
          and_self, dite_eq_ite, ite_self, rootPolynomialActionDifferentialCoboundaryIncidence,
          add_zero]
      · simp only [dite_eq_right hβ]
        by_cases hadm : ∀ i,
            0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i
        · simp only [dite_eq_left hadm]
          exact rootPolynomialActionIncidence_pair_eq_structureRoots
            lam f S α β hα hβ hadm
        · simp only [dite_eq_right hadm, add_zero]
          simp only [rootPolynomialActionCoboundaryDifferentialIncidence, hα, ↓reduceDIte,
            rootAdmissibleErase_val, Finset.mem_erase, ne_eq, hβ, and_false, hadm, dite_eq_ite,
            ite_self, rootPolynomialActionDifferentialCoboundaryIncidence, rootAdmissibleInsert_val,
            Finset.mem_insert, heq, or_true, Finset.erase_insert_of_ne (Ne.symm heq), add_zero]
  · simp only [dite_eq_right hα, zero_add]
    apply Finset.sum_eq_zero
    intro β _
    by_cases heq : α = β
    · simp only [heq, ↓reduceIte]
    · simp only [heq, ↓reduceIte, rootPolynomialActionCoboundaryDifferentialIncidence, hα,
        ↓reduceDIte, rootPolynomialActionDifferentialCoboundaryIncidence, rootAdmissibleInsert_val,
        Finset.mem_insert, or_self, dite_eq_ite, ite_self, add_zero]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootPolynomialActionHodgeOffDiagonalIncidence_eq_offDiagonal_apply_coe
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (S : AdmissibleRootWedge lam (k + 1)) :
    rootPolynomialActionHodgeOffDiagonalIncidence lam f S =
      (((rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1) f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) :=
  rootPolynomialActionHodgeOffDiagonalIncidence_eq_offDiagonal_apply_coe_aux
    lam f S

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

private def weightedRootBracketEdgeAdjoint {r k : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (T : AdmissibleRootWedge lam k)
    (h : rootBracketBoundaryCoefficient S.val T.val ≠ 0) :
    JointHarmonicWeightSpace n (rootWedgeWeight lam T) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam S) :=
  (jointHarmonicWeightCast n (rootWedgeWeight lam T)
    (rootWedgeWeight lam S)
    (rootWedgeWeight_eq_of_bracketBoundaryCoefficient_ne_zero
      lam S T h).symm).toLinearMap

@[simp] theorem weightedRootBracketEdgeAdjoint_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (T : AdmissibleRootWedge lam k)
    (h : rootBracketBoundaryCoefficient S.val T.val ≠ 0)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam T)) :
    (((weightedRootBracketEdgeAdjoint n lam S T h p).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
      (p.val : PolynomialSpace r n) :=
  jointHarmonicWeightCast_coe
    (rootWedgeWeight lam T) (rootWedgeWeight lam S)
    (rootWedgeWeight_eq_of_bracketBoundaryCoefficient_ne_zero
      lam S T h).symm p

theorem weightedRootBracketEdge_fischer_adjoint {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (T : AdmissibleRootWedge lam k)
    (h : rootBracketBoundaryCoefficient S.val T.val ≠ 0)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S))
    (q : JointHarmonicWeightSpace n (rootWedgeWeight lam T)) :
    (jointHarmonicWeightFischerCore n (rootWedgeWeight lam T)).inner
        (weightedRootBracketEdge n lam S T h p) q =
      (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner
        p (weightedRootBracketEdgeAdjoint n lam S T h q) := by
  rw [jointHarmonicWeightFischerCore_inner,
    jointHarmonicWeightFischerCore_inner,
    weightedRootBracketEdge_coe,
    weightedRootBracketEdgeAdjoint_coe]

/-- The weighted root bracket coboundary used in the spherical-code argument. -/
def weightedRootBracketCoboundary {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam k →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1) := by
  classical
  refine
    { toFun := fun f S =>
        ∑ T : AdmissibleRootWedge lam k,
          if h : rootBracketBoundaryCoefficient S.val T.val = 0 then 0
          else rootBracketBoundaryCoefficient S.val T.val •
            weightedRootBracketEdgeAdjoint n lam S T h (f T)
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    funext S
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs with h
    · simp only [add_zero]
    · simp only [map_add, smul_add]
  · intro c f
    funext S
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs with h
    · simp only [smul_zero]
    · simp only [map_smul, smul_smul, mul_comm]

@[simp] theorem weightedRootBracketCoboundary_apply {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam (k + 1)) :
    weightedRootBracketCoboundary n lam k f S =
      ∑ T : AdmissibleRootWedge lam k,
        if h : rootBracketBoundaryCoefficient S.val T.val = 0 then 0
        else rootBracketBoundaryCoefficient S.val T.val •
          weightedRootBracketEdgeAdjoint n lam S T h (f T) := by
  unfold weightedRootBracketCoboundary DFunLike.coe LinearMap.instFunLike
  with_reducible rfl

private theorem bracketFischerCore_inner_comm_metriccodes2_9c41043c
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (p q : V) :
    c.inner p q = c.inner q p := by
  simpa only [Real.ringHom_apply] using c.conj_inner_symm q p

private theorem bracketFischerCore_zero_left_metriccodes2_9c41043c
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (p : V) :
    c.inner 0 p = 0 := by
  have h := c.add_left (0 : V) 0 p
  simp only [zero_add] at h
  linarith

private theorem bracketFischerCore_zero_right_metriccodes2_9c41043c
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (p : V) :
    c.inner p 0 = 0 := by
  rw [bracketFischerCore_inner_comm_metriccodes2_9c41043c,
    bracketFischerCore_zero_left_metriccodes2_9c41043c]

private theorem bracketFischerCore_sum_left_metriccodes2_9c41043c
    {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V)
    (p : ι → V) (q : V) :
    c.inner (∑ i, p i) q = ∑ i, c.inner (p i) q := by
  classical
  have h (s : Finset ι) :
      c.inner (∑ i ∈ s, p i) q = ∑ i ∈ s, c.inner (p i) q := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, bracketFischerCore_zero_left_metriccodes2_9c41043c]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, c.add_left, ih]
  simpa only using h Finset.univ

private theorem bracketFischerCore_sum_right_metriccodes2_9c41043c
    {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V)
    (p : V) (q : ι → V) :
    c.inner p (∑ i, q i) = ∑ i, c.inner p (q i) := by
  rw [bracketFischerCore_inner_comm_metriccodes2_9c41043c,
    bracketFischerCore_sum_left_metriccodes2_9c41043c]
  apply Finset.sum_congr rfl
  intro i _
  exact bracketFischerCore_inner_comm_metriccodes2_9c41043c c (q i) p

private theorem bracketFischerCore_smul_left_metriccodes2_9c41043c
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V)
    (a : ℝ) (p q : V) :
    c.inner (a • p) q = a * c.inner p q := by
  simpa only [Real.ringHom_apply] using c.smul_left p q a

private theorem bracketFischerCore_smul_right_metriccodes2_9c41043c
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V)
    (a : ℝ) (p q : V) :
    c.inner p (a • q) = a * c.inner p q := by
  rw [bracketFischerCore_inner_comm_metriccodes2_9c41043c,
    bracketFischerCore_smul_left_metriccodes2_9c41043c,
    bracketFischerCore_inner_comm_metriccodes2_9c41043c c q p]

theorem weightedRootBracketBoundary_fischer_adjoint
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam (k + 1))
    (q : RootJointHarmonicChain n lam k) :
    (rootJointHarmonicChainFischerCore n lam k).inner
        (weightedRootBracketBoundary n lam k p) q =
      (rootJointHarmonicChainFischerCore n lam (k + 1)).inner
        p (weightedRootBracketCoboundary n lam k q) := by
  classical
  rw [rootJointHarmonicChainFischerCore_inner,
    rootJointHarmonicChainFischerCore_inner]
  simp_rw [weightedRootBracketBoundary_apply,
    weightedRootBracketCoboundary_apply]
  calc
    _ = ∑ T : AdmissibleRootWedge lam k,
        ∑ S : AdmissibleRootWedge lam (k + 1),
          (jointHarmonicWeightFischerCore n (rootWedgeWeight lam T)).inner
            (if h : rootBracketBoundaryCoefficient S.val T.val = 0 then 0
             else rootBracketBoundaryCoefficient S.val T.val •
               weightedRootBracketEdge n lam S T h (p S)) (q T) := by
          apply Finset.sum_congr rfl
          intro T _
          exact bracketFischerCore_sum_left_metriccodes2_9c41043c
            (jointHarmonicWeightFischerCore n (rootWedgeWeight lam T)) _ _
    _ = ∑ S : AdmissibleRootWedge lam (k + 1),
        ∑ T : AdmissibleRootWedge lam k,
          (jointHarmonicWeightFischerCore n (rootWedgeWeight lam T)).inner
            (if h : rootBracketBoundaryCoefficient S.val T.val = 0 then 0
             else rootBracketBoundaryCoefficient S.val T.val •
               weightedRootBracketEdge n lam S T h (p S)) (q T) := by
          rw [Finset.sum_comm]
    _ = ∑ S : AdmissibleRootWedge lam (k + 1),
        ∑ T : AdmissibleRootWedge lam k,
          (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)).inner
            (p S)
            (if h : rootBracketBoundaryCoefficient S.val T.val = 0 then 0
             else rootBracketBoundaryCoefficient S.val T.val •
               weightedRootBracketEdgeAdjoint n lam S T h (q T)) := by
          apply Finset.sum_congr rfl
          intro S _
          apply Finset.sum_congr rfl
          intro T _
          split_ifs with h
          · exact
              (bracketFischerCore_zero_left_metriccodes2_9c41043c
                (jointHarmonicWeightFischerCore n
                  (rootWedgeWeight lam T)) (q T)).trans
                (bracketFischerCore_zero_right_metriccodes2_9c41043c
                  (jointHarmonicWeightFischerCore n
                    (rootWedgeWeight lam S)) (p S)).symm
          · calc
              _ = rootBracketBoundaryCoefficient S.val T.val *
                    (jointHarmonicWeightFischerCore n
                      (rootWedgeWeight lam T)).inner
                        (weightedRootBracketEdge n lam S T h (p S))
                        (q T) :=
                  bracketFischerCore_smul_left_metriccodes2_9c41043c
                    (jointHarmonicWeightFischerCore n
                      (rootWedgeWeight lam T))
                    (rootBracketBoundaryCoefficient S.val T.val)
                    (weightedRootBracketEdge n lam S T h (p S)) (q T)
              _ = rootBracketBoundaryCoefficient S.val T.val *
                    (jointHarmonicWeightFischerCore n
                      (rootWedgeWeight lam S)).inner
                        (p S)
                        (weightedRootBracketEdgeAdjoint n lam S T h
                          (q T)) :=
                  congrArg
                    (fun x : ℝ =>
                      rootBracketBoundaryCoefficient S.val T.val * x)
                    (weightedRootBracketEdge_fischer_adjoint
                      lam S T h (p S) (q T))
              _ = _ :=
                  (bracketFischerCore_smul_right_metriccodes2_9c41043c
                    (jointHarmonicWeightFischerCore n
                      (rootWedgeWeight lam S))
                    (rootBracketBoundaryCoefficient S.val T.val)
                    (p S)
                    (weightedRootBracketEdgeAdjoint n lam S T h
                      (q T))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      symm
      exact bracketFischerCore_sum_right_metriccodes2_9c41043c
        (jointHarmonicWeightFischerCore n (rootWedgeWeight lam S)) _ _

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem weightedRootBracketCoboundary_apply_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam (k + 1)) :
    (((weightedRootBracketCoboundary n lam k f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
        ∑ T : AdmissibleRootWedge lam k,
          rootBracketBoundaryCoefficient S.val T.val •
            ((f T).val : PolynomialSpace r n) := by
  classical
  rw [weightedRootBracketCoboundary_apply]
  simp only [AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs with h
  · simp only [ZeroMemClass.coe_zero, h, zero_smul]
  · change
      rootBracketBoundaryCoefficient S.val T.val •
        (((weightedRootBracketEdgeAdjoint n lam S T h (f T)).val :
          youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
          PolynomialSpace r n) = _
    rw [weightedRootBracketEdgeAdjoint_coe]

end

section


variable {ι M : Type*} [LinearOrder ι]
variable [AddCommGroup M] [Module ℝ M]

theorem actualExteriorRootContraction_creation_creation_contraction_anticommute
    (a b c d : ι) :
    actualExteriorRootContraction M a *
          (actualExteriorRootCreation M b *
            (actualExteriorRootCreation M c *
              actualExteriorRootContraction M d)) +
        (actualExteriorRootCreation M b *
          (actualExteriorRootCreation M c *
            actualExteriorRootContraction M d)) *
          actualExteriorRootContraction M a =
      (if a = b then
        actualExteriorRootCreation M c *
          actualExteriorRootContraction M d else 0) -
      (if a = c then
        actualExteriorRootCreation M b *
          actualExteriorRootContraction M d else 0) := by
  have hab := actualExteriorRootContraction_creation_anticommute
    (M := M) a b
  have hac := actualExteriorRootContraction_creation_anticommute
    (M := M) a c
  have had := actualExteriorRootContraction_anticommute
    (M := M) a d
  calc
    _ =
        (actualExteriorRootContraction M a *
          actualExteriorRootCreation M b +
          actualExteriorRootCreation M b *
            actualExteriorRootContraction M a) *
            actualExteriorRootCreation M c *
              actualExteriorRootContraction M d -
        actualExteriorRootCreation M b *
          (actualExteriorRootContraction M a *
            actualExteriorRootCreation M c +
            actualExteriorRootCreation M c *
              actualExteriorRootContraction M a) *
              actualExteriorRootContraction M d +
        actualExteriorRootCreation M b *
          actualExteriorRootCreation M c *
          (actualExteriorRootContraction M a *
            actualExteriorRootContraction M d +
            actualExteriorRootContraction M d *
              actualExteriorRootContraction M a) := by
          noncomm_ring
    _ = _ := by
      rw [hab, hac, had]
      split_ifs <;> simp

theorem actualExteriorRootContraction_creation_contraction_contraction_anticommute
    (a b c d : ι) :
    actualExteriorRootContraction M a *
          (actualExteriorRootCreation M b *
            (actualExteriorRootContraction M c *
              actualExteriorRootContraction M d)) +
        (actualExteriorRootCreation M b *
          (actualExteriorRootContraction M c *
            actualExteriorRootContraction M d)) *
          actualExteriorRootContraction M a =
      if a = b then
        actualExteriorRootContraction M c *
          actualExteriorRootContraction M d else 0 := by
  have hab := actualExteriorRootContraction_creation_anticommute
    (M := M) a b
  have hac := actualExteriorRootContraction_anticommute
    (M := M) a c
  have had := actualExteriorRootContraction_anticommute
    (M := M) a d
  calc
    _ =
        (actualExteriorRootContraction M a *
          actualExteriorRootCreation M b +
          actualExteriorRootCreation M b *
            actualExteriorRootContraction M a) *
            actualExteriorRootContraction M c *
              actualExteriorRootContraction M d -
        actualExteriorRootCreation M b *
          (actualExteriorRootContraction M a *
            actualExteriorRootContraction M c +
            actualExteriorRootContraction M c *
              actualExteriorRootContraction M a) *
              actualExteriorRootContraction M d +
        actualExteriorRootCreation M b *
          actualExteriorRootContraction M c *
          (actualExteriorRootContraction M a *
            actualExteriorRootContraction M d +
            actualExteriorRootContraction M d *
              actualExteriorRootContraction M a) := by
          noncomm_ring
    _ = _ := by
      rw [hab, hac, had]
      split_ifs <;> simp

/-- The actual exterior root bracket coboundary used in the spherical-code argument. -/
def actualExteriorRootBracketCoboundary [Fintype ι]
    (structureConstant : ι → ι → ι → ℝ) :
    Module.End ℝ (Finset ι → M) :=
  ∑ b : ι, ∑ c : ι, ∑ d : ι,
    structureConstant b c d •
      (actualExteriorRootCreation M b *
        (actualExteriorRootCreation M c *
          actualExteriorRootContraction M d))

theorem actualExteriorRootContraction_bracketCoboundary_anticommute
    [Fintype ι]
    (structureConstant : ι → ι → ι → ℝ) (a : ι) :
    actualExteriorRootContraction M a *
          actualExteriorRootBracketCoboundary
            (M := M) structureConstant +
        actualExteriorRootBracketCoboundary
          (M := M) structureConstant *
            actualExteriorRootContraction M a =
      (∑ c : ι, ∑ d : ι,
        structureConstant a c d •
          (actualExteriorRootCreation M c *
            actualExteriorRootContraction M d)) -
        (∑ b : ι, ∑ d : ι,
          structureConstant b a d •
            (actualExteriorRootCreation M b *
              actualExteriorRootContraction M d)) := by
  classical
  unfold actualExteriorRootBracketCoboundary
  simp_rw [Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc]
  simp_rw [← Finset.sum_add_distrib, ← smul_add,
    actualExteriorRootContraction_creation_creation_contraction_anticommute,
    smul_sub, Finset.sum_sub_distrib]
  simp only [smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The full root exterior polynomial chain used in the spherical-code argument. -/
abbrev FullRootExteriorPolynomialChain (r n : ℕ) :=
  Finset (PositiveRoot r) → PolynomialSpace r n

/-- The full root exterior polynomial action used in the spherical-code argument. -/
def fullRootExteriorPolynomialAction (r n : ℕ) (α : PositiveRoot r) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) where
  toFun f S := positiveRootOperator n α (f S)
  map_add' f g := by
    funext S
    exact (positiveRootOperator n α).map_add (f S) (g S)
  map_smul' c f := by
    funext S
    exact (positiveRootOperator n α).map_smul c (f S)

@[simp] theorem fullRootExteriorPolynomialAction_apply
    {r n : ℕ} (α : PositiveRoot r)
    (f : FullRootExteriorPolynomialChain r n)
    (S : Finset (PositiveRoot r)) :
    fullRootExteriorPolynomialAction r n α f S =
      positiveRootOperator n α (f S) := rfl

theorem fullRootExteriorPolynomialAction_contraction_commute
    {r n : ℕ} (α β : PositiveRoot r) :
    fullRootExteriorPolynomialAction r n α *
        actualExteriorRootContraction (PolynomialSpace r n) β =
      actualExteriorRootContraction (PolynomialSpace r n) β *
        fullRootExteriorPolynomialAction r n α := by
  apply LinearMap.ext
  intro f
  funext S
  simp only [Module.End.mul_apply,
    fullRootExteriorPolynomialAction_apply,
    actualExteriorRootContraction_apply]
  split_ifs <;> simp

theorem fullRootExteriorPolynomialAction_creation_commute
    {r n : ℕ} (α β : PositiveRoot r) :
    fullRootExteriorPolynomialAction r n α *
        actualExteriorRootCreation (PolynomialSpace r n) β =
      actualExteriorRootCreation (PolynomialSpace r n) β *
        fullRootExteriorPolynomialAction r n α := by
  apply LinearMap.ext
  intro f
  funext S
  simp only [Module.End.mul_apply,
    fullRootExteriorPolynomialAction_apply,
    actualExteriorRootCreation_apply]
  split_ifs <;> simp

theorem fullRootExteriorPolynomialAction_commutator
    {r n : ℕ} (α β : PositiveRoot r) :
    fullRootExteriorPolynomialAction r n α *
        fullRootExteriorPolynomialAction r n β -
      fullRootExteriorPolynomialAction r n β *
        fullRootExteriorPolynomialAction r n α =
      ∑ γ : PositiveRoot r,
        rootStructureConstant α β γ •
          fullRootExteriorPolynomialAction r n γ := by
  classical
  apply LinearMap.ext
  intro f
  funext S
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  change
    positiveRootOperator n α (positiveRootOperator n β (f S)) -
      positiveRootOperator n β (positiveRootOperator n α (f S)) =
      (∑ γ : PositiveRoot r,
        rootStructureConstant α β γ •
          fullRootExteriorPolynomialAction r n γ) f S
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply,
    ]
  simpa only [positiveRootOperator_apply, polarization_apply, map_sum, Derivation.leibniz,
    smul_eq_mul,
    MvPolynomial.pderiv_X, Finset.sum_apply, Pi.smul_apply,
      fullRootExteriorPolynomialAction_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.coe_sum, LinearMap.coe_smul] using
    LinearMap.congr_fun (positiveRootOperator_commutator α β) (f S)

theorem actualExteriorRootContraction_mul_self_zero
    {r n : ℕ} (α : PositiveRoot r) :
    actualExteriorRootContraction (PolynomialSpace r n) α *
        actualExteriorRootContraction (PolynomialSpace r n) α = 0 := by
  classical
  apply LinearMap.ext
  intro f
  funext S
  simp only [Module.End.mul_apply]
  by_cases h : α ∈ S <;>
    simp [actualExteriorRootContraction_apply, h]

/-- The full root exterior action atom used in the spherical-code argument. -/
def fullRootExteriorActionAtom (r n : ℕ) (α : PositiveRoot r) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  fullRootExteriorPolynomialAction r n α *
    actualExteriorRootContraction (PolynomialSpace r n) α

/-- The full root exterior action used in the spherical-code argument. -/
def fullRootExteriorAction (r n : ℕ) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  ∑ α : PositiveRoot r, fullRootExteriorActionAtom r n α

/-- The full root exterior bracket atom used in the spherical-code argument. -/
def fullRootExteriorBracketAtom (r n : ℕ)
    (α β γ : PositiveRoot r) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  actualExteriorRootCreation (PolynomialSpace r n) γ *
    (actualExteriorRootContraction (PolynomialSpace r n) β *
      actualExteriorRootContraction (PolynomialSpace r n) α)

/-- The full root exterior bracket used in the spherical-code argument. -/
def fullRootExteriorBracket (r n : ℕ) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) := by
  classical
  exact ∑ α : PositiveRoot r, ∑ β : PositiveRoot r,
    if α < β then
      ∑ γ : PositiveRoot r,
        rootStructureConstant α β γ •
          fullRootExteriorBracketAtom r n α β γ
    else 0

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The root polynomial chain zero extension used in the spherical-code argument. -/
def rootPolynomialChainZeroExtension (r n k : ℕ) :
    RootPolynomialChain r n k →ₗ[ℝ]
      (Finset (PositiveRoot r) → PolynomialSpace r n) := by
  classical
  refine
    { toFun := fun f S =>
        if h : S.card = k then f ⟨S, h⟩ else 0
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    funext S
    by_cases h : S.card = k <;> simp [h]
  · intro c f
    funext S
    by_cases h : S.card = k <;> simp [h]

@[simp] theorem rootPolynomialChainZeroExtension_apply {r n k : ℕ}
    (f : RootPolynomialChain r n k)
    (S : Finset (PositiveRoot r)) :
    rootPolynomialChainZeroExtension r n k f S =
      if h : S.card = k then f ⟨S, h⟩ else 0 := by
  classical
  rfl

theorem rootPolynomialChainZeroExtension_wedge {r n k : ℕ}
    (f : RootPolynomialChain r n k)
    (S : RootWedge r k) :
    rootPolynomialChainZeroExtension r n k f S.val = f S := by
  classical
  simp only [rootPolynomialChainZeroExtension_apply, S.property, ↓reduceDIte, Subtype.coe_eta]

theorem rootPolynomialChainZeroExtension_of_card_ne {r n k : ℕ}
    (f : RootPolynomialChain r n k)
    (S : Finset (PositiveRoot r)) (h : S.card ≠ k) :
    rootPolynomialChainZeroExtension r n k f S = 0 := by
  simp only [rootPolynomialChainZeroExtension_apply, h, ↓reduceDIte]

theorem rootActionBoundary_eq_exteriorContraction_zeroExtension
    {r n k : ℕ}
    (f : RootPolynomialChain r n (k + 1))
    (T : RootWedge r k) :
    rootActionBoundary r n k f T =
      ∑ α : PositiveRoot r,
        positiveRootOperator n α
          (actualExteriorRootContraction (PolynomialSpace r n) α
            (rootPolynomialChainZeroExtension r n (k + 1) f) T.val) := by
  classical
  rw [rootActionBoundary_apply]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hα : α ∈ T.val
  · simp only [hα, ↓reduceDIte, actualExteriorRootContraction_apply, ↓reduceIte,
      map_zero, ]
  · have hcard : (insert α T.val).card = k + 1 := by
      simp only [hα, not_false_eq_true, Finset.card_insert_of_notMem, T.property]
    have hwedge : rootWedgeInsert T α hα =
        (⟨insert α T.val, hcard⟩ : RootWedge r (k + 1)) := by
      apply Subtype.ext
      rfl
    simp only [hα, ↓reduceDIte, actualExteriorRootContraction_apply,
      ↓reduceIte, rootPolynomialChainZeroExtension_apply,
      map_smul]
    split_ifs with hcard'
    · convert congrArg
        (fun p : PolynomialSpace r n =>
          realExteriorRootSign (insert α T.val) α •
            positiveRootOperator n α p)
        (congrArg f hwedge) using 1
      congr 2
      · ext x
        simp only [Finset.mem_insert]
      · congr 1
        apply Subtype.ext
        ext x
        simp only [Finset.mem_insert]
    · exfalso
      apply hcard'
      simp only [hα, not_false_eq_true, Finset.card_insert_of_notMem, T.property]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

private def rootWedgeErase {r k : ℕ}
    (S : RootWedge r (k + 1)) (α : PositiveRoot r)
    (hα : α ∈ S.val) : RootWedge r k := by
  refine ⟨S.val.erase α, ?_⟩
  rw [Finset.card_erase_of_mem hα, S.property]
  omega

@[simp] theorem rootWedgeErase_val {r k : ℕ}
    (S : RootWedge r (k + 1)) (α : PositiveRoot r)
    (hα : α ∈ S.val) :
    (rootWedgeErase S α hα).val = S.val.erase α := rfl

/-- The root action coboundary used in the spherical-code argument. -/
def rootActionCoboundary (r n k : ℕ) :
    RootPolynomialChain r n k →ₗ[ℝ]
      RootPolynomialChain r n (k + 1) := by
  classical
  exact LinearMap.pi fun S =>
    ∑ α : PositiveRoot r,
      if hα : α ∈ S.val then
        realExteriorRootSign S.val α •
          (positiveRootUpperOperator n α).comp
            (LinearMap.proj (rootWedgeErase S α hα))
      else 0

@[simp] theorem rootActionCoboundary_apply {r n k : ℕ}
    (f : RootPolynomialChain r n k)
    (S : RootWedge r (k + 1)) :
    rootActionCoboundary r n k f S =
      ∑ α : PositiveRoot r,
        if hα : α ∈ S.val then
          realExteriorRootSign S.val α •
            positiveRootUpperOperator n α
              (f (rootWedgeErase S α hα))
        else 0 := by
  classical
  change
    (∑ α : PositiveRoot r,
      if hα : α ∈ S.val then
        realExteriorRootSign S.val α •
          (positiveRootUpperOperator n α).comp
            (LinearMap.proj (rootWedgeErase S α hα))
      else 0) f = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with hα <;> simp

/-- The root bracket coboundary used in the spherical-code argument. -/
def rootBracketCoboundary (r n k : ℕ) :
    RootPolynomialChain r n k →ₗ[ℝ]
      RootPolynomialChain r n (k + 1) :=
  LinearMap.pi fun S =>
    ∑ T : RootWedge r k,
      rootBracketBoundaryCoefficient S T •
        (LinearMap.proj T :
          RootPolynomialChain r n k →ₗ[ℝ] PolynomialSpace r n)

@[simp] theorem rootBracketCoboundary_apply {r n k : ℕ}
    (f : RootPolynomialChain r n k)
    (S : RootWedge r (k + 1)) :
    rootBracketCoboundary r n k f S =
      ∑ T : RootWedge r k,
        rootBracketBoundaryCoefficient S T • f T := by
  classical
  simp only [rootBracketCoboundary, LinearMap.pi_apply, LinearMap.coe_sum, LinearMap.coe_smul,
    LinearMap.coe_proj, Finset.sum_apply, Pi.smul_apply, Function.eval]

theorem rootJointHarmonicPolynomialInclusion_bracketCoboundary_intertwines
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    (rootJointHarmonicPolynomialInclusion n lam (k + 1)).comp
        (weightedRootBracketCoboundary n lam k) =
      (rootBracketCoboundary r n k).comp
        (rootJointHarmonicPolynomialInclusion n lam k) := by
  classical
  apply LinearMap.ext
  intro f
  funext S
  simp only [LinearMap.comp_apply]
  let P : RootWedge r k → Prop :=
    fun T => ∀ i, 0 ≤ signedRootWeight lam T.val i
  let F : RootWedge r k → PolynomialSpace r n :=
    fun T =>
      if h : P T then
        rootBracketBoundaryCoefficient S T •
          ((f (⟨T, h⟩ : AdmissibleRootWedge lam k)).val :
            PolynomialSpace r n)
      else 0
  by_cases hS : ∀ i, 0 ≤ signedRootWeight lam S.val i
  · let U : AdmissibleRootWedge lam (k + 1) := ⟨S, hS⟩
    change
      (if h : ∀ i, 0 ≤ signedRootWeight lam S.val i then
        (((weightedRootBracketCoboundary n lam k f
            (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1))).val :
          youngMultihomogeneousSubmodule n
            (rootWedgeWeight lam
              (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1)))) :
          PolynomialSpace r n)
      else 0) = _
    rw [dite_eq_left hS, weightedRootBracketCoboundary_apply_coe,
      rootBracketCoboundary_apply]
    have hleft :
        (∑ T : AdmissibleRootWedge lam k,
          rootBracketBoundaryCoefficient
            (⟨S, hS⟩ : AdmissibleRootWedge lam (k + 1)).val T.val •
              ((f T).val : PolynomialSpace r n)) =
          ∑ T : {T : RootWedge r k // P T}, F T.val := by
      apply Finset.sum_congr rfl
      intro T _
      simp only [T.property, implies_true, ↓reduceDIte, F, P]
    rw [hleft]
    change
      (∑ T : {T : RootWedge r k // P T}, F T.val) =
        ∑ T : RootWedge r k,
          rootBracketBoundaryCoefficient S T •
            rootJointHarmonicPolynomialInclusion n lam k f T
    calc
      (∑ T : {T : RootWedge r k // P T}, F T.val) =
          ∑ T ∈ Finset.univ.filter P, F T :=
        (Finset.sum_subtype (Finset.univ.filter P) (by simp only [Finset.mem_filter,
                                                         Finset.mem_univ, true_and,
                                                           implies_true]) F).symm
      _ = ∑ T : RootWedge r k, F T := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro T _
        by_cases hT : P T
        · rw [ite_eq_left hT]
        · rw [ite_eq_right hT]
          simp only [hT, ↓reduceDIte, F]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T _
        by_cases hT : P T
        · change
            (if h : P T then
              rootBracketBoundaryCoefficient S T •
                ((f (⟨T, h⟩ : AdmissibleRootWedge lam k)).val :
                  PolynomialSpace r n)
            else 0) =
              rootBracketBoundaryCoefficient S T •
                (if h : P T then
                  ((f (⟨T, h⟩ : AdmissibleRootWedge lam k)).val :
                    PolynomialSpace r n)
                else 0)
          simp only [dite_eq_left hT]
        · simp only [hT, ↓reduceDIte, rootJointHarmonicPolynomialInclusion, LinearMap.coe_mk,
            AddHom.coe_mk, smul_zero, F, P]
  · change
      (if h : ∀ i, 0 ≤ signedRootWeight lam S.val i then
        (((weightedRootBracketCoboundary n lam k f
            (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1))).val :
          youngMultihomogeneousSubmodule n
            (rootWedgeWeight lam
              (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1)))) :
          PolynomialSpace r n)
      else 0) = _
    rw [dite_eq_right hS, rootBracketCoboundary_apply]
    symm
    apply Finset.sum_eq_zero
    intro T _
    by_cases hT : ∀ i, 0 ≤ signedRootWeight lam T.val i
    · have hcoeff : rootBracketBoundaryCoefficient S T = 0 := by
        by_contra hnonzero
        apply hS
        intro i
        rw [signedRootWeight_eq_of_bracketBoundaryCoefficient_ne_zero
          lam S T hnonzero i]
        exact hT i
      simp only [hcoeff, zero_smul]
    · simp only [rootJointHarmonicPolynomialInclusion, LinearMap.coe_mk, AddHom.coe_mk, hT,
        ↓reduceDIte, smul_zero]

theorem upperRootOperator_eq_zero_of_inadmissible_insert
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hbad : ¬ ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam T)) :
    polarization r n (positiveRootFirst α) (positiveRootSecond α)
      (p.val : PolynomialSpace r n) = 0 := by
  classical
  push Not at hbad
  obtain ⟨i, hi⟩ := hbad
  have hins := signedRootWeight_insert lam T.val.val α hα i
  have hsource := T.property i
  have hsecond : i = positiveRootSecond α := by
    by_contra hne
    have hcharge : 0 ≤ rootCharge α i := by
      by_cases hfirst : i = positiveRootFirst α
      · simp only [rootCharge, hfirst, ↓reduceIte, zero_le_one]
      · simp only [rootCharge, hfirst, ↓reduceIte, hne, Std.le_refl]
    omega
  subst i
  rw [rootCharge_second] at hins
  have hdegree :
      rootWedgeWeight lam T (positiveRootSecond α) = 0 := by
    have hcast := rootWedgeWeight_cast lam T (positiveRootSecond α)
    omega
  exact youngMultihomogeneous_polarization_eq_zero_of_rowDegree_zero
    (rootWedgeWeight lam T) p.val
    (positiveRootFirst α) (positiveRootSecond α) hdegree

theorem positiveRootUpperOperator_eq_zero_of_inadmissible_target
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : RootWedge r (k + 1))
    (hS : ¬ ∀ i, 0 ≤ signedRootWeight lam S.val i)
    (α : PositiveRoot r) (hα : α ∈ S.val)
    (hadm : ∀ i,
      0 ≤ signedRootWeight lam (rootWedgeErase S α hα).val i)
    (p : JointHarmonicWeightSpace n
      (rootWedgeWeight lam
        (⟨rootWedgeErase S α hα, hadm⟩ :
          AdmissibleRootWedge lam k))) :
    positiveRootUpperOperator n α
      (p.val : PolynomialSpace r n) = 0 := by
  let T : AdmissibleRootWedge lam k :=
    ⟨rootWedgeErase S α hα, hadm⟩
  have hnot : α ∉ T.val.val := by
    change α ∉ S.val.erase α
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
  have hbad : ¬ ∀ i,
      0 ≤ signedRootWeight lam (insert α T.val.val) i := by
    intro hgood
    apply hS
    simpa [T, Finset.insert_erase hα] using hgood
  exact upperRootOperator_eq_zero_of_inadmissible_insert
    lam T α hnot hbad p

theorem rootActionCoboundary_eq_exteriorCreation_zeroExtension
    {r n k : ℕ} (f : RootPolynomialChain r n k)
    (S : RootWedge r (k + 1)) :
    rootActionCoboundary r n k f S =
      ∑ α : PositiveRoot r,
        positiveRootUpperOperator n α
          (actualExteriorRootCreation (PolynomialSpace r n) α
            (rootPolynomialChainZeroExtension r n k f) S.val) := by
  classical
  rw [rootActionCoboundary_apply]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hα : α ∈ S.val
  · have hcard : (S.val.erase α).card = k := by
      rw [Finset.card_erase_of_mem hα, S.property]
      omega
    have hwedge : rootWedgeErase S α hα =
        (⟨S.val.erase α, hcard⟩ : RootWedge r k) := by
      apply Subtype.ext
      rfl
    simp only [hα, ↓reduceDIte, actualExteriorRootCreation_apply,
      ↓reduceIte, rootPolynomialChainZeroExtension_apply,
      map_smul]
    split_ifs with hcard'
    · congr 2
      apply congrArg f
      apply Subtype.ext
      ext x
      simp only [rootWedgeErase_val, Finset.mem_erase, ne_eq]
    · exfalso
      apply hcard'
      convert hcard using 1
      congr 1
      ext x
      simp only [Finset.mem_erase, ne_eq]
  · simp only [hα, ↓reduceDIte, actualExteriorRootCreation_apply, ↓reduceIte,
      map_zero, ]

/-- The full root exterior upper polynomial action used in the spherical-code argument. -/
def fullRootExteriorUpperPolynomialAction (r n : ℕ) (α : PositiveRoot r) :
    Module.End ℝ (Finset (PositiveRoot r) → PolynomialSpace r n) where
  toFun f S := positiveRootUpperOperator n α (f S)
  map_add' f g := by
    funext S
    exact (positiveRootUpperOperator n α).map_add (f S) (g S)
  map_smul' c f := by
    funext S
    exact (positiveRootUpperOperator n α).map_smul c (f S)

@[simp] theorem fullRootExteriorUpperPolynomialAction_apply
    {r n : ℕ} (α : PositiveRoot r)
    (f : Finset (PositiveRoot r) → PolynomialSpace r n)
    (S : Finset (PositiveRoot r)) :
    fullRootExteriorUpperPolynomialAction r n α f S =
      positiveRootUpperOperator n α (f S) := rfl

/-- The full root exterior action coboundary used in the spherical-code argument. -/
def fullRootExteriorActionCoboundary (r n : ℕ) :
    Module.End ℝ (Finset (PositiveRoot r) → PolynomialSpace r n) :=
  ∑ α : PositiveRoot r,
    fullRootExteriorUpperPolynomialAction r n α *
      actualExteriorRootCreation (PolynomialSpace r n) α

theorem rootActionCoboundary_zeroExtension
    {r n k : ℕ} (f : RootPolynomialChain r n k) :
    rootPolynomialChainZeroExtension r n (k + 1)
        (rootActionCoboundary r n k f) =
      fullRootExteriorActionCoboundary r n
        (rootPolynomialChainZeroExtension r n k f) := by
  classical
  funext S
  by_cases hcard : S.card = k + 1
  · let W : RootWedge r (k + 1) := ⟨S, hcard⟩
    change
      rootPolynomialChainZeroExtension r n (k + 1)
          (rootActionCoboundary r n k f) W.val =
        fullRootExteriorActionCoboundary r n
          (rootPolynomialChainZeroExtension r n k f) W.val
    rw [rootPolynomialChainZeroExtension_wedge,
      rootActionCoboundary_eq_exteriorCreation_zeroExtension]
    simp only [fullRootExteriorActionCoboundary,
      LinearMap.sum_apply, Finset.sum_apply,
      fullRootExteriorUpperPolynomialAction_apply,
      Module.End.mul_apply]
  · rw [rootPolynomialChainZeroExtension_of_card_ne _ S hcard]
    unfold fullRootExteriorActionCoboundary
    rw [LinearMap.sum_apply, Finset.sum_apply]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro α _
    simp only [Module.End.mul_apply,
      fullRootExteriorUpperPolynomialAction_apply,
      actualExteriorRootCreation_apply]
    by_cases hα : α ∈ S
    · rw [ite_eq_left hα, map_smul]
      simp only [rootPolynomialChainZeroExtension_apply]
      split_ifs with he
      · exfalso
        apply hcard
        have hc : (S.erase α).card + 1 = S.card :=
          Finset.card_erase_add_one hα
        have he' : (S.erase α).card = k := by
          convert he using 1
          congr 1
          ext x
          simp only [Finset.mem_erase, ne_eq]
        omega
      · simp only [map_zero, smul_zero]
    · simp only [hα, ↓reduceIte, map_zero,
        ]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootJointHarmonicPolynomialInclusion_actionCoboundary_intertwines
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    (rootJointHarmonicPolynomialInclusion n lam (k + 1)).comp
        (weightedExteriorActionCoboundary n lam k) =
      (rootActionCoboundary r n k).comp
        (rootJointHarmonicPolynomialInclusion n lam k) := by
  classical
  apply LinearMap.ext
  intro q
  funext S
  simp only [LinearMap.comp_apply]
  by_cases hS : ∀ i, 0 ≤ signedRootWeight lam S.val i
  · let U : AdmissibleRootWedge lam (k + 1) := ⟨S, hS⟩
    change
      (if h : ∀ i, 0 ≤ signedRootWeight lam S.val i then
        (((weightedExteriorActionCoboundary n lam k q
            (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1))).val :
          youngMultihomogeneousSubmodule n
            (rootWedgeWeight lam
              (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1)))) :
          PolynomialSpace r n)
      else 0) = _
    rw [dite_eq_left hS, weightedExteriorActionCoboundary_apply_erase_coe,
      rootActionCoboundary_apply]
    apply Finset.sum_congr rfl
    intro α _
    by_cases hα : α ∈ S.val
    · simp only [hα, ↓reduceDIte]
      split_ifs with hadm
      · have hadm' : ∀ i,
            0 ≤ signedRootWeight lam (rootWedgeErase S α hα).val i := by
          simpa only [rootWedgeErase] using hadm
        let T : AdmissibleRootWedge lam k :=
          ⟨rootWedgeErase S α hα, hadm'⟩
        have hT : rootAdmissibleErase lam
              (⟨S, hS⟩ : AdmissibleRootWedge lam (k + 1))
              α hα hadm = T := by
          apply Subtype.ext
          apply Subtype.ext
          ext x
          simp only [rootAdmissibleErase_val, Finset.mem_erase, ne_eq, rootWedgeErase, T]
        have hcoeff := congrArg
          (fun V : AdmissibleRootWedge lam k =>
            ((q V).val : PolynomialSpace r n)) hT
        have hincl := rootJointHarmonicPolynomialInclusion_apply_admissible
          lam q T
        change
          realExteriorRootSign S.val α •
            polarization r n (positiveRootFirst α) (positiveRootSecond α)
              (((q (rootAdmissibleErase lam
                (⟨S, hS⟩ : AdmissibleRootWedge lam (k + 1))
                α hα hadm)).val :
                youngMultihomogeneousSubmodule n
                  (rootWedgeWeight lam
                    (rootAdmissibleErase lam
                      (⟨S, hS⟩ : AdmissibleRootWedge lam (k + 1))
                      α hα hadm))) : PolynomialSpace r n) =
            realExteriorRootSign S.val α •
              positiveRootUpperOperator n α
                (rootJointHarmonicPolynomialInclusion n lam k q T.val)
        rw [hincl, positiveRootUpperOperator_apply, hcoeff]
      · have hadm' : ¬ ∀ i,
            0 ≤ signedRootWeight lam (rootWedgeErase S α hα).val i := by
          simpa only [rootWedgeErase, not_forall, not_le] using hadm
        have hincl : rootJointHarmonicPolynomialInclusion n lam k q
            (rootWedgeErase S α hα) = 0 := by
          change
            (if h : ∀ i,
                0 ≤ signedRootWeight lam
                  (rootWedgeErase S α hα).val i then
              ((q (⟨rootWedgeErase S α hα, h⟩ :
                AdmissibleRootWedge lam k)).val : PolynomialSpace r n)
            else 0) = 0
          rw [dite_eq_right hadm']
        rw [hincl, map_zero, smul_zero]
    · simp only [hα, ↓reduceDIte]
  · change
      (if h : ∀ i, 0 ≤ signedRootWeight lam S.val i then
        (((weightedExteriorActionCoboundary n lam k q
            (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1))).val :
          youngMultihomogeneousSubmodule n
            (rootWedgeWeight lam
              (⟨S, h⟩ : AdmissibleRootWedge lam (k + 1)))) :
          PolynomialSpace r n)
      else 0) = _
    rw [dite_eq_right hS, rootActionCoboundary_apply]
    symm
    apply Finset.sum_eq_zero
    intro α _
    by_cases hα : α ∈ S.val
    · simp only [hα, ↓reduceDIte]
      by_cases hadm : ∀ i,
          0 ≤ signedRootWeight lam (rootWedgeErase S α hα).val i
      · have hzero := positiveRootUpperOperator_eq_zero_of_inadmissible_target
          lam S hS α hα hadm
          (q (⟨rootWedgeErase S α hα, hadm⟩ :
            AdmissibleRootWedge lam k))
        let T : AdmissibleRootWedge lam k :=
          ⟨rootWedgeErase S α hα, hadm⟩
        have hincl := rootJointHarmonicPolynomialInclusion_apply_admissible
          lam q T
        change
          realExteriorRootSign S.val α •
            positiveRootUpperOperator n α
              (rootJointHarmonicPolynomialInclusion n lam k q T.val) = 0
        rw [hincl, hzero, smul_zero]
      · have hincl : rootJointHarmonicPolynomialInclusion n lam k q
            (rootWedgeErase S α hα) = 0 := by
          change
            (if h : ∀ i,
                0 ≤ signedRootWeight lam
                  (rootWedgeErase S α hα).val i then
              ((q (⟨rootWedgeErase S α hα, h⟩ :
                AdmissibleRootWedge lam k)).val : PolynomialSpace r n)
            else 0) = 0
          rw [dite_eq_right hadm]
        rw [hincl, map_zero, smul_zero]
    · simp only [hα, ↓reduceDIte]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem weightedExteriorActionHodge_eq_diagonal_add_offDiagonal
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    (weightedExteriorActionCoboundary n lam k).comp
        (weightedExteriorActionDifferential n lam k) +
      (weightedExteriorActionDifferential n lam (k + 1)).comp
        (weightedExteriorActionCoboundary n lam (k + 1)) =
      rootJointHarmonicHodgeDiagonal n lam (k + 1) +
        rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1) := by
  apply LinearMap.ext
  intro f
  funext S
  apply Subtype.ext
  apply Subtype.ext
  change
    (((((weightedExteriorActionCoboundary n lam k).comp
          (weightedExteriorActionDifferential n lam k) +
        (weightedExteriorActionDifferential n lam (k + 1)).comp
          (weightedExteriorActionCoboundary n lam (k + 1))) f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
      (((rootJointHarmonicHodgeDiagonal n lam (k + 1) f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n) +
      (((rootJointHarmonicActionHodgeOffDiagonal n lam (k + 1) f S).val :
        youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
        PolynomialSpace r n)
  rw [weightedExteriorActionHodge_apply_coe_eq_hodgeDiagonal_add_offDiagonal,
    rootPolynomialActionHodgeOffDiagonalIncidence_eq_offDiagonal_apply_coe]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootPolynomialChainZeroExtension_eq_sum_single
    {r n k : ℕ} (f : RootPolynomialChain r n k) :
    rootPolynomialChainZeroExtension r n k f =
      ∑ S : RootWedge r k,
        (Pi.single S.val (f S) :
          Finset (PositiveRoot r) → PolynomialSpace r n) := by
  classical
  funext U
  by_cases hU : U.card = k
  · let W : RootWedge r k := ⟨U, hU⟩
    have hmem (S : RootWedge r k) : U = S.val ↔ S = W := by
      constructor
      · intro h
        apply Subtype.ext
        exact h.symm
      · intro h
        cases h
        rfl
    simp only [rootPolynomialChainZeroExtension_apply, hU, ↓reduceDIte, Finset.sum_apply,
      Pi.single_apply, hmem, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, W]
  · have hne (S : RootWedge r k) : S.val ≠ U := by
      intro h
      apply hU
      rw [← h]
      exact S.property
    simp only [rootPolynomialChainZeroExtension_apply, hU, ↓reduceDIte, Finset.sum_apply, ne_eq,
      hne, not_false_eq_true, Pi.single_eq_of_ne', Finset.sum_const_zero]

theorem rootExteriorBracketAtom_support_iff
    {ι : Type*} [LinearOrder ι]
    (S T : Finset ι) (α β γ : ι) :
    (γ ∈ T ∧ β ∉ T.erase γ ∧
      α ∉ insert β (T.erase γ) ∧
      insert α (insert β (T.erase γ)) = S) ↔
      (α ∈ S ∧ β ∈ S.erase α ∧
        γ ∉ (S.erase α).erase β ∧
        T = insert γ ((S.erase α).erase β)) := by
  classical
  constructor
  · rintro ⟨hγ, hβ, hα, hS⟩
    have hSα : S.erase α = insert β (T.erase γ) := by
      rw [← hS, Finset.erase_insert hα]
    have hSαβ : (S.erase α).erase β = T.erase γ := by
      rw [hSα, Finset.erase_insert hβ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hS]
      simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, true_or]
    · rw [hSα]
      simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, true_or]
    · rw [hSαβ]
      simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
    · rw [hSαβ, Finset.insert_erase hγ]
  · rintro ⟨hα, hβ, hγ, hT⟩
    have hTγ : T.erase γ = (S.erase α).erase β := by
      rw [hT, Finset.erase_insert hγ]
    have hTγβ : insert β (T.erase γ) = S.erase α := by
      rw [hTγ, Finset.insert_erase hβ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hT]
      simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, true_or]
    · rw [hTγ]
      simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
    · rw [hTγβ]
      simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
    · rw [hTγβ, Finset.insert_erase hα]

theorem fullRootExteriorAction_zeroExtension_apply
    {r n k : ℕ}
    (f : RootPolynomialChain r n (k + 1))
    (T : RootWedge r k) :
    fullRootExteriorAction r n
        (rootPolynomialChainZeroExtension r n (k + 1) f) T.val =
      rootActionBoundary r n k f T := by
  classical
  rw [rootActionBoundary_eq_exteriorContraction_zeroExtension]
  simp only [fullRootExteriorAction, fullRootExteriorActionAtom, LinearMap.coe_sum,
    Finset.sum_apply, Module.End.mul_apply, fullRootExteriorPolynomialAction_apply,
    actualExteriorRootContraction_apply, rootPolynomialChainZeroExtension_apply, smul_dite,
    smul_zero, positiveRootOperator_apply, polarization_apply]

end

section


open scoped BigOperators

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

theorem rootStructureConstant_coboundaryIncidence_swap
    {r : ℕ} (a : PositiveRoot r) :
    (∑ b : PositiveRoot r, ∑ d : PositiveRoot r,
      rootStructureConstant b a d •
        (actualExteriorRootCreation M b *
          actualExteriorRootContraction M d)) =
      -(∑ c : PositiveRoot r, ∑ d : PositiveRoot r,
        rootStructureConstant a c d •
          (actualExteriorRootCreation M c *
            actualExteriorRootContraction M d)) := by
  classical
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [rootStructureConstant_swap a b d]
  exact neg_smul (rootStructureConstant a b d)
    (actualExteriorRootCreation M b * actualExteriorRootContraction M d)

/-- The actual ordered root bracket coboundary used in the spherical-code argument. -/
def actualOrderedRootBracketCoboundary {r : ℕ} :
    Module.End ℝ (Finset (PositiveRoot r) → M) :=
  ((2 : ℝ)⁻¹) •
    actualExteriorRootBracketCoboundary (M := M)
      (rootStructureConstant (r := r))

theorem actualExteriorRootContraction_orderedBracketCoboundary_anticommute
    {r : ℕ} (a : PositiveRoot r) :
    actualExteriorRootContraction M a *
          (actualOrderedRootBracketCoboundary (M := M) (r := r)) +
        (actualOrderedRootBracketCoboundary (M := M) (r := r)) *
          actualExteriorRootContraction M a =
      ∑ c : PositiveRoot r, ∑ d : PositiveRoot r,
        rootStructureConstant a c d •
          (actualExteriorRootCreation M c *
            actualExteriorRootContraction M d) := by
  classical
  let Z : Module.End ℝ (Finset (PositiveRoot r) → M) :=
    ∑ c : PositiveRoot r, ∑ d : PositiveRoot r,
      rootStructureConstant a c d •
        (actualExteriorRootCreation M c *
          actualExteriorRootContraction M d)
  calc
    _ = ((2 : ℝ)⁻¹) •
          (actualExteriorRootContraction M a *
              actualExteriorRootBracketCoboundary (M := M)
                (rootStructureConstant (r := r)) +
            actualExteriorRootBracketCoboundary (M := M)
                (rootStructureConstant (r := r)) *
              actualExteriorRootContraction M a) := by
          unfold actualOrderedRootBracketCoboundary
          rw [mul_smul_comm, smul_mul_assoc, smul_add]
    _ = ((2 : ℝ)⁻¹) • (Z - -Z) := by
          rw [actualExteriorRootContraction_bracketCoboundary_anticommute,
            rootStructureConstant_coboundaryIncidence_swap]
    _ = Z := by
          rw [sub_neg_eq_add, ← two_smul ℝ Z, smul_smul]
          norm_num
    _ = _ := rfl

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The root joint harmonic bracket action mixed used in the spherical-code argument. -/
def rootJointHarmonicBracketActionMixed {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam (k + 1) :=
  (weightedRootBracketCoboundary n lam k).comp
      (weightedExteriorActionDifferential n lam k) +
    (weightedExteriorActionDifferential n lam (k + 1)).comp
      (weightedRootBracketCoboundary n lam (k + 1))

end

section


open MetricCodes.Spherical.HigherHarmonicYoung

/-- The root polynomial bracket action mixed used in the spherical-code argument. -/
def rootPolynomialBracketActionMixed (r n k : ℕ) :
    RootPolynomialChain r n (k + 1) →ₗ[ℝ]
      RootPolynomialChain r n (k + 1) :=
  (rootBracketCoboundary r n k).comp (rootActionBoundary r n k) +
    (rootActionBoundary r n (k + 1)).comp
      (rootBracketCoboundary r n (k + 1))

theorem rootJointHarmonicPolynomialInclusion_bracketActionMixed_intertwines
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ) :
    (rootJointHarmonicPolynomialInclusion n lam (k + 1)).comp
        (rootJointHarmonicBracketActionMixed n lam k) =
      (rootPolynomialBracketActionMixed r n k).comp
        (rootJointHarmonicPolynomialInclusion n lam (k + 1)) := by
  apply LinearMap.ext
  intro f
  have hfirst := LinearMap.congr_fun
    (rootJointHarmonicPolynomialInclusion_bracketCoboundary_intertwines
      (n := n) (k := k) lam)
    (weightedExteriorActionDifferential n lam k f)
  have hsecond := congrArg (rootBracketCoboundary r n k)
    (LinearMap.congr_fun
      (rootJointHarmonicPolynomialInclusion_action_intertwines
        (n := n) (k := k) lam) f)
  have hthird := LinearMap.congr_fun
    (rootJointHarmonicPolynomialInclusion_action_intertwines
      (n := n) (k := k + 1) lam)
    (weightedRootBracketCoboundary n lam (k + 1) f)
  have hfourth := congrArg (rootActionBoundary r n (k + 1))
    (LinearMap.congr_fun
      (rootJointHarmonicPolynomialInclusion_bracketCoboundary_intertwines
        (n := n) (k := k + 1) lam) f)
  simp only [LinearMap.comp_apply, rootJointHarmonicBracketActionMixed,
    rootPolynomialBracketActionMixed, LinearMap.add_apply]
  rw [map_add]
  simp only [LinearMap.comp_apply] at hfirst hsecond hthird hfourth
  exact congrArg₂ (· + ·) (hfirst.trans hsecond) (hthird.trans hfourth)

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootStructureConstant_output_eq_right_zero {r : ℕ}
    (γ α : PositiveRoot r) : rootStructureConstant γ α α = 0 := by
  by_contra h
  rcases (rootStructureConstant_ne_zero_iff γ α α).mp h with
    ⟨hjoin, hout⟩ | ⟨hjoin, hout⟩
  · have hsecond : α.val.2 = γ.val.2 := by
      simpa only using congrArg (fun z : Fin (r + 1) × Fin (r + 1) => z.2) hout
    have hγ := γ.property
    omega
  · have hfirst : α.val.1 = γ.val.1 := by
      simpa only using congrArg (fun z : Fin (r + 1) × Fin (r + 1) => z.1) hout
    have hγ := γ.property
    omega

theorem fullRootExteriorPolynomialAction_orderedBracketCoboundary_commute
    {r n : ℕ} (γ : PositiveRoot r) :
    fullRootExteriorPolynomialAction r n γ *
        actualOrderedRootBracketCoboundary
          (M := PolynomialSpace r n) (r := r) =
      actualOrderedRootBracketCoboundary
          (M := PolynomialSpace r n) (r := r) *
        fullRootExteriorPolynomialAction r n γ := by
  classical
  unfold actualOrderedRootBracketCoboundary
    actualExteriorRootBracketCoboundary
  simp_rw [mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul]
  apply congrArg (fun z => ((2 : ℝ)⁻¹) • z)
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro δ _
  rw [mul_smul_comm, smul_mul_assoc]
  apply congrArg (fun z => rootStructureConstant α β δ • z)
  have hα := fullRootExteriorPolynomialAction_creation_commute
    (n := n) γ α
  have hβ := fullRootExteriorPolynomialAction_creation_commute
    (n := n) γ β
  have hδ := fullRootExteriorPolynomialAction_contraction_commute
    (n := n) γ δ
  calc
    _ = (fullRootExteriorPolynomialAction r n γ *
          actualExteriorRootCreation (PolynomialSpace r n) α) *
        (actualExteriorRootCreation (PolynomialSpace r n) β *
          actualExteriorRootContraction (PolynomialSpace r n) δ) := by
          noncomm_ring
    _ = (actualExteriorRootCreation (PolynomialSpace r n) α *
          fullRootExteriorPolynomialAction r n γ) *
        (actualExteriorRootCreation (PolynomialSpace r n) β *
          actualExteriorRootContraction (PolynomialSpace r n) δ) := by
          rw [hα]
    _ = actualExteriorRootCreation (PolynomialSpace r n) α *
        (fullRootExteriorPolynomialAction r n γ *
          actualExteriorRootCreation (PolynomialSpace r n) β) *
          actualExteriorRootContraction (PolynomialSpace r n) δ := by
          noncomm_ring
    _ = actualExteriorRootCreation (PolynomialSpace r n) α *
        (actualExteriorRootCreation (PolynomialSpace r n) β *
          fullRootExteriorPolynomialAction r n γ) *
          actualExteriorRootContraction (PolynomialSpace r n) δ := by
          rw [hβ]
    _ = actualExteriorRootCreation (PolynomialSpace r n) α *
        actualExteriorRootCreation (PolynomialSpace r n) β *
        (fullRootExteriorPolynomialAction r n γ *
          actualExteriorRootContraction (PolynomialSpace r n) δ) := by
          noncomm_ring
    _ = actualExteriorRootCreation (PolynomialSpace r n) α *
        actualExteriorRootCreation (PolynomialSpace r n) β *
        (actualExteriorRootContraction (PolynomialSpace r n) δ *
          fullRootExteriorPolynomialAction r n γ) := by
          rw [hδ]
    _ = _ := by noncomm_ring

/-- The full root exterior lower root structure incidence used in the spherical-code argument. -/
def fullRootExteriorLowerRootStructureIncidence (r n : ℕ) :
    Module.End ℝ (FullRootExteriorPolynomialChain r n) :=
  ∑ α : PositiveRoot r, ∑ β : PositiveRoot r, ∑ γ : PositiveRoot r,
    rootStructureConstant γ α β •
      (fullRootExteriorPolynomialAction r n γ *
        (actualExteriorRootCreation (PolynomialSpace r n) α *
          actualExteriorRootContraction (PolynomialSpace r n) β))

theorem fullRootExteriorAction_orderedBracketCoboundary_anticommute
    {r n : ℕ} :
    fullRootExteriorAction r n *
          actualOrderedRootBracketCoboundary
            (M := PolynomialSpace r n) (r := r) +
        actualOrderedRootBracketCoboundary
            (M := PolynomialSpace r n) (r := r) *
          fullRootExteriorAction r n =
      fullRootExteriorLowerRootStructureIncidence r n := by
  classical
  unfold fullRootExteriorAction fullRootExteriorActionAtom
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ γ : PositiveRoot r,
          fullRootExteriorPolynomialAction r n γ *
            (actualExteriorRootContraction (PolynomialSpace r n) γ *
              actualOrderedRootBracketCoboundary
                (M := PolynomialSpace r n) (r := r) +
              actualOrderedRootBracketCoboundary
                (M := PolynomialSpace r n) (r := r) *
                actualExteriorRootContraction (PolynomialSpace r n) γ) := by
          apply Finset.sum_congr rfl
          intro γ _
          have hcomm :=
            fullRootExteriorPolynomialAction_orderedBracketCoboundary_commute
              (n := n) γ
          calc
            _ = fullRootExteriorPolynomialAction r n γ *
                  actualExteriorRootContraction (PolynomialSpace r n) γ *
                    actualOrderedRootBracketCoboundary
                      (M := PolynomialSpace r n) (r := r) +
                (actualOrderedRootBracketCoboundary
                    (M := PolynomialSpace r n) (r := r) *
                  fullRootExteriorPolynomialAction r n γ) *
                    actualExteriorRootContraction (PolynomialSpace r n) γ := by
                  apply congrArg₂ (· + ·) rfl
                  exact (mul_assoc _ _ _).symm
            _ = fullRootExteriorPolynomialAction r n γ *
                  actualExteriorRootContraction (PolynomialSpace r n) γ *
                    actualOrderedRootBracketCoboundary
                      (M := PolynomialSpace r n) (r := r) +
                fullRootExteriorPolynomialAction r n γ *
                  actualOrderedRootBracketCoboundary
                    (M := PolynomialSpace r n) (r := r) *
                    actualExteriorRootContraction (PolynomialSpace r n) γ := by
                  rw [← hcomm]
            _ = _ := by noncomm_ring
    _ = ∑ γ : PositiveRoot r, ∑ α : PositiveRoot r,
          ∑ β : PositiveRoot r,
            rootStructureConstant γ α β •
              (fullRootExteriorPolynomialAction r n γ *
                (actualExteriorRootCreation (PolynomialSpace r n) α *
                  actualExteriorRootContraction (PolynomialSpace r n) β)) := by
          apply Finset.sum_congr rfl
          intro γ _
          rw [actualExteriorRootContraction_orderedBracketCoboundary_anticommute]
          simp_rw [Finset.mul_sum, mul_smul_comm]
    _ = fullRootExteriorLowerRootStructureIncidence r n := by
          unfold fullRootExteriorLowerRootStructureIncidence
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro α _
          rw [Finset.sum_comm]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

section LowerStructureAtom



end LowerStructureAtom

theorem rootJointHarmonicActionLowerRootStructureCross_apply_coe
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    (((rootJointHarmonicActionLowerRootStructureCross n lam k f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
      ∑ α : PositiveRoot r,
        if hα : α ∈ S.val.val then
          ∑ β : PositiveRoot r,
            if hβ : β ∈ S.val.val then 0
            else if hadm : ∀ i,
                0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i then
              ∑ γ : PositiveRoot r,
                if _hγ : rootStructureConstant α γ β = 0 then 0
                else (rootSwapExteriorHodgeSign S α β *
                    rootStructureConstant α γ β) •
                  polarization r n (positiveRootSecond γ) (positiveRootFirst γ)
                    ((f (rootAdmissibleSwap lam S α β hα hβ hadm)).val :
                      PolynomialSpace r n)
            else 0
        else 0 := by
  classical
  rw [rootJointHarmonicActionLowerRootStructureCross_apply]
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
        rw [rootSwapLowerStructureEdge_coe]
    · simp only [ZeroMemClass.coe_zero]
  · simp only [ZeroMemClass.coe_zero]

end

end UniversalBGGRootComplex

end HigherHarmonicYoung

end Spherical

end MetricCodes

end MetricCodesNoncomputable
