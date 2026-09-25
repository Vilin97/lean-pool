/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFixedPointDescentCore
/-!
# Finite-level and direct-limit fixed-point descent endpoints

This endpoint leaf turns the reusable fixed-point comparisons into actual
descent witnesses first at one finite Galois level and then in the rational
idèle-class direct limit.
-/

@[expose] public section

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity
/-- The tower base-change equivalence carries extension of a rational
relative idele class along `K ↪ U` to relative class inclusion of the
corresponding idele class of `K`. This is the actual commuting square used
for descent. -/
theorem rationalRelativeIdeleClass_descent_square
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U]
    (hKU :
      K ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)))
    (h_algebraMap : ∀ x : K,
      ((algebraMap K U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ))
    (q : IdeleClassGroup K) :
    rationalRelativeIdeleClassTowerBaseChangeEquiv K U
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
          (IntermediateField.inclusion hKU)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm q)) =
      RelativeIdeleGroup.classInclusion K U q := by
  have hAlgebra :=
    rationalIntermediateField_algebra_eq_inclusion
      K U hKU h_algebraMap
  cases hAlgebra
  let : Algebra K U :=
    (IntermediateField.inclusion hKU).toRingHom.toAlgebra
  let : IsScalarTower ℚ K U :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K U :=
    FiniteDimensional.right ℚ K U
  let : IsGalois K U :=
    IsGalois.tower_top_of_isGalois ℚ K U
  calc
    rationalRelativeIdeleClassTowerBaseChangeEquiv K U
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
            (IntermediateField.inclusion hKU)
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K)).symm q)) =
        RelativeIdeleGroup.classInclusion K U
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K)).symm q)) := by
      change
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
            ((TowerRelativeIdeleGroup.classGroupEquiv ℚ K U).symm
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
                (IntermediateField.inclusion hKU)
                ((_root_.relativeIdeleClassBaseChangeMulEquiv
                  (K := ℚ) (L := K)).symm q))) =
          RelativeIdeleGroup.classInclusion K U
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K)
              ((_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := K)).symm q))
      exact
        rationalRelativeIdeleClassEmbedding_towerBaseChange
          hKU
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm q)
    _ = RelativeIdeleGroup.classInclusion K U q := by
      exact
        congrArg (RelativeIdeleGroup.classInclusion K U)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).apply_symm_apply q)

/-- A rational relative idele class at a finite Galois level whose actual
tower base change is fixed over `K` descends to an actual idele class of
`K`.  The conclusion is the commuting square with relative scalar
extension, not merely an abstract preimage. -/
theorem rationalRelativeIdeleClass_exists_descent_of_tower_fixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U]
    (hKU :
      K ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)))
    (h_algebraMap : ∀ x : K,
      ((algebraMap K U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ))
    (d : RelativeIdeleGroup.ClassGroup ℚ U)
    (hd_fixed :
      towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
            ((TowerRelativeIdeleGroup.classGroupEquiv
              ℚ K U).symm d) ∈
        RelativeIdeleGroup.galoisFixedClassSubgroup K U) :
    ∃ q : IdeleClassGroup K,
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
          (IntermediateField.inclusion hKU)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm q) =
        d := by
  let e :
      RelativeIdeleGroup.ClassGroup ℚ U ≃*
        RelativeIdeleGroup.ClassGroup K U :=
    rationalRelativeIdeleClassTowerBaseChangeEquiv K U
  let dK : RelativeIdeleGroup.ClassGroup K U :=
    towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
      ((TowerRelativeIdeleGroup.classGroupEquiv ℚ K U).symm d)
  have hdK_fixed :
      dK ∈
        RelativeIdeleGroup.galoisFixedClassSubgroup K U := by
    exact hd_fixed
  let dFixed :
      RelativeIdeleGroup.galoisFixedClassSubgroup K U :=
    ⟨dK, hdK_fixed⟩
  let q : IdeleClassGroup K :=
    (rationalIntermediateIdeleClassEquivGaloisFixed K U).symm dFixed
  have hqU :
      RelativeIdeleGroup.classInclusion K U q = dK := by
    calc
      RelativeIdeleGroup.classInclusion K U q =
          ((rationalIntermediateIdeleClassEquivGaloisFixed K U q :
              RelativeIdeleGroup.galoisFixedClassSubgroup K U) :
            RelativeIdeleGroup.ClassGroup K U) :=
        (rationalIntermediateIdeleClassEquivGaloisFixed_coe
          K U q).symm
      _ = dK := by
        exact congrArg Subtype.val
          ((rationalIntermediateIdeleClassEquivGaloisFixed
            K U).apply_symm_apply dFixed)
  refine ⟨q, e.injective ?_⟩
  calc
    e
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
          (IntermediateField.inclusion hKU)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm q)) =
        RelativeIdeleGroup.classInclusion K U q :=
      rationalRelativeIdeleClass_descent_square
        K U hKU h_algebraMap q
    _ = dK := hqU
    _ = e d := rfl

/-- Every rational direct-limit idele class fixed by the absolute Galois
subgroup over a finite intermediate field comes from an actual idele
class of that field.  The proof chooses an actual finite-Galois
representative and descends it through the tower comparison. -/
theorem rationalDirectLimit_fixed_exists_ideleClass
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (z : rationalIdeleClassDirectLimit)
    (hz_fixed :
      ∀ σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ,
        σ ∈ K.fixingSubgroup → σ • z = z) :
    ∃ q : IdeleClassGroup K,
      rationalIntermediateIdeleClassToDirectLimit K q = z := by
  obtain ⟨E, c, hzc⟩ :=
    DirectLimit.exists_eq_mk
      (fun _ _ h => rationalRelativeIdeleClassTransition h) z
  let U :
      FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
    E ⊔ rationalNormalClosure K
  let hEU : E ≤ U :=
    le_sup_left
  let hNU : rationalNormalClosure K ≤ U :=
    le_sup_right
  let hKU :
      K ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)) :=
    (IntermediateField.le_normalClosure K).trans hNU
  let d : RelativeIdeleGroup.ClassGroup ℚ U :=
    RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
      (IntermediateField.inclusion hEU) c
  have hzU :
      z = (⟦⟨U, d⟩⟧ : rationalIdeleClassDirectLimit) := by
    exact hzc.trans
      (rationalIdeleClassDirectLimit_mk_apply c hEU).symm
  let : Algebra K U :=
    (IntermediateField.inclusion hKU).toRingHom.toAlgebra
  let : IsScalarTower ℚ K U :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K U :=
    FiniteDimensional.right ℚ K U
  let : IsGalois K U :=
    IsGalois.tower_top_of_isGalois ℚ K U
  have h_algebraMap (x : K) :
      ((algebraMap K U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ) :=
    rfl
  have hd_fixed :=
    rationalTowerRelativeIdeleClass_fixed_of_directLimit_fixed
      K U h_algebraMap d z hzU hz_fixed
  obtain ⟨q, hq⟩ :=
    rationalRelativeIdeleClass_exists_descent_of_tower_fixed
      K U hKU h_algebraMap d hd_fixed
  refine ⟨q, ?_⟩
  calc
    rationalIntermediateIdeleClassToDirectLimit K q =
        (⟦⟨U,
          RelativeIdeleGroup.classEmbedding (K := ℚ)
            (L := rationalNormalClosure K) (M := U)
            (IntermediateField.inclusion hNU)
            (rationalIntermediateIdeleClassToNormalClosure K q)⟩⟧ :
          rationalIdeleClassDirectLimit) :=
      (rationalIdeleClassDirectLimit_mk_apply
        (rationalIntermediateIdeleClassToNormalClosure K q)
        hNU).symm
    _ =
        (⟦⟨U,
          RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
            (IntermediateField.inclusion hKU)
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K)).symm q)⟩⟧ :
          rationalIdeleClassDirectLimit) := by
      apply congrArg
        (fun a : RelativeIdeleGroup.ClassGroup ℚ U =>
          (⟦⟨U, a⟩⟧ : rationalIdeleClassDirectLimit))
      change
        RelativeIdeleGroup.classEmbedding (K := ℚ)
            (L := rationalNormalClosure K) (M := U)
            (IntermediateField.inclusion hNU)
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K)
              (M := rationalNormalClosure K)
              (IntermediateField.inclusion
                (IntermediateField.le_normalClosure K))
              ((_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := K)).symm q)) =
          RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
            (IntermediateField.inclusion
              ((IntermediateField.le_normalClosure K).trans hNU))
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K)).symm q)
      exact
        rationalRelativeIdeleClassEmbedding_comp
          (IntermediateField.le_normalClosure K) hNU
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm q)
    _ = ⟦⟨U, d⟩⟧ := by rw [hq]
    _ = z := hzU.symm

end Reciprocity
end GlobalClassFieldTheory
