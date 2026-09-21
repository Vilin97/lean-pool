/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection
import LeanPool.ClassFieldTheory.GaloisCohomology.Topology.TotallyDisconnectedQuotients
/-!
# The identity component of the idele class group

This module packages the connected component of the identity in the idele
class group as a closed normal subgroup and names the corresponding quotient.
-/

open scoped NNReal NumberField Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The connected component of the identity in the idele class group. -/
def ideleClassIdentityComponent : Subgroup (IdeleClassGroup K) :=
  Subgroup.connectedComponentOfOne (IdeleClassGroup K)

@[simp]
theorem coe_ideleClassIdentityComponent :
    (ideleClassIdentityComponent K : Set (IdeleClassGroup K)) =
      connectedComponent (1 : IdeleClassGroup K) :=
  rfl

/-- The identity component of the idele class group is closed. -/
theorem ideleClassIdentityComponent_isClosed :
    IsClosed (ideleClassIdentityComponent K : Set (IdeleClassGroup K)) := by
  rw [coe_ideleClassIdentityComponent]
  exact isClosed_connectedComponent

instance ideleClassIdentityComponent_normal :
    (ideleClassIdentityComponent K).Normal := by
  change (Subgroup.connectedComponentOfOne (IdeleClassGroup K)).Normal
  exact
    QuotientGroup.Subgroup.Normal.connectedComponentOfOne
      (IdeleClassGroup K)

/-- The idele class group modulo its identity component. -/
abbrev ideleClassComponentQuotient :=
  IdeleClassGroup K ⧸ ideleClassIdentityComponent K

noncomputable instance ideleClassComponentQuotientT2Space :
    T2Space (ideleClassComponentQuotient K) := by
  let : IsClosed
      (ideleClassIdentityComponent K : Set (IdeleClassGroup K)) :=
    ideleClassIdentityComponent_isClosed K
  infer_instance

noncomputable instance ideleClassComponentQuotientTotallyDisconnectedSpace :
    TotallyDisconnectedSpace (ideleClassComponentQuotient K) :=
  QuotientGroup.totallyDisconnectedSpace_quotient_connectedComponentOfOne

/-- The positive archimedean norm section, passed to the idele class group. -/
noncomputable def ideleClassPositiveArchimedeanSection :
    ℝ≥0ˣ →* IdeleClassGroup K :=
  (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)).comp
    (IdeleGroup.positiveArchimedeanSection K)

/-- The positive archimedean section of the idele class group, with its
natural continuity. -/
noncomputable def ideleClassPositiveArchimedeanSectionContinuous :
    ℝ≥0ˣ →ₜ* IdeleClassGroup K where
  __ := ideleClassPositiveArchimedeanSection K
  continuous_toFun :=
    QuotientGroup.continuous_mk.comp
      (IdeleGroup.positiveArchimedeanSectionContinuous K).continuous_toFun

@[simp]
theorem ideleClassPositiveArchimedeanSectionContinuous_apply
    (r : ℝ≥0ˣ) :
    ideleClassPositiveArchimedeanSectionContinuous K r =
      ideleClassPositiveArchimedeanSection K r :=
  rfl

/-- A positive real number, viewed as a nonnegative-real unit. -/
private def positiveRealNNRealUnit
    (x : Set.Ioi (0 : ℝ)) : ℝ≥0ˣ :=
  Units.mk0 (Real.toNNReal x.1)
    (Real.toNNReal_pos.mpr x.2).ne'

/-- The parametrization of nonnegative-real units by positive reals is
continuous. -/
private theorem continuous_positiveRealNNRealUnit :
    Continuous positiveRealNNRealUnit := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous
      (fun x : Set.Ioi (0 : ℝ) ↦ Real.toNNReal x.1)
    exact continuous_real_toNNReal.comp continuous_subtype_val
  · change Continuous
      (fun x : Set.Ioi (0 : ℝ) ↦
        (Real.toNNReal x.1)⁻¹)
    exact
      (continuous_real_toNNReal.comp continuous_subtype_val).inv₀
        (fun x ↦ (Real.toNNReal_pos.mpr x.2).ne')

/-- The multiplicative group of positive nonnegative reals is connected. -/
private theorem nnrealUnits_connectedSpace :
    ConnectedSpace ℝ≥0ˣ := by
  let : ConnectedSpace (Set.Ioi (0 : ℝ)) :=
    isConnected_iff_connectedSpace.mp isConnected_Ioi
  apply Function.Surjective.connectedSpace
      (f := positiveRealNNRealUnit)
  · intro r
    let x : Set.Ioi (0 : ℝ) :=
      ⟨((r : ℝ≥0) : ℝ),
        NNReal.coe_pos.mpr
          (pos_iff_ne_zero.mpr r.ne_zero)⟩
    refine ⟨x, ?_⟩
    apply Units.ext
    simp [positiveRealNNRealUnit, x]
  · exact continuous_positiveRealNNRealUnit

/-- Every value of the positive archimedean class section lies in the
identity component. -/
theorem ideleClassPositiveArchimedeanSection_mem_identityComponent
    (r : ℝ≥0ˣ) :
    ideleClassPositiveArchimedeanSection K r ∈
      ideleClassIdentityComponent K := by
  change
    ideleClassPositiveArchimedeanSection K r ∈
      connectedComponent (1 : IdeleClassGroup K)
  let : ConnectedSpace ℝ≥0ˣ :=
    nnrealUnits_connectedSpace
  have hr : r ∈ connectedComponent (1 : ℝ≥0ˣ) := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact Set.mem_univ r
  have himage :
      ideleClassPositiveArchimedeanSectionContinuous K r ∈
        connectedComponent
          (ideleClassPositiveArchimedeanSectionContinuous K 1) :=
    Continuous.mapsTo_connectedComponent
      (ideleClassPositiveArchimedeanSectionContinuous K).continuous_toFun
      (1 : ℝ≥0ˣ) hr
  simpa using himage

@[simp]
theorem ideleClassPositiveArchimedeanSection_absoluteNorm
    (r : ℝ≥0ˣ) :
    IdeleClassGroup.absoluteNorm
        (ideleClassPositiveArchimedeanSection K r) =
      r⁻¹ := by
  rw [ideleClassPositiveArchimedeanSection, MonoidHom.comp_apply,
    IdeleClassGroup.absoluteNorm_mk,
    IdeleGroup.positiveArchimedeanSection_absoluteNorm]

/-- The norm-one factor of an idele-class representative after removing its
positive archimedean norm component. -/
noncomputable def ideleClassNormOneCorrection
    (a : IdeleGroup K) :
    IdeleClassGroup.normOneSubgroup (K := K) :=
  let correction : IdeleGroup.normOneSubgroup (K := K) :=
    IdeleGroup.positiveArchimedeanNormOneCorrection K a
  ⟨QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (correction : IdeleGroup K),
    (IdeleClassGroup.mk_mem_normOneSubgroup_iff
      (K := K) (correction : IdeleGroup K)).2 correction.property⟩

@[simp]
theorem coe_ideleClassNormOneCorrection (a : IdeleGroup K) :
    (ideleClassNormOneCorrection K a : IdeleClassGroup K) =
      QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
        (IdeleGroup.positiveArchimedeanNormOneCorrection K a) :=
  rfl

/-- Every idele class is the product of a norm-one class and the inverse of
its positive archimedean norm section. -/
theorem ideleClass_mk_eq_normOneCorrection_mul_positiveSection_inv
    (a : IdeleGroup K) :
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a =
      (ideleClassNormOneCorrection K a : IdeleClassGroup K) *
        (ideleClassPositiveArchimedeanSection K
          (IdeleGroup.absoluteNorm a))⁻¹ := by
  rw [coe_ideleClassNormOneCorrection,
    ideleClassPositiveArchimedeanSection, MonoidHom.comp_apply]
  simpa only [map_mul, map_inv] using
    congrArg
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K))
      (IdeleGroup.eq_positiveArchimedeanNormOneCorrection_mul_section_inv
        (K := K) a)

/-- The norm-one idele classes map continuously onto the component quotient. -/
noncomputable def ideleClassNormOneToComponentQuotient :
    IdeleClassGroup.normOneSubgroup (K := K) →ₜ*
      ideleClassComponentQuotient K where
  __ :=
    (QuotientGroup.mk' (ideleClassIdentityComponent K)).comp
      (IdeleClassGroup.normOneSubgroup (K := K)).subtype
  continuous_toFun :=
    QuotientGroup.continuous_mk.comp continuous_subtype_val

/-- Every connected-component class has a norm-one representative. -/
theorem ideleClassNormOneToComponentQuotient_surjective :
    Function.Surjective (ideleClassNormOneToComponentQuotient K) := by
  intro z
  obtain ⟨c, rfl⟩ :=
    QuotientGroup.mk'_surjective (ideleClassIdentityComponent K) z
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective (IdeleGroup.principalSubgroup K) c
  let n : IdeleClassGroup.normOneSubgroup (K := K) :=
    ideleClassNormOneCorrection K a
  refine ⟨n, ?_⟩
  have hsection :
      QuotientGroup.mk' (ideleClassIdentityComponent K)
          (ideleClassPositiveArchimedeanSection K
            (IdeleGroup.absoluteNorm a)) = 1 :=
    (QuotientGroup.eq_one_iff
      (ideleClassPositiveArchimedeanSection K
        (IdeleGroup.absoluteNorm a))).2
      (ideleClassPositiveArchimedeanSection_mem_identityComponent K _)
  change
    QuotientGroup.mk' (ideleClassIdentityComponent K)
        (n : IdeleClassGroup K) =
      QuotientGroup.mk' (ideleClassIdentityComponent K)
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a)
  symm
  rw [ideleClass_mk_eq_normOneCorrection_mul_positiveSection_inv]
  rw [map_mul, map_inv, hsection]
  simp only [inv_one, mul_one]
  rfl

/-- The idele-class component quotient is compact. -/
noncomputable instance ideleClassComponentQuotientCompactSpace :
    CompactSpace (ideleClassComponentQuotient K) :=
  Function.Surjective.compactSpace
    (ideleClassNormOneToComponentQuotient K).continuous_toFun
    (ideleClassNormOneToComponentQuotient_surjective K)

/-- Every continuous homomorphism from the idele class group to a totally
disconnected topological group kills the identity component. -/
theorem ideleClassIdentityComponent_le_ker
    {H : Type*}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TotallyDisconnectedSpace H]
    (f : IdeleClassGroup K →ₜ* H) :
    ideleClassIdentityComponent K ≤ f.ker :=
  f.connectedComponentOfOne_le_ker
