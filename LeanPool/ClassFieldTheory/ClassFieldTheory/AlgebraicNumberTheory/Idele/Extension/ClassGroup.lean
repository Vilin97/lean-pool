/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormProperties
public import Mathlib.LinearAlgebra.Basis.VectorSpace
/-!
# Idele classes in finite extensions

The tensor-product model makes the key intersection calculation

`I_K ∩ Lˣ = Kˣ`

an elementary linear-algebra statement.  A linear retraction of
`K → 𝔸_K` shows that an equality `a ⊗ 1 = 1 ⊗ x` forces both factors to
come from the same scalar in `K`.  We then descend the idele inclusion to
quotients and prove it injective.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable
section


variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

namespace RelativeIdeleGroup

omit [NumberField L] [FiniteDimensional K L] in
/-- If a base adele and an extension-field element define the same
element of `𝔸_K ⊗_K L`, then they arise from one scalar of `K`. -/
theorem exists_scalar_of_adeleInclusion_eq_fieldInclusion
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L)
    (h : adeleInclusion K L a = fieldInclusion K L x) :
    ∃ k : K,
      a = algebraMap K (NumberField.AdeleRing (𝓞 K) K) k ∧
      x = algebraMap K L k := by
  let η :=
    Algebra.linearMap K
      (NumberField.AdeleRing (𝓞 K) K)
  have hη : LinearMap.ker η = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (NumberField.AdeleRing.algebraMap_injective
        (R := 𝓞 K) (K := K))
  let ε :
      NumberField.AdeleRing (𝓞 K) K →ₗ[K] K :=
    η.leftInverse
  have hε :
      ε (1 : NumberField.AdeleRing (𝓞 K) K) = 1 := by
    change ε (algebraMap K
      (NumberField.AdeleRing (𝓞 K) K) 1) = 1
    exact LinearMap.leftInverse_apply_of_inj hη 1
  let q :
      RelativeAdeleRing K L →ₗ[K] L :=
    (TensorProduct.lid K L).toLinearMap.comp
      (TensorProduct.map ε LinearMap.id)
  have hq := congrArg q h
  have hx : x = algebraMap K L (ε a) := by
    simpa [q, adeleInclusion, fieldInclusion, hε,
      Algebra.smul_def] using hq.symm
  refine ⟨ε a, ?_, hx⟩
  apply
    (Algebra.TensorProduct.includeLeft_injective
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := L)
      (FaithfulSMul.algebraMap_injective K L))
  change adeleInclusion K L a =
    adeleInclusion K L
      (algebraMap K
        (NumberField.AdeleRing (𝓞 K) K) (ε a))
  rw [h, hx]
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
    (A := NumberField.AdeleRing (𝓞 K) K)
    (B := L) (ε a)).symm

/-- The subgroup of principal relative ideles. -/
def principalSubgroup :
    Subgroup (RelativeIdeleGroup K L) :=
  (principalIdele K L).range

/-- The relative idele class group in the canonical presentation
`𝔸_L = 𝔸_K ⊗_K L`. -/
abbrev ClassGroup :=
  RelativeIdeleGroup K L ⧸ principalSubgroup K L

omit [NumberField L] [FiniteDimensional K L] in
/-- The preimage of the principal relative ideles under `I_K → I_L` is
exactly the subgroup of principal ideles of `K`. -/
theorem comap_principalSubgroup :
    Subgroup.comap (inclusion K L)
        (principalSubgroup K L) =
      IdeleGroup.principalSubgroup K := by
  ext a
  constructor
  · rintro ⟨x, hx⟩
    have htensor :
        adeleInclusion K L
            ((IdeleGroup.equivAdeleRingUnits (K := K) a :
              (NumberField.AdeleRing (𝓞 K) K)ˣ) :
              NumberField.AdeleRing (𝓞 K) K) =
          fieldInclusion K L (x : L) := by
      exact congrArg Units.val hx.symm
    obtain ⟨k, hkA, hkL⟩ :=
      exists_scalar_of_adeleInclusion_eq_fieldInclusion
        K L _ _ htensor
    have hk : k ≠ 0 := by
      intro hk0
      have : (x : L) = 0 := by
        rw [hkL, hk0, map_zero]
      exact x.ne_zero this
    let y : Kˣ := Units.mk0 k hk
    refine ⟨y, ?_⟩
    apply (IdeleGroup.equivAdeleRingUnits (K := K)).injective
    apply Units.ext
    change
      algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) k =
        ((IdeleGroup.equivAdeleRingUnits (K := K) a :
          (NumberField.AdeleRing (𝓞 K) K)ˣ) :
          NumberField.AdeleRing (𝓞 K) K)
    exact hkA.symm
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map (algebraMap K L) y, ?_⟩
    exact (inclusion_principalIdele K L y).symm

/-- Inclusion of ideles descends to inclusion of idele classes. -/
def classInclusion :
    IdeleClassGroup K →* ClassGroup K L :=
  QuotientGroup.map
    (IdeleGroup.principalSubgroup K)
    (principalSubgroup K L)
    (inclusion K L)
    (by
      rw [← comap_principalSubgroup K L])

omit [NumberField L] [FiniteDimensional K L] in
theorem classInclusion_mk (a : IdeleGroup K) :
    classInclusion K L
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk' (principalSubgroup K L)
        (inclusion K L a) :=
  rfl

/-- The determinant norm on relative ideles, descended to their
relative idele-class presentation. -/
noncomputable def classNorm :
    ClassGroup K L →* IdeleClassGroup K :=
  QuotientGroup.map
    (principalSubgroup K L)
    (IdeleGroup.principalSubgroup K)
    (RelativeIdeleGroup.norm K L)
    (by
      rintro _ ⟨x, rfl⟩
      refine
        ⟨Units.map (Algebra.norm K) x, ?_⟩
      exact
        (RelativeIdeleGroup.norm_principalIdele
          K L x).symm)

omit [NumberField L] in
theorem classNorm_mk
    (a : RelativeIdeleGroup K L) :
    classNorm K L
        (QuotientGroup.mk' (principalSubgroup K L) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K L a) :=
  rfl

/-- The norm quotient in the relative idele-class presentation. -/
abbrev ClassNormQuotient :=
  IdeleClassGroup K ⧸ (classNorm K L).range

omit [NumberField L] [FiniteDimensional K L] in
/-- The scalar-extension map `C_K → C_L` is injective. -/
theorem classInclusion_injective :
    Function.Injective (classInclusion K L) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  unfold classInclusion
  rw [QuotientGroup.ker_map,
    comap_principalSubgroup K L]
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (QuotientGroup.eq_one_iff a).2 ha
  · intro hz
    have hz1 : z = 1 := Subgroup.mem_bot.mp hz
    obtain ⟨a, rfl⟩ :=
      QuotientGroup.mk_surjective z
    exact ⟨a, (QuotientGroup.eq_one_iff a).1 hz1, rfl⟩

end RelativeIdeleGroup
