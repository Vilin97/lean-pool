/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.GaloisCohomology
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
/-!
# Galois descent for idele classes

For a finite Galois extension `L/K`, the Galois action on relative ideles
preserves principal ideles and hence descends to the relative idele class
group. Noether's form of Hilbert 90 then shows that every fixed
class has a fixed representative. Together with fixed-idele descent, this identifies
the fixed subgroup with the embedded copy of `C_K`.
-/

@[expose] public section

open scoped NumberField
open NumberField

noncomputable section


variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

namespace RelativeIdeleGroup

omit [NumberField L] [FiniteDimensional K L] in
/-- The diagonal copy of `Lˣ` in the relative ideles is injective. -/
theorem principalIdele_injective :
    Function.Injective (principalIdele K L) := by
  exact Units.map_injective
    (Algebra.TensorProduct.includeRight_injective
      (B := L)
      (NumberField.AdeleRing.algebraMap_injective
        (R := 𝓞 K) (K := K)))

omit [NumberField L] [FiniteDimensional K L] in
/-- Galois conjugation preserves the principal-relative-idele
congruence, so it acts on the quotient class group. -/
instance principalQuotientAction :
    MulAction.QuotientAction (L ≃ₐ[K] L)
      (principalSubgroup K L) where
  inv_mul_mem σ {a a'} h := by
    rcases h with ⟨x, hx⟩
    refine
      ⟨Units.map σ.toRingEquiv.toMonoidHom x, ?_⟩
    rw [← smul_principalIdele K L σ x, hx]
    simp [smul_def]

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem smul_class_mk
    (σ : L ≃ₐ[K] L) (a : RelativeIdeleGroup K L) :
    σ •
        (QuotientGroup.mk'
          (principalSubgroup K L) a) =
      QuotientGroup.mk'
        (principalSubgroup K L) (σ • a) :=
  rfl

/-- The quotient Galois action on relative idele classes, viewed as an
action by group automorphisms. -/
@[reducible]
noncomputable def relativeIdeleClassMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (ClassGroup K L) := by
  letI := relativeIdeleMulDistribMulAction K L
  exact Function.Surjective.mulDistribMulAction
    (QuotientGroup.mk' (principalSubgroup K L))
    (QuotientGroup.mk'_surjective (principalSubgroup K L))
    (fun _ _ ↦ rfl)

/-- The subgroup of relative idele classes fixed by every Galois
automorphism. -/
def galoisFixedClassSubgroup :
    Subgroup (ClassGroup K L) := by
  letI := relativeIdeleClassMulDistribMulAction K L
  exact FixedPoints.subgroup (L ≃ₐ[K] L) (ClassGroup K L)

omit [NumberField L] [FiniteDimensional K L] in
/-- Every class coming from `C_K` is Galois fixed. -/
theorem classInclusion_range_le_galoisFixed :
    (classInclusion K L).range ≤
      galoisFixedClassSubgroup K L := by
  rintro _ ⟨c, rfl⟩
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk_surjective c
  intro σ
  change
    σ •
        QuotientGroup.mk'
          (principalSubgroup K L)
          (inclusion K L a) =
      QuotientGroup.mk'
        (principalSubgroup K L)
        (inclusion K L a)
  rw [smul_class_mk, smul_inclusion]

omit [NumberField L] in
/-- A Galois-fixed relative idele class has a Galois-fixed idele
representative. This is the Noether–Hilbert-90 step in idele-class descent. -/
theorem exists_fixed_representative_of_fixed_class
    (a : RelativeIdeleGroup K L)
    (ha :
      ∀ σ : L ≃ₐ[K] L,
        σ •
            QuotientGroup.mk'
              (principalSubgroup K L) a =
          QuotientGroup.mk'
            (principalSubgroup K L) a) :
    ∃ a' : RelativeIdeleGroup K L,
      QuotientGroup.mk'
          (principalSubgroup K L) a' =
        QuotientGroup.mk'
          (principalSubgroup K L) a ∧
      ∀ σ : L ≃ₐ[K] L, σ • a' = a' := by
  classical
  let := relativeIdeleMulDistribMulAction K L
  have hex :
      ∀ σ : L ≃ₐ[K] L,
        ∃ x : Lˣ,
          principalIdele K L x =
            (σ • a) / a := by
    intro σ
    have hmem :
        (σ • a) / a ∈ principalSubgroup K L := by
      exact (QuotientGroup.eq_iff_div_mem).1 (ha σ)
    exact hmem
  let f : (L ≃ₐ[K] L) → Lˣ :=
    fun σ ↦ Classical.choose (hex σ)
  have hf_spec :
      ∀ σ : L ≃ₐ[K] L,
        principalIdele K L (f σ) =
          (σ • a) / a :=
    fun σ ↦ Classical.choose_spec (hex σ)
  have hf_cocycle :
      groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    apply principalIdele_injective K L
    have hsmul :
        principalIdele K L (σ • f τ) =
          σ • principalIdele K L (f τ) := by
      calc
        principalIdele K L (σ • f τ) =
            principalIdele K L
              (Units.map
                σ.toRingEquiv.toMonoidHom (f τ)) := by
          congr 1
        _ = σ • principalIdele K L (f τ) :=
          (smul_principalIdele K L σ (f τ)).symm
    rw [map_mul, hsmul,
      hf_spec (σ * τ), hf_spec τ, hf_spec σ,
      smul_div', ← mul_smul]
    exact (div_mul_div_cancel _ _ _).symm
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
      f hf_cocycle
  let a' : RelativeIdeleGroup K L :=
    a / principalIdele K L β
  have hratio :
      ∀ σ : L ≃ₐ[K] L,
        (σ • principalIdele K L β) /
            principalIdele K L β =
          (σ • a) / a := by
    intro σ
    have hβ' :
        Units.map σ.toRingEquiv.toMonoidHom β / β =
          f σ := by
      calc
        Units.map σ.toRingEquiv.toMonoidHom β / β =
            σ • β / β := by
          congr 2
        _ = f σ := hβ σ
    rw [smul_principalIdele,
      ← map_div, hβ', hf_spec σ]
  have ha'fixed :
      ∀ σ : L ≃ₐ[K] L, σ • a' = a' := by
    intro σ
    change
      σ • (a / principalIdele K L β) =
        a / principalIdele K L β
    rw [smul_div']
    calc
      (σ • a) / (σ • principalIdele K L β) =
          ((σ • a) / a) *
            (a / (σ • principalIdele K L β)) := by
        exact (div_mul_div_cancel _ _ _).symm
      _ = ((σ • principalIdele K L β) /
            principalIdele K L β) *
          (a / (σ • principalIdele K L β)) := by
        rw [← hratio σ]
      _ = a / principalIdele K L β := by
        exact div_mul_div_cancel' _ _ _
  refine ⟨a', ?_, ha'fixed⟩
  apply (QuotientGroup.eq_iff_div_mem).2
  refine ⟨β⁻¹, ?_⟩
  change
    (principalIdele K L β)⁻¹ =
      (a / principalIdele K L β) / a
  simpa only [div_mul_eq_div_div] using
    (div_mul_cancel_right a
      (principalIdele K L β)).symm

omit [NumberField L] in
/-- Every Galois-fixed relative idele class comes from `C_K`. -/
theorem galoisFixed_le_classInclusion_range
    [IsGalois K L] :
    galoisFixedClassSubgroup K L ≤
      (classInclusion K L).range := by
  intro c hc
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk_surjective c
  have ha :
      ∀ σ : L ≃ₐ[K] L,
        σ •
            QuotientGroup.mk'
              (principalSubgroup K L) a =
          QuotientGroup.mk'
            (principalSubgroup K L) a :=
    hc
  obtain ⟨a', ha'class, ha'fixed⟩ :=
    exists_fixed_representative_of_fixed_class
      K L a ha
  have ha'mem :
      a' ∈ galoisFixedSubgroup K L :=
    ha'fixed
  rw [← inclusion_range_eq_galoisFixedSubgroup
    K L] at ha'mem
  obtain ⟨b, hb⟩ := ha'mem
  refine
    ⟨QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K) b, ?_⟩
  rw [classInclusion_mk, hb]
  exact ha'class

omit [NumberField L] in
/-- Galois descent for idele classes,
`C_L^{Gal(L/K)} = C_K`. -/
theorem classInclusion_range_eq_galoisFixedClassSubgroup
    [IsGalois K L] :
    (classInclusion K L).range =
      galoisFixedClassSubgroup K L :=
  le_antisymm
    (classInclusion_range_le_galoisFixed K L)
    (galoisFixed_le_classInclusion_range K L)

end RelativeIdeleGroup
