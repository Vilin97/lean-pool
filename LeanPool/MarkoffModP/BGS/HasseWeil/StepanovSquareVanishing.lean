/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FrobeniusRestriction
import LeanPool.MarkoffModP.BGS.HasseWeil.StepanovRestrictionMaps
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLeadingTermCancellation
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlaceCases
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlacePrincipalDivisor
import Mathlib.Tactic

/-!
# The quadratic Frobenius vanishing step

Let `q = #K`.  The two Stepanov restrictions use the grids

* `f i * (g j) ^ q`, and
* `(f i) ^ q * g j`.

At a place whose residue field satisfies `z ^ (q ^ 2) = z`, the residue of
the first grid is the `q`-Frobenius of the residue of the second grid.
Consequently, if the second restriction vanishes and all grid entries are
regular at the place, the first restriction either vanishes or has positive
order there.

The square-Frobenius identity is an explicit hypothesis.  In particular,
this file does not assert that every normalization place above a quadratic
extension point has residue degree at most two.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain
open scoped Polynomial nonZeroDivisors

noncomputable section


section LocalResidue

variable (K R : Type*) [Field K] [Fintype K]
  [CommRing R] [IsLocalRing R] [Algebra K R]

/-- The residue map of a local `K`-algebra, bundled as a `K`-algebra map. -/
def stepanovLocalResidueAlgHom :
    R →ₐ[K] IsLocalRing.ResidueField R :=
  Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal R)

omit [Fintype K] in
@[simp]
theorem stepanovLocalResidueAlgHom_apply (r : R) :
    stepanovLocalResidueAlgHom K R r =
      algebraMap R (IsLocalRing.ResidueField R) r := by
  rfl

/-- The first Stepanov residue is the `q`-Frobenius of the second residue
when every residue satisfies the quadratic Frobenius identity. -/
theorem stepanovLocalResidue_first_eq_frobenius_second
    {α β : Type*} (F : α → R) (G : β → R) (c : α × β →₀ K)
    (hsquare : ∀ z : IsLocalRing.ResidueField R,
      z ^ (Fintype.card K) ^ 2 = z) :
    stepanovLocalResidueAlgHom K R
        (Finsupp.linearCombination K
          (fun ij : α × β =>
            F ij.1 * (G ij.2) ^ Fintype.card K) c) =
      powCardAlgHom K (IsLocalRing.ResidueField R) 1
        (stepanovLocalResidueAlgHom K R
          (Finsupp.linearCombination K
            (fun ij : α × β =>
              (F ij.1) ^ Fintype.card K * G ij.2) c)) := by
  let ρ := stepanovLocalResidueAlgHom K R
  let φ := powCardAlgHom K (IsLocalRing.ResidueField R) 1
  have hbasis (ij : α × β) :
      ρ (F ij.1 * (G ij.2) ^ Fintype.card K) =
        φ (ρ ((F ij.1) ^ Fintype.card K * G ij.2)) := by
    dsimp only [ρ, φ]
    simp only [map_mul, map_pow, powCardAlgHom_apply, Nat.pow_one]
    rw [← pow_mul]
    rw [show (stepanovLocalResidueAlgHom K R (F ij.1)) ^
          (Fintype.card K * Fintype.card K) =
        stepanovLocalResidueAlgHom K R (F ij.1) by
      simpa only [pow_two] using
        hsquare (stepanovLocalResidueAlgHom K R (F ij.1))]
  calc
    ρ (Finsupp.linearCombination K
        (fun ij : α × β =>
          F ij.1 * (G ij.2) ^ Fintype.card K) c) =
      Finsupp.linearCombination K
        (fun ij : α × β =>
          ρ (F ij.1 * (G ij.2) ^ Fintype.card K)) c := by
        exact Finsupp.apply_linearCombination K ρ.toLinearMap _ c
    _ = Finsupp.linearCombination K
        (fun ij : α × β =>
          φ (ρ ((F ij.1) ^ Fintype.card K * G ij.2))) c := by
        apply congrArg (fun v => Finsupp.linearCombination K v c)
        funext ij
        exact hbasis ij
    _ = φ (Finsupp.linearCombination K
        (fun ij : α × β =>
          ρ ((F ij.1) ^ Fintype.card K * G ij.2)) c) := by
        exact (Finsupp.apply_linearCombination K φ.toLinearMap _ c).symm
    _ = φ (ρ (Finsupp.linearCombination K
        (fun ij : α × β =>
          (F ij.1) ^ Fintype.card K * G ij.2) c)) := by
        apply congrArg φ
        exact (Finsupp.apply_linearCombination K ρ.toLinearMap _ c).symm

end LocalResidue

section LocalOrder

variable (K R L : Type*) [Field K] [Fintype K]
  [CommRing R] [IsDedekindDomain R] [IsDiscreteValuationRing R]
  [Algebra K R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- Local DVR form of square-Frobenius vanishing.  If the second local
linear combination is zero, the first is either zero in the fraction field
or has positive order at the maximal ideal. -/
theorem stepanovLocal_first_eq_zero_or_order_pos
    {α β : Type*} (F : α → R) (G : β → R) (c : α × β →₀ K)
    (hsquare : ∀ z : IsLocalRing.ResidueField R,
      z ^ (Fintype.card K) ^ 2 = z)
    (hsecond :
      Finsupp.linearCombination K
        (fun ij : α × β =>
          (F ij.1) ^ Fintype.card K * G ij.2) c = 0) :
    algebraMap R L
        (Finsupp.linearCombination K
          (fun ij : α × β =>
            F ij.1 * (G ij.2) ^ Fintype.card K) c) = 0 ∨
      0 < finitePlaceOrder
        (IsDiscreteValuationRing.maximalIdeal R)
        (algebraMap R L
          (Finsupp.linearCombination K
            (fun ij : α × β =>
              F ij.1 * (G ij.2) ^ Fintype.card K) c)) := by
  let a : R := Finsupp.linearCombination K
    (fun ij : α × β =>
      F ij.1 * (G ij.2) ^ Fintype.card K) c
  have hresidue : stepanovLocalResidueAlgHom K R a = 0 := by
    have h := stepanovLocalResidue_first_eq_frobenius_second
      K R F G c hsquare
    change stepanovLocalResidueAlgHom K R a = _ at h
    rw [hsecond, map_zero, map_zero] at h
    exact h
  have haMem : a ∈ IsLocalRing.maximalIdeal R := by
    apply (IsLocalRing.residue_eq_zero_iff a).mp
    exact hresidue
  by_cases haMap : algebraMap R L a = 0
  · exact Or.inl haMap
  · refine Or.inr ?_
    have ha : a ≠ 0 := by
      intro ha0
      apply haMap
      rw [ha0, map_zero]
    have horder := one_le_finitePlaceOrder_algebraMap_of_mem
      (L := L) (IsDiscreteValuationRing.maximalIdeal R) a haMem ha
    change 0 < finitePlaceOrder
      (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R L a)
    omega

end LocalOrder

section FiniteExtensionPlace

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- Finite-place form used after the two Stepanov restriction maps.

The families are assumed regular at `q`.  The residue hypothesis is stated
on the canonical residue field `q.asIdeal.ResidueField`; it is transported
internally to the residue field of the localized DVR. -/
theorem onePointStepanovFirstRestrictionMap_eq_zero_or_principalDivisor_pos_at_finitePlace
    {α β : Type*}
    (q : FiniteExtensionFinitePlace K L)
    (f : α → L) (g : β → L) (c : α × β →₀ K)
    (hfRegular : ∀ i,
      0 ≤ finiteExtensionPrincipalDivisor K L (f i) (.inl q))
    (hgRegular : ∀ j,
      0 ≤ finiteExtensionPrincipalDivisor K L (g j) (.inl q))
    (hsquare : ∀ z : q.asIdeal.ResidueField,
      z ^ (Fintype.card K) ^ 2 = z)
    (hsecond : onePointStepanovSecondRestrictionMap K L f g
      (Fintype.card K) c = 0) :
    onePointStepanovFirstRestrictionMap K L f g
        (Fintype.card K) c = 0 ∨
      0 < finiteExtensionPrincipalDivisor K L
        (onePointStepanovFirstRestrictionMap K L f g
          (Fintype.card K) c) (.inl q) := by
  let A := RatFuncFiniteIntegralClosure K L
  let R := FiniteExtensionFinitePlaceLocalRing K L q
  let : Algebra K L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K (RatFunc K)))
  let : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra K[X] L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K[X] (RatFunc K)))
  let : IsScalarTower K[X] (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra K (RatFuncFiniteIntegralClosure K L) :=
    RingHom.toAlgebra
      ((algebraMap K[X] (RatFuncFiniteIntegralClosure K L)).comp
        (algebraMap K K[X]))
  let : IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
    IsIntegralClosure.isIntegral_algebra K[X] L
  let : Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
    Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)
  let : Module.IsTorsionFree K[X] L :=
    Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L
  let : Module.IsTorsionFree K[X]
      (RatFuncFiniteIntegralClosure K L) :=
    IsIntegralClosure.isTorsionFree K[X] L
  let : IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
    IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
      (RatFuncFiniteIntegralClosure K L)
  let : IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      K[X] (RatFunc K) L (RatFuncFiniteIntegralClosure K L)
  let : Algebra (RatFuncFiniteIntegralClosure K L)
      (RatFuncFiniteIntegralClosure K L) :=
    Algebra.id (RatFuncFiniteIntegralClosure K L)
  let localAlgebra : Algebra (RatFuncFiniteIntegralClosure K L)
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    OreLocalization.instAlgebra
  let := localAlgebra
  let : SMul (RatFuncFiniteIntegralClosure K L)
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    localAlgebra.toSMul
  let : Algebra K (FiniteExtensionFinitePlaceLocalRing K L q) :=
    OreLocalization.instAlgebra
  let := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  let := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  let : IsScalarTower K R L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    symm
    change finiteExtensionFinitePlaceLocalizationToField
      (K := K) (L := L) q (algebraMap K R x) = algebraMap K L x
    rw [show algebraMap K R x =
      algebraMap A R (algebraMap K A x) by rfl]
    rw [show finiteExtensionFinitePlaceLocalizationToField
        (K := K) (L := L) q (algebraMap A R (algebraMap K A x)) =
      algebraMap A L (algebraMap K A x) by
        exact DFunLike.congr_fun
          (finiteExtensionFinitePlaceLocalizationToField_comp_algebraMap
            (K := K) (L := L) q) (algebraMap K A x)]
    rfl
  let : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A q.ne_bot R
  let eResidue :
      (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal) ≃+*
        IsLocalRing.ResidueField R :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal q.asIdeal R
  let eQuotientResidue :
      (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal) ≃+*
        q.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (algebraMap
        (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal)
        q.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal)
  have hsquareQuotient :
      ∀ z : RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal,
        z ^ (Fintype.card K) ^ 2 = z := by
    intro z
    apply eQuotientResidue.injective
    simpa only [map_pow] using hsquare (eQuotientResidue z)
  have hsquareLocal : ∀ z : IsLocalRing.ResidueField R,
      z ^ (Fintype.card K) ^ 2 = z := by
    intro z
    have h := congrArg eResidue (hsquareQuotient (eResidue.symm z))
    simpa only [map_pow, RingEquiv.apply_symm_apply] using h
  have hfTop (i : α) :
      (0 : WithTop ℤ) ≤
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q (f i) := by
    by_cases hfi : f i = 0
    · simp [hfi, finiteExtensionFinitePlaceLocalOrderTop]
    · rw [finiteExtensionFinitePlaceLocalOrderTop_eq_principalDivisor
        K L q (f i) hfi]
      exact_mod_cast hfRegular i
  have hgTop (j : β) :
      (0 : WithTop ℤ) ≤
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q (g j) := by
    by_cases hgj : g j = 0
    · simp [hgj, finiteExtensionFinitePlaceLocalOrderTop]
    · rw [finiteExtensionFinitePlaceLocalOrderTop_eq_principalDivisor
        K L q (g j) hgj]
      exact_mod_cast hgRegular j
  let F : α → R := fun i => Classical.choose
    (finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
      (K := K) (L := L) q (f i) (hfTop i))
  let G : β → R := fun j => Classical.choose
    (finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
      (K := K) (L := L) q (g j) (hgTop j))
  have hF (i : α) : f i = algebraMap R L (F i) := by
    exact Classical.choose_spec
      (finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
        (K := K) (L := L) q (f i) (hfTop i))
  have hG (j : β) : g j = algebraMap R L (G j) := by
    exact Classical.choose_spec
      (finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
        (K := K) (L := L) q (g j) (hgTop j))
  let firstLocal : R := Finsupp.linearCombination K
    (fun ij : α × β =>
      F ij.1 * (G ij.2) ^ Fintype.card K) c
  let secondLocal : R := Finsupp.linearCombination K
    (fun ij : α × β =>
      (F ij.1) ^ Fintype.card K * G ij.2) c
  let ι : R →ₗ[K] L := (IsScalarTower.toAlgHom K R L).toLinearMap
  have hfirstMap :
      onePointStepanovFirstRestrictionMap K L f g (Fintype.card K) c =
        algebraMap R L firstLocal := by
    symm
    calc
      algebraMap R L firstLocal = ι firstLocal := rfl
      _ = Finsupp.linearCombination K
          (fun ij : α × β =>
            ι (F ij.1 * (G ij.2) ^ Fintype.card K)) c := by
        exact Finsupp.apply_linearCombination K ι _ c
      _ = Finsupp.linearCombination K
          (fun ij : α × β =>
            f ij.1 * (g ij.2) ^ Fintype.card K) c := by
        apply congrArg (fun v => Finsupp.linearCombination K v c)
        funext ij
        change algebraMap R L
          (F ij.1 * (G ij.2) ^ Fintype.card K) = _
        rw [map_mul, map_pow, ← hF ij.1, ← hG ij.2]
      _ = onePointStepanovFirstRestrictionMap K L f g
          (Fintype.card K) c := rfl
  have hsecondMap :
      onePointStepanovSecondRestrictionMap K L f g (Fintype.card K) c =
        algebraMap R L secondLocal := by
    symm
    calc
      algebraMap R L secondLocal = ι secondLocal := rfl
      _ = Finsupp.linearCombination K
          (fun ij : α × β =>
            ι ((F ij.1) ^ Fintype.card K * G ij.2)) c := by
        exact Finsupp.apply_linearCombination K ι _ c
      _ = Finsupp.linearCombination K
          (fun ij : α × β =>
            (f ij.1) ^ Fintype.card K * g ij.2) c := by
        apply congrArg (fun v => Finsupp.linearCombination K v c)
        funext ij
        change algebraMap R L
          ((F ij.1) ^ Fintype.card K * G ij.2) = _
        rw [map_mul, map_pow, ← hF ij.1, ← hG ij.2]
      _ = onePointStepanovSecondRestrictionMap K L f g
          (Fintype.card K) c := rfl
  have hsecondLocal : secondLocal = 0 := by
    apply IsFractionRing.injective R L
    rw [map_zero, ← hsecondMap]
    exact hsecond
  have hlocal := stepanovLocal_first_eq_zero_or_order_pos
    K R L F G c hsquareLocal hsecondLocal
  rcases hlocal with hzero | hpositive
  · exact Or.inl (by rw [hfirstMap]; exact hzero)
  · refine Or.inr ?_
    rw [hfirstMap,
      finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder,
      ← finiteExtensionFinitePlaceLocalOrder_eq_globalOrder q]
    change 0 < finitePlaceOrder
      (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R L firstLocal)
    exact hpositive

end FiniteExtensionPlace

end

end BGS.HasseWeil
