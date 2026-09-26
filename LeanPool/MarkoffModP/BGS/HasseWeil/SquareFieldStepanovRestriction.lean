/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.StepanovSquareVanishing
public import Mathlib.Tactic

/-!
# Stepanov restrictions over a square constant field

Let `S/K` be a quadratic extension of finite fields and put `s = #K`.
The square-field Stepanov argument is linear over the full constant field
`S`, but its two restrictions are related by the `s`-power automorphism.
Consequently the coefficients of the first restriction must be transformed
by that automorphism.  This is the semilinear point which is lost if an
`S`-rational point is treated merely as a degree-two place over `K`.

This file packages the coefficient transform and proves the local residue
identity.  It makes no point-count or smoothness assertion.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain
open scoped Polynomial BigOperators

noncomputable section


section Coefficients

variable (K S : Type*) [Field K] [Fintype K]
  [Field S] [Algebra K S]

/-- Apply the `#K`-power automorphism coefficientwise to a finite grid over
the square constant field. -/
def squareRootFrobeniusCoefficients {ι : Type*} (c : ι →₀ S) : ι →₀ S :=
  Finsupp.mapRange (powCardAlgHom K S 1) (map_zero (powCardAlgHom K S 1)) c

@[simp]
theorem squareRootFrobeniusCoefficients_apply
    {ι : Type*} (c : ι →₀ S) (i : ι) :
    squareRootFrobeniusCoefficients K S c i =
      (c i) ^ Fintype.card K := by
  simp [squareRootFrobeniusCoefficients, powCardAlgHom_apply]

theorem squareRootFrobeniusCoefficients_ne_zero
    {ι : Type*} {c : ι →₀ S} (hc : c ≠ 0) :
    squareRootFrobeniusCoefficients K S c ≠ 0 := by
  intro hzero
  apply hc
  apply Finsupp.mapRange_injective _ _ (powCardAlgHom K S 1).injective
  change squareRootFrobeniusCoefficients K S c =
    squareRootFrobeniusCoefficients K S 0
  rw [hzero]
  ext i
  simp [squareRootFrobeniusCoefficients]

end Coefficients

section Restriction

variable (K S : Type*) [Field K] [Fintype K]
  [Field S] [Fintype S] [DecidableEq S] [Algebra K S]
  [DecidableEq (RatFunc S)]
variable (L : Type*) [Field L] [Algebra (RatFunc S) L]
  [FiniteDimensional (RatFunc S) L]
  [Algebra.IsSeparable (RatFunc S) L]

local instance squareFieldRestrictionConstantAlgebra : Algebra S L :=
  RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
    (algebraMap S (RatFunc S)))

local instance squareFieldRestrictionConstantTower :
    IsScalarTower S (RatFunc S) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The first square-field restriction.  The function grid is
`f_i g_j^s`, while the coefficients are transformed by `c ↦ c^s`. -/
def squareFieldStepanovFirstRestriction
    {α β : Type*} (f : α → L) (g : β → L) (c : α × β →₀ S) : L :=
  onePointStepanovFirstRestrictionMap S L f g (Fintype.card K)
    (squareRootFrobeniusCoefficients K S c)

/-- The transformed first restriction has the same one-point pole budget as
the ordinary first restriction. -/
theorem squareFieldStepanovFirstRestriction_mem
    {α β : Type*} (P : FiniteExtensionPlace S L)
    (f : α → L) (g : β → L) (ell m : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace S L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace S L P m)
    (c : α × β →₀ S) :
    squareFieldStepanovFirstRestriction K S L f g c ∈
      finiteExtensionOnePointRiemannSpace S L P
        (ell + Fintype.card K * m) := by
  exact onePointStepanovFirstRestrictionMap_mem S L P f g ell m
    (Fintype.card K) hf hg (squareRootFrobeniusCoefficients K S c)

/-- Rank-nullity over the full square constant field produces a coefficient
grid killed by the second restriction.  Frobenius injectivity and linear
independence of the first grid make the transformed first restriction
nonzero. -/
theorem exists_squareFieldStepanovAuxiliary_of_target_finrank_upper
    {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteExtensionPlace S L)
    (f : α → L) (g : β → L) (ell m targetBound : ℕ)
    (hf : ∀ i, f i ∈ finiteExtensionOnePointRiemannSpace S L P ell)
    (hg : ∀ j, g j ∈ finiteExtensionOnePointRiemannSpace S L P m)
    (hLI : LinearIndependent S
      (fun ij : α × β => f ij.1 * (g ij.2) ^ Fintype.card K))
    (hupper : Module.finrank S
      (finiteExtensionOnePointRiemannSpace S L P
        (Fintype.card K * ell + m)) ≤ targetBound)
    (hnumeric : targetBound < Fintype.card α * Fintype.card β) :
    ∃ c : α × β →₀ S,
      c ≠ 0 ∧
      onePointStepanovSecondRestrictionMap S L f g
        (Fintype.card K) c = 0 ∧
      squareFieldStepanovFirstRestriction K S L f g c ≠ 0 := by
  obtain ⟨c, hc, hsecond, _hfirst⟩ :=
    exists_onePointStepanovAuxiliary_of_target_finrank_upper
      S L P f g ell m (Fintype.card K) targetBound
        hf hg hLI hupper hnumeric
  have hcFrob : squareRootFrobeniusCoefficients K S c ≠ 0 :=
    squareRootFrobeniusCoefficients_ne_zero K S hc
  have hinjective : Function.Injective
      (onePointStepanovFirstRestrictionMap S L f g (Fintype.card K)) :=
    onePointStepanovFirstRestrictionMap_injective_of_linearIndependent
      S L f g (Fintype.card K) hLI
  refine ⟨c, hc, ?_, ?_⟩
  · have h := congrArg Subtype.val hsecond
    simpa only [onePointStepanovSecondCodRestrictionMap_coe,
      Submodule.coe_zero] using h
  · intro hzero
    apply hcFrob
    apply hinjective
    rw [map_zero]
    simpa only [squareFieldStepanovFirstRestriction] using hzero

end Restriction

section LocalResidue

variable (K S R : Type*) [Field K] [Fintype K]
  [Field S] [Algebra K S]
  [CommRing R] [IsLocalRing R] [Algebra S R]
  [Algebra K R]

/-- With Frobenius-transformed coefficients, the residue of the first
restriction is the `#K`-power of the residue of the second restriction. -/
theorem squareFieldStepanovLocalResidue_first_eq_frobenius_second
    {α β : Type*} (F : α → R) (G : β → R) (c : α × β →₀ S)
    (hsquare : ∀ z : IsLocalRing.ResidueField R,
      z ^ (Fintype.card K) ^ 2 = z) :
    stepanovLocalResidueAlgHom S R
        (Finsupp.linearCombination S
          (fun ij : α × β =>
            F ij.1 * (G ij.2) ^ Fintype.card K)
          (squareRootFrobeniusCoefficients K S c)) =
      powCardAlgHom K (IsLocalRing.ResidueField R) 1
        (stepanovLocalResidueAlgHom S R
          (Finsupp.linearCombination S
            (fun ij : α × β =>
              (F ij.1) ^ Fintype.card K * G ij.2) c)) := by
  classical
  let ρ := stepanovLocalResidueAlgHom S R
  let φ := powCardAlgHom K (IsLocalRing.ResidueField R) 1
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  simp only [squareRootFrobeniusCoefficients]
  have hmap :
      (Finsupp.mapRange (powCardAlgHom K S 1)
          (map_zero (powCardAlgHom K S 1)) c).sum
          (fun ij a => a • (F ij.1 * G ij.2 ^ Fintype.card K)) =
        c.sum fun ij a =>
          (powCardAlgHom K S 1 a) •
            (F ij.1 * G ij.2 ^ Fintype.card K) := by
    exact Finsupp.sum_mapRange_index (fun ij =>
      zero_smul S (F ij.1 * G ij.2 ^ Fintype.card K))
  rw [hmap]
  change ρ (c.sum fun ij a =>
      (powCardAlgHom K S 1 a) •
        (F ij.1 * G ij.2 ^ Fintype.card K)) =
    φ (ρ (c.sum fun ij a =>
      a • (F ij.1 ^ Fintype.card K * G ij.2)))
  simp only [map_finsuppSum, map_smul, map_mul, map_pow]
  apply Finsupp.sum_congr
  intro ij hij
  dsimp only [φ]
  simp only [Algebra.smul_def, map_mul, map_pow,
    powCardAlgHom_apply, Nat.pow_one]
  rw [← pow_mul]
  rw [show (ρ (F ij.1)) ^ (Fintype.card K * Fintype.card K) =
      ρ (F ij.1) by
    simpa only [pow_two] using hsquare (ρ (F ij.1))]

end LocalResidue

section LocalOrder

variable (K S R L : Type*) [Field K] [Fintype K]
  [Field S] [Algebra K S]
  [CommRing R] [IsDedekindDomain R] [IsDiscreteValuationRing R]
  [Algebra S R] [Algebra K R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- Local DVR form of the semilinear square-field vanishing step. -/
theorem squareFieldStepanovLocal_first_eq_zero_or_order_pos
    {α β : Type*} (F : α → R) (G : β → R) (c : α × β →₀ S)
    (hsquare : ∀ z : IsLocalRing.ResidueField R,
      z ^ (Fintype.card K) ^ 2 = z)
    (hsecond :
      Finsupp.linearCombination S
        (fun ij : α × β =>
          (F ij.1) ^ Fintype.card K * G ij.2) c = 0) :
    algebraMap R L
        (Finsupp.linearCombination S
          (fun ij : α × β =>
            F ij.1 * (G ij.2) ^ Fintype.card K)
          (squareRootFrobeniusCoefficients K S c)) = 0 ∨
      0 < finitePlaceOrder
        (IsDiscreteValuationRing.maximalIdeal R)
        (algebraMap R L
          (Finsupp.linearCombination S
            (fun ij : α × β =>
              F ij.1 * (G ij.2) ^ Fintype.card K)
            (squareRootFrobeniusCoefficients K S c))) := by
  let a : R := Finsupp.linearCombination S
    (fun ij : α × β =>
      F ij.1 * (G ij.2) ^ Fintype.card K)
    (squareRootFrobeniusCoefficients K S c)
  have hresidue : stepanovLocalResidueAlgHom S R a = 0 := by
    have h := squareFieldStepanovLocalResidue_first_eq_frobenius_second
      K S R F G c hsquare
    change stepanovLocalResidueAlgHom S R a = _ at h
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

variable (K S : Type*) [Field K] [Fintype K]
  [Field S] [DecidableEq S] [Algebra K S]
  [DecidableEq (RatFunc S)]
variable (L : Type*) [Field L] [Algebra (RatFunc S) L]
  [FiniteDimensional (RatFunc S) L]
  [Algebra.IsSeparable (RatFunc S) L]

omit [DecidableEq S] in
/-- Finite-place form of semilinear square-field vanishing.  The function
field and its places are over the full constant field `S`; `K` supplies the
half-Frobenius exponent. -/
theorem squareFieldStepanovFirstRestriction_eq_zero_or_principalDivisor_pos_at_finitePlace
    {α β : Type*}
    (q : FiniteExtensionFinitePlace S L)
    (f : α → L) (g : β → L) (c : α × β →₀ S)
    (hfRegular : ∀ i,
      0 ≤ finiteExtensionPrincipalDivisor S L (f i) (.inl q))
    (hgRegular : ∀ j,
      0 ≤ finiteExtensionPrincipalDivisor S L (g j) (.inl q))
    (hsquare : ∀ z : q.asIdeal.ResidueField,
      z ^ (Fintype.card K) ^ 2 = z)
    (hsecond : onePointStepanovSecondRestrictionMap S L f g
      (Fintype.card K) c = 0) :
    squareFieldStepanovFirstRestriction K S L f g c = 0 ∨
      0 < finiteExtensionPrincipalDivisor S L
        (squareFieldStepanovFirstRestriction K S L f g c) (.inl q) := by
  let A := RatFuncFiniteIntegralClosure S L
  let R := FiniteExtensionFinitePlaceLocalRing S L q
  let : Algebra S L :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
      (algebraMap S (RatFunc S)))
  let : IsScalarTower S (RatFunc S) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S[X] L :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
      (algebraMap S[X] (RatFunc S)))
  let : IsScalarTower S[X] (RatFunc S) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S (RatFuncFiniteIntegralClosure S L) :=
    RingHom.toAlgebra
      ((algebraMap S[X] (RatFuncFiniteIntegralClosure S L)).comp
        (algebraMap S S[X]))
  let : IsScalarTower S S[X] (RatFuncFiniteIntegralClosure S L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsIntegral S[X] (RatFuncFiniteIntegralClosure S L) :=
    IsIntegralClosure.isIntegral_algebra S[X] L
  let : Module.Finite S[X] (RatFuncFiniteIntegralClosure S L) :=
    Module.IsNoetherian.finite S[X] (RatFuncFiniteIntegralClosure S L)
  let : Module.IsTorsionFree S[X] L :=
    Module.IsTorsionFree.trans_faithfulSMul S[X] (RatFunc S) L
  let : Module.IsTorsionFree S[X]
      (RatFuncFiniteIntegralClosure S L) :=
    IsIntegralClosure.isTorsionFree S[X] L
  let : IsDedekindDomain (RatFuncFiniteIntegralClosure S L) :=
    IsIntegralClosure.isDedekindDomain S[X] (RatFunc S) L
      (RatFuncFiniteIntegralClosure S L)
  let : IsFractionRing (RatFuncFiniteIntegralClosure S L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      S[X] (RatFunc S) L (RatFuncFiniteIntegralClosure S L)
  let : Algebra (RatFuncFiniteIntegralClosure S L)
      (RatFuncFiniteIntegralClosure S L) :=
    Algebra.id (RatFuncFiniteIntegralClosure S L)
  let localAlgebra : Algebra (RatFuncFiniteIntegralClosure S L)
      (FiniteExtensionFinitePlaceLocalRing S L q) :=
    OreLocalization.instAlgebra
  let := localAlgebra
  let : SMul (RatFuncFiniteIntegralClosure S L)
      (FiniteExtensionFinitePlaceLocalRing S L q) :=
    localAlgebra.toSMul
  let : Algebra S (FiniteExtensionFinitePlaceLocalRing S L q) :=
    OreLocalization.instAlgebra
  let := finiteExtensionFinitePlaceLocalAlgebra (K := S) (L := L) q
  let := finiteExtensionFinitePlaceLocalIsFractionRing (K := S) (L := L) q
  let : IsScalarTower S R L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    symm
    change finiteExtensionFinitePlaceLocalizationToField
      (K := S) (L := L) q (algebraMap S R x) = algebraMap S L x
    rw [show algebraMap S R x =
      algebraMap A R (algebraMap S A x) by rfl]
    rw [show finiteExtensionFinitePlaceLocalizationToField
        (K := S) (L := L) q (algebraMap A R (algebraMap S A x)) =
      algebraMap A L (algebraMap S A x) by
        exact DFunLike.congr_fun
          (finiteExtensionFinitePlaceLocalizationToField_comp_algebraMap
            (K := S) (L := L) q) (algebraMap S A x)]
    rfl
  let : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A q.ne_bot R
  let : Algebra K R := RingHom.toAlgebra
    ((algebraMap S R).comp (algebraMap K S))
  let eResidue :
      (RatFuncFiniteIntegralClosure S L ⧸ q.asIdeal) ≃+*
        IsLocalRing.ResidueField R :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal q.asIdeal R
  let eQuotientResidue :
      (RatFuncFiniteIntegralClosure S L ⧸ q.asIdeal) ≃+*
        q.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (algebraMap
        (RatFuncFiniteIntegralClosure S L ⧸ q.asIdeal)
        q.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal)
  have hsquareQuotient :
      ∀ z : RatFuncFiniteIntegralClosure S L ⧸ q.asIdeal,
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
        finiteExtensionFinitePlaceLocalOrderTop (K := S) (L := L) q (f i) := by
    by_cases hfi : f i = 0
    · simp [hfi, finiteExtensionFinitePlaceLocalOrderTop]
    · rw [finiteExtensionFinitePlaceLocalOrderTop_eq_principalDivisor
        S L q (f i) hfi]
      exact_mod_cast hfRegular i
  have hgTop (j : β) :
      (0 : WithTop ℤ) ≤
        finiteExtensionFinitePlaceLocalOrderTop (K := S) (L := L) q (g j) := by
    by_cases hgj : g j = 0
    · simp [hgj, finiteExtensionFinitePlaceLocalOrderTop]
    · rw [finiteExtensionFinitePlaceLocalOrderTop_eq_principalDivisor
        S L q (g j) hgj]
      exact_mod_cast hgRegular j
  let F : α → R := fun i => Classical.choose
    (finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
      (K := S) (L := L) q (f i) (hfTop i))
  let G : β → R := fun j => Classical.choose
    (finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
      (K := S) (L := L) q (g j) (hgTop j))
  have hF (i : α) : f i = algebraMap R L (F i) := by
    exact Classical.choose_spec
      (finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
        (K := S) (L := L) q (f i) (hfTop i))
  have hG (j : β) : g j = algebraMap R L (G j) := by
    exact Classical.choose_spec
      (finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
        (K := S) (L := L) q (g j) (hgTop j))
  let firstLocal : R := Finsupp.linearCombination S
    (fun ij : α × β =>
      F ij.1 * (G ij.2) ^ Fintype.card K)
    (squareRootFrobeniusCoefficients K S c)
  let secondLocal : R := Finsupp.linearCombination S
    (fun ij : α × β =>
      (F ij.1) ^ Fintype.card K * G ij.2) c
  let ι : R →ₗ[S] L := (IsScalarTower.toAlgHom S R L).toLinearMap
  have hfirstMap :
      squareFieldStepanovFirstRestriction K S L f g c =
        algebraMap R L firstLocal := by
    symm
    calc
      algebraMap R L firstLocal = ι firstLocal := rfl
      _ = Finsupp.linearCombination S
          (fun ij : α × β =>
            ι (F ij.1 * (G ij.2) ^ Fintype.card K))
          (squareRootFrobeniusCoefficients K S c) := by
        exact Finsupp.apply_linearCombination S ι _ _
      _ = Finsupp.linearCombination S
          (fun ij : α × β =>
            f ij.1 * (g ij.2) ^ Fintype.card K)
          (squareRootFrobeniusCoefficients K S c) := by
        apply congrArg (fun v => Finsupp.linearCombination S v
          (squareRootFrobeniusCoefficients K S c))
        funext ij
        change algebraMap R L
          (F ij.1 * (G ij.2) ^ Fintype.card K) = _
        rw [map_mul, map_pow, ← hF ij.1, ← hG ij.2]
      _ = squareFieldStepanovFirstRestriction K S L f g c := rfl
  have hsecondMap :
      onePointStepanovSecondRestrictionMap S L f g
          (Fintype.card K) c = algebraMap R L secondLocal := by
    symm
    calc
      algebraMap R L secondLocal = ι secondLocal := rfl
      _ = Finsupp.linearCombination S
          (fun ij : α × β =>
            ι ((F ij.1) ^ Fintype.card K * G ij.2)) c := by
        exact Finsupp.apply_linearCombination S ι _ c
      _ = Finsupp.linearCombination S
          (fun ij : α × β =>
            (f ij.1) ^ Fintype.card K * g ij.2) c := by
        apply congrArg (fun v => Finsupp.linearCombination S v c)
        funext ij
        change algebraMap R L
          ((F ij.1) ^ Fintype.card K * G ij.2) = _
        rw [map_mul, map_pow, ← hF ij.1, ← hG ij.2]
      _ = onePointStepanovSecondRestrictionMap S L f g
          (Fintype.card K) c := rfl
  have hsecondLocal : secondLocal = 0 := by
    apply IsFractionRing.injective R L
    rw [map_zero, ← hsecondMap]
    exact hsecond
  have hlocal := squareFieldStepanovLocal_first_eq_zero_or_order_pos
    K S R L F G c hsquareLocal hsecondLocal
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
