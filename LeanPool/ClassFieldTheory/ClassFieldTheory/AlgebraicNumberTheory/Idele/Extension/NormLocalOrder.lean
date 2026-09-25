/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
public import Mathlib.RingTheory.RamificationInertia.Inertia
/-!
# Local orders of finite-place norms

For a finite extension of number fields and a place upstairs, the order of
the concrete local field norm is the inertia degree times the upstairs
order.  The proof uses the actual norm–valuation theorem for finite separable
local-field extensions.  The two normalization comparisons needed here are
also concrete:

* the intrinsic local-field valuation is compared with the distinguished
  `ℤᵐ⁰`-valued completion valuation;
* the residue degree of the completed extension is identified with the
  inertia degree of the corresponding prime of the number-field extension.
-/

@[expose] public section

open scoped NumberField ValuativeRel WithZero
open NumberField IsDedekindDomain

noncomputable section

namespace FiniteIdeleGroup

universe u v w

private lemma withZeroMultiplicativeInt_le_exp_neg_one_of_lt_one
    (γ : WithZero (Multiplicative ℤ)) (hγ : γ < 1) :
    γ ≤ WithZero.exp (-1 : ℤ) := by
  cases γ using WithZero.recZeroCoe with
  | zero =>
      exact bot_le
  | coe γ =>
      rw [WithZero.exp_eq_coe_ofAdd, WithZero.coe_le_coe]
      rw [← Multiplicative.toAdd_le]
      change Multiplicative.toAdd γ ≤ (-1 : ℤ)
      have hγ' : Multiplicative.toAdd γ < (0 : ℤ) := by
        have : γ < (1 : Multiplicative ℤ) := by
          simpa using hγ
        change
          Multiplicative.toAdd γ <
            Multiplicative.toAdd (1 : Multiplicative ℤ)
        exact Multiplicative.toAdd_lt.mpr this
      omega

/-- A surjective standard integer valuation gives the same normalized
integer value as the intrinsic local-field valuation. -/
private theorem normalizedValue_eq_withZeroLog_of_surjective
    (F : Type w)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (ν : Valuation F (WithZero (Multiplicative ℤ)))
    [ν.Compatible]
    (hν : Function.Surjective ν)
    (x : Fˣ) :
    LocalFieldTheory.IsNonarchimedeanLocalField.v F
        (Additive.ofMul x) =
      WithZero.log (ν (x : F)) := by
  let ν₀ := ValuativeRel.valuation F
  have hEquiv : ν₀.IsEquiv ν :=
    ValuativeRel.isEquiv ν₀ ν
  obtain ⟨π, hπ⟩ :=
    hν (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  let ϖ : Fˣ := Units.mk0 π hπ0
  have hπlt : ν π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hπIntrinsicLt : ν₀ π < 1 :=
    hEquiv.lt_one_iff_lt_one.mpr hπlt
  have hπIntrinsicMax :
      ∀ γ : ValuativeRel.ValueGroupWithZero F,
        γ < 1 → γ ≤ ν₀ π := by
    intro γ hγ
    obtain ⟨y, hy⟩ :=
      ValuativeRel.valuation_surjective γ
    have hylt : ν y < 1 := by
      apply hEquiv.lt_one_iff_lt_one.mp
      simpa [ν₀, hy]
    have hyle : ν y ≤ ν π := by
      rw [hπ]
      exact
        withZeroMultiplicativeInt_le_exp_neg_one_of_lt_one
          (ν y) hylt
    have hyle' : ν₀ y ≤ ν₀ π :=
      hEquiv.le_iff_le.mpr hyle
    simpa [ν₀, hy] using hyle'
  let φ :=
    _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hφπ :
      φ (ν₀ π) = WithZero.exp (-1 : ℤ) := by
    apply le_antisymm
    · exact
        withZeroMultiplicativeInt_le_exp_neg_one_of_lt_one
          (φ (ν₀ π)) (by
            have h := φ.strictMono hπIntrinsicLt
            simpa [φ] using h)
    · let γ : ValuativeRel.ValueGroupWithZero F :=
        φ.symm (WithZero.exp (-1 : ℤ))
      have hγlt : γ < 1 := by
        have hneg :
            WithZero.exp (-1 : ℤ) <
              (1 : WithZero (Multiplicative ℤ)) := by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
          omega
        have h := φ.symm.strictMono hneg
        simpa [γ, φ] using h
      have hγle := hπIntrinsicMax γ hγlt
      have hmap := φ.toOrderIso.monotone hγle
      rw [← φ.apply_symm_apply (WithZero.exp (-1 : ℤ))]
      exact hmap
  have hϖValue :
      LocalFieldTheory.IsNonarchimedeanLocalField.v F
          (Additive.ofMul ϖ) = -1 := by
    rw [LocalFieldTheory.IsNonarchimedeanLocalField.v_apply]
    apply (WithZero.toAdd_unzero_eq_iff _ (-1 : ℤ)).2
    change
      φ (ν₀ ((ϖ : Fˣ) : F)) =
        ((Multiplicative.ofAdd (-1 : ℤ) :
            Multiplicative ℤ) :
          WithZero (Multiplicative ℤ))
    change
      φ (ν₀ π) =
        ((Multiplicative.ofAdd (-1 : ℤ) :
            Multiplicative ℤ) :
          WithZero (Multiplicative ℤ))
    simpa only [WithZero.exp_eq_coe_ofAdd] using hφπ
  let n : ℤ := WithZero.log (ν (x : F))
  let y : Fˣ := x * ϖ ^ n
  have hxν0 : ν (x : F) ≠ 0 :=
    (Valuation.ne_zero_iff ν).2 x.ne_zero
  have hyν : ν (y : F) = 1 := by
    have hϖν : ν (ϖ : F) = WithZero.exp (-1 : ℤ) := by
      simpa [ϖ] using hπ
    calc
      ν (y : F) =
          ν (x : F) * ν (ϖ : F) ^ n := by
            simp [y]
      _ =
          WithZero.exp n * WithZero.exp (-1 : ℤ) ^ n := by
            rw [← WithZero.exp_log hxν0]
            rw [hϖν]
      _ =
          WithZero.exp n *
            WithZero.exp (n • (-1 : ℤ)) := by
              rw [WithZero.exp_zsmul]
      _ = WithZero.exp (n + n • (-1 : ℤ)) := by
            rw [WithZero.exp_add]
      _ = 1 := by
            simp
  have hyInvν : ν ((y⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hyν, inv_one]
  have hyMem : (y : F) ∈ 𝒪[F] := by
    change ν₀ (y : F) ≤ 1
    exact hEquiv.le_one_iff_le_one.mpr (by rw [hyν])
  have hyInvMem : ((y⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    change ν₀ ((y⁻¹ : Fˣ) : F) ≤ 1
    exact hEquiv.le_one_iff_le_one.mpr (by rw [hyInvν])
  let yInteger : 𝒪[F]ˣ :=
    { val := ⟨(y : F), hyMem⟩
      inv := ⟨((y⁻¹ : Fˣ) : F), hyInvMem⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  have hyField :
      LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
          F yInteger =
        y := by
    apply Units.ext
    rfl
  have hyValue :
      LocalFieldTheory.IsNonarchimedeanLocalField.v F
          (Additive.ofMul y) = 0 := by
    rw [← hyField]
    exact
      LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits
        F yInteger
  have hdecomp : y * ϖ ^ (-n) = x := by
    rw [show y = x * ϖ ^ n by rfl, mul_assoc, zpow_neg,
      mul_inv_cancel, mul_one]
  have hdecompValue :=
    congrArg
      (fun z : Fˣ =>
        LocalFieldTheory.IsNonarchimedeanLocalField.v F
          (Additive.ofMul z))
      hdecomp
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.v_mul,
    hyValue,
    LocalFieldTheory.IsNonarchimedeanLocalField.v_zpow,
    hϖValue] at hdecompValue
  dsimp [n] at hdecompValue ⊢
  linarith

/-- Identity on the underlying field gives the equivalence between the
intrinsic valuation ring and the distinguished valued-field integer ring. -/
private noncomputable def intrinsicIntegerEquivValuedInteger
    (F : Type w)
    [Field F] [ValuativeRel F]
    [Valued F (WithZero (Multiplicative ℤ))]
    [(Valued.v :
      Valuation F (WithZero (Multiplicative ℤ))).Compatible] :
    𝒪[F] ≃+* Valued.integer F := by
  apply RingEquiv.subringCongr
  exact congrArg ValuationSubring.toSubring <|
    (Valuation.isEquiv_iff_valuationSubring
      (ValuativeRel.valuation F)
      (Valued.v : Valuation F (WithZero (Multiplicative ℤ)))).mp <|
      ValuativeRel.isEquiv
        (ValuativeRel.valuation F)
        (Valued.v :
          Valuation F (WithZero (Multiplicative ℤ)))

/-- The residue field for the intrinsic valuation is the residue field of
the distinguished `ℤᵐ⁰`-valued completion valuation. -/
private noncomputable def intrinsicResidueFieldEquivValuedResidueField
    (F : Type w)
    [Field F] [ValuativeRel F]
    [Valued F (WithZero (Multiplicative ℤ))]
    [(Valued.v :
      Valuation F (WithZero (Multiplicative ℤ))).Compatible] :
    𝓀[F] ≃+* Valued.ResidueField F :=
  IsLocalRing.ResidueField.mapEquiv
    (intrinsicIntegerEquivValuedInteger F)


private theorem absNorm_eq_card_intrinsicAdicResidueField
    (K : Type u) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    [ValuativeRel (v.adicCompletion K)]
    [(Valued.v :
      Valuation (v.adicCompletion K)
        (WithZero (Multiplicative ℤ))).Compatible] :
    Ideal.absNorm v.asIdeal =
      Nat.card 𝓀[v.adicCompletion K] := by
  calc
    Ideal.absNorm v.asIdeal =
        Nat.card
          (Valued.ResidueField (v.adicCompletion K)) := by
      rw [Ideal.absNorm_apply]
      exact
        Nat.card_congr
          (GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField
            (K := K) v).toEquiv
    _ = Nat.card 𝓀[v.adicCompletion K] := by
      exact
        (Nat.card_congr
          (intrinsicResidueFieldEquivValuedResidueField
            (v.adicCompletion K)).toEquiv).symm

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The local order of the actual norm between finite-place completions is
multiplied by the inertia degree of the upstairs prime. -/
theorem localOrder_normUnits
    (v₀ : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀})
    (x : (W.1.adicCompletion L)ˣ) :
    letI : Algebra
        (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    (localOrder v₀
      (LocalFieldTheory.normUnits
        (v₀.adicCompletion K) (W.1.adicCompletion L) x)).toAdd =
      (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        (localOrder W.1 x).toAdd := by
  classical
  let F := v₀.adicCompletion K
  let E := W.1.adicCompletion L
  let : Algebra F E :=
    (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
  let : IsScalarTower K F E :=
    finitePlaceAdicCompletionMap_isScalarTower K L v₀ W
  let : FiniteDimensional F E :=
    finitePlaceAdicCompletionMap_moduleFinite K L v₀ W
  let : CharZero F :=
    charZero_of_injective_algebraMap
      (algebraMap K F).injective
  let : Algebra.IsIntegral F E :=
    Algebra.IsIntegral.of_finite F E
  let : Algebra.IsSeparable F E :=
    Algebra.IsSeparable.of_integral F E
  let νF : Valuation F (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let νE : Valuation E (WithZero (Multiplicative ℤ)) :=
    Valued.v
  have hνF : Function.Surjective νF := by
    simpa [F, νF] using
      v₀.valuedAdicCompletion_surjective K
  have hνE : Function.Surjective νE := by
    simpa [E, νE] using
      W.1.valuedAdicCompletion_surjective L
  let : ValuativeRel F :=
    ValuativeRel.ofValuation νF
  let : ValuativeRel E :=
    ValuativeRel.ofValuation νE
  let : νF.Compatible :=
    Valuation.Compatible.ofValuation νF
  let : νE.Compatible :=
    Valuation.Compatible.ofValuation νE
  let : νF.IsNontrivial := by
    obtain ⟨π, hπ⟩ :=
      hνF (WithZero.exp (-1 : ℤ))
    refine ⟨⟨π, ?_, ?_⟩⟩
    · rw [hπ]
      simp
    · rw [hπ]
      change
        WithZero.exp (-1 : ℤ) ≠
          WithZero.exp (0 : ℤ)
      simp
  let : νE.IsNontrivial := by
    obtain ⟨π, hπ⟩ :=
      hνE (WithZero.exp (-1 : ℤ))
    refine ⟨⟨π, ?_, ?_⟩⟩
    · rw [hπ]
      simp
    · rw [hπ]
      change
        WithZero.exp (-1 : ℤ) ≠
          WithZero.exp (0 : ℤ)
      simp
  let : ValuativeRel.IsNontrivial F :=
    (ValuativeRel.isNontrivial_iff_isNontrivial νF).2
      inferInstance
  let : ValuativeRel.IsNontrivial E :=
    (ValuativeRel.isNontrivial_iff_isNontrivial νE).2
      inferInstance
  let : IsValuativeTopology F :=
    LocalFieldTheory.isValuativeTopology_of_valued_ofValuation
      F (WithZero (Multiplicative ℤ))
  let : IsValuativeTopology E :=
    LocalFieldTheory.isValuativeTopology_of_valued_ofValuation
      E (WithZero (Multiplicative ℤ))
  let : IsNonarchimedeanLocalField F :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : IsNonarchimedeanLocalField E :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let ν₀F := ValuativeRel.valuation F
  let ν₀E := ValuativeRel.valuation E
  let : W.1.asIdeal.LiesOver v₀.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  let : ν₀F.HasExtension ν₀E := by
    apply Valuation.HasExtension.ofComapInteger
    ext z
    change
      ν₀E (algebraMap F E z) ≤ 1 ↔
        ν₀F z ≤ 1
    rw [(ValuativeRel.isEquiv ν₀E νE).le_one_iff_le_one,
      (ValuativeRel.isEquiv ν₀F νF).le_one_iff_le_one]
    have hmap :
        νE (algebraMap F E z) =
          νF z ^
            W.1.asIdeal.ramificationIdx (𝓞 K) := by
      have h :=
        finitePlaceAdicCompletionMap_valued
          K L v₀ W z
      rw [Ideal.ramificationIdx'_eq_ramificationIdx
        v₀.asIdeal W.1.asIdeal v₀.ne_bot] at h
      exact h
    rw [hmap,
      pow_le_one_iff
        (W.1.asIdeal.ramificationIdx_pos
          (𝓞 K)).ne']
  let : Algebra 𝒪[F] E :=
    Algebra.ofSubsemiring 𝒪[F]
  let : IsIntegralClosure 𝒪[E] 𝒪[F] E :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure F E
  have hNormValue :=
    LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable
      F E x
  rw [
    normalizedValue_eq_withZeroLog_of_surjective
      F νF hνF
        (LocalFieldTheory.normUnits F E x),
    normalizedValue_eq_withZeroLog_of_surjective
      E νE hνE x
  ] at hNormValue
  have hResidueDegree :
      Module.finrank 𝓀[F] 𝓀[E] =
        W.1.asIdeal.inertiaDeg (𝓞 K) := by
    apply
      Nat.pow_right_injective
        (Nat.succ_le_iff.mpr
          (HeightOneSpectrum.one_lt_absNorm v₀))
    calc
      Ideal.absNorm v₀.asIdeal ^
            Module.finrank 𝓀[F] 𝓀[E] =
          Nat.card 𝓀[F] ^
            Module.finrank 𝓀[F] 𝓀[E] := by
              rw [
                absNorm_eq_card_intrinsicAdicResidueField
                  K v₀
              ]
      _ = Nat.card 𝓀[E] :=
        Module.natCard_eq_pow_finrank.symm
      _ = Ideal.absNorm W.1.asIdeal := by
        rw [
          absNorm_eq_card_intrinsicAdicResidueField
            L W.1
        ]
      _ =
          Ideal.absNorm v₀.asIdeal ^
            W.1.asIdeal.inertiaDeg (𝓞 K) := by
        exact
          (Ideal.absNorm_pow_inertiaDeg
            v₀.asIdeal W.1.asIdeal).symm
  rw [hResidueDegree] at hNormValue
  rw [localOrder_apply, localOrder_apply]
  change
    -WithZero.log
        (νF
          (LocalFieldTheory.normUnits F E x : F)) =
      (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        -WithZero.log (νE (x : E))
  calc
    -WithZero.log
          (νF
            (LocalFieldTheory.normUnits F E x : F)) =
        -((W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          WithZero.log (νE (x : E))) := by
            rw [hNormValue]
    _ =
        (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          -WithZero.log (νE (x : E)) := by
            ring

end FiniteIdeleGroup

end
