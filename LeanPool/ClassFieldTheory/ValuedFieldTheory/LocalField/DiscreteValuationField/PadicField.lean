/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.Homomorphisms
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
/-!
# The concrete p-adic field `ℚ_[p]`

This file is the first concrete example leaf for the DVF navigation library.
It deliberately uses mathlib's public p-adic objects directly in theorem
statements instead of introducing public aliases for `ℚ_[p]` or its unit group.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField
namespace Examples
namespace Qp

open Filter
open scoped Topology
open scoped WithZero

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

/-- The neighbourhood filter on `ℚ_[p]` induced by `Padic.mulValuation`.
This keeps statements below on the valuation topology instead of the ambient
metric topology selected by the global `ℚ_[p]` instance. -/
noncomputable def padicMulValuationNhds
    (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : Filter ℚ_[p] :=
  @nhds ℚ_[p] (@UniformSpace.toTopologicalSpace ℚ_[p]
    (Valued.mk' (Padic.mulValuation (p := p))).toUniformSpace) x

/-- Characterization of the named neighbourhood filter by the topology
transported from `Padic.mulValuation`. -/
theorem padicMulValuationNhds_eq_valuedNhds
    (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    padicMulValuationNhds p x =
      @nhds ℚ_[p] (@UniformSpace.toTopologicalSpace ℚ_[p]
        (Valued.mk' (Padic.mulValuation (p := p))).toUniformSpace) x :=
  rfl

/-- The DVR valuation on `ℚ_[p]` obtained from the discrete valuation ring
`ℤ_[p]`.  This is the chosen-valuation side of the local-field structure theory,
the local-field structure classification, for the basic `p`-adic field. -/
abbrev padicDVRValuation (p : ℕ) [Fact p.Prime] :
    _root_.Valuation ℚ_[p] ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]

/-- The valuation subring of the DVR valuation on `ℚ_[p]` is the usual
`p`-adic integer ring. -/
noncomputable def padicIntEquivValuationSubring
    (p : ℕ) [Fact p.Prime] :
    ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
  IsDiscreteValuationRing.equivValuationSubring (A := ℤ_[p]) (K := ℚ_[p])

/-- The valuation-subring equivalence is the usual inclusion into `ℚ_[p]`
after forgetting the integrality proof. -/
@[simp]
theorem padicIntEquivValuationSubring_coe
    (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) :
    ((padicIntEquivValuationSubring p x :
        (padicDVRValuation p).valuationSubring) : ℚ_[p]) =
      (x : ℚ_[p]) :=
  rfl

/-- The residue field of `ℤ_[p]` is `ZMod p`. -/
noncomputable def padicIntResidueFieldEquivZMod
    (p : ℕ) [Fact p.Prime] :
    IsLocalRing.ResidueField ℤ_[p] ≃+* ZMod p :=
  PadicInt.residueField

/-- The residue field of `ℤ_[p]` is finite. -/
theorem padicInt_residueField_finite
    (p : ℕ) [Fact p.Prime] :
    Finite (IsLocalRing.ResidueField ℤ_[p]) :=
  Finite.of_equiv (ZMod p)
    (padicIntResidueFieldEquivZMod p).symm.toEquiv

/-- The valuation in `(padicDVRValuation p).IsRankOneDiscrete` is rank-one and discrete. -/
instance padicDVRValuation_isRankOneDiscrete
    (p : ℕ) [Fact p.Prime] :
    (padicDVRValuation p).IsRankOneDiscrete := by
  dsimp [padicDVRValuation]
  infer_instance

/-- The canonical prime element has normalized value `exp (-1)` for the
chosen DVR valuation on `ℚ_[p]`. -/
theorem padicDVRValuation_apply_p
    (p : ℕ) [Fact p.Prime] :
    padicDVRValuation p (p : ℚ_[p]) =
      WithZero.exp (-1 : ℤ) := by
  change (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
      (((p : ℤ_[p]) : ℚ_[p])) = WithZero.exp (-1 : ℤ)
  calc
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
        (((p : ℤ_[p]) : ℚ_[p])) =
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation
          (p : ℤ_[p]) := by
      simpa using
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation_of_algebraMap
          (K := ℚ_[p]) (p : ℤ_[p])
    _ = WithZero.exp (-1 : ℤ) :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p])
        (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
        PadicInt.maximalIdeal_eq_span_p

/-- The canonical prime element is a uniformizer for the chosen DVR
valuation on `ℚ_[p]`. -/
theorem padicDVRValuation_isUniformizer_p
    (p : ℕ) [Fact p.Prime] :
    (padicDVRValuation p).IsUniformizer (p : ℚ_[p]) :=
  WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
    (padicDVRValuation p) (p : ℚ_[p])
    (padicDVRValuation_apply_p p)

/-- The valuation subring of the DVR valuation on `ℚ_[p]` is complete for its
maximal-ideal topology.  The proof transports mathlib's adic completeness of
`ℤ_[p]` across the explicit valuation-subring equivalence. -/
theorem padicDVRValuation_isAdicComplete
    (p : ℕ) [Fact p.Prime] :
    IsAdicComplete
      (IsLocalRing.maximalIdeal (padicDVRValuation p).valuationSubring)
      (padicDVRValuation p).valuationSubring := by
  let e : ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
    padicIntEquivValuationSubring p
  let : Algebra ℤ_[p] (padicDVRValuation p).valuationSubring :=
    e.toRingHom.toAlgebra
  let eLin : ℤ_[p] ≃ₗ[ℤ_[p]] (padicDVRValuation p).valuationSubring :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r x
        change e (r * x) =
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring r) * e x
        simp [RingHom.algebraMap_toAlgebra] }
  have hcompleteZp :
      IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] :=
    inferInstance
  let : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] :=
    hcompleteZp
  have hcompleteAsZp :
      IsAdicComplete
        (IsLocalRing.maximalIdeal ℤ_[p])
        (padicDVRValuation p).valuationSubring :=
    isAdicComplete_of_linearEquiv
      (M := ℤ_[p]) (N := (padicDVRValuation p).valuationSubring)
      (IsLocalRing.maximalIdeal ℤ_[p]) eLin
  have hcompleteMap :
      IsAdicComplete
        ((IsLocalRing.maximalIdeal ℤ_[p]).map
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring))
        (padicDVRValuation p).valuationSubring :=
    (isAdicComplete_map_algebraMap_iff
      (I := IsLocalRing.maximalIdeal ℤ_[p])
      (S := (padicDVRValuation p).valuationSubring)).2 hcompleteAsZp
  have hmem (x : ℤ_[p]) :
      algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring x ∈
          IsLocalRing.maximalIdeal (padicDVRValuation p).valuationSubring ↔
        x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hx hunit
      exact hx (hunit.map (algebraMap ℤ_[p]
        (padicDVRValuation p).valuationSubring))
    · intro hx hunit
      apply hx
      have hpre := hunit.map e.symm.toRingHom
      simpa [RingHom.algebraMap_toAlgebra] using hpre
  have hmapMax :
      (IsLocalRing.maximalIdeal ℤ_[p]).map
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring) =
        IsLocalRing.maximalIdeal (padicDVRValuation p).valuationSubring := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (hmem x).2 hx
    · intro y hy
      have hx :
          e.symm y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
        apply (hmem (e.symm y)).1
        simpa [RingHom.algebraMap_toAlgebra] using hy
      have hmap :=
        Ideal.mem_map_of_mem
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring) hx
      simpa [RingHom.algebraMap_toAlgebra] using hmap
  simpa [hmapMax] using hcompleteMap

/-- The standard `p`-adic valuation is complete as a discrete valuation. -/
instance padicDVRValuation_isCompleteDiscrete
    (p : ℕ) [Fact p.Prime] :
    Valuation.IsCompleteDiscrete (padicDVRValuation p) where
  isAdicComplete := padicDVRValuation_isAdicComplete p

/-- The concrete complete-DVF package for the `p`-adic field `ℚ_[p]`. -/
noncomputable def padicCompleteDVF
    (p : ℕ) [Fact p.Prime] :
    CompleteDVF ℚ_[p] where
  ValueGroup := ℤᵐ⁰
  valuation := padicDVRValuation p
  instCompleteDiscrete := inferInstance

/-- The residue field of the complete-DVF package on `ℚ_[p]` is finite. -/
theorem padicCompleteDVF_residueField_finite
    (p : ℕ) [Fact p.Prime] :
    Finite (padicCompleteDVF p).residueField := by
  let e : ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
    padicIntEquivValuationSubring p
  let : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    padicInt_residueField_finite p
  have hfiniteVal :
      Finite (IsLocalRing.ResidueField
        (padicDVRValuation p).valuationSubring) :=
    Finite.of_equiv (IsLocalRing.ResidueField ℤ_[p])
      (IsLocalRing.ResidueField.mapEquiv e)
  simpa [padicCompleteDVF, CompleteDVF.residueField,
    CompleteDVF.valuationSubring, CompleteDVF.toDVF] using hfiniteVal

/-- The residue field of the concrete complete-DVF package on `ℚ_[p]` has
cardinality exactly `p`. -/
theorem padicCompleteDVF_residueField_card
    (p : ℕ) [Fact p.Prime] :
    Nat.card (padicCompleteDVF p).residueField = p := by
  let eO : ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
    padicIntEquivValuationSubring p
  let eRes :
      IsLocalRing.ResidueField (padicDVRValuation p).valuationSubring ≃+*
        ZMod p :=
    (IsLocalRing.ResidueField.mapEquiv eO).symm.trans
      (padicIntResidueFieldEquivZMod p)
  change
    Nat.card
        (IsLocalRing.ResidueField
          (padicDVRValuation p).valuationSubring) =
      p
  calc
    Nat.card
        (IsLocalRing.ResidueField
          (padicDVRValuation p).valuationSubring) =
        Nat.card (ZMod p) :=
      Nat.card_congr eRes.toEquiv
    _ = p := Nat.card_zmod p

/-- The local-field structure theory, the local-field structure classification, `p`-adic
base-field direction:
`ℚ_[p]` is a local field in the chosen-complete-DVF sense used in this
formalization. -/
noncomputable def padicLocalField
    (p : ℕ) [Fact p.Prime] :
    LocalField ℚ_[p] := by
  let F : CompleteDVF ℚ_[p] := padicCompleteDVF p
  haveI : Finite F.residueField := by
    simpa [F] using padicCompleteDVF_residueField_finite p
  exact { toCompleteDVF := F }

/-- mathlib's bundled p-adic multiplicative valuation has the expected value
on nonzero natural-number denominators. -/
theorem padic_mulValuation_natCast_of_ne_zero
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Padic.mulValuation (p := p) ((n : ℕ) : ℚ_[p]) =
      WithZero.exp (-(padicValNat p n : ℤ)) := by
  have hnQp : (((n : ℕ) : ℚ_[p]) ≠ 0) :=
    Nat.cast_ne_zero.mpr hn
  simp [Padic.mulValuation, hnQp]

/-- Successor form of the natural-number denominator valuation used in the
logarithm-series estimate. -/
theorem padic_mulValuation_logSeries_denominator
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Padic.mulValuation (p := p) ((n + 1 : ℕ) : ℚ_[p]) =
      WithZero.exp (-(padicValNat p (n + 1) : ℤ)) := by
  simpa using
    padic_mulValuation_natCast_of_ne_zero
      p (n + 1) (Nat.succ_ne_zero n)

/-- Factorial-denominator form used by the exponential-series estimate. -/
theorem padic_mulValuation_expSeries_denominator
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Padic.mulValuation (p := p) ((n.factorial : ℕ) : ℚ_[p]) =
      WithZero.exp (-(padicValNat p n.factorial : ℤ)) := by
  simpa using
    padic_mulValuation_natCast_of_ne_zero
      p n.factorial (Nat.factorial_ne_zero n)

/-- Standard p-adic specialization of the logarithm-term convergence estimate:
if `v x < 1` for mathlib's `Padic.mulValuation`, then the unsigned
logarithm-series terms tend to zero. -/
theorem tendsto_zero_logSeriesTermField_padic_mulValuation_of_lt_one
    (p : ℕ) [Fact p.Prime] (x : ℚ_[p])
    (hvx : Padic.mulValuation (p := p) x <
      (1 : WithZero (Multiplicative ℤ))) :
    Tendsto
      (fun n : ℕ =>
        MultiplicativeIntegerValuation.logSeriesTermField x
          (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) n)
      atTop (padicMulValuationNhds p (0 : ℚ_[p])) := by
  rw [padicMulValuationNhds_eq_valuedNhds]
  exact
    MultiplicativeIntegerValuation.tendsto_zero_logSeriesTermField_ofWithZeroValuation_of_lt_one
      (v := Padic.mulValuation (p := p)) (p := p) x
      (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      (padic_mulValuation_logSeries_denominator p) hvx

/-- Signed version of
`tendsto_zero_logSeriesTermField_padic_mulValuation_of_lt_one`. -/
theorem tendsto_zero_signedLogSeriesTermField_padic_mulValuation_of_lt_one
    (p : ℕ) [Fact p.Prime] (x : ℚ_[p])
    (hvx : Padic.mulValuation (p := p) x <
      (1 : WithZero (Multiplicative ℤ))) :
    Tendsto
      (fun n : ℕ =>
        MultiplicativeIntegerValuation.signedLogSeriesTermField x
          (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) n)
      atTop (padicMulValuationNhds p (0 : ℚ_[p])) := by
  rw [padicMulValuationNhds_eq_valuedNhds]
  exact
    MultiplicativeIntegerValuation.tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
      (v := Padic.mulValuation (p := p)) (p := p) x
      (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      (padic_mulValuation_logSeries_denominator p) hvx

/-- Standard p-adic specialization of the exponential-term convergence
estimate on the radius `v x < exp (-1)`. -/
theorem tendsto_zero_expSeriesTermField_padic_mulValuation_of_lt_exp_neg_one
    (p : ℕ) [Fact p.Prime] (x : ℚ_[p])
    (hvx : Padic.mulValuation (p := p) x < WithZero.exp (-1 : ℤ)) :
    Tendsto
      (fun n : ℕ =>
        MultiplicativeIntegerValuation.expSeriesTermField x
          (fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) n)
      atTop (padicMulValuationNhds p (0 : ℚ_[p])) := by
  rw [padicMulValuationNhds_eq_valuedNhds]
  exact
    MultiplicativeIntegerValuation.tendsto_zero_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := Padic.mulValuation (p := p)) (p := p) x
      (fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      (padic_mulValuation_expSeries_denominator p) hvx

/-- Membership in mathlib's `p^m`-power roots of unity inside the actual
p-adic unit group is the usual unit equation. -/
theorem mem_rootsOfUnity_padic_iff
    (p m : ℕ) [Fact p.Prime] (ζ : (ℚ_[p])ˣ) :
    ζ ∈ rootsOfUnity (p ^ m) ℚ_[p] ↔ ζ ^ (p ^ m) = 1 :=
  mem_rootsOfUnity (p ^ m) ζ

/-- The same roots-of-unity criterion after coercing the p-adic unit to
`ℚ_[p]`. -/
theorem mem_rootsOfUnity_padic_iff_coe_pow
    (p m : ℕ) [Fact p.Prime] (ζ : (ℚ_[p])ˣ) :
    ζ ∈ rootsOfUnity (p ^ m) ℚ_[p] ↔
      ((ζ : ℚ_[p]) ^ (p ^ m) = 1) :=
  mem_rootsOfUnity' (p ^ m) ζ

/-- The identity p-adic unit lies in every finite p-power roots-of-unity
subgroup. -/
theorem one_mem_rootsOfUnity_padic
    (p m : ℕ) [Fact p.Prime] :
    (1 : (ℚ_[p])ˣ) ∈ rootsOfUnity (p ^ m) ℚ_[p] :=
  (mem_rootsOfUnity_padic_iff p m 1).2 (by simp)

/-- A primitive p-adic `p^m`-power root is a root of mathlib's corresponding
cyclotomic polynomial over `ℚ_[p]`. -/
theorem primitiveRoot_isRoot_cyclotomic_padic
    (p m : ℕ) [Fact p.Prime] {ζ : ℚ_[p]}
    (hζ : IsPrimitiveRoot ζ (p ^ m)) :
    (Polynomial.cyclotomic (p ^ m) ℚ_[p]).IsRoot ζ := by
  exact IsPrimitiveRoot.isRoot_cyclotomic
    (pow_pos (Fact.out : Nat.Prime p).pos m) hζ

end Qp
end Examples
end LocalFieldTheory.DiscreteValuationField

end
