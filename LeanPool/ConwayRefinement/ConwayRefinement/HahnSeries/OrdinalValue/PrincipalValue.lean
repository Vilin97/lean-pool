/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.MultiplicativelyPrincipal
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.LeastTerm

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SuccessorFactorization
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.GeneralFactorization

/-!
# Principal and residual ordinal values

Berarducci, Definition 6.4 assigns principal and residual values to a nonpositive Hahn series
`b` whose ordinal value satisfies `1 < v_J(b)`. Its value is a positive additive-principal
ordinal, and therefore has a unique nonincreasing factorisation into infinite multiplicatively
principal ordinals greater than one. The principal value is the final factor. The residual value
is the product of all preceding factors, with value one when there is only one factor.

`SeriesWithOrdinalValueAboveOne` is the exact domain of these operations. The definitions therefore
have no arbitrary branch at ordinal values zero and one. Both values are represented by
`NatOrdinal`: this makes Berarducci's Hessenberg-product reconstruction directly available while
the corresponding theorem on underlying ordinary ordinals records the product printed in the
source.

The factor list and its ordinary-versus-Hessenberg product comparison are provided by the ordinal
factorisation module. The image theorem for `ordinalValue` supplies the additive-principality
hypothesis required to enter its exact domain.
-/

universe v

open scoped NatOrdinal

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- Nonpositive Hahn series in the exact domain of Berarducci's principal and residual values. -/
abbrev SeriesWithOrdinalValueAboveOne (K : Type v) [Field K] :=
  {b : Series K // 1 < ordinalValue b}

namespace SeriesWithOrdinalValueAboveOne

private def factorOrdinal (b : SeriesWithOrdinalValueAboveOne K) :
    Ordinal.AdditivePrincipalAboveOne :=
  ⟨(ordinalValue b.1).val, ordinalValue_isAdditivelyPrincipal_of_one_lt b.2, b.2⟩

/-- The final factor in the canonical multiplicative factorisation of `v_J(b)`. -/
noncomputable def principalValue (b : SeriesWithOrdinalValueAboveOne K) : NatOrdinal :=
  NatOrdinal.of b.factorOrdinal.principalFactor

/-- The product of all but the final factor in the canonical factorisation of `v_J(b)`. -/
noncomputable def residualValue (b : SeriesWithOrdinalValueAboveOne K) : NatOrdinal :=
  NatOrdinal.of b.factorOrdinal.residualFactor

/-- The principal value is an infinite multiplicatively principal ordinal. -/
theorem principalValue_isInfiniteMultiplicativelyPrincipal
    (b : SeriesWithOrdinalValueAboveOne K) :
    Ordinal.IsInfiniteMultiplicativelyPrincipal b.principalValue.val := by
  simp only [principalValue, NatOrdinal.val_of]
  exact b.factorOrdinal.principalFactor_isInfiniteMultiplicativelyPrincipal

/-- The principal value satisfies Berarducci's printed multiplicative-principality predicate. -/
theorem principalValue_isMultiplicativelyPrincipal
    (b : SeriesWithOrdinalValueAboveOne K) :
    Ordinal.IsMultiplicativelyPrincipal b.principalValue.val :=
  (Ordinal.isInfiniteMultiplicativelyPrincipal_iff_two_lt_and_isMultiplicativelyPrincipal.mp
    b.principalValue_isInfiniteMultiplicativelyPrincipal).2

/-- The principal value is strictly greater than one. -/
theorem one_lt_principalValue (b : SeriesWithOrdinalValueAboveOne K) :
    1 < b.principalValue := by
  change NatOrdinal.of (1 : Ordinal) <
    NatOrdinal.of b.factorOrdinal.principalFactor
  exact NatOrdinal.of.lt_iff_lt.mpr b.factorOrdinal.one_lt_principalFactor

/-- The residual value is a positive additive-principal ordinal. -/
theorem residualValue_isAdditivelyPrincipal
    (b : SeriesWithOrdinalValueAboveOne K) :
    Ordinal.IsAdditivelyPrincipal b.residualValue.val := by
  simp only [residualValue, NatOrdinal.val_of]
  exact b.factorOrdinal.residualFactor_isAdditivelyPrincipal

/-- The residual value is nonzero. -/
theorem residualValue_ne_zero (b : SeriesWithOrdinalValueAboveOne K) :
    b.residualValue ≠ 0 := by
  intro hzero
  apply b.residualValue_isAdditivelyPrincipal.ne_zero
  have hval := congrArg NatOrdinal.val hzero
  simpa using hval

/-- Ordinary ordinal multiplication of the residual and principal values recovers `v_J(b)`. -/
theorem residualValue_val_mul_principalValue_val
    (b : SeriesWithOrdinalValueAboveOne K) :
    b.residualValue.val * b.principalValue.val = (ordinalValue b.1).val := by
  simpa only [residualValue, principalValue, NatOrdinal.val_of, factorOrdinal] using
    b.factorOrdinal.residualFactor_mul_principalFactor

/-- Hessenberg multiplication of the residual and principal values also recovers `v_J(b)`. -/
theorem residualValue_mul_principalValue
    (b : SeriesWithOrdinalValueAboveOne K) :
    b.residualValue * b.principalValue = ordinalValue b.1 := by
  change NatOrdinal.of b.factorOrdinal.residualFactor *
      NatOrdinal.of b.factorOrdinal.principalFactor = ordinalValue b.1
  rw [b.factorOrdinal.naturalResidual_mul_naturalPrincipal]
  simp [factorOrdinal]

/-- Every canonical multiplicative factor of the ordinal value is at least the principal value,
read on Cantor terms of the logarithm. -/
theorem log_principalValue_le_of_mem_terms_ordinalValue
    (b : SeriesWithOrdinalValueAboveOne K) {t : Ordinal}
    (ht : t ∈ (Ordinal.log Ordinal.omega0 (ordinalValue b.1).val).additivePrincipalTerms) :
    Ordinal.log Ordinal.omega0 b.principalValue.val ≤ t := by
  have h := b.factorOrdinal.log_principalFactor_le_of_mem_terms ht
  simpa [principalValue] using h

/-- The same bound for the canonical factors of the residual value. -/
theorem log_principalValue_le_of_mem_terms_residualValue
    (b : SeriesWithOrdinalValueAboveOne K) {t : Ordinal}
    (ht : t ∈ (Ordinal.log Ordinal.omega0 b.residualValue.val).additivePrincipalTerms) :
    Ordinal.log Ordinal.omega0 b.principalValue.val ≤ t := by
  have hmem : t ∈
      (Ordinal.log Ordinal.omega0 b.factorOrdinal.1).additivePrincipalTerms :=
    b.factorOrdinal.mem_terms_of_mem_terms_log_residualFactor (by simpa [residualValue] using ht)
  have h := b.factorOrdinal.log_principalFactor_le_of_mem_terms hmem
  simpa [principalValue] using h

/-- The logarithm of the principal value is additive principal. -/
theorem isAdditivelyPrincipal_log_principalValue (b : SeriesWithOrdinalValueAboveOne K) :
    Ordinal.IsAdditivelyPrincipal (Ordinal.log Ordinal.omega0 b.principalValue.val) := by
  obtain ⟨e, he⟩ := Ordinal.isInfiniteMultiplicativelyPrincipal_iff.mp
    b.principalValue_isInfiniteMultiplicativelyPrincipal
  rw [he, Ordinal.log_opow Ordinal.one_lt_omega0]
  exact Ordinal.isAdditivelyPrincipal_omega0_opow e

/-- The principal value is the power of `ω` at that logarithm. -/
theorem principalValue_val_eq_opow_log (b : SeriesWithOrdinalValueAboveOne K) :
    Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 b.principalValue.val = b.principalValue.val :=
  (b.principalValue_isInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal).opow_log_self

/-- The residual value is strictly smaller than the ordinal value. -/
theorem residualValue_lt_ordinalValue (b : SeriesWithOrdinalValueAboveOne K) :
    b.residualValue < ordinalValue b.1 := by
  rw [← b.residualValue_mul_principalValue]
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left b.one_lt_principalValue
      (pos_iff_ne_zero.mpr b.residualValue_ne_zero)

/-- Berarducci, Remark 6.7: a series whose ordinal value is the residual value of `b` has
principal value at least that of `b`. -/
theorem principalValue_le_of_ordinalValue_eq_residualValue
    (b d : SeriesWithOrdinalValueAboveOne K) (hd : ordinalValue d.1 = b.residualValue) :
    b.principalValue ≤ d.principalValue := by
  have hval : d.factorOrdinal.1 = b.factorOrdinal.residualFactor := by
    change (ordinalValue d.1).val = b.factorOrdinal.residualFactor
    rw [hd]
    rfl
  exact NatOrdinal.of.le_iff_le.mpr
    (Ordinal.AdditivePrincipalAboveOne.principalFactor_le_principalFactor_of_eq_residualFactor
      b.factorOrdinal d.factorOrdinal hval)

/-- When `v_J(b)` is already infinite multiplicatively principal, it is the principal value. -/
theorem principalValue_eq_ordinalValue_of_isInfiniteMultiplicativelyPrincipal
    (b : SeriesWithOrdinalValueAboveOne K)
    (hb : Ordinal.IsInfiniteMultiplicativelyPrincipal (ordinalValue b.1).val) :
    b.principalValue = ordinalValue b.1 := by
  apply NatOrdinal.val.injective
  simp only [principalValue, NatOrdinal.val_of]
  exact
    b.factorOrdinal.principalFactor_eq_self_of_isInfiniteMultiplicativelyPrincipal hb

/-- When `v_J(b)` is already infinite multiplicatively principal, the residual value is one. -/
theorem residualValue_eq_one_of_isInfiniteMultiplicativelyPrincipal
    (b : SeriesWithOrdinalValueAboveOne K)
    (hb : Ordinal.IsInfiniteMultiplicativelyPrincipal (ordinalValue b.1).val) :
    b.residualValue = 1 := by
  apply NatOrdinal.val.injective
  simp only [residualValue, NatOrdinal.val_of, NatOrdinal.val_one]
  exact
    b.factorOrdinal.residualFactor_eq_one_of_isInfiniteMultiplicativelyPrincipal hb

private theorem ordinalValue_isInfiniteMultiplicativelyPrincipal_of_isMultiplicativelyPrincipal
    (b : SeriesWithOrdinalValueAboveOne K)
    (hb : Ordinal.IsMultiplicativelyPrincipal (ordinalValue b.1).val) :
    Ordinal.IsInfiniteMultiplicativelyPrincipal (ordinalValue b.1).val := by
  rw [Ordinal.isInfiniteMultiplicativelyPrincipal_iff_two_lt_and_isMultiplicativelyPrincipal]
  refine ⟨?_, hb⟩
  have hone : (1 : Ordinal) < (ordinalValue b.1).val :=
    NatOrdinal.of_lt_iff.mp b.2
  have homega : Ordinal.omega0 ≤ (ordinalValue b.1).val :=
    (ordinalValue_isAdditivelyPrincipal_of_one_lt b.2).omega0_le_of_one_lt hone
  exact (Ordinal.natCast_lt_omega0 2).trans_le homega

/-- Under Berarducci's exact multiplicative-principality hypothesis, the principal value is the
ordinal value itself. -/
theorem principalValue_eq_ordinalValue_of_isMultiplicativelyPrincipal
    (b : SeriesWithOrdinalValueAboveOne K)
    (hb : Ordinal.IsMultiplicativelyPrincipal (ordinalValue b.1).val) :
    b.principalValue = ordinalValue b.1 :=
  b.principalValue_eq_ordinalValue_of_isInfiniteMultiplicativelyPrincipal
    (ordinalValue_isInfiniteMultiplicativelyPrincipal_of_isMultiplicativelyPrincipal b hb)

/-- Under Berarducci's exact multiplicative-principality hypothesis, the residual value is one. -/
theorem residualValue_eq_one_of_isMultiplicativelyPrincipal
    (b : SeriesWithOrdinalValueAboveOne K)
    (hb : Ordinal.IsMultiplicativelyPrincipal (ordinalValue b.1).val) :
    b.residualValue = 1 :=
  b.residualValue_eq_one_of_isInfiniteMultiplicativelyPrincipal
    (ordinalValue_isInfiniteMultiplicativelyPrincipal_of_isMultiplicativelyPrincipal b hb)

/-- Conversely, a lower bound on every canonical multiplicative factor of `v_J(c)` is a lower
bound on `v_J^p(c)`. -/
theorem le_principalValue_of_forall_mem_terms (b c : SeriesWithOrdinalValueAboveOne K)
    (h : ∀ t ∈ (Ordinal.log Ordinal.omega0 (ordinalValue c.1).val).additivePrincipalTerms,
      Ordinal.log Ordinal.omega0 b.principalValue.val ≤ t) :
    b.principalValue ≤ c.principalValue := by
  have hmem : Ordinal.log Ordinal.omega0 c.principalValue.val
      ∈ (Ordinal.log Ordinal.omega0 (ordinalValue c.1).val).additivePrincipalTerms := by
    simpa [principalValue, factorOrdinal] using c.factorOrdinal.log_principalFactor_mem_terms
  refine NatOrdinal.val.le_iff_le.mp ?_
  rw [← b.principalValue_val_eq_opow_log, ← c.principalValue_val_eq_opow_log]
  exact (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).mpr (h _ hmem)

/-- Principal and residual values depend only on the ordinal value of the series. -/
theorem principalValue_eq_and_residualValue_eq_of_ordinalValue_eq
    (b c : SeriesWithOrdinalValueAboveOne K) (hbc : ordinalValue b.1 = ordinalValue c.1) :
    b.principalValue = c.principalValue ∧ b.residualValue = c.residualValue := by
  have hfactor : b.factorOrdinal = c.factorOrdinal := by
    apply Subtype.ext
    exact congrArg NatOrdinal.val hbc
  constructor
  · simp [principalValue, hfactor]
  · simp [residualValue, hfactor]

/-- If `v_J(b) = ω^α` and `α` has positive constant Cantor coefficient, the final
multiplicative factor of `v_J(b)` is `ω`. -/
theorem principalValue_eq_wpow_one_of_ordinalValue_eq_wpow
    (b : SeriesWithOrdinalValueAboveOne K) (alpha : NatOrdinal)
    (halpha : 0 < alpha.constantCoeff) (hb : ordinalValue b.1 = ω^ alpha) :
    b.principalValue = ω^ (1 : NatOrdinal) := by
  apply NatOrdinal.val.injective
  simp only [principalValue, NatOrdinal.val_of, NatOrdinal.val_wpow,
    NatOrdinal.val_one, Ordinal.opow_one]
  change Ordinal.AdditivePrincipalAboveOne.principalFactor
      (⟨(ordinalValue b.1).val,
        ordinalValue_isAdditivelyPrincipal_of_one_lt b.2, b.2⟩ :
        Ordinal.AdditivePrincipalAboveOne) = Ordinal.omega0
  have hbval : (ordinalValue b.1).val = Ordinal.omega0 ^ alpha.val := by
    simpa only [NatOrdinal.val_wpow] using congrArg NatOrdinal.val hb
  let q : Ordinal.AdditivePrincipalAboveOne :=
    ⟨Ordinal.omega0 ^ alpha.val,
      Ordinal.isAdditivelyPrincipal_omega0_opow alpha.val,
      hbval ▸ b.2⟩
  have hfactor :
      (⟨(ordinalValue b.1).val,
        ordinalValue_isAdditivelyPrincipal_of_one_lt b.2, b.2⟩ :
        Ordinal.AdditivePrincipalAboveOne) = q :=
    Subtype.ext hbval
  rw [hfactor]
  dsimp only [q]
  exact Ordinal.AdditivePrincipalAboveOne.principalFactor_wpow_of_constantCoeff_pos
    alpha halpha (Ordinal.isAdditivelyPrincipal_omega0_opow alpha.val)
      (hbval ▸ b.2)

/-- If `v_J(b) = ω^α` and `α` has positive constant Cantor coefficient, deleting the
final multiplicative factor leaves `ω^(α.removeNat 1)`. -/
theorem residualValue_eq_wpow_removeNat_of_ordinalValue_eq_wpow
    (b : SeriesWithOrdinalValueAboveOne K) (alpha : NatOrdinal)
    (halpha : 0 < alpha.constantCoeff) (hb : ordinalValue b.1 = ω^ alpha) :
    b.residualValue = ω^ (alpha.removeNat 1) := by
  apply NatOrdinal.val.injective
  simp only [residualValue, NatOrdinal.val_of, NatOrdinal.val_wpow]
  change Ordinal.AdditivePrincipalAboveOne.residualFactor
      (⟨(ordinalValue b.1).val,
        ordinalValue_isAdditivelyPrincipal_of_one_lt b.2, b.2⟩ :
        Ordinal.AdditivePrincipalAboveOne) =
      Ordinal.omega0 ^ (alpha.removeNat 1).val
  have hbval : (ordinalValue b.1).val = Ordinal.omega0 ^ alpha.val := by
    simpa only [NatOrdinal.val_wpow] using congrArg NatOrdinal.val hb
  let q : Ordinal.AdditivePrincipalAboveOne :=
    ⟨Ordinal.omega0 ^ alpha.val,
      Ordinal.isAdditivelyPrincipal_omega0_opow alpha.val,
      hbval ▸ b.2⟩
  have hfactor :
      (⟨(ordinalValue b.1).val,
        ordinalValue_isAdditivelyPrincipal_of_one_lt b.2, b.2⟩ :
        Ordinal.AdditivePrincipalAboveOne) = q :=
    Subtype.ext hbval
  rw [hfactor]
  dsimp only [q]
  exact Ordinal.AdditivePrincipalAboveOne.residualFactor_wpow_of_constantCoeff_pos
    alpha halpha (Ordinal.isAdditivelyPrincipal_omega0_opow alpha.val)
      (hbval ▸ b.2)

theorem residualValue_eq_wpow_removeLeastTerm
    (b : SeriesWithOrdinalValueAboveOne K) (alpha : NatOrdinal)
    (hb : ordinalValue b.1 = ω^ alpha) :
    b.residualValue = ω^ (NatOrdinal.removeLeastTerm alpha) := by
  apply NatOrdinal.val.injective
  simp only [residualValue, NatOrdinal.val_of, NatOrdinal.val_wpow]
  have hbval : (ordinalValue b.1).val = Ordinal.omega0 ^ alpha.val := by
    simpa only [NatOrdinal.val_wpow] using congrArg NatOrdinal.val hb
  change Ordinal.AdditivePrincipalAboveOne.residualFactor
      (⟨(ordinalValue b.1).val,
        ordinalValue_isAdditivelyPrincipal_of_one_lt b.2, b.2⟩ :
        Ordinal.AdditivePrincipalAboveOne) = _
  have hfactor :
      (⟨(ordinalValue b.1).val,
        ordinalValue_isAdditivelyPrincipal_of_one_lt b.2, b.2⟩ :
        Ordinal.AdditivePrincipalAboveOne) =
      (⟨Ordinal.omega0 ^ alpha.val,
        Ordinal.isAdditivelyPrincipal_omega0_opow alpha.val, hbval ▸ b.2⟩ :
        Ordinal.AdditivePrincipalAboveOne) :=
    Subtype.ext hbval
  rw [hfactor, Ordinal.residualFactor_omega0_opow alpha.val
      (Ordinal.isAdditivelyPrincipal_omega0_opow alpha.val) (hbval ▸ b.2),
    NatOrdinal.val_removeLeastTerm]

theorem principalValue_eq_wpow_leastTerm
    (b : SeriesWithOrdinalValueAboveOne K) (alpha : NatOrdinal)
    (hb : ordinalValue b.1 = ω^ alpha) :
    b.principalValue = ω^ (NatOrdinal.leastTerm alpha) := by
  have halpha : alpha ≠ 0 := by
    intro hzero
    rw [hzero, NatOrdinal.wpow_zero] at hb
    exact absurd hb b.2.ne'
  have hne : alpha.val.additivePrincipalTerms ≠ [] :=
    NatOrdinal.additivePrincipalTerms_ne_nil halpha
  apply NatOrdinal.val.injective
  simp only [principalValue, NatOrdinal.val_of, NatOrdinal.val_wpow]
  have hbval : (ordinalValue b.1).val = Ordinal.omega0 ^ alpha.val := by
    simpa only [NatOrdinal.val_wpow] using congrArg NatOrdinal.val hb
  change Ordinal.AdditivePrincipalAboveOne.principalFactor
      (⟨(ordinalValue b.1).val,
        ordinalValue_isAdditivelyPrincipal_of_one_lt b.2, b.2⟩ :
        Ordinal.AdditivePrincipalAboveOne) = _
  have hfactor :
      (⟨(ordinalValue b.1).val,
        ordinalValue_isAdditivelyPrincipal_of_one_lt b.2, b.2⟩ :
        Ordinal.AdditivePrincipalAboveOne) =
      (⟨Ordinal.omega0 ^ alpha.val,
        Ordinal.isAdditivelyPrincipal_omega0_opow alpha.val, hbval ▸ b.2⟩ :
        Ordinal.AdditivePrincipalAboveOne) :=
    Subtype.ext hbval
  rw [hfactor, Ordinal.principalFactor_omega0_opow alpha.val
      (Ordinal.isAdditivelyPrincipal_omega0_opow alpha.val) (hbval ▸ b.2) hne,
    NatOrdinal.val_leastTerm hne]

end SeriesWithOrdinalValueAboveOne

end Berarducci
