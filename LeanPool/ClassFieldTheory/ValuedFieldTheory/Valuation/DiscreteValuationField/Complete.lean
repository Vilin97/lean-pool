/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport

/-! # Complete -/
namespace ValuationTheory

/-!
# Complete discretely valued fields
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

namespace Valuation

variable {K : Type u} [Field K]
variable {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]

/-- A complete discrete valuation. -/
class IsCompleteDiscrete (val : _root_.Valuation K Gamma) : Prop where
  /-- A complete discrete valuation has discrete rank one. -/
  [isRankOneDiscrete : val.IsRankOneDiscrete]
  /-- The valuation ring is complete for its maximal-ideal adic topology. -/
  isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring

attribute [instance] IsCompleteDiscrete.isRankOneDiscrete

/-- Completeness of the valued field implies adic completeness of its valuation subring. -/
theorem isAdicComplete (val : _root_.Valuation K Gamma) [IsCompleteDiscrete val] :
    IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring :=
  IsCompleteDiscrete.isAdicComplete (val := val)

/-- Pulling a complete discrete valuation back along a field equivalence
preserves both rank-one discreteness and adic completeness. -/
instance isCompleteDiscrete_comap_ringEquiv
    {L : Type w} [Field L]
    (val : _root_.Valuation K Gamma) [IsCompleteDiscrete val] (e : L ≃+* K) :
    IsCompleteDiscrete (val.comap (e : L →+* K)) where
  isRankOneDiscrete := isRankOneDiscrete_comap_ringEquiv val e
  isAdicComplete := by
    let r := valuationSubringRingEquivOfComap val e
    have hmap :
        (IsLocalRing.maximalIdeal val.valuationSubring).map
            (r.symm : val.valuationSubring →+*
              (val.comap (e : L →+* K)).valuationSubring) =
          IsLocalRing.maximalIdeal
            (val.comap (e : L →+* K)).valuationSubring := by
      calc
        (IsLocalRing.maximalIdeal val.valuationSubring).map
            (r.symm : val.valuationSubring →+*
              (val.comap (e : L →+* K)).valuationSubring) =
            (IsLocalRing.maximalIdeal val.valuationSubring).comap
              (r : (val.comap (e : L →+* K)).valuationSubring →+*
                val.valuationSubring) := Ideal.map_symm r
        _ = IsLocalRing.maximalIdeal
              (val.comap (e : L →+* K)).valuationSubring :=
          maximalIdeal_comap_valuationSubringRingEquivOfComap val e
    let : IsAdicComplete
        (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring :=
      isAdicComplete val
    simpa [hmap] using
      (isAdicComplete_map_ringEquiv
        (I := IsLocalRing.maximalIdeal val.valuationSubring) r.symm)

/-- The valuation subring of a complete discrete valuation field is henselian. -/
theorem henselianRing (val : _root_.Valuation K Gamma) [IsCompleteDiscrete val] :
    HenselianRing val.valuationSubring (IsLocalRing.maximalIdeal val.valuationSubring) := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring)
      val.valuationSubring := isAdicComplete val
  infer_instance

/-- In a rank-one discrete valuation ring, membership in the `n`-th power of
the maximal ideal is the same as the corresponding valuation bound against a
chosen uniformizer power. -/
theorem mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
    (val : _root_.Valuation K Gamma) [val.IsRankOneDiscrete]
    {pi x : val.valuationSubring}
    (hpi : val.IsUniformizer (pi : K)) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal val.valuationSubring ^ n ↔
      val (x : K) ≤ val ((pi ^ n : val.valuationSubring) : K) := by
  rw [hpi.is_generator, Ideal.span_singleton_pow]
  simpa [Ideal.mem_span_singleton] using
    (_root_.Valuation.Integers.dvd_iff_le
      (_root_.Valuation.valuationSubring.integers (v := val))
      (x := pi ^ n) (y := x))

end Valuation

/-- A field with a chosen complete rank-one discrete valuation. -/
structure CompleteDVF (K : Type u) [Field K] where
  /-- The ordered multiplicative value group. -/
  ValueGroup : Type v
  /-- The ordered commutative group-with-zero structure on the value group. -/
  [instValueGroup : LinearOrderedCommGroupWithZero ValueGroup]
  /-- The chosen valuation on the field. -/
  valuation : _root_.Valuation K ValueGroup
  /-- The chosen valuation is complete and discretely rank one. -/
  [instCompleteDiscrete : Valuation.IsCompleteDiscrete valuation]

attribute [instance] CompleteDVF.instValueGroup CompleteDVF.instCompleteDiscrete

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- A complete DVF is Henselian.  This is the canonical forgetful projection:
all weaker DVF data are obtained through this object. -/
abbrev toHenselianDVF (F : CompleteDVF.{u, v} K) : HenselianDVF.{u, v} K where
  toDVF :=
    { ValueGroup := F.ValueGroup
      valuation := F.valuation }
  instHenselian := by
    change HenselianRing F.valuation.valuationSubring
      (IsLocalRing.maximalIdeal F.valuation.valuationSubring)
    exact Valuation.henselianRing F.valuation

/-- The underlying DVF, obtained along the canonical
`CompleteDVF -> HenselianDVF -> DVF` path. -/
abbrev toDVF (F : CompleteDVF.{u, v} K) : DVF.{u, v} K :=
  F.toHenselianDVF.toDVF

/-- Introduces the abbreviation `valuationSubring`. -/
abbrev valuationSubring (F : CompleteDVF.{u, v} K) : Type u :=
  F.toHenselianDVF.valuationSubring

/-- Introduces the abbreviation `maximalIdeal`. -/
abbrev maximalIdeal (F : CompleteDVF.{u, v} K) : Ideal F.valuationSubring :=
  F.toHenselianDVF.maximalIdeal

/-- Introduces the abbreviation `residueField`. -/
abbrev residueField (F : CompleteDVF.{u, v} K) : Type u :=
  F.toHenselianDVF.residueField

/-- Introduces the abbreviation `residueMap`. -/
abbrev residueMap (F : CompleteDVF.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toHenselianDVF.residueMap

/-- The valuation subring in the complete model is a discrete valuation ring. -/
theorem valuationSubring_isDiscreteValuationRing (F : CompleteDVF.{u, v} K) :
    IsDiscreteValuationRing F.valuationSubring :=
  F.toDVF.valuationSubring_isDiscreteValuationRing

/-- The complete DVR model is complete for its maximal-ideal-adic topology. -/
theorem isAdicComplete (F : CompleteDVF.{u, v} K) :
    IsAdicComplete F.maximalIdeal F.valuationSubring := by
  change IsAdicComplete
    (IsLocalRing.maximalIdeal F.valuation.valuationSubring)
    F.valuation.valuationSubring
  exact Valuation.isAdicComplete F.valuation

/-- The complete DVR valuation ring carries its canonical adic-completeness instance. -/
instance instIsAdicComplete (F : CompleteDVF.{u, v} K) :
    IsAdicComplete F.maximalIdeal F.valuationSubring :=
  F.isAdicComplete

/-- Adic completeness makes the complete DVR valuation ring henselian. -/
theorem henselianRing (F : CompleteDVF.{u, v} K) :
    HenselianRing F.valuationSubring F.maximalIdeal :=
  F.toHenselianDVF.henselianRing

/-- Membership in the valuation subring is characterized by nonnegative valuation. -/
theorem mem_valuationSubring_iff (F : CompleteDVF.{u, v} K) (x : K) :
    x ∈ F.valuation.valuationSubring ↔ F.valuation x <= 1 :=
  F.toDVF.mem_valuationSubring_iff x

/-- Membership in the maximal ideal is characterized by strictly positive valuation. -/
theorem mem_maximalIdeal_iff (F : CompleteDVF.{u, v} K)
    (x : F.valuationSubring) :
    x ∈ F.maximalIdeal ↔ F.valuation (x : K) < 1 :=
  F.toDVF.mem_maximalIdeal_iff x

/-- An integral element has zero residue exactly when it lies in the maximal ideal. -/
theorem residue_eq_zero_iff (F : CompleteDVF.{u, v} K)
    (x : F.valuationSubring) :
    F.residueMap x = 0 ↔ x ∈ F.maximalIdeal :=
  IsLocalRing.residue_eq_zero_iff x

/-- An integral element has nonzero residue exactly when it is a unit. -/
theorem residue_ne_zero_iff_isUnit (F : CompleteDVF.{u, v} K)
    (x : F.valuationSubring) :
    F.residueMap x ≠ 0 ↔ IsUnit x :=
  IsLocalRing.residue_ne_zero_iff_isUnit x

/-- Every residue-field element has a representative in the valuation ring. -/
theorem residue_surjective (F : CompleteDVF.{u, v} K) :
    Function.Surjective F.residueMap :=
  IsLocalRing.residue_surjective

/-- A complete discrete valuation field admits a uniformizer. -/
theorem exists_uniformizer (F : CompleteDVF.{u, v} K) :
    Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K)) :=
  F.toDVF.exists_uniformizer

/-- Every chosen uniformizer lies in the maximal ideal. -/
theorem uniformizer_mem_maximalIdeal (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    pi ∈ F.maximalIdeal :=
  F.toDVF.uniformizer_mem_maximalIdeal hpi

/-- The maximal ideal is the principal ideal generated by a uniformizer. -/
theorem maximalIdeal_eq_span_uniformizer (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    F.maximalIdeal = Ideal.span ({pi} : Set F.valuationSubring) :=
  F.toDVF.maximalIdeal_eq_span_uniformizer hpi

/-- Powers of the maximal ideal are generated by powers of any chosen
uniformizer. -/
theorem maximalIdeal_pow_eq_span_uniformizer_pow (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) :
    F.maximalIdeal ^ n = Ideal.span ({pi ^ n} : Set F.valuationSubring) :=
  F.toDVF.maximalIdeal_pow_eq_span_uniformizer_pow hpi n

/-- Membership in a power of the maximal ideal is divisibility by the
corresponding power of a uniformizer. -/
theorem mem_maximalIdeal_pow_iff_uniformizer_pow_dvd (F : CompleteDVF.{u, v} K)
    {pi x : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    x ∈ F.maximalIdeal ^ n ↔ pi ^ n ∣ x :=
  F.toDVF.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd hpi n

/-- A uniformizer belongs to the maximal ideal but not to its square. -/
theorem uniformizer_not_mem_maximalIdeal_sq (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    pi ∉ F.maximalIdeal ^ 2 :=
  F.toDVF.uniformizer_not_mem_maximalIdeal_sq hpi

/-- Every nonzero ideal in the valuation ring of a complete DVF is a power of
the maximal ideal. -/
theorem nonzero_ideal_eq_maximalIdeal_pow (F : CompleteDVF.{u, v} K)
    (I : Ideal F.valuationSubring) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = F.maximalIdeal ^ n :=
  F.toDVF.nonzero_ideal_eq_maximalIdeal_pow I hI

/-- In a complete DVF, the principal filtration generated by any nonzero
element of the maximal ideal is complete.  The source is that every nonzero
ideal in a DVR is a positive power of the maximal ideal. -/
theorem principalAdicComplete_of_ne_zero_mem_maximalIdeal
    (F : CompleteDVF.{u, v} K) {π : F.valuationSubring}
    (hπ_ne : π ≠ 0) (hπ_mem : π ∈ F.maximalIdeal) :
    IsAdicComplete (Ideal.span ({π} : Set F.valuationSubring))
      F.valuationSubring := by
  have hspan_ne :
      Ideal.span ({π} : Set F.valuationSubring) ≠ ⊥ := by
    intro hspan
    have hπ_bot : π ∈ (⊥ : Ideal F.valuationSubring) := by
      rw [← hspan]
      exact Ideal.mem_span_singleton_self π
    exact hπ_ne (by simpa using hπ_bot)
  rcases F.nonzero_ideal_eq_maximalIdeal_pow
      (Ideal.span ({π} : Set F.valuationSubring)) hspan_ne with
    ⟨n, hn⟩
  have hspan_le :
      Ideal.span ({π} : Set F.valuationSubring) ≤ F.maximalIdeal := by
    rw [Ideal.span_le]
    intro x hx
    have hxπ : x = π := by simpa using hx
    simpa [hxπ] using hπ_mem
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    have htop_le : (⊤ : Ideal F.valuationSubring) ≤ F.maximalIdeal := by
      simpa [hn, hn_zero] using hspan_le
    have hone : (1 : F.valuationSubring) ∈ F.maximalIdeal :=
      htop_le trivial
    exact
      (IsLocalRing.maximalIdeal.isMaximal F.valuationSubring).isPrime.one_notMem
        hone
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_ne_zero
  have hmax_complete : IsAdicComplete F.maximalIdeal F.valuationSubring :=
    F.isAdicComplete
  let : IsAdicComplete F.maximalIdeal F.valuationSubring := hmax_complete
  have hpow :
      IsAdicComplete (F.maximalIdeal ^ n) F.valuationSubring :=
    isAdicComplete_pow_of_isAdicComplete
      (M := F.valuationSubring) F.maximalIdeal hn_pos
  simpa [hn] using hpow

/-- Principal precompleteness generated from complete-DVF completeness. -/
theorem principalPrecomplete_of_ne_zero_mem_maximalIdeal
    (F : CompleteDVF.{u, v} K) {π : F.valuationSubring}
    (hπ_ne : π ≠ 0) (hπ_mem : π ∈ F.maximalIdeal) :
    IsPrecomplete (Ideal.span ({π} : Set F.valuationSubring))
      F.valuationSubring :=
  (F.principalAdicComplete_of_ne_zero_mem_maximalIdeal
    hπ_ne hπ_mem).toIsPrecomplete

/-- Principal separatedness generated from complete-DVF completeness. -/
theorem principalHausdorff_of_ne_zero_mem_maximalIdeal
    (F : CompleteDVF.{u, v} K) {π : F.valuationSubring}
    (hπ_ne : π ≠ 0) (hπ_mem : π ∈ F.maximalIdeal) :
    IsHausdorff (Ideal.span ({π} : Set F.valuationSubring))
      F.valuationSubring :=
  (F.principalAdicComplete_of_ne_zero_mem_maximalIdeal
    hπ_ne hπ_mem).toIsHausdorff

/-- The maximal ideal of a complete DVF valuation ring is nonzero. -/
theorem maximalIdeal_ne_bot (F : CompleteDVF.{u, v} K) :
    F.maximalIdeal ≠ ⊥ := by
  rcases F.exists_uniformizer with ⟨pi, hpi⟩
  intro hbot
  have hmem : pi ∈ (⊥ : Ideal F.valuationSubring) := by
    rw [← hbot]
    exact F.uniformizer_mem_maximalIdeal hpi
  have hzero_sub : pi = 0 := by
    simpa using hmem
  apply hpi.ne_zero
  exact Subtype.ext_iff.mp hzero_sub

/-- No power of a uniformizer lies one step deeper in the maximal-ideal
filtration. -/
theorem uniformizer_pow_not_mem_maximalIdeal_pow_succ
    (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) :
    pi ^ n ∉ F.maximalIdeal ^ (n + 1) :=
  F.toDVF.uniformizer_pow_not_mem_maximalIdeal_pow_succ hpi n

/-- The maximal-ideal topology on the valuation ring of a complete DVF is
separated.  This is the uniqueness half needed by unit-level completion
arguments. -/
theorem eq_zero_of_mem_maximalIdeal_pow_all
    (F : CompleteDVF.{u, v} K) {x : F.valuationSubring}
    (hx : ∀ n : ℕ, x ∈ F.maximalIdeal ^ n) :
    x = 0 := by
  by_contra hx_ne
  have hspan_ne : Ideal.span ({x} : Set F.valuationSubring) ≠ ⊥ := by
    intro hspan
    have hx_bot : x ∈ (⊥ : Ideal F.valuationSubring) := by
      rw [← hspan]
      exact Ideal.mem_span_singleton_self x
    exact hx_ne (by simpa using hx_bot)
  rcases F.nonzero_ideal_eq_maximalIdeal_pow
      (Ideal.span ({x} : Set F.valuationSubring)) hspan_ne with
    ⟨n, hspan_eq⟩
  rcases F.exists_uniformizer with ⟨pi, hpi⟩
  have hspan_le : Ideal.span ({x} : Set F.valuationSubring) ≤
      F.maximalIdeal ^ (n + 1) := by
    rw [Ideal.span_le]
    intro y hy
    have hyx : y = x := by simpa using hy
    simpa [hyx] using hx (n + 1)
  have hle : F.maximalIdeal ^ n ≤ F.maximalIdeal ^ (n + 1) := by
    simpa [hspan_eq] using hspan_le
  have hpow_mem : pi ^ n ∈ F.maximalIdeal ^ n := by
    rw [F.maximalIdeal_pow_eq_span_uniformizer_pow hpi n]
    exact Ideal.mem_span_singleton_self (pi ^ n)
  exact F.uniformizer_pow_not_mem_maximalIdeal_pow_succ hpi n (hle hpow_mem)

/-- Valuation-ring units are separated by all finite maximal-ideal quotient
coordinates. -/
theorem unit_eq_of_idealQuotient_eq_all
    (F : CompleteDVF.{u, v} K) {u₁ u₂ : F.valuationSubringˣ}
    (h :
      ∀ n : ℕ,
        Ideal.Quotient.mk (F.maximalIdeal ^ n) (u₁ : F.valuationSubring) =
          Ideal.Quotient.mk (F.maximalIdeal ^ n) (u₂ : F.valuationSubring)) :
    u₁ = u₂ := by
  apply Units.ext
  have hsub :
      ∀ n : ℕ,
        (u₁ : F.valuationSubring) - (u₂ : F.valuationSubring) ∈
          F.maximalIdeal ^ n := by
    intro n
    exact
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n)
        (x := (u₁ : F.valuationSubring))
        (y := (u₂ : F.valuationSubring))).1 (h n)
  exact sub_eq_zero.mp (F.eq_zero_of_mem_maximalIdeal_pow_all hsub)

end CompleteDVF
end DiscreteValuationField

end

end ValuationTheory
