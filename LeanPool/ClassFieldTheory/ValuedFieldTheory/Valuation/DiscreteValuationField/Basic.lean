/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.CharP.Subring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring

/-! # Basic -/

@[expose] public section
namespace ValuationTheory

/-!
# Discretely valued fields

This is the basic one-dimensional API for fields equipped with a chosen
rank-one discrete valuation.
-/

noncomputable section

universe u v

namespace ValuationSubring

/-- A valuation subring has the characteristic of its ambient field. -/
instance charP {K : Type u} [Field K] (R : ValuationSubring K) (p : ℕ) [CharP K p] :
    CharP R p :=
  CharP.subring K p R.toSubring

end ValuationSubring

namespace DiscreteValuationField

/-- A field with a chosen rank-one discrete valuation. -/
structure DVF (K : Type u) [Field K] where
  /-- The ordered multiplicative value group. -/
  ValueGroup : Type v
  /-- The ordered commutative group-with-zero structure on the value group. -/
  [instValueGroup : LinearOrderedCommGroupWithZero ValueGroup]
  /-- The chosen valuation on the field. -/
  valuation : _root_.Valuation K ValueGroup
  /-- The chosen valuation has discrete rank one. -/
  [instRankOneDiscrete : valuation.IsRankOneDiscrete]

attribute [instance] DVF.instValueGroup DVF.instRankOneDiscrete

namespace DVF

variable {K : Type u} [Field K]

/-- The valuation subring of a DVF. -/
abbrev valuationSubring (F : DVF.{u, v} K) : Type u :=
  F.valuation.valuationSubring

/-- The valuation subring of a discrete valuation field is a commutative ring. -/
instance valuationSubring.commRing (F : DVF.{u, v} K) :
    CommRing F.valuationSubring :=
  ValuationSubring.instCommRingSubtypeMem F.valuation.valuationSubring

/-- The valuation subring of a discrete valuation field is local. -/
instance valuationSubring.isLocalRing (F : DVF.{u, v} K) :
    IsLocalRing F.valuationSubring :=
  ValuationSubring.isLocalRing F.valuation.valuationSubring

/-- The valuation subring of a discrete valuation field is an integral domain. -/
instance valuationSubring.isDomain (F : DVF.{u, v} K) :
    IsDomain F.valuationSubring :=
  ValuationSubring.instIsDomainSubtypeMem F.valuation.valuationSubring

/-- The maximal ideal of the valuation subring. -/
abbrev maximalIdeal (F : DVF.{u, v} K) : Ideal F.valuationSubring :=
  IsLocalRing.maximalIdeal F.valuationSubring

/-- The residue field of the valuation subring. -/
abbrev residueField (F : DVF.{u, v} K) : Type u :=
  IsLocalRing.ResidueField F.valuationSubring

/-- The residue ring of a discrete valuation field carries its canonical field structure. -/
instance residueField.field (F : DVF.{u, v} K) : Field F.residueField :=
  IsLocalRing.ResidueField.field F.valuation.valuationSubring

/-- The residue map of a DVF. -/
abbrev residueMap (F : DVF.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  IsLocalRing.residue F.valuationSubring

/-- The valuation subring of a DVF is a DVR. -/
theorem valuationSubring_isDiscreteValuationRing (F : DVF.{u, v} K) :
    IsDiscreteValuationRing F.valuationSubring :=
  Valuation.valuationSubring_isDiscreteValuationRing F.valuation

/-- The valuation ring of a DVF is a fraction ring inside the field. -/
theorem valuationSubring_isFractionRing (F : DVF.{u, v} K) :
    IsFractionRing F.valuationSubring K :=
  (Valuation.valuationSubring.integers (v := F.valuation)).isFractionRing

/-- The valuation ring of a DVF is integrally closed. -/
theorem valuationSubring_isIntegrallyClosed (F : DVF.{u, v} K) :
    IsIntegrallyClosed F.valuationSubring := by
  change IsIntegrallyClosed F.valuation.valuationSubring
  infer_instance

/-- The valuation ring of a DVF is Noetherian. -/
theorem valuationSubring_isNoetherianRing (F : DVF.{u, v} K) :
    IsNoetherianRing F.valuationSubring := by
  have : IsDiscreteValuationRing F.valuationSubring :=
    F.valuationSubring_isDiscreteValuationRing
  infer_instance

/-- Membership in the valuation subring is `v x <= 1`. -/
theorem mem_valuationSubring_iff (F : DVF.{u, v} K) (x : K) :
    x ∈ F.valuation.valuationSubring ↔ F.valuation x <= 1 :=
  Valuation.mem_valuationSubring_iff (v := F.valuation) x

/-- Maximal-ideal membership is `v x < 1`. -/
theorem mem_maximalIdeal_iff (F : DVF.{u, v} K)
    (x : F.valuationSubring) :
    x ∈ F.maximalIdeal ↔ F.valuation (x : K) < 1 := by
  change
    x ∈ IsLocalRing.maximalIdeal F.valuation.valuationSubring ↔
    (F.valuation (x : K) < 1)
  exact Valuation.mem_maximalIdeal_iff (v := F.valuation)

/-- Zero residue is equivalent to membership in the maximal ideal. -/
theorem residue_eq_zero_iff (F : DVF.{u, v} K)
    (x : F.valuationSubring) :
    F.residueMap x = 0 ↔ x ∈ F.maximalIdeal := by
  change
    IsLocalRing.residue F.valuation.valuationSubring x = 0 ↔
    x ∈ IsLocalRing.maximalIdeal F.valuation.valuationSubring
  exact IsLocalRing.residue_eq_zero_iff x

/-- A residue class in a DVF valuation ring is nonzero exactly when its
representative is a unit of the valuation ring. -/
theorem residue_ne_zero_iff_isUnit (F : DVF.{u, v} K)
    (x : F.valuationSubring) :
    F.residueMap x ≠ 0 ↔ IsUnit x := by
  change IsLocalRing.residue F.valuation.valuationSubring x ≠ 0 ↔ IsUnit x
  exact IsLocalRing.residue_ne_zero_iff_isUnit x

/-- The residue map is surjective. -/
theorem residue_surjective (F : DVF.{u, v} K) :
    Function.Surjective F.residueMap :=
  IsLocalRing.residue_surjective (R := F.valuation.valuationSubring)

/-- A DVF has a uniformizer in its valuation subring. -/
theorem exists_uniformizer (F : DVF.{u, v} K) :
    Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K)) := by
  change Exists
    (fun pi : F.valuation.valuationSubring => F.valuation.IsUniformizer (pi : K))
  exact Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial F.valuation

/-- A uniformizer lies in the maximal ideal. -/
theorem uniformizer_mem_maximalIdeal (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    pi ∈ F.maximalIdeal := by
  change pi ∈ IsLocalRing.maximalIdeal F.valuation.valuationSubring
  exact (Valuation.mem_maximalIdeal_iff (v := F.valuation)).2 hpi.val_lt_one

/-- A uniformizer generates the maximal ideal. -/
theorem maximalIdeal_eq_span_uniformizer (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    F.maximalIdeal = Ideal.span (Set.singleton pi) := by
  change IsLocalRing.maximalIdeal F.valuation.valuationSubring =
    Ideal.span (Set.singleton pi)
  exact Valuation.IsUniformizer.is_generator (v := F.valuation) hpi

/-- Powers of the maximal ideal are generated by powers of any chosen
uniformizer. -/
theorem maximalIdeal_pow_eq_span_uniformizer_pow (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) :
    F.maximalIdeal ^ n = Ideal.span ({pi ^ n} : Set F.valuationSubring) := by
  rw [F.maximalIdeal_eq_span_uniformizer hpi]
  exact Ideal.span_singleton_pow pi n

/-- Membership in a power of the maximal ideal is divisibility by the
corresponding power of a uniformizer. -/
theorem mem_maximalIdeal_pow_iff_uniformizer_pow_dvd (F : DVF.{u, v} K)
    {pi x : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    x ∈ F.maximalIdeal ^ n ↔ pi ^ n ∣ x := by
  rw [F.maximalIdeal_pow_eq_span_uniformizer_pow hpi n,
    Ideal.mem_span_singleton]

/-- No power of a uniformizer lies one step deeper in the maximal-ideal
filtration. -/
theorem uniformizer_pow_not_mem_maximalIdeal_pow_succ
    (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) :
    pi ^ n ∉ F.maximalIdeal ^ (n + 1) := by
  rw [F.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd hpi (n + 1)]
  rintro ⟨a, ha⟩
  have hpi_ne : pi ≠ 0 := by
    intro hzero
    exact hpi.ne_zero (by simpa using congrArg (fun x : F.valuationSubring => (x : K)) hzero)
  have hpow_ne : pi ^ n ≠ 0 := pow_ne_zero n hpi_ne
  have hcancel : (1 : F.valuationSubring) = pi * a := by
    apply mul_left_cancel₀ hpow_ne
    calc
      pi ^ n * (1 : F.valuationSubring) = pi ^ n := by rw [mul_one]
      _ = pi ^ (n + 1) * a := ha
      _ = (pi ^ n * pi) * a := by rw [pow_succ]
      _ = pi ^ n * (pi * a) := by rw [mul_assoc]
  have hunit : IsUnit pi :=
    isUnit_iff_dvd_one.2 ⟨a, hcancel⟩
  exact hpi.not_isUnit hunit

/-- A uniformizer belongs to the maximal ideal but not to its square. -/
theorem uniformizer_not_mem_maximalIdeal_sq (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    pi ∉ F.maximalIdeal ^ 2 := by
  simpa using F.uniformizer_pow_not_mem_maximalIdeal_pow_succ hpi 1

/-- Every nonzero ideal in the valuation ring of a DVF is a power of the maximal
ideal. -/
theorem nonzero_ideal_eq_maximalIdeal_pow (F : DVF.{u, v} K)
    (I : Ideal F.valuationSubring) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = F.maximalIdeal ^ n := by
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible F.valuationSubring
  obtain ⟨n, hn⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hpi
  refine ⟨n, ?_⟩
  rw [hn]
  rw [← Ideal.span_singleton_pow]
  rw [← hpi.maximalIdeal_eq]

/-- An element of the valuation ring lying in the maximal ideal but not in its
square is a uniformizer. -/
theorem isUniformizer_of_mem_maximalIdeal_of_not_mem_maximalIdeal_sq
    (F : DVF.{u, v} K) {x : F.valuationSubring}
    (hx : x ∈ F.maximalIdeal) (hx_sq : x ∉ F.maximalIdeal ^ 2) :
    F.valuation.IsUniformizer (x : K) := by
  have hx_ne : x ≠ 0 := by
    intro hzero
    exact hx_sq (by simp [hzero])
  have hspan_ne : Ideal.span ({x} : Set F.valuationSubring) ≠ ⊥ := by
    intro hspan
    have hx_bot : x ∈ (⊥ : Ideal F.valuationSubring) := by
      rw [← hspan]
      exact Ideal.mem_span_singleton_self x
    exact hx_ne (by simpa using hx_bot)
  rcases F.nonzero_ideal_eq_maximalIdeal_pow
      (Ideal.span ({x} : Set F.valuationSubring)) hspan_ne with
    ⟨n, hn⟩
  have hspan_le_max :
      Ideal.span ({x} : Set F.valuationSubring) ≤ F.maximalIdeal := by
    rw [Ideal.span_le]
    intro y hy
    have hyx : y = x := by simpa using hy
    simpa [hyx] using hx
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    have hone : (1 : F.valuationSubring) ∈ F.maximalIdeal := by
      have htop_le :
          (⊤ : Ideal F.valuationSubring) ≤ F.maximalIdeal := by
        simpa [hn, hn_zero] using hspan_le_max
      exact htop_le trivial
    exact
      (IsLocalRing.maximalIdeal.isMaximal F.valuationSubring).isPrime.one_notMem
        hone
  have hn_lt_two : n < 2 := by
    by_contra hnot
    have htwo_le : 2 ≤ n := Nat.le_of_not_lt hnot
    have hx_span : x ∈ Ideal.span ({x} : Set F.valuationSubring) :=
      Ideal.mem_span_singleton_self x
    have hx_pow : x ∈ F.maximalIdeal ^ n := by
      simpa [hn] using hx_span
    exact hx_sq (Ideal.pow_le_pow_right htwo_le hx_pow)
  have hn_eq_one : n = 1 := by
    cases n with
    | zero => exact (hn_ne_zero rfl).elim
    | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
            exact
              ((not_lt_of_ge
                (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))))
                hn_lt_two).elim
  have hmax :
      F.maximalIdeal = Ideal.span ({x} : Set F.valuationSubring) := by
    simpa [hn_eq_one] using hn.symm
  exact Valuation.isUniformizer_of_maximalIdeal_eq_span (v := F.valuation) hmax

/-- Multiplying a uniformizer by a valuation-ring unit does not move it into
the square of the maximal ideal. -/
theorem uniformizer_mul_unit_not_mem_maximalIdeal_sq
    (F : DVF.{u, v} K) {pi u : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (hu : IsUnit u) :
    pi * u ∉ F.maximalIdeal ^ 2 := by
  intro hmem
  have hmem' : u * pi ∈ F.maximalIdeal ^ 2 := by
    rw [mul_comm u pi]
    exact hmem
  exact F.uniformizer_not_mem_maximalIdeal_sq hpi
    (((F.maximalIdeal ^ 2).unit_mul_mem_iff_mem hu).1 hmem')

/-- The maximal ideal of a DVF valuation ring is nonzero. -/
theorem maximalIdeal_ne_bot (F : DVF.{u, v} K) :
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

/-! ### Successive quotients of powers of the maximal ideal -/

/-- The submodule `m^(n+1)` inside `m^n`. -/
abbrev maximalIdealPowSuccSubmodule (F : DVF.{u, v} K) (n : ℕ) :
    Submodule F.valuationSubring ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
  Submodule.comap (Submodule.subtype (p := (F.maximalIdeal ^ n : Ideal F.valuationSubring)))
    ((F.maximalIdeal ^ (n + 1) : Ideal F.valuationSubring) :
      Submodule F.valuationSubring F.valuationSubring)

/-- The additive ideal-power quotient `m^n/m^(n+1)`. -/
def MaximalIdealPowSuccQuot (F : DVF.{u, v} K) (n : ℕ) : Type u :=
  ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
    F.maximalIdealPowSuccSubmodule n

/-- A successive maximal-ideal quotient is an additive commutative group. -/
instance maximalIdealPowSuccQuotAddCommGroup
    (F : DVF.{u, v} K) (n : ℕ) :
    AddCommGroup (F.MaximalIdealPowSuccQuot n) := by
  change AddCommGroup
    (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n)
  infer_instance

/-- A successive maximal-ideal quotient is a module over the valuation subring. -/
instance maximalIdealPowSuccQuotModule
    (F : DVF.{u, v} K) (n : ℕ) :
    Module F.valuationSubring (F.MaximalIdealPowSuccQuot n) := by
  change Module F.valuationSubring
    (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n)
  infer_instance

/-- Explicit access to the concrete submodule-quotient representation. -/
def maximalIdealPowSuccQuotConcreteLinearEquiv
    (F : DVF.{u, v} K) (n : ℕ) :
    F.MaximalIdealPowSuccQuot n ≃ₗ[F.valuationSubring]
      (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
        F.maximalIdealPowSuccSubmodule n) := by
  change
    (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
        F.maximalIdealPowSuccSubmodule n) ≃ₗ[F.valuationSubring]
      (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
        F.maximalIdealPowSuccSubmodule n)
  exact LinearEquiv.refl F.valuationSubring _

/-- The quotient map `m^n → m^n/m^(n+1)`. -/
def maximalIdealPowSuccQuotMk (F : DVF.{u, v} K) (n : ℕ) :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) →ₗ[F.valuationSubring]
      F.MaximalIdealPowSuccQuot n := by
  change
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)
      →ₗ[F.valuationSubring]
        (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
          F.maximalIdealPowSuccSubmodule n)
  exact Submodule.mkQ (F.maximalIdealPowSuccSubmodule n)

/-- The concrete linear equivalence sends a quotient representative to the same coset. -/
@[simp]
theorem maximalIdealPowSuccQuotConcreteLinearEquiv_mk
    (F : DVF.{u, v} K) (n : ℕ)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    F.maximalIdealPowSuccQuotConcreteLinearEquiv n
        (F.maximalIdealPowSuccQuotMk n a) =
      Submodule.Quotient.mk a :=
  rfl

/-- The canonical map onto a successive maximal-ideal quotient is surjective. -/
theorem maximalIdealPowSuccQuotMk_surjective
    (F : DVF.{u, v} K) (n : ℕ) :
    Function.Surjective (F.maximalIdealPowSuccQuotMk n) :=
  Submodule.mkQ_surjective (F.maximalIdealPowSuccSubmodule n)

/-- Eliminate an ideal-power quotient class through its canonical map. -/
protected theorem MaximalIdealPowSuccQuot.inductionOn
    (F : DVF.{u, v} K) (n : ℕ)
    {motive : F.MaximalIdealPowSuccQuot n → Prop}
    (q : F.MaximalIdealPowSuccQuot n)
    (h : ∀ a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u),
      motive (F.maximalIdealPowSuccQuotMk n a)) :
    motive q := by
  change motive
    (show ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n from q)
  refine Submodule.Quotient.induction_on
    (F.maximalIdealPowSuccSubmodule n) q ?_
  intro a
  exact h a

/-- Binary elimination through arbitrary ideal-power representatives. -/
protected theorem MaximalIdealPowSuccQuot.inductionOn₂
    (F : DVF.{u, v} K) (n : ℕ)
    {motive : F.MaximalIdealPowSuccQuot n →
      F.MaximalIdealPowSuccQuot n → Prop}
    (q r : F.MaximalIdealPowSuccQuot n)
    (h : ∀ a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u),
      motive (F.maximalIdealPowSuccQuotMk n a)
        (F.maximalIdealPowSuccQuotMk n b)) :
    motive q r := by
  refine MaximalIdealPowSuccQuot.inductionOn F n
    (motive := fun q' ↦ motive q' r) q ?_
  intro a
  refine MaximalIdealPowSuccQuot.inductionOn F n
    (motive := fun r' ↦ motive (F.maximalIdealPowSuccQuotMk n a) r') r ?_
  intro b
  exact h a b

/-- Descend a representative-level function constant modulo `m^(n+1)`. -/
def maximalIdealPowSuccQuotLift
    (F : DVF.{u, v} K) {P : Sort*} (n : ℕ)
    (f : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) → P)
    (h : ∀ a b, a - b ∈ F.maximalIdealPowSuccSubmodule n →
      f a = f b) :
    F.MaximalIdealPowSuccQuot n → P := by
  change
    ((((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n) → P)
  refine Quotient.lift f ?_
  intro a b hab
  have hq :
      (Submodule.Quotient.mk a :
        ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
          F.maximalIdealPowSuccSubmodule n) =
        Submodule.Quotient.mk b :=
    Quotient.sound hab
  exact h a b
    ((Submodule.Quotient.eq (F.maximalIdealPowSuccSubmodule n)).1 hq)

/-- A lift from the successive ideal quotient evaluates on representatives by the supplied map. -/
@[simp]
theorem maximalIdealPowSuccQuotLift_mk
    (F : DVF.{u, v} K) {P : Sort*} (n : ℕ)
    (f : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) → P)
    (h : ∀ a b, a - b ∈ F.maximalIdealPowSuccSubmodule n →
      f a = f b)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    F.maximalIdealPowSuccQuotLift n f h
        (F.maximalIdealPowSuccQuotMk n a) = f a :=
  rfl

/-- Descend a linear map vanishing on `m^(n+1)` inside `m^n`. -/
def maximalIdealPowSuccQuotLinearLift
    (F : DVF.{u, v} K) {M : Type*} [AddCommGroup M]
    [Module F.valuationSubring M] (n : ℕ)
    (f : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)
      →ₗ[F.valuationSubring] M)
    (h : F.maximalIdealPowSuccSubmodule n ≤ f.ker) :
    F.MaximalIdealPowSuccQuot n →ₗ[F.valuationSubring] M := by
  change
    (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n) →ₗ[F.valuationSubring] M
  exact (F.maximalIdealPowSuccSubmodule n).liftQ f h

/-- The linear lift from a successive ideal quotient has the prescribed value on representatives. -/
@[simp]
theorem maximalIdealPowSuccQuotLinearLift_mk
    (F : DVF.{u, v} K) {M : Type*} [AddCommGroup M]
    [Module F.valuationSubring M] (n : ℕ)
    (f : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)
      →ₗ[F.valuationSubring] M)
    (h : F.maximalIdealPowSuccSubmodule n ≤ f.ker)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    F.maximalIdealPowSuccQuotLinearLift n f h
        (F.maximalIdealPowSuccQuotMk n a) = f a :=
  rfl

/-- A successive ideal-quotient class is zero exactly when its representative
lies in the next power. -/
theorem maximalIdealPowSuccQuotMk_eq_zero_iff (F : DVF.{u, v} K) (n : ℕ)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    F.maximalIdealPowSuccQuotMk n a = 0 ↔
      (a : F.valuationSubring) ∈ F.maximalIdeal ^ (n + 1) := by
  change (Submodule.Quotient.mk a :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- Two successive ideal-quotient classes agree exactly when their difference
lies in the next power. -/
@[simp]
theorem maximalIdealPowSuccQuotMk_eq_iff
    (F : DVF.{u, v} K) (n : ℕ)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    F.maximalIdealPowSuccQuotMk n a =
        F.maximalIdealPowSuccQuotMk n b ↔
      a - b ∈ F.maximalIdealPowSuccSubmodule n := by
  change (Submodule.Quotient.mk a :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n) =
    Submodule.Quotient.mk b ↔ _
  exact Submodule.Quotient.eq (F.maximalIdealPowSuccSubmodule n)

/-- Multiplication by the corresponding uniformizer power lands in the required
maximal-ideal power. -/
theorem mul_uniformizer_pow_mem_maximalIdeal_pow (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (r : F.valuationSubring) :
    r * pi ^ n ∈ F.maximalIdeal ^ n := by
  rw [F.maximalIdeal_pow_eq_span_uniformizer_pow hpi n]
  rw [Ideal.mem_span_singleton]
  exact ⟨r, mul_comm _ _⟩

/-- Multiplication by `pi^n`, landing in `m^n`. -/
def maximalIdealPowMulUniformizerPowMap (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    F.valuationSubring →ₗ[F.valuationSubring]
      ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) where
  toFun r := ⟨r * pi ^ n, F.mul_uniformizer_pow_mem_maximalIdeal_pow hpi n r⟩
  map_add' r s := by
    ext
    simp [add_mul]
  map_smul' a r := by
    ext
    simp [mul_assoc]

/-- After multiplying by a uniformizer power, next-level membership is equivalent
to maximal-ideal membership. -/
theorem mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (r : F.valuationSubring) :
    r * pi ^ n ∈ F.maximalIdeal ^ (n + 1) ↔ r ∈ F.maximalIdeal := by
  rw [F.maximalIdeal_pow_eq_span_uniformizer_pow hpi (n + 1),
    F.maximalIdeal_eq_span_uniformizer hpi]
  constructor
  · intro h
    rcases (Ideal.mem_span_singleton.mp h) with ⟨c, hc⟩
    refine Ideal.mem_span_singleton.mpr ⟨c, ?_⟩
    have hpi_ne : pi ≠ 0 := by
      intro hzero
      exact hpi.ne_zero (by simpa using congrArg (fun x : F.valuationSubring => (x : K)) hzero)
    have hne : pi ^ n ≠ 0 := pow_ne_zero n hpi_ne
    have hcancel : r * pi ^ n = (pi * c) * pi ^ n := by
      calc
        r * pi ^ n = pi ^ (n + 1) * c := hc
        _ = (pi * c) * pi ^ n := by
          rw [pow_succ']
          ring
    exact mul_right_cancel₀ hne hcancel
  · intro h
    rcases (Ideal.mem_span_singleton.mp h) with ⟨c, hc⟩
    refine Ideal.mem_span_singleton.mpr ⟨c, ?_⟩
    rw [hc]
    rw [pow_succ']
    ring

/-- The map `O → m^n/m^(n+1)` induced by multiplication by `pi^n`. -/
def maximalIdealPowSuccQuotMulUniformizerPowMap (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    F.valuationSubring →ₗ[F.valuationSubring] F.MaximalIdealPowSuccQuot n :=
  (F.maximalIdealPowSuccQuotMk n).comp
    (F.maximalIdealPowMulUniformizerPowMap hpi n)

/-- The kernel of multiplication by a uniformizer power is the residue-level defining submodule. -/
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_ker (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    LinearMap.ker (F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n) =
      F.maximalIdeal := by
  ext r
  rw [LinearMap.mem_ker]
  change F.maximalIdealPowSuccQuotMk n
      (F.maximalIdealPowMulUniformizerPowMap hpi n r) = 0 ↔
    r ∈ F.maximalIdeal
  rw [F.maximalIdealPowSuccQuotMk_eq_zero_iff n]
  change r * pi ^ n ∈ F.maximalIdeal ^ (n + 1) ↔ r ∈ F.maximalIdeal
  exact F.mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff hpi n r

/-- Multiplication by a uniformizer power surjects onto the successive ideal quotient. -/
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_surjective (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    Function.Surjective (F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n) := by
  intro x
  refine MaximalIdealPowSuccQuot.inductionOn F n
    (motive := fun x' ↦
      ∃ a, F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n a = x') x ?_
  intro a
  have ha_span : (a : F.valuationSubring) ∈
      Ideal.span ({pi ^ n} : Set F.valuationSubring) := by
    simpa [F.maximalIdeal_pow_eq_span_uniformizer_pow hpi n] using a.2
  rcases (Ideal.mem_span_singleton.mp ha_span) with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  change F.maximalIdealPowSuccQuotMk n
      (F.maximalIdealPowMulUniformizerPowMap hpi n r) =
    F.maximalIdealPowSuccQuotMk n a
  have hrep : F.maximalIdealPowMulUniformizerPowMap hpi n r = a := by
    ext
    simp [maximalIdealPowMulUniformizerPowMap, hr, mul_comm]
  rw [hrep]

/-- Principal-ideal scaling: multiplication by `pi^n` identifies
`O/m` linearly with `m^n/m^(n+1)`. -/
noncomputable def residueLinearEquivMaximalIdealPowSuccQuotOfUniformizer
    (F : DVF.{u, v} K) {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    F.residueField ≃ₗ[F.valuationSubring] F.MaximalIdealPowSuccQuot n :=
  (Submodule.quotEquivOfEq (F.maximalIdeal : Submodule F.valuationSubring F.valuationSubring)
      (LinearMap.ker (F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n))
      (F.maximalIdealPowSuccQuotMulUniformizerPowMap_ker hpi n).symm).trans
    ((F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n).quotKerEquivOfSurjective
      (F.maximalIdealPowSuccQuotMulUniformizerPowMap_surjective hpi n))

/-- Additive form of `O/m ≃ m^n/m^(n+1)`. -/
noncomputable def residueAddEquivMaximalIdealPowSuccQuotOfUniformizer
    (F : DVF.{u, v} K) {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    F.residueField ≃+ F.MaximalIdealPowSuccQuot n :=
  (F.residueLinearEquivMaximalIdealPowSuccQuotOfUniformizer hpi n).toAddEquiv

/-- The residue-to-graded-piece equivalence sends a residue class to its
uniformizer-scaled quotient class. -/
@[simp] theorem residueAddEquivMaximalIdealPowSuccQuotOfUniformizer_residue
    (F : DVF.{u, v} K) {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ)
    (r : F.valuationSubring) :
    F.residueAddEquivMaximalIdealPowSuccQuotOfUniformizer hpi n
        (F.residueMap r) =
      F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n r := by
  let f := F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n
  let hker :
      (F.maximalIdeal : Submodule F.valuationSubring F.valuationSubring) =
        LinearMap.ker f :=
    (F.maximalIdealPowSuccQuotMulUniformizerPowMap_ker hpi n).symm
  change (Submodule.quotEquivOfEq
        (F.maximalIdeal : Submodule F.valuationSubring F.valuationSubring)
        (LinearMap.ker f) hker).trans
      (f.quotKerEquivOfSurjective
        (F.maximalIdealPowSuccQuotMulUniformizerPowMap_surjective hpi n))
      (Submodule.Quotient.mk r) = f r
  rw [LinearEquiv.trans_apply]
  have hquot :
      Submodule.quotEquivOfEq
          (F.maximalIdeal : Submodule F.valuationSubring F.valuationSubring)
          (LinearMap.ker f) hker (Submodule.Quotient.mk r) =
        (Submodule.Quotient.mk r :
          F.valuationSubring ⧸ LinearMap.ker f) := by
    exact Submodule.quotEquivOfEq_mk
      (p := (F.maximalIdeal : Submodule F.valuationSubring F.valuationSubring))
      (p' := LinearMap.ker f) hker r
  rw [hquot]
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]

end DVF
end DiscreteValuationField

end

end ValuationTheory
