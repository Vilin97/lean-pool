/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SUnit.LogLattice
import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.KummerCorrespondenceFormula
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.GroupTheory.PowerIndex
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
/-!
# Power quotients of S-unit groups

The finite `n`-th-power quotient of an `S`-unit group, its cardinality, and explicit `ZMod n` coordinates.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The total place-set cardinal `s = #S`, with all infinite places included. -/
def totalPlaceCard
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  Fintype.card (InfinitePlace K) + S.card

/-- The number of places in the `S`-unit theorem is one more than the
free rank of the `S`-unit group.  The extra coordinate is the
roots-of-unity coordinate. -/
theorem totalPlaceCard_eq_sUnitLogRank_add_one
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    totalPlaceCard (K := K) S =
      SUnitGroup.logRank (K := K) S + 1 := by
  unfold totalPlaceCard SUnitGroup.logRank
  have hinfinite :
      0 < Fintype.card (InfinitePlace K) :=
    Fintype.card_pos
  omega

/-- One roots-of-unity coordinate together with `r` free coordinates
is the product of `r + 1` copies of `ZMod n`, in multiplicative
notation. -/
noncomputable def multiplicativeZModProductEquivPiSucc
    (n r : ℕ) :
    Multiplicative (ZMod n) ×
        Multiplicative (Fin r → ZMod n) ≃*
      (Fin (r + 1) → Multiplicative (ZMod n)) where
  toFun x i :=
    Fin.cases x.1
      (fun j => Multiplicative.ofAdd (x.2.toAdd j)) i
  invFun f :=
    (f 0,
      Multiplicative.ofAdd
        (fun j => (f j.succ).toAdd))
  left_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · rfl
    · apply Multiplicative.toAdd.injective
      funext j
      rfl
  right_inv := by
    intro f
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  map_mul' := by
    intro x y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl

/-- Coordinatewise reduction of a finite free `ℤ`-module modulo `n`. -/
def finsuppModHom (d n : ℕ) :
    (Fin d →₀ ℤ) →+ (Fin d → ZMod n) where
  toFun x i := x i
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp

/-- Every vector over `ZMod n` has an integral lift. -/
theorem finsuppModHom_surjective (d n : ℕ) :
    Function.Surjective (finsuppModHom d n) := by
  intro y
  choose x hx using fun i => ZMod.intCast_surjective (y i)
  let x' : Fin d →₀ ℤ :=
    (Finsupp.equivFunOnFinite).symm x
  refine ⟨x', ?_⟩
  ext i
  exact hx i

/-- The kernel of coordinatewise reduction is exactly the subgroup of
`n`-fold multiples. -/
theorem finsuppModHom_ker (d n : ℕ) :
    (finsuppModHom d n).ker =
      LocalFieldTheory.nsmulAddSubgroup (Fin d →₀ ℤ) n := by
  ext x
  constructor
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff]
    let y : Fin d → ℤ := fun i => (x i) / n
    let y' : Fin d →₀ ℤ :=
      (Finsupp.equivFunOnFinite).symm y
    refine ⟨y', ?_⟩
    ext i
    have hdiv : (n : ℤ) ∣ x i := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact congrFun hx i
    change (n : ℤ) * (x i / n) = x i
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiv
  · intro hx
    rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [AddMonoidHom.mem_ker]
    ext i
    simp [finsuppModHom]

/-- The finite-free quotient `(ℤ^d) / n(ℤ^d)` is `(ZMod n)^d`. -/
noncomputable def finsuppNsmulQuotientEquivPiZMod
    (d n : ℕ) :
    (Fin d →₀ ℤ) ⧸
        LocalFieldTheory.nsmulAddSubgroup (Fin d →₀ ℤ) n ≃+
      (Fin d → ZMod n) := by
  rw [← finsuppModHom_ker d n]
  exact QuotientAddGroup.quotientKerEquivOfSurjective
    (finsuppModHom d n)
    (finsuppModHom_surjective d n)

/-- In multiplicative notation, the free integral quotient by `n`-th
powers is a product of copies of `ZMod n`. -/
noncomputable def multiplicativeFinsuppNthPowerQuotientEquivPiZMod
    (d n : ℕ) :
    Multiplicative (Fin d →₀ ℤ) ⧸
        (powMonoidHom n :
          Multiplicative (Fin d →₀ ℤ) →*
            Multiplicative (Fin d →₀ ℤ)).range ≃*
      Multiplicative (Fin d → ZMod n) := by
  rw [
    LocalFieldTheory.powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  exact (finsuppNsmulQuotientEquivPiZMod d n).toMultiplicative

/-- The quotient of a finite free integral module by a positive multiple
is finite. -/
noncomputable instance finite_finsupp_nsmulQuotient
    (d : ℕ) (n : ℕ+) :
    Finite
      ((Fin d →₀ ℤ) ⧸
        LocalFieldTheory.nsmulAddSubgroup
          (Fin d →₀ ℤ) (n : ℕ)) := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact Finite.of_equiv
    (Fin d → ZMod (n : ℕ))
    (finsuppNsmulQuotientEquivPiZMod d n).symm

/-- The cardinality of `(ℤ^d) / n(ℤ^d)` is `n ^ d`. -/
theorem card_finsupp_nsmulQuotient
    (d : ℕ) (n : ℕ+) :
    Nat.card
        ((Fin d →₀ ℤ) ⧸
          LocalFieldTheory.nsmulAddSubgroup
            (Fin d →₀ ℤ) (n : ℕ)) =
      (n : ℕ) ^ d := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  rw [Nat.card_congr
    (finsuppNsmulQuotientEquivPiZMod d n).toEquiv,
    Nat.card_pi]
  simp

omit [NumberField K] in
/-- A primitive `n`-th root in `K` embeds a cyclic subgroup of order `n`
into the roots of unity of the integer ring. -/
theorem n_dvd_numberField_torsionOrder
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    (n : ℕ) ∣ NumberField.Units.torsionOrder K := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hmu
  have hζprim : IsPrimitiveRoot ζ (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hζ
  let ζO : 𝓞 K := hζprim.toInteger
  have hζOprim : IsPrimitiveRoot ζO (n : ℕ) :=
    hζprim.toInteger_isPrimitiveRoot
  let hu : IsUnit ζO := hζOprim.isUnit n.ne_zero
  let u : (𝓞 K)ˣ := hu.unit
  have huval : (u : 𝓞 K) = ζO :=
    hu.unit_spec
  have huprim : IsPrimitiveRoot u (n : ℕ) := by
    rw [← IsPrimitiveRoot.coe_units_iff, huval]
    exact hζOprim
  have hutorsion : u ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion,
      CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, n.pos, huprim.pow_eq_one⟩
  let ut : NumberField.Units.torsion K :=
    ⟨u, hutorsion⟩
  have hutprim : IsPrimitiveRoot ut (n : ℕ) := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact huprim
  rw [NumberField.Units.torsionOrder,
    hutprim.eq_orderOf]
  exact orderOf_dvd_natCard ut

include numberFieldK in
/-- If `K` contains a primitive `n`-th root, the quotient of its roots of
unity by `n`-th powers has cardinality `n`. -/
theorem card_numberField_torsion_nthPowerQuotient
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card
        (NumberField.Units.torsion K ⧸
          (powMonoidHom (n : ℕ) :
            NumberField.Units.torsion K →*
              NumberField.Units.torsion K).range) =
      (n : ℕ) := by
  let T := NumberField.Units.torsion K
  let P :=
    (powMonoidHom (n : ℕ) : T →* T).range
  have hcardP :
      Nat.card P =
        Nat.card T / (Nat.card T).gcd (n : ℕ) := by
    exact IsCyclic.card_powMonoidHom_range T (n : ℕ)
  have hgcd_dvd : (Nat.card T).gcd (n : ℕ) ∣ Nat.card T :=
    Nat.gcd_dvd_left _ _
  have hcard_factor :
      (Nat.card T).gcd (n : ℕ) *
          (Nat.card T / (Nat.card T).gcd (n : ℕ)) =
        Nat.card T :=
    Nat.mul_div_cancel' hgcd_dvd
  have hquotient :
      Nat.card (T ⧸ P) *
          (Nat.card T / (Nat.card T).gcd (n : ℕ)) =
        Nat.card T := by
    rw [← hcardP]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup P).symm
  have hfactor_pos :
      0 < Nat.card T / (Nat.card T).gcd (n : ℕ) := by
    rw [Nat.div_pos_iff]
    have hTpos : 0 < Nat.card T := Nat.card_pos
    exact ⟨Nat.gcd_pos_of_pos_left _ hTpos,
      Nat.gcd_le_left (m := Nat.card T) (n : ℕ) hTpos⟩
  have hcard :
      Nat.card (T ⧸ P) =
        (Nat.card T).gcd (n : ℕ) := by
    exact Nat.eq_of_mul_eq_mul_right hfactor_pos
      (hquotient.trans hcard_factor.symm)
  change Nat.card (T ⧸ P) = (n : ℕ)
  rw [hcard, Nat.gcd_eq_right]
  simpa [T, NumberField.Units.torsionOrder] using
    n_dvd_numberField_torsionOrder (K := K) n hmu

/-- The roots-of-unity contribution to the `S`-unit quotient is one
copy of `ZMod n`. -/
noncomputable def numberFieldTorsionNthPowerQuotientEquivZMod
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    NumberField.Units.torsion K ⧸
        (powMonoidHom (n : ℕ) :
          NumberField.Units.torsion K →*
            NumberField.Units.torsion K).range ≃*
      Multiplicative (ZMod (n : ℕ)) := by
  letI : IsCyclic
      (NumberField.Units.torsion K ⧸
        (powMonoidHom (n : ℕ) :
          NumberField.Units.torsion K →*
            NumberField.Units.torsion K).range) :=
    isCyclic_of_surjective
      (QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          NumberField.Units.torsion K →*
            NumberField.Units.torsion K).range)
      (QuotientGroup.mk'_surjective _)
  apply mulEquivOfCyclicCardEq
  rw [card_numberField_torsion_nthPowerQuotient
    (K := K) n hmu]
  simp

/-- The `n`-th-power quotient of an `S`-unit group is finite. -/
noncomputable instance finite_sUnit_nthPowerQuotient
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+) :
    Finite
      (SUnitGroup (K := K) S ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range) := by
  apply LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv
    (SUnitGroup (K := K) S)
    (NumberField.Units.torsion K ×
      Multiplicative
        (Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ))
    (n : ℕ)
    (SUnitGroup.decomposition (K := K) S)

/-- The `S`-unit theorem in the form used in the finite S-unit preparation argument:

`#(Kˢ / Kˢⁿ) = n ^ (#InfinitePlace K + #S)`.
-/
theorem card_sUnit_nthPowerQuotient
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card
        (SUnitGroup (K := K) S ⧸
          (powMonoidHom (n : ℕ) :
            SUnitGroup (K := K) S →*
              SUnitGroup (K := K) S).range) =
      (n : ℕ) ^ totalPlaceCard (K := K) S := by
  let F :=
    Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hfree :
      Nat.card
          (Multiplicative F ⧸
            (powMonoidHom (n : ℕ) :
              Multiplicative F →* Multiplicative F).range) =
        (n : ℕ) ^ SUnitGroup.logRank (K := K) S := by
    have htransport :=
      LocalFieldTheory.card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
        F (n : ℕ)
    rw [htransport]
    exact card_finsupp_nsmulQuotient
      (SUnitGroup.logRank (K := K) S) n
  have hplace :
      totalPlaceCard (K := K) S =
        SUnitGroup.logRank (K := K) S + 1 := by
    unfold totalPlaceCard SUnitGroup.logRank
    have hinfinite :
        0 < Fintype.card (InfinitePlace K) :=
      Fintype.card_pos
    omega
  calc
    Nat.card
        (SUnitGroup (K := K) S ⧸
          (powMonoidHom (n : ℕ) :
            SUnitGroup (K := K) S →*
              SUnitGroup (K := K) S).range) =
        Nat.card
          ((NumberField.Units.torsion K × Multiplicative F) ⧸
            (powMonoidHom (n : ℕ) :
              NumberField.Units.torsion K × Multiplicative F →*
                NumberField.Units.torsion K ×
                  Multiplicative F).range) := by
      exact Nat.card_congr
        (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
          (SUnitGroup (K := K) S)
          (NumberField.Units.torsion K × Multiplicative F)
          (n : ℕ)
          (SUnitGroup.decomposition (K := K) S)).toEquiv
    _ =
        Nat.card
          ((NumberField.Units.torsion K ⧸
              (powMonoidHom (n : ℕ) :
                NumberField.Units.torsion K →*
                  NumberField.Units.torsion K).range) ×
            (Multiplicative F ⧸
              (powMonoidHom (n : ℕ) :
                Multiplicative F →* Multiplicative F).range)) := by
      exact Nat.card_congr
        (LocalFieldTheory.nthPowerProductQuotientEquiv
          (NumberField.Units.torsion K) (Multiplicative F)
          (n : ℕ)).toEquiv
    _ =
        (n : ℕ) *
          (n : ℕ) ^ SUnitGroup.logRank (K := K) S := by
      rw [Nat.card_prod,
        card_numberField_torsion_nthPowerQuotient (K := K) n hmu,
        hfree]
    _ = (n : ℕ) ^ totalPlaceCard (K := K) S := by
      rw [hplace, pow_succ']

/-- The full `S`-unit quotient has one torsion coordinate and one
coordinate for every logarithmic free generator. -/
noncomputable def sUnitNthPowerQuotientCoordinates
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    SUnitGroup (K := K) S ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range ≃*
      Multiplicative (ZMod (n : ℕ)) ×
        Multiplicative
          (Fin (SUnitGroup.logRank (K := K) S) →
            ZMod (n : ℕ)) :=
  (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
      (SUnitGroup (K := K) S)
      (NumberField.Units.torsion K ×
        Multiplicative
          (Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ))
      (n : ℕ)
      (SUnitGroup.decomposition (K := K) S)).trans <|
    (LocalFieldTheory.nthPowerProductQuotientEquiv
      (NumberField.Units.torsion K)
      (Multiplicative
        (Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ))
      (n : ℕ)).trans <|
      MulEquiv.prodCongr
        (numberFieldTorsionNthPowerQuotientEquivZMod
          (K := K) n hmu)
        (multiplicativeFinsuppNthPowerQuotientEquivPiZMod
          (SUnitGroup.logRank (K := K) S) (n : ℕ))

/-- If a positive power of a global unit is an `S`-unit, then the unit
itself is an `S`-unit.  This is the valuation-theoretic saturation needed
to compare the abstract Kummer quotient with `Kˢ / Kˢⁿ`. -/
theorem mem_sUnitGroup_of_pow_mem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ+) (x : Kˣ)
    (hx : x ^ (n : ℕ) ∈ SUnitGroup (K := K) S) :
    x ∈ SUnitGroup (K := K) S := by
  rw [mem_SUnitGroup_iff] at hx ⊢
  intro v hv
  have hpow := hx v hv
  change
    v.valuation K (((x : Kˣ) : K) ^ (n : ℕ)) = 1
      at hpow
  rw [map_pow] at hpow
  exact
    (pow_eq_one_iff_left
      (a := v.valuation K ((x : Kˣ) : K)) n.ne_zero).mp hpow

/-- The admissible subgroup

`Kˢ · Kˣⁿ ≤ Kˣ`

whose radical extension is the field `N = K(√[n]{Kˢ})` in the finite S-unit preparation argument. -/
def fullSUnitKummerSubgroup
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    KummerTheory.KummerSubgroup K n :=
  ⟨SUnitGroup (K := K) S ⊔
      KummerTheory.unitNthPowersSubgroup K n,
    le_sup_right⟩

/-- Include an `S`-unit in the full `S`-unit Kummer subgroup. -/
def sUnitToFullSUnitKummerSubgroup
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S →*
      (fullSUnitKummerSubgroup (K := K) n S).1 :=
  Subgroup.inclusion le_sup_left

/-- Map an `S`-unit to its class in
`(Kˢ · Kˣⁿ) / Kˣⁿ`. -/
def sUnitToFullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S →*
      KummerTheory.RestrictedRadicalQuotient
        n (fullSUnitKummerSubgroup (K := K) n S) :=
  (KummerTheory.restrictedRadicalQuotientMk
      n (fullSUnitKummerSubgroup (K := K) n S)).comp
    (sUnitToFullSUnitKummerSubgroup (K := K) n S)

/-- `S`-unit `n`-th powers vanish in the full radical quotient. -/
theorem nthPowerSubgroup_le_ker_sUnitToFullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powMonoidHom (n : ℕ) :
        SUnitGroup (K := K) S →*
          SUnitGroup (K := K) S).range ≤
      MonoidHom.ker
        (sUnitToFullSUnitRadicalQuotient (K := K) n S) := by
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      (G := SUnitGroup (K := K) S)).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  rw [MonoidHom.mem_ker, map_pow]
  apply
    (KummerTheory.restrictedRadicalQuotientMk_eq_one_iff
      n (fullSUnitKummerSubgroup (K := K) n S) _).2
  exact
    (KummerTheory.mem_restrictedNthPowersSubgroup_iff
      n (fullSUnitKummerSubgroup (K := K) n S)).2
      ⟨(y : Kˣ), rfl⟩

/-- The canonical comparison

`Kˢ / Kˢⁿ → (Kˢ · Kˣⁿ) / Kˣⁿ`. -/
def sUnitNthPowerQuotientToFullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range →*
      KummerTheory.RestrictedRadicalQuotient
        n (fullSUnitKummerSubgroup (K := K) n S) :=
  QuotientGroup.lift
    (powMonoidHom (n : ℕ) :
      SUnitGroup (K := K) S →*
        SUnitGroup (K := K) S).range
    (sUnitToFullSUnitRadicalQuotient (K := K) n S)
    (nthPowerSubgroup_le_ker_sUnitToFullSUnitRadicalQuotient
      (K := K) n S)

/-- Every class in `(Kˢ · Kˣⁿ) / Kˣⁿ` has an `S`-unit representative. -/
theorem sUnitNthPowerQuotientToFullSUnitRadicalQuotient_surjective
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (sUnitNthPowerQuotientToFullSUnitRadicalQuotient
        (K := K) n S) := by
  intro q
  obtain ⟨x, rfl⟩ :=
    KummerTheory.restrictedRadicalQuotientMk_surjective
      n (fullSUnitKummerSubgroup (K := K) n S) q
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Subgroup.mem_sup.1 x.property
  let yS : SUnitGroup (K := K) S := ⟨y, hy⟩
  refine
    ⟨QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range yS, ?_⟩
  change
    KummerTheory.restrictedRadicalQuotientMk
        n (fullSUnitKummerSubgroup (K := K) n S)
        (sUnitToFullSUnitKummerSubgroup (K := K) n S yS) =
      KummerTheory.restrictedRadicalQuotientMk
        n (fullSUnitKummerSubgroup (K := K) n S) x
  apply
    (KummerTheory.restrictedRadicalQuotientMk_eq_iff
      n (fullSUnitKummerSubgroup (K := K) n S) _ _).2
  change y / x.1 ∈ KummerTheory.unitNthPowersSubgroup K n
  rw [← hyz]
  simpa using
    (KummerTheory.unitNthPowersSubgroup K n).inv_mem hz

/-- The canonical comparison from `Kˢ / Kˢⁿ` is injective.  The only
arithmetic point is saturation of the `S`-unit group under positive
powers, proved above from valuations. -/
theorem sUnitNthPowerQuotientToFullSUnitRadicalQuotient_injective
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective
      (sUnitNthPowerQuotientToFullSUnitRadicalQuotient
        (K := K) n S) := by
  intro q r hqr
  induction q using QuotientGroup.induction_on' with
  | _ x =>
      induction r using QuotientGroup.induction_on' with
      | _ y =>
          apply (QuotientGroup.eq_iff_div_mem).2
          have hglobal :
              ((x : Kˣ) / (y : Kˣ)) ∈
                KummerTheory.unitNthPowersSubgroup K n := by
            have hrestricted :=
              (KummerTheory.restrictedRadicalQuotientMk_eq_iff
                n (fullSUnitKummerSubgroup (K := K) n S) _ _).1 hqr
            exact
              (KummerTheory.mem_restrictedNthPowersSubgroup_iff
                n (fullSUnitKummerSubgroup (K := K) n S)).1 hrestricted
          obtain ⟨z, hz⟩ :=
            (KummerTheory.mem_unitNthPowersSubgroup_iff n).mp hglobal
          have hzpow :
              z ^ (n : ℕ) ∈ SUnitGroup (K := K) S := by
            rw [hz]
            exact (SUnitGroup (K := K) S).div_mem x.property y.property
          let zS : SUnitGroup (K := K) S :=
            ⟨z, mem_sUnitGroup_of_pow_mem (K := K) S n z hzpow⟩
          apply
            (MonoidHom.mem_range
              (G := SUnitGroup (K := K) S)).2
          refine ⟨zS, ?_⟩
          rw [powMonoidHom_apply]
          apply Subtype.ext
          exact hz

/-- The exact quotient identification used to define
`N = K(√[n]{Kˢ})`. -/
noncomputable def sUnitNthPowerQuotientEquivFullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range ≃*
      KummerTheory.RestrictedRadicalQuotient
        n (fullSUnitKummerSubgroup (K := K) n S) :=
  MulEquiv.ofBijective
    (sUnitNthPowerQuotientToFullSUnitRadicalQuotient
      (K := K) n S)
    ⟨sUnitNthPowerQuotientToFullSUnitRadicalQuotient_injective
        (K := K) n S,
      sUnitNthPowerQuotientToFullSUnitRadicalQuotient_surjective
        (K := K) n S⟩

/-- The full `S`-unit radical quotient is finite. -/
noncomputable instance finite_fullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite
      (KummerTheory.RestrictedRadicalQuotient
        n (fullSUnitKummerSubgroup (K := K) n S)) :=
  Finite.of_equiv
    (SUnitGroup (K := K) S ⧸
      (powMonoidHom (n : ℕ) :
        SUnitGroup (K := K) S →*
          SUnitGroup (K := K) S).range)
    (sUnitNthPowerQuotientEquivFullSUnitRadicalQuotient
      (K := K) n S)

/-- The radical quotient defining `N` has cardinality `n ^ s`. -/
theorem card_fullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card
        (KummerTheory.RestrictedRadicalQuotient
          n (fullSUnitKummerSubgroup (K := K) n S)) =
      (n : ℕ) ^ totalPlaceCard (K := K) S := by
  rw [← card_sUnit_nthPowerQuotient (K := K) S n hmu]
  exact Nat.card_congr
    (sUnitNthPowerQuotientEquivFullSUnitRadicalQuotient
      (K := K) n S).symm.toEquiv

end KummerTheory
