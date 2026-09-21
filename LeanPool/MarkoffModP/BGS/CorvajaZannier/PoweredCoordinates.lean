/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryIndependence
import LeanPool.MarkoffModP.BGS.External.GeneralCurveTheorems
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Prime-to-characteristic powers of plane-curve coordinates

Corvaja--Zannier's plane torsion corollary applies the function-field theorem
to powers of the two coordinate functions.  This file makes the algebraic
part of that passage explicit.  A positive power preserves the geometric
nonconstancy of every character.  If the exponent is prime to the
characteristic, a separating coordinate power generates the function field
over its Frobenius subfield, has nonzero differential, and has minimal
polynomial of degree exactly the characteristic.

The last theorem applies the already-proved resultant form of Proposition 1
to powered coordinates once an explicit irreducible relation between those
powers is supplied.  Constructing that elimination relation, and controlling
its bidegrees, remains a separate algebraic-geometric step; it is not assumed
implicitly here.
-/

namespace BGS.CorvajaZannier

noncomputable section

/-- No nontrivial character in the powered coordinates is constant on the
geometric torus curve. -/
def PoweredTorusCurveNotSubtorusTranslate
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K)
    (m n : ℕ) : Prop :=
  ∀ (a b : ℤ), (a ≠ 0 ∨ b ≠ 0) →
    ∀ c : (AlgebraicClosure K)ˣ,
      ∃ x y : (AlgebraicClosure K)ˣ,
        MvPolynomial.eval ![(x : AlgebraicClosure K),
          (y : AlgebraicClosure K)]
            (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f) = 0 ∧
        (x ^ m) ^ a * (y ^ n) ^ b ≠ c

/-- Positive coordinate powers preserve the source's multiplicative
independence-modulo-constants condition. -/
theorem poweredTorusCurveNotSubtorusTranslate
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hnot : BGS.External.TorusCurveNotSubtorusTranslate f) :
    PoweredTorusCurveNotSubtorusTranslate f m n := by
  intro a b hab c
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hab' : (m : ℤ) * a ≠ 0 ∨ (n : ℤ) * b ≠ 0 := by
    rcases hab with ha | hb
    · exact Or.inl (mul_ne_zero hm0 ha)
    · exact Or.inr (mul_ne_zero hn0 hb)
  obtain ⟨x, y, hcurve, hcharacter⟩ :=
    hnot ((m : ℤ) * a) ((n : ℤ) * b) hab' c
  refine ⟨x, y, hcurve, ?_⟩
  simpa only [← zpow_natCast, ← zpow_mul] using hcharacter

/-- If `m` is coprime to `p`, adjoining `z ^ m` is the same as adjoining
`z`, provided the `p`-th power of `z` is already in the smaller field.

The reverse inclusion is the explicit Bézout identity
`a * m + b * p = 1`, interpreted using integer powers in the ambient field. -/
theorem adjoin_pow_eq_adjoin_of_coprime
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (z : L) (hz : z ≠ 0) (p m : ℕ) (hcop : Nat.Coprime m p)
    (hzp : z ^ p ∈ IntermediateField.adjoin F ({z ^ m} : Set L)) :
    IntermediateField.adjoin F ({z ^ m} : Set L) =
      IntermediateField.adjoin F ({z} : Set L) := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact pow_mem (IntermediateField.subset_adjoin F {z} (Set.mem_singleton z)) m
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rcases hcop.isCoprime with ⟨a, b, hab⟩
    have hzm : z ^ m ∈ IntermediateField.adjoin F ({z ^ m} : Set L) :=
      IntermediateField.subset_adjoin F {z ^ m} (Set.mem_singleton (z ^ m))
    have hprod : (z ^ m) ^ a * (z ^ p) ^ b = z := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
        ← zpow_add₀ hz]
      simpa [mul_comm] using congrArg (fun e : ℤ => z ^ e) hab
    have hmem : (z ^ m) ^ a * (z ^ p) ^ b ∈
        IntermediateField.adjoin F ({z ^ m} : Set L) :=
      mul_mem (zpow_mem hzm a) (zpow_mem hzp b)
    rw [hprod] at hmem
    exact hmem

/-- A prime-to-characteristic power of a Frobenius-separating generator is
again a generator over the Frobenius subfield. -/
theorem adjoin_frobeniusSubfield_pow_eq_top
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]
    (z : L) (hz : z ≠ 0) (m : ℕ) (hm : ¬ p ∣ m)
    [Algebra.IsSeparable
      (IntermediateField.adjoin (frobeniusSubfield L p) {z}) L] :
    IntermediateField.adjoin (frobeniusSubfield L p) ({z ^ m} : Set L) = ⊤ := by
  let F := frobeniusSubfield L p
  have hcop : Nat.Coprime m p :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hm).symm
  have hzp : z ^ p ∈ IntermediateField.adjoin F ({z ^ m} : Set L) := by
    let zp : F := ⟨z ^ p, ⟨z, by simp [frobenius_def]⟩⟩
    change (zp : L) ∈ IntermediateField.adjoin F ({z ^ m} : Set L)
    exact (IntermediateField.adjoin F ({z ^ m} : Set L)).algebraMap_mem zp
  rw [adjoin_pow_eq_adjoin_of_coprime z hz p m hcop hzp]
  exact adjoin_frobeniusSubfield_eq_top p z

/-- A prime-to-characteristic power of a function with nonzero derivative
again has nonzero derivative. -/
theorem derivation_pow_ne_zero_of_not_dvd
    {C L : Type*} [CommRing C] [Field L] [Algebra C L]
    {p : ℕ} [CharP L p]
    (D : Derivation C L L) (z : L) (m : ℕ)
    (hm : ¬ p ∣ m) (hz : z ≠ 0) (hDz : D z ≠ 0) :
    D (z ^ m) ≠ 0 := by
  rw [D.leibniz_pow]
  rw [← Nat.cast_smul_eq_nsmul L, smul_smul]
  exact smul_ne_zero
    (mul_ne_zero (by
      rw [ne_eq, CharP.cast_eq_zero_iff L p]
      exact hm) (pow_ne_zero _ hz)) hDz

/-- The exact-constants derivation associated to `z` also detects every
prime-to-characteristic power of `z`. -/
theorem exists_derivation_power_ne_zero_with_exact_frobenius_constants
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]
    (z : L) (hz : z ≠ 0) (hzNot : z ∉ frobeniusSubfield L p)
    (m : ℕ) (hm : ¬ p ∣ m)
    [Algebra.IsSeparable
      (IntermediateField.adjoin (frobeniusSubfield L p) {z}) L] :
    ∃ D : Derivation (frobeniusSubfield L p) L L,
      D (z ^ m) ≠ 0 ∧
      ∀ w : L, D w = 0 ↔
        ∃ c : frobeniusSubfield L p,
          algebraMap (frobeniusSubfield L p) L c = w := by
  obtain ⟨D, hDz, hker⟩ :=
    exists_derivation_with_exact_frobenius_constants (p := p) z hzNot
  refine ⟨D, derivation_pow_ne_zero_of_not_dvd D z m hm hz ?_, hker⟩
  simp [hDz]

/-- A prime-to-characteristic power of a Frobenius-separating element is not
itself a Frobenius power. -/
theorem frobeniusPower_not_mem
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]
    (z : L) (hz : z ≠ 0) (hzNot : z ∉ frobeniusSubfield L p)
    (m : ℕ) (hm : ¬ p ∣ m)
    [Algebra.IsSeparable
      (IntermediateField.adjoin (frobeniusSubfield L p) {z}) L] :
    z ^ m ∉ frobeniusSubfield L p := by
  obtain ⟨D, hDpow, hker⟩ :=
    exists_derivation_power_ne_zero_with_exact_frobenius_constants
      z hz hzNot m hm
  intro hpow
  apply hDpow
  apply (hker (z ^ m)).2
  exact ⟨⟨z ^ m, hpow⟩, rfl⟩

/-- The minimal polynomial of a prime-to-characteristic power of a
Frobenius-separating element still has degree exactly `p` over `L^p`. -/
theorem frobeniusPower_minpoly_natDegree_eq_char
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]
    (z : L) (hz : z ≠ 0) (hzNot : z ∉ frobeniusSubfield L p)
    (m : ℕ) (hm : ¬ p ∣ m)
    [Algebra.IsSeparable
      (IntermediateField.adjoin (frobeniusSubfield L p) {z}) L] :
    (minpoly (frobeniusSubfield L p) (z ^ m)).natDegree = p := by
  let F := frobeniusSubfield L p
  have hnot : z ^ m ∉ F := frobeniusPower_not_mem z hz hzNot m hm
  have htop : IntermediateField.adjoin F ({z ^ m} : Set L) = ⊤ :=
    adjoin_frobeniusSubfield_pow_eq_top z hz m hm
  let E : IntermediateField F L := IntermediateField.adjoin F {z ^ m}
  letI : Algebra.IsSeparable E L := by
    change Algebra.IsSeparable
      (IntermediateField.adjoin F ({z ^ m} : Set L)) L
    rw [htop]
    refine ⟨fun w ↦ ?_⟩
    let wTop : (⊤ : IntermediateField F L) := ⟨w, trivial⟩
    change IsSeparable (⊤ : IntermediateField F L) w
    have hw : algebraMap (⊤ : IntermediateField F L) L wTop = w := rfl
    rw [← hw]
    exact isSeparable_algebraMap (K := L) wTop
  exact minpoly_natDegree_over_frobeniusSubfield_eq_char
    (p := p) (z ^ m) hnot

/-- A positive power of the first coordinate remains transcendental over the
constant field. -/
theorem firstCoordinatePow_transcendental
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    {m : ℕ} (hm : 0 < m) :
    letI := planeCurveCoordinateRing_isDomain hf
    Transcendental K ((planeCurveFunction f 0) ^ m) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  exact (firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)).pow hm

/-- A positive power of the second coordinate remains transcendental over the
constant field. -/
theorem secondCoordinatePow_transcendental
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    Transcendental K ((planeCurveFunction f 1) ^ n) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  exact (secondCoordinate_transcendental hf
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)).pow hn

/-- The first powered coordinate alone generates the curve function field
over its Frobenius subfield. -/
theorem adjoin_frobeniusSubfield_firstCoordinatePow_eq_top
    {K : Type*} [Field K] [PerfectField K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : ¬ p ∣ m) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    IntermediateField.adjoin
        (frobeniusSubfield (PlaneCurveFunctionField f) p)
        ({(planeCurveFunction f 0) ^ m} : Set (PlaneCurveFunctionField f)) = ⊤ := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  letI : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let x : L := planeCurveFunction f 0
  have hsep := (finiteSeparable_over_firstCoordinate_of_irreducible
    hf hpartialSecond).2
  letI : Algebra.IsSeparable (FirstCoordinateSubfield f) L := hsep
  letI : Algebra.IsSeparable (IntermediateField.adjoin F {x}) L :=
    isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin
      (K := K) (L := L) (p := p) x
  have hxTrans : Transcendental K x := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxTrans
    rw [hx]
    exact isAlgebraic_zero
  exact adjoin_frobeniusSubfield_pow_eq_top x hx0 m hm

/-- The second powered coordinate alone generates the curve function field
over its Frobenius subfield. -/
theorem adjoin_frobeniusSubfield_secondCoordinatePow_eq_top
    {K : Type*} [Field K] [PerfectField K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (n : ℕ) (hn : ¬ p ∣ n) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    IntermediateField.adjoin
        (frobeniusSubfield (PlaneCurveFunctionField f) p)
        ({(planeCurveFunction f 1) ^ n} : Set (PlaneCurveFunctionField f)) = ⊤ := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  letI : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let y : L := planeCurveFunction f 1
  have hsep := (finiteSeparable_over_secondCoordinate_of_irreducible
    hf hpartialFirst).2
  letI : Algebra.IsSeparable (SecondCoordinateSubfield f) L := hsep
  letI : Algebra.IsSeparable (IntermediateField.adjoin F {y}) L :=
    isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin
      (K := K) (L := L) (p := p) y
  have hyTrans : Transcendental K y := secondCoordinate_transcendental hf
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hy0 : y ≠ 0 := by
    intro hy
    apply hyTrans
    rw [hy]
    exact isAlgebraic_zero
  exact adjoin_frobeniusSubfield_pow_eq_top y hy0 n hn

/-- Exact Frobenius-subfield degree of the first powered coordinate. -/
theorem minpoly_firstCoordinatePow_natDegree_eq_char
    {K : Type*} [Field K] [PerfectField K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : ¬ p ∣ m) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    (minpoly (frobeniusSubfield (PlaneCurveFunctionField f) p)
      ((planeCurveFunction f 0) ^ m)).natDegree = p := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  letI : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let x : L := planeCurveFunction f 0
  have hsep := (finiteSeparable_over_firstCoordinate_of_irreducible
    hf hpartialSecond).2
  letI : Algebra.IsSeparable (FirstCoordinateSubfield f) L := hsep
  letI : Algebra.IsSeparable (IntermediateField.adjoin F {x}) L :=
    isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin
      (K := K) (L := L) (p := p) x
  have hxTrans : Transcendental K x := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxTrans
    rw [hx]
    exact isAlgebraic_zero
  have hxNot : x ∉ F := firstCoordinate_not_mem_frobeniusSubfield
    hf hpartialSecond
  exact frobeniusPower_minpoly_natDegree_eq_char x hx0 hxNot m hm

/-- Exact Frobenius-subfield degree of the second powered coordinate. -/
theorem minpoly_secondCoordinatePow_natDegree_eq_char
    {K : Type*} [Field K] [PerfectField K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (n : ℕ) (hn : ¬ p ∣ n) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    (minpoly (frobeniusSubfield (PlaneCurveFunctionField f) p)
      ((planeCurveFunction f 1) ^ n)).natDegree = p := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  letI : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let y : L := planeCurveFunction f 1
  have hsep := (finiteSeparable_over_secondCoordinate_of_irreducible
    hf hpartialFirst).2
  letI : Algebra.IsSeparable (SecondCoordinateSubfield f) L := hsep
  letI : Algebra.IsSeparable (IntermediateField.adjoin F {y}) L :=
    isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin
      (K := K) (L := L) (p := p) y
  have hyTrans : Transcendental K y := secondCoordinate_transcendental hf
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hy0 : y ≠ 0 := by
    intro hy
    apply hyTrans
    rw [hy]
    exact isAlgebraic_zero
  have hyNot : y ∉ F := secondCoordinate_not_mem_frobeniusSubfield
    hf hpartialFirst
  exact frobeniusPower_minpoly_natDegree_eq_char y hy0 hyNot n hn

/-- One derivation with exact constant field `L^p` detects both powered plane
coordinates.  This is the differential hypothesis required by the torsion
specialization. -/
theorem exists_derivation_coordinatePowers_ne_zero
    {K : Type*} [Field K] [PerfectField K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : ¬ p ∣ m) (hn : ¬ p ∣ n) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    ∃ D : Derivation
        (frobeniusSubfield (PlaneCurveFunctionField f) p)
        (PlaneCurveFunctionField f) (PlaneCurveFunctionField f),
      D ((planeCurveFunction f 0) ^ m) ≠ 0 ∧
      D ((planeCurveFunction f 1) ^ n) ≠ 0 ∧
      ∀ z : PlaneCurveFunctionField f, D z = 0 ↔
        ∃ c : frobeniusSubfield (PlaneCurveFunctionField f) p,
          algebraMap (frobeniusSubfield (PlaneCurveFunctionField f) p)
            (PlaneCurveFunctionField f) c = z := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  letI : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  have hsepX := (finiteSeparable_over_firstCoordinate_of_irreducible
    hf hpartialSecond).2
  letI : Algebra.IsSeparable (FirstCoordinateSubfield f) L := hsepX
  letI : Algebra.IsSeparable (IntermediateField.adjoin F {x}) L :=
    isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin
      (K := K) (L := L) (p := p) x
  have hsepY := (finiteSeparable_over_secondCoordinate_of_irreducible
    hf hpartialFirst).2
  letI : Algebra.IsSeparable (SecondCoordinateSubfield f) L := hsepY
  letI : Algebra.IsSeparable (IntermediateField.adjoin F {y}) L :=
    isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin
      (K := K) (L := L) (p := p) y
  have hxTrans : Transcendental K x := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  have hyTrans : Transcendental K y := secondCoordinate_transcendental hf
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxTrans
    rw [hx]
    exact isAlgebraic_zero
  have hy0 : y ≠ 0 := by
    intro hy
    apply hyTrans
    rw [hy]
    exact isAlgebraic_zero
  have hxNot : x ∉ F := firstCoordinate_not_mem_frobeniusSubfield
    hf hpartialSecond
  have hyNot : y ∉ F := secondCoordinate_not_mem_frobeniusSubfield
    hf hpartialFirst
  have hynNot : y ^ n ∉ F := frobeniusPower_not_mem y hy0 hyNot n hn
  obtain ⟨D, hDx, hker⟩ :=
    exists_derivation_power_ne_zero_with_exact_frobenius_constants
      x hx0 hxNot m hm
  have hDy : D (y ^ n) ≠ 0 := by
    intro hzero
    obtain ⟨c, hc⟩ := (hker (y ^ n)).mp hzero
    apply hynNot
    rw [← hc]
    exact c.property
  exact ⟨D, hDx, hDy, hker⟩

/-- Proposition 1 for powered plane coordinates, with all Frobenius and
separability obligations discharged.  The remaining polynomial `g` is an
explicit relation between the powers; its irreducibility and bidegrees are
kept visible because constructing it is the genuine elimination frontier. -/
theorem poweredCoordinates_auxiliaryFamily_linearIndependent_of_relation
    {K : Type*} [Field K] [PerfectField K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (m n : ℕ) (hn : ¬ p ∣ n) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    ∀ (g : Polynomial (Polynomial
        (frobeniusSubfield (PlaneCurveFunctionField f) p)))
      (a b h k : ℕ),
      0 < a → 0 < h → 0 < k →
      Irreducible g →
      g.natDegree = a →
      (transposeBivariate g).natDegree = b →
      (∀ i, (g.coeff i).natDegree ≤ b) →
      evalBivariate ((planeCurveFunction f 1) ^ n)
        ((planeCurveFunction f 0) ^ m) g = 0 →
      a * h + b * k < p →
      ¬ (a ≤ k ∧ b ≤ h) →
      LinearIndependent
        (frobeniusSubfield (PlaneCurveFunctionField f) p)
        (auxiliaryFamily ((planeCurveFunction f 0) ^ m)
          ((planeCurveFunction f 1) ^ n) h k) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  letI : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  intro g a b h k ha hh hk hg hdegreeU hdegreeV hcoeff hzero hsize hexcluded
  have hminpoly : (minpoly F (y ^ n)).natDegree = p :=
    minpoly_secondCoordinatePow_natDegree_eq_char hf hpartialFirst n hn
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hn
    simp [hn0]
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn0
  have hyTrans : Transcendental K y := secondCoordinate_transcendental hf
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hynTrans : Transcendental K (y ^ n) := hyTrans.pow hnPos
  have hynOne : y ^ n ≠ 1 := by
    intro hyn
    apply hynTrans
    rw [hyn]
    exact isAlgebraic_one
  exact auxiliaryFamily_linearIndependent_of_irreducible_bidegree
    g a b h k p ha hh hk hg hdegreeU hdegreeV hcoeff
      (x ^ m) (y ^ n) hynOne hminpoly hzero hsize hexcluded

end

end BGS.CorvajaZannier
