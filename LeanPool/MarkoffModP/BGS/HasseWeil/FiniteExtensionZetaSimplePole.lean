/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionDivisorClassRecurrence

/-!
# A discrete simple-pole witness for the divisor zeta series

The eventual Riemann--Roch class formula shows that, in every sufficiently
large admissible degree, advancing by the divisor-degree index produces more
effective divisors than multiplication by the corresponding power of the
constant-field cardinality.  This is the coefficient-level noncancellation
behind the simple pole at `T = 1`.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped Polynomial

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance simplePoleConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance simplePoleConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

private theorem geomSum_add' (q a b : ℕ) :
    (∑ i ∈ Finset.range (a + b), q ^ i) =
      (∑ i ∈ Finset.range a, q ^ i) +
        q ^ a * ∑ i ∈ Finset.range b, q ^ i := by
  rw [Finset.sum_range_add, Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]

/-- Multiples of the canonical index divisor give actual divisor classes in
all integer degrees that are nonnegative multiples of the index. -/
def finiteExtensionDivisorClassOfDegreeIndexMul (m : ℕ) :
    FiniteExtensionDivisorClassOfDegree K L
      ((m * finiteExtensionDivisorDegreeIndex K L : ℕ) : ℤ) := by
  let D := m • finiteExtensionDivisorIndexRepresentative K L
  refine ⟨finiteExtensionDivisorClassMap K L D, ?_⟩
  rw [finiteExtensionDivisorClassDegree_mk]
  change finiteExtensionDivisorDegreeHom K L D = _
  rw [map_nsmul]
  change m • finiteExtensionDivisorDegree K L
      (finiteExtensionDivisorIndexRepresentative K L) = _
  rw [finiteExtensionDivisorIndexRepresentative_degree]
  norm_num [D]

/-- In an admissible large degree, the effective-divisor coefficient grows
strictly more than the geometric `q^d` multiple when the degree is advanced
by the divisor-degree index `d`. -/
theorem finiteExtensionEffectiveDivisorCount_pow_mul_lt_add_index_of_uniformRiemann
    (genus threshold n : ℕ)
    (hconstants : algebraicClosure K L = ⊥)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hn : threshold ≤ n)
    (hclass : Nonempty
      (FiniteExtensionDivisorClassOfDegree K L (n : ℤ))) :
    Nat.card K ^ finiteExtensionDivisorDegreeIndex K L *
        finiteExtensionEffectiveDivisorCount K L n <
      finiteExtensionEffectiveDivisorCount K L
        (n + finiteExtensionDivisorDegreeIndex K L) := by
  let d := finiteExtensionDivisorDegreeIndex K L
  let q := Nat.card K
  let h := Nat.card (FiniteExtensionDivisorClassOfDegree K L (n : ℤ))
  let ell := n + 1 - genus
  have hd : 0 < d := finiteExtensionDivisorDegreeIndex_pos K L
  have hn1 : threshold ≤ n + d := by omega
  have hgenus : genus ≤ n := hRiemann.1.trans hn
  let : Finite (FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) :=
    finiteExtensionDivisorClassOfDegree_finite_of_uniformRiemann
      K L genus threshold n hRiemann hn
  let : Nonempty (FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) :=
    hclass
  have hh : 0 < h := by
    exact Nat.card_pos
  have hsum : 0 < ∑ i ∈ Finset.range d, q ^ i := by
    have hle : q ^ 0 ≤ ∑ i ∈ Finset.range d, q ^ i := by
      apply Finset.single_le_sum
      · intro i _
        exact Nat.zero_le _
      · exact Finset.mem_range.mpr hd
    simpa using lt_of_lt_of_le (by simp : 0 < q ^ 0) hle
  have hcount0 :=
    finiteExtensionEffectiveDivisorCount_eq_classCount_mul_geomSum_of_uniformRiemann
      K L genus threshold n hconstants hRiemann hn
  have hcount1 :=
    finiteExtensionEffectiveDivisorCount_eq_classCount_mul_geomSum_of_uniformRiemann
      K L genus threshold (n + d) hconstants hRiemann hn1
  have hclasses :
      Nat.card (FiniteExtensionDivisorClassOfDegree K L ((n + d : ℕ) : ℤ)) =
        h := by
    rw [← finiteExtensionDivisorClassOfDegree_natCard_add_index K L n]
  have hell : n + d + 1 - genus = d + ell := by
    dsimp only [ell]
    omega
  have hformula :
      finiteExtensionEffectiveDivisorCount K L (n + d) =
        q ^ d * finiteExtensionEffectiveDivisorCount K L n +
          h * ∑ i ∈ Finset.range d, q ^ i := by
    rw [hcount0, hcount1]
    change
      Nat.card (FiniteExtensionDivisorClassOfDegree K L
          ((n + d : ℕ) : ℤ)) *
          (∑ i ∈ Finset.range (n + d + 1 - genus), q ^ i) =
        q ^ d *
            (h * ∑ i ∈ Finset.range (n + 1 - genus), q ^ i) +
          h * ∑ i ∈ Finset.range d, q ^ i
    rw [hclasses, hell, geomSum_add' q d ell]
    dsimp only [ell]
    ring
  rw [hformula]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos hh hsum)

/-- There is always a sufficiently large admissible coefficient witnessing
the strict simple-pole growth. -/
theorem exists_finiteExtensionEffectiveDivisorCount_pow_mul_lt_add_index
    (genus threshold : ℕ)
    (hconstants : algebraicClosure K L = ⊥)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold) :
    ∃ n, threshold ≤ n ∧
      Nat.card K ^ finiteExtensionDivisorDegreeIndex K L *
          finiteExtensionEffectiveDivisorCount K L n <
        finiteExtensionEffectiveDivisorCount K L
          (n + finiteExtensionDivisorDegreeIndex K L) := by
  let d := finiteExtensionDivisorDegreeIndex K L
  let n := threshold * d
  have hd : 0 < d := finiteExtensionDivisorDegreeIndex_pos K L
  have hn : threshold ≤ n := by
    dsimp only [n]
    nlinarith
  refine ⟨n, hn, ?_⟩
  apply
    finiteExtensionEffectiveDivisorCount_pow_mul_lt_add_index_of_uniformRiemann
      K L genus threshold n hconstants hRiemann hn
  dsimp only [n, d]
  exact ⟨finiteExtensionDivisorClassOfDegreeIndexMul K L threshold⟩

end

end BGS.HasseWeil
