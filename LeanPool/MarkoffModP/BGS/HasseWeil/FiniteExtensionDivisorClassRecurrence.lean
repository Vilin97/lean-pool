/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionDivisorDegreeIndex
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionEffectiveDivisorSplit
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannSpaceProjectivization

/-!
# Divisor classes and the indexed eventual recurrence

This file builds the exhaustive divisor-class quotient and partitions the
effective divisors of a fixed degree into its class fibers.  Under exact
constants, each fiber is the projectivization of the corresponding Riemann
space.

The final recurrence is conditional on one explicit geometric input:
the uniform eventual Riemann formula for *arbitrary* exhaustive divisors,
not merely divisors on one effective ray.  This is the remaining theorem
needed to turn the existing one-ray stabilization results into the global
divisor-count recurrence.  In particular, no finiteness of a projective
divisor class group is assumed: it follows, in every sufficiently large
degree, from the uniform formula and the already proved finiteness of the
effective divisors of that degree.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance divisorClassConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance divisorClassConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The additive subgroup of exhaustive principal divisors. -/
def finiteExtensionPrincipalDivisorSubgroup :
    AddSubgroup (FiniteExtensionDivisor K L) where
  carrier := {D | ∃ x : L, x ≠ 0 ∧ finiteExtensionPrincipalDivisor K L x = D}
  zero_mem' := ⟨1, one_ne_zero, finiteExtensionPrincipalDivisor_one K L⟩
  add_mem' := by
    rintro D E ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, mul_ne_zero hx hy,
      finiteExtensionPrincipalDivisor_mul K L x y hx hy⟩
  neg_mem' := by
    rintro D ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, inv_ne_zero hx,
      finiteExtensionPrincipalDivisor_inv K L x hx⟩

/-- The exhaustive divisor class group. -/
abbrev FiniteExtensionDivisorClass :=
  FiniteExtensionDivisor K L ⧸ finiteExtensionPrincipalDivisorSubgroup K L

/-- The quotient map from exhaustive divisors to divisor classes. -/
def finiteExtensionDivisorClassMap :
    FiniteExtensionDivisor K L →+ FiniteExtensionDivisorClass K L :=
  QuotientAddGroup.mk' (finiteExtensionPrincipalDivisorSubgroup K L)

omit [Fintype K] in
@[simp]
theorem finiteExtensionDivisorClassMap_principal
    (x : L) (hx : x ≠ 0) :
    finiteExtensionDivisorClassMap K L
        (finiteExtensionPrincipalDivisor K L x) = 0 := by
  change
    ((finiteExtensionPrincipalDivisor K L x : FiniteExtensionDivisor K L) :
      FiniteExtensionDivisor K L ⧸ finiteExtensionPrincipalDivisorSubgroup K L) = 0
  exact QuotientAddGroup.eq_zero_iff _ |>.2 ⟨x, hx, rfl⟩

omit [Fintype K] in
private theorem finiteExtensionPrincipalDivisorSubgroup_le_degreeKernel :
    finiteExtensionPrincipalDivisorSubgroup K L ≤
      (finiteExtensionDivisorDegreeHom K L).ker := by
  rintro D ⟨x, hx, rfl⟩
  exact finiteExtensionDivisorDegree_principal K L x hx

/-- Divisor degree descends to divisor classes because principal divisors
have degree zero. -/
def finiteExtensionDivisorClassDegree :
    FiniteExtensionDivisorClass K L →+ ℤ :=
  QuotientAddGroup.lift (finiteExtensionPrincipalDivisorSubgroup K L)
    (finiteExtensionDivisorDegreeHom K L)
    (by exact finiteExtensionPrincipalDivisorSubgroup_le_degreeKernel K L)

omit [Fintype K] in
@[simp]
theorem finiteExtensionDivisorClassDegree_mk
    (D : FiniteExtensionDivisor K L) :
    finiteExtensionDivisorClassDegree K L
        (finiteExtensionDivisorClassMap K L D) =
      finiteExtensionDivisorDegree K L D :=
  by
    classical
    rfl

/-- Divisor classes of a prescribed integer degree. -/
abbrev FiniteExtensionDivisorClassOfDegree (n : ℤ) :=
  {c : FiniteExtensionDivisorClass K L //
    finiteExtensionDivisorClassDegree K L c = n}

/-- A chosen divisor representative of a class. -/
def finiteExtensionDivisorClassRepresentative
    (c : FiniteExtensionDivisorClass K L) : FiniteExtensionDivisor K L :=
  Quotient.out c

omit [Fintype K] in
@[simp]
theorem finiteExtensionDivisorClassMap_representative
    (c : FiniteExtensionDivisorClass K L) :
    finiteExtensionDivisorClassMap K L
        (finiteExtensionDivisorClassRepresentative K L c) = c :=
  Quotient.out_eq c

omit [Fintype K] in
theorem finiteExtensionDivisorClassRepresentative_degree
    {n : ℤ} (c : FiniteExtensionDivisorClassOfDegree K L n) :
    finiteExtensionDivisorDegree K L
        (finiteExtensionDivisorClassRepresentative K L c.1) = n := by
  classical
  calc
    finiteExtensionDivisorDegree K L
        (finiteExtensionDivisorClassRepresentative K L c.1) =
        finiteExtensionDivisorClassDegree K L
          (finiteExtensionDivisorClassMap K L
            (finiteExtensionDivisorClassRepresentative K L c.1)) := by
          rw [finiteExtensionDivisorClassDegree_mk]
    _ = finiteExtensionDivisorClassDegree K L c.1 := by
      rw [finiteExtensionDivisorClassMap_representative]
    _ = n := c.2

/-- Translation by a divisor of degree `d` identifies the degree-`n` and
degree-`n+d` class fibers. -/
def finiteExtensionDivisorClassOfDegreeTranslateEquiv
    (H : FiniteExtensionDivisor K L) (n d : ℤ)
    (hH : finiteExtensionDivisorDegree K L H = d) :
    FiniteExtensionDivisorClassOfDegree K L n ≃
      FiniteExtensionDivisorClassOfDegree K L (n + d) where
  toFun c := ⟨c.1 + finiteExtensionDivisorClassMap K L H, by
    rw [map_add, c.2, finiteExtensionDivisorClassDegree_mk, hH]⟩
  invFun c := ⟨c.1 - finiteExtensionDivisorClassMap K L H, by
    rw [map_sub, c.2, finiteExtensionDivisorClassDegree_mk, hH]
    omega⟩
  left_inv c := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

/-- The divisor class of an effective divisor of natural degree `n`. -/
def finiteExtensionEffectiveDivisorClassOfDegree (n : ℕ)
    (D : {D : FiniteExtensionEffectiveDivisor K L //
      finiteExtensionEffectiveDivisorDegree K L D = n}) :
    FiniteExtensionDivisorClassOfDegree K L (n : ℤ) := by
  refine ⟨finiteExtensionDivisorClassMap K L
    (finiteExtensionEffectiveDivisorToDivisor K L D.1), ?_⟩
  rw [finiteExtensionDivisorClassDegree_mk]
  rw [← finiteExtensionEffectiveDivisorDegree_cast K L D.1, D.2]

/-- The fixed-degree effective divisors lying in one divisor class. -/
abbrev FiniteExtensionEffectiveDivisorClassFiber (n : ℕ)
    (c : FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) :=
  {D : {D : FiniteExtensionEffectiveDivisor K L //
      finiteExtensionEffectiveDivisorDegree K L D = n} //
    finiteExtensionEffectiveDivisorClassOfDegree K L n D = c}

omit [Fintype K] [DecidableEq K] in
private theorem finiteExtensionEffectiveDivisorToDivisor_of_symm
    (D : {D : FiniteExtensionDivisor K L // ∀ P, 0 ≤ D P}) :
    finiteExtensionEffectiveDivisorToDivisor K L
        ((finiteExtensionEffectiveDivisorEquivEffectiveIntegralDivisor K L).symm D) =
      D.1 := by
  classical
  exact congrArg Subtype.val
    ((finiteExtensionEffectiveDivisorEquivEffectiveIntegralDivisor K L).apply_symm_apply D)

/-- A fixed-degree class fiber is exactly the effective divisors in the
principal class of its chosen representative. -/
def finiteExtensionEffectiveDivisorClassFiberEquiv
    (n : ℕ) (c : FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) :
    FiniteExtensionEffectiveDivisorClassFiber K L n c ≃
      EffectiveDivisorInPrincipalClass K L
        (finiteExtensionDivisorClassRepresentative K L c.1) where
  toFun E := by
    let D := finiteExtensionEffectiveDivisorToDivisor K L E.1.1
    let R := finiteExtensionDivisorClassRepresentative K L c.1
    have hclass : finiteExtensionDivisorClassMap K L D =
        finiteExtensionDivisorClassMap K L R := by
      calc
        finiteExtensionDivisorClassMap K L D = c.1 := by
          exact congrArg Subtype.val E.2
        _ = finiteExtensionDivisorClassMap K L R :=
          (finiteExtensionDivisorClassMap_representative K L c.1).symm
    refine ⟨D, finiteExtensionEffectiveDivisorToDivisor_effective K L E.1.1, ?_⟩
    obtain ⟨x, hx, hdiv⟩ :=
      (QuotientAddGroup.eq_iff_sub_mem.mp hclass :
        D - R ∈ finiteExtensionPrincipalDivisorSubgroup K L)
    refine ⟨x, hx, ?_⟩
    rw [hdiv]
    exact (sub_add_cancel D R).symm
  invFun E := by
    let D : FiniteExtensionEffectiveDivisor K L :=
      (finiteExtensionEffectiveDivisorEquivEffectiveIntegralDivisor K L).symm
        ⟨E.1, E.2.1⟩
    have hDcast : finiteExtensionEffectiveDivisorToDivisor K L D = E.1 :=
      congrArg Subtype.val
        ((finiteExtensionEffectiveDivisorEquivEffectiveIntegralDivisor K L).apply_symm_apply
          ⟨E.1, E.2.1⟩)
    have hdegreeInt : finiteExtensionDivisorDegree K L E.1 = (n : ℤ) := by
      obtain ⟨x, hx, hE⟩ := E.2.2
      rw [hE, finiteExtensionDivisorDegree_add,
        finiteExtensionDivisorDegree_principal K L x hx,
        finiteExtensionDivisorClassRepresentative_degree K L c]
      simp
    have hdegreeNat : finiteExtensionEffectiveDivisorDegree K L D = n := by
      have hcast := finiteExtensionEffectiveDivisorDegree_cast K L D
      rw [hDcast, hdegreeInt] at hcast
      exact_mod_cast hcast
    refine ⟨⟨D, hdegreeNat⟩, ?_⟩
    apply Subtype.ext
    change finiteExtensionDivisorClassMap K L
      (finiteExtensionEffectiveDivisorToDivisor K L D) = c.1
    rw [hDcast]
    obtain ⟨x, hx, hE⟩ := E.2.2
    rw [hE, map_add, finiteExtensionDivisorClassMap_principal K L x hx,
      zero_add, finiteExtensionDivisorClassMap_representative]
  left_inv E := by
    apply Subtype.ext
    apply Subtype.ext
    change
      (finiteExtensionEffectiveDivisorEquivEffectiveIntegralDivisor K L).symm
        ((finiteExtensionEffectiveDivisorEquivEffectiveIntegralDivisor K L) E.1.1) = E.1.1
    exact (finiteExtensionEffectiveDivisorEquivEffectiveIntegralDivisor K L).symm_apply_apply E.1.1
  right_inv E := by
    apply Subtype.ext
    exact finiteExtensionEffectiveDivisorToDivisor_of_symm K L ⟨E.1, E.2.1⟩

/-- Uniform eventual Riemann formula for arbitrary exhaustive divisors.
This is the single geometric input not supplied by the current one-ray
stabilization files. -/
def HasFiniteExtensionUniformEventualRiemannFormula
    (genus threshold : ℕ) : Prop :=
  genus ≤ threshold ∧
    ∀ (D : FiniteExtensionDivisor K L) (n : ℕ), threshold ≤ n →
      finiteExtensionDivisorDegree K L D = (n : ℤ) →
        Module.Finite K (finiteExtensionRiemannSpace K L D) ∧
          Module.finrank K (finiteExtensionRiemannSpace K L D) =
            n + 1 - genus

/-- The uniform eventual formula makes every sufficiently large divisor
class effective. -/
theorem finiteExtensionEffectiveDivisorClassOfDegree_surjective_of_uniformRiemann
    (genus threshold n : ℕ)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hn : threshold ≤ n) :
    Function.Surjective
      (finiteExtensionEffectiveDivisorClassOfDegree K L n) := by
  intro c
  let R := finiteExtensionDivisorClassRepresentative K L c.1
  have hRdegree : finiteExtensionDivisorDegree K L R = (n : ℤ) :=
    finiteExtensionDivisorClassRepresentative_degree K L c
  have hdata := hRiemann.2 R n hn hRdegree
  let : Module.Finite K (finiteExtensionRiemannSpace K L R) := hdata.1
  have hpositive :
      0 < Module.finrank K (finiteExtensionRiemannSpace K L R) := by
    rw [hdata.2]
    have hg := hRiemann.1
    omega
  let : Nontrivial (finiteExtensionRiemannSpace K L R) :=
    Module.finrank_pos_iff.mp hpositive
  obtain ⟨x, hx⟩ := exists_ne (0 : finiteExtensionRiemannSpace K L R)
  let E : EffectiveDivisorInPrincipalClass K L R :=
    effectiveDivisorInPrincipalClassOfNonzeroSection K L R ⟨x, hx⟩
  let F := (finiteExtensionEffectiveDivisorClassFiberEquiv K L n c).symm E
  exact ⟨F.1, F.2⟩

/-- Hence the set of divisor classes of every sufficiently large admissible
degree is finite. -/
theorem finiteExtensionDivisorClassOfDegree_finite_of_uniformRiemann
    (genus threshold n : ℕ)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hn : threshold ≤ n) :
    Finite (FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) := by
  exact Finite.of_surjective
    (finiteExtensionEffectiveDivisorClassOfDegree K L n)
    (finiteExtensionEffectiveDivisorClassOfDegree_surjective_of_uniformRiemann
      K L genus threshold n hRiemann hn)

/-- Under exact constants, every sufficiently large fixed-degree class fiber
is finite. -/
theorem finiteExtensionEffectiveDivisorClassFiber_finite_of_uniformRiemann
    (genus threshold n : ℕ)
    (hconstants : algebraicClosure K L = ⊥)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hn : threshold ≤ n)
    (c : FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) :
    Finite (FiniteExtensionEffectiveDivisorClassFiber K L n c) := by
  let R := finiteExtensionDivisorClassRepresentative K L c.1
  have hRdegree : finiteExtensionDivisorDegree K L R = (n : ℤ) :=
    finiteExtensionDivisorClassRepresentative_degree K L c
  have hdata := hRiemann.2 R n hn hRdegree
  let : Module.Finite K (finiteExtensionRiemannSpace K L R) := hdata.1
  let : Finite (finiteExtensionRiemannSpace K L R) :=
    Module.finite_of_finite K
  exact Finite.of_equiv
    (Projectivization K (finiteExtensionRiemannSpace K L R))
    ((projectiveRiemannSectionEquivEffectiveDivisorInPrincipalClass
        K L R hconstants).trans
      (finiteExtensionEffectiveDivisorClassFiberEquiv K L n c).symm)

/-- Every large degree-`n` class fiber has the same geometric-sum
cardinality. -/
theorem finiteExtensionEffectiveDivisorClassFiber_card_eq_geomSum_of_uniformRiemann
    (genus threshold n : ℕ)
    (hconstants : algebraicClosure K L = ⊥)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hn : threshold ≤ n)
    (c : FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) :
    Nat.card (FiniteExtensionEffectiveDivisorClassFiber K L n c) =
      ∑ i ∈ Finset.range (n + 1 - genus), Nat.card K ^ i := by
  let R := finiteExtensionDivisorClassRepresentative K L c.1
  have hRdegree : finiteExtensionDivisorDegree K L R = (n : ℤ) :=
    finiteExtensionDivisorClassRepresentative_degree K L c
  have hdata := hRiemann.2 R n hn hRdegree
  rw [Nat.card_congr (finiteExtensionEffectiveDivisorClassFiberEquiv K L n c)]
  rw [effectiveDivisorInPrincipalClass_card_eq_geomSum K L R hconstants]
  rw [hdata.2]

/-- The global effective-divisor coefficient is the number of degree-`n`
classes times the common projective Riemann-space count. -/
theorem finiteExtensionEffectiveDivisorCount_eq_classCount_mul_geomSum_of_uniformRiemann
    (genus threshold n : ℕ)
    (hconstants : algebraicClosure K L = ⊥)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hn : threshold ≤ n) :
    finiteExtensionEffectiveDivisorCount K L n =
      Nat.card (FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) *
        ∑ i ∈ Finset.range (n + 1 - genus), Nat.card K ^ i := by
  let : Finite (FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) :=
    finiteExtensionDivisorClassOfDegree_finite_of_uniformRiemann
      K L genus threshold n hRiemann hn
  let : Fintype (FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) :=
    Fintype.ofFinite _
  let (c : FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) :
      Finite (FiniteExtensionEffectiveDivisorClassFiber K L n c) :=
    finiteExtensionEffectiveDivisorClassFiber_finite_of_uniformRiemann
      K L genus threshold n hconstants hRiemann hn c
  let f := finiteExtensionEffectiveDivisorClassOfDegree K L n
  calc
    finiteExtensionEffectiveDivisorCount K L n =
        Nat.card {D : FiniteExtensionEffectiveDivisor K L //
          finiteExtensionEffectiveDivisorDegree K L D = n} := by
      rw [finiteExtensionEffectiveDivisorCount, Nat.card_eq_fintype_card]
    _ = Nat.card (Σ c : FiniteExtensionDivisorClassOfDegree K L (n : ℤ),
          FiniteExtensionEffectiveDivisorClassFiber K L n c) := by
      exact (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ c : FiniteExtensionDivisorClassOfDegree K L (n : ℤ),
          Nat.card (FiniteExtensionEffectiveDivisorClassFiber K L n c) :=
      Nat.card_sigma
    _ = ∑ _c : FiniteExtensionDivisorClassOfDegree K L (n : ℤ),
          (∑ i ∈ Finset.range (n + 1 - genus), Nat.card K ^ i) := by
      apply Finset.sum_congr rfl
      intro c _
      exact finiteExtensionEffectiveDivisorClassFiber_card_eq_geomSum_of_uniformRiemann
        K L genus threshold n hconstants hRiemann hn c
    _ = Nat.card (FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) *
          ∑ i ∈ Finset.range (n + 1 - genus), Nat.card K ^ i := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [Nat.card_eq_fintype_card]

/-- A canonical signed divisor whose degree is the divisor-degree index.  It
need not be effective; this is why translation is carried out in the class
group rather than by adding an effective divisor. -/
def finiteExtensionDivisorIndexRepresentative :
    FiniteExtensionDivisor K L :=
  Classical.choose (exists_finiteExtensionDivisor_degree_eq_index K L)

omit [Fintype K] [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionDivisorIndexRepresentative_degree :
    finiteExtensionDivisorDegree K L
        (finiteExtensionDivisorIndexRepresentative K L) =
      (finiteExtensionDivisorDegreeIndex K L : ℤ) :=
  Classical.choose_spec (exists_finiteExtensionDivisor_degree_eq_index K L)

omit [Fintype K] in
/-- Translation by the signed index representative preserves the number of
classes when the degree is advanced by the index. -/
theorem finiteExtensionDivisorClassOfDegree_natCard_add_index (n : ℕ) :
    Nat.card (FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) =
      Nat.card (FiniteExtensionDivisorClassOfDegree K L
        ((n + finiteExtensionDivisorDegreeIndex K L : ℕ) : ℤ)) := by
  classical
  let e := finiteExtensionDivisorClassOfDegreeTranslateEquiv K L
    (finiteExtensionDivisorIndexRepresentative K L)
    (n : ℤ) (finiteExtensionDivisorDegreeIndex K L : ℤ)
    (finiteExtensionDivisorIndexRepresentative_degree K L)
  have h := Nat.card_congr e
  convert h using 1
  norm_num

private theorem geomSum_add (q a b : ℕ) :
    (∑ i ∈ Finset.range (a + b), q ^ i) =
      (∑ i ∈ Finset.range a, q ^ i) +
        q ^ a * ∑ i ∈ Finset.range b, q ^ i := by
  rw [Finset.sum_range_add, Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]

/-- The finite geometric sums satisfy the indexed curve-zeta recurrence. -/
theorem geomSum_indexed_recurrence (q ell d : ℕ) :
    (∑ i ∈ Finset.range (ell + 2 * d), q ^ i) +
        q ^ d * (∑ i ∈ Finset.range ell, q ^ i) =
      (q ^ d + 1) * ∑ i ∈ Finset.range (ell + d), q ^ i := by
  rw [show ell + 2 * d = (ell + d) + d by omega]
  rw [geomSum_add q (ell + d) d, geomSum_add q ell d, pow_add]
  ring

private theorem mul_geomSum_indexed_recurrence (h q ell d : ℕ) :
    h * (∑ i ∈ Finset.range (ell + 2 * d), q ^ i) +
        q ^ d * (h * (∑ i ∈ Finset.range ell, q ^ i)) =
      (q ^ d + 1) *
        (h * ∑ i ∈ Finset.range (ell + d), q ^ i) := by
  calc
    h * (∑ i ∈ Finset.range (ell + 2 * d), q ^ i) +
          q ^ d * (h * (∑ i ∈ Finset.range ell, q ^ i)) =
        h * ((∑ i ∈ Finset.range (ell + 2 * d), q ^ i) +
          q ^ d * (∑ i ∈ Finset.range ell, q ^ i)) := by ring
    _ = h * ((q ^ d + 1) *
          ∑ i ∈ Finset.range (ell + d), q ^ i) := by
      rw [geomSum_indexed_recurrence]
    _ = (q ^ d + 1) *
          (h * ∑ i ∈ Finset.range (ell + d), q ^ i) := by ring

/-- The actual eventual indexed recurrence for exhaustive effective-divisor
counts.  The only unproved input is the explicitly stated uniform eventual
Riemann formula. -/
theorem finiteExtensionEffectiveDivisorCount_indexed_eventual_recurrence
    (genus threshold n : ℕ)
    (hconstants : algebraicClosure K L = ⊥)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hn : threshold ≤ n) :
    finiteExtensionEffectiveDivisorCount K L
          (n + 2 * finiteExtensionDivisorDegreeIndex K L) +
        Nat.card K ^ finiteExtensionDivisorDegreeIndex K L *
          finiteExtensionEffectiveDivisorCount K L n =
      (Nat.card K ^ finiteExtensionDivisorDegreeIndex K L + 1) *
        finiteExtensionEffectiveDivisorCount K L
          (n + finiteExtensionDivisorDegreeIndex K L) := by
  let d := finiteExtensionDivisorDegreeIndex K L
  let q := Nat.card K
  have hn1 : threshold ≤ n + d := by omega
  have hn2 : threshold ≤ n + 2 * d := by omega
  have hcount0 :=
    finiteExtensionEffectiveDivisorCount_eq_classCount_mul_geomSum_of_uniformRiemann
      K L genus threshold n hconstants hRiemann hn
  have hcount1 :=
    finiteExtensionEffectiveDivisorCount_eq_classCount_mul_geomSum_of_uniformRiemann
      K L genus threshold (n + d) hconstants hRiemann hn1
  have hcount2 :=
    finiteExtensionEffectiveDivisorCount_eq_classCount_mul_geomSum_of_uniformRiemann
      K L genus threshold (n + 2 * d) hconstants hRiemann hn2
  have hclass01 :
      Nat.card (FiniteExtensionDivisorClassOfDegree K L (n : ℤ)) =
        Nat.card (FiniteExtensionDivisorClassOfDegree K L ((n + d : ℕ) : ℤ)) := by
    simpa [d] using
      (finiteExtensionDivisorClassOfDegree_natCard_add_index K L n)
  have hclass12 :
      Nat.card (FiniteExtensionDivisorClassOfDegree K L ((n + d : ℕ) : ℤ)) =
        Nat.card (FiniteExtensionDivisorClassOfDegree K L
          ((n + 2 * d : ℕ) : ℤ)) := by
    simpa [d, Nat.add_assoc, two_mul] using
      (finiteExtensionDivisorClassOfDegree_natCard_add_index K L (n + d))
  have hgenus : genus ≤ n := hRiemann.1.trans hn
  have hlength1 : n + d + 1 - genus = (n + 1 - genus) + d := by omega
  have hlength2 : n + 2 * d + 1 - genus = (n + 1 - genus) + 2 * d := by omega
  change
    finiteExtensionEffectiveDivisorCount K L (n + 2 * d) +
        q ^ d * finiteExtensionEffectiveDivisorCount K L n =
      (q ^ d + 1) * finiteExtensionEffectiveDivisorCount K L (n + d)
  rw [hcount0, hcount1, hcount2]
  rw [← hclass12, ← hclass01]
  rw [hlength1, hlength2]
  exact mul_geomSum_indexed_recurrence
    (Nat.card (FiniteExtensionDivisorClassOfDegree K L (n : ℤ)))
    q (n + 1 - genus) d

/-- Subtractive integer form of the indexed recurrence, matching the
coefficient hypothesis used by formal zeta rationality. -/
theorem finiteExtensionEffectiveDivisorCount_indexed_eventual_recurrence_int
    (genus threshold n : ℕ)
    (hconstants : algebraicClosure K L = ⊥)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hn : threshold ≤ n) :
    (finiteExtensionEffectiveDivisorCount K L
        (n + 2 * finiteExtensionDivisorDegreeIndex K L) : ℤ) =
      ((Nat.card K ^ finiteExtensionDivisorDegreeIndex K L + 1 : ℕ) : ℤ) *
          finiteExtensionEffectiveDivisorCount K L
            (n + finiteExtensionDivisorDegreeIndex K L) -
        (Nat.card K ^ finiteExtensionDivisorDegreeIndex K L : ℕ) *
          finiteExtensionEffectiveDivisorCount K L n := by
  have h := congrArg (fun m : ℕ ↦ (m : ℤ))
    (finiteExtensionEffectiveDivisorCount_indexed_eventual_recurrence
      K L genus threshold n hconstants hRiemann hn)
  push_cast at h ⊢
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm, add_left_comm, add_assoc] using h

/-- Complex form used directly by `FormalZetaRationality`. -/
theorem finiteExtensionEffectiveDivisorCount_indexed_eventual_recurrence_complex
    (genus threshold n : ℕ)
    (hconstants : algebraicClosure K L = ⊥)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hn : threshold ≤ n) :
    (finiteExtensionEffectiveDivisorCount K L
        (n + 2 * finiteExtensionDivisorDegreeIndex K L) : ℂ) =
      ((Nat.card K : ℂ) ^ finiteExtensionDivisorDegreeIndex K L + 1) *
          finiteExtensionEffectiveDivisorCount K L
            (n + finiteExtensionDivisorDegreeIndex K L) -
        (Nat.card K : ℂ) ^ finiteExtensionDivisorDegreeIndex K L *
          finiteExtensionEffectiveDivisorCount K L n := by
  have h := congrArg (fun m : ℕ ↦ (m : ℂ))
    (finiteExtensionEffectiveDivisorCount_indexed_eventual_recurrence
      K L genus threshold n hconstants hRiemann hn)
  push_cast at h ⊢
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm, add_left_comm, add_assoc] using h

end

end BGS.HasseWeil
