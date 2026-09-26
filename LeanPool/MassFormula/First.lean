/-
Copyright (c) 2026 Hyeon Seung-Hyeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hyeon Seung-Hyeon
-/

-- Adapted for Lean Pool from 0stellensatz/MassFormula at 7fa41a621f724f110183904d3fd19c6730a932ad.
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import LeanPool.MassFormula.Defs
import LeanPool.MassFormula.Discriminant
import LeanPool.MassFormula.EisensteinMonogenic
import LeanPool.MassFormula.UniformizerParam
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Auxiliary file: `tsum_one_div_q_pow_c`—**Theorem 1**, the mass formula (§3, pp.1032–1033)

This file follows Serre's first proof (§3) in a *root-counting variant*. The paper partitions the
Eisenstein region into classes indexed by the isomorphism classes of representatives, proves Theorem
2, and recovers Theorem 1 through Remark 3°. Here, instead, each individual `L` in `sigma K n` gets
the counting function `rootCount L`—the number of roots of `f` lying in `L`—and the same
change-of-variables computation along the parametrization of equations (5)–(13) evaluates its
integral over the Eisenstein region as `(1 / q ^ (d L + 1)) * (1 - 1 / q)`. Since a.e. `f` is
separable (equation (3)) with each of its `n` roots generating exactly one member of `sigma K n`,
the counts sum to `n` a.e., and integrating gives Theorem 1 directly—no quotient by isomorphism, no
`w L`. This is the paper's computation reassembled, and is the more direct route to the sum indexed
by `sigma K n`; Theorem 2 is recovered from the
same core ([Serre 1978, §3, pp.1032–1033][Serre1978]).

Modeling decisions, local to this file:

- A monic polynomial of degree `n` *is* its coefficient vector `a : Fin n → K`, with `a i` the
  coefficient of `X ^ i` (`toPoly`)—the paper's identification of the space of such polynomials
  with a subspace of the coefficient space.
- The paper's measure, the product of the coordinate measures normalized so that `𝒪[K]` has volume
  `1`, is realized in one stroke as the Haar measure of the additive group `Fin n → K` normalized on
  the positive compact integer box (`muCoeff`). By uniqueness of Haar measure this is the product of
  the normalized coordinate measures, but the product structure is only ever needed *inside* the
  volume computations, so neither `Measure.pi` nor any σ-finiteness enters the statements.
- The Borel structure `[MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]` is a per-lemma
  hypothesis of the machinery; the concluding theorem introduces it via `borel`, so its statement
  requires no measurable-space parameter.
- The Eisenstein condition of equation (1) is stated multiplicatively: every coefficient lies in the
  open unit ball, and the constant term has the largest valuation below `1`—that of a uniformizer.
- `rootCount L a` counts the roots of `toPoly a` in `L` *with multiplicity* (`Multiset.card` of
  `aroots`); on the full-measure separable locus all multiplicities are `1`, so the count agrees
  with the paper's fiber count of the parametrization ([Serre 1978, Lemma 1, p.1033][Serre1978]).

The file contains the volume of the Eisenstein region (`muCoeff_eisensteinSet`, with its
coset-counting helpers), the Eisenstein irreducibility and separability facts, the a.e. reduction of
the root-count identity (`tsum_rootCount`, via the null hyperplane `a 1 = 0`), the counting
combinatorics of `tsum_rootCount_of_separable`, the ramification core
`isTotallyRamified_adjoin_root` (via `EisensteinMonogenic.lean`), the bound `sub_one_le_d`, the
local constancy `rootCount_eventuallyEq` of the root count on the separable locus (via the Newton
lifting of `RootLifting.lean`), the a.e. measurability `aemeasurable_rootCount` of the root count
(from that local constancy), the countability `countable_sigma` of `sigma K n` (positive masses with
bounded finite subsums), the change-of-variables identity `lintegral_rootCount` (assembled from the
box decomposition below on top of `UniformizerParam.lean` and `HaarScaling.lean`), and the assembly
of Theorem 1 (`tsum_one_div_q_pow_c`).

## References

* [Serre1978] J-P. Serre, *Une «formule de masse» pour les extensions totalement ramifiées de
  degré donné d'un corps local*, C. R. Acad. Sci. Paris **286** (1978), Série A, 1031–1036.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer, 1979.
-/

public section

open ValuativeRel MeasureTheory
open scoped ENNReal Pointwise

namespace MassFormula

variable {K : Type*} [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
  [IsNonarchimedeanLocalField K]

/-! ## The coefficient space, its measure, and the counting functions -/

/-- The monic polynomial of degree `n` encoded by a coefficient vector `a : Fin n → K`, with `a i`
the coefficient of `X ^ i`—the paper's identification of monic polynomials of degree `n` with
points of the coefficient space ([Serre 1978, p.1032][Serre1978]). -/
noncomputable def toPoly {n : ℕ} (a : Fin n → K) : Polynomial K :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

/-- The counting function implicit in Lemma 1: the number of roots of `toPoly a` lying in the
subextension `L`, with multiplicity. On the separable locus this is the fiber count of the
parametrization over `f`, that is the number of uniformizers of `L` with minimal polynomial `f`
([Serre 1978, Lemma 1, p.1033][Serre1978]). -/
noncomputable def rootCount (L : IntermediateField K (SeparableClosure K)) {n : ℕ}
    (a : Fin n → K) : ℕ :=
  ((toPoly a).aroots ↥L).card

variable (K)

/-- The Eisenstein region of equation (1), as a set of coefficient vectors: every coefficient lies
in the open unit ball, and the constant term has the largest valuation below `1`, that of a
uniformizer ([Serre 1978, eq. (1), p.1032][Serre1978]). -/
def eisensteinSet (n : ℕ) : Set (Fin n → K) :=
  {a | (∀ i, valuation K (a i) < 1) ∧
    ∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K ((toPoly a).coeff 0)}

/-- The integer box in the coefficient space, compact with nonempty interior—the normalizing set
of the measure below, giving `𝒪[K]` volume `1` coordinatewise ([Serre 1978, p.1032][Serre1978]). -/
noncomputable def integerPositiveCompacts (n : ℕ) :
    TopologicalSpace.PositiveCompacts (Fin n → K) where
  carrier := Set.univ.pi fun _ => (𝒪[K] : Set K)
  isCompact' := isCompact_univ_pi fun _ => isCompact_iff_compactSpace.mpr
    (inferInstanceAs (CompactSpace 𝒪[K]))
  interior_nonempty' := by
    rw [interior_pi_set Set.finite_univ]
    exact ⟨0, fun i _ => mem_interior_iff_mem_nhds.mpr
      ((IsValuativeTopology.mem_nhds_zero_iff _).mpr
        ⟨1, fun x hx => (Valuation.mem_integer_iff _ _).mpr (le_of_lt (by simpa using hx))⟩)⟩

/-- The paper's measure on the coefficient space: the Haar measure of the locally compact additive
group `Fin n → K`, normalized so that the integer box has volume `1`
([Serre 1978, p.1032][Serre1978]). -/
noncomputable def muCoeff (n : ℕ) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] :
    Measure (Fin n → K) :=
  Measure.addHaarMeasure (integerPositiveCompacts K n)

variable {K}

/-! ## The `X^n + ∑ C (c i) X^i` coefficient shape, over any commutative ring -/

/-- Below the top degree, the `k`-th coefficient of the shape is `c k`. -/
private lemma shape_coeff {R : Type*} [CommRing R] {n : ℕ} (c : Fin n → R) (k : ℕ) (hk : k < n) :
    (Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).coeff k =
      c ⟨k, hk⟩ := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, ite_eq_right (by omega),
    Polynomial.finsetSum_coeff, Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]
  · simp
  · intro i _ hne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      ite_eq_right fun h => hne (Fin.ext (by simpa using h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The lower-order sum of the shape has degree `< n`. -/
private lemma shape_degree_sum_lt {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (c : Fin n → R) :
    (∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).degree <
      (Polynomial.X ^ n : Polynomial R).degree := by
  rw [Polynomial.degree_X_pow]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro i _
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)

/-- The shape is monic. -/
private lemma shape_monic {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} (c : Fin n → R) :
    (Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).Monic :=
  (Polynomial.monic_X_pow n).add_of_left (shape_degree_sum_lt c)

/-- The shape has `natDegree` exactly `n`. -/
private lemma shape_natDegree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (c : Fin n → R) :
    (Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).natDegree =
      n := by
  have h := Polynomial.degree_add_eq_left_of_degree_lt (shape_degree_sum_lt c)
  rw [Polynomial.degree_X_pow] at h
  exact Polynomial.natDegree_eq_of_degree_eq_some h

omit [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- Conversely, a monic polynomial of degree `n` *is* the shape on its own lower-coefficient
vector—`toPoly` inverts the coefficient extraction. -/
private lemma toPoly_coeffs {n : ℕ} {F : Polynomial K} (hF : F.Monic) (hdeg : F.natDegree = n) :
    toPoly (fun i : Fin n => F.coeff i) = F := by
  unfold toPoly
  ext k
  rcases lt_trichotomy k n with hk | hk | hk
  · exact shape_coeff _ k hk
  · -- at `k = n` both sides are the leading coefficient `1`
    have hsum0 : (∑ i : Fin n, Polynomial.C (F.coeff (i : ℕ)) * Polynomial.X ^ (i : ℕ)).coeff k
        = 0 := by
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        ite_eq_right (by have := i.isLt; omega), mul_zero]
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, ite_eq_left hk, hsum0, add_zero, hk, ← hdeg,
      hF.coeff_natDegree]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [shape_natDegree]; exact hk),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hk)]

/-! ## Haar-measure helpers: residue representatives, the uniformizer, and coset counting

The box-volume computations below implement the coset counting behind equation (2): the integer box
has volume `1` by normalization; it is the disjoint union of `q ^ n` translates of the
open-unit-ball box, indexed by vectors of residues; and the unit-ball box is in turn the disjoint
union of `q` translates of the box whose `0`-coordinate is shrunk one valuation level, indexed by
residues via a uniformizer ([Serre 1978, eq. (2), p.1032][Serre1978]).
-/

omit [IsUniformAddGroup K] in
/-- The open unit ball of `K` is the vanishing locus of the residue map. -/
private lemma valuation_lt_one_iff_residue_eq_zero (z : 𝒪[K]) :
    valuation K (z : K) < 1 ↔ IsLocalRing.residue 𝒪[K] z = 0 := by
  have h : IsLocalRing.residue 𝒪[K] z = 0 ↔ z ∈ IsLocalRing.maximalIdeal 𝒪[K] :=
    Ideal.Quotient.eq_zero_iff_mem
  rw [h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← Valuation.Integer.not_isUnit_iff_valuation_lt_one]

omit [IsUniformAddGroup K] in
/-- A uniformizer of `K`: a nonzero element of largest valuation below `1`—extracted from a
generator of the maximal ideal of the discrete valuation ring `𝒪[K]`. -/
private lemma exists_uniformizer :
    ∃ ϖ : K, ϖ ≠ 0 ∧ valuation K ϖ < 1 ∧
      ∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K ϖ := by
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  refine ⟨ϖ₀, ?_, ?_, ?_⟩
  · exact_mod_cast hϖ₀.ne_zero
  · exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hϖ₀.not_isUnit
  · intro y hy
    have hyO : y ∈ 𝒪[K] := ((valuation K).mem_integer_iff y).mpr hy.le
    have h1 : ¬IsUnit (⟨y, hyO⟩ : 𝒪[K]) :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hy
    have h2 : (⟨y, hyO⟩ : 𝒪[K]) ∈ IsLocalRing.maximalIdeal 𝒪[K] :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h1)
    rw [hϖ₀.maximalIdeal_eq, Ideal.mem_span_singleton] at h2
    obtain ⟨z, hz⟩ := h2
    have hy' : y = (ϖ₀ : K) * (z : K) := by
      have h3 := congrArg (fun w : 𝒪[K] => (w : K)) hz
      push_cast at h3
      exact h3
    rw [hy', map_mul]
    exact mul_le_of_le_one_right' (((valuation K).mem_integer_iff _).mp z.2)

omit [IsUniformAddGroup K] in
/-- Any element of the open unit ball has valuation at most that of a given irreducible of
`𝒪[K]`—every uniformizer realizes the largest valuation below `1`. -/
private lemma valuation_le_of_lt_one {π : 𝒪[K]} (hπ : Irreducible π) {y : K}
    (hy : valuation K y < 1) : valuation K y ≤ valuation K (π : K) := by
  have hyO : y ∈ 𝒪[K] := ((valuation K).mem_integer_iff y).mpr hy.le
  have h1 : ¬IsUnit (⟨y, hyO⟩ : 𝒪[K]) :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hy
  have h2 : (⟨y, hyO⟩ : 𝒪[K]) ∈ IsLocalRing.maximalIdeal 𝒪[K] :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h1)
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at h2
  obtain ⟨z, hz⟩ := h2
  have hy' : y = (π : K) * (z : K) := by
    have h3 := congrArg (fun w : 𝒪[K] => (w : K)) hz
    push_cast at h3
    exact h3
  rw [hy', map_mul]
  exact mul_le_of_le_one_right' (((valuation K).mem_integer_iff _).mp z.2)

omit [IsUniformAddGroup K] in
/-- Open balls are open: around any point, the basis ball of the same radius stays inside, by the
ultrametric inequality. -/
private lemma isOpen_ballLT (γ : (ValueGroupWithZero K)ˣ) :
    IsOpen {x : K | valuation K x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  refine ((IsValuativeTopology.hasBasis_nhds y).mem_iff).mpr ⟨γ, trivial, fun z hz => ?_⟩
  have h : valuation K z ≤ max (valuation K (z - y)) (valuation K y) := by
    simpa using (valuation K).map_add (z - y) y
  exact h.trans_lt (max_lt hz hy)

omit [IsUniformAddGroup K] in
/-- Co-balls are open as well: inside the basis ball of radius `γ` around a point, the valuation
cannot drop below `γ`, by the ultrametric equality. -/
private lemma isOpen_ballGE (γ : (ValueGroupWithZero K)ˣ) :
    IsOpen {x : K | (γ : ValueGroupWithZero K) ≤ valuation K x} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hy' : (γ : ValueGroupWithZero K) ≤ valuation K y := hy
  refine ((IsValuativeTopology.hasBasis_nhds y).mem_iff).mpr ⟨γ, trivial, fun z hz => ?_⟩
  have hz' : valuation K (z - y) < (γ : ValueGroupWithZero K) := hz
  change (γ : ValueGroupWithZero K) ≤ valuation K z
  refine le_trans hy' ?_
  by_contra hlt
  push Not at hlt
  have h1 : valuation K y ≤ max (valuation K (y - z)) (valuation K z) := by
    simpa using (valuation K).map_add (y - z) z
  have h2 : valuation K (y - z) < valuation K y := by
    rw [(valuation K).map_sub_swap y z]
    exact hz'.trans_le hy'
  exact absurd h1 (not_le.mpr (max_lt h2 hlt))

omit [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- The constant coefficient of `toPoly a` is the `0`-coordinate of `a`. -/
private lemma toPoly_coeff_zero {n : ℕ} (hn : 0 < n) (a : Fin n → K) :
    (toPoly a).coeff 0 = a ⟨0, hn⟩ := by
  unfold toPoly
  exact shape_coeff a 0 hn

omit [IsUniformAddGroup K] in
/-- A system of representatives of the residue field inside `K`: integral elements, exactly one in
each coset of the open unit ball. -/
private lemma exists_rep : ∃ rep : 𝓀[K] → K, (∀ κ, rep κ ∈ 𝒪[K]) ∧
    (∀ z : 𝒪[K], valuation K ((z : K) - rep (IsLocalRing.residue 𝒪[K] z)) < 1) ∧
    (∀ κ κ' : 𝓀[K], valuation K (rep κ - rep κ') < 1 → κ = κ') := by
  have hsurj : Function.Surjective (IsLocalRing.residue 𝒪[K]) := IsLocalRing.residue_surjective
  set sec : 𝓀[K] → 𝒪[K] := Function.surjInv hsurj with hsec
  refine ⟨fun κ => (sec κ : K), fun κ => (sec κ).2, fun z => ?_, fun κ κ' h => ?_⟩
  · have : ((z - sec (IsLocalRing.residue 𝒪[K] z) : 𝒪[K]) : K) =
        (z : K) - (sec (IsLocalRing.residue 𝒪[K] z) : K) := by push_cast; ring
    rw [← this, valuation_lt_one_iff_residue_eq_zero, map_sub,
      Function.surjInv_eq hsurj, sub_self]
  · have hcoe : ((sec κ - sec κ' : 𝒪[K]) : K) = (sec κ : K) - (sec κ' : K) := by
      push_cast; ring
    rw [← hcoe, valuation_lt_one_iff_residue_eq_zero, map_sub,
      Function.surjInv_eq hsurj, Function.surjInv_eq hsurj, sub_eq_zero] at h
    exact h

/-- `muCoeff` is translation-invariant, being a Haar measure. -/
instance muCoeff_isAddLeftInvariant (n : ℕ)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] :
    (muCoeff K n).IsAddLeftInvariant :=
  inferInstanceAs (Measure.addHaarMeasure _).IsAddLeftInvariant

/-- `muCoeff` is positive on nonempty open sets, being a Haar measure on the locally compact group
`Fin n → K`. -/
instance muCoeff_isOpenPosMeasure (n : ℕ)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] :
    (muCoeff K n).IsOpenPosMeasure :=
  inferInstanceAs (Measure.addHaarMeasure _).IsOpenPosMeasure

omit [IsUniformAddGroup K] in
/-- The unit-ball box has volume `1 / q ^ n`: the integer box, of volume `1`, is the disjoint union
of its `q ^ n` translates by vectors of residue representatives. -/
private lemma measure_pi_ball (n : ℕ) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] :
    muCoeff K n (Set.univ.pi fun _ : Fin n => {x : K | valuation K x < 1}) =
      (q K : ℝ≥0∞)⁻¹ ^ n := by
  classical
  have := Fintype.ofFinite 𝓀[K]
  obtain ⟨rep, hrepO, hrep0, hrepinj⟩ := exists_rep (K := K)
  set B : Set K := {x : K | valuation K x < 1} with hB
  set W : Set (Fin n → K) := Set.univ.pi fun _ => B with hW
  set f : (Fin n → 𝓀[K]) → Set (Fin n → K) := fun κ => (fun i => rep (κ i)) +ᵥ W with hf
  have hWopen : IsOpen W := isOpen_set_pi Set.finite_univ fun i _ => isOpen_ballLT 1
  have hmem : ∀ (κ : Fin n → 𝓀[K]) (a : Fin n → K),
      a ∈ f κ ↔ ∀ i, valuation K (a i - rep (κ i)) < 1 := by
    intro κ a
    rw [hf, Set.mem_vadd_set_iff_neg_vadd_mem]
    simp [hW, hB, Set.mem_pi, vadd_eq_add, neg_add_eq_sub]
  have hdecomp : (Set.univ.pi fun _ : Fin n => (𝒪[K] : Set K)) = ⋃ κ, f κ := by
    ext a
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_iUnion]
    constructor
    · intro ha
      refine ⟨fun i => IsLocalRing.residue 𝒪[K] ⟨a i, ha i⟩, (hmem _ _).mpr fun i => ?_⟩
      exact hrep0 ⟨a i, ha i⟩
    · rintro ⟨κ, hκ⟩ i
      have h1 := (hmem κ a).mp hκ i
      have h2 : valuation K (rep (κ i)) ≤ 1 := ((valuation K).mem_integer_iff _).mp (hrepO _)
      have h3 : valuation K (a i) ≤
          max (valuation K (a i - rep (κ i))) (valuation K (rep (κ i))) := by
        simpa using (valuation K).map_add (a i - rep (κ i)) (rep (κ i))
      exact ((valuation K).mem_integer_iff _).mpr (h3.trans (max_le h1.le h2))
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro κ κ' hne
    rw [Function.onFun, Set.disjoint_left]
    intro a haκ haκ'
    apply hne
    funext i
    apply hrepinj
    have h1 := (hmem κ a).mp haκ i
    have h2 := (hmem κ' a).mp haκ' i
    have h3 : rep (κ i) - rep (κ' i) = (a i - rep (κ' i)) - (a i - rep (κ i)) := by ring
    rw [h3]
    exact ((valuation K).map_sub _ _).trans_lt (max_lt h2 h1)
  have hone : muCoeff K n (Set.univ.pi fun _ : Fin n => (𝒪[K] : Set K)) = 1 :=
    Measure.addHaarMeasure_self (K₀ := integerPositiveCompacts K n)
  have hcount : (1 : ℝ≥0∞) = (q K : ℝ≥0∞) ^ n * muCoeff K n W := by
    rw [← hone, hdecomp, measure_iUnion hdisj fun κ => (hWopen.vadd _).measurableSet]
    have hv : ∀ κ : Fin n → 𝓀[K], muCoeff K n (f κ) = muCoeff K n W := fun κ =>
      measure_vadd _ _ _
    simp_rw [hv]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi]
    congr 1
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast [q, Nat.card_eq_fintype_card]
    rfl
  have hq0 : ((q K : ℝ≥0∞)) ^ n ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (by have := one_lt_q K; omega))
  have hqtop : ((q K : ℝ≥0∞)) ^ n ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  calc muCoeff K n W
      = ((q K : ℝ≥0∞) ^ n)⁻¹ * ((q K : ℝ≥0∞) ^ n * muCoeff K n W) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 hqtop, one_mul]
    _ = ((q K : ℝ≥0∞) ^ n)⁻¹ * 1 := by rw [← hcount]
    _ = (q K : ℝ≥0∞)⁻¹ ^ n := by rw [mul_one, ← ENNReal.inv_pow]

omit [IsUniformAddGroup K] in
/-- Shrinking the `0`-coordinate of the unit-ball box one valuation level divides the volume by `q`:
the box is the disjoint union of `q` translates of the shrunk box, indexed by residues via a
uniformizer. -/
private lemma measure_pi_ballTwo (n : ℕ) (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    {ϖ : K} (hϖ0 : ϖ ≠ 0) (hϖ1 : valuation K ϖ < 1)
    (hmax : ∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K ϖ) :
    muCoeff K n (Set.univ.pi fun i : Fin n =>
        if i = ⟨0, hn⟩ then {x : K | valuation K x < valuation K ϖ}
        else {x : K | valuation K x < 1}) =
      (q K : ℝ≥0∞)⁻¹ ^ n * (q K : ℝ≥0∞)⁻¹ := by
  classical
  have := Fintype.ofFinite 𝓀[K]
  obtain ⟨rep, hrepO, hrep0, hrepinj⟩ := exists_rep (K := K)
  have hvne : valuation K ϖ ≠ 0 := (valuation K).ne_zero_iff.mpr hϖ0
  set idx : Fin n := ⟨0, hn⟩ with hidx
  set B : Set K := {x : K | valuation K x < 1} with hB
  set B₂ : Set K := {x : K | valuation K x < valuation K ϖ} with hB₂
  set W : Set (Fin n → K) := Set.univ.pi fun _ => B with hW
  set W₂ : Set (Fin n → K) := Set.univ.pi fun i => if i = idx then B₂ else B with hW₂
  set t : 𝓀[K] → Fin n → K := fun κ i => if i = idx then ϖ * rep κ else 0 with ht
  have hW₂open : IsOpen W₂ := isOpen_set_pi Set.finite_univ fun i _ => by
    split
    · exact isOpen_ballLT (Units.mk0 _ hvne)
    · exact isOpen_ballLT 1
  have hmemW : ∀ a : Fin n → K, a ∈ W ↔ ∀ i, valuation K (a i) < 1 := by
    intro a
    simp [hW, hB, Set.mem_pi]
  have hmem2 : ∀ (κ : 𝓀[K]) (a : Fin n → K), a ∈ (t κ +ᵥ W₂) ↔
      (valuation K (a idx - ϖ * rep κ) < valuation K ϖ ∧
        ∀ i, i ≠ idx → valuation K (a i) < 1) := by
    intro κ a
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_pi]
    constructor
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · have := h idx (Set.mem_univ _)
        simpa [ht, hB₂, vadd_eq_add, neg_add_eq_sub] using this
      · have := h i (Set.mem_univ _)
        simpa [ht, hB, vadd_eq_add, neg_add_eq_sub, hi] using this
    · rintro ⟨h0, hrest⟩ i _
      by_cases hi : i = idx
      · subst hi
        simpa [ht, hB₂, vadd_eq_add, neg_add_eq_sub] using h0
      · simpa [ht, hB, vadd_eq_add, neg_add_eq_sub, hi] using hrest i hi
  have hdecomp2 : W = ⋃ κ, (t κ +ᵥ W₂) := by
    ext a
    rw [hmemW a]
    simp only [Set.mem_iUnion]
    constructor
    · intro ha
      have hz : valuation K (a idx / ϖ) ≤ 1 := by
        rw [map_div₀]
        exact (div_le_one₀ (zero_lt_iff.mpr hvne)).mpr (hmax _ (ha idx))
      set z : 𝒪[K] := ⟨a idx / ϖ, ((valuation K).mem_integer_iff _).mpr hz⟩ with hz'
      refine ⟨IsLocalRing.residue 𝒪[K] z, (hmem2 _ _).mpr ⟨?_, fun i _ => ha i⟩⟩
      have h0 := hrep0 z
      have heq : a idx - ϖ * rep (IsLocalRing.residue 𝒪[K] z) =
          ϖ * ((z : K) - rep (IsLocalRing.residue 𝒪[K] z)) := by
        rw [hz']
        field_simp
      rw [heq, map_mul]
      calc valuation K ϖ * valuation K ((z : K) - rep (IsLocalRing.residue 𝒪[K] z))
          < valuation K ϖ * 1 := mul_lt_mul_of_pos_left h0 (zero_lt_iff.mpr hvne)
        _ = valuation K ϖ := mul_one _
    · rintro ⟨κ, hκ⟩
      obtain ⟨h0, hrest⟩ := (hmem2 κ a).mp hκ
      intro i
      by_cases hi : i = idx
      · subst hi
        have h2 : valuation K (ϖ * rep κ) < 1 := by
          rw [map_mul]
          exact (mul_le_of_le_one_right'
            (((valuation K).mem_integer_iff _).mp (hrepO κ))).trans_lt hϖ1
        have h3 : valuation K (a idx) ≤
            max (valuation K (a idx - ϖ * rep κ)) (valuation K (ϖ * rep κ)) := by
          simpa using (valuation K).map_add (a idx - ϖ * rep κ) (ϖ * rep κ)
        exact h3.trans_lt (max_lt (h0.trans hϖ1) h2)
      · exact hrest i hi
  have hdisj2 : Pairwise (Function.onFun Disjoint fun κ => t κ +ᵥ W₂) := by
    intro κ κ' hne
    rw [Function.onFun, Set.disjoint_left]
    intro a haκ haκ'
    apply hne
    apply hrepinj
    have h1 := ((hmem2 κ a).mp haκ).1
    have h2 := ((hmem2 κ' a).mp haκ').1
    have h3 : ϖ * (rep κ - rep κ') = (a idx - ϖ * rep κ') - (a idx - ϖ * rep κ) := by ring
    have h4 : valuation K (ϖ * (rep κ - rep κ')) < valuation K ϖ := by
      rw [h3]
      exact ((valuation K).map_sub _ _).trans_lt (max_lt h2 h1)
    rw [map_mul] at h4
    have h5 : valuation K ϖ * valuation K (rep κ - rep κ') < valuation K ϖ * 1 := by
      rwa [mul_one]
    exact lt_of_mul_lt_mul_left h5 zero_le
  have hcount2 : muCoeff K n W = (q K : ℝ≥0∞) * muCoeff K n W₂ := by
    rw [hdecomp2, measure_iUnion hdisj2 fun κ => (hW₂open.vadd _).measurableSet]
    have hv : ∀ κ : 𝓀[K], muCoeff K n (t κ +ᵥ W₂) = muCoeff K n W₂ := fun κ =>
      measure_vadd _ _ _
    simp_rw [hv]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    push_cast [q, Nat.card_eq_fintype_card]
    rfl
  have hq0 : ((q K : ℝ≥0∞)) ≠ 0 := Nat.cast_ne_zero.mpr (by have := one_lt_q K; omega)
  have hqtop : ((q K : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hball := measure_pi_ball (K := K) n
  rw [← hW] at hball
  calc muCoeff K n W₂
      = (q K : ℝ≥0∞)⁻¹ * ((q K : ℝ≥0∞) * muCoeff K n W₂) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 hqtop, one_mul]
    _ = (q K : ℝ≥0∞)⁻¹ * (q K : ℝ≥0∞)⁻¹ ^ n := by rw [← hcount2, hball]
    _ = (q K : ℝ≥0∞)⁻¹ ^ n * (q K : ℝ≥0∞)⁻¹ := mul_comm _ _

/-! ## The Eisenstein region: set identity, measurability, irreducibility, separability

These are the deterministic facts behind equation (3) and Lemma 1: the region is a difference of
boxes (hence measurable), every point has an irreducible polynomial by the Eisenstein criterion over
`𝒪[K]` and Gauss's lemma, and the inseparable points lie on the null hyperplane where the
`X ^ 1`-coefficient vanishes ([Serre 1978, eq. (3), p.1032; Lemma 1, p.1033][Serre1978]).
-/

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- The Eisenstein region is the unit-ball box minus the box with the constant coordinate shrunk one
valuation level. -/
private lemma eisensteinSet_eq_diff {n : ℕ} (hn : 0 < n) {ϖ : K} (hϖ1 : valuation K ϖ < 1)
    (hmax : ∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K ϖ) :
    eisensteinSet K n =
      (Set.univ.pi fun _ : Fin n => {x : K | valuation K x < 1}) \
        (Set.univ.pi fun i : Fin n =>
          if i = ⟨0, hn⟩ then {x : K | valuation K x < valuation K ϖ}
          else {x : K | valuation K x < 1}) := by
  classical
  have hmemW₂ : ∀ a : Fin n → K, (a ∈ Set.univ.pi fun i : Fin n =>
      if i = ⟨0, hn⟩ then {x : K | valuation K x < valuation K ϖ}
      else {x : K | valuation K x < 1}) ↔
      (valuation K (a ⟨0, hn⟩) < valuation K ϖ ∧
        ∀ i, i ≠ ⟨0, hn⟩ → valuation K (a i) < 1) := by
    intro a
    rw [Set.mem_pi]
    constructor
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · simpa using h ⟨0, hn⟩ (Set.mem_univ _)
      · simpa [hi] using h i (Set.mem_univ _)
    · rintro ⟨h0, hrest⟩ i _
      by_cases hi : i = ⟨0, hn⟩
      · subst hi; simpa using h0
      · simpa [hi] using hrest i hi
  ext a
  rw [Set.mem_sdiff, hmemW₂]
  constructor
  · rintro ⟨h1, h2⟩
    have h2' := h2 ϖ hϖ1
    rw [toPoly_coeff_zero hn a] at h2'
    refine ⟨?_, fun hc => absurd hc.1 (not_lt.mpr h2')⟩
    rw [Set.mem_pi]
    exact fun i _ => h1 i
  · rintro ⟨h1, h2⟩
    rw [Set.mem_pi] at h1
    have h1' : ∀ i, valuation K (a i) < 1 := fun i => h1 i (Set.mem_univ _)
    refine ⟨h1', fun y hy => ?_⟩
    rw [toPoly_coeff_zero hn a]
    have hnl : ¬ valuation K (a ⟨0, hn⟩) < valuation K ϖ := fun hc =>
      h2 ⟨hc, fun i _ => h1' i⟩
    exact (hmax y hy).trans (not_lt.mp hnl)

omit [IsUniformAddGroup K] in
/-- The Eisenstein region is measurable. -/
private lemma measurableSet_eisensteinSet {n : ℕ} (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] :
    MeasurableSet (eisensteinSet K n) := by
  obtain ⟨ϖ, hϖ0, hϖ1, hmax⟩ := exists_uniformizer (K := K)
  have hvne : valuation K ϖ ≠ 0 := (valuation K).ne_zero_iff.mpr hϖ0
  rw [eisensteinSet_eq_diff hn hϖ1 hmax]
  refine MeasurableSet.diff
    (isOpen_set_pi Set.finite_univ fun i _ => isOpen_ballLT 1).measurableSet
    (isOpen_set_pi Set.finite_univ fun i _ => ?_).measurableSet
  split
  · exact isOpen_ballLT (Units.mk0 _ hvne)
  · exact isOpen_ballLT 1

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- Eisenstein coefficient vectors are integral. -/
private lemma eisensteinSet_subset_pi {n : ℕ} :
    eisensteinSet K n ⊆ Set.univ.pi fun _ : Fin n => (𝒪[K] : Set K) := by
  rintro a ⟨h1, -⟩
  rw [Set.mem_pi]
  exact fun i _ => ((valuation K).mem_integer_iff _).mpr (h1 i).le

omit [IsUniformAddGroup K] in
/-- The Eisenstein region is open: coordinatewise, it is the open unit ball at every coordinate,
sharpened at the constant coordinate by the open co-ball condition `v ϖ ≤ v (a 0)`. -/
private lemma isOpen_eisensteinSet {n : ℕ} (hn : 0 < n) : IsOpen (eisensteinSet K n) := by
  classical
  obtain ⟨ϖ, hϖ0, hϖ1, hmax⟩ := exists_uniformizer (K := K)
  have hvne : valuation K ϖ ≠ 0 := (valuation K).ne_zero_iff.mpr hϖ0
  have hmem : ∀ a : Fin n → K, (a ∈ Set.univ.pi fun i : Fin n =>
      if i = ⟨0, hn⟩ then {x : K | valuation K x < 1 ∧ valuation K ϖ ≤ valuation K x}
      else {x : K | valuation K x < 1}) ↔
      ((valuation K (a ⟨0, hn⟩) < 1 ∧ valuation K ϖ ≤ valuation K (a ⟨0, hn⟩)) ∧
        ∀ i, i ≠ ⟨0, hn⟩ → valuation K (a i) < 1) := by
    intro a
    rw [Set.mem_pi]
    constructor
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · simpa using h ⟨0, hn⟩ (Set.mem_univ _)
      · simpa [hi] using h i (Set.mem_univ _)
    · rintro ⟨h0, hrest⟩ i _
      by_cases hi : i = ⟨0, hn⟩
      · subst hi; simpa using h0
      · simpa [hi] using hrest i hi
  have hE : eisensteinSet K n = Set.univ.pi fun i : Fin n =>
      if i = ⟨0, hn⟩ then {x : K | valuation K x < 1 ∧ valuation K ϖ ≤ valuation K x}
      else {x : K | valuation K x < 1} := by
    ext a
    rw [hmem a]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := h2 ϖ hϖ1
      rw [toPoly_coeff_zero hn a] at h3
      exact ⟨⟨h1 _, h3⟩, fun i _ => h1 i⟩
    · rintro ⟨⟨h01, h02⟩, hrest⟩
      refine ⟨fun i => ?_, fun y hy => ?_⟩
      · by_cases hi : i = ⟨0, hn⟩
        · subst hi; exact h01
        · exact hrest i hi
      · rw [toPoly_coeff_zero hn a]
        exact (hmax y hy).trans h02
  rw [hE]
  refine isOpen_set_pi Set.finite_univ fun i _ => ?_
  split
  · exact (isOpen_ballLT 1).inter (isOpen_ballGE (Units.mk0 _ hvne))
  · exact isOpen_ballLT 1

omit [IsUniformAddGroup K] in
/-- The `K`-coefficient vector of a monic Eisenstein polynomial of degree `n` over `𝒪[K]` lies in
the Eisenstein region: the lower coefficients lie in the maximal ideal, and the constant one is a
uniformizer times a unit. -/
private lemma coeff_mem_eisensteinSet {n : ℕ} (hn : 0 < n) {f : Polynomial 𝒪[K]} {π : 𝒪[K]}
    (hπ : Irreducible π) (hdeg : f.natDegree = n)
    (hei : f.IsEisensteinAt (Submodule.span 𝒪[K] {π})) :
    (fun i : Fin n => (f.map (algebraMap 𝒪[K] K)).coeff i) ∈ eisensteinSet K n := by
  -- the lower coefficients lie in the open unit ball
  have hvlt : ∀ k : ℕ, k < n → valuation K ((f.coeff k : 𝒪[K]) : K) < 1 := by
    intro k hk
    have h1 := hei.mem (show k < f.natDegree by rw [hdeg]; exact hk)
    rw [Ideal.submodule_span_eq, ← hπ.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h1
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp h1
  -- the constant coefficient is `π` times a unit, so its valuation is exactly `v (π)`
  have h0m : f.coeff 0 ∈ Ideal.span {π} := by
    have h1 := hei.mem (show 0 < f.natDegree by rw [hdeg]; exact hn)
    rwa [Ideal.submodule_span_eq] at h1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp h0m
  have hbu : IsUnit b := by
    by_contra hbu
    apply hei.notMem
    rw [Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    have hbm : b ∈ IsLocalRing.maximalIdeal 𝒪[K] :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hbu)
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hbm
    obtain ⟨c, hc⟩ := hbm
    exact ⟨c, by rw [hb, hc]; ring⟩
  have hv0 : valuation K (algebraMap 𝒪[K] K (f.coeff 0)) = valuation K (π : K) := by
    have hbv : valuation K (b : K) = 1 := by
      have hble : valuation K (b : K) ≤ 1 := ((valuation K).mem_integer_iff _).mp b.2
      have hbnl : ¬valuation K (b : K) < 1 := fun hlt =>
        Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hlt hbu
      exact le_antisymm hble (not_lt.mp hbnl)
    have h4 : ((f.coeff 0 : 𝒪[K]) : K) = (π : K) * (b : K) := by
      rw [hb]; push_cast; ring
    rw [show algebraMap 𝒪[K] K (f.coeff 0) = ((f.coeff 0 : 𝒪[K]) : K) from rfl, h4, map_mul,
      hbv, mul_one]
  refine ⟨fun i => ?_, fun y hy => ?_⟩
  · change valuation K ((f.map (algebraMap 𝒪[K] K)).coeff i) < 1
    rw [Polynomial.coeff_map]
    exact hvlt i i.isLt
  · rw [toPoly_coeff_zero hn]
    change valuation K y ≤ valuation K ((f.map (algebraMap 𝒪[K] K)).coeff 0)
    rw [Polynomial.coeff_map, hv0]
    exact valuation_le_of_lt_one hπ hy

omit [IsUniformAddGroup K] in
/-- On the Eisenstein region, `toPoly a` is irreducible over `K`: its integral model is Eisenstein
at the maximal ideal of `𝒪[K]`, hence irreducible there, and Gauss's lemma transfers irreducibility
to the fraction field `K`. -/
private lemma irreducible_toPoly {n : ℕ} (hn : 0 < n) {a : Fin n → K}
    (ha : a ∈ eisensteinSet K n) : Irreducible (toPoly a) := by
  obtain ⟨h1, h2⟩ := ha
  have hmem : ∀ i, a i ∈ 𝒪[K] := fun i => ((valuation K).mem_integer_iff _).mpr (h1 i).le
  set g : Polynomial 𝒪[K] :=
    Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (⟨a i, hmem i⟩ : 𝒪[K]) * Polynomial.X ^ (i : ℕ)
    with hg
  have hgmonic : g.Monic := shape_monic _
  have hgdeg : g.natDegree = n := shape_natDegree _
  have hmap : g.map (algebraMap 𝒪[K] K) = toPoly a := by
    unfold toPoly
    rw [hg, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    rfl
  -- the integral model is Eisenstein at the maximal ideal
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖlt : valuation K (ϖ₀ : K) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hϖ₀.not_isUnit
  have hEis : g.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hgmonic.leadingCoeff]
      exact fun hmem1 =>
        (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem1)) isUnit_one
    · intro k hk
      rw [hgdeg] at hk
      rw [hg, shape_coeff _ k hk]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr
        (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr (h1 ⟨k, hk⟩)))
    · intro hc
      rw [hg, shape_coeff _ 0 hn] at hc
      -- membership in `𝓂²` bounds the valuation by `v (ϖ₀)²`
      rw [hϖ₀.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hc
      obtain ⟨z, hz⟩ := hc
      have hvle : valuation K (a ⟨0, hn⟩) ≤ valuation K (ϖ₀ : K) ^ 2 := by
        have h3 := congrArg (fun w : 𝒪[K] => (w : K)) hz
        push_cast at h3
        rw [h3, map_mul, map_pow]
        exact mul_le_of_le_one_right' (((valuation K).mem_integer_iff _).mp z.2)
      -- but the Eisenstein condition forces `v (ϖ₀) ≤ v (a 0)`, a contradiction
      have hlb : valuation K (ϖ₀ : K) ≤ valuation K (a ⟨0, hn⟩) := by
        have := h2 (ϖ₀ : K) hϖlt
        rwa [toPoly_coeff_zero hn a] at this
      have hne0 : valuation K (ϖ₀ : K) ≠ 0 :=
        (valuation K).ne_zero_iff.mpr (by exact_mod_cast hϖ₀.ne_zero)
      have hsq : valuation K (ϖ₀ : K) ^ 2 < valuation K (ϖ₀ : K) := by
        calc valuation K (ϖ₀ : K) ^ 2
            = valuation K (ϖ₀ : K) * valuation K (ϖ₀ : K) := sq _
          _ < valuation K (ϖ₀ : K) * 1 := mul_lt_mul_of_pos_left hϖlt (zero_lt_iff.mpr hne0)
          _ = valuation K (ϖ₀ : K) := mul_one _
      exact absurd (hlb.trans (hvle.trans hsq.le))
        (lt_irrefl _ (lt_of_le_of_lt (hlb.trans hvle) hsq)).elim
  have h𝒪irr : Irreducible g :=
    hEis.irreducible (Ideal.IsMaximal.isPrime inferInstance) hgmonic.isPrimitive
      (by rw [hgdeg]; exact hn)
  have : IsFractionRing 𝒪[K] K :=
    inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
  have := (hgmonic.irreducible_iff_irreducible_map_fraction_map (K := K)).mp h𝒪irr
  rwa [hmap] at this

omit [IsUniformAddGroup K] in
/-- For `2 ≤ n`, a point of the Eisenstein region whose `X ^ 1`-coefficient is nonzero has separable
polynomial: the polynomial is irreducible, and the constant coefficient of its derivative is that
`X ^ 1`-coefficient. -/
private lemma separable_toPoly {n : ℕ} (hn2 : 2 ≤ n) {a : Fin n → K}
    (ha : a ∈ eisensteinSet K n) (h1 : a ⟨1, by omega⟩ ≠ 0) : (toPoly a).Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero (irreducible_toPoly (by omega) ha)]
  intro hder
  apply h1
  have hc1 : (toPoly a).coeff 1 = a ⟨1, by omega⟩ := by
    unfold toPoly
    exact shape_coeff _ 1 (by omega)
  have hd0 : (Polynomial.derivative (toPoly a)).coeff 0 = a ⟨1, by omega⟩ := by
    rw [Polynomial.coeff_derivative, hc1]
    simp
  rw [hder, Polynomial.coeff_zero] at hd0
  exact hd0.symm

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- Powers of an element of valuation `< 1` have strictly decreasing valuations. -/
private lemma valuation_pow_lt_valuation_pow {ϖ : K} (hϖ0 : ϖ ≠ 0) (hϖ1 : valuation K ϖ < 1)
    {k l : ℕ} (hkl : k < l) : valuation K (ϖ ^ l) < valuation K (ϖ ^ k) := by
  have hne : valuation K ϖ ≠ 0 := (valuation K).ne_zero_iff.mpr hϖ0
  rw [map_pow, map_pow]
  have hlt1 : valuation K ϖ ^ (l - k) < 1 := pow_lt_one₀ zero_le hϖ1 (by omega)
  calc valuation K ϖ ^ l
      = valuation K ϖ ^ k * valuation K ϖ ^ (l - k) := by rw [← pow_add]; congr 1; omega
    _ < valuation K ϖ ^ k * 1 :=
        mul_lt_mul_of_pos_left hlt1 (zero_lt_iff.mpr (pow_ne_zero _ hne))
    _ = valuation K ϖ ^ k := mul_one _

/-- Inside the integer box, the hyperplane `a j = 0` is null: for every `m` the box contains `m`
disjoint translates of the slice, shifted by the powers `ϖ ^ 0` through `ϖ ^ (m - 1)` in the `j`-th
coordinate, so the slice's measure is below `1 / m` for every `m`. -/
private lemma measure_pi_inter_coord_eq_zero (n : ℕ)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] (j : Fin n) :
    muCoeff K n ((Set.univ.pi fun _ : Fin n => (𝒪[K] : Set K)) ∩ {a | a j = 0}) = 0 := by
  classical
  obtain ⟨ϖ, hϖ0, hϖ1, hmax⟩ := exists_uniformizer (K := K)
  set S : Set (Fin n → K) :=
    (Set.univ.pi fun _ : Fin n => (𝒪[K] : Set K)) ∩ {a | a j = 0} with hS
  have hSclosed : IsClosed S := by
    rw [hS]
    refine IsClosed.inter ?_ (isClosed_eq (continuous_apply j) continuous_const)
    -- the ball has to be phrased over `Valued.v.restrict` to meet `Valued.isClosed_closedBall`
    have hpi : (Set.univ.pi fun _ : Fin n => (𝒪[K] : Set K)) =
        Set.univ.pi fun _ : Fin n => {x : K | Valued.v.restrict x ≤ 1} := by
      ext b
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, SetLike.mem_coe,
        Valuation.mem_integer_iff, Valuation.restrict_le_one_iff, forall_const]
      exact Iff.rfl
    rw [hpi]
    exact isClosed_set_pi fun i _ => Valued.isClosed_closedBall K 1
  have key : ∀ m : ℕ, (m : ℝ≥0∞) * muCoeff K n S ≤ 1 := by
    intro m
    have hone : muCoeff K n (Set.univ.pi fun _ : Fin n => (𝒪[K] : Set K)) = 1 :=
      Measure.addHaarMeasure_self (K₀ := integerPositiveCompacts K n)
    set t : Fin m → Fin n → K := fun k i => if i = j then ϖ ^ (k : ℕ) else 0 with ht
    have htmem : ∀ (k : Fin m) (i : Fin n), t k i ∈ 𝒪[K] := by
      intro k i
      rw [ht]
      dsimp only
      split
      · exact pow_mem (((valuation K).mem_integer_iff _).mpr hϖ1.le) _
      · exact zero_mem _
    have hmem : ∀ (k : Fin m) (x : Fin n → K), x ∈ t k +ᵥ S ↔
        ((∀ i, x i - t k i ∈ 𝒪[K]) ∧ x j = ϖ ^ (k : ℕ)) := by
      intro k x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, hS]
      simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, forall_true_left,
        Set.mem_ofPred_eq, vadd_eq_add, neg_add_eq_sub, Pi.sub_apply]
      have htj : t k j = ϖ ^ (k : ℕ) := by rw [ht]; simp
      constructor
      · rintro ⟨hA, hB⟩
        rw [htj] at hB
        exact ⟨hA, sub_eq_zero.mp hB⟩
      · rintro ⟨hA, hB⟩
        exact ⟨hA, by rw [htj, hB, sub_self]⟩
    have hsub : (⋃ k, t k +ᵥ S) ⊆ Set.univ.pi fun _ : Fin n => (𝒪[K] : Set K) := by
      intro x hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hA, _⟩ := (hmem k x).mp hk
      rw [Set.mem_pi]
      intro i _
      have h2 := add_mem (hA i) (htmem k i)
      rwa [sub_add_cancel] at h2
    have hdisj : Pairwise (Function.onFun Disjoint fun k : Fin m => t k +ᵥ S) := by
      intro k l hkl
      rw [Function.onFun, Set.disjoint_left]
      intro x hxk hxl
      apply hkl
      have h1 := ((hmem k x).mp hxk).2
      have h2 := ((hmem l x).mp hxl).2
      have heq : ϖ ^ (k : ℕ) = ϖ ^ (l : ℕ) := by rw [← h1, ← h2]
      refine Fin.ext ?_
      by_contra hne'
      rcases Nat.lt_trichotomy (k : ℕ) (l : ℕ) with h | h | h
      · exact absurd (congrArg (valuation K) heq)
          (ne_of_gt (valuation_pow_lt_valuation_pow hϖ0 hϖ1 h))
      · exact hne' h
      · exact absurd (congrArg (valuation K) heq)
          (ne_of_lt (valuation_pow_lt_valuation_pow hϖ0 hϖ1 h))
    have hunion : muCoeff K n (⋃ k, t k +ᵥ S) = (m : ℝ≥0∞) * muCoeff K n S := by
      rw [measure_iUnion hdisj fun k => (hSclosed.vadd _).measurableSet]
      have hv : ∀ k : Fin m, muCoeff K n (t k +ᵥ S) = muCoeff K n S := fun k =>
        measure_vadd _ _ _
      simp_rw [hv]
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hunion, ← hone]
    exact measure_mono hsub
  by_contra hne0
  have hx1 : muCoeff K n S ≤ 1 := by simpa using key 1
  have hxtop : muCoeff K n S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ENNReal.inv_ne_top.mpr hne0)
  have hlt : (1 : ℝ≥0∞) < m * muCoeff K n S := by
    have h' := ENNReal.mul_lt_mul_right hne0 hxtop hm
    rwa [ENNReal.mul_inv_cancel hne0 hxtop, mul_comm] at h'
  exact absurd (key m) (not_le.mpr hlt)

omit [IsUniformAddGroup K] in
/-- On the Eisenstein region, the minimal polynomial over `𝒪[K]` of a root of `toPoly a` is the
integral model itself: monic, of degree `n`, and Eisenstein at any uniformizer. -/
private lemma minpoly_eq_of_root {n : ℕ} (hn : 0 < n) {a : Fin n → K}
    (ha : a ∈ eisensteinSet K n) {x : SeparableClosure K}
    (hx : Polynomial.aeval x (toPoly a) = 0) :
    ∃ π : 𝒪[K], Irreducible π ∧ IsIntegral 𝒪[K] x ∧
      (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}) := by
  obtain ⟨h1, h2⟩ := ha
  have hmem : ∀ i, a i ∈ 𝒪[K] := fun i => ((valuation K).mem_integer_iff _).mpr (h1 i).le
  set g : Polynomial 𝒪[K] :=
    Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (⟨a i, hmem i⟩ : 𝒪[K]) * Polynomial.X ^ (i : ℕ)
    with hg
  have hgmonic : g.Monic := shape_monic _
  have hgdeg : g.natDegree = n := shape_natDegree _
  have hmap : g.map (algebraMap 𝒪[K] K) = toPoly a := by
    unfold toPoly
    rw [hg, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    rfl
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖlt : valuation K (ϖ₀ : K) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hϖ₀.not_isUnit
  have hEis : g.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hgmonic.leadingCoeff]
      exact fun hmem1 =>
        (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem1)) isUnit_one
    · intro k hk
      rw [hgdeg] at hk
      rw [hg, shape_coeff _ k hk]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr
        (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr (h1 ⟨k, hk⟩)))
    · intro hc
      rw [hg, shape_coeff _ 0 hn] at hc
      -- membership in `𝓂²` bounds the valuation by `v (ϖ₀)²`
      rw [hϖ₀.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hc
      obtain ⟨z, hz⟩ := hc
      have hvle : valuation K (a ⟨0, hn⟩) ≤ valuation K (ϖ₀ : K) ^ 2 := by
        have h3 := congrArg (fun w : 𝒪[K] => (w : K)) hz
        push_cast at h3
        rw [h3, map_mul, map_pow]
        exact mul_le_of_le_one_right' (((valuation K).mem_integer_iff _).mp z.2)
      -- but the Eisenstein condition forces `v (ϖ₀) ≤ v (a 0)`, a contradiction
      have hlb : valuation K (ϖ₀ : K) ≤ valuation K (a ⟨0, hn⟩) := by
        have := h2 (ϖ₀ : K) hϖlt
        rwa [toPoly_coeff_zero hn a] at this
      have hne0 : valuation K (ϖ₀ : K) ≠ 0 :=
        (valuation K).ne_zero_iff.mpr (by exact_mod_cast hϖ₀.ne_zero)
      have hsq : valuation K (ϖ₀ : K) ^ 2 < valuation K (ϖ₀ : K) := by
        calc valuation K (ϖ₀ : K) ^ 2
            = valuation K (ϖ₀ : K) * valuation K (ϖ₀ : K) := sq _
          _ < valuation K (ϖ₀ : K) * 1 := mul_lt_mul_of_pos_left hϖlt (zero_lt_iff.mpr hne0)
          _ = valuation K (ϖ₀ : K) := mul_one _
      exact absurd (hlb.trans (hvle.trans hsq.le))
        (lt_irrefl _ (lt_of_le_of_lt (hlb.trans hvle) hsq)).elim
  have h𝒪irr : Irreducible g :=
    hEis.irreducible (Ideal.IsMaximal.isPrime inferInstance) hgmonic.isPrimitive
      (by rw [hgdeg]; exact hn)
  have haevg : Polynomial.aeval x g = 0 := by
    rw [← hmap, Polynomial.aeval_map_algebraMap] at hx
    exact hx
  have hint : IsIntegral 𝒪[K] x := ⟨g, hgmonic, haevg⟩
  have : IsFractionRing 𝒪[K] K :=
    inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
  have hdvdg : minpoly 𝒪[K] x ∣ g := minpoly.isIntegrallyClosed_dvd hint haevg
  have hmineq : minpoly 𝒪[K] x = g := by
    obtain ⟨c, hc⟩ := hdvdg
    rcases h𝒪irr.isUnit_or_isUnit hc with hu | hu
    · exact absurd hu (Polynomial.not_isUnit_of_natDegree_pos _ (minpoly.natDegree_pos hint))
    · refine Polynomial.eq_of_monic_of_associated (minpoly.monic hint) hgmonic ?_
      exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩
  refine ⟨ϖ₀, hϖ₀, hint, ?_⟩
  rw [hmineq, Ideal.submodule_span_eq, ← hϖ₀.maximalIdeal_eq]
  exact hEis

variable (K)

/-! ## Local constancy of the root count on the separable locus -/

/-- Local constancy of the root count at a separable point of the Eisenstein region: for every `L`
in `sigma K n`, all coefficient vectors near `a` have the same number of roots in `L` as `a` itself.
The quantitative content is `card_aroots_eq`—Newton lifting over the complete ring of integers of
`L`—whose modulus, the `T`-th power of `𝓂[K]`, this statement converts into the neighborhood of `a`
of coordinatewise radius the `T`-th power of the valuation of `π`. This is the shared analytic input
of `aemeasurable_rootCount`, `countable_sigma`, and `lintegral_rootCount`. -/
theorem rootCount_eventuallyEq (n : ℕ) (hn : 0 < n)
    (L : IntermediateField K (SeparableClosure K)) (hL : L ∈ sigma K n) {a : Fin n → K}
    (ha : a ∈ eisensteinSet K n) (hsep : (toPoly a).Separable) :
    ∀ᶠ b in nhds a, rootCount L b = rootCount L a := by
  classical
  obtain ⟨h1, -⟩ := ha
  have hmem : ∀ i, a i ∈ 𝒪[K] := fun i => ((valuation K).mem_integer_iff _).mpr (h1 i).le
  -- the integral model of `toPoly a`
  set f : Polynomial 𝒪[K] :=
    Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (⟨a i, hmem i⟩ : 𝒪[K]) * Polynomial.X ^ (i : ℕ)
    with hf
  have hfmonic : f.Monic := shape_monic _
  have hfdeg : f.natDegree = n := shape_natDegree _
  have hfmap : f.map (algebraMap 𝒪[K] K) = toPoly a := by
    unfold toPoly
    rw [hf, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    rfl
  have hfsep : (f.map (algebraMap 𝒪[K] K)).Separable := by rw [hfmap]; exact hsep
  obtain ⟨T, hT0, hTkey⟩ := card_aroots_eq n hn L hL hfmonic hfsep
  -- the ball radius `v(π)^T` around `a`
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hπ₀1 : valuation K (π₀ : K) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hπ₀.not_isUnit
  have hπ₀0 : (π₀ : K) ≠ 0 := by exact_mod_cast hπ₀.ne_zero
  have hγ0 : valuation K ((π₀ : K)) ^ T ≠ 0 :=
    pow_ne_zero _ ((valuation K).ne_zero_iff.mpr hπ₀0)
  set γ : (ValueGroupWithZero K)ˣ := Units.mk0 _ hγ0 with hγ
  have hnhds : {b : Fin n → K | ∀ i, valuation K (b i - a i) < (γ : ValueGroupWithZero K)} ∈
      nhds a := by
    have h2 : (Set.univ.pi fun i : Fin n =>
        {z : K | valuation K (z - a i) < (γ : ValueGroupWithZero K)}) ∈ nhds a := by
      refine set_pi_mem_nhds Set.finite_univ fun i _ => ?_
      exact ((IsValuativeTopology.hasBasis_nhds (a i)).mem_iff).mpr ⟨γ, trivial, fun z hz => hz⟩
    refine Filter.mem_of_superset h2 fun b hb i => ?_
    exact hb i (Set.mem_univ i)
  filter_upwards [hnhds] with b hb
  -- the coordinates of `b` are integral: they differ from those of `a` by less than `v(π)`
  have hγle : (γ : ValueGroupWithZero K) ≤ 1 := by
    rw [hγ]
    exact pow_le_one₀ zero_le hπ₀1.le
  have hbmem : ∀ i, b i ∈ 𝒪[K] := by
    intro i
    have h3 : valuation K (b i) ≤ max (valuation K (b i - a i)) (valuation K (a i)) := by
      have h4 : (b i - a i) + a i = b i := by ring
      simpa [h4] using (valuation K).map_add (b i - a i) (a i)
    exact ((valuation K).mem_integer_iff _).mpr
      (h3.trans (max_le ((hb i).le.trans hγle) (h1 i).le))
  -- the integral model of `toPoly b`
  set g : Polynomial 𝒪[K] :=
    Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (⟨b i, hbmem i⟩ : 𝒪[K]) * Polynomial.X ^ (i : ℕ)
    with hg
  have hgmonic : g.Monic := shape_monic _
  have hgdeg : g.natDegree = n := shape_natDegree _
  have hgmap : g.map (algebraMap 𝒪[K] K) = toPoly b := by
    unfold toPoly
    rw [hg, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    rfl
  -- the coefficientwise congruence modulo `𝓂[K] ^ T`
  have hclose : ∀ i, g.coeff i - f.coeff i ∈ 𝓂[K] ^ T := by
    intro i
    rcases Nat.lt_or_ge i n with hilt | hige
    · rw [hg, hf, shape_coeff _ i hilt, shape_coeff _ i hilt]
      rw [hπ₀.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      refine Valuation.Integers.dvd_of_le (Valuation.integer.integers (valuation K)) ?_
      have h5 : ((⟨b ⟨i, hilt⟩, hbmem ⟨i, hilt⟩⟩ - ⟨a ⟨i, hilt⟩, hmem ⟨i, hilt⟩⟩ : 𝒪[K]) : K) =
          b ⟨i, hilt⟩ - a ⟨i, hilt⟩ := by push_cast; ring
      calc valuation K (algebraMap 𝒪[K] K
          (⟨b ⟨i, hilt⟩, hbmem ⟨i, hilt⟩⟩ - ⟨a ⟨i, hilt⟩, hmem ⟨i, hilt⟩⟩))
          = valuation K (b ⟨i, hilt⟩ - a ⟨i, hilt⟩) := by
            rw [show algebraMap 𝒪[K] K (⟨b ⟨i, hilt⟩, hbmem ⟨i, hilt⟩⟩ -
              ⟨a ⟨i, hilt⟩, hmem ⟨i, hilt⟩⟩) = ((⟨b ⟨i, hilt⟩, hbmem ⟨i, hilt⟩⟩ -
              ⟨a ⟨i, hilt⟩, hmem ⟨i, hilt⟩⟩ : 𝒪[K]) : K) from rfl, h5]
        _ ≤ valuation K ((π₀ : K)) ^ T := (hb ⟨i, hilt⟩).le
        _ = valuation K (algebraMap 𝒪[K] K (π₀ ^ T)) := by rw [map_pow, map_pow]; rfl
    · have h6 : g.coeff i = f.coeff i := by
        rcases Nat.eq_or_lt_of_le hige with heq | hlt
        · rw [show g.coeff i = 1 from by rw [← heq, ← hgdeg]; exact hgmonic.coeff_natDegree,
            show f.coeff i = 1 from by rw [← heq, ← hfdeg]; exact hfmonic.coeff_natDegree]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hgdeg ▸ hlt),
            Polynomial.coeff_eq_zero_of_natDegree_lt (hfdeg ▸ hlt)]
      rw [h6, sub_self]
      exact zero_mem _
  -- conclude through the threshold theorem
  have h7 := hTkey g hgmonic hclose
  unfold rootCount
  rw [← hfmap, ← hgmap]
  exact h7

/-! ## The core lemmas -/

omit [IsUniformAddGroup K] in
/-- The Eisenstein region has volume `(1 / q ^ n) * (1 - 1 / q)`.
It is a difference of two boxes—the box of radius `π` minus the sub-box where the constant term lies
in `π ^ 2 * 𝒪[K]`—of indices `q ^ n` and `q ^ (n + 1)` in the integer box; translation invariance
and the coset count give the volumes `1 / q ^ n` and `1 / q ^ (n + 1)`
([Serre 1978, eq. (2), p.1032][Serre1978]). -/
theorem muCoeff_eisensteinSet (n : ℕ) (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] :
    muCoeff K n (eisensteinSet K n) = (q K : ℝ≥0∞)⁻¹ ^ n * (1 - (q K : ℝ≥0∞)⁻¹) := by
  classical
  obtain ⟨ϖ, hϖ0, hϖ1, hmax⟩ := exists_uniformizer (K := K)
  have hvne : valuation K ϖ ≠ 0 := (valuation K).ne_zero_iff.mpr hϖ0
  have hq0' : ((q K : ℝ≥0∞)) ≠ 0 := Nat.cast_ne_zero.mpr (by have := one_lt_q K; omega)
  have hW₂open : IsOpen (Set.univ.pi fun i : Fin n =>
      if i = ⟨0, hn⟩ then {x : K | valuation K x < valuation K ϖ}
      else {x : K | valuation K x < 1}) :=
    isOpen_set_pi Set.finite_univ fun i _ => by
      split
      · exact isOpen_ballLT (Units.mk0 _ hvne)
      · exact isOpen_ballLT 1
  have hmemW₂ : ∀ a : Fin n → K, (a ∈ Set.univ.pi fun i : Fin n =>
      if i = ⟨0, hn⟩ then {x : K | valuation K x < valuation K ϖ}
      else {x : K | valuation K x < 1}) ↔
      (valuation K (a ⟨0, hn⟩) < valuation K ϖ ∧
        ∀ i, i ≠ ⟨0, hn⟩ → valuation K (a i) < 1) := by
    intro a
    rw [Set.mem_pi]
    constructor
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · simpa using h ⟨0, hn⟩ (Set.mem_univ _)
      · simpa [hi] using h i (Set.mem_univ _)
    · rintro ⟨h0, hrest⟩ i _
      by_cases hi : i = ⟨0, hn⟩
      · subst hi; simpa using h0
      · simpa [hi] using hrest i hi
  have hsub : (Set.univ.pi fun i : Fin n =>
      if i = ⟨0, hn⟩ then {x : K | valuation K x < valuation K ϖ}
      else {x : K | valuation K x < 1}) ⊆
      Set.univ.pi fun _ : Fin n => {x : K | valuation K x < 1} := by
    intro a ha
    obtain ⟨h0, hrest⟩ := (hmemW₂ a).mp ha
    rw [Set.mem_pi]
    intro i _
    by_cases hi : i = ⟨0, hn⟩
    · subst hi; exact h0.trans hϖ1
    · exact hrest i hi
  have hE := eisensteinSet_eq_diff hn hϖ1 hmax
  have hfin : muCoeff K n (Set.univ.pi fun i : Fin n =>
      if i = ⟨0, hn⟩ then {x : K | valuation K x < valuation K ϖ}
      else {x : K | valuation K x < 1}) ≠ ⊤ := by
    rw [measure_pi_ballTwo n hn hϖ0 hϖ1 hmax]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hq0'))
      (ENNReal.inv_ne_top.mpr hq0')
  rw [hE, measure_sdiff hsub hW₂open.measurableSet.nullMeasurableSet hfin,
    measure_pi_ball n, measure_pi_ballTwo n hn hϖ0 hϖ1 hmax]
  refine ENNReal.sub_eq_of_eq_add (ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hq0')) (ENNReal.inv_ne_top.mpr hq0')) ?_
  have hle : (q K : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (by exact_mod_cast (one_lt_q K).le)
  rw [← mul_add, tsub_add_cancel_of_le hle, mul_one]

/-- Away from the measure-zero discriminant locus the root count is locally constant—Krasner's
lemma, or continuity of the roots—hence a.e. measurable on the Eisenstein region. The local
constancy is `rootCount_eventuallyEq`; it makes the root count continuous on the separable part of
the region, and for `2 ≤ n` the inseparable part sits on the null hyperplane `a 1 = 0`, so
restricting the measure there changes nothing ([Serre 1978, eq. (3), p.1032][Serre1978]). -/
theorem aemeasurable_rootCount (n : ℕ) (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (L : IntermediateField K (SeparableClosure K)) (hL : L ∈ sigma K n) :
    AEMeasurable (fun a => (rootCount L a : ℝ≥0∞))
      ((muCoeff K n).restrict (eisensteinSet K n)) := by
  rcases Nat.lt_or_ge n 2 with hsmall | h2
  · -- `n = 1`: every Eisenstein polynomial is linear, hence separable, so the root count is
    -- locally constant on the whole region
    have h1 : n = 1 := by omega
    subst h1
    have hcont : ContinuousOn (fun a => (rootCount L a : ℝ≥0∞)) (eisensteinSet K 1) := by
      intro a haE
      have hsep : (toPoly a).Separable := by
        have htp : toPoly a = Polynomial.X + Polynomial.C (a 0) := by
          unfold toPoly
          rw [Fin.sum_univ_one]
          simp
        rw [htp]
        exact Polynomial.separable_X_add_C _
      have hev : (fun b => (rootCount L b : ℝ≥0∞)) =ᶠ[nhds a]
          fun _ => (rootCount L a : ℝ≥0∞) := by
        filter_upwards [rootCount_eventuallyEq K 1 hn L hL haE hsep] with b hb
        rw [hb]
      exact hev.continuousAt.continuousWithinAt
    exact hcont.aemeasurable (measurableSet_eisensteinSet hn)
  · -- `2 ≤ n`: off the hyperplane `a 1 = 0` the polynomial is separable and the root count locally
    -- constant, hence continuous there
    have h1n : 1 < n := by omega
    set V : Set (Fin n → K) := eisensteinSet K n ∩ {a | a ⟨1, h1n⟩ ≠ 0} with hV
    have hVsub : V ⊆ eisensteinSet K n := fun a ha => ha.1
    have hVmeas : MeasurableSet V := by
      rw [hV]
      exact (measurableSet_eisensteinSet hn).inter
        (isClosed_eq (continuous_apply (⟨1, h1n⟩ : Fin n)) continuous_const).measurableSet.compl
    have hcont : ContinuousOn (fun a => (rootCount L a : ℝ≥0∞)) V := by
      rintro a ⟨haE, ha1⟩
      have hev : (fun b => (rootCount L b : ℝ≥0∞)) =ᶠ[nhds a]
          fun _ => (rootCount L a : ℝ≥0∞) := by
        filter_upwards [rootCount_eventuallyEq K n hn L hL haE
          (separable_toPoly h2 haE ha1)] with b hb
        rw [hb]
      exact hev.continuousAt.continuousWithinAt
    -- the part of the region off `V` lies on the null hyperplane, so the region and `V` agree a.e.
    have hnull : muCoeff K n (eisensteinSet K n \ V) = 0 := by
      refine measure_mono_null ?_ (measure_pi_inter_coord_eq_zero n ⟨1, h1n⟩)
      rintro a ⟨haE, haV⟩
      refine ⟨eisensteinSet_subset_pi haE, ?_⟩
      by_contra h0
      exact haV ⟨haE, h0⟩
    have hcongr : eisensteinSet K n =ᵐ[muCoeff K n] V := by
      rw [ae_eq_set, Set.sdiff_eq_empty.mpr hVsub]
      exact ⟨hnull, measure_empty⟩
    rw [Measure.restrict_congr_set hcongr]
    exact hcont.aemeasurable hVmeas

/-! ## The change-of-variables core

The assembly of equations (5)–(13) on top of `UniformizerParam.lean` and `HaarScaling.lean`. Fix an
Eisenstein generator `ξ` of `integers L` (`exists_eisenstein_generator`) and a radius `ρ` with
`d L + n ≤ n * ρ`; the classes of `integers L` modulo `π ^ ρ` times `integers L` whose
representative is a uniformizer index a family of *boxes* in the coefficient space—the box of the
class of `η` being the coefficient vector of the monic annihilator of `η`, translated by the lattice
of multiplication by `π ^ ρ` times the derivative of that annihilator at `η`, in the chart at `η`.
By the local fiber count (`existsUnique_isRoot_iff`), a.e. polynomial of the Eisenstein region lies
in exactly `rootCount` many boxes; each box has volume `1 / q ^ (n * ρ + d L)`
(`measure_imageLattice_eq_inv_pow` through `det_leftMulMatrix` and `addVal_norm`); and the
corresponding cubes of the chart at `ξ` partition the set of uniformizers, of volume
`(1 / q) * (1 - 1 / q)` (equation (5), `measure_image_coord_uniformizers`)—so the number of classes
cancels between the two sums and the integral is `(1 / q ^ d L) * (1 / q) * (1 - 1 / q)`.
-/

section Assembly

variable {K}

open IsDiscreteValuationRing

/-! ### Generic helpers over a discrete valuation ring -/

section DVRHelpers

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- Elements of equal additive valuation are associated: the valuation inequality is divisibility,
in both directions. -/
private lemma associated_of_addVal_eq {a b : A} (h : addVal A a = addVal A b) :
    Associated a b :=
  associated_of_dvd_dvd (addVal_le_iff_dvd.mp h.le) (addVal_le_iff_dvd.mp h.ge)

/-- An element of additive valuation `k` is an associate of the `k`-th power of any uniformizer. -/
private lemma associated_pow_of_addVal {ϖ : A} (hϖ : Irreducible ϖ) {a : A} {k : ℕ}
    (h : addVal A a = (k : ℕ∞)) : Associated a (ϖ ^ k) :=
  associated_of_addVal_eq (by rw [h, hϖ.addVal_pow])

/-- An element of additive valuation `1` is a uniformizer. -/
private lemma irreducible_of_addVal_eq_one {a : A} (h : addVal A a = 1) : Irreducible a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  exact ((associated_of_addVal_eq (a := a) (b := ϖ)
    (by rw [h, addVal_uniformizer hϖ])).symm).irreducible hϖ

/-- A perturbation of valuation greater than one preserves a uniformizer's valuation. -/
private lemma addVal_eq_one_of_close {w v : A} (hw : Irreducible w)
    (hdist : (1 : ℕ∞) < addVal A (v - w)) : addVal A v = 1 := by
  have hlt : addVal A w < addVal A (v - w) := by
    rwa [addVal_uniformizer hw]
  rw [show v = w + (v - w) by rw [add_comm, sub_add_cancel],
    (addVal A).map_add_eq_of_lt_left hlt]
  exact addVal_uniformizer hw

/-- Any two uniformizers are associated. -/
private lemma associated_of_irreducible {a b : A} (ha : Irreducible a) (hb : Irreducible b) :
    Associated a b :=
  associated_of_addVal_eq (by rw [addVal_uniformizer ha, addVal_uniformizer hb])

end DVRHelpers

/-! ### Additive-valuation converters on `𝒪[K]` -/

omit [IsUniformAddGroup K] in
/-- Positivity of the additive valuation is the open unit ball of the multiplicative one. -/
private lemma one_le_addVal_iff_valuation_lt_one (z : 𝒪[K]) :
    1 ≤ addVal 𝒪[K] z ↔ valuation K (z : K) < 1 := by
  rw [Order.one_le_iff_ne_zero, Ne, addVal_eq_zero_iff,
    ← Valuation.Integer.not_isUnit_iff_valuation_lt_one]

omit [IsUniformAddGroup K] in
/-- An integral element of the exact multiplicative valuation of a uniformizer has additive
valuation `1`. -/
private lemma addVal_eq_one_of_valuation_eq {π : 𝒪[K]} (hπ : Irreducible π) {z : 𝒪[K]}
    (h : valuation K (z : K) = valuation K (π : K)) : addVal 𝒪[K] z = 1 := by
  have h1 : Associated z (π ^ 1) :=
    associated_pow_of_valuation hπ (by rw [h, pow_one])
  rw [pow_one] at h1
  rw [addVal_eq_of_associated h1, addVal_uniformizer hπ]

omit [IsUniformAddGroup K] in
/-- Conversely, an integral element of additive valuation `1` has the exact multiplicative valuation
of the uniformizer. -/
private lemma valuation_eq_of_addVal_eq_one {π : 𝒪[K]} (hπ : Irreducible π) {z : 𝒪[K]}
    (h : addVal 𝒪[K] z = 1) : valuation K (z : K) = valuation K (π : K) := by
  have h2 : Associated z π := by
    have h1 := associated_pow_of_addVal hπ (a := z) (k := 1) (by exact_mod_cast h)
    rwa [pow_one] at h1
  obtain ⟨u, hu⟩ := h2
  have hvu : valuation K ((u : 𝒪[K]) : K) = 1 :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mp u.isUnit
  have h3 := congrArg (fun w : 𝒪[K] => valuation K (w : K)) hu
  rw [show ((z * (u : 𝒪[K]) : 𝒪[K]) : K) = (z : K) * ((u : 𝒪[K]) : K) from by push_cast; ring,
    map_mul, hvu, mul_one] at h3
  exact h3

/-! ### The chart and the lattices at an arbitrary basis -/

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- The membership criterion of `toCoeff_equivFun_mem_imageLattice_iff`, at an
arbitrary `𝒪[K]`-basis of a discrete valuation ring. -/
private lemma toCoeff_mem_imageLattice_iff_addVal {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra 𝒪[K] A] {m : ℕ} (b : Module.Basis (Fin m) 𝒪[K] A)
    (z y : A) :
    toCoeff (b.equivFun y) ∈
        imageLattice (Algebra.leftMulMatrix b z) ↔
      addVal A z ≤ addVal A y := by
  rw [toCoeff_mem_imageLattice_iff, mem_range_leftMulMatrix_iff,
    addVal_le_iff_dvd]

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- The chart image of a ball of radius the valuation of `z` is the lattice of the multiplication by
`z`, at an arbitrary `𝒪[K]`-basis (the generalization of `image_coord_eq_imageLattice`). -/
private lemma image_toCoeff_equivFun_eq_imageLattice {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra 𝒪[K] A] {m : ℕ} (b : Module.Basis (Fin m) 𝒪[K] A)
    (z : A) :
    (fun w => toCoeff (b.equivFun w)) '' {y | addVal A z ≤ addVal A y} =
      imageLattice (Algebra.leftMulMatrix b z) := by
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (toCoeff_mem_imageLattice_iff_addVal b z y).mpr hy
  · intro ha
    rw [imageLattice_eq_image_range] at ha
    obtain ⟨c, hcmem, hc⟩ := ha
    refine ⟨b.equivFun.symm c, ?_, ?_⟩
    · refine (toCoeff_mem_imageLattice_iff_addVal b z _).mp ?_
      rw [LinearEquiv.apply_symm_apply]
      exact (toCoeff_mem_imageLattice_iff _ c).mpr hcmem
    · dsimp only
      rw [LinearEquiv.apply_symm_apply, hc]

/-! ### Small `ℕ∞` arithmetic helpers -/

/-- `addVal` is insensitive to negation. -/
private lemma addVal_neg'' {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (z : A) : addVal A (-z) = addVal A z :=
  addVal_eq_of_associated ⟨-1, by simp⟩

private lemma two_le_of_one_lt {v : ℕ∞} (h : 1 < v) : 2 ≤ v := by
  rcases eq_or_ne v ⊤ with rfl | hv
  · exact le_top
  · lift v to ℕ using hv
    exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast h)

/-- From `n ≤ n v + k` with `k < n`, the valuation `v` is positive. -/
private lemma one_le_of_le_mul_add {n k : ℕ} (hk : k < n) {v : ℕ∞}
    (h : (n : ℕ∞) ≤ (n : ℕ∞) * v + (k : ℕ∞)) : 1 ≤ v := by
  rcases eq_or_ne v ⊤ with rfl | hv
  · exact le_top
  · lift v to ℕ using hv with a
    rw [show (n : ℕ∞) * (a : ℕ∞) + (k : ℕ∞) = ((n * a + k : ℕ) : ℕ∞) from by push_cast; ring,
      Nat.cast_le] at h
    rcases Nat.eq_zero_or_pos a with rfl | h1
    · omega
    · exact_mod_cast h1

/-- From `n ρ + d ≤ n v + k` with `k < n ≤ d + 1`, the valuation `v` is at least `ρ`. -/
private lemma le_of_mul_add_le {n ρ dd k : ℕ} (hn : 0 < n) (hk : k < n) (hkd : n - 1 ≤ dd)
    {v : ℕ∞} (h : ((n * ρ + dd : ℕ) : ℕ∞) ≤ (n : ℕ∞) * v + (k : ℕ∞)) : (ρ : ℕ∞) ≤ v := by
  rcases eq_or_ne v ⊤ with rfl | hv
  · exact le_top
  · lift v to ℕ using hv with a
    rw [show (n : ℕ∞) * (a : ℕ∞) + (k : ℕ∞) = ((n * a + k : ℕ) : ℕ∞) from by push_cast; ring,
      Nat.cast_le] at h
    have h3 : k ≤ dd := by omega
    have h4 : n * ρ + dd ≤ n * a + dd := h.trans (by omega)
    exact_mod_cast Nat.le_of_mul_le_mul_left (by omega) hn

/-! ### The integral model of a coefficient vector -/

/-- The integral model of the monic polynomial `toPoly a` of an integral coefficient vector. -/
private noncomputable def intModel {n : ℕ} (a : Fin n → K) (ha : ∀ i, a i ∈ 𝒪[K]) :
    Polynomial 𝒪[K] :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (⟨a i, ha i⟩ : 𝒪[K]) * Polynomial.X ^ (i : ℕ)

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
private lemma intModel_monic {n : ℕ} (a : Fin n → K) (ha : ∀ i, a i ∈ 𝒪[K]) :
    (intModel a ha).Monic := by
  unfold intModel
  exact shape_monic _

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
private lemma intModel_natDegree {n : ℕ} (a : Fin n → K) (ha : ∀ i, a i ∈ 𝒪[K]) :
    (intModel a ha).natDegree = n := by
  unfold intModel
  exact shape_natDegree _

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
private lemma intModel_coeff {n : ℕ} (a : Fin n → K) (ha : ∀ i, a i ∈ 𝒪[K]) (i : Fin n) :
    (intModel a ha).coeff (i : ℕ) = ⟨a i, ha i⟩ := by
  unfold intModel
  rw [shape_coeff _ (i : ℕ) i.isLt]

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
private lemma intModel_map {n : ℕ} (a : Fin n → K) (ha : ∀ i, a i ∈ 𝒪[K]) :
    (intModel a ha).map (algebraMap 𝒪[K] K) = toPoly a := by
  unfold intModel toPoly
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  rfl

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
private lemma integral_of_root_toPoly (L : IntermediateField K (SeparableClosure K)) {n : ℕ}
    (a : Fin n → K) (ha : ∀ i, a i ∈ 𝒪[K]) (y : ↥L)
    (hy : Polynomial.aeval y (toPoly a) = 0) : y ∈ integers L := by
  have h5 : Polynomial.aeval y (intModel a ha) = 0 := by
    rw [← Polynomial.aeval_map_algebraMap K, intModel_map a ha]
    exact hy
  exact ⟨intModel a ha, intModel_monic a ha, by rwa [Polynomial.aeval_def] at h5⟩

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
private lemma intModel_root_iff (L : IntermediateField K (SeparableClosure K)) {n : ℕ}
    (a : Fin n → K) (ha : ∀ i, a i ∈ 𝒪[K]) (w : ↥(integers L)) :
    Polynomial.eval w ((intModel a ha).map (algebraMap 𝒪[K] ↥(integers L))) = 0 ↔
      Polynomial.aeval (w : ↥L) (toPoly a) = 0 := by
  have hval_aeval : ((Polynomial.aeval w (intModel a ha) : ↥(integers L)) : ↥L) =
      Polynomial.aeval (w : ↥L) (toPoly a) := by
    rw [← intModel_map a ha, Polynomial.aeval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply (Subalgebra.val _) w (intModel a ha)).symm
  rw [Polynomial.eval_map, ← Polynomial.aeval_def, ← hval_aeval]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.val_injective (by rw [h]; rfl)⟩

/-! ### The annihilator package at an arbitrary uniformizer of `integers L`

The cubes decomposing the set of uniformizers are centered at arbitrary uniformizers `η` of
`integers L`, each carrying its own chart (the coordinates in the powers of `η`,
`powersBasisIntegers`) and its own monic annihilator; the definitions below bundle the two, with the
monogenic basis `basisOfEisenstein` as the junk value on non-uniformizers so that families indexed
by residue classes stay total.
-/

section UniformizerPackage

variable {π : 𝒪[K]} {x : SeparableClosure K}

open scoped Classical in
/-- The chart's basis at `η`: the powers of `η` when `η` is a uniformizer
(`powersBasisIntegers`), and the monogenic basis `basisOfEisenstein` otherwise—junk, so that box
families indexed by residue classes are total. -/
private noncomputable def basisAt (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    (η : ↥(integers (IntermediateField.adjoin K {x}))) :
    Module.Basis (Fin (minpoly 𝒪[K] x).natDegree) 𝒪[K]
      ↥(integers (IntermediateField.adjoin K {x})) :=
  if hη : Irreducible η then powersBasisIntegers hπ hint hei hη
  else basisOfEisenstein hπ hint hei

omit [IsUniformAddGroup K] in
private lemma basisAt_apply (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η)
    (i : Fin (minpoly 𝒪[K] x).natDegree) :
    basisAt hπ hint hei η i = η ^ (i : ℕ) := by
  unfold basisAt
  rw [dite_eq_left hη]
  exact powersBasisIntegers_apply hπ hint hei hη i

/-- The monic degree-`n` annihilator of `η`, read off the chart at `η`—the polynomial whose
coefficient vector centers the box of `η`'s class. -/
private noncomputable def annihAt (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    (η : ↥(integers (IntermediateField.adjoin K {x}))) : Polynomial 𝒪[K] :=
  annih (R := 𝒪[K]) (A := ↥(integers (IntermediateField.adjoin K {x})))
    (n := (minpoly 𝒪[K] x).natDegree) (basisAt hπ hint hei η) η

omit [IsUniformAddGroup K] in
private lemma annihAt_monic (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    (η : ↥(integers (IntermediateField.adjoin K {x}))) : (annihAt hπ hint hei η).Monic :=
  annih_monic _ _

omit [IsUniformAddGroup K] in
private lemma annihAt_natDegree (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    (η : ↥(integers (IntermediateField.adjoin K {x}))) :
    (annihAt hπ hint hei η).natDegree = (minpoly 𝒪[K] x).natDegree :=
  annih_natDegree _ _

omit [IsUniformAddGroup K] in
private lemma eval_map_annihAt (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η) :
    Polynomial.eval η ((annihAt hπ hint hei η).map
      (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))) = 0 :=
  eval_map_annih _ (basisAt_apply hπ hint hei hη)

omit [IsUniformAddGroup K] in
/-- The interleaving associating `π` with `η ^ n` at an arbitrary uniformizer `η`: any two
uniformizers of `integers L` are associated, so the Eisenstein generator's interleaving
transfers. -/
private lemma associated_algebraMap_pow_at (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η) :
    Associated (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})) π)
      (η ^ (minpoly 𝒪[K] x).natDegree) :=
  (associated_algebraMap_pow hπ hint hei).trans
    (Associated.pow_pow (associated_of_irreducible (irreducible_integralGen hπ hint hei) hη))

omit [IsUniformAddGroup K] in
/-- The valuation of `π ^ ρ` upstairs is `n * ρ`—the totally ramified normalization. -/
private lemma addVal_algebraMap_pow (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))] (ρ : ℕ) :
    addVal ↥(integers (IntermediateField.adjoin K {x}))
        (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})) (π ^ ρ)) =
      (((minpoly 𝒪[K] x).natDegree * ρ : ℕ) : ℕ∞) := by
  rw [addVal_algebraMap hπ (irreducible_integralGen hπ hint hei)
    (minpoly.natDegree_pos hint) (associated_algebraMap_pow hπ hint hei),
    hπ.addVal_pow]
  exact (Nat.cast_mul _ _).symm

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- `ξ` is a root of the base change of its own minimal polynomial (the public re-derivation of
`aeval_integralGen`, which is private there). -/
private lemma eval_map_minpoly_integralGen (hint : IsIntegral 𝒪[K] x) :
    Polynomial.eval (integralGen hint) ((minpoly 𝒪[K] x).map
      (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))) = 0 := by
  have hgen : Polynomial.aeval (IntermediateField.AdjoinSimple.gen K x) (minpoly 𝒪[K] x) = 0 := by
    apply (algebraMap ↥(IntermediateField.adjoin K {x}) (SeparableClosure K)).injective
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply,
      IntermediateField.AdjoinSimple.algebraMap_gen]
    exact minpoly.aeval 𝒪[K] x
  have hξaeval : Polynomial.aeval (integralGen hint) (minpoly 𝒪[K] x) = 0 := by
    apply Subtype.val_injective
    have h4 : ((Polynomial.aeval (integralGen hint) (minpoly 𝒪[K] x) :
        ↥(integers (IntermediateField.adjoin K {x}))) : ↥(IntermediateField.adjoin K {x})) =
        Polynomial.aeval (IntermediateField.AdjoinSimple.gen K x) (minpoly 𝒪[K] x) :=
      (Polynomial.aeval_algHom_apply (Subalgebra.val _) (integralGen hint)
        (minpoly 𝒪[K] x)).symm
    rw [show ((0 : ↥(integers (IntermediateField.adjoin K {x}))) :
      ↥(IntermediateField.adjoin K {x})) = 0 from rfl, h4, hgen]
  rwa [Polynomial.aeval_def, ← Polynomial.eval_map] at hξaeval

omit [IsUniformAddGroup K] in
/-- The fiber exponent at every uniformizer: the derivative of the annihilator of
`η` at `η` has valuation `d L`, for *every* uniformizer `η`—at the Eisenstein generator this is
`addVal_derivative_eq_d`, and the invariance `addVal_eval_derivative_eq_of_powersBasis` transports
it; the degenerate degree-`1` case, where the invariance lemma's positivity hypothesis fails, has
both sides equal to the valuation of `1`. -/
private lemma addVal_derivative_annihAt (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η) :
    addVal ↥(integers (IntermediateField.adjoin K {x}))
        (Polynomial.eval η (Polynomial.derivative ((annihAt hπ hint hei η).map
          (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))))) =
      (d (IntermediateField.adjoin K {x}) : ℕ∞) := by
  have hN : 0 < (minpoly 𝒪[K] x).natDegree := minpoly.natDegree_pos hint
  have hξder : addVal ↥(integers (IntermediateField.adjoin K {x}))
      (Polynomial.eval (integralGen hint) (Polynomial.derivative ((minpoly 𝒪[K] x).map
        (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))))) =
      (d (IntermediateField.adjoin K {x}) : ℕ∞) := by
    have h1 := addVal_derivative_eq_d hπ hint hei
    rwa [Polynomial.aeval_def, ← Polynomial.eval_map, ← Polynomial.derivative_map] at h1
  rcases Nat.lt_or_ge (minpoly 𝒪[K] x).natDegree 2 with hN1 | hN2
  · -- degree `1`: both derivatives evaluate to `1`
    have hone : (minpoly 𝒪[K] x).natDegree = 1 := by omega
    have hlin : ∀ P : Polynomial 𝒪[K], P.Monic → P.natDegree = 1 →
        ∀ w : ↥(integers (IntermediateField.adjoin K {x})),
        Polynomial.eval w (Polynomial.derivative (P.map
          (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))))) = 1 := by
      intro P hPm hPdeg w
      have hQdeg : (P.map (algebraMap 𝒪[K]
          ↥(integers (IntermediateField.adjoin K {x})))).natDegree = 1 := by
        rw [hPm.natDegree_map, hPdeg]
      have hQ := Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hQdeg)
      have hc1 : (P.map (algebraMap 𝒪[K]
          ↥(integers (IntermediateField.adjoin K {x})))).coeff 1 = 1 := by
        rw [← hQdeg]
        exact (hPm.map _).coeff_natDegree
      rw [hc1, map_one, one_mul] at hQ
      rw [hQ, Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
        add_zero, Polynomial.eval_one]
    have hdd : (d (IntermediateField.adjoin K {x}) : ℕ∞) = 0 := by
      rw [← hξder, hlin _ (minpoly.monic hint) hone _, addVal_one]
    rw [hlin _ (annihAt_monic hπ hint hei η)
      (by rw [annihAt_natDegree hπ hint hei η]; exact hone) η, addVal_one, hdd]
  · -- degree `≥ 2`: the invariance of the derivative order
    have hd1 : 1 ≤ d (IntermediateField.adjoin K {x}) := by
      have := sub_one_le_d_adjoin K hπ hint hei
      omega
    rw [← hξder]
    exact addVal_eval_derivative_eq_of_powersBasis hN
      (basisOfEisenstein hπ hint hei) (basisAt hπ hint hei η)
      (basisOfEisenstein_apply hπ hint hei) (basisAt_apply hπ hint hei hη)
      (minpoly.monic hint) rfl (eval_map_minpoly_integralGen hint)
      (annihAt_monic hπ hint hei η) (annihAt_natDegree hπ hint hei η)
      (eval_map_annihAt hπ hint hei hη)
      (by rw [hξder]; exact_mod_cast hd1)

omit [IsUniformAddGroup K] in
/-- The annihilator in the `X^n + ∑ C (c i) X^i` shape, on the negated coordinates of `η^n`. -/
private lemma annihAt_eq_shape (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    (η : ↥(integers (IntermediateField.adjoin K {x}))) :
    annihAt hπ hint hei η = Polynomial.X ^ (minpoly 𝒪[K] x).natDegree +
      ∑ i : Fin (minpoly 𝒪[K] x).natDegree,
        Polynomial.C (-((basisAt hπ hint hei η).repr
          (η ^ (minpoly 𝒪[K] x).natDegree) i)) * Polynomial.X ^ (i : ℕ) := by
  unfold annihAt annih expand
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_neg]
  exact (neg_mul _ _).symm

omit [IsUniformAddGroup K] in
/-- Below the top degree, the coefficients of the annihilator are the negated coordinates of
`η ^ n`. -/
private lemma annihAt_coeff (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    (η : ↥(integers (IntermediateField.adjoin K {x}))) {k : ℕ}
    (hk : k < (minpoly 𝒪[K] x).natDegree) :
    (annihAt hπ hint hei η).coeff k =
      -((basisAt hπ hint hei η).repr (η ^ (minpoly 𝒪[K] x).natDegree) ⟨k, hk⟩) := by
  rw [annihAt_eq_shape hπ hint hei η]
  exact shape_coeff _ k hk

omit [IsUniformAddGroup K] in
/-- The coordinates of `η ^ n` all lie in the maximal ideal: the annihilator is Eisenstein below the
top degree. -/
private lemma one_le_addVal_repr_pow (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η)
    (i : Fin (minpoly 𝒪[K] x).natDegree) :
    1 ≤ addVal 𝒪[K] ((basisAt hπ hint hei η).repr
      (η ^ (minpoly 𝒪[K] x).natDegree) i) := by
  have hN : 0 < (minpoly 𝒪[K] x).natDegree := minpoly.natDegree_pos hint
  have hpow : (((minpoly 𝒪[K] x).natDegree : ℕ) : ℕ∞) ≤
      addVal ↥(integers (IntermediateField.adjoin K {x}))
        (η ^ (minpoly 𝒪[K] x).natDegree) := by
    rw [hη.addVal_pow]
  have hco := (le_addVal_iff hπ hη hN
    (associated_algebraMap_pow_at hπ hint hei hη) (basisAt hπ hint hei η)
    (basisAt_apply hπ hint hei hη) (η ^ (minpoly 𝒪[K] x).natDegree) _).mp hpow i
  exact one_le_of_le_mul_add i.isLt hco

omit [IsUniformAddGroup K] in
/-- The `0`-th coordinate of `η ^ n` has valuation exactly `1`: the annihilator's constant
coefficient is a uniformizer of `𝒪[K]` times a unit. -/
private lemma addVal_repr_pow_zero (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η) :
    addVal 𝒪[K] ((basisAt hπ hint hei η).repr (η ^ (minpoly 𝒪[K] x).natDegree)
      ⟨0, minpoly.natDegree_pos hint⟩) = 1 := by
  have hN : 0 < (minpoly 𝒪[K] x).natDegree := minpoly.natDegree_pos hint
  refine le_antisymm ?_ (one_le_addVal_repr_pow hπ hint hei hη _)
  by_contra hgt
  push Not at hgt
  have h2 := two_le_of_one_lt hgt
  have hup : (((minpoly 𝒪[K] x).natDegree + 1 : ℕ) : ℕ∞) ≤
      addVal ↥(integers (IntermediateField.adjoin K {x}))
        (η ^ (minpoly 𝒪[K] x).natDegree) := by
    refine (le_addVal_iff hπ hη hN
      (associated_algebraMap_pow_at hπ hint hei hη) (basisAt hπ hint hei η)
      (basisAt_apply hπ hint hei hη) _ _).mpr fun i => ?_
    rcases eq_or_ne (i : ℕ) 0 with hi0 | hi0
    · have hieq : i = ⟨0, hN⟩ := Fin.ext hi0
      subst hieq
      calc (((minpoly 𝒪[K] x).natDegree + 1 : ℕ) : ℕ∞)
          ≤ (((minpoly 𝒪[K] x).natDegree * 2 : ℕ) : ℕ∞) := by
            rw [Nat.cast_le]
            omega
        _ = ((minpoly 𝒪[K] x).natDegree : ℕ∞) * 2 := by push_cast; ring
        _ ≤ ((minpoly 𝒪[K] x).natDegree : ℕ∞) *
              addVal 𝒪[K] ((basisAt hπ hint hei η).repr
                (η ^ (minpoly 𝒪[K] x).natDegree) ⟨0, hN⟩) := mul_le_mul_right h2 _
        _ ≤ _ := by
            rw [show (((⟨0, hN⟩ : Fin (minpoly 𝒪[K] x).natDegree) : ℕ) : ℕ∞) = 0 from rfl,
              add_zero]
    · have hi1 : 1 ≤ (i : ℕ) := by omega
      calc (((minpoly 𝒪[K] x).natDegree + 1 : ℕ) : ℕ∞)
          = ((minpoly 𝒪[K] x).natDegree : ℕ∞) + 1 := by push_cast; ring
        _ ≤ ((minpoly 𝒪[K] x).natDegree : ℕ∞) *
              addVal 𝒪[K] ((basisAt hπ hint hei η).repr
                (η ^ (minpoly 𝒪[K] x).natDegree) i) + ((i : ℕ) : ℕ∞) := by
            refine add_le_add ?_ (by exact_mod_cast hi1)
            calc ((minpoly 𝒪[K] x).natDegree : ℕ∞)
                = ((minpoly 𝒪[K] x).natDegree : ℕ∞) * 1 := (mul_one _).symm
              _ ≤ _ := mul_le_mul_right (one_le_addVal_repr_pow hπ hint hei hη i) _
  rw [hη.addVal_pow, Nat.cast_le] at hup
  omega

omit [IsUniformAddGroup K] in
/-- The annihilator's coefficients below the top degree lie in the maximal ideal. -/
private lemma one_le_addVal_annihAt_coeff (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η) {k : ℕ}
    (hk : k < (minpoly 𝒪[K] x).natDegree) :
    1 ≤ addVal 𝒪[K] ((annihAt hπ hint hei η).coeff k) := by
  rw [annihAt_coeff hπ hint hei η hk, addVal_neg'']
  exact one_le_addVal_repr_pow hπ hint hei hη _

omit [IsUniformAddGroup K] in
/-- The annihilator's constant coefficient has valuation exactly `1`. -/
private lemma addVal_annihAt_coeff_zero (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η) :
    addVal 𝒪[K] ((annihAt hπ hint hei η).coeff 0) = 1 := by
  rw [annihAt_coeff hπ hint hei η (minpoly.natDegree_pos hint), addVal_neg'']
  exact addVal_repr_pow_zero hπ hint hei hη

/-! ### The box of a uniformizer -/

/-- The box of `η`: the coefficient vector of the annihilator of `η`, translated by the
lattice of multiplication by `π ^ ρ` times the derivative of that annihilator at `η`, in the chart
at `η`. By `mem_boxAt_iff` below, its membership condition on an integral vector `a` is the fiber
criterion of `existsUnique_isRoot_iff`: the value of `toPoly a` at `η` has valuation at least
`n * ρ + d L`. -/
private noncomputable def boxAt (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    (ρ : ℕ) (η : ↥(integers (IntermediateField.adjoin K {x}))) :
    Set (Fin (minpoly 𝒪[K] x).natDegree → K) :=
  (fun i : Fin (minpoly 𝒪[K] x).natDegree =>
      (((annihAt hπ hint hei η).coeff i : 𝒪[K]) : K)) +ᵥ
    imageLattice (Algebra.leftMulMatrix (basisAt hπ hint hei η)
      (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})) (π ^ ρ) *
        Polynomial.eval η (Polynomial.derivative ((annihAt hπ hint hei η).map
          (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))))))

omit [IsUniformAddGroup K] in
/-- The multiplier of the box lattice—`π ^ ρ` times the derivative of the annihilator at `η`—has
valuation `n * ρ + d L`. -/
private lemma addVal_boxAt_multiplier (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η) (ρ : ℕ) :
    addVal ↥(integers (IntermediateField.adjoin K {x}))
        (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})) (π ^ ρ) *
          Polynomial.eval η (Polynomial.derivative ((annihAt hπ hint hei η).map
            (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))))) =
      (((minpoly 𝒪[K] x).natDegree * ρ + d (IntermediateField.adjoin K {x}) : ℕ) : ℕ∞) := by
  rw [addVal_mul, addVal_algebraMap_pow hπ hint hei ρ, addVal_derivative_annihAt hπ hint hei hη]
  exact (Nat.cast_add _ _).symm

omit [IsUniformAddGroup K] in
/-- The membership criterion of the box, from the affinity in the coefficients of evaluation at `η`:
an integral vector lies in the box of `η` exactly when its polynomial takes at `η` a value of
valuation at least `n * ρ + d L`. -/
private lemma mem_boxAt_iff (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η) (ρ : ℕ)
    {a : Fin (minpoly 𝒪[K] x).natDegree → K} (ha : ∀ i, a i ∈ 𝒪[K]) :
    a ∈ boxAt hπ hint hei ρ η ↔
      (((minpoly 𝒪[K] x).natDegree * ρ + d (IntermediateField.adjoin K {x}) : ℕ) : ℕ∞) ≤
        addVal ↥(integers (IntermediateField.adjoin K {x}))
          (Polynomial.eval η ((intModel a ha).map
            (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))))) := by
  have hN : 0 < (minpoly 𝒪[K] x).natDegree := minpoly.natDegree_pos hint
  have hDdeg : ((intModel a ha) - annihAt hπ hint hei η).natDegree <
      (minpoly 𝒪[K] x).natDegree :=
    natDegree_sub_lt hN (intModel_monic a ha) (intModel_natDegree a ha)
      (annihAt_monic hπ hint hei η) (annihAt_natDegree hπ hint hei η)
  have hchart : a - (fun i : Fin (minpoly 𝒪[K] x).natDegree =>
      (((annihAt hπ hint hei η).coeff i : 𝒪[K]) : K)) =
      toCoeff ((basisAt hπ hint hei η).equivFun
        (Polynomial.eval η (((intModel a ha) - annihAt hπ hint hei η).map
          (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))))) := by
    rw [eval_map_eq_sum hDdeg, equivFun_sum _ (basisAt_apply hπ hint hei hη)]
    funext i
    rw [Pi.sub_apply, toCoeff_apply, Polynomial.coeff_sub, intModel_coeff a ha i]
    push_cast
    ring
  unfold boxAt
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, hchart,
    toCoeff_mem_imageLattice_iff_addVal, addVal_boxAt_multiplier hπ hint hei hη ρ]
  have hsplit : (intModel a ha).map
      (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))) =
      (annihAt hπ hint hei η).map
        (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))) +
      ((intModel a ha) - annihAt hπ hint hei η).map
        (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))) := by
    rw [← Polynomial.map_add]
    congr 1
    ring
  rw [hsplit, Polynomial.eval_add, eval_map_annihAt hπ hint hei hη, zero_add]

omit [IsUniformAddGroup K] in
/-- The boxes stay inside the Eisenstein region for `2 ≤ ρ`: the perturbation's coordinates are
`ρ`-deep by orthogonality (with `n - 1 ≤ d L` absorbing the coordinate offsets), so they cannot move
the annihilator's coefficients out of the maximal ideal nor disturb the exact valuation of its
constant term. -/
private lemma boxAt_subset_eisensteinSet (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η)
    {ρ : ℕ} (hρ2 : 2 ≤ ρ) :
    boxAt hπ hint hei ρ η ⊆ eisensteinSet K (minpoly 𝒪[K] x).natDegree := by
  have hN : 0 < (minpoly 𝒪[K] x).natDegree := minpoly.natDegree_pos hint
  intro a haB
  unfold boxAt at haB
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub,
    imageLattice_eq_image_range] at haB
  obtain ⟨cvec, hcmem, hcv⟩ := haB
  -- the perturbation, as an element of `A_L`, and its coordinate depth
  have hwval : (((minpoly 𝒪[K] x).natDegree * ρ + d (IntermediateField.adjoin K {x}) : ℕ) : ℕ∞) ≤
      addVal ↥(integers (IntermediateField.adjoin K {x}))
        ((basisAt hπ hint hei η).equivFun.symm cvec) := by
    have h1 : toCoeff ((basisAt hπ hint hei η).equivFun
        ((basisAt hπ hint hei η).equivFun.symm cvec)) ∈
        imageLattice (Algebra.leftMulMatrix (basisAt hπ hint hei η)
          (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})) (π ^ ρ) *
            Polynomial.eval η (Polynomial.derivative ((annihAt hπ hint hei η).map
              (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))))))) := by
      rw [LinearEquiv.apply_symm_apply]
      exact (toCoeff_mem_imageLattice_iff _ cvec).mpr hcmem
    have h2 := (toCoeff_mem_imageLattice_iff_addVal _ _ _).mp h1
    rw [addVal_boxAt_multiplier hπ hint hei hη ρ] at h2
    exact h2
  have hrepr_eq : ((basisAt hπ hint hei η).repr
      ((basisAt hπ hint hei η).equivFun.symm cvec) : Fin (minpoly 𝒪[K] x).natDegree → 𝒪[K]) =
      cvec := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hcoord : ∀ i, (ρ : ℕ∞) ≤ addVal 𝒪[K] (cvec i) := by
    intro i
    have h3 := (le_addVal_iff hπ hη hN
      (associated_algebraMap_pow_at hπ hint hei hη) (basisAt hπ hint hei η)
      (basisAt_apply hπ hint hei hη) ((basisAt hπ hint hei η).equivFun.symm cvec) _).mp
      hwval i
    rw [show (basisAt hπ hint hei η).repr ((basisAt hπ hint hei η).equivFun.symm cvec) i =
      cvec i from congrFun hrepr_eq i] at h3
    exact le_of_mul_add_le hN i.isLt (sub_one_le_d_adjoin K hπ hint hei) h3
  -- the coordinates of `a` themselves
  have hai : ∀ i, a i =
      (((annihAt hπ hint hei η).coeff i + cvec i : 𝒪[K]) : K) := by
    intro i
    have h4 := congrFun hcv i
    rw [toCoeff_apply, Pi.sub_apply] at h4
    push_cast
    linear_combination -h4
  refine ⟨fun i => ?_, fun y hy => ?_⟩
  · -- every coordinate lies in the open unit ball
    rw [hai i, ← one_le_addVal_iff_valuation_lt_one]
    refine le_trans (le_min (one_le_addVal_annihAt_coeff hπ hint hei hη i.isLt) ?_) addVal_add
    exact le_trans (by exact_mod_cast Nat.one_le_of_lt hρ2) (hcoord i)
  · -- the constant coordinate has the exact valuation of `π`
    rw [toPoly_coeff_zero hN a, hai ⟨0, hN⟩]
    have hlt : addVal 𝒪[K] ((annihAt hπ hint hei η).coeff
        ((⟨0, hN⟩ : Fin (minpoly 𝒪[K] x).natDegree) : ℕ)) <
        addVal 𝒪[K] (cvec ⟨0, hN⟩) := by
      have h5 : addVal 𝒪[K] ((annihAt hπ hint hei η).coeff
          ((⟨0, hN⟩ : Fin (minpoly 𝒪[K] x).natDegree) : ℕ)) = 1 :=
        addVal_annihAt_coeff_zero hπ hint hei hη
      rw [h5]
      exact lt_of_lt_of_le (by exact_mod_cast hρ2) (hcoord ⟨0, hN⟩)
    have hval0 : addVal 𝒪[K] ((annihAt hπ hint hei η).coeff
        ((⟨0, hN⟩ : Fin (minpoly 𝒪[K] x).natDegree) : ℕ) + cvec ⟨0, hN⟩) = 1 := by
      rw [(addVal 𝒪[K]).map_add_eq_of_lt_left hlt]
      exact addVal_annihAt_coeff_zero hπ hint hei hη
    rw [valuation_eq_of_addVal_eq_one hπ hval0]
    exact valuation_le_of_lt_one hπ hy

/-- An Eisenstein relation forces its integral root to be a uniformizer. -/
private lemma irreducible_of_eisenstein_relation {R A : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra R A]
    {π : R} {ξ : A} {n : ℕ} (hπ : Irreducible π) (hξ : Irreducible ξ)
    (hN : 0 < n) (hass : Associated (algebraMap R A π) (ξ ^ n))
    (c : Fin n → R) (w : A) (hci : ∀ i, 1 ≤ addVal R (c i))
    (hc0 : addVal R (c ⟨0, hN⟩) = 1)
    (hsum : w ^ n = -∑ i : Fin n, algebraMap R A (c i) * w ^ (i : ℕ)) :
    Irreducible w := by
  -- step 1: the root is not a unit
  have hv1 : 1 ≤ addVal A w := by
    by_contra hv
    have hv0 : addVal A w = 0 := by
      rcases eq_or_ne (addVal A w) ⊤ with htop | hne
      · exact absurd (htop ▸ le_top) hv
      · lift addVal A w to ℕ using hne with v0 hv0'
        have h6 : ¬(1 ≤ v0) := fun h => hv (by exact_mod_cast h)
        norm_cast
        omega
    have hL : addVal A
        (w ^ n) = 0 := by
      rw [(addVal A).map_pow, hv0, smul_zero]
    have hR : 1 ≤ addVal A
        (w ^ n) := by
      rw [hsum, addVal_neg'']
      refine (addVal A).map_le_sum fun i _ => ?_
      rw [addVal_mul, addVal_algebraMap hπ hξ hN hass]
      refine le_trans ?_ le_self_add
      calc (1 : ℕ∞) = 1 * 1 := (one_mul 1).symm
        _ ≤ (n : ℕ∞) * addVal R (c i) :=
            mul_le_mul' (by exact_mod_cast hN) (hci i)
    rw [hL] at hR
    exact absurd hR (by norm_num)
  -- step 2: the sum has valuation exactly `n`
  have hterm0 : addVal A
      (algebraMap R A
        (c ⟨0, hN⟩) *
        w ^ ((⟨0, hN⟩ : Fin n) : ℕ)) =
      (n : ℕ∞) := by
    rw [show ((⟨0, hN⟩ : Fin n) : ℕ) = 0 from rfl, pow_zero, mul_one,
      addVal_algebraMap hπ hξ hN hass, hc0, mul_one]
  have hrest : ∀ i : Fin n, i ≠ ⟨0, hN⟩ →
      ((n + 1 : ℕ) : ℕ∞) ≤
        addVal A
          (algebraMap R A
            (c i) * w ^ (i : ℕ)) := by
    intro i hi
    have hi1 : 1 ≤ (i : ℕ) := by
      by_contra h
      exact hi (Fin.ext (show (i : ℕ) = 0 by omega))
    rw [addVal_mul, addVal_algebraMap hπ hξ hN hass]
    have hA : (n : ℕ∞) ≤
        (n : ℕ∞) * addVal R (c i) := by
      calc (n : ℕ∞)
          = (n : ℕ∞) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_right (hci i) _
    have hB : (1 : ℕ∞) ≤ addVal A (w ^ (i : ℕ)) := by
      rw [(addVal A).map_pow, nsmul_eq_mul]
      calc (1 : ℕ∞) = 1 * 1 := (one_mul 1).symm
        _ ≤ ((i : ℕ) : ℕ∞) * addVal A w :=
            mul_le_mul' (by exact_mod_cast hi1) hv1
    calc ((n + 1 : ℕ) : ℕ∞)
        = (n : ℕ∞) + 1 := by push_cast; ring
      _ ≤ _ := add_le_add hA hB
  have hlt : addVal A
      (algebraMap R A
        (c ⟨0, hN⟩) *
        w ^ ((⟨0, hN⟩ : Fin n) : ℕ)) <
      addVal A
        (∑ j ∈ Finset.univ.erase (⟨0, hN⟩ : Fin n),
          algebraMap R A
            (c j) * w ^ (j : ℕ)) := by
    rw [hterm0]
    refine lt_of_lt_of_le ?_
      ((addVal A).map_le_sum fun j hj =>
        hrest j (Finset.ne_of_mem_erase hj))
    exact_mod_cast Nat.lt_succ_self n
  have hsplit : addVal A
      (∑ i : Fin n,
        algebraMap R A
          (c i) * w ^ (i : ℕ)) =
      (n : ℕ∞) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hN⟩ : Fin n)),
      (addVal A).map_add_eq_of_lt_left hlt, hterm0]
  -- conclude: `n • v (w) = n`, so `v (w) = 1`
  have h5 := congrArg (addVal A) hsum
  rw [(addVal A).map_pow, nsmul_eq_mul,
    addVal_neg'', hsplit] at h5
  have hvne : addVal A w ≠ ⊤ := by
    intro htop
    rw [htop, ENat.mul_top (by exact_mod_cast hN.ne' :
      (n : ℕ∞) ≠ 0)] at h5
    exact ENat.natCast_ne_top _ h5.symm
  lift addVal A w to ℕ using hvne with v0 hv0'
  have h6 : n * v0 = n * 1 := by
    rw [mul_one]
    exact_mod_cast h5
  exact irreducible_of_addVal_eq_one (by
    rw [← hv0']
    exact_mod_cast Nat.eq_of_mul_eq_mul_left hN h6)

omit [IsUniformAddGroup K] in
/-- A root of an Eisenstein polynomial in `integers L` is a uniformizer: its valuation `v` satisfies
`n * v = n`, the value of the combination of the `c i * η ^ i` having valuation `n` with the `i = 0`
term strictly minimal once `1 ≤ v`—and `1 ≤ v` because every term of the sum is deep. -/
private lemma irreducible_of_isRoot (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {a : Fin (minpoly 𝒪[K] x).natDegree → K}
    (haE : a ∈ eisensteinSet K (minpoly 𝒪[K] x).natDegree) (ha : ∀ i, a i ∈ 𝒪[K])
    {w : ↥(integers (IntermediateField.adjoin K {x}))}
    (hw : Polynomial.eval w ((intModel a ha).map
      (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))) = 0) :
    Irreducible w := by
  obtain ⟨h1, h2⟩ := haE
  have hN : 0 < (minpoly 𝒪[K] x).natDegree := minpoly.natDegree_pos hint
  have hξ := irreducible_integralGen hπ hint hei
  have hass := associated_algebraMap_pow hπ hint hei
  have hπlt : valuation K (π : K) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hπ.not_isUnit
  -- the coefficients and their valuations
  have hci : ∀ i, 1 ≤ addVal 𝒪[K] ((⟨a i, ha i⟩ : 𝒪[K])) := fun i =>
    (one_le_addVal_iff_valuation_lt_one _).mpr (h1 i)
  have hc0 : addVal 𝒪[K] ((⟨a ⟨0, hN⟩, ha ⟨0, hN⟩⟩ : 𝒪[K])) = 1 := by
    refine addVal_eq_one_of_valuation_eq hπ ?_
    refine le_antisymm (valuation_le_of_lt_one hπ (h1 _)) ?_
    have h3 := h2 (π : K) hπlt
    rwa [toPoly_coeff_zero hN a] at h3
  -- the evaluated shape
  have hev : Polynomial.eval w ((intModel a ha).map
      (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))) =
      w ^ (minpoly 𝒪[K] x).natDegree + ∑ i : Fin (minpoly 𝒪[K] x).natDegree,
        algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))
          (⟨a i, ha i⟩ : 𝒪[K]) * w ^ (i : ℕ) := by
    unfold intModel
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hev] at hw
  have hsum : w ^ (minpoly 𝒪[K] x).natDegree =
      -∑ i : Fin (minpoly 𝒪[K] x).natDegree,
        algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))
          (⟨a i, ha i⟩ : 𝒪[K]) * w ^ (i : ℕ) := by
    linear_combination hw
  exact irreducible_of_eisenstein_relation (R := ↥𝒪[K])
    (A := ↥(integers (IntermediateField.adjoin K {x}))) hπ hξ hN hass
    (fun i => (⟨a i, ha i⟩ : 𝒪[K])) w hci hc0 hsum

end UniformizerPackage

/-! ### The volume of a box, and the a.e. separability -/

section BoxMeasure

variable {π : 𝒪[K]} {x : SeparableClosure K}

private lemma measurableSet_boxAt (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    [MeasurableSpace (Fin (minpoly 𝒪[K] x).natDegree → K)]
    [BorelSpace (Fin (minpoly 𝒪[K] x).natDegree → K)] (ρ : ℕ)
    (η : ↥(integers (IntermediateField.adjoin K {x}))) :
    MeasurableSet (boxAt hπ hint hei ρ η) := by
  unfold boxAt
  exact ((isCompact_imageLattice _).isClosed.vadd _).measurableSet

omit [IsUniformAddGroup K] in
/-- The multiplier of a root box has the expected norm order. -/
private lemma associated_norm_boxAt_multiplier (hπ : Irreducible π)
    (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η) (ρ : ℕ) :
    Associated
      (Algebra.norm 𝒪[K] (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))
        (π ^ ρ) * Polynomial.eval η (Polynomial.derivative ((annihAt hπ hint hei η).map
          (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))))))
      (π ^ ((minpoly 𝒪[K] x).natDegree * ρ + d (IntermediateField.adjoin K {x}))) := by
  exact associated_pow_of_addVal hπ
    ((addVal_norm hπ hint hei _).trans (addVal_boxAt_multiplier hπ hint hei hη ρ))

/-- The volume of a box is `1 / q ^ (n * ρ + d L)`: the box is a translate of the lattice of
multiplication by `π ^ ρ` times the derivative of the annihilator at `η`, whose determinant is the
norm (`det_leftMulMatrix`), whose `π`-adic order is the valuation upstairs (`addVal_norm`), which is
`n * ρ + d L` (`addVal_boxAt_multiplier`). -/
private lemma measure_boxAt (hπ : Irreducible π) (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    [MeasurableSpace (Fin (minpoly 𝒪[K] x).natDegree → K)]
    [BorelSpace (Fin (minpoly 𝒪[K] x).natDegree → K)]
    (μ : Measure (Fin (minpoly 𝒪[K] x).natDegree → K)) [μ.IsAddLeftInvariant]
    (hnorm : μ (integerBox K (minpoly 𝒪[K] x).natDegree) = 1)
    {η : ↥(integers (IntermediateField.adjoin K {x}))} (hη : Irreducible η) (ρ : ℕ) :
    μ (boxAt hπ hint hei ρ η) = (q K : ℝ≥0∞)⁻¹ ^
      ((minpoly 𝒪[K] x).natDegree * ρ + d (IntermediateField.adjoin K {x})) := by
  unfold boxAt
  rw [measure_vadd]
  exact measure_imageLattice_leftMul (A := ↥(integers (IntermediateField.adjoin K {x})))
    (basisAt hπ hint hei η) μ hnorm hπ _ (associated_norm_boxAt_multiplier hπ hint hei hη ρ)

end BoxMeasure

/-- Almost every point of the Eisenstein region is separable—region-membership and separability
bundled, extracted from the null-hyperplane argument of `tsum_rootCount`
([Serre 1978, eq. (3), p.1032][Serre1978]). -/
private lemma ae_separable (n : ℕ) (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] :
    ∀ᵐ a ∂((muCoeff K n).restrict (eisensteinSet K n)),
      a ∈ eisensteinSet K n ∧ (toPoly a).Separable := by
  rcases Nat.lt_or_ge n 2 with hsmall | h2
  · have h1 : n = 1 := by omega
    subst h1
    filter_upwards [ae_restrict_mem (measurableSet_eisensteinSet Nat.one_pos)] with a haE
    refine ⟨haE, ?_⟩
    have htp : toPoly a = Polynomial.X + Polynomial.C (a 0) := by
      unfold toPoly
      rw [Fin.sum_univ_one]
      simp
    rw [htp]
    exact Polynomial.separable_X_add_C _
  · have hnull : (muCoeff K n).restrict (eisensteinSet K n)
        {a : Fin n → K | a ⟨1, by omega⟩ = 0} = 0 := by
      rw [Measure.restrict_apply' (measurableSet_eisensteinSet hn)]
      refine measure_mono_null ?_ (measure_pi_inter_coord_eq_zero n ⟨1, by omega⟩)
      rintro a ⟨ha1, haE⟩
      exact ⟨eisensteinSet_subset_pi haE, ha1⟩
    have hae1 : ∀ᵐ a ∂((muCoeff K n).restrict (eisensteinSet K n)), a ⟨1, by omega⟩ ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    filter_upwards [ae_restrict_mem (measurableSet_eisensteinSet hn), hae1] with a haE ha1
    exact ⟨haE, separable_toPoly h2 haE ha1⟩

end Assembly

open IsDiscreteValuationRing in
/-- The uniformizer residue classes recover the Haar mass of all uniformizers. -/
private theorem uniformizer_classes_mass {π : 𝒪[K]} (hπ : Irreducible π) {x : SeparableClosure K}
    (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    [MeasurableSpace (Fin (minpoly 𝒪[K] x).natDegree → K)]
    [BorelSpace (Fin (minpoly 𝒪[K] x).natDegree → K)]
    (ρ : ℕ) (I : Ideal ↥(integers (IntermediateField.adjoin K {x})))
    (rep : (↥(integers (IntermediateField.adjoin K {x})) ⧸ I) →
      ↥(integers (IntermediateField.adjoin K {x})))
    (T : Finset (↥(integers (IntermediateField.adjoin K {x})) ⧸ I))
    (hclass : ∀ (t : ↥(integers (IntermediateField.adjoin K {x})) ⧸ I)
      (w : ↥(integers (IntermediateField.adjoin K {x}))),
      Ideal.Quotient.mk I w = t ↔
        (((minpoly 𝒪[K] x).natDegree * ρ : ℕ) : ℕ∞) ≤
          addVal ↥(integers (IntermediateField.adjoin K {x})) (w - rep t))
    (hTmem : ∀ t, t ∈ T ↔ Irreducible (rep t))
    (hrepirr : ∀ w : ↥(integers (IntermediateField.adjoin K {x})), Irreducible w →
      Irreducible (rep (Ideal.Quotient.mk I w)))
    (hval_of_class : ∀ w : ↥(integers (IntermediateField.adjoin K {x})),
      Irreducible (rep (Ideal.Quotient.mk I w)) →
      addVal ↥(integers (IntermediateField.adjoin K {x})) w = 1)
    (hone : muCoeff K (minpoly 𝒪[K] x).natDegree
      (integerBox K (minpoly 𝒪[K] x).natDegree) = 1) :
    (T.card : ℝ≥0∞) * (q K : ℝ≥0∞)⁻¹ ^ ((minpoly 𝒪[K] x).natDegree * ρ) =
      (q K : ℝ≥0∞)⁻¹ * (1 - (q K : ℝ≥0∞)⁻¹) := by
  classical
  have hcsub : ∀ u v : ↥(integers (IntermediateField.adjoin K {x})),
      coord hπ hint hei (u - v) =
        coord hπ hint hei u - coord hπ hint hei v := by
    intro u v
    unfold coord
    rw [map_sub, map_sub]
  have hcadd : ∀ u v : ↥(integers (IntermediateField.adjoin K {x})),
      coord hπ hint hei (u + v) =
        coord hπ hint hei u + coord hπ hint hei v := by
    intro u v
    unfold coord
    rw [map_add, map_add]
  have himg : ∀ t : ↥(integers (IntermediateField.adjoin K {x})) ⧸ I,
      coord hπ hint hei '' {w | Ideal.Quotient.mk I w = t} =
        coord hπ hint hei (rep t) +ᵥ
          coord hπ hint hei ''
            {w | addVal ↥(integers (IntermediateField.adjoin K {x}))
                (integralGen hint ^ ((minpoly 𝒪[K] x).natDegree * ρ)) ≤
              addVal ↥(integers (IntermediateField.adjoin K {x})) w} := by
    intro t
    ext b
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Set.mem_ofPred_eq] at hw
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
      refine ⟨w - rep t, ?_, hcsub w (rep t)⟩
      rw [Set.mem_ofPred_eq, (irreducible_integralGen hπ hint hei).addVal_pow]
      exact (hclass t w).mp hw
    · intro hb
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hb
      obtain ⟨u, hu, hub⟩ := hb
      rw [Set.mem_ofPred_eq, (irreducible_integralGen hπ hint hei).addVal_pow] at hu
      refine ⟨rep t + u, ?_, ?_⟩
      · rw [Set.mem_ofPred_eq]
        refine (hclass t (rep t + u)).mpr ?_
        simpa using hu
      · rw [hcadd (rep t) u, hub]
        ring
  have hcubemeas : ∀ t, MeasurableSet (coord hπ hint hei ''
      {w | Ideal.Quotient.mk I w = t}) := by
    intro t
    rw [himg t, image_coord_eq_imageLattice hπ hint hei]
    exact ((isCompact_imageLattice _).isClosed.vadd _).measurableSet
  have hcubevol : ∀ t, muCoeff K (minpoly 𝒪[K] x).natDegree
      (coord hπ hint hei '' {w | Ideal.Quotient.mk I w = t}) =
      (q K : ℝ≥0∞)⁻¹ ^ ((minpoly 𝒪[K] x).natDegree * ρ) := by
    intro t
    rw [himg t, measure_vadd]
    exact measure_image_coord_ball hπ hint hei _ hone
      ((minpoly 𝒪[K] x).natDegree * ρ)
  -- the cubes of the uniformizer classes partition the image of `Π_L`
  have hsetpart : {w : ↥(integers (IntermediateField.adjoin K {x})) |
      addVal ↥(integers (IntermediateField.adjoin K {x})) w = 1} =
      ⋃ t ∈ T, {w | Ideal.Quotient.mk I w = t} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hw
      exact ⟨Ideal.Quotient.mk I w,
        (hTmem _).mpr (hrepirr w (irreducible_of_addVal_eq_one hw)), rfl⟩
    · rintro ⟨t, htT, ht⟩
      refine hval_of_class w ?_
      rw [ht]
      exact (hTmem t).mp htT
  have hdisj : (↑T : Set (↥(integers (IntermediateField.adjoin K {x})) ⧸ I)).PairwiseDisjoint
      (fun t => coord hπ hint hei '' {w | Ideal.Quotient.mk I w = t}) := by
    intro t₁ _ t₂ _ hne
    refine Set.disjoint_image_of_injective (coord_injective hπ hint hei) ?_
    rw [Set.disjoint_left]
    intro w hw₁ hw₂
    rw [Set.mem_ofPred_eq] at hw₁ hw₂
    exact hne (hw₁.symm.trans hw₂)
  have h9 := measure_image_coord_uniformizers hπ hint hei
    (muCoeff K (minpoly 𝒪[K] x).natDegree) hone
  rw [hsetpart, Set.image_iUnion₂,
    measure_biUnion_finset hdisj (fun t _ => hcubemeas t)] at h9
  rw [Finset.sum_congr rfl (fun t _ => hcubevol t), Finset.sum_const, nsmul_eq_mul] at h9
  exact h9

open IsDiscreteValuationRing in
omit [IsUniformAddGroup K] in
/-- On the separable Eisenstein locus, roots are counted by their uniformizer residue boxes. -/
private theorem rootCount_eq_sum_indicator {π : 𝒪[K]} (hπ : Irreducible π) {x : SeparableClosure K}
    (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}))
    [IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x}))]
    (hAC : IsAdicComplete
      (IsLocalRing.maximalIdeal ↥(integers (IntermediateField.adjoin K {x})))
      ↥(integers (IntermediateField.adjoin K {x})))
    (ρ : ℕ) (I : Ideal ↥(integers (IntermediateField.adjoin K {x})))
    (rep : (↥(integers (IntermediateField.adjoin K {x})) ⧸ I) →
      ↥(integers (IntermediateField.adjoin K {x})))
    (T : Finset (↥(integers (IntermediateField.adjoin K {x})) ⧸ I))
    (hclass : ∀ (t : ↥(integers (IntermediateField.adjoin K {x})) ⧸ I)
      (w : ↥(integers (IntermediateField.adjoin K {x}))),
      Ideal.Quotient.mk I w = t ↔
        (((minpoly 𝒪[K] x).natDegree * ρ : ℕ) : ℕ∞) ≤
          addVal ↥(integers (IntermediateField.adjoin K {x})) (w - rep t))
    (hTmem : ∀ t, t ∈ T ↔ Irreducible (rep t))
    (hrepirr : ∀ w : ↥(integers (IntermediateField.adjoin K {x})), Irreducible w →
      Irreducible (rep (Ideal.Quotient.mk I w)))
    (hρbound : d (IntermediateField.adjoin K {x}) + (minpoly 𝒪[K] x).natDegree ≤
      (minpoly 𝒪[K] x).natDegree * ρ) :
    ∀ a ∈ eisensteinSet K (minpoly 𝒪[K] x).natDegree, (toPoly a).Separable →
      (rootCount (IntermediateField.adjoin K {x}) a : ℝ≥0∞) =
        ∑ t ∈ T, (boxAt hπ hint hei ρ (rep t)).indicator 1 a := by
  classical
  have hn := minpoly.natDegree_pos hint
  intro a haE hsep
  have ha : ∀ i, a i ∈ 𝒪[K] := fun i => ((valuation K).mem_integer_iff _).mpr (haE.1 i).le
  have hne : toPoly a ≠ 0 := by
    rw [← intModel_map a ha]
    exact ((intModel_monic a ha).map _).ne_zero
  have hnodup : ((toPoly a).aroots ↥(IntermediateField.adjoin K {x})).Nodup :=
    Polynomial.nodup_roots hsep.map
  have hint_y := integral_of_root_toPoly (IntermediateField.adjoin K {x}) a ha
  have hroot_iff := intModel_root_iff (IntermediateField.adjoin K {x}) a ha
  have hind : ∑ t ∈ T, (boxAt hπ hint hei ρ (rep t)).indicator
      (1 : (Fin (minpoly 𝒪[K] x).natDegree → K) → ℝ≥0∞) a =
      ((T.filter fun t => a ∈ boxAt hπ hint hei ρ (rep t)).card : ℝ≥0∞) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hb : a ∈ boxAt hπ hint hei ρ (rep t)
    · rw [Set.indicator_of_mem hb, ite_eq_left hb, Nat.cast_one, Pi.one_apply]
    · rw [Set.indicator_of_notMem hb, ite_eq_right hb, Nat.cast_zero]
  rw [hind]
  norm_cast
  unfold rootCount
  rw [← Multiset.toFinset_card_of_nodup hnodup]
  have hFroot : ∀ y ∈ ((toPoly a).aroots ↥(IntermediateField.adjoin K {x})).toFinset,
      Polynomial.aeval y (toPoly a) = 0 := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_aroots] at hy
    exact hy.2
  refine Finset.card_bij
    (fun y hy => Ideal.Quotient.mk I ⟨y, hint_y y (hFroot y hy)⟩) ?_ ?_ ?_
  · -- into the uniformizer classes whose box contains `a`
    intro y hy
    have hw : Polynomial.eval (⟨y, hint_y y (hFroot y hy)⟩ :
        ↥(integers (IntermediateField.adjoin K {x}))) ((intModel a ha).map
          (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))) = 0 :=
      (hroot_iff _).mpr (hFroot y hy)
    have hirr : Irreducible (⟨y, hint_y y (hFroot y hy)⟩ :
        ↥(integers (IntermediateField.adjoin K {x}))) :=
      irreducible_of_isRoot hπ hint hei haE ha hw
    have hrept := hrepirr _ hirr
    have hdist := (hclass (Ideal.Quotient.mk I ⟨y, hint_y y (hFroot y hy)⟩) _).mp rfl
    rw [Finset.mem_filter]
    refine ⟨(hTmem _).mpr hrept, ?_⟩
    rw [mem_boxAt_iff hπ hint hei hrept ρ ha]
    exact le_addVal_eval_of_isRoot hπ hrept hn
      (associated_algebraMap_pow_at hπ hint hei hrept)
      (intModel_monic a ha) (intModel_natDegree a ha)
      (annihAt_monic hπ hint hei _) (annihAt_natDegree hπ hint hei _)
      (eval_map_annihAt hπ hint hei hrept)
      (addVal_derivative_annihAt hπ hint hei hrept) hρbound hw hdist
  · -- injectivity: two roots of the same class coincide
    intro y₁ hy₁ y₂ hy₂ heq
    set w₁ : ↥(integers (IntermediateField.adjoin K {x})) :=
      ⟨y₁, hint_y y₁ (hFroot y₁ hy₁)⟩ with hw₁def
    set w₂ : ↥(integers (IntermediateField.adjoin K {x})) :=
      ⟨y₂, hint_y y₂ (hFroot y₂ hy₂)⟩ with hw₂def
    have hw₁ : Polynomial.eval w₁ ((intModel a ha).map
        (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))) = 0 :=
      (hroot_iff _).mpr (hFroot y₁ hy₁)
    have hw₂ : Polynomial.eval w₂ ((intModel a ha).map
        (algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})))) = 0 :=
      (hroot_iff _).mpr (hFroot y₂ hy₂)
    have hirr₁ : Irreducible w₁ := irreducible_of_isRoot hπ hint hei haE ha hw₁
    have hrept := hrepirr _ hirr₁
    have hd₁ := (hclass (Ideal.Quotient.mk I w₁) w₁).mp rfl
    have hd₂ := (hclass (Ideal.Quotient.mk I w₁) w₂).mp heq.symm
    have heq' := eq_of_isRoot_of_dist hπ hrept hn
      (associated_algebraMap_pow_at hπ hint hei hrept)
      (intModel_monic a ha) (intModel_natDegree a ha)
      (annihAt_monic hπ hint hei _) (annihAt_natDegree hπ hint hei _)
      (eval_map_annihAt hπ hint hei hrept)
      (addVal_derivative_annihAt hπ hint hei hrept) hρbound hw₁ hw₂ hd₁ hd₂
    exact congrArg Subtype.val heq'
  · -- surjectivity: a box membership lifts to a root by Newton
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htT, htB⟩ := ht
    have hrept : Irreducible (rep t) := (hTmem t).mp htT
    rw [mem_boxAt_iff hπ hint hei hrept ρ ha] at htB
    obtain ⟨w, hweval, hwdist⟩ := exists_isRoot_of_le_addVal_eval hAC hπ
      hrept hn (associated_algebraMap_pow_at hπ hint hei hrept)
      (intModel_monic a ha) (intModel_natDegree a ha)
      (annihAt_monic hπ hint hei _) (annihAt_natDegree hπ hint hei _)
      (eval_map_annihAt hπ hint hei hrept)
      (addVal_derivative_annihAt hπ hint hei hrept) hρbound htB
    have hyroot : Polynomial.aeval ((w : ↥(IntermediateField.adjoin K {x}))) (toPoly a) = 0 :=
      (hroot_iff w).mp hweval
    have hmk : ∀ h : (w : ↥(IntermediateField.adjoin K {x})) ∈
        ((toPoly a).aroots ↥(IntermediateField.adjoin K {x})).toFinset,
        Ideal.Quotient.mk I (⟨(w : ↥(IntermediateField.adjoin K {x})),
          hint_y _ (hFroot _ h)⟩ : ↥(integers (IntermediateField.adjoin K {x}))) = t := by
      intro h
      rw [show (⟨(w : ↥(IntermediateField.adjoin K {x})), hint_y _ (hFroot _ h)⟩ :
        ↥(integers (IntermediateField.adjoin K {x}))) = w from Subtype.ext rfl]
      exact (hclass t w).mpr hwdist
    have hwmem : (w : ↥(IntermediateField.adjoin K {x})) ∈
        ((toPoly a).aroots ↥(IntermediateField.adjoin K {x})).toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
      exact ⟨hne, hyroot⟩
    exact ⟨(w : ↥(IntermediateField.adjoin K {x})), hwmem, hmk hwmem⟩

open IsDiscreteValuationRing in
/-- The heart of §3, equations (5)–(13): for `L` in `sigma K n`, the integral of `rootCount L` over
the Eisenstein region is `(1 / q ^ (d L + 1)) * (1 - 1 / q)`, that is `1 / q ^ d L` times the volume
of the set of uniformizers. The route is the lattice form of the paper's change of variables (see
the header of `UniformizerParam.lean`): fixing `ρ = d L + 2`, the classes of `integers L` modulo
`π ^ ρ` times `integers L` whose representative is a uniformizer index a family of disjoint boxes in
the coefficient space—the box of the class of `η` being the exact level set where the value at `η`
has valuation at least `n * ρ + d L` (`mem_boxAt_iff`), of volume `1 / q ^ (n * ρ + d L)`
(`measure_boxAt`), contained in the region (`boxAt_subset_eisensteinSet`). A.e. `f` lies in exactly
`rootCount L f` boxes—the fiber count `existsUnique_isRoot_iff` makes each root correspond to its
class bijectively, every root of an Eisenstein polynomial being a uniformizer
(`irreducible_of_isRoot`)—while the corresponding cubes of the chart partition the image of the set
of uniformizers, of volume `(1 / q) * (1 - 1 / q)` (equation (5),
`measure_image_coord_uniformizers`). So the number of classes cancels between the two sums, and the
integral is `(1 / q ^ d L) * (1 / q) * (1 - 1 / q)`—Lemmas 1–3 with no Jacobian and no `w L`
([Serre 1978, §3, pp.1032–1033][Serre1978]). -/
theorem lintegral_rootCount (n : ℕ) (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (L : IntermediateField K (SeparableClosure K)) (hL : L ∈ sigma K n) :
    ∫⁻ a in eisensteinSet K n, (rootCount L a : ℝ≥0∞) ∂(muCoeff K n) =
      (q K : ℝ≥0∞)⁻¹ ^ (d L + 1) * (1 - (q K : ℝ≥0∞)⁻¹) := by
  classical
  obtain ⟨x, π, hπ, hint, hei, hadj, hdeg⟩ := exists_eisenstein_generator K n hn L hL
  subst hadj
  subst hdeg
  have : IsFractionRing ↥𝒪[K] K :=
    inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
  have hLoc : IsLocalRing ↥(integers (IntermediateField.adjoin K {x})) :=
    isLocalRing_integers hπ hint hei
  have hDVR : IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x})) :=
    isDiscreteValuationRing_integers hπ hint hei
  have hAC : IsAdicComplete
      (IsLocalRing.maximalIdeal ↥(integers (IntermediateField.adjoin K {x})))
      ↥(integers (IntermediateField.adjoin K {x})) := by
    rw [← IsLocalRing.eq_maximalIdeal (isMaximal_span_integralGen hπ hint hei)]
    exact isAdicComplete_span_integralGen hπ hint hei
  -- the radius `ρ` and its arithmetic
  set ρ := d (IntermediateField.adjoin K {x}) + 2 with hρdef
  have hρ2 : 2 ≤ ρ := by omega
  have hρbound : d (IntermediateField.adjoin K {x}) + (minpoly 𝒪[K] x).natDegree ≤
      (minpoly 𝒪[K] x).natDegree * ρ := by
    rw [hρdef, Nat.mul_add]
    exact add_le_add (Nat.le_mul_of_pos_left _ hn) (Nat.le_mul_of_pos_right _ (by norm_num))
  have hNρ1 : 1 < (minpoly 𝒪[K] x).natDegree * ρ := by
    calc 1 < 1 * 2 := by norm_num
      _ ≤ (minpoly 𝒪[K] x).natDegree * ρ := Nat.mul_le_mul hn (by omega)
  -- the classes modulo `π^ρ`, their representatives, and the class dictionary
  set I : Ideal ↥(integers (IntermediateField.adjoin K {x})) :=
    Ideal.span {algebraMap 𝒪[K] ↥(integers (IntermediateField.adjoin K {x})) (π ^ ρ)}
    with hIdef
  have hImem : ∀ z : ↥(integers (IntermediateField.adjoin K {x})),
      z ∈ I ↔ (((minpoly 𝒪[K] x).natDegree * ρ : ℕ) : ℕ∞) ≤
        addVal ↥(integers (IntermediateField.adjoin K {x})) z := by
    intro z
    rw [hIdef, Ideal.mem_span_singleton, ← addVal_le_iff_dvd,
      addVal_algebraMap_pow hπ hint hei ρ]
  set rep : (↥(integers (IntermediateField.adjoin K {x})) ⧸ I) →
      ↥(integers (IntermediateField.adjoin K {x})) :=
    Function.surjInv Ideal.Quotient.mk_surjective with hrepdef
  have hrep : ∀ t, Ideal.Quotient.mk I (rep t) = t := fun t =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective t
  have hclass : ∀ (t : ↥(integers (IntermediateField.adjoin K {x})) ⧸ I)
      (w : ↥(integers (IntermediateField.adjoin K {x}))),
      Ideal.Quotient.mk I w = t ↔
        (((minpoly 𝒪[K] x).natDegree * ρ : ℕ) : ℕ∞) ≤
          addVal ↥(integers (IntermediateField.adjoin K {x})) (w - rep t) := by
    intro t w
    rw [← hImem]
    constructor
    · intro h
      exact Ideal.Quotient.eq.mp (h.trans (hrep t).symm)
    · intro h
      have h2 : Ideal.Quotient.mk I w = Ideal.Quotient.mk I (rep t) := Ideal.Quotient.eq.mpr h
      rw [h2, hrep t]
  -- the classes are finitely many: coordinatewise, they inject into `(𝒪 / π^ρ)^n`
  have hQfin : Finite (𝒪[K] ⧸ Ideal.span {π ^ ρ}) := by
    have hcard : Nat.card (𝒪[K] ⧸ Ideal.span {π ^ ρ}) = q K ^ ρ := by
      have : (IsLocalRing.maximalIdeal 𝒪[K]).IsPrime := Ideal.IsMaximal.isPrime inferInstance
      have hne : IsLocalRing.maximalIdeal 𝒪[K] ≠ ⊥ := by
        rw [hπ.maximalIdeal_eq, Ne, Ideal.span_singleton_eq_bot]
        exact hπ.ne_zero
      have hspan : Ideal.span {π ^ ρ} = IsLocalRing.maximalIdeal 𝒪[K] ^ ρ := by
        rw [← Ideal.span_singleton_pow, hπ.maximalIdeal_eq]
      rw [← Submodule.cardQuot_apply, hspan, cardQuot_pow_of_prime hne,
        Submodule.cardQuot_apply]
      rfl
    exact Nat.finite_of_card_ne_zero (by
      rw [hcard]
      exact pow_ne_zero _ (by have := one_lt_q K; omega))
  have hAIfin : Finite (↥(integers (IntermediateField.adjoin K {x})) ⧸ I) := by
    refine Finite.of_injective (fun t => fun i : Fin (minpoly 𝒪[K] x).natDegree =>
      Ideal.Quotient.mk (Ideal.span {π ^ ρ})
        ((basisOfEisenstein hπ hint hei).repr (rep t) i)) ?_
    intro t t' htt'
    have hco : ∀ i, (ρ : ℕ∞) ≤ addVal 𝒪[K]
        ((basisOfEisenstein hπ hint hei).repr (rep t - rep t') i) := by
      intro i
      have h2 : (basisOfEisenstein hπ hint hei).repr (rep t) i -
          (basisOfEisenstein hπ hint hei).repr (rep t') i ∈ Ideal.span {π ^ ρ} :=
        Ideal.Quotient.eq.mp (congrFun htt' i)
      rw [map_sub, Finsupp.sub_apply]
      rwa [Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hπ.addVal_pow] at h2
    have h3 : rep t - rep t' ∈ I := by
      rw [hImem, le_addVal_mul_iff_coords hπ hint hei ρ]
      exact hco
    have h4 : Ideal.Quotient.mk I (rep t) = Ideal.Quotient.mk I (rep t') :=
      Ideal.Quotient.eq.mpr h3
    rw [hrep, hrep] at h4
    exact h4
  have := Fintype.ofFinite (↥(integers (IntermediateField.adjoin K {x})) ⧸ I)
  set T : Finset (↥(integers (IntermediateField.adjoin K {x})) ⧸ I) :=
    Finset.univ.filter (fun t => Irreducible (rep t)) with hTdef
  have hTmem : ∀ t, t ∈ T ↔ Irreducible (rep t) := by
    intro t
    rw [hTdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ t, h⟩⟩
  -- irreducibility is a class invariant, the radius exceeding `1`
  have hrepirr : ∀ w : ↥(integers (IntermediateField.adjoin K {x})), Irreducible w →
      Irreducible (rep (Ideal.Quotient.mk I w)) := by
    intro w hw
    have hdist := (hclass (Ideal.Quotient.mk I w) w).mp rfl
    apply irreducible_of_addVal_eq_one
    apply addVal_eq_one_of_close hw
    rw [(addVal ↥(integers (IntermediateField.adjoin K {x}))).map_sub_swap]
    exact lt_of_lt_of_le (by exact_mod_cast hNρ1) hdist
  have hval_of_class : ∀ w : ↥(integers (IntermediateField.adjoin K {x})),
      Irreducible (rep (Ideal.Quotient.mk I w)) →
      addVal ↥(integers (IntermediateField.adjoin K {x})) w = 1 := by
    intro w hrw
    have hdist := (hclass (Ideal.Quotient.mk I w) w).mp rfl
    exact addVal_eq_one_of_close hrw (lt_of_lt_of_le (by exact_mod_cast hNρ1) hdist)
  -- the normalization, and the cubes of the chart at the Eisenstein generator
  have hone : muCoeff K (minpoly 𝒪[K] x).natDegree
      (integerBox K (minpoly 𝒪[K] x).natDegree) = 1 :=
    Measure.addHaarMeasure_self (K₀ := integerPositiveCompacts K (minpoly 𝒪[K] x).natDegree)
  have hTcount := uniformizer_classes_mass K hπ hint hei ρ I rep T
    hclass hTmem hrepirr hval_of_class hone
  have hcount := rootCount_eq_sum_indicator K hπ hint hei hAC ρ I rep T
    hclass hTmem hrepirr hρbound
  -- assemble the integral
  have hae : ∀ᵐ a ∂((muCoeff K (minpoly 𝒪[K] x).natDegree).restrict
      (eisensteinSet K (minpoly 𝒪[K] x).natDegree)),
      (rootCount (IntermediateField.adjoin K {x}) a : ℝ≥0∞) =
        ∑ t ∈ T, (boxAt hπ hint hei ρ (rep t)).indicator 1 a := by
    filter_upwards [ae_separable (minpoly 𝒪[K] x).natDegree hn] with a haa
    exact hcount a haa.1 haa.2
  calc ∫⁻ a in eisensteinSet K (minpoly 𝒪[K] x).natDegree,
      (rootCount (IntermediateField.adjoin K {x}) a : ℝ≥0∞)
        ∂(muCoeff K (minpoly 𝒪[K] x).natDegree)
      = ∫⁻ a in eisensteinSet K (minpoly 𝒪[K] x).natDegree,
          ∑ t ∈ T, (boxAt hπ hint hei ρ (rep t)).indicator 1 a
          ∂(muCoeff K (minpoly 𝒪[K] x).natDegree) := lintegral_congr_ae hae
    _ = ∑ t ∈ T, ∫⁻ a in eisensteinSet K (minpoly 𝒪[K] x).natDegree,
          (boxAt hπ hint hei ρ (rep t)).indicator 1 a
          ∂(muCoeff K (minpoly 𝒪[K] x).natDegree) :=
        lintegral_finsetSum _ fun t _ =>
          measurable_one.indicator (measurableSet_boxAt hπ hint hei ρ (rep t))
    _ = ∑ t ∈ T, muCoeff K (minpoly 𝒪[K] x).natDegree (boxAt hπ hint hei ρ (rep t)) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [lintegral_indicator_one (measurableSet_boxAt hπ hint hei ρ (rep t)),
          Measure.restrict_apply (measurableSet_boxAt hπ hint hei ρ (rep t)),
          Set.inter_eq_self_of_subset_left
            (boxAt_subset_eisensteinSet hπ hint hei ((hTmem t).mp ht) hρ2)]
    _ = ∑ t ∈ T, (q K : ℝ≥0∞)⁻¹ ^
          ((minpoly 𝒪[K] x).natDegree * ρ + d (IntermediateField.adjoin K {x})) :=
        Finset.sum_congr rfl fun t ht =>
          measure_boxAt hπ hint hei _ hone ((hTmem t).mp ht) ρ
    _ = (T.card : ℝ≥0∞) * ((q K : ℝ≥0∞)⁻¹ ^ ((minpoly 𝒪[K] x).natDegree * ρ) *
          (q K : ℝ≥0∞)⁻¹ ^ d (IntermediateField.adjoin K {x})) := by
        rw [Finset.sum_const, nsmul_eq_mul, pow_add]
    _ = ((T.card : ℝ≥0∞) * (q K : ℝ≥0∞)⁻¹ ^ ((minpoly 𝒪[K] x).natDegree * ρ)) *
          (q K : ℝ≥0∞)⁻¹ ^ d (IntermediateField.adjoin K {x}) := by ring
    _ = ((q K : ℝ≥0∞)⁻¹ * (1 - (q K : ℝ≥0∞)⁻¹)) *
          (q K : ℝ≥0∞)⁻¹ ^ d (IntermediateField.adjoin K {x}) := by rw [hTcount]
    _ = (q K : ℝ≥0∞)⁻¹ ^ (d (IntermediateField.adjoin K {x}) + 1) *
          (1 - (q K : ℝ≥0∞)⁻¹) := by
        rw [pow_succ]
        ring

omit [IsUniformAddGroup K] in
/-- The ramification core: a root of an Eisenstein polynomial generates a
*totally ramified* extension ([Serre 1979, Chap. I, §6, Prop. 17][Serre1979]). The minimal
polynomial of the root over `𝒪[K]` is identified with the integral Eisenstein model
(`minpoly_eq_of_root`), and `isTotallyRamified_adjoin` computes `ramificationIdx L = n` through the
monogenic presentation `integers_eq_adjoin`. -/
theorem isTotallyRamified_adjoin_root {n : ℕ} (hn : 0 < n) {a : Fin n → K}
    (ha : a ∈ eisensteinSet K n) {x : SeparableClosure K}
    (hx : Polynomial.aeval x (toPoly a) = 0) :
    IsTotallyRamified (IntermediateField.adjoin K {x}) := by
  obtain ⟨π, hπ, hint, hei⟩ := minpoly_eq_of_root hn ha hx
  exact isTotallyRamified_adjoin hπ hint hei

omit [IsUniformAddGroup K] in
/-- The algebraic core of equation (3) and Lemma 1: a *separable* point of the Eisenstein region has
root counts over `sigma K n` summing to `n`. The polynomial is irreducible with `n` distinct roots
in `SeparableClosure K`; each root generates a member of `sigma K n` (of degree `n` via its minimal
polynomial, totally ramified by `isTotallyRamified_adjoin_root`); a member of `sigma K n` contains a
root exactly when the root generates it (equal finite degrees); so the root counts are the fiber
counts of the map sending a root `x` to `K⟮x⟯` on the `n`-element root set, and fiberwise counting
sums them to `n` ([Serre 1978, eq. (3), p.1032; Lemma 1, p.1033][Serre1978]). -/
theorem tsum_rootCount_of_separable {n : ℕ} (hn : 0 < n) {a : Fin n → K}
    (ha : a ∈ eisensteinSet K n) (hsep : (toPoly a).Separable) :
    ∑' L : sigma K n, (rootCount L.1 a : ℝ≥0∞) = n := by
  classical
  have hmonic : (toPoly a).Monic := by unfold toPoly; exact shape_monic _
  have hdeg : (toPoly a).natDegree = n := by unfold toPoly; exact shape_natDegree _
  have hirr : Irreducible (toPoly a) := irreducible_toPoly hn ha
  have hne : toPoly a ≠ 0 := hmonic.ne_zero
  set S : Finset (SeparableClosure K) := ((toPoly a).aroots (SeparableClosure K)).toFinset
    with hS
  have hnodup : ((toPoly a).aroots (SeparableClosure K)).Nodup :=
    Polynomial.nodup_roots hsep.map
  have hcardS : S.card = n := by
    rw [hS, Multiset.toFinset_card_of_nodup hnodup]
    have hsplits : ((toPoly a).map (algebraMap K (SeparableClosure K))).Splits :=
      IsSepClosed.splits_codomain _ hsep
    rw [Polynomial.aroots_def, ← hsplits.natDegree_eq_card_roots, hmonic.natDegree_map, hdeg]
  have hroot : ∀ x ∈ S, Polynomial.aeval x (toPoly a) = 0 := by
    intro x hx
    rw [hS, Multiset.mem_toFinset, Polynomial.mem_aroots] at hx
    exact hx.2
  have hfinrank : ∀ x ∈ S, Module.finrank K ↥(IntermediateField.adjoin K {x}) = n := by
    intro x hx
    have hint : IsIntegral K x := ⟨toPoly a, hmonic, hroot x hx⟩
    have hmin : minpoly K x = toPoly a :=
      (minpoly.eq_of_irreducible_of_monic hirr (hroot x hx) hmonic).symm
    rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]
  have hmemsigma : ∀ x ∈ S, IntermediateField.adjoin K {x} ∈ sigma K n := fun x hx =>
    mem_sigma.mpr ⟨hfinrank x hx, isTotallyRamified_adjoin_root K hn ha (hroot x hx)⟩
  set T : Finset (IntermediateField K (SeparableClosure K)) :=
    S.image (fun x => IntermediateField.adjoin K {x}) with hT
  -- the fiber identity: roots in `M` are exactly the roots generating `M`
  have hfiber : ∀ M ∈ sigma K n, rootCount M a =
      (S.filter fun x => IntermediateField.adjoin K {x} = M).card := by
    intro M hM
    have hMrank : Module.finrank K ↥M = n := (mem_sigma.mp hM).1
    have : FiniteDimensional K ↥M := Module.finite_of_finrank_pos (by rw [hMrank]; omega)
    have hnodupM : ((toPoly a).aroots ↥M).Nodup := Polynomial.nodup_roots hsep.map
    change ((toPoly a).aroots ↥M).card = _
    rw [← Multiset.toFinset_card_of_nodup hnodupM]
    refine Finset.card_bij (fun y _ => (y : SeparableClosure K)) ?_ ?_ ?_
    · intro y hy
      rw [Multiset.mem_toFinset, Polynomial.mem_aroots] at hy
      have hyroot : Polynomial.aeval (y : SeparableClosure K) (toPoly a) = 0 := by
        rw [show ((y : SeparableClosure K)) = M.val y from rfl,
          Polynomial.aeval_algHom_apply, hy.2, map_zero]
      rw [Finset.mem_filter]
      refine ⟨by rw [hS, Multiset.mem_toFinset, Polynomial.mem_aroots]; exact ⟨hne, hyroot⟩, ?_⟩
      have hle : IntermediateField.adjoin K {(y : SeparableClosure K)} ≤ M := by
        rw [IntermediateField.adjoin_le_iff]
        exact Set.singleton_subset_iff.mpr y.2
      have hrank2 :
          Module.finrank K ↥(IntermediateField.adjoin K {(y : SeparableClosure K)}) = n := by
        have hint : IsIntegral K (y : SeparableClosure K) := ⟨toPoly a, hmonic, hyroot⟩
        have hmin : minpoly K (y : SeparableClosure K) = toPoly a :=
          (minpoly.eq_of_irreducible_of_monic hirr hyroot hmonic).symm
        rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]
      exact IntermediateField.eq_of_le_of_finrank_le hle (by rw [hMrank, hrank2])
    · intro y1 h1 y2 h2 heq
      exact Subtype.val_injective heq
    · intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxS, hxM⟩ := hx
      have hxmem : x ∈ M := by
        rw [← hxM]
        exact IntermediateField.mem_adjoin_simple_self K x
      refine ⟨⟨x, hxmem⟩, ?_, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
      refine ⟨hne, ?_⟩
      have h3 : ((Polynomial.aeval (⟨x, hxmem⟩ : ↥M) (toPoly a) : ↥M) : SeparableClosure K) =
          Polynomial.aeval x (toPoly a) :=
        (Polynomial.aeval_algHom_apply M.val ((⟨x, hxmem⟩ : ↥M)) (toPoly a)).symm
      exact Subtype.val_injective (by rw [h3, hroot x hxS]; rfl)
  -- collapse the `tsum` to the finite image
  have hzero : ∀ L : sigma K n, L.1 ∉ T → (rootCount L.1 a : ℝ≥0∞) = 0 := by
    intro L hLT
    rw [hfiber L.1 L.2]
    norm_cast
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hxS hadj
    exact hLT (hT ▸ Finset.mem_image.mpr ⟨x, hxS, hadj⟩)
  have htsum : ∑' L : sigma K n, (rootCount L.1 a : ℝ≥0∞) =
      ∑ L ∈ T.subtype (· ∈ sigma K n), (rootCount L.1 a : ℝ≥0∞) := by
    refine tsum_eq_sum ?_
    intro L hLT'
    refine hzero L fun hLT => hLT' ?_
    rw [Finset.mem_subtype]
    exact hLT
  have hTsub : ∀ M ∈ T, M ∈ sigma K n := by
    intro M hM
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp (hT ▸ hM)
    exact hmemsigma x hxS
  have hsum2 : ∑ L ∈ T.subtype (· ∈ sigma K n), (rootCount L.1 a : ℝ≥0∞) =
      ∑ M ∈ T, (rootCount M a : ℝ≥0∞) :=
    Finset.sum_subtype_of_mem (p := fun M => M ∈ sigma K n)
      (fun M => (rootCount M a : ℝ≥0∞)) hTsub
  rw [htsum, hsum2]
  have hfibersum : ∑ M ∈ T, ((S.filter fun x => IntermediateField.adjoin K {x} = M).card : ℝ≥0∞) =
      (n : ℝ≥0∞) := by
    rw [← Nat.cast_sum]
    congr 1
    rw [← hcardS]
    have hmaps : (↑S : Set (SeparableClosure K)).MapsTo
        (fun x => IntermediateField.adjoin K {x}) (↑T) := by
      intro x hx
      rw [Finset.mem_coe] at hx
      rw [Finset.mem_coe, hT]
      exact Finset.mem_image_of_mem _ hx
    exact (Finset.card_eq_sum_card_fiberwise hmaps).symm
  rw [← hfibersum]
  exact Finset.sum_congr rfl fun M hM => by rw [hfiber M (hTsub M hM)]

/-- Almost every `f` in the Eisenstein region has nonzero discriminant—and such an `f`,
irreducible by the Eisenstein criterion and separable, has exactly `n` roots in
`SeparableClosure K`, each a uniformizer generating a totally ramified subextension of degree `n`. A
root generating `L` lies in no other member of `sigma K n` (two members containing a common
generator coincide), so the root counts over `sigma K n` sum to `n`
([Serre 1978, eq. (3), p.1032][Serre1978]). -/
theorem tsum_rootCount (n : ℕ) (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] :
    ∀ᵐ a ∂((muCoeff K n).restrict (eisensteinSet K n)),
      ∑' L : sigma K n, (rootCount L.1 a : ℝ≥0∞) = n := by
  rcases Nat.lt_or_ge n 2 with hsmall | h2
  · -- `n = 1`: every Eisenstein polynomial is linear, hence separable
    have h1 : n = 1 := by omega
    subst h1
    filter_upwards [ae_restrict_mem (measurableSet_eisensteinSet Nat.one_pos)] with a haE
    refine tsum_rootCount_of_separable K Nat.one_pos haE ?_
    have htp : toPoly a = Polynomial.X + Polynomial.C (a 0) := by
      unfold toPoly
      rw [Fin.sum_univ_one]
      simp
    rw [htp]
    exact Polynomial.separable_X_add_C _
  · -- `2 ≤ n`: the inseparable locus lies in the null hyperplane `a 1 = 0`
    have hnull : (muCoeff K n).restrict (eisensteinSet K n)
        {a : Fin n → K | a ⟨1, by omega⟩ = 0} = 0 := by
      rw [Measure.restrict_apply' (measurableSet_eisensteinSet hn)]
      refine measure_mono_null ?_ (measure_pi_inter_coord_eq_zero n ⟨1, by omega⟩)
      rintro a ⟨ha1, haE⟩
      exact ⟨eisensteinSet_subset_pi haE, ha1⟩
    have hae1 : ∀ᵐ a ∂((muCoeff K n).restrict (eisensteinSet K n)), a ⟨1, by omega⟩ ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    filter_upwards [ae_restrict_mem (measurableSet_eisensteinSet hn), hae1] with a haE ha1
    exact tsum_rootCount_of_separable K hn haE (separable_toPoly h2 haE ha1)

/-- `sigma K n` is countable—all the `tsum`–`lintegral` interchange of the assembly needs.
Remarks 1° and 2° refine this (finiteness outside the equal-characteristic wild case, Krasner's
counts), but countability is cheaper: the members of `sigma K n` carve the Eisenstein region into
pieces of positive volume with bounded total. Concretely, each `L` in `sigma K n` owns a nonempty
open subset of the Eisenstein region on which its root count is positive—a neighborhood, by the
local constancy `rootCount_eventuallyEq`, of the coefficient vector of the minimal polynomial of an
Eisenstein generator (`exists_eisenstein_generator`); the masses are positive (Haar), while any
finitely many of them total at most `n` times the volume of the region because the root counts sum
to `n` a.e. (equation (3)); a family of positive masses with bounded finite subsums has countable
index. -/
theorem countable_sigma (n : ℕ) (hn : 0 < n) : (sigma K n).Countable := by
  classical
  let : MeasurableSpace (Fin n → K) := borel _
  have : BorelSpace (Fin n → K) := ⟨rfl⟩
  have : IsFractionRing ↥𝒪[K] K :=
    inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
  -- each `L` gets a nonempty open subset of the region with root count `≥ 1` throughout
  have hex : ∀ L ∈ sigma K n, ∃ O : Set (Fin n → K), IsOpen O ∧ O.Nonempty ∧
      O ⊆ eisensteinSet K n ∧ ∀ b ∈ O, 1 ≤ rootCount L b := by
    intro L hL
    obtain ⟨x, π, hπ, hint, hei, hadj, hdeg⟩ := exists_eisenstein_generator K n hn L hL
    -- the coefficient vector of the minimal polynomial of the Eisenstein generator
    set F : Polynomial K := (minpoly 𝒪[K] x).map (algebraMap 𝒪[K] K) with hF
    have hFmin : minpoly K x = F := by
      rw [hF]
      exact minpoly.isIntegrallyClosed_eq_field_fractions' K hint
    have hmono : (minpoly 𝒪[K] x).Monic := minpoly.monic hint
    have hFmonic : F.Monic := hmono.map _
    have hFdeg : F.natDegree = n := by rw [hF, hmono.natDegree_map, hdeg]
    set a : Fin n → K := fun i => F.coeff i with ha
    have htoPoly : toPoly a = F := toPoly_coeffs hFmonic hFdeg
    have haE : a ∈ eisensteinSet K n := coeff_mem_eisensteinSet hn hπ hdeg hei
    have hsep : (toPoly a).Separable := by
      rw [htoPoly, ← hFmin]
      exact Algebra.IsSeparable.isSeparable K x
    -- the generator itself is a root of `toPoly a` lying in `L`
    have hxL : x ∈ L := hadj ▸ IntermediateField.mem_adjoin_simple_self K x
    have hroot : Polynomial.aeval x (toPoly a) = 0 := by
      rw [htoPoly, ← hFmin]
      exact minpoly.aeval K x
    have hcount : 1 ≤ rootCount L a := by
      have hne : toPoly a ≠ 0 := by rw [htoPoly]; exact hFmonic.ne_zero
      have hrootL : Polynomial.aeval (⟨x, hxL⟩ : ↥L) (toPoly a) = 0 := by
        have h3 : ((Polynomial.aeval (⟨x, hxL⟩ : ↥L) (toPoly a) : ↥L) : SeparableClosure K) =
            Polynomial.aeval x (toPoly a) :=
          (Polynomial.aeval_algHom_apply L.val (⟨x, hxL⟩ : ↥L) (toPoly a)).symm
        exact Subtype.val_injective (by rw [h3, hroot]; rfl)
      exact Multiset.card_pos_iff_exists_mem.mpr
        ⟨_, Polynomial.mem_aroots.mpr ⟨hne, hrootL⟩⟩
    -- local constancy turns the positive count at `a` into a positive count on an open neighborhood
    obtain ⟨U, hUeq, hUopen, haU⟩ :=
      eventually_nhds_iff.mp (rootCount_eventuallyEq K n hn L hL haE hsep)
    refine ⟨U ∩ eisensteinSet K n, hUopen.inter (isOpen_eisensteinSet hn), ⟨a, haU, haE⟩,
      Set.inter_subset_right, fun b hb => ?_⟩
    have hbeq := hUeq b hb.1
    omega
  choose O hOopen hOne hOsub hOge using fun L : ↥(sigma K n) => hex L.1 L.2
  -- the masses are positive ...
  have hOpos : ∀ L : ↥(sigma K n), muCoeff K n (O L) ≠ 0 := fun L =>
    (hOopen L).measure_ne_zero (muCoeff K n) (hOne L)
  -- ... while any finitely many of them total at most `n` times the volume of the region, since
  -- the counts sum to `n` a.e.
  have hEone : muCoeff K n (eisensteinSet K n) ≤ 1 := by
    have hone : muCoeff K n (Set.univ.pi fun _ : Fin n => (𝒪[K] : Set K)) = 1 :=
      Measure.addHaarMeasure_self (K₀ := integerPositiveCompacts K n)
    exact hone ▸ measure_mono eisensteinSet_subset_pi
  have hsum : ∀ s : Finset ↥(sigma K n),
      ∑ L ∈ s, muCoeff K n (O L) ≤ (n : ℝ≥0∞) * muCoeff K n (eisensteinSet K n) := by
    intro s
    have hind : ∀ L : ↥(sigma K n), muCoeff K n (O L) =
        ∫⁻ b in eisensteinSet K n, (O L).indicator 1 b ∂(muCoeff K n) := by
      intro L
      rw [lintegral_indicator_one (hOopen L).measurableSet,
        Measure.restrict_apply (hOopen L).measurableSet,
        Set.inter_eq_self_of_subset_left (hOsub L)]
    calc ∑ L ∈ s, muCoeff K n (O L)
        = ∑ L ∈ s, ∫⁻ b in eisensteinSet K n, (O L).indicator 1 b ∂(muCoeff K n) :=
          Finset.sum_congr rfl fun L _ => hind L
      _ = ∫⁻ b in eisensteinSet K n, ∑ L ∈ s, (O L).indicator 1 b ∂(muCoeff K n) :=
          (lintegral_finsetSum s fun L _ =>
            measurable_one.indicator (hOopen L).measurableSet).symm
      _ ≤ ∫⁻ _ in eisensteinSet K n, (n : ℝ≥0∞) ∂(muCoeff K n) := by
          refine lintegral_mono_ae ?_
          filter_upwards [tsum_rootCount K n hn] with b hb
          calc ∑ L ∈ s, (O L).indicator 1 b
              ≤ ∑ L ∈ s, (rootCount L.1 b : ℝ≥0∞) := by
                refine Finset.sum_le_sum fun L _ => ?_
                by_cases hbO : b ∈ O L
                · rw [Set.indicator_of_mem hbO, Pi.one_apply]
                  exact_mod_cast hOge L b hbO
                · rw [Set.indicator_of_notMem hbO]
                  exact zero_le
            _ ≤ ∑' L : sigma K n, (rootCount L.1 b : ℝ≥0∞) := ENNReal.sum_le_tsum s
            _ = (n : ℝ≥0∞) := hb
      _ = (n : ℝ≥0∞) * muCoeff K n (eisensteinSet K n) := setLIntegral_const _ _
  -- a family of positive masses with bounded finite subsums has countable index
  have htsum : ∑' L : ↥(sigma K n), muCoeff K n (O L) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
      (ne_top_of_le_ne_top ENNReal.one_ne_top hEone)) ?_
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le hsum
  have hcnt : Countable ↥(sigma K n) := by
    have hcov : (Set.univ : Set ↥(sigma K n)) ⊆
        ⋃ k : ℕ, {L : ↥(sigma K n) | ((k : ℝ≥0∞))⁻¹ ≤ muCoeff K n (O L)} := by
      intro L _
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (hOpos L)
      exact Set.mem_iUnion.mpr ⟨k, hk.le⟩
    have hfin : ∀ k : ℕ, {L : ↥(sigma K n) | ((k : ℝ≥0∞))⁻¹ ≤ muCoeff K n (O L)}.Finite :=
      fun k => ENNReal.finite_const_le_of_tsum_ne_top htsum
        (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top k))
    have h := (Set.countable_iUnion fun k => (hfin k).countable).mono hcov
    rwa [Set.countable_univ_iff] at h
  exact Set.countable_coe_iff.mp hcnt

/-! ## The assembly -/

/-- The sum of `1 / q ^ c L` over `L` in `sigma K n` is `n`, assembled from the core lemmas above.
Summing `lintegral_rootCount` over the
countably many members of `sigma K n` and interchanging sum and integral turns the a.e. identity
that the root counts sum to `n` into an identity between the sum of the
`(1 / q ^ (d L + 1)) * (1 - 1 / q)` and `n` times the volume of the region, itself
`n * (1 / q ^ n) * (1 - 1 / q)`; cancelling `1 - 1 / q` and multiplying through by `q ^ n` gives the
mass formula, the bound `n - 1 ≤ d L` (`sub_one_le_d`) converting `q ^ n * (1 / q ^ (d L + 1))`
into `1 / q ^ c L` ([Serre 1978, Theorem 1, p.1031][Serre1978]). -/
theorem tsum_one_div_q_pow_c (n : ℕ) (hn : 0 < n) :
    ∑' L : sigma K n, 1 / (q K : ℝ≥0∞) ^ c L.1 = n := by
  let : MeasurableSpace (Fin n → K) := borel _
  have : BorelSpace (Fin n → K) := ⟨rfl⟩
  have hQ1 : (1 : ℝ≥0∞) < (q K : ℝ≥0∞) := by exact_mod_cast one_lt_q K
  have hQ0 : (q K : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans hQ1).ne'
  have hQtop : (q K : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hfac0 : 1 - (q K : ℝ≥0∞)⁻¹ ≠ 0 :=
    (tsub_pos_of_lt (ENNReal.inv_lt_one.mpr hQ1)).ne'
  have hfactop : 1 - (q K : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have : Countable (sigma K n) := (countable_sigma K n hn).to_subtype
  -- the summed change-of-variables identity, still carrying the factor `1 - q⁻¹`
  have key : (∑' L : sigma K n, (q K : ℝ≥0∞)⁻¹ ^ (d L.1 + 1)) * (1 - (q K : ℝ≥0∞)⁻¹) =
      (n : ℝ≥0∞) * (q K : ℝ≥0∞)⁻¹ ^ n * (1 - (q K : ℝ≥0∞)⁻¹) := by
    rw [← ENNReal.tsum_mul_right]
    calc ∑' L : sigma K n, (q K : ℝ≥0∞)⁻¹ ^ (d L.1 + 1) * (1 - (q K : ℝ≥0∞)⁻¹)
        = ∑' L : sigma K n,
            ∫⁻ a in eisensteinSet K n, (rootCount L.1 a : ℝ≥0∞) ∂(muCoeff K n) :=
          tsum_congr fun L => (lintegral_rootCount K n hn L.1 L.2).symm
      _ = ∫⁻ a in eisensteinSet K n,
            ∑' L : sigma K n, (rootCount L.1 a : ℝ≥0∞) ∂(muCoeff K n) :=
          -- `f` and `μ` are pinned explicitly: leaving them to unification against
          -- the `aemeasurable_rootCount` terms sends the elaborator into a `whnf` loop
          (lintegral_tsum (μ := (muCoeff K n).restrict (eisensteinSet K n))
            (f := fun (L : sigma K n) (a : Fin n → K) => (rootCount L.1 a : ℝ≥0∞))
            fun L => aemeasurable_rootCount K n hn L.1 L.2).symm
      _ = ∫⁻ _ in eisensteinSet K n, (n : ℝ≥0∞) ∂(muCoeff K n) := by
          refine lintegral_congr_ae ?_
          filter_upwards [tsum_rootCount K n hn] with a ha
          exact ha
      _ = (n : ℝ≥0∞) * muCoeff K n (eisensteinSet K n) := setLIntegral_const _ _
      _ = (n : ℝ≥0∞) * (q K : ℝ≥0∞)⁻¹ ^ n * (1 - (q K : ℝ≥0∞)⁻¹) := by
          rw [muCoeff_eisensteinSet K n hn, mul_assoc]
  -- cancel the factor `1 - q⁻¹`
  have key2 : ∑' L : sigma K n, (q K : ℝ≥0∞)⁻¹ ^ (d L.1 + 1) =
      (n : ℝ≥0∞) * (q K : ℝ≥0∞)⁻¹ ^ n := by
    have h := congrArg (· * (1 - (q K : ℝ≥0∞)⁻¹)⁻¹) key
    simpa [mul_assoc, ENNReal.mul_inv_cancel hfac0 hfactop] using h
  -- multiply through by `q^n`
  have key3 : ∑' L : sigma K n, (q K : ℝ≥0∞) ^ n * (q K : ℝ≥0∞)⁻¹ ^ (d L.1 + 1) = n := by
    rw [ENNReal.tsum_mul_left, key2, mul_left_comm, ← mul_pow,
      ENNReal.mul_inv_cancel hQ0 hQtop, one_pow, mul_one]
  -- identify the summands termwise, via the bound `n - 1 ≤ d (L)`
  refine Eq.trans (tsum_congr fun L => ?_) key3
  have hd : n ≤ d L.1 + 1 := by
    have h := sub_one_le_d K n hn L.1 L.2
    omega
  obtain ⟨e, he⟩ : ∃ e, d L.1 + 1 = n + e := ⟨d L.1 + 1 - n, (Nat.add_sub_cancel' hd).symm⟩
  have hce : c L.1 = e := by
    unfold c
    rw [(mem_sigma.mp L.2).1]
    omega
  rw [hce, he, pow_add, one_div, ENNReal.inv_pow, ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel hQ0 hQtop, one_pow, one_mul]

end MassFormula
