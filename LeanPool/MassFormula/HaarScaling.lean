/-
Copyright (c) 2026 Hyeon Seung-Hyeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hyeon Seung-Hyeon
-/

-- Adapted for Lean Pool from 0stellensatz/MassFormula at 7fa41a621f724f110183904d3fd19c6730a932ad.
module

public import LeanPool.MassFormula.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
import Mathlib.MeasureTheory.Group.Action
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Auxiliary file: the linear Haar scaling law

Lemma 3 of the paper, in the form §3 consumes it: an integral matrix `M` with nonzero determinant
scales the Haar measure of the coefficient space by `1 / q ^ k`, where `k` is the `π`-adic order of
`M.det` ([Serre 1978, Lemma 3, p.1033][Serre1978]). The lemma is the volume input of the change of
variables along the parametrization of equations (11)–(13), where `M` is the Jacobian of the
minimal-polynomial map and `k` is `d L`.

The route is uniqueness-free—no appeal to the uniqueness of Haar measure, hence no
second-countability or regularity side conditions. Everything reduces to *lattices*, that is to the
images of the integer box under `M`:

- **The index.** `card_quotient_range`: the quotient of the integer box by its image under `M` has
  exactly `q ^ k` elements. Mathlib's Smith normal form over the principal ideal ring `𝒪[K]`
  (`Submodule.quotientEquivPiSpan`) splits the quotient into a product of the residue rings of the
  diagonal coefficients `a i`, whose product is associated to `M.det`
  (`LinearMap.associated_det_comp_equiv`), and each factor is `q` to the order of `a i` because
  `𝒪[K]` is a discrete valuation ring with residue cardinality `q`.
- **The volume.** `measure_integerBox_eq_pow_mul`: the image lattice is a compact subgroup of the
  integer box of index `q ^ k`, so the box is the disjoint union of its `q ^ k` translates and has
  `q ^ k` times its volume.
- **The box form.** `measure_box_eq_inv_pow`: the lattice of a *diagonal* matrix is the coordinate
  box whose `i`-th factor is `π ^ e i` times `𝒪[K]` (`imageLattice_diagonal`), so a box has volume
  `1 / q ^ (∑ i, e i)` once the measure is normalized on the integer box. This is what a ball of
  `integers L` becomes in the coordinates of a power basis, and the only other volume the assembly
  of equation (13) needs.
- **The ball form.** `measure_ball_eq_pow_mul`: a ball is itself a translate of the lattice of the
  box of constant radii `π ^ m`, and the image of a ball is a translate of the lattice of the matrix
  `π ^ m • M`, whose determinant has order `m * n + k`—so the scaling factor `q ^ k` appears as a
  ratio of two lattice volumes, with no scaling law for general sets needed.

Modeling decisions, local to this file:

- The scaling exponent is carried by the hypothesis `Associated M.det (π ^ k)`—the `π`-adic order
  of the determinant, stated through associates so that no `ℤ`-valued valuation or choice of
  normalization enters. `associated_pow_of_valuation` converts a valuation-level hypothesis (the
  form Lemma 2 of the paper produces) into it.
- The coefficient space, its measure `muCoeff`, and the integer box are those of `First.lean`; the
  box and the balls are restated here as `integerBox` and `ball` to keep this file independent of
  that one.

## References

* [Serre1978] J-P. Serre, *Une «formule de masse» pour les extensions totalement ramifiées de
  degré donné d'un corps local*, C. R. Acad. Sci. Paris **286** (1978), Série A, 1031–1036.
-/

public section

open ValuativeRel MeasureTheory Module
open scoped ENNReal Pointwise

namespace MassFormula

variable {K : Type*} [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
  [IsNonarchimedeanLocalField K]

/-! ## The `π`-adic order of an element of `𝒪[K]`, through associates -/

omit [IsUniformAddGroup K] in
/-- Every nonzero element of the discrete valuation ring `𝒪[K]` is associated to a power of a fixed
uniformizer. -/
private lemma exists_associated_pow {π : 𝒪[K]} (hπ : Irreducible π) {a : 𝒪[K]} (ha : a ≠ 0) :
    ∃ k : ℕ, Associated a (π ^ k) := by
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  exact ⟨k, u⁻¹, by rw [hu, mul_comm (u : 𝒪[K]), mul_assoc, Units.mul_inv, mul_one]⟩

omit [IsUniformAddGroup K] in
/-- The residue ring of a power of a uniformizer has `q ^ k` elements: the ideal is the `k`-th power
of the maximal ideal, whose residue ring is the residue field of cardinality `q`. -/
private lemma card_quotient_span_pow {π : 𝒪[K]} (hπ : Irreducible π) (k : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {π ^ k}) = q K ^ k := by
  have : (IsLocalRing.maximalIdeal 𝒪[K]).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  have hne : IsLocalRing.maximalIdeal 𝒪[K] ≠ ⊥ := by
    rw [hπ.maximalIdeal_eq, Ne, Ideal.span_singleton_eq_bot]
    exact hπ.ne_zero
  have hspan : Ideal.span {π ^ k} = IsLocalRing.maximalIdeal 𝒪[K] ^ k := by
    rw [← Ideal.span_singleton_pow, hπ.maximalIdeal_eq]
  rw [← Submodule.cardQuot_apply, hspan, cardQuot_pow_of_prime hne, Submodule.cardQuot_apply]
  rfl

omit [IsUniformAddGroup K] in
/-- The residue ring of any element of `π`-adic order `k` has `q ^ k` elements. -/
private lemma card_quotient_span {π : 𝒪[K]} (hπ : Irreducible π) {a : 𝒪[K]} {k : ℕ}
    (h : Associated a (π ^ k)) : Nat.card (𝒪[K] ⧸ Ideal.span {a}) = q K ^ k := by
  rw [Ideal.span_singleton_eq_span_singleton.mpr h, card_quotient_span_pow hπ]

omit [IsUniformAddGroup K] in
/-- The `π`-adic order is well defined: associated powers of a uniformizer have equal exponents,
since their residue rings have `q ^ k` elements and `1 < q`. -/
private lemma pow_eq_of_associated {π : 𝒪[K]} (hπ : Irreducible π) {m k : ℕ}
    (h : Associated (π ^ m) (π ^ k)) : m = k := by
  have h1 : Nat.card (𝒪[K] ⧸ Ideal.span {π ^ m}) = Nat.card (𝒪[K] ⧸ Ideal.span {π ^ k}) := by
    rw [Ideal.span_singleton_eq_span_singleton.mpr h]
  rw [card_quotient_span_pow hπ, card_quotient_span_pow hπ] at h1
  exact Nat.pow_right_injective (by have := one_lt_q K; omega) h1

omit [IsUniformAddGroup K] in
/-- The valuation-level form of the order hypothesis: an integral element whose valuation is the
`k`-th power of the valuation of `π` is associated to `π ^ k`—the bridge from the shape a valuation
computation produces to the `Associated` hypothesis of the scaling law below
([Serre 1978, Lemma 2, p.1033][Serre1978]). -/
theorem associated_pow_of_valuation {π : 𝒪[K]} (hπ : Irreducible π) {a : 𝒪[K]} {k : ℕ}
    (hval : valuation K (a : K) = valuation K (π : K) ^ k) : Associated a (π ^ k) := by
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hπ.not_isUnit
  have hπne : valuation K (π : K) ≠ 0 :=
    (valuation K).ne_zero_iff.mpr (by exact_mod_cast hπ.ne_zero)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at hval
    exact absurd (hval.symm.trans (by simp)) (pow_ne_zero k hπne)
  obtain ⟨m, u, hu⟩ := exists_associated_pow hπ ha0
  -- associated elements have equal valuations, the unit contributing `1`
  have hvu : valuation K ((u : 𝒪[K]) : K) = 1 :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mp u.isUnit
  have hvm : valuation K (π : K) ^ m = valuation K (π : K) ^ k := by
    have h2 := congrArg (fun z : 𝒪[K] => valuation K (z : K)) hu
    rw [show ((a * (u : 𝒪[K]) : 𝒪[K]) : K) = (a : K) * ((u : 𝒪[K]) : K) from by push_cast; ring,
      map_mul, hvu, mul_one, hval,
      show ((π ^ m : 𝒪[K]) : K) = (π : K) ^ m from by push_cast; ring, map_pow] at h2
    exact h2.symm
  -- powers of a valuation `< 1` are pairwise distinct, so the exponents agree
  have hinj : ∀ i j : ℕ, i < j → valuation K (π : K) ^ j < valuation K (π : K) ^ i := by
    intro i j hij
    calc valuation K (π : K) ^ j
        = valuation K (π : K) ^ i * valuation K (π : K) ^ (j - i) := by
          rw [← pow_add]; congr 1; omega
      _ < valuation K (π : K) ^ i * 1 :=
          mul_lt_mul_of_pos_left (pow_lt_one₀ zero_le hπ1 (by omega))
            (zero_lt_iff.mpr (pow_ne_zero _ hπne))
      _ = valuation K (π : K) ^ i := mul_one _
  have hmk : m = k := by
    rcases Nat.lt_trichotomy m k with h | h | h
    · exact absurd hvm (ne_of_gt (hinj m k h))
    · exact h
    · exact absurd hvm (ne_of_lt (hinj k m h))
  rw [← hmk]
  exact ⟨u, hu⟩

/-! ## The index of an image lattice -/

omit [IsUniformAddGroup K] in
/-- The index of an image lattice: the quotient of the integer box by its image under `M` has
exactly `q ^ k` elements, where `k` is the `π`-adic order of `M.det`. Mathlib's Smith normal form
over the principal ideal ring `𝒪[K]` presents the quotient as a product of the residue rings of the
diagonal coefficients `a i`; their product is associated to `M.det` because the two embeddings of
the integer box into itself with image the lattice—the one through `M` and the one through the Smith
bases—differ by an automorphism, and `LinearMap.associated_det_comp_equiv` makes their determinants
associated. -/
theorem card_quotient_range {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝒪[K]) (hdet : M.det ≠ 0)
    {π : 𝒪[K]} (hπ : Irreducible π) {k : ℕ} (hk : Associated M.det (π ^ k)) :
    Nat.card ((Fin n → 𝒪[K]) ⧸ LinearMap.range (Matrix.mulVecLin M)) = q K ^ k := by
  classical
  have hinj : Function.Injective (Matrix.mulVecLin M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hx
  set N := LinearMap.range (Matrix.mulVecLin M) with hN
  set b := Pi.basisFun 𝒪[K] (Fin n) with hb
  set e : (Fin n → 𝒪[K]) ≃ₗ[𝒪[K]] ↥N := LinearEquiv.ofInjective _ hinj with he
  have hrank : finrank 𝒪[K] ↥N = finrank 𝒪[K] (Fin n → 𝒪[K]) := (e.finrank_eq).symm
  set a := Submodule.smithNormalFormCoeffs b hrank with ha
  -- the quotient splits into the residue rings of the diagonal coefficients
  have hcard : Nat.card ((Fin n → 𝒪[K]) ⧸ N) = ∏ i, Nat.card (𝒪[K] ⧸ Ideal.span {a i}) := by
    rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b hrank).toEquiv, Nat.card_pi]
  -- the product of the diagonal coefficients is associated to `det M`
  set b' := Submodule.smithNormalFormTopBasis b hrank with hb'
  set ab := Submodule.smithNormalFormBotBasis b hrank with hab
  set e' : (Fin n → 𝒪[K]) ≃ₗ[𝒪[K]] ↥N := b'.equiv ab (Equiv.refl _) with he'
  have hdiag : ∀ i, (N.subtype ∘ₗ (e' : (Fin n → 𝒪[K]) →ₗ[𝒪[K]] ↥N)) (b' i) = a i • b' i := by
    intro i
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, he', b'.equiv_apply, Equiv.refl_apply]
    exact Submodule.smithNormalFormBotBasis_def b hrank i
  have hdetf : LinearMap.det (N.subtype ∘ₗ (e' : (Fin n → 𝒪[K]) →ₗ[𝒪[K]] ↥N)) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', show LinearMap.toMatrix b' b'
      (N.subtype ∘ₗ (e' : (Fin n → 𝒪[K]) →ₗ[𝒪[K]] ↥N)) = Matrix.diagonal a from ?_,
      Matrix.det_diagonal]
    ext i j
    rw [LinearMap.toMatrix_apply, hdiag, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hsub : N.subtype ∘ₗ (e : (Fin n → 𝒪[K]) →ₗ[𝒪[K]] ↥N) = Matrix.mulVecLin M := rfl
  have hprod : Associated (∏ i, a i) M.det := by
    have h1 := LinearMap.associated_det_comp_equiv N.subtype e' e
    rw [hdetf, hsub, ← Matrix.toLin'_apply', LinearMap.det_toLin'] at h1
    exact h1
  -- the exponents add up to the order of the determinant
  have hane : ∀ i, a i ≠ 0 := fun i => Submodule.smithNormalFormCoeffs_ne_zero b hrank i
  choose ord hord using fun i => exists_associated_pow hπ (hane i)
  have hsum : Associated (π ^ ∑ i, ord i) (π ^ k) := by
    have h2 : Associated (π ^ ∑ i, ord i) (∏ i, a i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Associated.prod Finset.univ _ _ fun i _ => (hord i).symm
    exact (h2.trans hprod).trans hk
  rw [hcard]
  calc ∏ i, Nat.card (𝒪[K] ⧸ Ideal.span {a i})
      = ∏ i, q K ^ ord i := Finset.prod_congr rfl fun i _ => card_quotient_span hπ (hord i)
    _ = q K ^ ∑ i, ord i := by rw [Finset.prod_pow_eq_pow_sum]
    _ = q K ^ k := by rw [pow_eq_of_associated hπ hsum]

/-! ## The integer box, its lattices, and the balls -/

variable (K) in
/-- The integer box of the coefficient space—the normalizing set of the paper's measure, which
gives `𝒪[K]` volume `1` coordinatewise ([Serre 1978, p.1032][Serre1978]). -/
def integerBox (n : ℕ) : Set (Fin n → K) :=
  Set.univ.pi fun _ => (𝒪[K] : Set K)

/-- The image lattice `M · 𝒪^n` of an integral matrix, inside the coefficient space. -/
noncomputable def imageLattice {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝒪[K]) : Set (Fin n → K) :=
  (M.map (algebraMap 𝒪[K] K)).mulVec '' integerBox K n

/-- The coordinatewise closed ball around `x` of radius the `m`-th power of the valuation of `π`. -/
def ball {n : ℕ} (x : Fin n → K) (π : 𝒪[K]) (m : ℕ) : Set (Fin n → K) :=
  {y | ∀ i, valuation K (y i - x i) ≤ valuation K (π : K) ^ m}

/-- The coordinatewise box around the origin whose `i`-th radius is the `e i`-th power of the
valuation of `π`—the lattice whose `i`-th factor is `π ^ e i` times `𝒪[K]`, which is what a ball of
`integers L` becomes in the coordinates of a power basis (`le_addVal_mul_iff_coords`). -/
def box {n : ℕ} (π : 𝒪[K]) (e : Fin n → ℕ) : Set (Fin n → K) :=
  Set.univ.pi fun i => {z : K | valuation K z ≤ valuation K (π : K) ^ (e i)}

/-- The coordinatewise inclusion of the integer box into the coefficient space, as an additive
monoid homomorphism—the integral picture of the box. -/
def toCoeff {n : ℕ} : (Fin n → 𝒪[K]) →+ (Fin n → K) where
  toFun y := fun i => (y i : K)
  map_zero' := by funext i; simp
  map_add' y z := by funext i; simp

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
lemma toCoeff_apply {n : ℕ} (y : Fin n → 𝒪[K]) (i : Fin n) :
    toCoeff y i = (y i : K) := rfl

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
lemma toCoeff_injective {n : ℕ} : Function.Injective (toCoeff (K := K) (n := n)) := by
  intro y z hyz
  funext i
  exact Subtype.val_injective (congrFun hyz i)

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- The integer box is exactly the range of the integral picture. -/
lemma range_toCoeff {n : ℕ} : Set.range (toCoeff (K := K) (n := n)) = integerBox K n := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Set.mem_pi.mpr fun i _ => (y i).2
  · intro hx
    rw [integerBox, Set.mem_pi] at hx
    exact ⟨fun i => ⟨x i, hx i (Set.mem_univ i)⟩, rfl⟩

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- The algebra map commutes with multiplication by an integral matrix. -/
private lemma toCoeff_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝒪[K]) (y : Fin n → 𝒪[K]) :
    (M.map (algebraMap 𝒪[K] K)).mulVec (toCoeff y) = toCoeff (M.mulVec y) := by
  funext i
  simp only [toCoeff_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast
  rfl

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- The image lattice is the integral picture of the range submodule. -/
lemma imageLattice_eq_image_range {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝒪[K]) :
    imageLattice M = toCoeff '' (LinearMap.range (Matrix.mulVecLin M) : Set (Fin n → 𝒪[K])) := by
  rw [imageLattice, ← range_toCoeff, ← Set.image_univ, Set.image_image]
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨M.mulVec y, ⟨y, rfl⟩, (toCoeff_mulVec M y).symm⟩
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, Set.mem_univ y, toCoeff_mulVec M y⟩

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- Membership in an image lattice, in the integral picture: an integral vector lies in the image of
the integer box under `M` exactly when it lies in the range of `M` over `𝒪[K]`—the integral picture
being injective. -/
lemma toCoeff_mem_imageLattice_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝒪[K])
    (y : Fin n → 𝒪[K]) :
    toCoeff y ∈ imageLattice M ↔ y ∈ LinearMap.range (Matrix.mulVecLin M) := by
  rw [imageLattice_eq_image_range]
  exact ⟨fun ⟨z, hz, hzy⟩ => (toCoeff_injective hzy) ▸ hz, fun hy => ⟨y, hy, rfl⟩⟩

omit [IsUniformAddGroup K] in
/-- The image lattice sits inside the integer box, and is compact—the continuous image of the
compact box. -/
lemma isCompact_imageLattice {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝒪[K]) :
    IsCompact (imageLattice M) := by
  refine IsCompact.image ?_ ?_
  · exact isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[K]))
  · refine continuous_pi fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

/-! ## The volume of an image lattice -/

/-- The volume of an image lattice: the integer box is the disjoint union of the `q ^ k` translates
of its image under `M`, so the box has `q ^ k` times the volume of that image—for *any*
translation-invariant measure, no normalization needed. The index `q ^ k` is `card_quotient_range`;
the decomposition is the coset decomposition of the integer box modulo the lattice, transported
along the integral picture `toCoeff`, and the lattice is measurable because it is compact. -/
theorem measure_integerBox_eq_pow_mul {n : ℕ} [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (M : Matrix (Fin n) (Fin n) 𝒪[K]) (hdet : M.det ≠ 0) {π : 𝒪[K]} (hπ : Irreducible π)
    {k : ℕ} (hk : Associated M.det (π ^ k)) :
    μ (integerBox K n) = (q K : ℝ≥0∞) ^ k * μ (imageLattice M) := by
  classical
  set Lat := LinearMap.range (Matrix.mulVecLin M) with hLat
  have hcardQ : Nat.card ((Fin n → 𝒪[K]) ⧸ Lat) = q K ^ k := card_quotient_range M hdet hπ hk
  have : Finite ((Fin n → 𝒪[K]) ⧸ Lat) := Nat.finite_of_card_ne_zero (by
    rw [hcardQ]
    exact pow_ne_zero _ (by have := one_lt_q K; omega))
  have := Fintype.ofFinite ((Fin n → 𝒪[K]) ⧸ Lat)
  -- a system of coset representatives
  have hsurj : Function.Surjective
      (Submodule.Quotient.mk : (Fin n → 𝒪[K]) → (Fin n → 𝒪[K]) ⧸ Lat) :=
    Submodule.Quotient.mk_surjective Lat
  set rep := Function.surjInv hsurj with hrep
  have hrepeq : ∀ t, (Submodule.Quotient.mk (rep t) : (Fin n → 𝒪[K]) ⧸ Lat) = t := fun t =>
    Function.surjInv_eq hsurj t
  have hLimg := imageLattice_eq_image_range M
  -- membership in the lattice, in the integral picture
  have hmemL : ∀ y : Fin n → 𝒪[K], toCoeff y ∈ imageLattice M ↔ y ∈ Lat :=
    fun y => toCoeff_mem_imageLattice_iff M y
  -- the coset decomposition of the box
  have hdecomp : integerBox K n = ⋃ t, (toCoeff (rep t) +ᵥ imageLattice M) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := (range_toCoeff (K := K) (n := n)) ▸ hx
      refine ⟨Submodule.Quotient.mk y, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub,
        show toCoeff y - toCoeff (rep (Submodule.Quotient.mk y)) =
          toCoeff (y - rep (Submodule.Quotient.mk y)) from by rw [map_sub], hmemL]
      refine (Submodule.Quotient.mk_eq_zero Lat).mp ?_
      rw [Submodule.Quotient.mk_sub, hrepeq, sub_self]
    · rintro ⟨t, ht⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, hLimg] at ht
      obtain ⟨z, -, hz⟩ := ht
      have hxeq : x = toCoeff (rep t + z) := by
        rw [map_add, hz]
        abel
      rw [hxeq, ← range_toCoeff]
      exact ⟨rep t + z, rfl⟩
  -- the translates are pairwise disjoint, since the representatives are pairwise incongruent
  have hdisj : Pairwise (Function.onFun Disjoint fun t => toCoeff (rep t) +ᵥ imageLattice M) := by
    intro t t' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hxt hxt'
    apply hne
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, hLimg] at hxt hxt'
    obtain ⟨z, hzL, hz⟩ := hxt
    obtain ⟨z', hz'L, hz'⟩ := hxt'
    have hsub : rep t + z = rep t' + z' :=
      toCoeff_injective (by rw [map_add, map_add, hz, hz']; abel)
    rw [← hrepeq t, ← hrepeq t']
    have h1 : (Submodule.Quotient.mk (rep t + z) : (Fin n → 𝒪[K]) ⧸ Lat) =
        Submodule.Quotient.mk (rep t' + z') := by rw [hsub]
    rwa [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero Lat).mpr hzL,
      (Submodule.Quotient.mk_eq_zero Lat).mpr hz'L, add_zero, add_zero] at h1
  -- counting the cosets
  have hclosed : IsClosed (imageLattice M) := (isCompact_imageLattice M).isClosed
  rw [hdecomp, measure_iUnion hdisj fun t => (hclosed.vadd _).measurableSet]
  have hv : ∀ t, μ (toCoeff (rep t) +ᵥ imageLattice M) = μ (imageLattice M) := fun t =>
    measure_vadd _ _ _
  simp_rw [hv]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [← Nat.card_eq_fintype_card, hcardQ]
  push_cast
  ring

/-! ## The scaling law on boxes and on balls -/

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- Membership in a box, coordinate by coordinate. -/
theorem mem_box_iff {n : ℕ} (π : 𝒪[K]) (e : Fin n → ℕ) (w : Fin n → K) :
    w ∈ box π e ↔ ∀ i, valuation K (w i) ≤ valuation K (π : K) ^ (e i) := by
  rw [box, Set.mem_pi]
  exact ⟨fun h i => h i (Set.mem_univ i), fun h i _ => h i⟩

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- The lattice of a diagonal matrix is a box: multiplication by `π ^ e i` in the `i`-th coordinate
has image `π ^ e i` times `𝒪[K]` there, so the image lattice of a diagonal integral matrix of powers
is the coordinate box of the corresponding radii. -/
theorem imageLattice_diagonal {n : ℕ} {π : 𝒪[K]} (hπ : Irreducible π) (e : Fin n → ℕ) :
    imageLattice (Matrix.diagonal fun i => π ^ e i) = box π e := by
  have hπ0 : (π : K) ≠ 0 := by exact_mod_cast hπ.ne_zero
  have hvne : valuation K (π : K) ≠ 0 := (valuation K).ne_zero_iff.mpr hπ0
  have hmul : ∀ z : Fin n → K,
      ((Matrix.diagonal fun i => π ^ e i).map (algebraMap 𝒪[K] K)).mulVec z
        = fun i => (π : K) ^ e i * z i := by
    intro z
    rw [Matrix.diagonal_map (map_zero _)]
    funext i
    rw [Matrix.mulVec_diagonal,
      show (algebraMap 𝒪[K] K) (π ^ e i) = (π : K) ^ e i from by rw [map_pow]; rfl]
  ext w
  rw [mem_box_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    intro i
    rw [integerBox, Set.mem_pi] at hz
    rw [hmul z]
    dsimp only
    rw [map_mul, map_pow]
    exact mul_le_of_le_one_right' (((valuation K).mem_integer_iff _).mp (hz i (Set.mem_univ i)))
  · intro hw
    -- divide coordinatewise by `π ^ e i`
    have hzmem : ∀ i, w i / (π : K) ^ e i ∈ 𝒪[K] := by
      intro i
      refine ((valuation K).mem_integer_iff _).mpr ?_
      rw [map_div₀, map_pow]
      exact (div_le_one₀ (zero_lt_iff.mpr (pow_ne_zero _ hvne))).mpr (hw i)
    refine ⟨fun i => w i / (π : K) ^ e i, Set.mem_pi.mpr fun i _ => hzmem i, ?_⟩
    rw [hmul]
    funext i
    rw [mul_div_cancel₀ _ (pow_ne_zero _ hπ0)]

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- The determinant of a diagonal matrix of powers of the uniformizer. -/
private lemma det_diagonal_pow {n : ℕ} (π : 𝒪[K]) (e : Fin n → ℕ) :
    (Matrix.diagonal fun i => π ^ e i).det = π ^ (∑ i, e i) := by
  rw [Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]

/-- The volume of an image lattice: for a measure normalized on the integer box—the paper's
normalization giving `𝒪[K]` volume `1`, coordinatewise—the lattice of a matrix whose determinant
has `π`-adic order `k` has volume `1 / q ^ k` ([Serre 1978, p.1032][Serre1978]). -/
theorem measure_imageLattice_eq_inv_pow {n : ℕ} [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hnorm : μ (integerBox K n) = 1) (M : Matrix (Fin n) (Fin n) 𝒪[K]) (hdet : M.det ≠ 0)
    {π : 𝒪[K]} (hπ : Irreducible π) {k : ℕ} (hk : Associated M.det (π ^ k)) :
    μ (imageLattice M) = (q K : ℝ≥0∞)⁻¹ ^ k := by
  have h1 := measure_integerBox_eq_pow_mul μ M hdet hπ hk
  rw [hnorm] at h1
  rw [← ENNReal.inv_pow]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1.symm)

/-- The volume of a coordinate box: the diagonal case of the lattice volume, the box of radii
`π ^ e i` having volume `1 / q ^ (∑ i, e i)`. -/
theorem measure_box_eq_inv_pow {n : ℕ} [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hnorm : μ (integerBox K n) = 1)
    {π : 𝒪[K]} (hπ : Irreducible π) (e : Fin n → ℕ) :
    μ (box π e) = (q K : ℝ≥0∞)⁻¹ ^ (∑ i, e i) := by
  have hdet : (Matrix.diagonal fun i => π ^ e i).det ≠ 0 := by
    rw [det_diagonal_pow]
    exact pow_ne_zero _ hπ.ne_zero
  rw [← imageLattice_diagonal hπ]
  exact measure_imageLattice_eq_inv_pow μ hnorm _ hdet hπ (by rw [det_diagonal_pow])

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- A ball is a translate of the box of constant radii, i.e. of the scalar lattice `π^m · 𝒪^n`. -/
private lemma ball_eq_vadd {n : ℕ} (x : Fin n → K) {π : 𝒪[K]} (hπ : Irreducible π) (m : ℕ) :
    ball x π m = x +ᵥ imageLattice (Matrix.diagonal fun _ : Fin n => π ^ m) := by
  ext y
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, imageLattice_diagonal hπ,
    mem_box_iff]
  rfl

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- The `π`-adic order of the determinant of the scalar matrix `π^m · 1`, in its diagonal form. -/
private lemma det_diagonal_const {n : ℕ} (π : 𝒪[K]) (m : ℕ) :
    (Matrix.diagonal fun _ : Fin n => π ^ m).det = π ^ (m * n) := by
  rw [det_diagonal_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_comm]

/-- The form the change of variables consumes: an integral matrix whose determinant has
`π`-adic order `k` shrinks the volume of every ball by exactly `q ^ k`. Both the ball and its image
are translates of lattices—of the integer box scaled by `π ^ m`, and of its image under `M`, of
determinant orders `m * n` and `m * n + k`—so the two applications of
`measure_integerBox_eq_pow_mul` differ by the factor `q ^ k`, which is all that survives after the
common factor `q ^ (m * n)` is cancelled. -/
theorem measure_ball_eq_pow_mul {n : ℕ} [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (M : Matrix (Fin n) (Fin n) 𝒪[K]) (hdet : M.det ≠ 0) {π : 𝒪[K]} (hπ : Irreducible π)
    {k : ℕ} (hk : Associated M.det (π ^ k)) (x : Fin n → K) (m : ℕ) :
    μ (ball x π m) =
      (q K : ℝ≥0∞) ^ k * μ ((M.map (algebraMap 𝒪[K] K)).mulVec '' ball x π m) := by
  classical
  have hπ0 : π ≠ 0 := hπ.ne_zero
  set D := Matrix.diagonal fun _ : Fin n => π ^ m with hD
  have hdetD : D.det = π ^ (m * n) := det_diagonal_const π m
  have hdetD0 : D.det ≠ 0 := by rw [hdetD]; exact pow_ne_zero _ hπ0
  -- the image of the ball is a translate of the lattice of `M * D`
  have himg : (M.map (algebraMap 𝒪[K] K)).mulVec '' ball x π m =
      (M.map (algebraMap 𝒪[K] K)).mulVec x +ᵥ imageLattice (M * D) := by
    rw [ball_eq_vadd x hπ m]
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, imageLattice] at hu
      obtain ⟨z, hz, hzu⟩ := hu
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, imageLattice]
      refine ⟨z, hz, ?_⟩
      rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hzu, Matrix.mulVec_sub]
    · intro hw
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, imageLattice] at hw
      obtain ⟨z, hz, hzw⟩ := hw
      refine ⟨x + (D.map (algebraMap 𝒪[K] K)).mulVec z, ?_, ?_⟩
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, imageLattice]
        exact ⟨z, hz, by abel⟩
      · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.map_mul, hzw]
        abel
  -- the two lattice volumes
  have h1 : μ (integerBox K n) = (q K : ℝ≥0∞) ^ (m * n) * μ (imageLattice D) :=
    measure_integerBox_eq_pow_mul μ D hdetD0 hπ (by rw [hdetD])
  have h2 : μ (integerBox K n) = (q K : ℝ≥0∞) ^ (m * n + k) * μ (imageLattice (M * D)) := by
    refine measure_integerBox_eq_pow_mul μ (M * D) (by
      rw [Matrix.det_mul]
      exact mul_ne_zero hdet hdetD0) hπ ?_
    rw [Matrix.det_mul, hdetD, pow_add, mul_comm ((π : 𝒪[K]) ^ (m * n))]
    exact Associated.mul_right hk _
  -- cancel the common factor `q ^ (m * n)`
  have hq0 : (q K : ℝ≥0∞) ^ (m * n) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (by have := one_lt_q K; omega))
  have hqtop : (q K : ℝ≥0∞) ^ (m * n) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [himg, ball_eq_vadd x hπ m, ← hD, measure_vadd, measure_vadd]
  refine (ENNReal.mul_right_inj hq0 hqtop).mp ?_
  rw [← h1, h2, pow_add, mul_assoc]

end MassFormula
