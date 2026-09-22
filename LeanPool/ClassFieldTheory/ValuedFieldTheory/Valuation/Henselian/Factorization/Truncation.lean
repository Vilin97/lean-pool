/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
/-!
# coefficient truncation for the Hensel correction step

This file contains the finite coefficient-cutting step used in the
proof of Hensel's lemma: after the division step, coefficients already zero in
the residue field may be omitted to impose the required degree bound.
-/

noncomputable section

open scoped Polynomial
open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

/-- low-degree part of a polynomial up to degree `N`. -/
def henselFactorizationLowPart {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) : R[X] :=
  Finset.sum (Finset.range (N + 1)) fun i => Polynomial.monomial i (P.coeff i)

/-- coefficients at degrees kept by `lowPart`. -/
theorem henselFactorization_lowPart_coeff_of_le
    {R : Type*} [Semiring R] {N n : ℕ} (P : R[X]) (hn : n ≤ N) :
    (henselFactorizationLowPart N P).coeff n = P.coeff n := by
  classical
  unfold henselFactorizationLowPart
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _hb hbn
    simp [Polynomial.coeff_monomial, hbn]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

/-- coefficients above the cutoff vanish in `lowPart`. -/
theorem henselFactorization_lowPart_coeff_eq_zero_of_lt
    {R : Type*} [Semiring R] {N n : ℕ} (P : R[X]) (hn : N < n) :
    (henselFactorizationLowPart N P).coeff n = 0 := by
  classical
  unfold henselFactorizationLowPart
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero ?_
  intro b hb
  have hbn : b ≠ n := by
    intro hbn
    have hn_le : n ≤ N := Nat.lt_succ_iff.mp (by simpa [hbn] using hb)
    exact (Nat.not_lt_of_ge hn_le) hn
  simp [Polynomial.coeff_monomial, hbn]

/-- `lowPart` has the intended degree bound. -/
theorem henselFactorization_lowPart_natDegree_le
    {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) :
    (henselFactorizationLowPart N P).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact henselFactorization_lowPart_coeff_eq_zero_of_lt (P := P) hn

/-- omitting high coefficients already in the kernel does not
change the residual polynomial. -/
theorem henselFactorization_lowPart_map_eq_of_high_coeff_mem_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (N : ℕ) (P : R[X])
    (hhigh : ∀ n : ℕ, N < n → P.coeff n ∈ RingHom.ker φ) :
    (henselFactorizationLowPart N P).map φ = P.map φ := by
  ext n
  by_cases hn : n ≤ N
  · rw [Polynomial.coeff_map, Polynomial.coeff_map,
      henselFactorization_lowPart_coeff_of_le (P := P) hn]
  · have hlt : N < n := Nat.lt_of_not_ge hn
    have hker := hhigh n hlt
    rw [Polynomial.coeff_map, Polynomial.coeff_map,
      henselFactorization_lowPart_coeff_eq_zero_of_lt (P := P) hlt]
    rw [RingHom.mem_ker] at hker
    simpa using hker.symm

/-- residue-map form of high-coefficient truncation. -/
theorem henselFactorization_lowPart_residue_map_eq_of_high_coeff_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] (N : ℕ) (P : R[X])
    (hhigh : ∀ n : ℕ, N < n → P.coeff n ∈ IsLocalRing.maximalIdeal R) :
    (henselFactorizationLowPart N P).map (IsLocalRing.residue R) =
      P.map (IsLocalRing.residue R) := by
  apply henselFactorization_lowPart_map_eq_of_high_coeff_mem_ker
  intro n hn
  have h := hhigh n hn
  rwa [IsLocalRing.ker_residue]

/-- kernel-level truncation: the correction congruence
survives replacing a provisional correction polynomial by its low-degree part
when the omitted coefficients already lie in the same coefficient-map kernel. -/
theorem henselFactorization_correction_after_lowPart_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    {g0 h0 fn p Q : R[X]} (N : ℕ)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ RingHom.ker φ)
    (hhigh : ∀ n : ℕ, N < n → Q.coeff n ∈ RingHom.ker φ) :
    (henselFactorizationLowPart N Q).natDegree ≤ N ∧
      ∀ n : ℕ,
        (g0 * henselFactorizationLowPart N Q + h0 * p - fn).coeff n ∈
          RingHom.ker φ := by
  refine ⟨henselFactorization_lowPart_natDegree_le N Q, ?_⟩
  have hmapQ :=
    henselFactorization_lowPart_map_eq_of_high_coeff_mem_ker φ N Q hhigh
  have hmapOld :
      (g0 * Q + h0 * p - fn).map φ = 0 := by
    exact (henselFactorization_map_eq_zero_iff_coeff_mem_ker
      φ (g0 * Q + h0 * p - fn)).2 hcorr
  have hmapNew :
      (g0 * henselFactorizationLowPart N Q + h0 * p - fn).map φ = 0 := by
    calc
      (g0 * henselFactorizationLowPart N Q + h0 * p - fn).map φ =
          g0.map φ * (henselFactorizationLowPart N Q).map φ +
            h0.map φ * p.map φ - fn.map φ := by
        exact henselFactorization_map_mul_add_mul_sub φ g0 h0
          (henselFactorizationLowPart N Q) p fn
      _ = g0.map φ * Q.map φ + h0.map φ * p.map φ - fn.map φ := by
        rw [hmapQ]
      _ = (g0 * Q + h0 * p - fn).map φ := by
        exact (henselFactorization_map_mul_add_mul_sub φ g0 h0 Q p fn).symm
      _ = 0 := hmapOld
  intro n
  exact (henselFactorization_map_eq_zero_iff_coeff_mem_ker
    φ (g0 * henselFactorizationLowPart N Q + h0 * p - fn)).1 hmapNew n

/-- ideal-level truncation: the correction congruence survives
replacing a provisional correction polynomial by its low-degree part when the
omitted coefficients already lie in the same ideal. -/
theorem henselFactorization_correction_after_lowPart_ideal
    {R : Type*} [CommRing R] {I : Ideal R}
    {g0 h0 fn p Q : R[X]} (N : ℕ)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ I)
    (hhigh : ∀ n : ℕ, N < n → Q.coeff n ∈ I) :
    (henselFactorizationLowPart N Q).natDegree ≤ N ∧
      ∀ n : ℕ,
        (g0 * henselFactorizationLowPart N Q + h0 * p - fn).coeff n ∈ I := by
  let φ : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hcorrKer :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ RingHom.ker φ := by
    intro n
    exact (henselFactorization_mem_ker_quotient_mk_iff I _).2 (hcorr n)
  have hhighKer :
      ∀ n : ℕ, N < n → Q.coeff n ∈ RingHom.ker φ := by
    intro n hn
    exact (henselFactorization_mem_ker_quotient_mk_iff I _).2 (hhigh n hn)
  rcases henselFactorization_correction_after_lowPart_ker
      φ (N := N) (g0 := g0) (h0 := h0) (fn := fn)
      (p := p) (Q := Q) hcorrKer hhighKer with
    ⟨hdeg, hker⟩
  refine ⟨hdeg, ?_⟩
  intro n
  exact (henselFactorization_mem_ker_quotient_mk_iff I _).1 (hker n)

/-- principal-ideal truncation: if the provisional correction
is congruent modulo `(π)` and all omitted coefficients are divisible by `π`,
then the truncated correction keeps the same congruence modulo `(π)`. -/
theorem henselFactorization_correction_after_lowPart_span_singleton
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 fn p Q : R[X]} (N : ℕ)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R))
    (hhigh : ∀ n : ℕ, N < n → Q.coeff n ∈
      Ideal.span ({π} : Set R)) :
    (henselFactorizationLowPart N Q).natDegree ≤ N ∧
      ∀ n : ℕ,
        (g0 * henselFactorizationLowPart N Q + h0 * p - fn).coeff n ∈
          Ideal.span ({π} : Set R) := by
  exact henselFactorization_correction_after_lowPart_ideal
    (I := Ideal.span ({π} : Set R)) N hcorr hhigh

/-- residue-field degree division: if the product with a
nonzero degree-`m` polynomial has degree at most `d`, then the right factor
has degree at most `d - m`. -/
theorem henselFactorization_natDegree_right_le_tsub_of_mul_natDegree_le
    {k : Type*} [Field k] {g Q : k[X]} {m d : ℕ}
    (hgdeg : g.natDegree = m) (hg : g ≠ 0)
    (hprod : (g * Q).natDegree ≤ d) :
    Q.natDegree ≤ d - m := by
  by_cases hQ : Q = 0
  · simp [hQ]
  · have hsum : m + Q.natDegree ≤ d := by
      simpa [hgdeg, Polynomial.natDegree_mul hg hQ] using hprod
    exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hsum)

/-- unit-leading degree division over an arbitrary
commutative ring: if the product with a degree-`m` polynomial whose leading
coefficient is a unit has degree at most `d`, then the right factor has degree
at most `d - m`.  This is the form needed over `O/(π)` in the iterative proof. -/
theorem henselFactorization_natDegree_right_le_tsub_of_unit_leading_mul_natDegree_le
    {R : Type*} [CommRing R] {g Q : R[X]} {m d : ℕ}
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m)
    (hprod : (g * Q).natDegree ≤ d) :
    Q.natDegree ≤ d - m := by
  by_cases hQ : Q = 0
  · simp [hQ]
  rcases henselFactorization_monic_normalization_of_unit_leadingCoeff
      (g := g) hgunit with
    ⟨u, _hu, hmonic, _hdegree, hnatDegree⟩
  let G : R[X] := Polynomial.C (((u⁻¹ : Rˣ) : R)) * g
  have hGmonic : G.Monic := by
    simpa [G] using hmonic
  have hGnat : G.natDegree = m := by
    simpa [G, hgdeg] using hnatDegree
  have hinvUnit : IsUnit (((u⁻¹ : Rˣ) : R)) := ⟨u⁻¹, rfl⟩
  have hGprod : (G * Q).natDegree ≤ d := by
    have hrewrite :
        G * Q = Polynomial.C (((u⁻¹ : Rˣ) : R)) * (g * Q) := by
      dsimp [G]
      ring
    rw [hrewrite, Polynomial.natDegree_C_mul_of_isUnit hinvUnit]
    exact hprod
  have hsum : m + Q.natDegree ≤ d := by
    have hmul := hGmonic.natDegree_mul' hQ
    rw [hGnat] at hmul
    simpa [hmul] using hGprod
  exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hsum)

/-- a unit-leading polynomial remains unit-leading with the
same natural degree after mapping to a nontrivial target ring.  This supplies
the unit-leading input used over `O/(π)`. -/
theorem henselFactorization_map_unit_leadingCoeff_natDegree_eq
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) {g : R[X]} {m : ℕ}
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m) :
    IsUnit (g.map φ).leadingCoeff ∧ (g.map φ).natDegree = m := by
  have hlead :
      (g.map φ).leadingCoeff = φ g.leadingCoeff :=
    Polynomial.leadingCoeff_map_eq_of_isUnit_leadingCoeff φ hgunit
  have hnat :
      (g.map φ).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff φ hgunit
  exact ⟨by
    rw [hlead]
    exact IsUnit.map φ hgunit, by
    rw [hnat, hgdeg]⟩

/-- quotient specialization of
`henselFactorization_map_unit_leadingCoeff_natDegree_eq`. -/
theorem henselFactorization_quotient_unit_leadingCoeff_natDegree_eq
    {R : Type*} [CommRing R] {I : Ideal R} [Nontrivial (R ⧸ I)]
    {g : R[X]} {m : ℕ}
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m) :
    IsUnit (g.map (Ideal.Quotient.mk I)).leadingCoeff ∧
      (g.map (Ideal.Quotient.mk I)).natDegree = m :=
  henselFactorization_map_unit_leadingCoeff_natDegree_eq
    (Ideal.Quotient.mk I) hgunit hgdeg

/-- if `π` lies in the maximal ideal of a local ring, then
the quotient `O/(π)` is nontrivial.  This is the displayed-factor source for the
nontriviality needed in the degree argument modulo `(π)`. -/
theorem henselFactorization_span_singleton_quotient_nontrivial_of_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    (hπ : π ∈ IsLocalRing.maximalIdeal R) :
    Nontrivial (R ⧸ Ideal.span ({π} : Set R)) := by
  rw [Ideal.Quotient.nontrivial_iff]
  intro htop
  have hle : Ideal.span ({π} : Set R) ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    simpa [hx] using hπ
  have htop_le :
      (⊤ : Ideal R) ≤ IsLocalRing.maximalIdeal R := by
    simpa [htop] using hle
  have hmaxTop : IsLocalRing.maximalIdeal R = ⊤ :=
    le_antisymm le_top htop_le
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmaxTop

/-- local-ring specialization: a unit-leading polynomial of
degree `m` stays unit-leading of degree `m` after reducing modulo `(π)`, for
`π` in the maximal ideal. -/
theorem henselFactorization_span_singleton_quotient_unit_leadingCoeff_natDegree_eq
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    {g : R[X]} {m : ℕ}
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m) :
    IsUnit
        ((g.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff) ∧
      (g.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m := by
  let : Nontrivial (R ⧸ Ideal.span ({π} : Set R)) :=
    henselFactorization_span_singleton_quotient_nontrivial_of_mem_maximalIdeal hπ
  exact henselFactorization_quotient_unit_leadingCoeff_natDegree_eq
    (I := Ideal.span ({π} : Set R)) hgunit hgdeg

/-- residual degree bound for the polynomial
`fn - h0 * p` that appears after the division step. -/
theorem henselFactorization_residue_sub_mul_natDegree_le
    {R : Type*} [CommRing R] [IsLocalRing R]
    {fn h0 P : R[X]} {a b d : ℕ}
    (hfn : (fn.map (IsLocalRing.residue R)).natDegree ≤ d)
    (hh0 : (h0.map (IsLocalRing.residue R)).natDegree ≤ a)
    (hP : (P.map (IsLocalRing.residue R)).natDegree ≤ b)
    (hab : a + b ≤ d) :
    ((fn - h0 * P).map (IsLocalRing.residue R)).natDegree ≤ d := by
  have hmul :
      (h0.map (IsLocalRing.residue R) *
        P.map (IsLocalRing.residue R)).natDegree ≤ d :=
    (Polynomial.natDegree_mul_le_of_le hh0 hP).trans hab
  have hmap :
      (fn - h0 * P).map (IsLocalRing.residue R) =
        fn.map (IsLocalRing.residue R) -
          h0.map (IsLocalRing.residue R) * P.map (IsLocalRing.residue R) := by
    exact henselFactorization_map_sub_mul (IsLocalRing.residue R) fn h0 P
  rw [hmap]
  simpa using
    (Polynomial.natDegree_sub_le_of_le
      (p := fn.map (IsLocalRing.residue R))
      (q := h0.map (IsLocalRing.residue R) *
        P.map (IsLocalRing.residue R)) hfn hmul)

/-- mapped degree bound for the polynomial `fn - h0*p` from
degree bounds already available before mapping.  This is the quotient-level
replacement for the residue-field degree bound in the principal `(π)` route. -/
theorem henselFactorization_map_sub_mul_natDegree_le_of_degree_bounds
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {fn h0 P : R[X]} {a b d : ℕ}
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ a)
    (hP : P.natDegree ≤ b)
    (hab : a + b ≤ d) :
    ((fn - h0 * P).map φ).natDegree ≤ d := by
  have hfnmap : (fn.map φ).natDegree ≤ d :=
    Polynomial.natDegree_map_le.trans hfn
  have hh0map : (h0.map φ).natDegree ≤ a :=
    Polynomial.natDegree_map_le.trans hh0
  have hPmap : (P.map φ).natDegree ≤ b :=
    Polynomial.natDegree_map_le.trans hP
  have hmul :
      (h0.map φ * P.map φ).natDegree ≤ d :=
    (Polynomial.natDegree_mul_le_of_le hh0map hPmap).trans hab
  have hmap :
      (fn - h0 * P).map φ =
        fn.map φ - h0.map φ * P.map φ := by
    exact henselFactorization_map_sub_mul φ fn h0 P
  rw [hmap]
  simpa using
    (Polynomial.natDegree_sub_le_of_le
      (p := fn.map φ) (q := h0.map φ * P.map φ) hfnmap hmul)

/-- quotient specialization of the degree bound for
`fn - h0*p` used before truncating the Hensel correction. -/
theorem henselFactorization_span_singleton_quotient_sub_mul_natDegree_le_of_degree_bounds
    {R : Type*} [CommRing R] {π : R}
    {fn h0 P : R[X]} {a b d : ℕ}
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ a)
    (hP : P.natDegree ≤ b)
    (hab : a + b ≤ d) :
    ((fn - h0 * P).map
      (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d :=
  henselFactorization_map_sub_mul_natDegree_le_of_degree_bounds
    (Ideal.Quotient.mk (Ideal.span ({π} : Set R))) hfn hh0 hP hab

/-- the correction congruence can be read in the product form
needed for the high-coefficient degree argument. -/
theorem henselFactorization_product_congruence_of_correction
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 h0 fn p Q : R[X]}
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ IsLocalRing.maximalIdeal R) :
    ∀ n : ℕ, (g0 * Q - (fn - h0 * p)).coeff n ∈
      IsLocalRing.maximalIdeal R := by
  intro n
  have heq : g0 * Q - (fn - h0 * p) = g0 * Q + h0 * p - fn := by
    ring
  rw [heq]
  exact hcorr n

/-- high-coefficient source for the correction truncation:
if `g0 * Q` is congruent to a polynomial of residual degree at most `d`, and
the residual degree of `g0` is `m`, then every coefficient of `Q` above
`d - m` lies in the maximal ideal. -/
theorem henselFactorization_high_coeff_mem_maximalIdeal_of_product_congruence_degree
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 Q A : R[X]} {m d : ℕ}
    (hgdeg : (g0.map (IsLocalRing.residue R)).natDegree = m)
    (hg : g0.map (IsLocalRing.residue R) ≠ 0)
    (hcong : ∀ n : ℕ, (g0 * Q - A).coeff n ∈ IsLocalRing.maximalIdeal R)
    (hAdeg : (A.map (IsLocalRing.residue R)).natDegree ≤ d) :
    ∀ n : ℕ, d - m < n → Q.coeff n ∈ IsLocalRing.maximalIdeal R := by
  have hmap :
      (g0 * Q - A).map (IsLocalRing.residue R) = 0 := by
    apply (henselFactorization_map_eq_zero_iff_coeff_mem_ker
      (IsLocalRing.residue R) (g0 * Q - A)).2
    intro n
    have h := hcong n
    rwa [IsLocalRing.ker_residue]
  have hsub :
      g0.map (IsLocalRing.residue R) * Q.map (IsLocalRing.residue R) -
        A.map (IsLocalRing.residue R) = 0 := by
    simpa [henselFactorization_map_mul_sub] using hmap
  have hprod_eq :
      g0.map (IsLocalRing.residue R) * Q.map (IsLocalRing.residue R) =
        A.map (IsLocalRing.residue R) :=
    sub_eq_zero.mp hsub
  have hprod_degree :
      (g0.map (IsLocalRing.residue R) * Q.map (IsLocalRing.residue R)).natDegree ≤ d := by
    rw [hprod_eq]
    exact hAdeg
  have hQdeg :
      (Q.map (IsLocalRing.residue R)).natDegree ≤ d - m :=
    henselFactorization_natDegree_right_le_tsub_of_mul_natDegree_le
      (g := g0.map (IsLocalRing.residue R))
      (Q := Q.map (IsLocalRing.residue R)) hgdeg hg hprod_degree
  intro n hn
  have hcoeff :
      (Q.map (IsLocalRing.residue R)).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQdeg hn)
  rw [Polynomial.coeff_map] at hcoeff
  have hker : Q.coeff n ∈ RingHom.ker (IsLocalRing.residue R) := by
    rw [RingHom.mem_ker]
    exact hcoeff
  rwa [IsLocalRing.ker_residue] at hker

/-- high-coefficient source modulo `(π)`: if `g0 * Q` is
congruent to a polynomial of degree at most `d` modulo `(π)`, and `g0` has
degree `m` with unit leading coefficient after reduction modulo `(π)`, then
every coefficient of `Q` above `d - m` is divisible by `π`. -/
theorem henselFactorization_high_coeff_mem_span_singleton_of_product_congruence_degree
    {R : Type*} [CommRing R] {π : R}
    {g0 Q A : R[X]} {m d : ℕ}
    (hgunit :
      IsUnit
        ((g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff))
    (hgdeg :
      (g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m)
    (hcong : ∀ n : ℕ, (g0 * Q - A).coeff n ∈
      Ideal.span ({π} : Set R))
    (hAdeg :
      (A.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d) :
    ∀ n : ℕ, d - m < n → Q.coeff n ∈ Ideal.span ({π} : Set R) := by
  let φ : R →+* R ⧸ Ideal.span ({π} : Set R) :=
    Ideal.Quotient.mk (Ideal.span ({π} : Set R))
  have hmap :
      (g0 * Q - A).map φ = 0 := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_zero_iff_coeff_mem
        (Ideal.span ({π} : Set R)) (g0 * Q - A)).2 hcong
  have hsub :
      g0.map φ * Q.map φ - A.map φ = 0 := by
    simpa [henselFactorization_map_mul_sub] using hmap
  have hprod_eq : g0.map φ * Q.map φ = A.map φ :=
    sub_eq_zero.mp hsub
  have hprod_degree : (g0.map φ * Q.map φ).natDegree ≤ d := by
    rw [hprod_eq]
    exact hAdeg
  have hQdeg :
      (Q.map φ).natDegree ≤ d - m :=
    henselFactorization_natDegree_right_le_tsub_of_unit_leading_mul_natDegree_le
      (g := g0.map φ) (Q := Q.map φ) (m := m) (d := d)
      (by simpa [φ] using hgunit) (by simpa [φ] using hgdeg) hprod_degree
  intro n hn
  have hcoeff : (Q.map φ).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQdeg hn)
  exact
    (henselFactorization_quotient_map_coeff_eq_zero_iff_coeff_mem
      (Ideal.span ({π} : Set R)) Q n).1 (by simpa [φ] using hcoeff)

/-- high-coefficient source specialized to the correction
congruence produced by the division step. -/
theorem henselFactorization_high_coeff_mem_maximalIdeal_of_correction_degree
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 h0 fn p Q : R[X]} {m d : ℕ}
    (hgdeg : (g0.map (IsLocalRing.residue R)).natDegree = m)
    (hg : g0.map (IsLocalRing.residue R) ≠ 0)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        IsLocalRing.maximalIdeal R)
    (hAdeg : ((fn - h0 * p).map (IsLocalRing.residue R)).natDegree ≤ d) :
    ∀ n : ℕ, d - m < n → Q.coeff n ∈ IsLocalRing.maximalIdeal R := by
  exact henselFactorization_high_coeff_mem_maximalIdeal_of_product_congruence_degree
    (g0 := g0) (Q := Q) (A := fn - h0 * p)
    (m := m) (d := d) hgdeg hg
    (henselFactorization_product_congruence_of_correction hcorr) hAdeg

/-- high-coefficient source modulo `(π)` specialized to the
correction congruence produced by the division step. -/
theorem henselFactorization_high_coeff_mem_span_singleton_of_correction_degree
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 fn p Q : R[X]} {m d : ℕ}
    (hgunit :
      IsUnit
        ((g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff))
    (hgdeg :
      (g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R))
    (hAdeg :
      ((fn - h0 * p).map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d) :
    ∀ n : ℕ, d - m < n → Q.coeff n ∈ Ideal.span ({π} : Set R) := by
  have hcong :
      ∀ n : ℕ, (g0 * Q - (fn - h0 * p)).coeff n ∈
        Ideal.span ({π} : Set R) := by
    intro n
    have heq : g0 * Q - (fn - h0 * p) = g0 * Q + h0 * p - fn := by
      ring
    rw [heq]
    exact hcorr n
  exact henselFactorization_high_coeff_mem_span_singleton_of_product_congruence_degree
    (π := π) (g0 := g0) (Q := Q) (A := fn - h0 * p)
    (m := m) (d := d) hgunit hgdeg hcong hAdeg

/-- one-step degree truncation modulo `(π)`: under the
principal correction congruence, the quotient-degree bound for `fn - h0*p`,
and the unit-leading degree data for `g0` modulo `(π)`, the low-degree part of
`Q` has degree at most `d-m` and keeps the correction congruence modulo `(π)`. -/
theorem henselFactorization_correction_after_degree_truncation_span_singleton
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 fn p Q : R[X]} {m d : ℕ}
    (hgunit :
      IsUnit
        ((g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff))
    (hgdeg :
      (g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R))
    (hAdeg :
      ((fn - h0 * p).map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d) :
    (henselFactorizationLowPart (d - m) Q).natDegree ≤ d - m ∧
      ∀ n : ℕ,
        (g0 * henselFactorizationLowPart (d - m) Q + h0 * p - fn).coeff n ∈
          Ideal.span ({π} : Set R) := by
  exact henselFactorization_correction_after_lowPart_span_singleton
    (π := π) (N := d - m) hcorr
    (henselFactorization_high_coeff_mem_span_singleton_of_correction_degree
      (π := π) (g0 := g0) (h0 := h0) (fn := fn) (p := p)
      (Q := Q) (m := m) (d := d) hgunit hgdeg hcorr hAdeg)

/-- principal-ideal one-step correction after Bezout and
division.  This is the displayed-factor route: the displayed factor
`a*g0 + b*h0 - 1 = C π * e`, not an equality `m = (π)`, supplies the
correction congruence modulo `(π)`. -/
theorem henselFactorization_correction_after_division_degree_truncation_span_singleton
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    {a b g0 h0 fn q p e : R[X]} {m d : ℕ}
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hgunit : IsUnit g0.leadingCoeff)
    (hg0nat : g0.natDegree = m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hdiv : b * fn = g0 * q + p)
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ d - m)
    (hp : p.natDegree ≤ m)
    (hmd : m ≤ d) :
    (henselFactorizationLowPart (d - m) (a * fn + h0 * q)).natDegree ≤ d - m ∧
      ∀ n : ℕ,
        (g0 * henselFactorizationLowPart (d - m) (a * fn + h0 * q) +
            h0 * p - fn).coeff n ∈ Ideal.span ({π} : Set R) := by
  rcases henselFactorization_span_singleton_quotient_unit_leadingCoeff_natDegree_eq
      (π := π) hπ hgunit hg0nat with
    ⟨hgunitQuot, hgdegQuot⟩
  have hcorr :
      ∀ n : ℕ, (g0 * (a * fn + h0 * q) + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R) :=
    henselFactorization_correction_congruence_span_singleton_after_division
      (π := π) hbezFactor hdiv
  have hAdeg :
      ((fn - h0 * p).map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d :=
    henselFactorization_span_singleton_quotient_sub_mul_natDegree_le_of_degree_bounds
      (π := π) (fn := fn) (h0 := h0) (P := p)
      (a := d - m) (b := m) (d := d) hfn hh0 hp (by
        rw [Nat.sub_add_cancel hmd])
  exact henselFactorization_correction_after_degree_truncation_span_singleton
    (π := π) (g0 := g0) (h0 := h0) (fn := fn) (p := p)
    (Q := a * fn + h0 * q) (m := m) (d := d)
    hgunitQuot hgdegQuot hcorr hAdeg

/-- the correction congruence survives replacing a provisional
correction polynomial by its low-degree part when the omitted coefficients are
already zero in the residue field. -/
theorem henselFactorization_correction_after_lowPart
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 h0 fn p Q : R[X]} (N : ℕ)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ IsLocalRing.maximalIdeal R)
    (hhigh : ∀ n : ℕ, N < n → Q.coeff n ∈ IsLocalRing.maximalIdeal R) :
    (henselFactorizationLowPart N Q).natDegree ≤ N ∧
      ∀ n : ℕ,
        (g0 * henselFactorizationLowPart N Q + h0 * p - fn).coeff n ∈
          IsLocalRing.maximalIdeal R := by
  refine ⟨henselFactorization_lowPart_natDegree_le N Q, ?_⟩
  have hmapQ :=
    henselFactorization_lowPart_residue_map_eq_of_high_coeff_mem_maximalIdeal
      N Q hhigh
  have hmapOld :
      (g0 * Q + h0 * p - fn).map (IsLocalRing.residue R) = 0 := by
    apply (henselFactorization_map_eq_zero_iff_coeff_mem_ker
      (IsLocalRing.residue R) (g0 * Q + h0 * p - fn)).2
    intro n
    have h := hcorr n
    rwa [IsLocalRing.ker_residue]
  have hmapNew :
      (g0 * henselFactorizationLowPart N Q + h0 * p - fn).map
        (IsLocalRing.residue R) = 0 := by
    calc
      (g0 * henselFactorizationLowPart N Q + h0 * p - fn).map
          (IsLocalRing.residue R) =
          g0.map (IsLocalRing.residue R) *
            (henselFactorizationLowPart N Q).map (IsLocalRing.residue R) +
              h0.map (IsLocalRing.residue R) * p.map (IsLocalRing.residue R) -
                fn.map (IsLocalRing.residue R) := by
        exact henselFactorization_map_mul_add_mul_sub (IsLocalRing.residue R) g0 h0
          (henselFactorizationLowPart N Q) p fn
      _ = g0.map (IsLocalRing.residue R) * Q.map (IsLocalRing.residue R) +
            h0.map (IsLocalRing.residue R) * p.map (IsLocalRing.residue R) -
              fn.map (IsLocalRing.residue R) := by
        rw [hmapQ]
      _ = (g0 * Q + h0 * p - fn).map (IsLocalRing.residue R) := by
        exact (henselFactorization_map_mul_add_mul_sub (IsLocalRing.residue R) g0 h0 Q p fn).symm
      _ = 0 := hmapOld
  intro n
  have hker :=
    (henselFactorization_map_eq_zero_iff_coeff_mem_ker
      (IsLocalRing.residue R)
      (g0 * henselFactorizationLowPart N Q + h0 * p - fn)).1 hmapNew n
  rwa [IsLocalRing.ker_residue] at hker

/-- one-step degree truncation of the provisional correction:
under the correction congruence and the residual degree bound for
`fn - h0*p`, the low-degree part of `Q` has degree at most `d - m` and keeps
the correction congruence. -/
theorem henselFactorization_correction_after_degree_truncation
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 h0 fn p Q : R[X]} {m d : ℕ}
    (hgdeg : (g0.map (IsLocalRing.residue R)).natDegree = m)
    (hg : g0.map (IsLocalRing.residue R) ≠ 0)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        IsLocalRing.maximalIdeal R)
    (hAdeg : ((fn - h0 * p).map (IsLocalRing.residue R)).natDegree ≤ d) :
    (henselFactorizationLowPart (d - m) Q).natDegree ≤ d - m ∧
      ∀ n : ℕ,
        (g0 * henselFactorizationLowPart (d - m) Q + h0 * p - fn).coeff n ∈
          IsLocalRing.maximalIdeal R := by
  exact henselFactorization_correction_after_lowPart
    (N := d - m) hcorr
    (henselFactorization_high_coeff_mem_maximalIdeal_of_correction_degree
      (g0 := g0) (h0 := h0) (fn := fn) (p := p) (Q := Q)
      (m := m) (d := d) hgdeg hg hcorr hAdeg)

/-- one-step correction after Bezout and division.  If
`b*fn = g0*q + p` is the division output and the residual degree bounds from
the proof are available, then the truncated provisional correction has
degree at most `d-m` and gives the required congruence. -/
theorem henselFactorization_correction_after_division_degree_truncation
    {R : Type*} [CommRing R] [IsLocalRing R]
    {a b g0 h0 fn q p : R[X]} {m d : ℕ}
    (hgdeg : (g0.map (IsLocalRing.residue R)).natDegree = m)
    (hg : g0.map (IsLocalRing.residue R) ≠ 0)
    (hbez : (a * g0 + b * h0).map (IsLocalRing.residue R) = 1)
    (hdiv : b * fn = g0 * q + p)
    (hfn : (fn.map (IsLocalRing.residue R)).natDegree ≤ d)
    (hh0 : (h0.map (IsLocalRing.residue R)).natDegree ≤ d - m)
    (hp : (p.map (IsLocalRing.residue R)).natDegree ≤ m)
    (hmd : m ≤ d) :
    (henselFactorizationLowPart (d - m) (a * fn + h0 * q)).natDegree ≤ d - m ∧
      ∀ n : ℕ,
        (g0 * henselFactorizationLowPart (d - m) (a * fn + h0 * q) +
            h0 * p - fn).coeff n ∈ IsLocalRing.maximalIdeal R := by
  have hcorr :
      ∀ n : ℕ, (g0 * (a * fn + h0 * q) + h0 * p - fn).coeff n ∈
        IsLocalRing.maximalIdeal R :=
    henselFactorization_correction_mem_maximalIdeal_after_division hbez hdiv
  have hAdeg :
      ((fn - h0 * p).map (IsLocalRing.residue R)).natDegree ≤ d :=
    henselFactorization_residue_sub_mul_natDegree_le
      (fn := fn) (h0 := h0) (P := p)
      (a := d - m) (b := m) (d := d) hfn hh0 hp (by
        rw [Nat.sub_add_cancel hmd])
  exact henselFactorization_correction_after_degree_truncation
    (g0 := g0) (h0 := h0) (fn := fn) (p := p)
    (Q := a * fn + h0 * q) (m := m) (d := d)
    hgdeg hg hcorr hAdeg

/-- replacement of the initial lifted factors by the current
inductive approximants in the correction congruence.  If `g` and `h` still
reduce to `g0` and `h0`, then a correction congruence for `g0,h0` is also a
correction congruence for `g,h`. -/
theorem henselFactorization_correction_congruence_replace_initial_factors
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 h0 g h fn p q : R[X]}
    (hg : ∀ n : ℕ, (g - g0).coeff n ∈ IsLocalRing.maximalIdeal R)
    (hh : ∀ n : ℕ, (h - h0).coeff n ∈ IsLocalRing.maximalIdeal R)
    (hcorr :
      ∀ n : ℕ, (g0 * q + h0 * p - fn).coeff n ∈
        IsLocalRing.maximalIdeal R) :
    ∀ n : ℕ, (g * q + h * p - fn).coeff n ∈
      IsLocalRing.maximalIdeal R := by
  have hgmap : g.map (IsLocalRing.residue R) =
      g0.map (IsLocalRing.residue R) := by
    have hzero : (g - g0).map (IsLocalRing.residue R) = 0 := by
      apply (henselFactorization_map_eq_zero_iff_coeff_mem_ker
        (IsLocalRing.residue R) (g - g0)).2
      intro n
      have hmem := hg n
      rwa [IsLocalRing.ker_residue]
    have hsub :
        g.map (IsLocalRing.residue R) - g0.map (IsLocalRing.residue R) = 0 := by
      simpa [Polynomial.map_sub] using hzero
    exact sub_eq_zero.mp hsub
  have hhmap : h.map (IsLocalRing.residue R) =
      h0.map (IsLocalRing.residue R) := by
    have hzero : (h - h0).map (IsLocalRing.residue R) = 0 := by
      apply (henselFactorization_map_eq_zero_iff_coeff_mem_ker
        (IsLocalRing.residue R) (h - h0)).2
      intro n
      have hmem := hh n
      rwa [IsLocalRing.ker_residue]
    have hsub :
        h.map (IsLocalRing.residue R) - h0.map (IsLocalRing.residue R) = 0 := by
      simpa [Polynomial.map_sub] using hzero
    exact sub_eq_zero.mp hsub
  have hcorrMap :
      (g0 * q + h0 * p - fn).map (IsLocalRing.residue R) = 0 := by
    apply (henselFactorization_map_eq_zero_iff_coeff_mem_ker
      (IsLocalRing.residue R) (g0 * q + h0 * p - fn)).2
    intro n
    have hmem := hcorr n
    rwa [IsLocalRing.ker_residue]
  have hmap :
      (g * q + h * p - fn).map (IsLocalRing.residue R) = 0 := by
    calc
      (g * q + h * p - fn).map (IsLocalRing.residue R) =
          g.map (IsLocalRing.residue R) * q.map (IsLocalRing.residue R) +
            h.map (IsLocalRing.residue R) * p.map (IsLocalRing.residue R) -
              fn.map (IsLocalRing.residue R) := by
        exact henselFactorization_map_mul_add_mul_sub (IsLocalRing.residue R) g h q p fn
      _ = g0.map (IsLocalRing.residue R) * q.map (IsLocalRing.residue R) +
            h0.map (IsLocalRing.residue R) * p.map (IsLocalRing.residue R) -
              fn.map (IsLocalRing.residue R) := by
        rw [hgmap, hhmap]
      _ = (g0 * q + h0 * p - fn).map (IsLocalRing.residue R) := by
        exact (henselFactorization_map_mul_add_mul_sub (IsLocalRing.residue R) g0 h0 q p fn).symm
      _ = 0 := hcorrMap
  intro n
  have hker :=
    (henselFactorization_map_eq_zero_iff_coeff_mem_ker
      (IsLocalRing.residue R) (g * q + h * p - fn)).1 hmap n
  rwa [IsLocalRing.ker_residue] at hker

/-- principal-ideal version of replacement of the initial
lifted factors by the current inductive approximants.  If `g` and `h` are
still congruent to `g0` and `h0` modulo `(π)`, then a correction congruence
for `g0,h0` modulo `(π)` is also one for `g,h`. -/
theorem henselFactorization_correction_congruence_replace_initial_factors_span_singleton
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 g h fn p q : R[X]}
    (hg : ∀ n : ℕ, (g - g0).coeff n ∈ Ideal.span ({π} : Set R))
    (hh : ∀ n : ℕ, (h - h0).coeff n ∈ Ideal.span ({π} : Set R))
    (hcorr :
      ∀ n : ℕ, (g0 * q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R)) :
    ∀ n : ℕ, (g * q + h * p - fn).coeff n ∈
      Ideal.span ({π} : Set R) := by
  let φ : R →+* R ⧸ Ideal.span ({π} : Set R) :=
    Ideal.Quotient.mk (Ideal.span ({π} : Set R))
  have hgmap : g.map φ = g0.map φ := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_iff_sub_coeff_mem
        (Ideal.span ({π} : Set R)) g g0).2 hg
  have hhmap : h.map φ = h0.map φ := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_iff_sub_coeff_mem
        (Ideal.span ({π} : Set R)) h h0).2 hh
  have hcorrMap : (g0 * q + h0 * p - fn).map φ = 0 := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_zero_iff_coeff_mem
        (Ideal.span ({π} : Set R)) (g0 * q + h0 * p - fn)).2 hcorr
  have hmap : (g * q + h * p - fn).map φ = 0 := by
    calc
      (g * q + h * p - fn).map φ =
          g.map φ * q.map φ + h.map φ * p.map φ - fn.map φ := by
        exact henselFactorization_map_mul_add_mul_sub φ g h q p fn
      _ = g0.map φ * q.map φ + h0.map φ * p.map φ - fn.map φ := by
        rw [hgmap, hhmap]
      _ = (g0 * q + h0 * p - fn).map φ := by
        exact (henselFactorization_map_mul_add_mul_sub φ g0 h0 q p fn).symm
      _ = 0 := hcorrMap
  intro n
  exact
    (henselFactorization_map_quotient_eq_zero_iff_coeff_mem
      (Ideal.span ({π} : Set R)) (g * q + h * p - fn)).1
      (by simpa [φ] using hmap) n

end Valuations
end AlgebraicNumberTheory

end
