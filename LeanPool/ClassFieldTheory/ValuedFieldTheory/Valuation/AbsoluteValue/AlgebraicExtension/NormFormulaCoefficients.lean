/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialLifting
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Core
/-!
# coefficient bound from primitive Hensel factorization

This file reuses the algebraic normalization and irreducibility obstruction
from the irreducible-polynomial coefficient bounds.  The factor lift is supplied directly by the
factorization form of Hensel's lemma in the primitive factorization definition, so no
  completeness or
separatedness hypothesis is needed.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- The normalized residual factor input from the irreducible-polynomial coefficient bounds
contradicts
irreducibility as soon as the valuation ring satisfies the construction's
factorization form of Hensel's lemma. -/
theorem normFormula_hensel_reduction_factor_input_not_irreducible_of_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hrpos : 0 < r) (hrlt : r < F.natDegree)
    (hfactor :
      F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch)) =
        Polynomial.X ^ r *
          (F.map (IsLocalRing.residue
            (absoluteValueValuationSubring v hnonarch)) /ₘ
              Polynomial.X ^ r))
    (hnatDegree : (Polynomial.X ^ r :
        (IsLocalRing.ResidueField
          (absoluteValueValuationSubring v hnonarch))[X]).natDegree =
        r)
    (hcoprime : IsCoprime (Polynomial.X ^ r)
      (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r))
    (hQ0 : ((F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r).coeff 0) ≠ 0)
    {f : K[X]}
    (hFmap : F.map (algebraMap
        (absoluteValueValuationSubring v hnonarch) K) = f)
    (hFdegree : F.natDegree = f.natDegree) :
    ¬ Irreducible f := by
  let V := absoluteValueValuationSubring v hnonarch
  let k := IsLocalRing.ResidueField V
  let fbar : k[X] := F.map (IsLocalRing.residue V)
  let qbar : k[X] := fbar /ₘ Polynomial.X ^ r
  have hprim : F.map (IsLocalRing.residue V) ≠ 0 := by
    exact
      irreduciblePolynomial_polynomial_ne_zero_of_eq_X_pow_mul_of_coeff_zero_ne_zero
        hfactor hQ0
  rcases hv hprim (by simpa [V, k, fbar, qbar] using hfactor) hcoprime with
    ⟨G, H, hGdegree_res, _hHle, hGH, _hGmap, _hHmap⟩
  have hGdegree : G.natDegree = r := hGdegree_res.trans hnatDegree
  exact irreduciblePolynomial_not_irreducible_of_valuation_factorization
    v hnonarch hFmap hFdegree hGH hGdegree hrpos hrlt

/-- Scaling by a coefficient of positive maximum value and applying the construction
Hensel factorization contradicts irreducibility when both endpoint values are
strictly below that maximum. -/
theorem normFormula_normalized_scale_not_irreducible_of_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m)
    (hconst : v (f.coeff 0) < m)
    (hlead : v f.leadingCoeff < m) :
    let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
    ¬ Irreducible g := by
  let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
  rcases irreduciblePolynomial_normalized_scale_hensel_reduction_factor_input
      v hnonarch hmpos hnmax hbound hconst hlead with
    ⟨F, r, hFmap, hFdegree, hrpos, hrlt, hfactor, hnatDegree, hcoprime, hQ0⟩
  exact
    normFormula_hensel_reduction_factor_input_not_irreducible_of_henselFactorization
      v hnonarch hv F hrpos hrlt hfactor hnatDegree hcoprime hQ0
      hFmap hFdegree

/-- Under primitive Hensel factorization, a positive coefficient maximum of an
irreducible polynomial is bounded by the larger endpoint value. -/
theorem normFormula_coeff_max_le_endpoint_max_of_irreducible_of_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hirr : Irreducible f)
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m) :
    m ≤ max (v (f.coeff 0)) (v f.leadingCoeff) := by
  by_contra hnot
  have hmaxlt : max (v (f.coeff 0)) (v f.leadingCoeff) < m :=
    lt_of_not_ge hnot
  have hconst : v (f.coeff 0) < m :=
    (le_max_left (v (f.coeff 0)) (v f.leadingCoeff)).trans_lt hmaxlt
  have hlead : v f.leadingCoeff < m :=
    (le_max_right (v (f.coeff 0)) (v f.leadingCoeff)).trans_lt hmaxlt
  have hscaled_irreducible :
      Irreducible (Polynomial.C (f.coeff n)⁻¹ * f) :=
    irreduciblePolynomial_irreducible_normalized_scale_of_irreducible
      v hmpos hnmax hirr
  have hscaled_not_irreducible :
      ¬ Irreducible (Polynomial.C (f.coeff n)⁻¹ * f) :=
    normFormula_normalized_scale_not_irreducible_of_henselFactorization
      v hnonarch hv hmpos hnmax hbound hconst hlead
  exact hscaled_not_irreducible hscaled_irreducible

/-- the finite norm-formula theorem coefficient source: primitive Hensel factorization alone bounds
every coefficient of an irreducible polynomial by its two endpoint values. -/
theorem normFormula_coeff_abs_le_endpoint_max_of_irreducible_of_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {f : K[X]} (hirr : Irreducible f) :
    ∀ i : ℕ, v (f.coeff i) ≤ max (v (f.coeff 0)) (v f.leadingCoeff) := by
  rcases irreduciblePolynomial_exists_coeff_abs_max_of_ne_zero v hirr.ne_zero with
    ⟨m, n, hmpos, _hnle, hnmax, hbound⟩
  have hmle : m ≤ max (v (f.coeff 0)) (v f.leadingCoeff) :=
    normFormula_coeff_max_le_endpoint_max_of_irreducible_of_henselFactorization
      v hnonarch hv hirr hmpos hnmax hbound
  intro i
  exact (hbound i).trans hmle

/-- the finite norm-formula theorem monic specialization: if the constant coefficient of an
irreducible monic polynomial lies in the closed unit ball, then every
coefficient lies there. -/
theorem normFormula_monic_coeff_abs_le_one_of_const_abs_le_one_of_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {f : K[X]} (hirr : Irreducible f)
    (hmonic : f.Monic)
    (hconst : v (f.coeff 0) ≤ 1) :
    ∀ i : ℕ, v (f.coeff i) ≤ 1 := by
  have hlead : v f.leadingCoeff = 1 := by
    rw [hmonic.leadingCoeff]
    simp
  have hendpoint :
      max (v (f.coeff 0)) (v f.leadingCoeff) ≤ 1 := by
    rw [hlead]
    exact max_le hconst le_rfl
  intro i
  exact
    (normFormula_coeff_abs_le_endpoint_max_of_irreducible_of_henselFactorization
      v hnonarch hv hirr i).trans hendpoint

end Valuations
end AlgebraicNumberTheory

end
