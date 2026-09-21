/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Weyl.MonicNormalization

/-!
# From principal-axis normalization to PBW monicity

Axis restriction does not merge coefficients: its degree-`N` coefficient is
exactly the coefficient of the pure selected-variable monomial. The same pure
coefficient passes unchanged from the degree-`N` principal component to the
full checked PBW normal form. Together with the Bernstein bound, this yields a
coefficient-one pure momentum term and excludes every higher momentum power.

The resulting data retain the symplectic matrices, inverse identities, scalar,
and exact normalized image. Converting this PBW statement to `Polynomial.Monic`
for the outer Ore layer remains separate.
-/

namespace Stafford38.WeylPBWMonicBridge

open Stafford38.Characteristic
open Stafford38.CharacteristicHomogeneousChart
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylMonicNormalization
open Stafford38.WeylPBW
open Stafford38.WeylSymplectic

noncomputable section
universe u
variable (k : Type u) [Field k]

theorem coeff_axisPolynomial {n : ℕ} (t : PhaseVar n)
    (P : SymbolRing k n) (N : ℕ) :
    (axisPolynomial k t P).coeff (Finsupp.single () N) =
      P.coeff (Finsupp.single t N) := by
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
      by_cases hsub : ∀ i ∈ m.support, i = t
      · have hm : m = Finsupp.single t (m t) := by
          ext i
          by_cases hit : i = t
          · subst i
            simp
          · have hi : i ∉ m.support := by
              intro him
              exact hit (hsub i him)
            rw [Finsupp.notMem_support_iff.mp hi]
            rw [Finsupp.single_apply]
            simp [Ne.symm hit]
        rw [hm]
        rw [axisPolynomial, MvPolynomial.aeval_monomial]
        rw [Finsupp.prod_single_index (by simp)]
        simp [MvPolynomial.X_pow_eq_monomial]
        by_cases hmt : m t = N
        · simp [hmt]
        · have hs : Finsupp.single t (m t) ≠ Finsupp.single t N := by
            intro h
            exact hmt (Finsupp.single_injective t h)
          simp [hmt, hs]
      · push Not at hsub
        rcases hsub with ⟨i, hi, hit⟩
        have hmne : m ≠ Finsupp.single t N := by
          intro hm
          subst m
          simp [ Ne.symm hit] at hi
        rw [axisPolynomial, MvPolynomial.aeval_monomial]
        have hz : m.prod
            (fun i e => (if i = t then MvPolynomial.X ()
              else (0 : MvPolynomial Unit k)) ^ e) = 0 := by
          rw [Finsupp.prod]
          apply Finset.prod_eq_zero hi
          have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
          simp [hit, hmi]
        rw [hz, mul_zero]
        simp [MvPolynomial.coeff_monomial, hmne]
  | add p q hp hq =>
      simp [map_add, hp, hq]

theorem coeff_principal_pure_eq_normalForm {n N : ℕ}
    (t : PhaseVar n) (d : PresentedWeyl k n) :
    (presentedPrincipalComponent k (@bernsteinWeight n) N d).coeff (Finsupp.single t N) =
      (presentedNormalFormLinearEquiv k n d).coeff (Finsupp.single t N) := by
  rw [coeff_presentedPrincipalComponent]
  simp [monomialWeight, bernsteinWeight]

/-- Membership in Bernstein degree `N` with pure `t`-power coefficient equal to one in PBW
normal form. -/
def IsPBWMonicAt {n : ℕ} (t : PhaseVar n) (N : ℕ)
    (d : PresentedWeyl k n) : Prop :=
  d ∈ bernsteinPiece k n N ∧
    (presentedNormalFormLinearEquiv k n d).coeff (Finsupp.single t N) = 1

theorem coeff_normalForm_eq_zero_of_exponent_gt {n N : ℕ}
    {t : PhaseVar n} {d : PresentedWeyl k n}
    (hd : d ∈ bernsteinPiece k n N) {m : PhaseVar n →₀ ℕ}
    (hmt : N < m t) :
    (presentedNormalFormLinearEquiv k n d).coeff m = 0 := by
  by_contra hcoeff
  have hweight := (mem_presentedWeightPiece k (@bernsteinWeight n) N d).mp
    hd m hcoeff
  have hle : m t ≤ monomialWeight (@bernsteinWeight n) m := by
    simpa [monomialWeight, bernsteinWeight] using
      Finsupp.single_eval_le_sum m (g := id) rfl (fun _ => Nat.zero_le _) t
  omega

/-- A symplectic change of coordinates and a nonzero scalar that make the pure PBW coefficient
equal to one while preserving the Bernstein degree bound. -/
structure NormalizedPBWChartData {n : ℕ} (t : PhaseVar n) (N : ℕ)
    (d : PresentedWeyl k n) where
  /-- The symplectic matrix defining the normalized coordinate change. -/
  M : Matrix (PhaseVar n) (PhaseVar n) k
  /-- The inverse symplectic matrix of the normalized coordinate change. -/
  Ninv : Matrix (PhaseVar n) (PhaseVar n) k
  /-- The nonzero scalar used to normalize the pure PBW coefficient. -/
  c : k
  hM : M * standardForm k n * Matrix.transpose M = standardForm k n
  hNinv : Ninv * standardForm k n * Matrix.transpose Ninv = standardForm k n
  hMN : M * Ninv = 1
  hNM : Ninv * M = 1
  hc : c ≠ 0
  mem_piece : normalizedSymplecticImage k M hM c d ∈ bernsteinPiece k n N
  pure_coeff : (presentedNormalFormLinearEquiv k n
        (normalizedSymplecticImage k M hM c d)).coeff (Finsupp.single t N) = 1

theorem HasNormalizedSymplecticChart.toNormalizedPBWChartData
    {n N : ℕ} {t : PhaseVar n} {d : PresentedWeyl k n}
    (hchart : HasNormalizedSymplecticChart k t N d) :
    Nonempty (NormalizedPBWChartData k t N d) := by
  rcases hchart with ⟨M, Ninv, c, hM, hNinv, hMN, hNM, hc, hpiece, haxis⟩
  refine ⟨⟨M, Ninv, c, hM, hNinv, hMN, hNM, hc, hpiece, ?_⟩⟩
  rw [← coeff_principal_pure_eq_normalForm k]
  rw [← coeff_axisPolynomial k]
  exact haxis

theorem HasNormalizedSymplecticChart.purePBWCoefficient
    {n N : ℕ} {t : PhaseVar n} {d : PresentedWeyl k n}
    (hchart : HasNormalizedSymplecticChart k t N d) :
    ∃ d' : PresentedWeyl k n, IsPBWMonicAt k t N d' := by
  rcases hchart with ⟨M, Ninv, c, hM, hNinv, hMN, hNM, hc, hpiece, haxis⟩
  refine ⟨normalizedSymplecticImage k M hM c d, hpiece, ?_⟩
  rw [← coeff_principal_pure_eq_normalForm k]
  rw [← coeff_axisPolynomial k]
  exact haxis

/- Exact statement pins for the coefficient bridge and retained chart data. -/
theorem coeff_axisPolynomial_statement {n : ℕ} (t : PhaseVar n)
    (P : SymbolRing k n) (N : ℕ) :
    (axisPolynomial k t P).coeff (Finsupp.single () N) =
      P.coeff (Finsupp.single t N) :=
  coeff_axisPolynomial k t P N

theorem isPBWMonicAt_statement {n : ℕ} (t : PhaseVar n) (N : ℕ)
    (d : PresentedWeyl k n) :
    IsPBWMonicAt k t N d ↔
      d ∈ bernsteinPiece k n N ∧
        (presentedNormalFormLinearEquiv k n d).coeff (Finsupp.single t N) = 1 :=
  Iff.rfl

theorem coeff_principal_pure_eq_normalForm_statement {n N : ℕ}
    (t : PhaseVar n) (d : PresentedWeyl k n) :
    (presentedPrincipalComponent k (@bernsteinWeight n) N d).coeff (Finsupp.single t N) =
      (presentedNormalFormLinearEquiv k n d).coeff (Finsupp.single t N) :=
  coeff_principal_pure_eq_normalForm k t d

theorem coeff_normalForm_eq_zero_of_exponent_gt_statement {n N : ℕ}
    {t : PhaseVar n} {d : PresentedWeyl k n}
    (hd : d ∈ bernsteinPiece k n N) {m : PhaseVar n →₀ ℕ}
    (hmt : N < m t) :
    (presentedNormalFormLinearEquiv k n d).coeff m = 0 :=
  coeff_normalForm_eq_zero_of_exponent_gt k hd hmt

theorem normalizedPBWChartData_fields {n N : ℕ} {t : PhaseVar n}
    {d : PresentedWeyl k n} (D : NormalizedPBWChartData k t N d) :
    D.M * standardForm k n * Matrix.transpose D.M = standardForm k n ∧
      D.Ninv * standardForm k n * Matrix.transpose D.Ninv = standardForm k n ∧
      D.M * D.Ninv = 1 ∧ D.Ninv * D.M = 1 ∧ D.c ≠ 0 ∧
      normalizedSymplecticImage k D.M D.hM D.c d ∈ bernsteinPiece k n N ∧
      (presentedNormalFormLinearEquiv k n
          (normalizedSymplecticImage k D.M D.hM D.c d)).coeff (Finsupp.single t N) = 1 :=
  ⟨D.hM, D.hNinv, D.hMN, D.hNM, D.hc, D.mem_piece, D.pure_coeff⟩

theorem normalizedPBWChartData_statement
    {n N : ℕ} {t : PhaseVar n} {d : PresentedWeyl k n}
    (hchart : HasNormalizedSymplecticChart k t N d) :
    Nonempty (NormalizedPBWChartData k t N d) :=
  HasNormalizedSymplecticChart.toNormalizedPBWChartData k hchart


end
end Stafford38.WeylPBWMonicBridge
