/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.SymplecticCompletion
public import LeanPool.Stafford38.Stafford38.Weyl.SymbolCompatibility


/-!
# Bernstein-top selection and scalar monic normalization

The checked PBW normal form selects the actual top Bernstein degree of every
nonzero presented Weyl element. Degree zero is exactly the scalar case. In
positive degree, the explicit symplectic chart is applied and the transformed
operator is scaled by the inverse of its nonzero pure-power coefficient. The
normalized principal axis coefficient is then exactly one.

This file stops at the commutative-symbol monicity interface. Identifying it
with a monic Ore polynomial in the selected momentum is the next dependency.
-/

@[expose] public section

namespace Stafford38.WeylMonicNormalization

open Stafford38.Characteristic
open Stafford38.CharacteristicHomogeneousChart
open Stafford38.CharacteristicSymplecticCompletion
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBW
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylSymplectic
open Stafford38.WeylSymbolCompatibility

noncomputable section
universe u
variable (k : Type u) [Field k]

theorem weightedHomogeneousComponent_weightedTotalDegree_ne_zero
    {σ : Type*} (w : σ → ℕ)
    {f : MvPolynomial σ k} (hf : f ≠ 0) :
    MvPolynomial.weightedHomogeneousComponent w
        (MvPolynomial.weightedTotalDegree w f) f ≠ 0 := by
  have hs : f.support.Nonempty := MvPolynomial.support_nonempty.mpr hf
  rcases Finset.exists_mem_eq_sup f.support hs (Finsupp.weight w) with
    ⟨m, hm, hmax⟩
  intro hzero
  have hc := congrArg (fun f : MvPolynomial _ _ => f.coeff m) hzero
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hc
  have hw : Finsupp.weight w m = MvPolynomial.weightedTotalDegree w f := by
    simpa [MvPolynomial.weightedTotalDegree] using hmax.symm
  rw [ite_eq_left hw] at hc
  exact (MvPolynomial.mem_support_iff.mp hm) hc

theorem principal_isHomogeneous {n N : ℕ} (d : PresentedWeyl k n) :
    (presentedPrincipalComponent k (@bernsteinWeight n) N d).IsHomogeneous N := by
  change MvPolynomial.IsWeightedHomogeneous (1 : PhaseVar n → ℕ)
    (presentedPrincipalComponent k (@bernsteinWeight n) N d) N
  have hweight : (@bernsteinWeight n) = (1 : PhaseVar n → ℕ) := by
    funext i
    rfl
  rw [← hweight]
  simpa [presentedPrincipalComponent] using
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := @bernsteinWeight n) (n := N)
      (φ := presentedNormalFormLinearEquiv k n d))

theorem exists_top_bernstein_piece {n : ℕ} {d : PresentedWeyl k n}
    (hd : d ≠ 0) :
    ∃ N : ℕ, d ∈ bernsteinPiece k n N ∧
      presentedPrincipalComponent k (@bernsteinWeight n) N d ≠ 0 := by
  let f := presentedNormalFormLinearEquiv k n d
  have hf : f ≠ 0 := by
    intro hzero
    apply hd
    apply (presentedNormalFormLinearEquiv k n).injective
    simpa [f] using hzero
  let N := MvPolynomial.weightedTotalDegree (@bernsteinWeight n) f
  refine ⟨N, ?_, ?_⟩
  · change d ∈ presentedWeightPiece k (@bernsteinWeight n) N
    rw [mem_presentedWeightPiece]
    intro m hm
    simpa [f, N, monomialWeight, Finsupp.weight_apply, smul_eq_mul] using
      MvPolynomial.le_weightedTotalDegree (@bernsteinWeight n)
        (MvPolynomial.mem_support_iff.mpr hm)
  · exact weightedHomogeneousComponent_weightedTotalDegree_ne_zero k
      (@bernsteinWeight n) hf

theorem eq_algebraMap_of_mem_bernsteinPiece_zero {n : ℕ}
    {d : PresentedWeyl k n} (hd : d ∈ bernsteinPiece k n 0) :
    ∃ c : k, d = algebraMap k (PresentedWeyl k n) c := by
  let f := presentedNormalFormLinearEquiv k n d
  let c := f.coeff 0
  have hf : f = MvPolynomial.C c := by
    ext m
    by_cases hm : m = 0
    · subst m
      simp [c]
    · have hcoeff : f.coeff m = 0 := by
        by_contra hne
        have hle := (mem_presentedWeightPiece k (@bernsteinWeight n) 0 d).mp hd m hne
        have hdeg : m.degree = 0 := by
          apply Nat.eq_zero_of_le_zero
          rw [Finsupp.degree_eq_weight_one]
          simpa [f, monomialWeight, bernsteinWeight,
            Finsupp.weight_apply, smul_eq_mul] using hle
        exact hm ((Finsupp.degree_eq_zero_iff m).mp hdeg)
      rw [hcoeff]
      simp [Ne.symm hm]
  refine ⟨c, ?_⟩
  apply (presentedNormalFormLinearEquiv k n).injective
  rw [show presentedNormalFormLinearEquiv k n d = f by rfl, hf]
  rw [← mul_one ((algebraMap k (PresentedWeyl k n)) c),
    ← Algebra.smul_def]
  change MvPolynomial.C c =
    presentedNormalFormLinearEquiv k n (c • (1 : PresentedWeyl k n))
  rw [map_smul, presentedNormalFormLinearEquiv_one]
  exact MvPolynomial.C_eq_smul_one

theorem scalar_or_positive_top_bernstein_piece {n : ℕ}
    {d : PresentedWeyl k n} (hd : d ≠ 0) :
    (∃ c : k, c ≠ 0 ∧ d = algebraMap k (PresentedWeyl k n) c) ∨
      ∃ N : ℕ, 0 < N ∧ d ∈ bernsteinPiece k n N ∧
        presentedPrincipalComponent k (@bernsteinWeight n) N d ≠ 0 := by
  rcases exists_top_bernstein_piece k hd with ⟨N, hpiece, hprincipal⟩
  by_cases hN : N = 0
  · subst N
    left
    rcases eq_algebraMap_of_mem_bernsteinPiece_zero k hpiece with ⟨c, hdc⟩
    refine ⟨c, ?_, hdc⟩
    intro hc
    subst c
    simp? at hdc
    exact hd hdc
  · right
    exact ⟨N, Nat.pos_of_ne_zero hN, hpiece, hprincipal⟩

/-- The symplectic image of a Weyl element rescaled by the inverse normalization coefficient. -/
def normalizedSymplecticImage {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    (c : k) (d : PresentedWeyl k n) : PresentedWeyl k n :=
  c⁻¹ • standardSymplecticAlgHom k M hM d

/-- Existence of an invertible symplectic change giving a normalized pure-axis principal
coefficient. -/
def HasNormalizedSymplecticChart {n : ℕ} (t : PhaseVar n) (N : ℕ)
    (d : PresentedWeyl k n) : Prop :=
  ∃ (M Ninv : Matrix (PhaseVar n) (PhaseVar n) k) (c : k),
    ∃ hM : M * standardForm k n * Matrix.transpose M = standardForm k n,
    Ninv * standardForm k n * Matrix.transpose Ninv = standardForm k n ∧
    M * Ninv = 1 ∧ Ninv * M = 1 ∧ c ≠ 0 ∧
    normalizedSymplecticImage k M hM c d ∈ bernsteinPiece k n N ∧
    (axisPolynomial k t
          (presentedPrincipalComponent k (@bernsteinWeight n) N
            (normalizedSymplecticImage k M hM c d))).coeff (Finsupp.single () N) = 1

theorem exists_normalized_symplectic_image [CharZero k]
    {n N : ℕ} (t : PhaseVar n) {d : PresentedWeyl k n}
    (hd : d ∈ bernsteinPiece k n N)
    (hP : (presentedPrincipalComponent k (@bernsteinWeight n) N d).IsHomogeneous N)
    (hPne : presentedPrincipalComponent k (@bernsteinWeight n) N d ≠ 0)
    (hN : 0 < N) :
    HasNormalizedSymplecticChart k t N d := by
  rcases exists_symplectic_chart_matrices k t hP hPne hN with
    ⟨M, Ninv, hM, hNinv, hMN, hNM, hc⟩
  let c : k := (axisPolynomial k t
      (Stafford38.CharacteristicLinearAction.symbolLinearAlgHom k M
        (presentedPrincipalComponent k (@bernsteinWeight n) N d))).coeff (Finsupp.single () N)
  have hc' : c ≠ 0 := hc
  refine ⟨M, Ninv, c, hM, hNinv, hMN, hNM, hc', ?_, ?_⟩
  · exact (bernsteinPiece k n N).smul_mem _
      (standardSymplecticAlgHom_preserves_bernsteinPiece k M hM hd)
  · rw [normalizedSymplecticImage, map_smul]
    rw [standardSymplecticAlgHom_principal_compatibility k M hM hd]
    simp only [map_smul, MvPolynomial.coeff_smul]
    change c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc'

theorem scalar_or_normalized_symplectic_image [CharZero k]
    {n : ℕ} (hn : 0 < n) {d : PresentedWeyl k n} (hd : d ≠ 0) :
    (∃ c : k, c ≠ 0 ∧ d = algebraMap k (PresentedWeyl k n) c) ∨
      ∃ N : ℕ, 0 < N ∧
        HasNormalizedSymplecticChart k (.inr ⟨0, hn⟩) N d := by
  rcases scalar_or_positive_top_bernstein_piece k hd with hscalar | htop
  · exact Or.inl hscalar
  · rcases htop with ⟨N, hN, hpiece, hprincipal⟩
    right
    refine ⟨N, hN, ?_⟩
    exact exists_normalized_symplectic_image k (.inr ⟨0, hn⟩) hpiece
      (principal_isHomogeneous k d) hprincipal hN

/- Exact statement pins for top-degree selection and the scalar/normalized
chart dichotomy. -/
theorem top_bernstein_piece_statement {n : ℕ} {d : PresentedWeyl k n}
    (hd : d ≠ 0) :
    ∃ N : ℕ, d ∈ bernsteinPiece k n N ∧
      presentedPrincipalComponent k (@bernsteinWeight n) N d ≠ 0 :=
  exists_top_bernstein_piece k hd

theorem scalar_or_normalized_chart_statement [CharZero k]
    {n : ℕ} (hn : 0 < n) {d : PresentedWeyl k n} (hd : d ≠ 0) :
    (∃ c : k, c ≠ 0 ∧ d = algebraMap k (PresentedWeyl k n) c) ∨
      ∃ N : ℕ, 0 < N ∧
        HasNormalizedSymplecticChart k (.inr ⟨0, hn⟩) N d :=
  scalar_or_normalized_symplectic_image k hn hd


end
end Stafford38.WeylMonicNormalization
