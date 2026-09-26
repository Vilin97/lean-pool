/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm.CoordinateChange
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm.Weierstrass

/-!
# Noetherianity of analytic germ rings

[Jakóbczak–Jarnicki][JakobczakJarnicki2021], Proposition 1.8.6: scalar analytic germs on
finite-dimensional complex spaces form Noetherian rings. The analytic induction step normalizes
a nonzero element of an ideal, divides by it, and uses finite generation of the resulting
submodule of the finite module of remainder coefficients. The dimension induction,
zero-dimensional base case, and coordinate transport are proved here from that step. No claim is
made for infinite-dimensional source spaces.

## Main results

`ideal_fg` is finite generation of ideals of finite-dimensional analytic germs. `ideal_fg_prod`
is the analytic induction step. `isNoetherianRing_coordinates` is Noetherianity on coordinate
spaces, from which the general instance is transported.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Filter
open scoped Topology

namespace SeveralComplexVariables.AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Given an ideal element regular in the distinguished coordinate, division against its Weierstrass
preparation shows the ideal is finitely generated: every element reduces, modulo the ideal
element, to a polynomial remainder of degree below the order; those remainders occurring in the
ideal form a submodule of the finite free module of degree-bounded coefficient tuples, finitely
generated since the coefficient ring is Noetherian. -/
theorem ideal_fg_of_orderInLastVariable_eq_nat [FiniteDimensional ℂ E]
    [IsNoetherianRing (AnalyticGerm ℂ (0 : E))] (J : Ideal (AnalyticGerm ℂ (0 : E × ℂ)))
    {g : AnalyticGerm ℂ (0 : E × ℂ)} (hgJ : g ∈ J) {d : ℕ} (hd : orderInLastVariable g = d) :
    J.FG := by
  classical
  obtain ⟨⟨u, w⟩, ⟨hwdist, hwdeg, hgeq⟩, -⟩ := existsUnique_preparation g hd
  simp only at hwdist hwdeg hgeq
  have hgu : polynomialHom w = (↑u⁻¹ : AnalyticGerm ℂ (0 : E × ℂ)) * g := by
    rw [hgeq, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  let M : Submodule (AnalyticGerm ℂ (0 : E)) (Fin d → AnalyticGerm ℂ (0 : E)) :=
    { carrier := {a | polynomialHom (remainderOfCoefficients a) ∈ J}
      zero_mem' := by
        change polynomialHom (remainderOfCoefficients 0) ∈ J
        simp [remainderOfCoefficients]
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, remainderOfCoefficients_add, map_add] at ha hb ⊢
        exact J.add_mem ha hb
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq, remainderOfCoefficients_smul, map_mul,
          polynomialHom_C] at ha ⊢
        exact J.mul_mem_left _ ha }
  have hMfg : M.FG := IsNoetherian.noetherian M
  obtain ⟨S, hS⟩ := hMfg
  refine ⟨insert g (S.image (fun a => polynomialHom (remainderOfCoefficients a))), ?_⟩
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_image, Set.mem_image,
      Finset.mem_coe] at hx
    rcases hx with rfl | ⟨a, haS, rfl⟩
    · exact hgJ
    · change a ∈ M
      rw [← hS]
      exact Submodule.subset_span haS
  · intro h hhJ
    obtain ⟨⟨q, r⟩, ⟨hrdeg, heq⟩, -⟩ := existsUnique_division w hwdist h
    simp only at hrdeg heq
    rw [hwdeg] at hrdeg
    have hreq : polynomialHom r = h - q * (↑u⁻¹ : AnalyticGerm ℂ (0 : E × ℂ)) * g := by
      rw [heq, hgu]; ring
    have hmem : polynomialHom r ∈ J := by
      rw [hreq]
      exact J.sub_mem hhJ (J.mul_mem_left _ hgJ)
    have har : r = remainderOfCoefficients (fun j : Fin d => r.coeff (j : ℕ)) :=
      eq_remainderOfCoefficients_of_degree_lt hrdeg
    have hmemM : (fun j : Fin d => r.coeff (j : ℕ)) ∈ M := by
      change polynomialHom (remainderOfCoefficients _) ∈ J
      rwa [← har]
    rw [← hS] at hmemM
    obtain ⟨f, hf⟩ := Submodule.mem_span_finset'.mp hmemM
    have hrsum : r =
        ∑ a : S, f a • remainderOfCoefficients (a : Fin d → AnalyticGerm ℂ (0 : E)) := by
      rw [har, ← hf, remainderOfCoefficients_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Polynomial.smul_eq_C_mul]
      exact remainderOfCoefficients_smul (f a) (a : Fin d → AnalyticGerm ℂ (0 : E))
    have hpolyr : polynomialHom r = ∑ a : S, parameterHom (f a) *
        polynomialHom (remainderOfCoefficients (a : Fin d → AnalyticGerm ℂ (0 : E))) := by
      rw [hrsum, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Polynomial.smul_eq_C_mul, map_mul, polynomialHom_C]
    have hheq : h = q * ((↑u⁻¹ : AnalyticGerm ℂ (0 : E × ℂ)) * g) +
        ∑ a : S, parameterHom (f a) *
          polynomialHom (remainderOfCoefficients (a : Fin d → AnalyticGerm ℂ (0 : E))) := by
      rw [heq, hgu, hpolyr]
    rw [hheq]
    apply Ideal.add_mem
    · exact Ideal.mul_mem_left _ q (Ideal.mul_mem_left _ _
        (Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self g _))))
    · apply Ideal.sum_mem
      intro a _
      apply Ideal.mul_mem_left
      apply Ideal.subset_span
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨(a : Fin d → AnalyticGerm ℂ (0 : E)), a.2, rfl⟩))

/-- Analytic induction step for Noetherianity. A nonzero element becomes regular in the
distinguished coordinate after a linear coordinate change; finite generation transports back
along the induced ring automorphism of the germ ring. -/
theorem ideal_fg_prod [FiniteDimensional ℂ E]
    [IsNoetherianRing (AnalyticGerm ℂ (0 : E))]
    (I : Ideal (AnalyticGerm ℂ (0 : E × ℂ))) : I.FG := by
  rcases eq_or_ne I ⊥ with hI0 | hI0
  · exact hI0 ▸ Submodule.fg_bot
  · obtain ⟨g, hgI, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    obtain ⟨g0, hg0A, rfl⟩ := exists_rep g
    have hg0ne : ¬ g0 =ᶠ[𝓝 0] 0 := fun h => hg0 (Subtype.ext (Germ.coe_eq.mpr h))
    obtain ⟨L, d, hd⟩ := exists_regular_coordinate_change hg0A hg0ne
    have hL0 : L (0 : E × ℂ) = 0 := L.map_zero
    have hΦ : AnalyticAt ℂ L (0 : E × ℂ) := L.toContinuousLinearMap.analyticAt 0
    have hΦsymm0 : AnalyticAt ℂ L.symm (L (0 : E × ℂ)) := by
      rw [hL0]; exact L.symm.toContinuousLinearMap.analyticAt 0
    set Φ : AnalyticGerm ℂ (0 : E × ℂ) ≃ₐ[ℂ] AnalyticGerm ℂ (0 : E × ℂ) :=
      pullbackEquivOfEq L.toHomeomorph 0 hΦ hΦsymm0 hL0 with hΦdef
    have hΦg : Φ (ofAnalyticAt g0 hg0A) = ofAnalyticAt (g0 ∘ L) (hg0A.comp_of_eq hΦ hL0) :=
      pullbackEquivOfEq_ofAnalyticAt L.toHomeomorph 0 hΦ hΦsymm0 hL0 g0 hg0A
    have hΦbij : Function.Bijective (Φ : AnalyticGerm ℂ (0 : E × ℂ) → AnalyticGerm ℂ (0 : E × ℂ)) :=
      pullbackEquivOfEq_bijective L.toHomeomorph 0 hΦ hΦsymm0 hL0
    have hΦorder : orderInLastVariable (Φ (ofAnalyticAt g0 hg0A)) = d := by
      rw [hΦg, orderInLastVariable_ofAnalyticAt]
      exact hd
    have hFG : (I.map (Φ.toRingEquiv : AnalyticGerm ℂ (0 : E × ℂ) →+*
        AnalyticGerm ℂ (0 : E × ℂ))).FG :=
      ideal_fg_of_orderInLastVariable_eq_nat _ (Ideal.mem_map_of_mem _ hgI) hΦorder
    have hcomap : (I.map (Φ.toRingEquiv : AnalyticGerm ℂ (0 : E × ℂ) →+*
        AnalyticGerm ℂ (0 : E × ℂ))).comap
          (Φ.toRingEquiv : AnalyticGerm ℂ (0 : E × ℂ) →+* AnalyticGerm ℂ (0 : E × ℂ)) = I :=
      Ideal.comap_map_of_bijective _ hΦbij
    have hI : I = (I.map (Φ.toRingEquiv : AnalyticGerm ℂ (0 : E × ℂ) →+*
        AnalyticGerm ℂ (0 : E × ℂ))).map
          (Φ.toRingEquiv.symm : AnalyticGerm ℂ (0 : E × ℂ) →+* AnalyticGerm ℂ (0 : E × ℂ)) := by
      conv_lhs => rw [← hcomap]
      rw [Ideal.map_comap_of_equiv Φ.toRingEquiv.symm, RingEquiv.symm_symm]
      rfl
    rw [hI]
    exact Ideal.FG.map hFG _

/-- Analytic induction step for factorization: an irreducible germ becomes regular in the
distinguished coordinate after a linear change, Weierstrass-prepares to a distinguished
polynomial, and irreducibility of the polynomial (hence, given a unique factorization base ring,
its primality) transports back to primality of the germ. -/
theorem prime_of_irreducible_of_baseUFD [FiniteDimensional ℂ E]
    [UniqueFactorizationMonoid (AnalyticGerm ℂ (0 : E))]
    {g : AnalyticGerm ℂ (0 : E × ℂ)} (hg : Irreducible g) : Prime g := by
  obtain ⟨g0, hg0A, rfl⟩ := exists_rep g
  have hg0ne : ¬ g0 =ᶠ[𝓝 0] 0 := fun h => hg.ne_zero (Subtype.ext (Germ.coe_eq.mpr h))
  obtain ⟨L, d, hd⟩ := exists_regular_coordinate_change hg0A hg0ne
  have hL0 : L (0 : E × ℂ) = 0 := L.map_zero
  have hΦ : AnalyticAt ℂ L (0 : E × ℂ) := L.toContinuousLinearMap.analyticAt 0
  have hΦsymm0 : AnalyticAt ℂ L.symm (L (0 : E × ℂ)) := by
    rw [hL0]; exact L.symm.toContinuousLinearMap.analyticAt 0
  set Φ : AnalyticGerm ℂ (0 : E × ℂ) ≃ₐ[ℂ] AnalyticGerm ℂ (0 : E × ℂ) :=
    pullbackEquivOfEq L.toHomeomorph 0 hΦ hΦsymm0 hL0 with hΦdef
  have hΦg : Φ (ofAnalyticAt g0 hg0A) = ofAnalyticAt (g0 ∘ L) (hg0A.comp_of_eq hΦ hL0) :=
    pullbackEquivOfEq_ofAnalyticAt L.toHomeomorph 0 hΦ hΦsymm0 hL0 g0 hg0A
  have hΦorder : orderInLastVariable (Φ (ofAnalyticAt g0 hg0A)) = d := by
    rw [hΦg, orderInLastVariable_ofAnalyticAt]
    exact hd
  have hΦirr : Irreducible (Φ (ofAnalyticAt g0 hg0A)) := hg.map Φ
  obtain ⟨⟨u, w⟩, ⟨hwdist, hwdeg, hgeq⟩, -⟩ :=
    existsUnique_preparation (Φ (ofAnalyticAt g0 hg0A)) hΦorder
  simp only at hwdist hwdeg hgeq
  have hpolyirr : Irreducible (polynomialHom w) :=
    (irreducible_isUnit_mul u.isUnit).mp (hgeq ▸ hΦirr)
  have hwirr : Irreducible w := (irreducible_polynomialHom_iff w hwdist).mp hpolyirr
  have hwp : Prime w := UniqueFactorizationMonoid.irreducible_iff_prime.mp hwirr
  have hpw : Prime (polynomialHom w) := prime_polynomialHom_of_isDistinguishedAt hwdist hwp
  have hpΦg : Prime (Φ (ofAnalyticAt g0 hg0A)) := by
    rw [hgeq]; exact (prime_units_mul u).mpr hpw
  exact (MulEquiv.prime_iff Φ).mp hpΦg

/-- The origin germ ring in `n` complex coordinates is Noetherian, by induction using
`ideal_fg_prod`. In dimension zero it is the scalar field. -/
theorem isNoetherianRing_coordinates (n : ℕ) :
    IsNoetherianRing (AnalyticGerm ℂ (0 : Fin n → ℂ)) := by
  induction n with
  | zero =>
      exact isNoetherianRing_of_ringEquiv ℂ (equivScalarOfSubsingleton ℂ (0 : Fin 0 → ℂ)).symm
  | succ n ih =>
      let := ih
      let : IsNoetherianRing (AnalyticGerm ℂ (0 : (Fin n → ℂ) × ℂ)) :=
        (isNoetherianRing_iff_ideal_fg _).mpr ideal_fg_prod
      let e : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × ℂ :=
        (LinearEquiv.piCongrLeft ℂ (fun _ => ℂ) (finSuccEquiv n)).trans
          ((LinearEquiv.piOptionEquivProd ℂ).trans (LinearEquiv.prodComm ℂ _ _))
      exact isNoetherianRing_of_ringEquiv _
        (linearEquivPullbackZero e.toContinuousLinearEquiv).toRingEquiv

/-- Scalar analytic germs at any point of a finite-dimensional complex normed space form a
Noetherian ring. This instance combines the analytic induction step with the dimension
induction. -/
instance [FiniteDimensional ℂ E] (x : E) : IsNoetherianRing (AnalyticGerm ℂ x) := by
  let e := (Module.finBasis ℂ E).equivFunL
  let := isNoetherianRing_coordinates (Module.finrank ℂ E)
  let : IsNoetherianRing (AnalyticGerm ℂ (0 : E)) :=
    isNoetherianRing_of_ringEquiv _ (linearEquivPullbackZero e).toRingEquiv
  exact isNoetherianRing_of_ringEquiv _ (translateEquiv x).symm.toRingEquiv

/-- Every ideal of finite-dimensional analytic germs has finitely many generators. -/
theorem ideal_fg [FiniteDimensional ℂ E] {x : E} (I : Ideal (AnalyticGerm ℂ x)) : I.FG :=
  (isNoetherianRing_iff_ideal_fg _).mp inferInstance I

end SeveralComplexVariables.AnalyticGerm

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
