/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CircularContinuation
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt.Extension
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Runge

/-!
# Examples of Runge domains

Complete Reinhardt open sets in `ℂⁿ` are Runge domains, since holomorphic functions on them are
represented by their Taylor series at the origin, converging locally uniformly. More generally,
circular connected open sets containing the origin are Runge domains, since holomorphic
functions on them are locally uniform sums of their homogeneous expansions, whose terms are
polynomials. In particular polydiscs and balls centered at the origin, and the whole space, are
Runge domains.

Runge domains are transported by holomorphic maps with polynomial inverses: if `U` is Runge, `Φ`
is holomorphic on `U` with values in `U'`, and `Ψ` is a polynomial map from `U'` into `U` with
`Φ ∘ Ψ = id` on `U'`, then `U'` is Runge. Translates and polynomial-automorphic images of Runge
domains are Runge ([Jakóbczak–Jarnicki][JakobczakJarnicki2021], Proposition 4.3.2).

References: [Hörmander][Hormander1973] (1973), Section 2.7;
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Section 4.3.

## Main definitions

* `mvPolynomialMap`: The polynomial map with components `G i`.

## Main results

* `IsCompleteReinhardt.isRungeDomain`: **Complete Reinhardt open sets are Runge domains** :
  holomorphic functions are locally uniform sums of their Taylor series at the origin.
* `IsCircular.isRungeDomain`: **Circular connected open sets containing the origin are Runge
  domains** : holomorphic functions are locally uniform sums of their homogeneous expansions, whose
  terms are polynomials.
* `IsRungeDomain.transport`: **Transport of Runge domains.** If `U` is a Runge domain, `Φ` is
  holomorphic on `U` with values in `U'`, and `Ψ` is a polynomial map from `U'` into `U` with `Φ ∘ Ψ
  = id` on `U'`, then `U'` is a Runge domain.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {n : ℕ}

section Reinhardt

/-- **Complete Reinhardt open sets are Runge domains**: holomorphic functions are locally uniform
sums of their Taylor series at the origin. -/
theorem IsCompleteReinhardt.isRungeDomain {U : Set (Fin n → ℂ)} (ho : IsOpen U)
    (hc : IsCompleteReinhardt U) : IsRungeDomain U := by
  intro f hf K hK hKU ε hε
  obtain ⟨hdom, heq⟩
    := IsCompleteReinhardt.subset_convergenceDomain_and_eqOn_powerSeriesSum ho hc hf
  have hsum := hasSumUniformlyOn_powerSeries (taylorCoefficientsAtZero f) hK (hKU.trans hdom)
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn, Metric.tendstoUniformlyOn_iff] at hsum
  obtain ⟨t, ht⟩ := (hsum ε hε).exists
  obtain ⟨P, hP⟩ := exists_mvPolynomial_eval_eq_sum t (fun m => taylorCoefficientsAtZero f m)
  refine ⟨P, fun z hz => ?_⟩
  have := ht z hz
  rw [dist_eq_norm, heq (hKU hz)] at this
  rw [hP z]
  simpa only [smul_eq_mul] using this

/-- Polydiscs centered at the origin are Runge domains. -/
theorem isRungeDomain_polydisc (r : Fin n → ℝ) :
    IsRungeDomain (polydisc (0 : Fin n → ℂ) r) :=
  (isCompleteReinhardt_polydisc r).isRungeDomain (isOpen_polydisc 0 r)

/-- Balls centered at the origin are Runge domains. -/
theorem isRungeDomain_ball (r : ℝ) : IsRungeDomain (ball (0 : Fin n → ℂ) r) := by
  refine IsCompleteReinhardt.isRungeDomain isOpen_ball fun z hz w hw => ?_
  rw [mem_ball_zero_iff] at hz ⊢
  refine lt_of_le_of_lt ?_ hz
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg z)]
  exact fun i => (hw i).trans (norm_le_pi_norm z i)

end Reinhardt

section Circular

/-- The restriction of a continuous multilinear map on `ℂⁿ` to the diagonal is a polynomial. -/
theorem exists_mvPolynomial_eval_eq_multilinear_diagonal {k : ℕ}
    (m : ContinuousMultilinearMap ℂ (fun _ : Fin k => (Fin n → ℂ)) ℂ) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ z, MvPolynomial.eval z P = m (fun _ => z) := by
  refine ⟨∑ r : Fin k → Fin n, MvPolynomial.C (m fun j => Pi.single (r j) (1 : ℂ)) *
    ∏ j, MvPolynomial.X (r j), fun z => ?_⟩
  have hz : (fun _ : Fin k => z) = fun _ => ∑ i : Fin n, z i • Pi.single i (1 : ℂ) := by
    funext _ j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hz, ContinuousMultilinearMap.map_sum]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]

/-- Homogeneous terms of power series on `ℂⁿ` are polynomials. -/
theorem exists_mvPolynomial_eval_eq_homogeneousTerm
    (p : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ) (k : ℕ) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ z, MvPolynomial.eval z P = homogeneousTerm p k z := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_eval_eq_multilinear_diagonal (p k)
  exact ⟨P, fun z => by rw [hP, homogeneousTerm_apply]⟩

/-- **Circular connected open sets containing the origin are Runge domains**: holomorphic
functions are locally uniform sums of their homogeneous expansions, whose terms are
polynomials. -/
theorem IsCircular.isRungeDomain {U : Set (Fin n → ℂ)} (ho : IsOpen U) (hc : IsPreconnected U)
    (hrot : IsCircular U) (hzero : (0 : Fin n → ℂ) ∈ U) : IsRungeDomain U := by
  intro f hf K hK hKU ε hε
  obtain ⟨p, hp⟩ := hf 0 hzero
  have hsum :=
    (IsCircular.hasSumLocallyUniformlyOn_homogeneousTerm_balancedHull ho hc hrot hzero hf hp).1
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hsum
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hsum.mono hKU)
  rw [Metric.tendstoUniformlyOn_iff] at hu
  obtain ⟨t, ht⟩ := (hu ε hε).exists
  choose Q hQ using exists_mvPolynomial_eval_eq_homogeneousTerm p
  refine ⟨∑ k ∈ t, Q k, fun z hz => ?_⟩
  have := ht z hz
  rw [dist_eq_norm] at this
  simpa only [map_sum, hQ] using this

end Circular

section Transport

/-- The polynomial map with components `G i`. -/
@[expose] def mvPolynomialMap (G : Fin n → MvPolynomial (Fin n) ℂ) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun i => MvPolynomial.eval z (G i)

/-- Polynomial maps are continuous. -/
theorem continuous_mvPolynomialMap (G : Fin n → MvPolynomial (Fin n) ℂ) :
    Continuous (mvPolynomialMap G) :=
  continuous_pi fun i => (G i).continuous_eval

/-- Substitution of a polynomial map into a polynomial. -/
theorem eval_bind₁_mvPolynomialMap (G : Fin n → MvPolynomial (Fin n) ℂ)
    (P : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂ) :
    MvPolynomial.eval z (MvPolynomial.bind₁ G P) = MvPolynomial.eval (mvPolynomialMap G z) P := by
  simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  rfl

/-- **Transport of Runge domains.** If `U` is a Runge domain, `Φ` is holomorphic on `U` with
values in `U'`, and `Ψ` is a polynomial map from `U'` into `U` with `Φ ∘ Ψ = id` on `U'`, then
`U'` is a Runge domain. -/
theorem IsRungeDomain.transport {U U' : Set (Fin n → ℂ)} (hU : IsRungeDomain U)
    {Φ : (Fin n → ℂ) → (Fin n → ℂ)} (hΦ : AnalyticOnNhd ℂ Φ U) (hΦU : MapsTo Φ U U')
    (G : Fin n → MvPolynomial (Fin n) ℂ) (hGU : MapsTo (mvPolynomialMap G) U' U)
    (hinv : ∀ z ∈ U', Φ (mvPolynomialMap G z) = z) : IsRungeDomain U' := by
  intro f hf K hK hKU ε hε
  have hfΦ : AnalyticOnNhd ℂ (f ∘ Φ) U := hf.comp hΦ hΦU
  have hK' : IsCompact (mvPolynomialMap G '' K) := hK.image (continuous_mvPolynomialMap G)
  obtain ⟨P, hP⟩ := hU (f ∘ Φ) hfΦ _ hK' (image_subset_iff.mpr fun z hz => hGU (hKU hz)) ε hε
  refine ⟨MvPolynomial.bind₁ G P, fun z hz => ?_⟩
  have := hP (mvPolynomialMap G z) (mem_image_of_mem _ hz)
  rw [eval_bind₁_mvPolynomialMap]
  simpa [comp_apply, hinv z (hKU hz)] using this

/-- Runge domains are transported by polynomial automorphisms with polynomial inverses. -/
theorem IsRungeDomain.image_mvPolynomialMap {U : Set (Fin n → ℂ)} (hU : IsRungeDomain U)
    (F G : Fin n → MvPolynomial (Fin n) ℂ)
    (hFG : ∀ z, mvPolynomialMap F (mvPolynomialMap G z) = z)
    (hGF : ∀ z, mvPolynomialMap G (mvPolynomialMap F z) = z) :
    IsRungeDomain (mvPolynomialMap F '' U) := by
  refine hU.transport (Φ := mvPolynomialMap F) ?_ (mapsTo_image _ _) G ?_ fun z _ => hFG z
  · exact fun z _ => by
      apply analyticAt_pi_iff.mpr
      intro i
      exact AnalyticOnNhd.eval_mvPolynomial (F i) z (mem_univ z)
  · rintro _ ⟨z, hz, rfl⟩
    rw [hGF]
    exact hz

/-- Translates of Runge domains are Runge domains. -/
theorem IsRungeDomain.translate {U : Set (Fin n → ℂ)} (hU : IsRungeDomain U) (a : Fin n → ℂ) :
    IsRungeDomain ((fun z => z + a) '' U) := by
  have hF : (fun z : Fin n → ℂ => z + a) =
      mvPolynomialMap (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) := by
    funext z i
    simp [mvPolynomialMap]
  rw [hF]
  refine hU.image_mvPolynomialMap _ (fun i => MvPolynomial.X i - MvPolynomial.C (a i)) ?_ ?_ <;>
    · intro z
      funext i
      simp [mvPolynomialMap]

end Transport

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
