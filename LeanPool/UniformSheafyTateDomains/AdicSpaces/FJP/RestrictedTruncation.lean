/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.TateTaylor

/-!
# Truncation convergence over general coefficients

([hrw-decomposition] BETA prep.)  Total-degree truncations of a restricted
power series over any normed ultrametric coefficient ring converge to the
series in the Gauss norm; consequently a series all of whose coefficients
lie in an ideal `𝔭` of the coefficient ring lies in the closure of the
extension ideal — so in the extension ideal itself whenever the latter is
closed (Wedhorn 6.17 for strongly noetherian Tate coefficients).
-/

@[expose] public section

@[expose] public section

namespace FiniteJet.GraphKoszul

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E]
  [NormOneClass E] [CompleteSpace E] {k : ℕ}

/-- Truncations converge to the series in the Gauss norm. -/
theorem tendsto_polyToP_truncTotal (F : P E k) :
    Filter.Tendsto
      (fun n => polyToP (E := E) (MvPowerSeries.truncTotal n F.1))
      Filter.atTop (nhds F) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hF : Filter.Tendsto (fun t : Fin k →₀ ℕ =>
      ‖MvPowerSeries.coeff t F.1‖) Filter.cofinite (nhds 0) := by
    have h0 := F.2
    have h1 : Filter.Tendsto (fun t : Fin k →₀ ℕ =>
        ‖MvPowerSeries.coeff t F.1‖ *
          t.prod fun j l => (fun _ : Fin k => (1 : ℝ)) j ^ l)
        Filter.cofinite (nhds 0) := h0
    simpa only [weight_one, mul_one] using h1
  have hfin : {t : Fin k →₀ ℕ |
      ¬ ‖MvPowerSeries.coeff t F.1‖ < ε / 2}.Finite := by
    have h2 := hF.eventually
      (eventually_lt_nhds (by positivity : (0 : ℝ) < ε / 2))
    simpa using h2
  refine ⟨(hfin.toFinset.sup fun t => Finsupp.degree t) + 1,
    fun n hn => ?_⟩
  rw [dist_comm, dist_eq_norm]
  have hcoeff : ∀ t : Fin k →₀ ℕ,
      ‖MvPowerSeries.coeff t
        ((F - polyToP (MvPowerSeries.truncTotal n F.1)).1)‖ ≤ ε / 2 := by
    intro t
    have hco : MvPowerSeries.coeff t
        ((F - polyToP (MvPowerSeries.truncTotal n F.1)).1) =
        MvPowerSeries.coeff t F.1 -
          (MvPowerSeries.truncTotal n F.1).coeff t := by
      have h3 : ((F - polyToP (MvPowerSeries.truncTotal n F.1)).1) =
          F.1 - ((MvPowerSeries.truncTotal n F.1 :
            MvPolynomial (Fin k) E) : MvPowerSeries (Fin k) E) := rfl
      rw [h3, map_sub, MvPolynomial.coeff_coe]
    rcases lt_or_ge (Finsupp.degree t) n with hdeg | hdeg
    · have h5 : (MvPowerSeries.truncTotal n F.1).coeff t =
          MvPowerSeries.coeff t F.1 :=
        MvPowerSeries.coeff_truncTotal (p := F.1) (h := hdeg)
      rw [hco, h5, sub_self, norm_zero]
      positivity
    · have h6 : (MvPowerSeries.truncTotal n F.1).coeff t = 0 :=
        MvPowerSeries.coeff_truncTotal_eq_zero F.1 hdeg
      rw [hco, h6, sub_zero]
      by_contra hbig
      push_neg at hbig
      have hmem : t ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact not_lt.mpr hbig.le
      have h4 : Finsupp.degree t ≤
          hfin.toFinset.sup fun t => Finsupp.degree t :=
        Finset.le_sup hmem
      omega
  have hnorm : ‖F - polyToP (MvPowerSeries.truncTotal n F.1)‖ ≤ ε / 2 := by
    rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
    refine ciSup_le fun t => ?_
    rw [weight_one, mul_one]
    exact hcoeff t
  linarith

/-- Polynomials with coefficients in an ideal lie in the extension ideal. -/
theorem polyToP_mem_map_of_coeff_mem (𝔭 : Ideal E)
    (p : MvPolynomial (Fin k) E) (hp : ∀ t, p.coeff t ∈ 𝔭) :
    polyToP (E := E) p ∈
      Ideal.map ((polyToP (E := E) (m := k)).comp
        (MvPolynomial.C : E →+* MvPolynomial (Fin k) E)) 𝔭 := by
  classical
  rw [p.as_sum, map_sum]
  refine Ideal.sum_mem _ fun v _ => ?_
  have h1 : (MvPolynomial.monomial v) (p.coeff v) =
      MvPolynomial.C (p.coeff v) * MvPolynomial.monomial v 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [h1, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hp v))

/-- **A restricted series with coefficients in `𝔭` lies in the extension
ideal**, provided the extension ideal is closed (Wedhorn 6.17 input). -/
theorem mem_map_of_coeff_mem (𝔭 : Ideal E) (F : P E k)
    (hF : ∀ t, MvPowerSeries.coeff t F.1 ∈ 𝔭)
    (hclosed : IsClosed ((Ideal.map ((polyToP (E := E) (m := k)).comp
      (MvPolynomial.C : E →+* MvPolynomial (Fin k) E)) 𝔭 :
        Ideal (P E k)) : Set (P E k))) :
    F ∈ Ideal.map ((polyToP (E := E) (m := k)).comp
      (MvPolynomial.C : E →+* MvPolynomial (Fin k) E)) 𝔭 := by
  have htend := tendsto_polyToP_truncTotal F
  refine hclosed.mem_of_tendsto htend ?_
  refine Filter.Eventually.of_forall fun n => ?_
  refine polyToP_mem_map_of_coeff_mem 𝔭 _ fun t => ?_
  by_cases hdeg : Finsupp.degree t < n
  · rw [show (MvPowerSeries.truncTotal n F.1).coeff t =
        MvPowerSeries.coeff t F.1 from
      MvPowerSeries.coeff_truncTotal (p := F.1) (h := hdeg)]
    exact hF t
  · rw [show (MvPowerSeries.truncTotal n F.1).coeff t = 0 from
      MvPowerSeries.coeff_truncTotal_eq_zero F.1 (not_lt.mp hdeg)]
    exact 𝔭.zero_mem

end FiniteJet.GraphKoszul
