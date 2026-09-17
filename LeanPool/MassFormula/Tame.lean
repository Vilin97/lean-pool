/-
Copyright (c) 2026 Hyeon Seung-Hyeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hyeon Seung-Hyeon
-/

-- Adapted for Lean Pool from 0stellensatz/MassFormula at 7fa41a621f724f110183904d3fd19c6730a932ad.
module

public import LeanPool.MassFormula.Defs
import LeanPool.MassFormula.Discriminant
import LeanPool.MassFormula.Finiteness
import LeanPool.MassFormula.UniformizerParam
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Auxiliary file: `c_eq_zero_iff`—tameness as the vanishing of `c` (p.1031)

The paper states that `c L = 0` exactly when `n` is prime to the residue characteristic `p`, in
other words when `L` / `K` is tamely ramified ([Serre 1978, p.1031][Serre1978]). Both directions
come from the same coefficient-by-coefficient valuation bookkeeping at an Eisenstein generator, with
no different ideal and no tame classification:

- *`p ∤ n` implies `c L = 0`*—the residue of `n` is then nonzero, so `n` is a unit of `𝒪[K]`
  (`addVal_natCast_eq_zero`), and the uniform bound of the finiteness half of Remark 1°
  (`c_le_of_mem_sigma`) reads `c L ≤ 0` at `t = 0`, the valuation of `n` being zero.
- *`p ∣ n` implies `c L ≠ 0`* (`n_le_d_of_dvd`)—every coefficient of the derivative of `g` at `ξ`,
  the sum of the terms `i * a i * ξ ^ (i - 1)`, is divisible by the uniformizer: the Eisenstein
  coefficients below the top lie in `𝓂[K]` by definition, and the top one is `n` itself, which
  `p ∣ n` puts in `𝓂[K]` (`dvd_natCast_of_dvd`). Every term of the power-basis combination then has
  valuation at least `n`, so orthogonality (`le_addVal_sum_iff`) gives `n ≤ d L`, `d L` being the
  valuation of that derivative (`addVal_derivative_eq_d`); hence `1 ≤ c L`, as `c L = d L + 1 - n`.

Classically this is the characterization of tame ramification by `d = e - 1`
([Serre 1979, Chap. III, §6, Prop. 13][Serre1979]).

## References

* [Serre1978] J-P. Serre, *Une «formule de masse» pour les extensions totalement ramifiées de
  degré donné d'un corps local*, C. R. Acad. Sci. Paris **286** (1978), Série A, 1031–1036.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer, 1979.
-/

@[expose] public section

open ValuativeRel IsDiscreteValuationRing

namespace MassFormula

variable (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
  [IsNonarchimedeanLocalField K]

omit [IsUniformAddGroup K] in
/-- When the residue characteristic divides `n`, the image of `n` in `𝒪[K]` falls into the maximal
ideal—it is divisible by any uniformizer. -/
private theorem dvd_natCast_of_dvd {π : ↥𝒪[K]} (hπ : Irreducible π) (n : ℕ)
    (hdvd : ringChar 𝓀[K] ∣ n) : π ∣ (n : ↥𝒪[K]) := by
  rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff,
    map_natCast]
  exact (ringChar.spec 𝓀[K] n).mpr hdvd

omit [IsUniformAddGroup K] in
/-- When the residue characteristic does not divide `n`, the image of `n` in `𝒪[K]` is a unit: its
valuation vanishes. -/
private theorem addVal_natCast_eq_zero (n : ℕ) (hndvd : ¬ ringChar 𝓀[K] ∣ n) :
    addVal ↥𝒪[K] (n : ↥𝒪[K]) = 0 := by
  refine addVal_eq_zero_iff.mpr (IsLocalRing.notMem_maximalIdeal.mp fun hmem => hndvd ?_)
  refine (ringChar.spec 𝓀[K] n).mp ?_
  rw [← map_natCast (IsLocalRing.residue ↥𝒪[K]), IsLocalRing.residue_eq_zero_iff]
  exact hmem

omit [IsUniformAddGroup K] in
/-- The wild lower bound: when the residue characteristic divides `n`, every `L` in `sigma K n` has
`n ≤ d L`. At an Eisenstein generator `ξ` (`exists_eisenstein_generator`) every coefficient of the
derivative of `g` at `ξ`, the sum of the terms `i * a i * ξ ^ (i - 1)`, is divisible by the
uniformizer—the Eisenstein ones below the top by definition, the top one being `n` itself, which
`p ∣ n` puts in `𝓂[K]`—so every term of the sum has valuation at least `n`, and the easy direction
of orthogonality (`le_addVal_sum_iff`) gives `n ≤ d L`, `d L` being the valuation of that derivative
(`addVal_derivative_eq_d`). This is the wild half of the classical characterization of tameness by
`d = e - 1` ([Serre 1979, Chap. III, §6, Prop. 13][Serre1979]). -/
private theorem n_le_d_of_dvd (n : ℕ) (hn : 0 < n) (hdvd : ringChar 𝓀[K] ∣ n)
    (L : IntermediateField K (SeparableClosure K)) (hL : L ∈ sigma K n) : n ≤ d L := by
  obtain ⟨x, π, hπ, hint, hei, hadj, hdeg⟩ := exists_eisenstein_generator K n hn L hL
  subst hadj
  subst hdeg
  have hDVR : IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x})) :=
    isDiscreteValuationRing_integers hπ hint hei
  -- the derivative of the minimal polynomial, as a combination of the power basis
  have hmonic : (minpoly 𝒪[K] x).Monic := minpoly.monic hint
  have hderivlt : (Polynomial.derivative (minpoly 𝒪[K] x)).natDegree <
      (minpoly 𝒪[K] x).natDegree := Polynomial.natDegree_derivative_lt hn.ne'
  have hsum : Polynomial.aeval (integralGen hint) (Polynomial.derivative (minpoly 𝒪[K] x)) =
      ∑ i : Fin (minpoly 𝒪[K] x).natDegree,
        algebraMap ↥𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))
          ((Polynomial.derivative (minpoly 𝒪[K] x)).coeff (i : ℕ)) *
            integralGen hint ^ (i : ℕ) := by
    rw [Polynomial.aeval_eq_sum_range' hderivlt, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _
  -- every coefficient of the derivative is divisible by the uniformizer
  have hdvdc : ∀ i : Fin (minpoly 𝒪[K] x).natDegree,
      π ∣ (Polynomial.derivative (minpoly 𝒪[K] x)).coeff (i : ℕ) := by
    intro i
    rcases Nat.lt_or_ge ((i : ℕ) + 1) (minpoly 𝒪[K] x).natDegree with hlt | hge
    · rw [Polynomial.coeff_derivative]
      refine Dvd.dvd.mul_right (Ideal.mem_span_singleton.mp ?_) _
      have hm := hei.mem hlt
      rwa [Ideal.submodule_span_eq] at hm
    · have heq : (i : ℕ) + 1 = (minpoly 𝒪[K] x).natDegree := by
        have := i.isLt
        omega
      rw [Polynomial.coeff_derivative, heq, hmonic.coeff_natDegree, one_mul,
        ← Nat.cast_add_one, heq]
      exact dvd_natCast_of_dvd K hπ _ hdvd
  -- so every term of the power-basis combination has valuation at least `n`
  have hkey : (((minpoly 𝒪[K] x).natDegree : ℕ) : ℕ∞) ≤
      addVal ↥(integers (IntermediateField.adjoin K {x}))
        (Polynomial.aeval (integralGen hint) (Polynomial.derivative (minpoly 𝒪[K] x))) := by
    rw [hsum]
    refine (le_addVal_sum_iff hπ (irreducible_integralGen hπ hint hei) hn
      (associated_algebraMap_pow hπ hint hei) _ _).mpr fun i => ?_
    have h1 : (1 : ℕ∞) ≤
        addVal ↥𝒪[K] ((Polynomial.derivative (minpoly 𝒪[K] x)).coeff (i : ℕ)) := by
      obtain ⟨z, hz⟩ := hdvdc i
      rw [hz, addVal_mul, addVal_uniformizer hπ]
      exact le_self_add
    calc (((minpoly 𝒪[K] x).natDegree : ℕ) : ℕ∞)
        = ((minpoly 𝒪[K] x).natDegree : ℕ∞) * 1 := (mul_one _).symm
      _ ≤ ((minpoly 𝒪[K] x).natDegree : ℕ∞) *
            addVal ↥𝒪[K] ((Polynomial.derivative (minpoly 𝒪[K] x)).coeff (i : ℕ)) :=
          mul_le_mul_right h1 _
      _ ≤ ((minpoly 𝒪[K] x).natDegree : ℕ∞) *
            addVal ↥𝒪[K] ((Polynomial.derivative (minpoly 𝒪[K] x)).coeff (i : ℕ)) +
              ((i : ℕ) : ℕ∞) := le_self_add
  -- read the bound off `d`
  rw [addVal_derivative_eq_d hπ hint hei] at hkey
  exact_mod_cast hkey

omit [IsUniformAddGroup K] in
/-- `c L = 0` if and only if `n` is prime to the residue characteristic, in other words if and only
if `L` / `K` is tamely ramified, assembled from the two bounds above ([Serre 1978,
p.1031][Serre1978]). -/
theorem c_eq_zero_iff (n : ℕ) (hn : 0 < n) (L : IntermediateField K (SeparableClosure K))
    (hL : L ∈ sigma K n) : c L = 0 ↔ ¬ ringChar 𝓀[K] ∣ n := by
  constructor
  · -- contrapositively: `p ∣ n` forces `n ≤ d (L)`, so `c (L) = d (L) + 1 - n ≥ 1`
    intro hc hdvd
    have hd := n_le_d_of_dvd K n hn hdvd L hL
    have hfr : Module.finrank K ↥L = n := hL.1
    have hc' : d L + 1 - Module.finrank K ↥L = 0 := hc
    rw [hfr] at hc'
    omega
  · -- `p ∤ n` makes `n` a unit of `𝒪[K]`, and `c_le_of_mem_sigma` then reads `c (L) ≤ n * 0`
    intro hndvd
    have h := c_le_of_mem_sigma K n 0 hn
      (by rw [Nat.cast_zero]; exact addVal_natCast_eq_zero K n hndvd) L hL
    omega

end MassFormula
