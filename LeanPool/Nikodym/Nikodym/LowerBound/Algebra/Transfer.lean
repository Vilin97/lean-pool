/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.BaseChange
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.BaseChangePrime
public import LeanPool.Nikodym.Nikodym.LowerBound.Jets.LowerBound

/-!
# Transfer of the algebraic interface along `K ⊆ RatFunc K`

This file implements the items **TR5** and **TR7** of the base-change node **TR** of
`docs/algebra_backend_design.md`. Throughout, `P := MvPolynomial (Fin d) K`,
`P' := MvPolynomial (Fin d) (RatFunc K)` and
`ι := MvPolynomial.map (algebraMap K (RatFunc K)) : P →+* P'`.

* **TR5** `minimalPrimes_map_ratFunc : (I.map ι).minimalPrimes = Ideal.map ι '' I.minimalPrimes`:
  the minimal primes over the extended ideal are exactly the extensions of the minimal primes
  over `I`. Extensions of primes are prime (TR4, `isPrime_map_ratFunc`), extension is injective
  and inverted by contraction (TR1, `comap_map_eq_self`), and every prime over `I.map ι`
  contracts to a prime over `I`.
* **TR7** `algebraInterface_of_infinite`: the assembly of `AlgebraInterface K d` for an
  *arbitrary* field `K` from the three input theorems A08, J02, B03 over the infinite field
  `RatFunc K`. The theorem takes A08 and B03 over `RatFunc K` as hypotheses (in exactly the
  shapes of the contracts `hilbert_le_degree_mul_choose_of_infinite` and
  `proper_cut_of_infinite` of the design document); J02 is `choose_le_jetDim_of_infinite`.
  All three fields are transported back to `K` with TR1–TR6 and TR5: the Hilbert function,
  degree, quotient dimension and jet dimension are invariant under `ι`, and for B03 the finset
  of minimal primes over `K` is `S := (finite_minimalPrimes_sup K I g).toFinset`, whose image
  under `Ideal.map ι` is the finset of minimal primes over `RatFunc K`
  (`toFinset_minimalPrimes_sup_map_ratFunc`), so that the degree sum is transported by
  `Finset.sum_image`.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- The base-change ring homomorphism `ι : P → P'` for `K' = RatFunc K`. -/
local notation "ι" => (MvPolynomial.map (algebraMap K (RatFunc K)) :
  MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) (RatFunc K))

/-! ### TR5: minimal primes under base change to `RatFunc K` -/

section MinimalPrimes

/-- Blueprint TR5 (one inclusion): the extension of a minimal prime over `I` is a minimal prime
over `I.map ι`. A prime `q` with `I.map ι ≤ q ≤ J.map ι` contracts to a prime between `I` and
`J`, hence to `J`, so `J.map ι = (q.comap ι).map ι ≤ q`. -/
theorem map_mem_minimalPrimes_map_ratFunc {I J : Ideal (MvPolynomial (Fin d) K)}
    (hJ : J ∈ I.minimalPrimes) : J.map ι ∈ (I.map ι).minimalPrimes := by
  have : J.IsPrime := hJ.1.1
  refine ⟨⟨isPrime_map_ratFunc J, Ideal.map_mono hJ.1.2⟩, fun q hq hqJ ↦ ?_⟩
  have : q.IsPrime := hq.1
  have h1 : I ≤ q.comap ι := Ideal.map_le_iff_le_comap.mp hq.2
  have h2 : q.comap ι ≤ J := by
    have h := Ideal.comap_mono (f := ι) hqJ
    rwa [comap_map_eq_self] at h
  have hJ' : Minimal (fun q ↦ q.IsPrime ∧ I ≤ q) J := hJ
  have h3 : q.comap ι = J := hJ'.eq_of_le ⟨Ideal.comap_isPrime ι q, h1⟩ h2
  calc J.map ι = (q.comap ι).map ι := by rw [h3]
    _ ≤ q := Ideal.map_comap_le

/-- Blueprint TR5: **the minimal primes over `I.map ι` are the extensions of the minimal primes
over `I`**, for `ι : P → P'` the base change to `RatFunc K`. -/
theorem minimalPrimes_map_ratFunc (I : Ideal (MvPolynomial (Fin d) K)) :
    (I.map ι).minimalPrimes = Ideal.map ι '' I.minimalPrimes := by
  ext q
  constructor
  · intro hq
    have hq' : Minimal (fun p ↦ p.IsPrime ∧ I.map ι ≤ p) q := hq
    have : q.IsPrime := hq.1.1
    obtain ⟨J, hJ, hJq⟩ := Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp hq.1.2)
    exact ⟨J, hJ,
      hq'.eq_of_le (map_mem_minimalPrimes_map_ratFunc hJ).1 (Ideal.map_le_iff_le_comap.mpr hJq)⟩
  · rintro ⟨J, hJ, rfl⟩
    exact map_mem_minimalPrimes_map_ratFunc hJ

/-- Blueprint TR5: the base change of `I + (g)` is `I.map ι + (ι g)`. -/
theorem map_sup_span_singleton (I : Ideal (MvPolynomial (Fin d) K)) (g : MvPolynomial (Fin d) K) :
    I.map ι ⊔ Ideal.span {ι g} = (I ⊔ Ideal.span {g}).map ι := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]

/-- Blueprint TR5: the finset of minimal primes over `I.map ι + (ι g)` is the image under
`Ideal.map ι` of the finset of minimal primes over `I + (g)`. -/
theorem toFinset_minimalPrimes_sup_map_ratFunc (I : Ideal (MvPolynomial (Fin d) K))
    (g : MvPolynomial (Fin d) K) :
    (finite_minimalPrimes_sup (RatFunc K) (I.map ι) (ι g)).toFinset =
      (finite_minimalPrimes_sup K I g).toFinset.image (Ideal.map ι) := by
  ext q
  simp only [Set.Finite.mem_toFinset, Finset.mem_image]
  rw [map_sup_span_singleton, minimalPrimes_map_ratFunc, Set.mem_image]

/-- Blueprint TR5: transport of a sum over the minimal primes of `I.map ι + (ι g)` to a sum over
the minimal primes of `I + (g)`. -/
theorem sum_minimalPrimes_sup_map_ratFunc (I : Ideal (MvPolynomial (Fin d) K))
    (g : MvPolynomial (Fin d) K) (φ : Ideal (MvPolynomial (Fin d) (RatFunc K)) → ℕ) :
    ∑ J ∈ (finite_minimalPrimes_sup (RatFunc K) (I.map ι) (ι g)).toFinset, φ J =
      ∑ J ∈ (finite_minimalPrimes_sup K I g).toFinset, φ (J.map ι) := by
  rw [toFinset_minimalPrimes_sup_map_ratFunc]
  exact Finset.sum_image fun _ _ _ _ h ↦ map_injective h

end MinimalPrimes

/-! ### TR7: assembly of the algebraic interface over an arbitrary field -/

section Assembly

/-- Blueprint TR7: **the algebraic interface over an arbitrary field `K`**, assembled from the
input theorems A08 (`hA08`) and B03 (`hB03`) over the infinite field `RatFunc K` and from J02
(`choose_le_jetDim_of_infinite`). Every statement is transported along
`ι = MvPolynomial.map (algebraMap K (RatFunc K))`, using that `ι` preserves primality (TR4),
the Hilbert function, the degree (TR2), the quotient dimension (TR3), the jet dimension (TR6)
and minimal primes (TR5). -/
theorem algebraInterface_of_infinite
    (hA08 : ∀ (I : Ideal (MvPolynomial (Fin d) (RatFunc K))), I.IsPrime → ∀ t : ℕ,
      hilbert I t ≤ degree I * (t + quotDim I).choose (quotDim I))
    (hB03 : ∀ (I : Ideal (MvPolynomial (Fin d) (RatFunc K))), I.IsPrime → 2 ≤ quotDim I →
      ∀ (g : MvPolynomial (Fin d) (RatFunc K)) (T : ℕ), g ∉ I → g.totalDegree ≤ T →
        I ⊔ Ideal.span {g} ≠ ⊤ →
        (∀ J ∈ (I ⊔ Ideal.span {g}).minimalPrimes, 0 < degree J) ∧
        ∑ J ∈ (finite_minimalPrimes_sup (RatFunc K) I g).toFinset, degree J ≤ T * degree I) :
    AlgebraInterface K d := by
  refine AlgebraInterface.mk' ?_ ?_ ?_
  · -- A08
    intro I hI t
    have := hI
    have h := hA08 (I.map ι) (isPrime_map_ratFunc I) t
    rwa [hilbert_map, degree_map, quotDim_map] at h
  · -- J02
    intro I hI x hx r hr
    have := hI
    have := isPrime_map_ratFunc I
    have hx' : I.map ι ≤ pointIdeal (fun i ↦ algebraMap K (RatFunc K) (x i)) := by
      rw [← map_pointIdeal]
      exact Ideal.map_mono hx
    have h := choose_le_jetDim_of_infinite (I.map ι) _ hx' hr
    rwa [jetDim_map I x hr, quotDim_map] at h
  · -- B03
    intro I hI hk g T hg hT hne
    have := hI
    have := isPrime_map_ratFunc I
    have hmem : ∀ J, J ∈ (finite_minimalPrimes_sup K I g).toFinset ↔
        J ∈ (I ⊔ Ideal.span {g}).minimalPrimes := fun J ↦ Set.Finite.mem_toFinset _
    have hg' : ι g ∉ I.map ι := (mem_map_iff I g).not.mpr hg
    have hT' : (ι g).totalDegree ≤ T := by rwa [totalDegree_map]
    have hne' : I.map ι ⊔ Ideal.span {ι g} ≠ ⊤ := by
      rw [map_sup_span_singleton]
      exact (map_ne_top_iff _).mpr hne
    have hk' : 2 ≤ quotDim (I.map ι) := by rwa [quotDim_map]
    obtain ⟨hpos, hsum⟩ := hB03 (I.map ι) inferInstance hk' (ι g) T hg' hT' hne'
    refine ⟨(finite_minimalPrimes_sup K I g).toFinset, fun J hJ ↦ ((hmem J).mp hJ).1.1,
      fun J hJ ↦ ((hmem J).mp hJ).1.2,
      fun J hJ ↦ quotDim_add_one_of_mem_minimalPrimes_sup hg ((hmem J).mp hJ),
      fun J hJ ↦ ?_, ?_, fun Q hQ hIQ ↦ ?_⟩
    · have h := hpos (J.map ι) (by
        rw [map_sup_span_singleton, minimalPrimes_map_ratFunc]
        exact ⟨J, (hmem J).mp hJ, rfl⟩)
      rwa [degree_map] at h
    · rw [sum_minimalPrimes_sup_map_ratFunc, degree_map] at hsum
      simpa only [degree_map] using hsum
    · have := hQ
      obtain ⟨J, hJ, hJQ⟩ := exists_minimalPrimes_le K _ hIQ
      exact ⟨J, (hmem J).mpr hJ, hJQ⟩

end Assembly

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
