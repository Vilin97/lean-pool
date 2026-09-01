/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Noetherian.Ruckert
import LeanPool.LocalComplexGeometry.Nullstellensatz.ZeroSetGerms
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Reduction of the analytic Nullstellensatz to prime ideals

This module contains no geometric assertion about prime ideals.  Instead it
isolates that assertion as `PrimeZeroSetProperty` and proves that it suffices
for the radical theorem, the finite-family representative-level theorem, and
the arbitrary-ideal zero-set equality.
-/

open Filter
open scoped BigOperators Topology


namespace LocalComplexGeometry

noncomputable section

/--
The prime-ideal zero-set statement in complex dimension `n`: every prime ideal
is exactly the ideal of holomorphic germs vanishing on the local zero-set germ
of any finite generating set selected for that prime.
-/
def PrimeZeroSetProperty (n : ℕ) : Prop :=
  ∀ P : Ideal (HolomorphicGerm n), P.IsPrime →
    vanishingIdeal (idealZeroSetGerm P) = P

/-- Vanishing on a fixed local set germ is a radical condition. -/
theorem vanishingIdeal_isRadical {n : ℕ} (Z : LocalSetGerm n) :
    (vanishingIdeal Z).IsRadical := by
  intro f hf
  obtain ⟨k, hfk⟩ := hf
  by_cases hk : k = 0
  · subst k
    have hone : (1 : HolomorphicGerm n) ∈ vanishingIdeal Z := by
      simpa using hfk
    have htop : vanishingIdeal Z = ⊤ :=
      (Ideal.eq_top_iff_one (vanishingIdeal Z)).2 hone
    rw [htop]
    exact Submodule.mem_top
  · change Z ≤ germZeroLocus f
    have hpow : Z ≤ germZeroLocus (f ^ k) := hfk
    rwa [germZeroLocus_pow f (Nat.pos_of_ne_zero hk)] at hpow

/--
Prime zero-set information implies the arbitrary-ideal radical equality.

The proof intersects the minimal primes above `I`.  It also applies to
`I = ⊤`: then the set of minimal primes is empty and its infimum is `⊤`.
-/
theorem vanishingIdeal_idealZeroSetGerm_eq_radical
    {n : ℕ} (hprime : PrimeZeroSetProperty n)
    (I : Ideal (HolomorphicGerm n)) :
    vanishingIdeal (idealZeroSetGerm I) = I.radical := by
  apply le_antisymm
  · intro g hg
    rw [← I.sInf_minimalPrimes, Ideal.mem_sInf]
    intro P hP
    have hPI : I ≤ P := hP.1.2
    have hzeroPI : idealZeroSetGerm P ≤ idealZeroSetGerm I :=
      idealZeroSetGerm_antitone hPI
    have hgP : g ∈ vanishingIdeal (idealZeroSetGerm P) :=
      hzeroPI.trans hg
    rw [hprime P hP.1.1] at hgP
    exact hgP
  · apply (vanishingIdeal_isRadical (idealZeroSetGerm I)).radical_le_iff.2
    intro f hf
    exact idealZeroSetGerm_le_germZeroLocus_of_mem I hf

/-- Explicit `I = ⊤` specialization of the radical reduction. -/
theorem vanishingIdeal_idealZeroSetGerm_top_of_primeZeroSetProperty
    {n : ℕ} (hprime : PrimeZeroSetProperty n) :
    vanishingIdeal
      (idealZeroSetGerm (⊤ : Ideal (HolomorphicGerm n))) = ⊤ := by
  rw [vanishingIdeal_idealZeroSetGerm_eq_radical hprime]
  exact Ideal.radical_top (HolomorphicGerm n)

open scoped Classical in
/-- The zero set of a finite image is the indexed common zero-set germ. -/
theorem finiteCommonZeroSet_image_univ_eq_indexedCommonZeroSet
    {n s : ℕ} (f : Fin s → HolomorphicGerm n) :
    finiteCommonZeroSet (Finset.univ.image f) = indexedCommonZeroSet f := by
  classical
  unfold finiteCommonZeroSet indexedCommonZeroSet
  rw [Finset.inf_image]
  rfl

open scoped Classical in
/-- The ideal spanned by a finite image is the ideal spanned by its range. -/
theorem span_image_univ_eq_span_range
    {n s : ℕ} (f : Fin s → HolomorphicGerm n) :
    Ideal.span ((Finset.univ.image f : Finset (HolomorphicGerm n)) :
      Set (HolomorphicGerm n)) = Ideal.span (Set.range f) := by
  classical
  congr 1
  ext g
  simp

/--
The exact comparator-facing finite-family Nullstellensatz follows from the
prime zero-set property.  The exponent is made positive by replacing an
arbitrary radical witness `k` by `k + 1`; this also handles the case where the
generated ideal is `⊤`.
-/
theorem localAnalyticNullstellensatz_of_primeZeroSetProperty
    {n s : ℕ} (hprime : PrimeZeroSetProperty n)
    {f : Fin s → ComplexEuclidean n → ℂ}
    {g : ComplexEuclidean n → ℂ}
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (hg : AnalyticAt ℂ g 0)
    (hzero : ∀ᶠ x in 𝓝 (0 : ComplexEuclidean n),
      (∀ i, f i x = 0) → g x = 0) :
    ∃ N : ℕ, 0 < N ∧
      ∃ h : Fin s → ComplexEuclidean n → ℂ,
        (∀ i, AnalyticAt ℂ (h i) 0) ∧
        (fun x ↦ g x ^ N) =ᶠ[𝓝 0]
          fun x ↦ ∑ i, h i x * f i x := by
  classical
  let F : Fin s → HolomorphicGerm n :=
    fun i ↦ HolomorphicGerm.ofFunction (f i) (hf i)
  let G : HolomorphicGerm n := HolomorphicGerm.ofFunction g hg
  let I : Ideal (HolomorphicGerm n) := Ideal.span (Set.range F)
  have hspan : Ideal.span
      ((Finset.univ.image F : Finset (HolomorphicGerm n)) :
        Set (HolomorphicGerm n)) = I := by
    change Ideal.span
      ((Finset.univ.image F : Finset (HolomorphicGerm n)) :
        Set (HolomorphicGerm n)) = Ideal.span (Set.range F)
    exact span_image_univ_eq_span_range F
  have hzeroSet : idealZeroSetGerm I = indexedCommonZeroSet F := by
    calc
      idealZeroSetGerm I =
          finiteCommonZeroSet (Finset.univ.image F) :=
        idealZeroSetGerm_eq_of_span_eq I (Finset.univ.image F) hspan
      _ = indexedCommonZeroSet F :=
        finiteCommonZeroSet_image_univ_eq_indexedCommonZeroSet F
  have hGvanish : G ∈ vanishingIdeal (idealZeroSetGerm I) := by
    change idealZeroSetGerm I ≤ germZeroLocus G
    rw [hzeroSet]
    exact (indexedCommonZeroSet_le_iff_eventually f hf g hg).2 hzero
  have hGradical : G ∈ I.radical := by
    rw [← vanishingIdeal_idealZeroSetGerm_eq_radical hprime I]
    exact hGvanish
  obtain ⟨k, hGk⟩ := hGradical
  have hGsucc : G ^ (k + 1) ∈ I := by
    rw [pow_succ']
    exact I.mul_mem_left G hGk
  have hGspan : G ^ (k + 1) ∈ Ideal.span (Set.range F) := by
    exact hGsucc
  obtain ⟨c, hc⟩ :=
    Ideal.mem_span_range_iff_exists_fun.mp hGspan
  choose h hh hrep using fun i ↦ HolomorphicGerm.exists_rep (c i)
  have hgerm : G ^ (k + 1) = ∑ i, c i * F i := hc.symm
  have hgermCoe := congrArg
    (fun φ : HolomorphicGerm n ↦ (φ : FunctionGerm n)) hgerm
  simp only [Subring.coe_pow, AddSubmonoidClass.coe_finsetSum,
    Subring.coe_mul] at hgermCoe
  have hGcoe : (G : FunctionGerm n) = g := rfl
  have hFcoe : ∀ i, (F i : FunctionGerm n) = f i := fun _ ↦ rfl
  rw [hGcoe] at hgermCoe
  simp_rw [← hrep, hFcoe] at hgermCoe
  have hleft :
      (((fun x ↦ g x ^ (k + 1)) : ComplexEuclidean n → ℂ) :
          FunctionGerm n) =
        (g : FunctionGerm n) ^ (k + 1) :=
    Filter.Germ.coe_pow g (k + 1)
  have hright :
      (((fun x ↦ ∑ i, h i x * f i x) :
          ComplexEuclidean n → ℂ) : FunctionGerm n) =
        ∑ i, (h i : FunctionGerm n) * (f i : FunctionGerm n) := by
    calc
      _ = ∑ i,
          (((fun x ↦ h i x * f i x) : ComplexEuclidean n → ℂ) :
            FunctionGerm n) := by
          rw [show (fun x ↦ ∑ i, h i x * f i x) =
              ∑ i, (fun x ↦ h i x * f i x) by
            funext x
            simp]
          exact map_sum (Filter.Germ.coeRingHom
              (𝓝 (0 : ComplexEuclidean n)))
            (fun i ↦ fun x ↦ h i x * f i x) Finset.univ
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact Filter.Germ.coe_mul (h i) (f i)
  refine ⟨k + 1, Nat.zero_lt_succ k, h, hh, ?_⟩
  apply Filter.Germ.coe_eq.mp
  exact hleft.trans (hgermCoe.trans hright.symm)

/--
The empty-family specialization.  Its common-zero hypothesis says exactly
that `g` is the zero germ, and the general reduction still returns a positive
exponent.
-/
theorem localAnalyticNullstellensatz_empty_of_primeZeroSetProperty
    {n : ℕ} (hprime : PrimeZeroSetProperty n)
    {g : ComplexEuclidean n → ℂ}
    (hg : AnalyticAt ℂ g 0)
    (hzero : g =ᶠ[𝓝 (0 : ComplexEuclidean n)] (fun _ ↦ 0)) :
    ∃ N : ℕ, 0 < N ∧
      (fun x ↦ g x ^ N) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
  let f : Fin 0 → ComplexEuclidean n → ℂ := fun i ↦ Fin.elim0 i
  have hf : ∀ i, AnalyticAt ℂ (f i) 0 := by
    intro i
    exact Fin.elim0 i
  have hcommon : ∀ᶠ x in 𝓝 (0 : ComplexEuclidean n),
      (∀ i, f i x = 0) → g x = 0 :=
    hzero.mono fun _ hx _ ↦ hx
  obtain ⟨N, hN, h, hh, hcertificate⟩ :=
    localAnalyticNullstellensatz_of_primeZeroSetProperty
      hprime hf hg hcommon
  refine ⟨N, hN, ?_⟩
  filter_upwards [hcertificate] with x hx
  simpa [f] using hx

end


end LocalComplexGeometry
