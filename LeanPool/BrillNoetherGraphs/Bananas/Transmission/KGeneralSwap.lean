/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaInversionFiniteSum
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionAPI

/-!
# Swapping the marks of a graph with general transmission

Swapping the two marked vertices replaces a raw transmission permutation
`tau` by its reflected inverse

`b |-> -tau^{-1}(-b)`.

This file proves that affine inversion count is unchanged by this operation
and consequently that `KGeneralTransmission` is independent of the ordering
of the two marks.
-/

namespace Bananas

open Utilities

/-- The inverse of a bijection, kept at the raw-function level used by
`IsTransmissionPermutation`. -/
noncomputable def rawInverse (tau : ℤ → ℤ) : ℤ → ℤ :=
  Function.invFun tau

@[simp] theorem rawInverse_apply_apply (tau : ℤ → ℤ)
    (hBij : Function.Bijective tau) (n : ℤ) :
    rawInverse tau (tau n) = n := by
  exact Function.leftInverse_invFun hBij.1 n

theorem apply_rawInverse_apply (tau : ℤ → ℤ)
    (hBij : Function.Bijective tau) (n : ℤ) :
    tau (rawInverse tau n) = n := by
  exact Function.rightInverse_invFun hBij.2 n

/-- Inverting a bijective affine function preserves its period. -/
theorem IsKAffine.rawInverse {k : ℕ} {tau : ℤ → ℤ}
    (hAffine : IsKAffine k tau) (hBij : Function.Bijective tau) :
    IsKAffine k (rawInverse tau) := by
  intro n
  apply hBij.1
  rw [apply_rawInverse_apply tau hBij, hAffine,
    apply_rawInverse_apply tau hBij]

/-- Reflection in both the domain and range. -/
def rawAffineReflection (tau : ℤ → ℤ) : ℤ → ℤ :=
  fun n => -tau (-n)

/-- The reflected inverse is the raw transmission permutation after swapping
the two marks. -/
noncomputable def swapTransmissionPermutation
    (tau : ℤ → ℤ) : ℤ → ℤ :=
  rawAffineReflection (rawInverse tau)

/-- Simultaneously translate a pair by an integral number of periods. -/
def shiftPair (k : ℕ) (q : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 + q * k, p.2 + q * k)

/-- Normalize the first coordinate of a pair into the standard period. -/
def normalizeFirstPair (k : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 % k, p.2 - (p.1 / k) * k)

theorem normalizeFirstPair_eq_shiftPair (k : ℕ) (p : ℤ × ℤ) :
    normalizeFirstPair k p = shiftPair k (-(p.1 / k)) p := by
  apply Prod.ext <;> simp only [normalizeFirstPair, shiftPair]
  · have h := Int.emod_add_mul_ediv p.1 (k : ℤ)
    calc
      p.1 % (k : ℤ) = p.1 - k * (p.1 / k) := by omega
      _ = p.1 + -(p.1 / k) * k := by ring
  · ring

/-- Normalization removes any simultaneous period translate from a pair whose
first coordinate is already in the standard period. -/
theorem normalizeFirstPair_shiftPair_of_fundamental
    {k : ℕ} (hk : 0 < k) (p : ℤ × ℤ)
    (hp0 : 0 ≤ p.1) (hpk : p.1 < k) (q : ℤ) :
    normalizeFirstPair k (shiftPair k q p) = p := by
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hmod : (p.1 + q * k) % (k : ℤ) = p.1 := by
    calc
      (p.1 + q * k) % (k : ℤ) = (p.1 + k * q) % k := by
        congr 2
        ring
      _ = p.1 % k := Int.add_mul_emod_self_left _ _ _
      _ = p.1 := Int.emod_eq_of_lt hp0 hpk
  have hdiv : (p.1 + q * k) / (k : ℤ) = q := by
    calc
      (p.1 + q * k) / (k : ℤ) = (p.1 + k * q) / k := by
        congr 2
        ring
      _ = p.1 / k + q := Int.add_mul_ediv_left _ _ (by omega)
      _ = q := by
        rw [Int.ediv_eq_zero_of_lt_abs hp0
          (by simpa [abs_of_pos hkZ] using hpk)]
        omega
  apply Prod.ext <;> simp only [normalizeFirstPair, shiftPair]
  · exact hmod
  · rw [hdiv]
    ring

/-- Applying an affine function to a simultaneous period translate translates
both values by the same period. -/
theorem IsKAffine.map_shiftPair {k : ℕ} {tau : ℤ → ℤ}
    (hAffine : IsKAffine k tau) (q : ℤ) (p : ℤ × ℤ) :
    (tau (shiftPair k q p).1, tau (shiftPair k q p).2) =
      shiftPair k q (tau p.1, tau p.2) := by
  apply Prod.ext <;>
    simp only [shiftPair, hAffine.iterate_int]

/-- The pair map taking an inversion of an inverse permutation back to the
corresponding inversion of the original permutation. -/
noncomputable def inverseInversionPair
    (tau : ℤ → ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (rawInverse tau p.2, rawInverse tau p.1)

/-- The pair map taking an inversion to the corresponding inversion of the
inverse permutation. -/
def inversionInversePair (tau : ℤ → ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (tau p.2, tau p.1)

theorem inverseInversionPair_inversionInversePair
    (tau : ℤ → ℤ) (hBij : Function.Bijective tau) (p : ℤ × ℤ) :
    inverseInversionPair tau (inversionInversePair tau p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · exact rawInverse_apply_apply tau hBij x
  · exact rawInverse_apply_apply tau hBij y

theorem inversionInversePair_inverseInversionPair
    (tau : ℤ → ℤ) (hBij : Function.Bijective tau) (p : ℤ × ℤ) :
    inversionInversePair tau (inverseInversionPair tau p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · change tau (rawInverse tau x) = x
    exact apply_rawInverse_apply tau hBij x
  · change tau (rawInverse tau y) = y
    exact apply_rawInverse_apply tau hBij y

/-- Normalize the inversion of the original permutation associated to an
inversion of its inverse. -/
noncomputable def normalizedInverseToOriginal
    (k : ℕ) (tau : ℤ → ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  normalizeFirstPair k (inverseInversionPair tau p)

/-- Normalize the inversion of the inverse permutation associated to an
inversion of the original. -/
def normalizedOriginalToInverse
    (k : ℕ) (tau : ℤ → ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  normalizeFirstPair k (inversionInversePair tau p)

theorem inverseInversionPair_shiftPair
    {k : ℕ} {tau : ℤ → ℤ} (hBij : Function.Bijective tau)
    (hAffine : IsKAffine k tau) (q : ℤ) (p : ℤ × ℤ) :
    inverseInversionPair tau (shiftPair k q p) =
      shiftPair k q (inverseInversionPair tau p) := by
  have hInvAffine := hAffine.rawInverse hBij
  apply Prod.ext <;>
    simp only [inverseInversionPair, shiftPair, hInvAffine.iterate_int]

theorem inversionInversePair_shiftPair
    {k : ℕ} {tau : ℤ → ℤ} (hAffine : IsKAffine k tau)
    (q : ℤ) (p : ℤ × ℤ) :
    inversionInversePair tau (shiftPair k q p) =
      shiftPair k q (inversionInversePair tau p) := by
  apply Prod.ext <;>
    simp only [inversionInversePair, shiftPair, hAffine.iterate_int]

theorem normalizedInverseToOriginal_mem
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hBij : Function.Bijective tau) (hAffine : IsKAffine k tau)
    {p : ℤ × ℤ} (hp : p ∈ kInversions k (rawInverse tau)) :
    normalizedInverseToOriginal k tau p ∈ kInversions k tau := by
  apply inversion_normalize_first_coordinate hk hAffine
  rcases p with ⟨a, b⟩
  change a < b ∧ rawInverse tau a > rawInverse tau b ∧ _ at hp
  change rawInverse tau b < rawInverse tau a ∧
    tau (rawInverse tau b) > tau (rawInverse tau a)
  exact ⟨hp.2.1, by
    rw [apply_rawInverse_apply tau hBij,
      apply_rawInverse_apply tau hBij]
    exact hp.1⟩

theorem normalizedOriginalToInverse_mem
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hBij : Function.Bijective tau) (hAffine : IsKAffine k tau)
    {p : ℤ × ℤ} (hp : p ∈ kInversions k tau) :
    normalizedOriginalToInverse k tau p ∈
      kInversions k (rawInverse tau) := by
  apply inversion_normalize_first_coordinate hk (hAffine.rawInverse hBij)
  rcases p with ⟨x, y⟩
  change x < y ∧ tau x > tau y ∧ _ at hp
  change tau y < tau x ∧ rawInverse tau (tau y) > rawInverse tau (tau x)
  exact ⟨hp.2.1, by
    rw [rawInverse_apply_apply tau hBij,
      rawInverse_apply_apply tau hBij]
    exact hp.1⟩

theorem normalizedInverseToOriginal_normalizedOriginalToInverse
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hBij : Function.Bijective tau) (hAffine : IsKAffine k tau)
    {p : ℤ × ℤ} (hp : p ∈ kInversions k tau) :
    normalizedInverseToOriginal k tau
        (normalizedOriginalToInverse k tau p) = p := by
  let q : ℤ := -(tau p.2 / k)
  have hNorm : normalizedOriginalToInverse k tau p =
      shiftPair k q (inversionInversePair tau p) := by
    exact normalizeFirstPair_eq_shiftPair k (inversionInversePair tau p)
  rw [normalizedInverseToOriginal, hNorm,
    inverseInversionPair_shiftPair hBij hAffine,
    inverseInversionPair_inversionInversePair tau hBij]
  exact normalizeFirstPair_shiftPair_of_fundamental hk p hp.2.2.1 hp.2.2.2 q

theorem normalizedOriginalToInverse_normalizedInverseToOriginal
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hBij : Function.Bijective tau) (hAffine : IsKAffine k tau)
    {p : ℤ × ℤ} (hp : p ∈ kInversions k (rawInverse tau)) :
    normalizedOriginalToInverse k tau
        (normalizedInverseToOriginal k tau p) = p := by
  let q : ℤ := -(rawInverse tau p.2 / k)
  have hNorm : normalizedInverseToOriginal k tau p =
      shiftPair k q (inverseInversionPair tau p) := by
    exact normalizeFirstPair_eq_shiftPair k (inverseInversionPair tau p)
  rw [normalizedOriginalToInverse, hNorm,
    inversionInversePair_shiftPair hAffine,
    inversionInversePair_inverseInversionPair tau hBij]
  exact normalizeFirstPair_shiftPair_of_fundamental hk p hp.2.2.1 hp.2.2.2 q

/-- Inversion preserves the number of affine-period inversion classes. -/
theorem kInversionCount_rawInverse
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hBij : Function.Bijective tau) (hAffine : IsKAffine k tau) :
    kInversionCount k (rawInverse tau) = kInversionCount k tau := by
  unfold kInversionCount
  apply Set.ncard_congr
    (fun p _ => normalizedInverseToOriginal k tau p)
  · exact fun _ hp => normalizedInverseToOriginal_mem hk hBij hAffine hp
  · intro p p' hp hp' heq
    have := congrArg (normalizedOriginalToInverse k tau) heq
    rw [normalizedOriginalToInverse_normalizedInverseToOriginal hk hBij hAffine hp,
      normalizedOriginalToInverse_normalizedInverseToOriginal hk hBij hAffine hp'] at this
    exact this
  · intro p hp
    refine ⟨normalizedOriginalToInverse k tau p,
      normalizedOriginalToInverse_mem hk hBij hAffine hp, ?_⟩
    exact normalizedInverseToOriginal_normalizedOriginalToInverse
      hk hBij hAffine hp

/-- Reflection in the origin preserves bijectivity. -/
theorem affineReflection_bijective {tau : ℤ → ℤ}
    (hBij : Function.Bijective tau) :
    Function.Bijective (rawAffineReflection tau) := by
  constructor
  · intro x y hxy
    unfold rawAffineReflection at hxy
    have h : tau (-x) = tau (-y) := by omega
    have := hBij.1 h
    omega
  · intro z
    obtain ⟨n, hn⟩ := hBij.2 (-z)
    refine ⟨-n, ?_⟩
    unfold rawAffineReflection
    rw [neg_neg, hn]
    omega

/-- Reflection in the origin preserves a positive affine period. -/
theorem IsKAffine.affineReflection
    {k : ℕ} {tau : ℤ → ℤ} (hAffine : IsKAffine k tau) :
    IsKAffine k (rawAffineReflection tau) := by
  intro n
  have h := hAffine.iterate_int (-n) (-1)
  unfold Bananas.rawAffineReflection
  have hArg : -(n + (k : ℤ)) = -n + (-1 : ℤ) * k := by ring
  rw [hArg, h]
  ring

/-- Reverse a pair and negate both entries.  This carries inversions of a
reflected permutation to inversions of the original permutation. -/
def reflectionInversionPair (p : ℤ × ℤ) : ℤ × ℤ :=
  (-p.2, -p.1)

theorem reflectionInversionPair_involutive :
    Function.Involutive reflectionInversionPair := by
  rintro ⟨x, y⟩
  simp [reflectionInversionPair]

theorem reflectionInversionPair_shiftPair
    (k : ℕ) (q : ℤ) (p : ℤ × ℤ) :
    reflectionInversionPair (shiftPair k q p) =
      shiftPair k (-q) (reflectionInversionPair p) := by
  rcases p with ⟨x, y⟩
  apply Prod.ext <;> simp only [reflectionInversionPair, shiftPair] <;> ring

/-- Normalize the original inversion corresponding to an inversion of the
reflected permutation.  The same map, with source and target exchanged, is
its inverse. -/
def normalizedReflectionInversion (k : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  normalizeFirstPair k (reflectionInversionPair p)

theorem normalizedReflectionInversion_mem
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hAffine : IsKAffine k tau) {p : ℤ × ℤ}
    (hp : p ∈ kInversions k (rawAffineReflection tau)) :
    normalizedReflectionInversion k p ∈ kInversions k tau := by
  apply inversion_normalize_first_coordinate hk hAffine
  rcases p with ⟨a, b⟩
  change a < b ∧ -tau (-a) > -tau (-b) ∧ _ at hp
  change -b < -a ∧ tau (-b) > tau (-a)
  omega

theorem normalizedReflectionInversion_mem_reflection
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hAffine : IsKAffine k tau) {p : ℤ × ℤ}
    (hp : p ∈ kInversions k tau) :
    normalizedReflectionInversion k p ∈
      kInversions k (rawAffineReflection tau) := by
  apply inversion_normalize_first_coordinate hk hAffine.affineReflection
  rcases p with ⟨a, b⟩
  change a < b ∧ tau a > tau b ∧ _ at hp
  change -b < -a ∧ -tau (-(-b)) > -tau (-(-a))
  simp only [neg_neg]
  omega

theorem normalizedReflectionInversion_involutive_on_kInversions
    {k : ℕ} (hk : 0 < k) {p : ℤ × ℤ}
    (hp : 0 ≤ p.1 ∧ p.1 < (k : ℤ)) :
    normalizedReflectionInversion k (normalizedReflectionInversion k p) = p := by
  let q : ℤ := -((reflectionInversionPair p).1 / k)
  have hNorm : normalizedReflectionInversion k p =
      shiftPair k q (reflectionInversionPair p) := by
    exact normalizeFirstPair_eq_shiftPair k (reflectionInversionPair p)
  rw [normalizedReflectionInversion, hNorm,
    reflectionInversionPair_shiftPair,
    reflectionInversionPair_involutive p]
  exact normalizeFirstPair_shiftPair_of_fundamental hk p hp.1 hp.2 (-q)

/-- Reflection in the origin preserves the number of affine-period inversion
classes. -/
theorem kInversionCount_affineReflection
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hAffine : IsKAffine k tau) :
    kInversionCount k (rawAffineReflection tau) = kInversionCount k tau := by
  unfold kInversionCount
  apply Set.ncard_congr (fun p _ => normalizedReflectionInversion k p)
  · exact fun _ hp => normalizedReflectionInversion_mem hk hAffine hp
  · intro p p' hp hp' heq
    have := congrArg (normalizedReflectionInversion k) heq
    rw [normalizedReflectionInversion_involutive_on_kInversions hk hp.2.2,
      normalizedReflectionInversion_involutive_on_kInversions hk hp'.2.2] at this
    exact this
  · intro p hp
    refine ⟨normalizedReflectionInversion k p,
      normalizedReflectionInversion_mem_reflection hk hAffine hp, ?_⟩
    exact normalizedReflectionInversion_involutive_on_kInversions hk hp.2.2

/-- Swapping a raw transmission permutation preserves its affine inversion
count. -/
theorem kInversionCount_swapTransmissionPermutation
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hBij : Function.Bijective tau) (hAffine : IsKAffine k tau) :
    kInversionCount k (swapTransmissionPermutation tau) =
      kInversionCount k tau := by
  unfold swapTransmissionPermutation
  rw [kInversionCount_affineReflection hk (hAffine.rawInverse hBij),
    kInversionCount_rawInverse hk hBij hAffine]

theorem rawInverse_bijective {tau : ℤ → ℤ}
    (hBij : Function.Bijective tau) :
    Function.Bijective (rawInverse tau) := by
  have hLeft : Function.LeftInverse (rawInverse tau) tau :=
    fun n => rawInverse_apply_apply tau hBij n
  have hRight : Function.RightInverse (rawInverse tau) tau :=
    fun n => apply_rawInverse_apply tau hBij n
  exact ⟨hRight.injective, hLeft.surjective⟩

theorem swapTransmissionPermutation_bijective {tau : ℤ → ℤ}
    (hBij : Function.Bijective tau) :
    Function.Bijective (swapTransmissionPermutation tau) := by
  exact affineReflection_bijective (rawInverse_bijective hBij)

theorem IsKAffine.swapTransmissionPermutation
    {k : ℕ} {tau : ℤ → ℤ} (hAffine : IsKAffine k tau)
    (hBij : Function.Bijective tau) :
    IsKAffine k (swapTransmissionPermutation tau) := by
  exact (hAffine.rawInverse hBij).affineReflection

/-- The marked second rank difference is symmetric in the ordered marks. -/
theorem rankDelta_mark_swap
    (G : CFGraph) (u v : G.V) (D : CFDiv G) :
    rankDelta (mark G v u) D = rankDelta (mark G u v) D := by
  have hSub : D - one_chip v - one_chip u =
      D - one_chip u - one_chip v := by
    abel
  unfold rankDelta mark
  rw [hSub]
  ring

/-- The reflected inverse is exactly the raw transmission permutation after
the order of the two marked vertices is exchanged. -/
theorem IsTransmissionPermutation.swap_marks
    {G : CFGraph} (u v : G.V) (D : CFDiv G) {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation (mark G u v) D tau) :
    IsTransmissionPermutation (mark G v u) D
      (swapTransmissionPermutation tau) := by
  refine ⟨swapTransmissionPermutation_bijective hTau.1, ?_⟩
  intro a b
  change (if swapTransmissionPermutation tau b = a then (1 : ℤ) else 0) =
    rankDelta (mark G v u) (D + a • one_chip v - b • one_chip u)
  have hCondition : swapTransmissionPermutation tau b = a ↔
      tau (-a) = -b := by
    unfold swapTransmissionPermutation rawAffineReflection
    constructor
    · intro h
      have hInv : rawInverse tau (-b) = -a := by omega
      calc
        tau (-a) = tau (rawInverse tau (-b)) := by rw [hInv]
        _ = -b := apply_rawInverse_apply tau hTau.1 (-b)
    · intro h
      have hInv : rawInverse tau (-b) = -a := by
        rw [← h]
        exact rawInverse_apply_apply tau hTau.1 (-a)
      omega
  have hIf : (if swapTransmissionPermutation tau b = a then (1 : ℤ) else 0) =
      (if tau (-a) = -b then 1 else 0) := by
    simp only [hCondition]
  rw [hIf, hTau.2 (-b) (-a), rankDelta_mark_swap G u v]
  congr 1
  rw [neg_zsmul, neg_zsmul]
  dsimp [mark]
  funext z
  change D z + -(b * one_chip u z) - -(a * one_chip v z) =
    D z + a * one_chip v z - b * one_chip u z
  ring

/-- A torsion period is unchanged when the two marked vertices are exchanged. -/
theorem torsionWitness_swap
    {G : CFGraph} (u v : G.V) {k : ℕ}
    (h : TorsionWitness (mark G u v) k) :
    TorsionWitness (mark G v u) k := by
  rcases h with ⟨hk, hPrincipal⟩
  refine ⟨hk, ?_⟩
  unfold linear_equiv at hPrincipal ⊢
  change (0 : CFDiv G) -
    (k : ℤ) • (one_chip u - one_chip v) ∈ principal_divisors G at hPrincipal
  change (0 : CFDiv G) -
    (k : ℤ) • (one_chip v - one_chip u) ∈ principal_divisors G
  have hEq : (0 : CFDiv G) -
      (k : ℤ) • (one_chip v - one_chip u) =
      -((0 : CFDiv G) - (k : ℤ) • (one_chip u - one_chip v)) := by
    ext z
    simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply]
    ring
  rw [hEq]
  exact AddSubgroup.neg_mem (principal_divisors G) hPrincipal

theorem torsionWitness_swap_iff
    {G : CFGraph} (u v : G.V) {k : ℕ} :
    TorsionWitness (mark G v u) k ↔
      TorsionWitness (mark G u v) k := by
  exact ⟨torsionWitness_swap v u, torsionWitness_swap u v⟩
/-- Submodularity of every divisor is unchanged by ordering the marks. -/
theorem allSubmodular_swap_iff
    {G : CFGraph} (u v : G.V) :
    AllSubmodular (mark G v u) ↔ AllSubmodular (mark G u v) := by
  rw [allSubmodular_iff_rankDelta_nonneg,
    allSubmodular_iff_rankDelta_nonneg]
  constructor <;> intro h D
  · rw [rankDelta_mark_swap G v u D]
    exact h D
  · rw [rankDelta_mark_swap G u v D]
    exact h D

/-- `k`-general transmission is independent of the ordering of the two marked
vertices. -/
theorem KGeneralTransmission.swap_marks
    {G : CFGraph} (u v : G.V) {k : ℕ}
    (hK : KGeneralTransmission (mark G u v) k) :
    KGeneralTransmission (mark G v u) k := by
  apply KGeneralTransmission_iff_without_finiteness.mpr
  refine ⟨torsionWitness_swap u v hK.1,
    (allSubmodular_swap_iff u v).2 hK.2.1, ?_⟩
  intro D
  obtain ⟨tau, hTau, hAffine, hCount⟩ := hK.exists_affine_transmission D
  refine ⟨swapTransmissionPermutation tau, hTau.swap_marks u v D,
    hAffine.swapTransmissionPermutation hTau.1, ?_⟩
  rw [kInversionCount_swapTransmissionPermutation hK.1.1 hTau.1 hAffine]
  exact hCount

theorem kGeneralTransmission_swap_iff
    {G : CFGraph} (u v : G.V) {k : ℕ} :
    KGeneralTransmission (mark G v u) k ↔
      KGeneralTransmission (mark G u v) k := by
  exact ⟨KGeneralTransmission.swap_marks v u,
    KGeneralTransmission.swap_marks u v⟩

end Bananas
