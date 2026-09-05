/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Phase.PowerMap

/-!
# The phase-to-root-count identity

Assuming the all-character Walsh formula `WalshCharacterFormula`, we prove

`Z(ρ) = Q²/8 * (∑_{u,v ∈ U} R_{u,v}(A,B) - c²)`,

for `A, B ∈ K^*` with `A³ + B³ = 1` and `A³ ≠ 1`, where `ρ = A³`, `σ = B³`.
-/

open Finset

namespace KasamiCyclicAdditive.Phase

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-! ### Auxiliary facts about `μ₃` and Gauss sums

The generic additive-character and Gauss-sum identities used here are shared
from `Phase/CharacterSums.lean`; this file contains the cube-support and
root-count-specific argument.
-/

omit [CharP K 2] in
/-- Summing over the cube roots of unity in `Kˣ` is the same as summing over
`μ₃(K)` inside `K`. -/
lemma sum_mu3Units {M : Type*} [AddCommMonoid M] (f : K → M) :
    ∑ u ∈ Finset.univ.filter (fun u : Kˣ => u ^ 3 = 1), f ((u : K))
      = ∑ u ∈ cubeRootsOne K, f u := by
  refine Finset.sum_nbij' (fun u : Kˣ => (u : K))
    (fun u : K => if h : u = 0 then 1 else Units.mk0 u h) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [mem_cubeRootsOne, ← Units.val_pow_eq_pow_val, hu, Units.val_one]
  · intro u hu
    rw [mem_cubeRootsOne] at hu
    have h0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
    simp only [dite_eq_right h0, Finset.mem_filter, Finset.mem_univ, true_and]
    ext
    simpa using hu
  · intro u _
    have h0 : (u : K) ≠ 0 := u.ne_zero
    simp [h0]
  · intro u hu
    rw [mem_cubeRootsOne] at hu
    have h0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
    simp [h0]
  · intro u _; rfl

omit [CharP K 2] in
/-- The cube roots of unity in `Kˣ` number `mu3Card K`. -/
lemma card_mu3Units : (Finset.univ.filter (fun u : Kˣ => u ^ 3 = 1)).card = mu3Card K := by
  have h := sum_mu3Units (K := K) (M := ℕ) (fun _ => 1)
  simpa [mu3Card] using h

omit [CharP K 2] in
/-- Every cube in `Kˣ` has exactly `c` cube roots. -/
lemma card_cubeRoots_units (A : Kˣ) : #{b : Kˣ | b ^ 3 = A ^ 3} = mu3Card K := by
  rw [← card_mu3Units]
  refine Finset.card_nbij' (fun b => b * A⁻¹) (fun u => u * A) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [mul_pow, hb, inv_pow, mul_inv_cancel]
  · intro u hu
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [mul_pow, hu, one_mul]
  · intro b _; simp
  · intro u _; simp

/-! ### Step 1: the closed form of `S` -/

omit [DecidableEq K] in
/-- The Gauss-sum ratio of the Walsh formula, rewritten using `G(θ) G(θ⁻¹) = Q`. -/
lemma ratio_eq {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive) (m : ℕ) (χ : MulChar K ℂ) :
    gaussSum (χ ^ (3 * m)) ψ / gaussSum (χ ^ 3) ψ
      = gaussSum ((χ ^ 3) ^ m) ψ * gaussSum ((χ ^ 3)⁻¹) ψ / (Fintype.card K : ℂ)
        + (if χ ^ 3 = 1 then 1 - 1 / (Fintype.card K : ℂ) else 0) := by
  classical
  have hQ : (Fintype.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [pow_mul]
  by_cases hθ : χ ^ 3 = 1
  · rw [hθ, ite_eq_left rfl, one_pow, inv_one, gaussSum_principal hψ]
    field_simp
    ring
  · rw [ite_eq_right hθ, add_zero]
    have hmi := KasamiCyclicAdditive.gaussSum_mul_inv hψ hθ
    have hne : gaussSum (χ ^ 3) ψ ≠ 0 := by
      intro h; rw [h, zero_mul] at hmi; exact hQ hmi.symm
    field_simp
    linear_combination (-gaussSum ((χ ^ 3) ^ m) ψ) * hmi

omit [CharP K 2] in
/-- Orthogonality turns the character sum into a count of solutions of `y³ = a x^{3m}`. -/
lemma sum_gaussSum_prod {ψ : AddChar K ℂ} {m : ℕ} (a : Kˣ) :
    ∑ χ : MulChar K ℂ, gaussSum ((χ ^ 3) ^ m) ψ * gaussSum ((χ ^ 3)⁻¹) ψ * χ ((a : K))
      = (Fintype.card Kˣ : ℂ) * ∑ x : Kˣ,
          ∑ y ∈ Finset.univ.filter (fun y : Kˣ => y ^ 3 = a * x ^ (3 * m)),
            ψ ((x : K) + (y : K)) := by
  have hg : ∀ (θ : MulChar K ℂ), gaussSum θ ψ = ∑ b : Kˣ, θ ((b : K)) * ψ ((b : K)) := by
    intro θ
    rw [gaussSum]
    exact (sum_units_eq_sum (fun b : K => θ b * ψ b) (by simp [MulChar.map_zero])).symm
  have hchi : ∀ (χ : MulChar K ℂ) (x y : Kˣ),
      ((χ ^ 3) ^ m) ((x : K)) * ((χ ^ 3)⁻¹) ((y : K)) * χ ((a : K))
        = χ (((x ^ (3 * m) * (y⁻¹) ^ 3 * a : Kˣ) : K)) := by
    intro χ x y
    rw [MulChar.inv_apply', ← Units.val_inv_eq_inv_val]
    simp only [MulChar.pow_apply_coe, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
      ← pow_mul]
  have hiff : ∀ x y : Kˣ, (x ^ (3 * m) * (y⁻¹) ^ 3 * a = 1) ↔ (y ^ 3 = a * x ^ (3 * m)) := by
    intro x y
    rw [inv_pow, mul_right_comm, mul_comm (x ^ (3 * m)) a, mul_inv_eq_one, eq_comm]
  calc ∑ χ : MulChar K ℂ, gaussSum ((χ ^ 3) ^ m) ψ * gaussSum ((χ ^ 3)⁻¹) ψ * χ ((a : K))
      = ∑ χ : MulChar K ℂ, ∑ x : Kˣ, ∑ y : Kˣ,
          χ (((x ^ (3 * m) * (y⁻¹) ^ 3 * a : Kˣ) : K)) * ψ ((x : K) + (y : K)) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [hg, hg, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [ψ.map_add_eq_mul, ← hchi]
        ring
    _ = ∑ x : Kˣ, ∑ y : Kˣ,
          (if (x ^ (3 * m) * (y⁻¹) ^ 3 * a) = 1 then (Fintype.card Kˣ : ℂ) else 0)
            * ψ ((x : K) + (y : K)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, sum_char_apply]
    _ = (Fintype.card Kˣ : ℂ) * ∑ x : Kˣ,
          ∑ y ∈ Finset.univ.filter (fun y : Kˣ => y ^ 3 = a * x ^ (3 * m)),
            ψ ((x : K) + (y : K)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h : y ^ 3 = a * x ^ (3 * m)
        · rw [ite_eq_left ((hiff x y).mpr h), ite_eq_left h]
        · rw [ite_eq_right (fun hc => h ((hiff x y).mp hc)), ite_eq_right h, zero_mul, mul_zero]

/-- The closed form of the Walsh phase obtained from the supplied
all-character Walsh formula `hS`. -/
lemma walshCoefficient_closed_form {ψ : AddChar K ℂ} {m e : ℕ} {S : K → ℂ} (hψ : ψ.IsPrimitive)
    (he : e = 3 * m) (hS : WalshCharacterFormula ψ e S) (a : Kˣ) :
    2 * S (a : K) = (#{b : Kˣ | b ^ 3 = a} : ℂ)
      + ∑ x : Kˣ, ∑ y ∈ Finset.univ.filter (fun y : Kˣ => y ^ 3 = a * x ^ (3 * m)),
          ψ ((x : K) + (y : K)) := by
  have hQ : (Fintype.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hN : (Fintype.card Kˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNQ : (Fintype.card Kˣ : ℂ) = (Fintype.card K : ℂ) - 1 := by
    rw [Fintype.card_units]
    have h1 : 1 ≤ Fintype.card K := Fintype.card_pos
    push_cast [Nat.cast_sub h1]
    ring
  rw [hS a, he, Finset.sum_congr rfl (fun χ _ => by rw [ratio_eq hψ m χ])]
  have hI : ∑ χ : MulChar K ℂ,
        (if χ ^ 3 = 1 then (1 - 1 / (Fintype.card K : ℂ)) else 0) * χ ((a : K))
      = (1 - 1 / (Fintype.card K : ℂ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : MulChar K ℂ => χ ^ 3 = 1), χ ((a : K)) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl fun χ _ => by split_ifs <;> ring
  have hP : ∑ χ : MulChar K ℂ,
        (gaussSum ((χ ^ 3) ^ m) ψ * gaussSum ((χ ^ 3)⁻¹) ψ / (Fintype.card K : ℂ)) * χ ((a : K))
      = (1 / (Fintype.card K : ℂ)) *
        ∑ χ : MulChar K ℂ, gaussSum ((χ ^ 3) ^ m) ψ * gaussSum ((χ ^ 3)⁻¹) ψ * χ ((a : K)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ _ => by ring
  rw [Finset.sum_congr rfl (fun χ _ => add_mul _ _ _), Finset.sum_add_distrib, hI, hP,
    sum_gaussSum_prod, sum_cubic_char_apply, hNQ]
  have hQ1 : (Fintype.card K : ℂ) - 1 ≠ 0 := by rw [← hNQ]; exact hN
  field_simp
  ring

/-- For `A ∈ Kˣ`, twice the phase at the cube `A³` is the additive Fourier transform
of `Φ` at `A`. -/
lemma two_S_cube {ψ : AddChar K ℂ} {m D e : ℕ} {S : K → ℂ} (hψ : ψ.IsPrimitive)
    (hm : m ≠ 0) (hD : D ≠ 0) (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (he : e = 3 * m)
    (hS : WalshCharacterFormula ψ e S) (A : Kˣ) :
    2 * S ((A : K) ^ 3) = phiHat ψ D (A : K) := by
  have key := walshCoefficient_closed_form hψ he hS (A ^ 3)
  rw [Units.val_pow_eq_pow_val] at key
  -- reindex the inner solution sets by `μ₃`
  have hinner : ∀ x : Kˣ,
      ∑ y ∈ Finset.univ.filter (fun y : Kˣ => y ^ 3 = A ^ 3 * x ^ (3 * m)),
          ψ ((x : K) + (y : K))
        = ∑ u ∈ cubeRootsOne K, ψ ((x : K) + u * (A : K) * (x : K) ^ m) := by
    intro x
    rw [← sum_mu3Units (fun u : K => ψ ((x : K) + u * (A : K) * (x : K) ^ m))]
    refine (Finset.sum_nbij' (fun u : Kˣ => u * (A * x ^ m)) (fun y : Kˣ => y * (A * x ^ m)⁻¹)
      ?_ ?_ ?_ ?_ ?_).symm
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rw [mul_pow, hu, one_mul, mul_pow, ← pow_mul, mul_comm m 3]
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [mul_pow, hy, inv_pow, mul_pow, ← pow_mul, mul_comm m 3, mul_inv_cancel]
    · intro u _; group
    · intro y _; group
    · intro u _
      congr 2
      push_cast
      ring
  rw [key, card_cubeRoots_units, Finset.sum_congr rfl (fun x _ => hinner x), Finset.sum_comm]
  -- restore the point `x = 0`
  have hzeroterm : ∀ u ∈ cubeRootsOne K,
      (1 : ℂ) + ∑ x : Kˣ, ψ ((x : K) + u * (A : K) * (x : K) ^ m)
        = ∑ x : K, ψ (x + u * (A : K) * x ^ m) := by
    intro u _
    have h := sum_units_add (fun x : K => ψ (x + u * (A : K) * x ^ m))
    simpa [zero_pow hm] using h
  have step1 : ∑ u ∈ cubeRootsOne K, ∑ x : K, ψ (x + u * (A : K) * x ^ m)
      = (mu3Card K : ℂ)
        + ∑ u ∈ cubeRootsOne K, ∑ x : Kˣ, ψ ((x : K) + u * (A : K) * (x : K) ^ m) := by
    rw [← Finset.sum_congr rfl hzeroterm, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one, mu3Card]
  rw [← step1]
  -- substitute `x = v t^D` with `v = (u⁻¹)^D`
  have hsubst : ∀ u ∈ cubeRootsOne K,
      ∑ x : K, ψ (x + u * (A : K) * x ^ m)
        = ∑ t : K, ψ ((u⁻¹) ^ D * t ^ D + (A : K) * t) := by
    intro u hu
    have hu0 : u ≠ 0 := cubeRootsOne_ne_zero hu
    have hv0 : (u⁻¹) ^ D ≠ 0 := pow_ne_zero _ (inv_ne_zero hu0)
    have hvm : ((u⁻¹) ^ D) ^ m = u⁻¹ := powD_powm hm hD hmD _
    have hbij : Function.Bijective (fun t : K => (u⁻¹) ^ D * t ^ D) :=
      (mulLeft_bijective₀ _ hv0).comp (powD_bijective hm hD hmD)
    refine (Fintype.sum_bijective _ hbij _ _ ?_).symm
    intro t
    congr 1
    have h1 : ((u⁻¹) ^ D * t ^ D) ^ m = u⁻¹ * t := by
      rw [mul_pow, hvm, powD_powm hm hD hmD]
    rw [h1]
    field_simp
  rw [Finset.sum_congr rfl hsubst]
  -- reindex `u ↦ (u⁻¹)^D`
  have hreindex : ∑ u ∈ cubeRootsOne K, ∑ t : K, ψ ((u⁻¹) ^ D * t ^ D + (A : K) * t)
      = ∑ v ∈ cubeRootsOne K, ∑ t : K, ψ (v * t ^ D + (A : K) * t) := by
    refine Finset.sum_nbij' (fun u : K => (u⁻¹) ^ D) (fun v : K => (v ^ m)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      rw [mem_cubeRootsOne] at hu
      simp only [mem_cubeRootsOne]
      rw [← pow_mul, mul_comm D 3, pow_mul, inv_pow, hu, inv_one, one_pow]
    · intro v hv
      rw [mem_cubeRootsOne] at hv
      simp only [mem_cubeRootsOne]
      rw [inv_pow, ← pow_mul, mul_comm m 3, pow_mul, hv, one_pow, inv_one]
    · intro u _
      rw [powD_powm hm hD hmD, inv_inv]
    · intro v _
      rw [inv_inv, powm_powD hm hD hmD]
    · intro u _; rfl
  rw [hreindex, phiHat]
  simp only [phi, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun t _ =>
    ψ.map_add_eq_mul _ _

/-- If `c = 3`, the phase vanishes at non-cubes. -/
lemma S_eq_zero_of_not_cube {ψ : AddChar K ℂ} {m e : ℕ} {S : K → ℂ} (hψ : ψ.IsPrimitive)
    (he : e = 3 * m) (hS : WalshCharacterFormula ψ e S) (a : Kˣ) (ha : ¬ ∃ b : Kˣ, b ^ 3 = a) :
    S ((a : K)) = 0 := by
  have key := walshCoefficient_closed_form hψ he hS a
  have h1 : #{b : Kˣ | b ^ 3 = a} = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b _ hb
    exact ha ⟨b, hb⟩
  have h2 : ∀ x : Kˣ, Finset.univ.filter (fun y : Kˣ => y ^ 3 = a * x ^ (3 * m)) = ∅ := by
    intro x
    rw [Finset.filter_eq_empty_iff]
    intro y _ hy
    refine ha ⟨y * (x ^ m)⁻¹, ?_⟩
    rw [mul_pow, hy, inv_pow, ← pow_mul, mul_comm m 3, mul_inv_cancel_right]
  simp only [h1, h2, Nat.cast_zero, Finset.sum_empty, Finset.sum_const_zero, add_zero] at key
  linear_combination key / 2

/-- Reindexing `Z` over `G/U`, combined with the closed form of `S`. -/
lemma eight_phaseTripleSum {ψ : AddChar K ℂ} {m D e : ℕ} {S : K → ℂ} {A B : K}
    (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (hD : D ≠ 0)
    (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (he : e = 3 * m) (hS : WalshCharacterFormula ψ e S)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    8 * phaseTripleSum S (A ^ 3) (B ^ 3) * (mu3Card K : ℂ)
      = ∑ z : Kˣ, phiHat ψ D (z : K) * phiHat ψ D (A * z) * phiHat ψ D (B * z) := by
  set f : Kˣ → ℂ := fun lam =>
    8 * (S ((lam : K)) * S (A ^ 3 * (lam : K)) * S (B ^ 3 * (lam : K))) with hf
  have hZf : 8 * phaseTripleSum S (A ^ 3) (B ^ 3) = ∑ lam : Kˣ, f lam := by
    rw [phaseTripleSum, Finset.mul_sum]
  -- the value of `f` at a cube is the product of three Fourier transforms
  have hcube : ∀ z : Kˣ, f (z ^ 3)
      = phiHat ψ D (z : K) * phiHat ψ D (A * z) * phiHat ψ D (B * z) := by
    intro z
    have hz := two_S_cube hψ hm hD hmD he hS z
    have hAz := two_S_cube hψ hm hD hmD he hS (Units.mk0 A hA * z)
    have hBz := two_S_cube hψ hm hD hmD he hS (Units.mk0 B hB * z)
    simp only [Units.val_mul, Units.val_mk0] at hAz hBz
    rw [hf]
    simp only [Units.val_pow_eq_pow_val]
    rw [show A ^ 3 * (z : K) ^ 3 = (A * (z : K)) ^ 3 by ring,
      show B ^ 3 * (z : K) ^ 3 = (B * (z : K)) ^ 3 by ring]
    rw [← hz, ← hAz, ← hBz]
    ring
  -- fibrewise counting of the cubing map
  have hcount : ∀ lam : Kˣ, (#{z : Kˣ | z ^ 3 = lam} : ℂ) * f lam = (mu3Card K : ℂ) * f lam := by
    intro lam
    by_cases h : ∃ b : Kˣ, b ^ 3 = lam
    · obtain ⟨b, hb⟩ := h
      rw [← hb, card_cubeRoots_units]
    · have hzero : f lam = 0 := by
        rw [hf]
        simp only
        rw [S_eq_zero_of_not_cube hψ he hS lam h]
        ring
      rw [hzero]
      ring
  have hfiber : ∑ z : Kˣ, f (z ^ 3) = ∑ lam : Kˣ, (#{z : Kˣ | z ^ 3 = lam} : ℂ) * f lam := by
    have hstep : ∀ lam : Kˣ, (#{z : Kˣ | z ^ 3 = lam} : ℂ) * f lam
        = ∑ z : Kˣ, (if z ^ 3 = lam then f lam else 0) := by
      intro lam
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun lam _ => hstep lam), Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (z ^ 3) f]
    simp
  rw [hZf, mul_comm, Finset.mul_sum,
    Finset.sum_congr rfl (fun lam (_ : lam ∈ Finset.univ) => (hcount lam).symm), ← hfiber]
  exact Finset.sum_congr rfl fun z _ => hcube z

/-! ### Fourier analysis of `Φ` -/

omit [CharP K 2] in
/-- `Φ` has vanishing total mass, i.e. `Φ̂(0) = 0`. -/
lemma sum_phi_eq_zero {ψ : AddChar K ℂ} {m D : ℕ} (hψ : ψ.IsPrimitive)
    (hm : m ≠ 0) (hD : D ≠ 0) (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) :
    ∑ t : K, phi ψ D t = 0 := by
  simp only [phi]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [sum_psi_mul_powD hψ hm hD hmD u, ite_eq_right (cubeRootsOne_ne_zero hu)]

omit [CharP K 2] in
/-- The transform `phiHat` vanishes at `0`. -/
lemma phiHat_zero {ψ : AddChar K ℂ} {m D : ℕ} (hψ : ψ.IsPrimitive)
    (hm : m ≠ 0) (hD : D ≠ 0) (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) :
    phiHat ψ D 0 = 0 := by
  simp only [phiHat, zero_mul, AddChar.map_zero_eq_one, mul_one]
  exact sum_phi_eq_zero hψ hm hD hmD

omit [Field K] [DecidableEq K] [CharP K 2] in
/-- A product of three sums over `K` expands to a triple sum. -/
private lemma triple_sum_mul {f g h : K → ℂ} :
    (∑ x, f x) * (∑ y, g y) * (∑ w, h w) = ∑ x, ∑ y, ∑ w, f x * g y * h w := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul_sum]

/-- The Parseval-type identity replacing the spectral computation of Steps 4–7. -/
lemma fourier_triple {ψ : AddChar K ℂ} {D : ℕ} (hψ : ψ.IsPrimitive) (A B : K) :
    ∑ z : K, phiHat ψ D z * phiHat ψ D (A * z) * phiHat ψ D (B * z)
      = (Fintype.card K : ℂ) * ∑ x : K, ∑ y : K,
          phi ψ D x * phi ψ D y * phi ψ D (A * x + B * y) := by
  have expand : ∀ z : K, phiHat ψ D z * phiHat ψ D (A * z) * phiHat ψ D (B * z)
      = ∑ x : K, ∑ y : K, ∑ w : K,
        phi ψ D x * phi ψ D y * phi ψ D w * ψ (z * (x + A * y + B * w)) := by
    intro z
    simp only [phiHat]
    rw [triple_sum_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun w _ => ?_
    rw [show z * (x + A * y + B * w) = z * x + (A * z * y + B * z * w) by ring,
      ψ.map_add_eq_mul, ψ.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun z _ => expand z, Finset.sum_comm]
  have step : ∀ x : K, ∑ z : K, ∑ y : K, ∑ w : K,
        phi ψ D x * phi ψ D y * phi ψ D w * ψ (z * (x + A * y + B * w))
      = ∑ y : K, ∑ w : K, phi ψ D x * phi ψ D y * phi ψ D w *
          (if x + A * y + B * w = 0 then (Fintype.card K : ℂ) else 0) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [AddChar.sum_mulShift _ hψ]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcond : ∀ x : K, (x + A * y + B * w = 0) = (x = A * y + B * w) := by
    intro x; simp [add_assoc, CharTwo.add_eq_zero]
  simp only [hcond, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-! ### Step 3: symmetrization -/

omit [Field K] [DecidableEq K] [CharP K 2] in
/-- The same expansion over an arbitrary finset. -/
private lemma triple_sum_mul' {ι : Type*} (s : Finset ι) (f g h : ι → ℂ) :
    (∑ x ∈ s, f x) * (∑ y ∈ s, g y) * (∑ w ∈ s, h w)
      = ∑ x ∈ s, ∑ y ∈ s, ∑ w ∈ s, f x * g y * h w := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_mul_sum _ _ _ _

omit [Field K] [DecidableEq K] [CharP K 2] in
/-- Moving the two sums over `K` inside the three finset sums. -/
private lemma sum_reorder5 {ι : Type*} (s : Finset ι) (F : K → K → ι → ι → ι → ℂ) :
    ∑ x : K, ∑ y : K, ∑ a ∈ s, ∑ b ∈ s, ∑ g ∈ s, F x y a b g
      = ∑ a ∈ s, ∑ b ∈ s, ∑ g ∈ s, ∑ x : K, ∑ y : K, F x y a b g := by
  calc ∑ x : K, ∑ y : K, ∑ a ∈ s, ∑ b ∈ s, ∑ g ∈ s, F x y a b g
      = ∑ x : K, ∑ a ∈ s, ∑ b ∈ s, ∑ g ∈ s, ∑ y : K, F x y a b g := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ g ∈ s, ∑ x : K, ∑ y : K, F x y a b g := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]

omit [CharP K 2] in
/-- Symmetrizing the Weil sum over the cube roots of unity. -/
lemma symmetrization {ψ : AddChar K ℂ} {m D : ℕ} (hm : m ≠ 0) (hD : D ≠ 0)
    (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (A B : K) :
    ∑ x : K, ∑ y : K, phi ψ D x * phi ψ D y * phi ψ D (A * x + B * y)
      = (mu3Card K : ℂ) * ∑ u ∈ cubeRootsOne K, ∑ v ∈ cubeRootsOne K, weilSum ψ D A B u v := by
  set U := cubeRootsOne K with hU
  set V : K → K → K → ℂ := fun a b g =>
    ∑ x : K, ∑ y : K, ψ (a * x ^ D + b * y ^ D + g * (A * x + B * y) ^ D) with hV
  -- expand the three copies of `Φ`
  have stepA : ∑ x : K, ∑ y : K, phi ψ D x * phi ψ D y * phi ψ D (A * x + B * y)
      = ∑ a ∈ U, ∑ b ∈ U, ∑ g ∈ U, V a b g := by
    have h1 : ∀ x y : K, phi ψ D x * phi ψ D y * phi ψ D (A * x + B * y)
        = ∑ a ∈ U, ∑ b ∈ U, ∑ g ∈ U, ψ (a * x ^ D + b * y ^ D + g * (A * x + B * y) ^ D) := by
      intro x y
      simp only [phi, ← hU]
      rw [triple_sum_mul']
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun g _ => ?_
      rw [ψ.map_add_eq_mul, ψ.map_add_eq_mul]
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => h1 x y, sum_reorder5]
  -- normalize the middle character to `1` by scaling `(x,y)` by `τ` with `τ^D = b⁻¹`
  have stepB : ∀ a ∈ U, ∀ b ∈ U, ∀ g ∈ U, V a b g = V (a * b⁻¹) 1 (g * b⁻¹) := by
    intro a _ b hb g _
    have hb0 : b ≠ 0 := cubeRootsOne_ne_zero hb
    set τ : K := (b⁻¹) ^ m with hτ
    have hτ0 : τ ≠ 0 := pow_ne_zero _ (inv_ne_zero hb0)
    have hτD : τ ^ D = b⁻¹ := by rw [hτ, ← pow_mul]; exact pow_mul_eq_self hm hD hmD _
    have hsub : ∀ (H : K → K → ℂ), ∑ x : K, ∑ y : K, H (τ * x) (τ * y)
        = ∑ x : K, ∑ y : K, H x y := by
      intro H
      have inner : ∀ x : K, ∑ y : K, H x (τ * y) = ∑ y : K, H x y := fun x =>
        Fintype.sum_bijective _ (mulLeft_bijective₀ τ hτ0) _ _ (fun y => rfl)
      calc ∑ x : K, ∑ y : K, H (τ * x) (τ * y) = ∑ x : K, ∑ y : K, H (τ * x) y :=
            Finset.sum_congr rfl fun x _ => inner (τ * x)
        _ = ∑ x : K, ∑ y : K, H x y :=
            Fintype.sum_bijective _ (mulLeft_bijective₀ τ hτ0) _ _ (fun x => rfl)
    simp only [hV]
    rw [← hsub (fun x y => ψ (a * x ^ D + b * y ^ D + g * (A * x + B * y) ^ D))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    have e1 : (τ * x) ^ D = b⁻¹ * x ^ D := by rw [mul_pow, hτD]
    have e2 : (τ * y) ^ D = b⁻¹ * y ^ D := by rw [mul_pow, hτD]
    have e3 : A * (τ * x) + B * (τ * y) = τ * (A * x + B * y) := by ring
    rw [e1, e2, e3, mul_pow, hτD]
    field_simp
  -- reindex the two outer characters
  have stepC : ∀ b ∈ U, ∑ a ∈ U, ∑ g ∈ U, V (a * b⁻¹) 1 (g * b⁻¹)
      = ∑ u ∈ U, ∑ v ∈ U, V u 1 v := by
    intro b hb
    have hbinv : b⁻¹ ∈ U := inv_mem_cubeRootsOne hb
    have hb0 : b ≠ 0 := cubeRootsOne_ne_zero hb
    refine Finset.sum_nbij' (fun a => a * b⁻¹) (fun u => u * b) ?_ ?_ ?_ ?_ ?_
    · exact fun a ha => mul_mem_cubeRootsOne ha hbinv
    · exact fun u hu => mul_mem_cubeRootsOne hu hb
    · intro a _; field_simp
    · intro u _; field_simp
    · intro a _
      refine Finset.sum_nbij' (fun g => g * b⁻¹) (fun v => v * b) ?_ ?_ ?_ ?_ ?_
      · exact fun g hg => mul_mem_cubeRootsOne hg hbinv
      · exact fun v hv => mul_mem_cubeRootsOne hv hb
      · intro g _; field_simp
      · intro v _; field_simp
      · intro g _; rfl
  have stepD : ∀ u v : K, V u 1 v = weilSum ψ D A B u v := by
    intro u v
    simp only [hV, weilSum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    ring
  have hfinal : ∑ b ∈ U, ∑ a ∈ U, ∑ g ∈ U, V a b g = ∑ _b ∈ U, ∑ u ∈ U, ∑ v ∈ U, V u 1 v := by
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun g hg => stepB a ha b hb g hg))]
    exact stepC b hb
  rw [stepA, Finset.sum_comm, hfinal]
  simp only [stepD, Finset.sum_const, nsmul_eq_mul, mu3Card, hU]

/-! ### Step 2: the root-count Weil sum -/

/-- The Weil sum in terms of the root count. -/
lemma weilSum_eq {ψ : AddChar K ℂ} {m D : ℕ} (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (hD : D ≠ 0)
    (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) {A B : K} (hA3 : A ^ 3 ≠ 1)
    {u v : K} (hu : u ∈ cubeRootsOne K) (hv : v ∈ cubeRootsOne K) :
    weilSum ψ D A B u v = (Fintype.card K : ℂ) * ((rootCount D A B u v : ℂ) - 1) := by
  rw [mem_cubeRootsOne] at hu hv
  -- on the slice `y = 0` the coefficient `u + v A^D` is nonzero, since `A^3 ≠ 1`
  have hAD : u + v * A ^ D ≠ 0 := by
    intro h
    rw [CharTwo.add_eq_zero] at h
    have h3 : (1 : K) = (A ^ 3) ^ D := by
      have h4 := congrArg (· ^ 3) h
      simp only [mul_pow, hu, hv, one_mul, ← pow_mul] at h4
      rw [h4]
      ring_nf
    exact hA3 (by rw [← pow_mul_eq_self hm hD hmD (A ^ 3), pow_mul', ← h3, one_pow])
  set C : K → K := fun t => u * t ^ D + v * (A * t + B) ^ D + 1 with hC
  -- for `y ≠ 0` substitute `x = t y`
  have hslice : ∀ y : K, y ≠ 0 →
      ∑ x : K, ψ (u * x ^ D + v * (A * x + B * y) ^ D + y ^ D) = ∑ t : K, ψ (C t * y ^ D) := by
    intro y hy
    refine (Fintype.sum_bijective (fun t : K => t * y) (mulRight_bijective₀ y hy) _ _ ?_).symm
    intro t
    congr 1
    have h1 : A * (t * y) + B * y = (A * t + B) * y := by ring
    rw [hC]
    simp only [h1, mul_pow]
    ring
  -- the slice `y = 0` vanishes
  have hzero : ∑ x : K, ψ (u * x ^ D + v * (A * x + B * (0:K)) ^ D + (0:K) ^ D) = 0 := by
    have hrw : ∀ x : K, u * x ^ D + v * (A * x + B * (0:K)) ^ D + (0:K) ^ D
        = (u + v * A ^ D) * x ^ D := by
      intro x
      simp only [mul_zero, add_zero, zero_pow hD, mul_pow]
      ring
    simp only [hrw]
    rw [sum_psi_mul_powD hψ hm hD hmD, ite_eq_right hAD]
  have hswap : weilSum ψ D A B u v
      = ∑ y : K, ∑ x : K, ψ (u * x ^ D + v * (A * x + B * y) ^ D + y ^ D) := by
    rw [weilSum, Finset.sum_comm]
  have hcompl : weilSum ψ D A B u v
      = ∑ y ∈ ({0} : Finset K)ᶜ, ∑ x : K, ψ (u * x ^ D + v * (A * x + B * y) ^ D + y ^ D) := by
    rw [hswap, ← Finset.sum_add_sum_compl ({0} : Finset K), Finset.sum_singleton, hzero, zero_add]
  rw [hcompl, Finset.sum_congr rfl (fun y hy => hslice y (by simpa using hy)), Finset.sum_comm]
  have hinner : ∀ t : K, ∑ y ∈ ({0} : Finset K)ᶜ, ψ (C t * y ^ D)
      = (if C t = 0 then (Fintype.card K : ℂ) else 0) - 1 := by
    intro t
    have h := Finset.sum_add_sum_compl ({0} : Finset K) (fun y : K => ψ (C t * y ^ D))
    rw [sum_psi_mul_powD hψ hm hD hmD] at h
    simp only [Finset.sum_singleton, zero_pow hD, mul_zero, AddChar.map_zero_eq_one] at h
    linear_combination h
  rw [Finset.sum_congr rfl (fun t _ => hinner t), Finset.sum_sub_distrib]
  simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  have hR : (Finset.univ.filter (fun t : K => C t = 0)).card = rootCount D A B u v := by
    rw [rootCount]
    congr 1
    apply Finset.filter_congr
    intro t _
    rw [hC]
    simp [CharTwo.add_eq_zero]
  rw [hR]
  ring

/-! ### Step 8: conclusion -/

/-- Fourier expansion and symmetrization reduce the phase triple sum to the total Weil sum.
This isolates the analytic bridge from the later root-count evaluation. -/
private lemma eight_phaseTripleSum_eq_card_mul_weilSum_sum
    {ψ : AddChar K ℂ} {m D e : ℕ} {S : K → ℂ} {A B : K}
    (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (hD : D ≠ 0)
    (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (he : e = 3 * m)
    (hS : WalshCharacterFormula ψ e S) (hA : A ≠ 0) (hB : B ≠ 0) :
    8 * phaseTripleSum S (A ^ 3) (B ^ 3)
      = (Fintype.card K : ℂ) *
          ∑ u ∈ cubeRootsOne K, ∑ v ∈ cubeRootsOne K, weilSum ψ D A B u v := by
  have hcne : (mu3Card K : ℂ) ≠ 0 := mu3Card_ne_zero
  have hunits : ∑ z : Kˣ, phiHat ψ D (z : K) * phiHat ψ D (A * z) * phiHat ψ D (B * z)
      = ∑ z : K, phiHat ψ D z * phiHat ψ D (A * z) * phiHat ψ D (B * z) := by
    refine sum_units_eq_sum (fun z => phiHat ψ D z * phiHat ψ D (A * z) * phiHat ψ D (B * z)) ?_
    simp [phiHat_zero hψ hm hD hmD]
  have key := eight_phaseTripleSum (S := S) hψ hm hD hmD he hS hA hB
  rw [hunits, fourier_triple hψ A B, symmetrization hm hD hmD A B] at key
  have h : (8 * phaseTripleSum S (A ^ 3) (B ^ 3)) * (mu3Card K : ℂ)
      = ((Fintype.card K : ℂ) *
          ∑ u ∈ cubeRootsOne K, ∑ v ∈ cubeRootsOne K, weilSum ψ D A B u v) *
            (mu3Card K : ℂ) := by
    linear_combination key
  exact mul_right_cancel₀ hcne h

/-- Summing the pointwise Weil-sum evaluation gives the total root-count correction. -/
private lemma sum_weilSum_eq_card_mul_rootCount_correction
    {ψ : AddChar K ℂ} {m D : ℕ} (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (hD : D ≠ 0)
    (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) {A B : K} (hA3 : A ^ 3 ≠ 1) :
    ∑ u ∈ cubeRootsOne K, ∑ v ∈ cubeRootsOne K, weilSum ψ D A B u v
      = (Fintype.card K : ℂ) *
          ((∑ u ∈ cubeRootsOne K, ∑ v ∈ cubeRootsOne K, (rootCount D A B u v : ℂ))
            - (mu3Card K : ℂ) ^ 2) := by
  have hterm : ∀ u ∈ cubeRootsOne K, ∀ v ∈ cubeRootsOne K,
      weilSum ψ D A B u v = (Fintype.card K : ℂ) * ((rootCount D A B u v : ℂ) - 1) :=
    fun u hu v hv => weilSum_eq hψ hm hD hmD hA3 hu hv
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => hterm u hu v hv))]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hone : (∑ _u ∈ cubeRootsOne K, ∑ _v ∈ cubeRootsOne K, (1 : ℂ)) =
      (mu3Card K : ℂ) ^ 2 := by
    simp [mu3Card, sq]
  rw [hone]

/-- **The phase-to-root-count identity.**  Let `K` be a finite field of characteristic two, `ψ` a
primitive additive character of `K`, `e = 3m` and `D` an inverse of `m` modulo `N = #Kˣ`.
Let `S : K → ℂ` satisfy the all-character Walsh formula. If `A, B ∈ K`, with
`A ≠ 0`, `A³ + B³ = 1`, and `A³ ≠ 1`,
then `Z(A³) = Q²/8 (∑_{u,v ∈ μ₃(K)} R_{u,v}(A,B) - c²)`.

(The source's hypothesis `B ≠ 0` is not stated separately here: it is implied by
`A³ + B³ = 1` together with `A³ ≠ 1`, and is derived inside the proof.) -/
theorem phase_to_root_count {ψ : AddChar K ℂ} {m D e : ℕ} {S : K → ℂ} {A B : K}
    (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (hD : D ≠ 0)
    (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (he : e = 3 * m) (hS : WalshCharacterFormula ψ e S)
    (hA : A ≠ 0) (hAB : A ^ 3 + B ^ 3 = 1) (hA3 : A ^ 3 ≠ 1) :
    phaseTripleSum S (A ^ 3) (B ^ 3)
      = (Fintype.card K : ℂ) ^ 2 / 8 *
        ((∑ u ∈ cubeRootsOne K, ∑ v ∈ cubeRootsOne K, (rootCount D A B u v : ℂ))
          - (mu3Card K : ℂ) ^ 2) := by
  have hB : B ≠ 0 := by
    rintro rfl
    exact hA3 (by simpa using hAB)
  have hphase := eight_phaseTripleSum_eq_card_mul_weilSum_sum
    (S := S) hψ hm hD hmD he hS hA hB
  have hroots := sum_weilSum_eq_card_mul_rootCount_correction
    (B := B) hψ hm hD hmD hA3
  rw [hroots] at hphase
  linear_combination hphase / 8

end KasamiCyclicAdditive.Phase
