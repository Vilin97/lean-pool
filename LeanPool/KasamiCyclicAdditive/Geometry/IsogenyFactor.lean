/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude

/-!
# Factoring `1 + π^k` through a prime-to-3 automorphism

For odd `k = 2r+1`, the isogeny `1 + π^k` factors as `(1 + π) ∘ G` with
`G = a - bπ`, where `a + 2b = 1`, `a - b = (-2)^r` and `a² + 2b² = m`, and
`H = a + bπ` satisfies `H ∘ G = G ∘ H = [m]`.  Whenever `[m]` is invertible on
the group — which on `E(K)` follows from an annihilator `N` coprime to `m` via
Bézout — `G` is bijective.

That isolates the entire 3-primary obstruction into the single factor `1 + π`,
and it is all abstract: this file is a calculation in a `ℤ`-module equipped
with an endomorphism `π` satisfying `π² = [-2]`.  No field, curve, Frobenius
map or algebraic closure appears.
-/

namespace KasamiCyclicAdditive.Isogeny

/-- The `n`-fold iterate of `pi`. -/
def piIter
    {G : Type*} [AddCommGroup G]
    (pi : G →+ G) : ℕ → G → G
  | 0, x => x
  | n + 1, x => pi (piIter pi n x)

/-- `a - b*pi`. -/
def gMap
    {G : Type*} [AddCommGroup G]
    (pi : G →+ G) (a b : ℤ) (x : G) : G :=
  a • x - b • pi x

/-- `a + b*pi`. -/
def hMap
    {G : Type*} [AddCommGroup G]
    (pi : G →+ G) (a b : ℤ) (x : G) : G :=
  a • x + b • pi x

/-- `gMap` commutes with multiplication by an integer. -/
lemma gMap_zsmul
    {G : Type*} [AddCommGroup G]
    (pi : G →+ G) (a b c : ℤ) (x : G) :
    gMap pi a b (c • x) = c • gMap pi a b x := by
  simp only [gMap, smul_sub, smul_smul, map_zsmul, mul_comm c]

/-- `gMap` commutes with `1 + pi`. -/
lemma gMap_add_map
    {G : Type*} [AddCommGroup G]
    (pi : G →+ G) (a b : ℤ) (x : G) :
    gMap pi a b x + pi (gMap pi a b x) = gMap pi a b (x + pi x) := by
  simp only [gMap, map_add, map_sub, map_zsmul]
  module

/-- `(-2)^r` is congruent to `1` modulo `3`. -/
lemma neg_two_pow_eq_one_add_three_mul (r : ℕ) :
    ∃ c : ℤ, (-2 : ℤ) ^ r = 1 + 3 * c := by
  induction r with
  | zero => exact ⟨0, by ring⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨-1 - 2 * c, by rw [pow_succ, hc]; ring⟩

/--
Arithmetic coefficients for the factorisation.

For `k = 2*r+1` and `2^k+1 = 3*m`, there are integers `a,b`
such that

    a + 2b = 1,
    a - b = (-2)^r,
    a^2 + 2b^2 = m.

Explicitly one may take

    b = (1 - (-2)^r)/3,
    a = (1 + 2*(-2)^r)/3.
-/
theorem exists_factor_coefficients
    {r m : ℕ}
    (he : 2 ^ (2 * r + 1) + 1 = 3 * m) :
    ∃ a b : ℤ,
      a + 2 * b = 1 ∧
      a - b = (-2 : ℤ) ^ r ∧
      a ^ 2 + 2 * b ^ 2 = (m : ℤ) := by
  obtain ⟨c, hc⟩ := neg_two_pow_eq_one_add_three_mul r
  refine ⟨1 + 2 * c, -c, by ring, by rw [hc]; ring, ?_⟩
  -- transfer the hypothesis to `ℤ`
  have heZ : (2 : ℤ) ^ (2 * r + 1) + 1 = 3 * (m : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) he
  have hsq : ((-2 : ℤ) ^ r) ^ 2 = 4 ^ r := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h4 : (2 : ℤ) ^ (2 * r + 1) = 2 * ((-2 : ℤ) ^ r) ^ 2 := by
    rw [hsq, pow_succ, pow_mul]; norm_num [mul_comm]
  rw [h4, hc] at heZ
  have : (3 : ℤ) * ((1 + 2 * c) ^ 2 + 2 * (-c) ^ 2) = 3 * (m : ℤ) := by
    rw [← heZ]; ring
  exact mul_left_cancel₀ (by norm_num) this

/-- Iterating `π² = [-2]`: the even powers of `π` are integer multiplications. -/
theorem piIter_even
    {G : Type*} [AddCommGroup G] (pi : G →+ G)
    (hpi2 : ∀ x : G, pi (pi x) = (-2 : ℤ) • x) (n : ℕ) (x : G) :
    piIter pi (2 * n) x = ((-2 : ℤ) ^ n) • x := by
  induction n generalizing x with
  | zero => simp [piIter]
  | succ k ih =>
    have h2 : 2 * (k + 1) = (2 * k) + 1 + 1 := by ring
    rw [h2]
    change pi (pi (piIter pi (2 * k) x)) = _
    rw [ih x, hpi2, smul_smul, pow_succ]
    ring_nf

/-- The factorization `(1 + π) ∘ G = 1 + π^(2r+1)`, with no invertibility
hypothesis.  Stated separately because it is needed over the algebraic closure,
where the group has no finite annihilator and `G` need not be bijective. -/
theorem gMap_factor
    {G : Type*} [AddCommGroup G]
    (pi : G →+ G)
    {r : ℕ} {a b : ℤ}
    (hpi2 : ∀ x : G, pi (pi x) = (-2 : ℤ) • x)
    (hab1 : a + 2 * b = 1)
    (hab2 : a - b = (-2 : ℤ) ^ r) :
    ∀ x : G, x + piIter pi (2 * r + 1) x
      = gMap pi a b x + pi (gMap pi a b x) := by
  have hz : ∀ (c : ℤ) (x : G), pi (c • x) = c • pi x := fun c x => map_zsmul pi c x
  have hiter1 : ∀ x : G, piIter pi (2 * r + 1) x = ((-2 : ℤ) ^ r) • pi x := by
    intro x
    change pi (piIter pi (2 * r) x) = _
    rw [piIter_even pi hpi2 r x, hz]
  intro x
  have hpg : pi (gMap pi a b x) = a • pi x + (2 * b) • x := by
    simp only [gMap, map_sub, hz, hpi2, smul_smul]
    module
  have key : gMap pi a b x + pi (gMap pi a b x)
      = (a + 2 * b) • x + (a - b) • pi x := by
    rw [hpg]
    simp only [gMap]
    module
  rw [hiter1 x, key, hab1, hab2, one_smul]

/--
Invertibility of `G = a - b*pi`.

Assume `pi² = [-2]` on an abelian group, and put `H = a + b*pi`.  The norm
identity `a² + 2b² = m` gives `HG = GH = [m]`, so if every element of the group
is killed by an integer `N` coprime to `m`, multiplication by `m` is invertible
by Bezout and hence `G` is bijective.

This needs neither `r` nor the coefficient identities: the factorization
`(1 + pi) G = 1 + pi^(2r+1)` is the separate statement `gMap_factor`.
-/
theorem gMap_bijective
    {G : Type*} [AddCommGroup G]
    (pi : G →+ G)
    {m : ℕ} {N a b : ℤ}
    (hpi2 : ∀ x : G, pi (pi x) = (-2 : ℤ) • x)
    (hnorm : a ^ 2 + 2 * b ^ 2 = (m : ℤ))
    (hann : ∀ x : G, N • x = 0)
    (hcop : IsCoprime (m : ℤ) N) :
    Function.Bijective (gMap pi a b) := by
  have hz : ∀ (c : ℤ) (x : G), pi (c • x) = c • pi x := fun c x => map_zsmul pi c x
  -- composition identities
  have hHG : ∀ x : G, hMap pi a b (gMap pi a b x) = (m : ℤ) • x := by
    intro x
    have hpg : pi (gMap pi a b x) = a • pi x + (2 * b) • x := by
      simp only [gMap, map_sub, hz, hpi2, smul_smul]
      module
    simp only [hMap]
    rw [hpg]
    simp only [gMap]
    rw [← hnorm]
    module
  have hGH : ∀ x : G, gMap pi a b (hMap pi a b x) = (m : ℤ) • x := by
    intro x
    have hph : pi (hMap pi a b x) = a • pi x + (-2 * b) • x := by
      simp only [hMap, map_add, hz, hpi2, smul_smul]
      module
    simp only [gMap]
    rw [hph]
    simp only [hMap]
    rw [← hnorm]
    module
  -- Bezout: multiplication by m is invertible
  obtain ⟨u, v, huv⟩ := hcop
  have hmu : ∀ x : G, u • ((m : ℤ) • x) = x := by
    intro x
    have : (u * (m : ℤ)) • x + (v * N) • x = (1 : ℤ) • x := by
      rw [← add_smul, huv]
    rw [mul_smul, mul_smul, hann, smul_zero, add_zero, one_smul] at this
    exact this
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h1 : (m : ℤ) • x = (m : ℤ) • y := by
      rw [← hHG x, ← hHG y, hxy]
    rw [← hmu x, ← hmu y, h1]
  · intro y
    refine ⟨hMap pi a b (u • y), ?_⟩
    rw [hGH, smul_comm, hmu]

end KasamiCyclicAdditive.Isogeny
