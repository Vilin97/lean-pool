/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push


/-!
# Lattice-ordered groups and vector lattices

This file develops the basic order-theoretic algebra of lattice-ordered groups and vector
lattices. The first part works in the general setting of an additive commutative group with a
compatible lattice order (`IsOrderedAddMonoid`): it establishes properties of `x⁺`, `x⁻`,
and `|x|`, together with order-theoretic suprema and infima lemmas. The second part adds a
real scalar multiplication (`VectorLattice`) and proves that positive scalars distribute over
`⊔` and `⊓`, culminating in `abs_smul'`. The Archimedean case is treated at the end.
-/

@[expose] public section

/-- A real vector lattice is a real module whose scalar multiplication is monotone for
non-negative scalars and is compatible with the lattice-ordered additive structure. -/
class VectorLattice (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] extends
  Module ℝ X,
  PosSMulMono ℝ X

/-- The real numbers form a vector lattice over themselves. -/
noncomputable instance : VectorLattice ℝ where

section LatticeOrderedGroup

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

variable (x : X)

/-- An element of a lattice-ordered group is zero iff its absolute value is zero.
Extends `Mathlib.Algebra.Order.Module.Basic.abs_eq_zero` to the non-total-order setting. -/
theorem abs_eq_zero_iff_zero : |x| = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [← negPart_add_posPart, add_eq_zero_iff_eq_neg] at h
    have h1 : x⁺ = 0 := by
      apply le_antisymm
      · rw [← neg_zero]
        apply le_neg_of_le_neg
        rw [← h]
        exact negPart_nonneg x
      · exact posPart_nonneg x
    have h2 : x⁻ = 0 := by
      apply le_antisymm
      · rw [h]
        apply neg_le_of_neg_le
        rw [neg_zero]
        exact posPart_nonneg x
      · exact negPart_nonneg x
    rw [← posPart_sub_negPart x]
    rw [h1, h2]
    simp
  · intro h
    simp [h]

/-- If `x = u - v` with `u ⊓ v = 0`, then `u` is the positive part of `x`. -/
theorem uniqueness_posPart {u v : X} (hdif : x = u - v) (udisv : u ⊓ v = 0) :
    u = x⁺ := by
  symm
  calc
         x⁺ = x ⊔ 0 := by rfl
         _ = (u - v) ⊔ 0 := by rw [hdif]
         _ = u ⊔ v + (-v) := by rw [add_comm, add_sup]; simp [sub_eq_add_neg, add_comm]
         _ = u + v + (-v) := by rw [← inf_add_sup u v, udisv, zero_add]
         _ = u := by simp

/-- `x ⊔ y = x + (y - x)⁺`. -/
theorem sup_eq_add_posPart (y : X) : x ⊔ y = x + (y - x)⁺ := by
  rw [posPart_def, add_sup, add_sub_cancel, add_zero, sup_comm]

/-- `x ⊓ y = x - (x - y)⁺`. -/
theorem inf_eq_sub_posPart (y : X) : x ⊓ y = x - (x - y)⁺ := by
  rw [posPart_def, sub_eq_add_neg, neg_sup, neg_sub, neg_zero, add_inf, add_zero, inf_comm]
  congr 1; abel

/-- `x - x ⊓ y = (x - y)⁺`. -/
theorem sub_inf_eq_posPart (y : X) : x - x ⊓ y = (x - y)⁺ := by
  rw [inf_eq_sub_posPart, sub_sub_cancel]

/-- The positive part is subadditive: `(x + y)⁺ ≤ x⁺ + y⁺`. -/
theorem posPart_add_le (y : X) : (x + y)⁺ ≤ x⁺ + y⁺ :=
  sup_le (add_le_add (le_posPart x) (le_posPart y))
    (add_nonneg (posPart_nonneg x) (posPart_nonneg y))

/-- The positive part is bounded by the modulus. -/
theorem posPart_le_abs : x⁺ ≤ |x| := by
  rw [posPart_def]
  exact sup_le (le_abs_self x) (abs_nonneg x)

/-- The negative part is bounded by the modulus. -/
theorem negPart_le_abs : x⁻ ≤ |x| := by
  rw [negPart_def]
  exact sup_le (neg_le_abs x) (abs_nonneg x)

/-- For non-negative `x`, `a`, `b`: `x ⊓ (a + b) ≤ x ⊓ a + x ⊓ b`. -/
theorem inf_le_inf_add_inf_of_nonneg (a b : X) (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    x ⊓ (a + b) ≤ x ⊓ a + x ⊓ b := by
  set c := x ⊓ (a + b) with hc_def
  have hcx : c ≤ x := inf_le_left
  have hcab : c ≤ a + b := inf_le_right
  have hca_nn : 0 ≤ c ⊓ a := le_inf (le_inf hx (add_nonneg ha hb)) ha
  have h1 : c - c ⊓ a = (c - a)⁺ := sub_inf_eq_posPart c a
  have h2 : (c - a)⁺ ≤ b := by
    rw [← posPart_of_nonneg hb]
    exact posPart_mono (sub_le_iff_le_add.mpr (by rwa [add_comm]))
  have h3 : c - c ⊓ a ≤ x := by
    have := sub_le_self c hca_nn
    exact this.trans hcx
  have h4 : c - c ⊓ a ≤ x ⊓ b := le_inf h3 (h1 ▸ h2)
  have h5 : c ⊓ a ≤ x ⊓ a := inf_le_inf_right _ hcx
  have h4' : c ≤ x ⊓ b + c ⊓ a := sub_le_iff_le_add.mp h4
  calc c ≤ x ⊓ b + c ⊓ a := h4'
    _ ≤ x ⊓ b + x ⊓ a := by gcongr
    _ = x ⊓ a + x ⊓ b := add_comm _ _

/-- Translation preserves suprema: `x + sup A = sup(x + A)`. -/
theorem isLUB_const_add {A : Set X} {a : X} (x : X) (h : IsLUB A a) :
    IsLUB ((fun z => x + z) '' A) (x + a) :=
  (OrderIso.addLeft x).isLUB_image'.mpr h

/-- Translation preserves infima: `x + inf A = inf(x + A)`. -/
theorem isGLB_const_add {A : Set X} {a : X} (x : X) (h : IsGLB A a) :
    IsGLB ((fun z => x + z) '' A) (x + a) :=
  (OrderIso.addLeft x).isGLB_image'.mpr h

/-- Meet distributes over arbitrary suprema: `x ⊓ sup A = sup {x ⊓ a : a ∈ A}`. -/
theorem isLUB_inf_const {A : Set X} {a : X} (x : X) (h : IsLUB A a) :
    IsLUB ((fun z => x ⊓ z) '' A) (x ⊓ a) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact inf_le_inf_left x (h.1 hz)
  · intro u hu
    have hA : ∀ z ∈ A, z ≤ u + (a - x)⁺ := by
      intro z hz
      have hzu : z - (z - x)⁺ ≤ u := by
        rw [← inf_eq_sub_posPart, inf_comm]; exact hu ⟨z, hz, rfl⟩
      have hmono : (z - x)⁺ ≤ (a - x)⁺ := posPart_mono (sub_le_sub_right (h.1 hz) x)
      have h1 : z ≤ u + (z - x)⁺ := sub_le_iff_le_add.mp hzu
      exact h1.trans (by gcongr)
    have key : a ≤ u + (a - x)⁺ := h.2 hA
    calc x ⊓ a = a ⊓ x := inf_comm _ _
      _ = a - (a - x)⁺ := inf_eq_sub_posPart a x
      _ ≤ u := sub_le_iff_le_add.mpr key

/-- Join distributes over arbitrary infima: `x ⊔ inf A = inf {x ⊔ a : a ∈ A}`. -/
theorem isGLB_sup_const {A : Set X} {a : X} (x : X) (h : IsGLB A a) :
    IsGLB ((fun z => x ⊔ z) '' A) (x ⊔ a) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact sup_le_sup_left (h.1 hz) x
  · intro u hu
    have hA : ∀ z ∈ A, u - (x - a)⁺ ≤ z := by
      intro z hz
      have hzu : u ≤ z + (x - z)⁺ := by
        rw [← sup_eq_add_posPart, sup_comm]; exact hu ⟨z, hz, rfl⟩
      have hmono : (x - z)⁺ ≤ (x - a)⁺ := posPart_mono (sub_le_sub_left (h.1 hz) x)
      exact sub_le_iff_le_add.mpr (hzu.trans (by gcongr))
    have key : u - (x - a)⁺ ≤ a := h.2 hA
    calc u = (u - (x - a)⁺) + (x - a)⁺ := by abel
      _ ≤ a + (x - a)⁺ := by gcongr
      _ = a ⊔ x := (sup_eq_add_posPart a x).symm
      _ = x ⊔ a := sup_comm _ _

/-- `inf(A + B) = inf A + inf B`. -/
theorem isGLB_add_sets {A B : Set X} {a b : X}
    (hA : IsGLB A a) (hB : IsGLB B b) :
    IsGLB ((fun p : X × X => p.1 + p.2) '' (A ×ˢ B)) (a + b) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩
    exact add_le_add (hA.1 hp) (hB.1 hq)
  · intro u hu
    have h1 : ∀ p ∈ A, u ≤ p + b := by
      intro p hp
      have hp_lb : u - p ∈ lowerBounds B := fun q hq => by
        have hpq : u ≤ p + q := hu ⟨(p, q), ⟨hp, hq⟩, rfl⟩
        rw [add_comm] at hpq
        exact sub_le_iff_le_add.mpr hpq
      have : u ≤ b + p := sub_le_iff_le_add.mp (hB.2 hp_lb)
      rwa [add_comm] at this
    have h2 : u - b ∈ lowerBounds A := fun p hp =>
      sub_le_iff_le_add.mpr (h1 p hp)
    exact sub_le_iff_le_add.mp (hA.2 h2)

/-- `inf(A ∨ B) = inf A ∨ inf B`, where `A ∨ B = {p ⊔ q : p ∈ A, q ∈ B}`. -/
theorem isGLB_sup_sets {A B : Set X} {a b : X}
    (hA : IsGLB A a) (hB : IsGLB B b) :
    IsGLB ((fun p : X × X => p.1 ⊔ p.2) '' (A ×ˢ B)) (a ⊔ b) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩
    exact sup_le_sup (hA.1 hp) (hB.1 hq)
  · intro u hu
    have h1 : ∀ q ∈ B, u ≤ a ⊔ q := by
      intro q hq
      have hlb : u ∈ lowerBounds ((fun z => q ⊔ z) '' A) := by
        rintro _ ⟨p, hp, rfl⟩
        have hpq : u ≤ p ⊔ q := hu ⟨(p, q), ⟨hp, hq⟩, rfl⟩
        rw [sup_comm] at hpq; exact hpq
      have hqa : u ≤ q ⊔ a := (isGLB_sup_const q hA).2 hlb
      rwa [sup_comm] at hqa
    exact (isGLB_sup_const a hB).2 (by rintro _ ⟨q, hq, rfl⟩; exact h1 q hq)

omit [AddCommGroup X] [IsOrderedAddMonoid X] in
/-- `inf(A ∪ B) = (inf A) ⊓ (inf B)`. -/
theorem isGLB_union {A B : Set X} {a b : X}
    (hA : IsGLB A a) (hB : IsGLB B b) : IsGLB (A ∪ B) (a ⊓ b) := by
  refine ⟨?_, ?_⟩
  · rintro z (hz | hz)
    · exact inf_le_left.trans (hA.1 hz)
    · exact inf_le_right.trans (hB.1 hz)
  · intro u hu
    have ha : u ≤ a := hA.2 fun z hz => hu (Or.inl hz)
    have hb : u ≤ b := hB.2 fun z hz => hu (Or.inr hz)
    exact le_inf ha hb

end LatticeOrderedGroup

section VectorLattice

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

variable (x y : X)

/-- A non-negative scalar distributes over `⊔`. -/
theorem nonneg_smul_sup (a : ℝ) (nonneg : a ≥ 0) :
  a • (x ⊔ y) = (a • x) ⊔ (a • y) := by
  by_cases h : a = 0
  · subst h
    simp only [zero_smul]; exact Eq.symm Std.max_self
  · apply le_antisymm
    · have hx : a⁻¹ • a • x ≤ a⁻¹ • (a • x ⊔ a • y) := by
        exact smul_le_smul_of_nonneg_left
         le_sup_left
         (by norm_num [nonneg])
      have hy : a⁻¹ • a • y ≤ a⁻¹ • (a • x ⊔ a • y) := by
        exact smul_le_smul_of_nonneg_left
         le_sup_right
         (by norm_num [nonneg])
      simp only [inv_smul_smul₀ h] at hx hy
      have hxy : x ⊔ y ≤ a⁻¹ • (a • x ⊔ a • y) :=
        sup_le hx hy
      calc
        a • (x ⊔ y) ≤ a • (a⁻¹ • (a • x ⊔ a • y)) := by
                      exact smul_le_smul_of_nonneg_left hxy nonneg
                  _ = a • x ⊔ a • y := by rw [smul_smul a a⁻¹ _]; norm_num [h];
    · have hx : a • x ≤ a • (x ⊔ y) :=
        smul_le_smul_of_nonneg_left le_sup_left nonneg
      have hy : a • y ≤ a • (x ⊔ y) :=
        smul_le_smul_of_nonneg_left le_sup_right nonneg
      exact sup_le hx hy

/-- A non-negative scalar commutes with the positive part. -/
theorem posPart_smul_nonneg {a : ℝ} (ha : 0 ≤ a) (x : X) :
    (a • x)⁺ = a • x⁺ := by
  change (a • x) ⊔ 0 = a • (x ⊔ 0)
  rw [← smul_zero a, ← nonneg_smul_sup x 0 a ha, smul_zero]

/-- A non-negative scalar distributes over suprema: `λ • sup A = sup (λ • A)`. -/
theorem isLUB_smul_of_nonneg {A : Set X} {a : X} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : IsLUB A a) : IsLUB ((fun z => lam • z) '' A) (lam • a) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact smul_le_smul_of_nonneg_left (h.1 hz) hlam
  · intro u hu
    by_cases hl : lam = 0
    · subst hl; rw [zero_smul]
      rcases A.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
      · have hmin : ∀ b : X, a ≤ b := fun b =>
          h.2 fun x hx => (Set.notMem_empty x hx).elim
        have h0a : 0 ≤ a :=
          (add_le_add_iff_left a).mp (by rw [add_zero]; exact hmin (a + a))
        exact h0a.trans (hmin u)
      · have : (0 : ℝ) • z ≤ u := hu ⟨z, hz, rfl⟩
        rwa [zero_smul] at this
    · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hl)
      have hinv_nn : 0 ≤ lam⁻¹ := le_of_lt (inv_pos.mpr hlam_pos)
      have h_ub : lam⁻¹ • u ∈ upperBounds A := fun z hz => by
        have h1 : lam⁻¹ • (lam • z) ≤ lam⁻¹ • u :=
          smul_le_smul_of_nonneg_left (hu ⟨z, hz, rfl⟩) hinv_nn
        rwa [inv_smul_smul₀ hl] at h1
      have h4 : lam • a ≤ lam • (lam⁻¹ • u) :=
        smul_le_smul_of_nonneg_left (h.2 h_ub) hlam
      rwa [smul_inv_smul₀ hl] at h4

/-- A non-negative scalar distributes over infima: `λ • inf A = inf (λ • A)`. -/
theorem isGLB_smul_of_nonneg {A : Set X} {a : X} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : IsGLB A a) : IsGLB ((fun z => lam • z) '' A) (lam • a) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact smul_le_smul_of_nonneg_left (h.1 hz) hlam
  · intro u hu
    by_cases hl : lam = 0
    · subst hl; rw [zero_smul]
      rcases A.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
      · have hmax : ∀ b : X, b ≤ a := fun b =>
          h.2 fun x hx => (Set.notMem_empty x hx).elim
        have ha0 : a ≤ 0 :=
          (add_le_add_iff_left a).mp (by rw [add_zero]; exact hmax (a + a))
        exact (hmax u).trans ha0
      · have : u ≤ (0 : ℝ) • z := hu ⟨z, hz, rfl⟩
        rwa [zero_smul] at this
    · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hl)
      have hinv_nn : 0 ≤ lam⁻¹ := le_of_lt (inv_pos.mpr hlam_pos)
      have h_lb : lam⁻¹ • u ∈ lowerBounds A := fun z hz => by
        have h1 : lam⁻¹ • u ≤ lam⁻¹ • (lam • z) :=
          smul_le_smul_of_nonneg_left (hu ⟨z, hz, rfl⟩) hinv_nn
        rwa [inv_smul_smul₀ hl] at h1
      have h4 : lam • (lam⁻¹ • u) ≤ lam • a :=
        smul_le_smul_of_nonneg_left (h.2 h_lb) hlam
      rwa [smul_inv_smul₀ hl] at h4

/-- A non-negative scalar distributes over `⊓`. -/
theorem nonneg_smul_inf (a : ℝ) (nonneg : a ≥ 0) :
  a • (x ⊓ y) = (a • x) ⊓ (a • y) := by
    calc
      a • (x ⊓ y) = (-1) • a • (- (x ⊓ y)) := by simp
                _ = (-1) • a • ((-x) ⊔ (-y)) := by rw [neg_inf]
                _ = (-1) • ((a • -x) ⊔ (a • -y)) := by rw [nonneg_smul_sup (-x) (-y) a nonneg]
                _ = - ((-a • x) ⊔ (-a • y)) := by simp
                _ = (a • x) ⊓ (a • y) := by rw [neg_sup]; simp

/-- Scalar `sup` distributes over a non-negative element. -/
theorem sup_smul_nonneg (a b : ℝ) (h : 0 ≤ x) :
    (a ⊔ b) • x = (a • x) ⊔ (b • x) := by
  apply le_antisymm
  · cases max_choice a b with
      | inl h => rw [h]; exact le_sup_left
      | inr h => rw [h]; exact le_sup_right
  · apply sup_le
    · exact smul_le_smul_of_nonneg_right le_sup_left h
    · exact smul_le_smul_of_nonneg_right le_sup_right h

/-- Scalar `inf` distributes over a non-negative element. -/
theorem inf_smul_nonneg (a b : ℝ) (h : 0 ≤ x) :
    (a ⊓ b) • x = (a • x) ⊓ (b • x) := by
  apply le_antisymm
  · apply le_inf
    · exact smul_le_smul_of_nonneg_right inf_le_left h
    · exact smul_le_smul_of_nonneg_right inf_le_right h
  · cases min_choice a b with
      | inl h => rw [h]; exact inf_le_left
      | inr h => rw [h]; exact inf_le_right

/-- `|a • x| = |a| • |x|` in a vector lattice.
Extends the Mathlib result of the same name from total orders to lattice orders. -/
theorem abs_smul' (a : ℝ) : |a • x| = |a| • |x| := by
  by_cases ha : a ≥ 0
  · rw [abs_of_nonneg ha]
    rw [abs, abs]
    rw [nonneg_smul_sup x (-x) a ha]
    simp
  · have hna : a < 0 := by linarith
    rw [abs_of_neg hna]
    rw [abs, abs]
    rw [nonneg_smul_sup x (-x) (-a) (by linarith)]
    simp [sup_comm]

section Archimedean

/-- A lattice-ordered group is **Archimedean** (in the vector-lattice sense) when the only
non-negative element all of whose multiples are bounded is zero: `0 ≤ x` and `∀ n, n • x ≤ y`
imply `x = 0`. This is the standard Archimedean property for partially ordered groups; it is
weaker than Mathlib's `Archimedean` class, which is stated for linearly ordered monoids. -/
class IsVLArchimedean (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] : Prop where
  le_zero_of_forall_nsmul_le {x y : X} :
    (∀ n : ℕ, n • x ≤ y) → x ≤ 0

private lemma nsmul_posPart_le_of_forall_nsmul_le {Y : Type*} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] (x : Y) :
    ∀ (n : ℕ) (v : Y), (∀ k : ℕ, k ≤ n → k • x ≤ v) → n • (x ⊔ 0) ≤ v := by
  intro n
  induction n with
  | zero =>
    intro v h
    simpa using h 0 (le_refl 0)
  | succ n ih =>
    intro v h
    rw [succ_nsmul, add_sup, add_zero]
    refine sup_le ?_ (ih v fun k hk => h k (hk.trans (Nat.le_succ n)))
    rw [← le_sub_iff_add_le]
    refine ih (v - x) fun k hk => ?_
    rw [le_sub_iff_add_le, ← succ_nsmul]
    exact h (k + 1) (Nat.succ_le_succ hk)

omit [VectorLattice X] in
/-- Constructor from the non-negative formulation of the Archimedean property. -/
theorem isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
    (H : ∀ {x y : X}, 0 ≤ x → (∀ n : ℕ, n • x ≤ y) → x = 0) :
    IsVLArchimedean X := by
  refine ⟨fun {x y} h => ?_⟩
  have hsup : x ⊔ 0 = 0 :=
    H le_sup_right
      (fun n => nsmul_posPart_le_of_forall_nsmul_le x n y fun k _ => h k)
  exact sup_eq_right.mp hsup

omit [VectorLattice X] in
/-- In a vector lattice, being Archimedean is equivalent to the condition that
`n • x ≤ y` for all `n : ℕ` implies `x ≤ 0`. -/
theorem isVLArchimedean_iff_le_zero_of_forall_nsmul_le :
    IsVLArchimedean X ↔ ∀ {x y : X}, (∀ n : ℕ, n • x ≤ y) → x ≤ 0 := by
  exact ⟨fun hArch _ _ h => hArch.le_zero_of_forall_nsmul_le h,
    fun H => ⟨fun {x y} h => H h⟩⟩

namespace IsVLArchimedean

omit [VectorLattice X] in
/-- Non-negative form of the Archimedean property. -/
theorem eq_zero_of_nonneg_of_forall_nsmul_le [IsVLArchimedean X] {x y : X}
    (hx : 0 ≤ x) (h : ∀ n : ℕ, n • x ≤ y) : x = 0 :=
  le_antisymm (IsVLArchimedean.le_zero_of_forall_nsmul_le h) hx

end IsVLArchimedean

/-- A vector lattice is Archimedean iff for every positive `u`, the infimum of
`(1/n) • u` over `n ≥ 1` equals `0`. -/
theorem isVLArchimedean_iff_isGLB_inv_smul :
    IsVLArchimedean X ↔
      ∀ u : X, 0 ≤ u →
        IsGLB {v : X | ∃ n : ℕ, 0 < n ∧ v = (n : ℝ)⁻¹ • u} 0 := by
  constructor
  · intro hArch u hu
    refine ⟨?_, ?_⟩
    · rintro _ ⟨n, _, rfl⟩
      exact smul_nonneg (by positivity) hu
    · intro w hw
      apply isVLArchimedean_iff_le_zero_of_forall_nsmul_le.mp hArch (y := u)
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · simpa using hu
      · have hwn : w ≤ (n : ℝ)⁻¹ • u := hw ⟨n, hnpos, rfl⟩
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h1 : (n : ℝ) • w ≤ (n : ℝ) • ((n : ℝ)⁻¹ • u) :=
          smul_le_smul_of_nonneg_left hwn hn_nn
        rw [smul_inv_smul₀ (Nat.cast_ne_zero.mpr hnpos.ne')] at h1
        rwa [Nat.cast_smul_eq_nsmul] at h1
  · intro H
    apply isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
    intro x y hx h
    set u := y ⊔ 0 with hu_def
    have hu : 0 ≤ u := le_sup_right
    have hx_lb : x ∈ lowerBounds {v : X | ∃ n : ℕ, 0 < n ∧ v = (n : ℝ)⁻¹ • u} := by
      rintro _ ⟨n, hnpos, rfl⟩
      have h1 : (n : ℝ) • x ≤ u := by
        rw [Nat.cast_smul_eq_nsmul]
        exact (h n).trans le_sup_left
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
      have h2 : (n : ℝ)⁻¹ • ((n : ℝ) • x) ≤ (n : ℝ)⁻¹ • u :=
        smul_le_smul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hn_pos))
      rwa [inv_smul_smul₀ hn_pos.ne'] at h2
    exact le_antisymm ((H u hu).2 hx_lb) hx

variable [IsVLArchimedean X]

omit [VectorLattice X] in
/-- An element whose absolute-value multiples are bounded must be zero. -/
theorem infinitesimal_eq_zero {x y : X}
    (h : ∀ n : ℕ, n • |x| ≤ y) : x = 0 := by
  have hab : |x| = 0 :=
    IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le (abs_nonneg x) h
  exact (abs_eq_zero_iff_zero x).mp hab

private lemma exists_real_eq_smul_of_linear_comparable
    (hcon : ∀ z : X, 0 ≤ z ∨ z ≤ 0)
    {u v : X} (hu : 0 ≤ u) (hu0 : u ≠ 0) (hv : 0 ≤ v) :
    ∃ r : ℝ, v = r • u := by
  let S : Set ℝ := {r | r • u ≤ v}
  have hS_ne : S.Nonempty := ⟨0, by simp [S, hv]⟩
  have hN : ∃ n : ℕ, ¬ (n : ℝ) • u ≤ v := by
    by_contra hna
    push Not at hna
    exact hu0 <| le_antisymm
      (isVLArchimedean_iff_le_zero_of_forall_nsmul_le.mp inferInstance
        (fun n => (Nat.cast_smul_eq_nsmul ℝ n u) ▸ hna n)) hu
  obtain ⟨N, hNp⟩ := hN
  have hS_bdd : BddAbove S := ⟨(N : ℝ), fun r hr => by
    by_contra hlt; push Not at hlt
    exact hNp ((smul_le_smul_of_nonneg_right hlt.le hu).trans hr)⟩
  set lam := sSup S with hlam_def
  refine ⟨lam, ?_⟩
  have heq : v - lam • u = 0 := by
    refine infinitesimal_eq_zero (y := u) fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · simpa using hu
    have hm_real_pos : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have hm_inv_pos : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hm_real_pos
    have hUp : v - lam • u ≤ (m : ℝ)⁻¹ • u := by
      have h_not : ¬ (lam + (m : ℝ)⁻¹) • u ≤ v := fun hle =>
        (lt_add_of_pos_right lam hm_inv_pos).not_ge (le_csSup hS_bdd hle)
      have hvle : v ≤ (lam + (m : ℝ)⁻¹) • u := by
        rcases hcon (v - (lam + (m : ℝ)⁻¹) • u) with hnn | hnp
        · exact absurd (sub_nonneg.mp hnn) h_not
        · exact sub_nonpos.mp hnp
      rw [add_smul] at hvle
      exact sub_le_iff_le_add.mpr (by rwa [add_comm])
    have hLo : -((m : ℝ)⁻¹ • u) ≤ v - lam • u := by
      obtain ⟨r, hrS, hr⟩ : ∃ r ∈ S, lam - (m : ℝ)⁻¹ < r :=
        exists_lt_of_lt_csSup hS_ne (sub_lt_self lam hm_inv_pos)
      have h2 : (lam - (m : ℝ)⁻¹) • u ≤ v :=
        (smul_le_smul_of_nonneg_right hr.le hu).trans hrS
      rw [sub_smul] at h2
      rw [neg_le, neg_sub]
      have h3 : lam • u ≤ v + (m : ℝ)⁻¹ • u := sub_le_iff_le_add.mp h2
      rw [add_comm] at h3
      exact sub_le_iff_le_add.mpr h3
    have habs : |v - lam • u| ≤ (m : ℝ)⁻¹ • u :=
      abs_le'.mpr ⟨hUp, neg_le.mp hLo⟩
    have hm_nn : (0 : ℝ) ≤ m := hm_real_pos.le
    have hmabs : (m : ℝ) • |v - lam • u| ≤ (m : ℝ) • ((m : ℝ)⁻¹ • u) :=
      smul_le_smul_of_nonneg_left habs hm_nn
    rw [smul_inv_smul₀ hm_real_pos.ne'] at hmabs
    rwa [Nat.cast_smul_eq_nsmul] at hmabs
  exact sub_eq_zero.mp heq

/-- If `X` is an Archimedean vector lattice with more than one dimension, then
there exists a vector in `X` which is neither positive nor negative. -/
theorem exists_not_nonneg_not_nonpos_of_one_lt_rank
    (h : 1 < Module.rank ℝ X) : ∃ x : X, ¬ 0 ≤ x ∧ ¬ x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hcon' : ∀ x : X, 0 ≤ x ∨ x ≤ 0 :=
    fun x => (Classical.or_iff_not_imp_left).mpr (hcon x)
  have hnt : Nontrivial X :=
    (rank_pos_iff_nontrivial (R := ℝ) (M := X)).mp (lt_of_le_of_lt zero_le_one h)
  obtain ⟨x0, hx0⟩ : ∃ x : X, x ≠ 0 := exists_ne 0
  obtain ⟨y0, hxy⟩ := exists_linearIndependent_pair_of_one_lt_rank h hx0
  have hy0 : y0 ≠ 0 := by
    have := hxy.ne_zero 1
    simpa [Matrix.cons_val_one, Matrix.head_cons] using this
  obtain ⟨u, hu_eq, hu_pos, hu_nz⟩ : ∃ u : X, (u = x0 ∨ u = -x0) ∧ 0 ≤ u ∧ u ≠ 0 := by
    rcases hcon' x0 with hp | hp
    · exact ⟨x0, Or.inl rfl, hp, hx0⟩
    · exact ⟨-x0, Or.inr rfl, neg_nonneg.mpr hp, neg_ne_zero.mpr hx0⟩
  obtain ⟨v, hv_eq, hv_pos, _⟩ : ∃ v : X, (v = y0 ∨ v = -y0) ∧ 0 ≤ v ∧ v ≠ 0 := by
    rcases hcon' y0 with hp | hp
    · exact ⟨y0, Or.inl rfl, hp, hy0⟩
    · exact ⟨-y0, Or.inr rfl, neg_nonneg.mpr hp, neg_ne_zero.mpr hy0⟩
  obtain ⟨r, hr⟩ := exists_real_eq_smul_of_linear_comparable hcon' hu_pos hu_nz hv_pos
  have hxy_dep : ∃ s : ℝ, y0 = s • x0 := by
    obtain (hu1 : u = x0) | (hu1 : u = -x0) := hu_eq
    · obtain (hv1 : v = y0) | (hv1 : v = -y0) := hv_eq
      · rw [hu1, hv1] at hr; exact ⟨r, hr⟩
      · rw [hu1, hv1] at hr
        refine ⟨-r, ?_⟩
        have h1 : y0 = -(r • x0) := by rw [← hr, neg_neg]
        rw [h1, neg_smul]
    · obtain (hv1 : v = y0) | (hv1 : v = -y0) := hv_eq
      · rw [hu1, hv1] at hr
        refine ⟨-r, ?_⟩
        rw [hr, smul_neg, ← neg_smul]
      · rw [hu1, hv1] at hr
        refine ⟨r, ?_⟩
        rw [smul_neg] at hr
        rw [← neg_neg y0, hr, neg_neg]
  obtain ⟨s, hs⟩ := hxy_dep
  let g : Fin 2 → ℝ := ![s, -1]
  have key : ∑ i : Fin 2, g i • ![x0, y0] i = 0 := by
    change ∑ i : Fin 2, (![s, -1] : Fin 2 → ℝ) i • ![x0, y0] i = 0
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hs, neg_one_smul]
    abel
  have h_false : g 1 = 0 := Fintype.linearIndependent_iff.mp hxy g key 1
  simp [g] at h_false

end Archimedean

end VectorLattice
