/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Normed


/-!
# Disjointness in vector lattices

Two elements `x`, `y` of a lattice-ordered group are **disjoint** when
`|x| ⊓ |y| = 0`, written `IsVLDisjoint x y`. This file collects the basic
theory: the symmetry and zero rules, the Birkhoff identity
`|x + y| = |x| + |y|`, the uniqueness of the positive/negative decomposition,
compatibility with scalar multiplication, monotonicity under absolute value,
closure under finite suprema and sums, and the finite-family identity
`|∑ i, α i • x i| = ∑ i, |α i| • |x i|` for pairwise-disjoint families. From
the last, a pairwise-disjoint family of non-zero vectors is linearly
independent over `ℝ`. Finally, in a normed vector lattice, a limit of a
pairwise-disjoint sequence is forced to be zero.
-/

@[expose] public section

open scoped Topology
open Filter Finset

section LatticeOrdered

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-! ### Definition and elementary lemmas -/

/-- Two elements of a lattice-ordered group are **disjoint** when
`|x| ⊓ |y| = 0`. -/
def IsVLDisjoint (x y : X) : Prop := |x| ⊓ |y| = 0

omit [IsOrderedAddMonoid X] in
theorem isVLDisjoint_comm {x y : X} :
    IsVLDisjoint x y ↔ IsVLDisjoint y x := by
  unfold IsVLDisjoint; rw [inf_comm]

/-- Zero is disjoint from every element. -/
theorem isVLDisjoint_zero_left (x : X) : IsVLDisjoint 0 x := by
  unfold IsVLDisjoint; simp [abs_zero]

/-- Every element is disjoint from zero. -/
theorem isVLDisjoint_zero_right (x : X) : IsVLDisjoint x 0 :=
  isVLDisjoint_comm.mpr (isVLDisjoint_zero_left x)

/-- Disjoint positive elements satisfy `x ⊓ y = 0`. -/
theorem inf_eq_zero_of_isVLDisjoint {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : IsVLDisjoint x y) : x ⊓ y = 0 := by
  unfold IsVLDisjoint at h; rwa [abs_of_nonneg hx, abs_of_nonneg hy] at h

/-- If `x ⊓ y = 0` then `x` and `y` are disjoint. -/
theorem isVLDisjoint_of_inf_eq_zero {x y : X}
    (h : x ⊓ y = 0) : IsVLDisjoint x y := by
  have hx : 0 ≤ x := h ▸ inf_le_left
  have hy : 0 ≤ y := h ▸ inf_le_right
  unfold IsVLDisjoint; rwa [abs_of_nonneg hx, abs_of_nonneg hy]

/-- Disjoint decomposition is unique: if `x = u₁ - v₁ = u₂ - v₂` with
`u₁ ⊥ v₁` and `u₂ ⊥ v₂` (all non-negative), then `u₁ = u₂` and
`v₁ = v₂`. -/
theorem isVLDisjoint_decomposition_unique {u₁ v₁ u₂ v₂ : X}
    (hu₁ : 0 ≤ u₁) (hv₁ : 0 ≤ v₁) (hu₂ : 0 ≤ u₂) (hv₂ : 0 ≤ v₂)
    (hd₁ : IsVLDisjoint u₁ v₁) (hd₂ : IsVLDisjoint u₂ v₂)
    (h : u₁ - v₁ = u₂ - v₂) : u₁ = u₂ ∧ v₁ = v₂ := by
  have h1 := inf_eq_zero_of_isVLDisjoint hu₁ hv₁ hd₁
  have h2 := inf_eq_zero_of_isVLDisjoint hu₂ hv₂ hd₂
  have eq1 : u₁ = (u₁ - v₁)⁺ :=
    uniqueness_posPart (u₁ - v₁) rfl h1
  have eq2 : u₂ = (u₂ - v₂)⁺ :=
    uniqueness_posPart (u₂ - v₂) rfl h2
  have hu : u₁ = u₂ := by rw [eq1, h, ← eq2]
  refine ⟨hu, ?_⟩
  have := h; rw [hu, sub_eq_add_neg, sub_eq_add_neg] at this
  exact neg_injective (add_left_cancel this)

omit [IsOrderedAddMonoid X] in
private theorem inf_eq_zero_of_le_disjoint {a b c d : X}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d)
    (hcd : c ⊓ d = 0) : a ⊓ b = 0 :=
  le_antisymm (hcd ▸ inf_le_inf hac hbd) (le_inf ha hb)

/-- If `x ⊥ y` then `|x + y| = |x| + |y|` (Birkhoff identity). -/
theorem abs_add_of_isVLDisjoint {x y : X} (h : IsVLDisjoint x y) :
    |x + y| = |x| + |y| := by
  have hd : |x| ⊓ |y| = 0 := h
  have hxp_yp : x⁺ ⊓ y⁺ = 0 := inf_eq_zero_of_le_disjoint
    (posPart_nonneg x) (posPart_nonneg y)
    (sup_le (le_abs_self x) (abs_nonneg x))
    (sup_le (le_abs_self y) (abs_nonneg y)) hd
  have hxp_yn : x⁺ ⊓ y⁻ = 0 := inf_eq_zero_of_le_disjoint
    (posPart_nonneg x) (negPart_nonneg y)
    (sup_le (le_abs_self x) (abs_nonneg x))
    (sup_le (neg_le_abs y) (abs_nonneg y)) hd
  have hxn_yp : x⁻ ⊓ y⁺ = 0 := inf_eq_zero_of_le_disjoint
    (negPart_nonneg x) (posPart_nonneg y)
    (sup_le (neg_le_abs x) (abs_nonneg x))
    (sup_le (le_abs_self y) (abs_nonneg y)) hd
  have hxn_yn : x⁻ ⊓ y⁻ = 0 := inf_eq_zero_of_le_disjoint
    (negPart_nonneg x) (negPart_nonneg y)
    (sup_le (neg_le_abs x) (abs_nonneg x))
    (sup_le (neg_le_abs y) (abs_nonneg y)) hd
  have hxn_xp : x⁻ ⊓ x⁺ = 0 := by
    rw [inf_comm]; exact posPart_inf_negPart_eq_zero x
  have hyn_yp : y⁻ ⊓ y⁺ = 0 := by
    rw [inf_comm]; exact posPart_inf_negPart_eq_zero y
  have term1 : (x⁺ + y⁺) ⊓ x⁻ = 0 := by
    apply le_antisymm _ (le_inf (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (negPart_nonneg x))
    rw [inf_comm]
    calc x⁻ ⊓ (x⁺ + y⁺)
        ≤ x⁻ ⊓ x⁺ + x⁻ ⊓ y⁺ := inf_le_inf_add_inf_of_nonneg x⁻ x⁺ y⁺
            (negPart_nonneg x) (posPart_nonneg x) (posPart_nonneg y)
      _ = 0 := by rw [hxn_xp, hxn_yp, add_zero]
  have term2 : (x⁺ + y⁺) ⊓ y⁻ = 0 := by
    apply le_antisymm _ (le_inf (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (negPart_nonneg y))
    rw [inf_comm]
    calc y⁻ ⊓ (x⁺ + y⁺)
        ≤ y⁻ ⊓ x⁺ + y⁻ ⊓ y⁺ := inf_le_inf_add_inf_of_nonneg y⁻ x⁺ y⁺
            (negPart_nonneg y) (posPart_nonneg x) (posPart_nonneg y)
      _ = 0 := by rw [inf_comm y⁻ x⁺, hxp_yn, hyn_yp, add_zero]
  have sum_disj : (x⁺ + y⁺) ⊓ (x⁻ + y⁻) = 0 := by
    apply le_antisymm _ (le_inf (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (add_nonneg (negPart_nonneg x) (negPart_nonneg y)))
    calc (x⁺ + y⁺) ⊓ (x⁻ + y⁻)
        ≤ (x⁺ + y⁺) ⊓ x⁻ + (x⁺ + y⁺) ⊓ y⁻ :=
          inf_le_inf_add_inf_of_nonneg (x⁺ + y⁺) x⁻ y⁻
            (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
            (negPart_nonneg x) (negPart_nonneg y)
      _ = 0 := by rw [term1, term2, add_zero]
  have hdec : x + y = (x⁺ + y⁺) - (x⁻ + y⁻) := by
    calc x + y = (x⁺ - x⁻) + (y⁺ - y⁻) := by
          rw [posPart_sub_negPart, posPart_sub_negPart]
      _ = (x⁺ + y⁺) - (x⁻ + y⁻) := by abel
  have hup := uniqueness_posPart (x + y) hdec sum_disj
  have hun : (x + y)⁻ = x⁻ + y⁻ := by
    have h3 := posPart_sub_negPart (x + y)
    rw [← hup] at h3
    have h4 : x⁺ + y⁺ - (x + y)⁻ = x⁺ + y⁺ - (x⁻ + y⁻) := by
      rw [h3, hdec]
    exact sub_right_injective h4
  calc |x + y| = (x + y)⁺ + (x + y)⁻ := (posPart_add_negPart (x + y)).symm
    _ = (x⁺ + y⁺) + (x⁻ + y⁻) := by rw [← hup, hun]
    _ = (x⁺ + x⁻) + (y⁺ + y⁻) := by abel
    _ = |x| + |y| := by rw [posPart_add_negPart, posPart_add_negPart]

/-- If `x, y ≥ 0` and `x ⊥ y` then `|x ⊔ y| = |x| ⊔ |y|`. -/
theorem abs_sup_of_isVLDisjoint {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (_ : IsVLDisjoint x y) : |x ⊔ y| = |x| ⊔ |y| := by
  rw [abs_of_nonneg (le_sup_of_le_left hx), abs_of_nonneg hx, abs_of_nonneg hy]

/-- The positive and negative parts of an element are disjoint. -/
theorem isVLDisjoint_posPart_negPart (x : X) : IsVLDisjoint x⁺ x⁻ :=
  isVLDisjoint_of_inf_eq_zero (posPart_inf_negPart_eq_zero x)

/-- If `|z| ≤ |y|` and `x ⊥ y` then `x ⊥ z`. -/
theorem IsVLDisjoint.mono_right {x y z : X} (h : IsVLDisjoint x y)
    (hzy : |z| ≤ |y|) : IsVLDisjoint x z := by
  refine le_antisymm ?_ (le_inf (abs_nonneg _) (abs_nonneg _))
  calc |x| ⊓ |z| ≤ |x| ⊓ |y| := inf_le_inf_left _ hzy
    _ = 0 := h

/-- If `|z| ≤ |x|` and `x ⊥ y` then `z ⊥ y`. -/
theorem IsVLDisjoint.mono_left {x y z : X} (h : IsVLDisjoint x y)
    (hzx : |z| ≤ |x|) : IsVLDisjoint z y :=
  isVLDisjoint_comm.mp ((isVLDisjoint_comm.mp h).mono_right hzx)

/-! ### Sum of non-negative disjoint elements equals their supremum -/

/-- For non-negative disjoint elements, `x + y = x ⊔ y`. -/
theorem add_eq_sup_of_isVLDisjoint_of_nonneg {x y : X}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : IsVLDisjoint x y) : x + y = x ⊔ y := by
  have hinf : x ⊓ y = 0 := inf_eq_zero_of_isVLDisjoint hx hy h
  have := inf_add_sup x y
  rw [hinf, zero_add] at this
  exact this.symm

/-- If a non-negative element is written as a sum of two disjoint elements,
then both summands are non-negative. -/
theorem nonneg_and_nonneg_of_isVLDisjoint_add_eq_of_nonneg
    {x y z : X} (hx : 0 ≤ x) (hyz : IsVLDisjoint y z) (hadd : y + z = x) :
    0 ≤ y ∧ 0 ≤ z := by
  have hsub : |y| + |z| - (y + z) = 0 := by
    calc
      |y| + |z| - (y + z) = |y + z| - (y + z) := by
        rw [abs_add_of_isVLDisjoint hyz]
      _ = |x| - x := by rw [hadd]
      _ = 0 := by rw [abs_of_nonneg hx, sub_self]
  have hy0 : |y| - y = 0 := by
    have hle : |y| - y ≤ |y| + |z| - (y + z) := by
      calc
        |y| - y ≤ (|y| - y) + (|z| - z) :=
          le_add_of_nonneg_right (sub_nonneg.mpr (le_abs_self z))
        _ = |y| + |z| - (y + z) := by abel
    exact le_antisymm (by rwa [hsub] at hle) (sub_nonneg.mpr (le_abs_self y))
  have hz0 : |z| - z = 0 := by
    calc
      |z| - z = 0 + (|z| - z) := by rw [zero_add]
      _ = (|y| - y) + (|z| - z) := by rw [hy0]
      _ = |y| + |z| - (y + z) := by abel
      _ = 0 := hsub
  constructor
  · rw [← sub_eq_zero.mp hy0]
    exact abs_nonneg y
  · rw [← sub_eq_zero.mp hz0]
    exact abs_nonneg z

/-- If `x ⊥ y` then `|x| ⊔ |y| = |x| + |y|`. -/
theorem sup_abs_eq_add_abs_of_isVLDisjoint {x y : X}
    (h : IsVLDisjoint x y) : |x| ⊔ |y| = |x| + |y| := by
  have := inf_add_sup |x| |y|
  rw [show |x| ⊓ |y| = 0 from h, zero_add] at this
  exact this

/-- If `x ⊥ y` then `|x + y| = |x| ⊔ |y|`. -/
theorem abs_add_eq_sup_abs_of_isVLDisjoint {x y : X}
    (h : IsVLDisjoint x y) : |x + y| = |x| ⊔ |y| := by
  rw [abs_add_of_isVLDisjoint h, sup_abs_eq_add_abs_of_isVLDisjoint h]

/-! ### Disjointness with sups and sums on the right -/

/-- If `x ⊥ y` and `x ⊥ z` then `x ⊥ y ⊔ z`. -/
theorem IsVLDisjoint.sup_right {x y z : X}
    (hy : IsVLDisjoint x y) (hz : IsVLDisjoint x z) :
    IsVLDisjoint x (y ⊔ z) := by
  have habs : |y ⊔ z| ≤ |y| + |z| := by
    rw [abs]
    refine sup_le ?_ ?_
    · exact sup_le ((le_abs_self y).trans
        (le_add_of_nonneg_right (abs_nonneg _)))
        ((le_abs_self z).trans (le_add_of_nonneg_left (abs_nonneg _)))
    · rw [neg_sup]
      exact inf_le_left.trans ((neg_le_abs y).trans
        (le_add_of_nonneg_right (abs_nonneg _)))
  refine le_antisymm ?_ (le_inf (abs_nonneg _) (abs_nonneg _))
  calc |x| ⊓ |y ⊔ z| ≤ |x| ⊓ (|y| + |z|) := inf_le_inf_left _ habs
    _ ≤ |x| ⊓ |y| + |x| ⊓ |z| := inf_le_inf_add_inf_of_nonneg _ _ _
        (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    _ = 0 := by rw [hy, hz, add_zero]

/-- If `x ⊥ y` and `x ⊥ z` then `x ⊥ y + z`. -/
theorem IsVLDisjoint.add_right {x y z : X}
    (hy : IsVLDisjoint x y) (hz : IsVLDisjoint x z) :
    IsVLDisjoint x (y + z) := by
  refine le_antisymm ?_ (le_inf (abs_nonneg _) (abs_nonneg _))
  calc |x| ⊓ |y + z| ≤ |x| ⊓ (|y| + |z|) := inf_le_inf_left _ (abs_add_le y z)
    _ ≤ |x| ⊓ |y| + |x| ⊓ |z| := inf_le_inf_add_inf_of_nonneg _ _ _
        (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    _ = 0 := by rw [hy, hz, add_zero]

/-- If `x ⊥ z` and `y ⊥ z` then `x ⊔ y ⊥ z`. -/
theorem IsVLDisjoint.sup_left {x y z : X}
    (hx : IsVLDisjoint x z) (hy : IsVLDisjoint y z) :
    IsVLDisjoint (x ⊔ y) z :=
  isVLDisjoint_comm.mp
    (IsVLDisjoint.sup_right (isVLDisjoint_comm.mp hx) (isVLDisjoint_comm.mp hy))

/-- If `x ⊥ z` and `y ⊥ z` then `x + y ⊥ z`. -/
theorem IsVLDisjoint.add_left {x y z : X}
    (hx : IsVLDisjoint x z) (hy : IsVLDisjoint y z) :
    IsVLDisjoint (x + y) z :=
  isVLDisjoint_comm.mp
    (IsVLDisjoint.add_right (isVLDisjoint_comm.mp hx) (isVLDisjoint_comm.mp hy))

/-! ### Disjoint pieces of an infimum -/

/-- For any `x, y`, the elements `x - x ⊓ y` and `y - x ⊓ y` are non-negative
and disjoint. -/
theorem isVLDisjoint_sub_inf (x y : X) :
    IsVLDisjoint (x - x ⊓ y) (y - x ⊓ y) := by
  have h1 : x - x ⊓ y = (x - y)⁺ := sub_inf_eq_posPart x y
  have h2 : y - x ⊓ y = (x - y)⁻ := by
    rw [inf_comm, sub_inf_eq_posPart, negPart_def, neg_sub, posPart_def]
  rw [h1, h2]
  exact isVLDisjoint_posPart_negPart (x - y)

/-! ### Finite disjoint sums -/

private lemma isVLDisjoint_finset_sum {ι : Type*} {s : Finset ι} {x : X} {f : ι → X}
    (h : ∀ i ∈ s, IsVLDisjoint x (f i)) : IsVLDisjoint x (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isVLDisjoint_zero_right x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (h a (Finset.mem_insert_self a s)).add_right ?_
    exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma sum_eq_sup'_aux {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → X)
    (hnn : ∀ i ∈ s, 0 ≤ f i)
    (hdisj : (s : Set ι).Pairwise fun i j => IsVLDisjoint (f i) (f j)) :
    ∑ i ∈ s, f i = s.sup' hs f := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [Finset.sum_cons, Finset.sup'_cons hs f]
    have mem_cons_of : ∀ i ∈ s, i ∈ Finset.cons a s ha :=
      fun i hi => Finset.mem_cons.mpr (Or.inr hi)
    have hnn_s : ∀ i ∈ s, 0 ≤ f i := fun i hi => hnn i (mem_cons_of i hi)
    have hnn_a : 0 ≤ f a := hnn a (Finset.mem_cons.mpr (Or.inl rfl))
    have hdisj_s : (s : Set ι).Pairwise fun i j => IsVLDisjoint (f i) (f j) := by
      intro i hi j hj hij
      exact hdisj (mem_cons_of i hi) (mem_cons_of j hj) hij
    rw [← ih hnn_s hdisj_s]
    have hsum_nn : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hnn_s
    have hdisj_sum : IsVLDisjoint (f a) (∑ i ∈ s, f i) := by
      apply isVLDisjoint_finset_sum
      intro i hi
      have hne_ai : a ≠ i := fun h => ha (h ▸ hi)
      exact hdisj (Finset.mem_cons.mpr (Or.inl rfl)) (mem_cons_of i hi) hne_ai
    exact add_eq_sup_of_isVLDisjoint_of_nonneg hnn_a hsum_nn hdisj_sum

/-- For a pairwise-disjoint family of non-negative elements, the finite sum
equals the supremum. -/
theorem sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg {n : ℕ} {f : Fin n → X}
    (hne : 0 < n) (hnn : ∀ i, 0 ≤ f i)
    (hdisj : Pairwise fun i j => IsVLDisjoint (f i) (f j)) :
    ∑ i, f i = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr
      ⟨⟨0, hne⟩⟩) f := by
  apply sum_eq_sup'_aux
  · intro i _; exact hnn i
  · intro i _ j _ hij; exact hdisj hij

end LatticeOrdered

section VectorLattice

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-! ### Scalar multiples preserve disjointness -/

/-- Scaling a non-negative disjoint pair preserves disjointness. -/
private lemma disjoint_smul_nonneg {x y : X} (a : ℝ) (nonneg : 0 ≤ a)
    (h : x ⊓ y = 0) : (a • x) ⊓ y = 0 := by
  let aux (x y : X) (h : x ⊓ y = 0) (a : ℝ)
      (nonneg : 0 ≤ a) (hone : a ≤ 1) : (a • x) ⊓ y = 0 := by
    have xnonneg : 0 ≤ x := by rw [← h]; exact inf_le_left
    have ynonneg : 0 ≤ y := by rw [← h]; exact inf_le_right
    apply le_antisymm
    · calc
        a • x ⊓ y ≤ (1 : ℝ) • x ⊓ y := by
            apply inf_le_inf
            · exact smul_le_smul_of_nonneg_right hone xnonneg
            · exact le_refl y
          _ = 0 := by simp [h]
    · exact le_inf (smul_nonneg nonneg xnonneg) ynonneg
  have hbig (hone : ¬ a ≤ 1) : (a • x) ⊓ y = 0 := by
    push Not at hone
    suffices hsuf : x ⊓ (a⁻¹ • y) = 0 from by
      symm
      calc
        0 = a • ( x ⊓ (a⁻¹ • y) ):= by rw [hsuf, smul_zero]
        _ = (a • x ⊓ a • a⁻¹ • y) := nonneg_smul_inf x (a⁻¹ • y) a nonneg
        _ = (a • x) ⊓ y := by rw [smul_smul]; field_simp [hone]; simp
    rw [inf_comm]; rw [inf_comm] at h
    refine aux y x h a⁻¹ ?_ ?_
    · exact inv_nonneg.mpr nonneg
    · field_simp; exact le_of_lt hone
  by_cases hone : a ≤ 1
  · exact aux x y h a nonneg hone
  · exact hbig hone

/-- Scalar multiplication on the left preserves disjointness. -/
theorem IsVLDisjoint.smul_left {x y : X} (h : IsVLDisjoint x y) (a : ℝ) :
    IsVLDisjoint (a • x) y := by
  change |a • x| ⊓ |y| = 0
  rw [abs_smul']
  exact disjoint_smul_nonneg (|a| : ℝ) (abs_nonneg a) h

/-- Scalar multiplication on the right preserves disjointness. -/
theorem IsVLDisjoint.smul_right {x y : X} (h : IsVLDisjoint x y) (a : ℝ) :
    IsVLDisjoint x (a • y) :=
  isVLDisjoint_comm.mp ((isVLDisjoint_comm.mp h).smul_left a)

/-- Two non-zero disjoint vectors exist in any Archimedean vector lattice of
`ℝ`-rank greater than one. -/
theorem exists_pair_ne_zero_isVLDisjoint [IsVLArchimedean X]
    (h : 1 < Module.rank ℝ X) :
    ∃ u v : X, u ≠ 0 ∧ v ≠ 0 ∧ IsVLDisjoint u v := by
  obtain ⟨x, hxp, hxn⟩ := exists_not_nonneg_not_nonpos_of_one_lt_rank h
  refine ⟨x⁺, x⁻, ?_, ?_, isVLDisjoint_posPart_negPart x⟩
  · exact fun h => hxn (posPart_eq_zero.mp h)
  · exact fun h => hxp (negPart_eq_zero.mp h)

/-! ### Disjoint positive parts from scalar multiples -/

/-- For any `x, y` and `λ > 0`, the positive parts `(x - λ • y)⁺` and
`(y - λ⁻¹ • x)⁺` are disjoint. -/
theorem isVLDisjoint_posPart_sub_smul (x y : X) {lam : ℝ} (hlam : 0 < lam) :
    IsVLDisjoint (x - lam • y)⁺ (y - lam⁻¹ • x)⁺ := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hinv : (0 : ℝ) ≤ lam⁻¹ := le_of_lt (inv_pos.mpr hlam)
  have heq : (y - lam⁻¹ • x)⁺ = lam⁻¹ • (x - lam • y)⁻ := by
    rw [negPart_def, nonneg_smul_sup _ _ _ hinv, smul_zero, posPart_def,
        neg_sub, smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [heq]
  exact (isVLDisjoint_posPart_negPart (x - lam • y)).smul_right lam⁻¹

/-! ### Finite disjoint families with scalars -/

private lemma abs_sum_finset {ι : Type*} (s : Finset ι) (x : ι → X) (α : ι → ℝ)
    (hdisj : (s : Set ι).Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    |∑ i ∈ s, α i • x i| = ∑ i ∈ s, |α i| • |x i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdisj_s : (s : Set ι).Pairwise fun i j => IsVLDisjoint (x i) (x j) := by
      intro i hi j hj hij
      exact hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hdisj_head : IsVLDisjoint (α a • x a) (∑ i ∈ s, α i • x i) := by
      apply isVLDisjoint_finset_sum
      intro i hi
      have hne_ai : a ≠ i := fun h => ha (h ▸ hi)
      exact ((hdisj (Finset.mem_insert_self a s)
        (Finset.mem_insert_of_mem hi) hne_ai).smul_left (α a)).smul_right (α i)
    rw [abs_add_of_isVLDisjoint hdisj_head, abs_smul', ih hdisj_s]

/-- For a pairwise-disjoint family and arbitrary scalars,
`|∑ i, α i • x i| = ∑ i, |α i| • |x i|`. -/
theorem abs_sum_of_pairwise_isVLDisjoint {n : ℕ} {x : Fin n → X} {α : Fin n → ℝ}
    (hdisj : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    |∑ i, α i • x i| = ∑ i, |α i| • |x i| :=
  abs_sum_finset Finset.univ x α (fun _ _ _ _ hij => hdisj hij)

/-- For a pairwise-disjoint family of non-negative elements and non-negative
scalars, `∑ i, α i • x i = ⨆ i, α i • x i` (with the sup taken over a
non-empty index). -/
theorem sup_smul_eq_sum_of_pairwise_isVLDisjoint_of_nonneg {n : ℕ}
    {x : Fin n → X} {α : Fin n → ℝ} (hne : 0 < n)
    (hnn : ∀ i, 0 ≤ x i) (hα : ∀ i, 0 ≤ α i)
    (hdisj : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    ∑ i, α i • x i = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr
      ⟨⟨0, hne⟩⟩) (fun i => α i • x i) := by
  refine sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg hne
    (fun i => smul_nonneg (hα i) (hnn i)) ?_
  intro i j hij
  exact ((hdisj hij).smul_left (α i)).smul_right (α j)

/-- A pairwise-disjoint family of non-zero vectors is linearly independent
over `ℝ`. -/
theorem linearIndependent_of_pairwise_isVLDisjoint {n : ℕ} {x : Fin n → X}
    (hne : ∀ i, x i ≠ 0)
    (hdisj : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    LinearIndependent ℝ x := by
  rw [Fintype.linearIndependent_iff]
  intro α hsum i
  have habs : |∑ i, α i • x i| = ∑ i, |α i| • |x i| :=
    abs_sum_of_pairwise_isVLDisjoint hdisj
  rw [hsum, abs_zero] at habs
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ |α j| • |x j| :=
    fun j _ => smul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hzero : |α i| • |x i| = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp habs.symm i (Finset.mem_univ i)
  by_contra hα
  have habs_ne : |α i| ≠ 0 := fun h => hα (abs_eq_zero.mp h)
  have hxi : |x i| = 0 := by
    have h2 : |α i|⁻¹ • (|α i| • |x i|) = |α i|⁻¹ • (0 : X) := by rw [hzero]
    rwa [smul_smul, inv_mul_cancel₀ habs_ne, one_smul, smul_zero] at h2
  exact hne i ((abs_eq_zero_iff_zero (x i)).mp hxi)

/-! ### Pairwise disjoint families and maximality

A subset of a vector lattice is **pairwise disjoint** when distinct members
are vector-lattice disjoint, and **maximal** when it is not properly
contained in any strictly larger pairwise disjoint subset. Every vector
lattice admits a maximal disjoint family consisting of strictly positive
vectors, by Zorn's lemma. -/

/-- A subset of `X` is **pairwise disjoint** when it does not contain `0`
and distinct members are vector-lattice disjoint. -/
def IsDisjointSet (Λ : Set X) : Prop :=
  0 ∉ Λ ∧ ∀ ⦃a⦄, a ∈ Λ → ∀ ⦃b⦄, b ∈ Λ → a ≠ b → IsVLDisjoint a b

/-- A **maximal disjoint family** in `X` is a pairwise disjoint set that is
not properly contained in any strictly larger pairwise disjoint subset of
`X`. The order is by inclusion (not refinement). -/
def IsMaximalDisjoint (Λ : Set X) : Prop :=
  Maximal IsDisjointSet Λ

omit [VectorLattice X] in
/-- A pairwise disjoint family of strictly positive elements is maximal iff
the only element disjoint from every member of the family is `0`. -/
theorem isMaximalDisjoint_iff_forall_eq_zero {Λ : Set X}
    (_hpos : ∀ x ∈ Λ, 0 < x) (hdis : IsDisjointSet Λ) :
    IsMaximalDisjoint Λ ↔ ∀ x : X, (∀ a ∈ Λ, IsVLDisjoint x a) → x = 0 := by
  refine ⟨?_, ?_⟩
  · intro hmax x hx
    by_contra hxne
    have habs_ne : |x| ≠ 0 := fun h => hxne ((abs_eq_zero_iff_zero x).mp h)
    have habs_pos : 0 < |x| := lt_of_le_of_ne (abs_nonneg x) (Ne.symm habs_ne)
    have habs_disj : ∀ a ∈ Λ, IsVLDisjoint |x| a := fun a ha =>
      (hx a ha).mono_left (abs_of_nonneg (abs_nonneg x)).le
    set Λ' : Set X := insert |x| Λ with hΛ'_def
    have hΛ'_dis : IsDisjointSet Λ' := by
      refine ⟨?_, ?_⟩
      · rintro (h0 | h0)
        · exact habs_ne h0.symm
        · exact hdis.1 h0
      · intro a ha b hb hab
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · exact (hab rfl).elim
          · exact habs_disj b hb
        · rcases hb with rfl | hb
          · exact isVLDisjoint_comm.mp (habs_disj a ha)
          · exact hdis.2 ha hb hab
    have hsub : Λ ⊆ Λ' := Set.subset_insert _ _
    have hsub' : Λ' ⊆ Λ := hmax.2 hΛ'_dis hsub
    have hxinΛ : |x| ∈ Λ := hsub' (Set.mem_insert _ _)
    have hself : |x| ⊓ |(|x|)| = 0 := hx |x| hxinΛ
    rw [abs_of_nonneg (abs_nonneg x), inf_idem] at hself
    exact habs_ne hself
  · intro hyp
    refine ⟨hdis, ?_⟩
    intro Λ' hΛ' hsub y hy
    by_contra hyΛ
    have hyΛ : y ∉ Λ := hyΛ
    have hy_disj : ∀ a ∈ Λ, IsVLDisjoint y a := by
      intro a ha
      have hane : y ≠ a := fun h => hyΛ (h.symm ▸ ha)
      exact hΛ'.2 hy (hsub ha) hane
    have hy0 : y = 0 := hyp y hy_disj
    exact hΛ'.1 (hy0 ▸ hy)

/-- **Existence of a maximal disjoint family of positive vectors.** Every
vector lattice admits a maximal disjoint family whose elements are all
strictly positive. -/
theorem exists_isMaximalDisjoint_pos (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] :
    ∃ Λ : Set X, IsMaximalDisjoint Λ ∧ ∀ x ∈ Λ, 0 < x := by
  let 𝒞 : Set (Set X) := {S | IsDisjointSet S ∧ ∀ x ∈ S, 0 < x}
  have hZorn : ∀ c ⊆ 𝒞, IsChain (· ⊆ ·) c → ∃ ub ∈ 𝒞, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨⟨?_, ?_⟩, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro ⟨S, hS, h0⟩
      exact (hc hS).1.1 h0
    · intro a ha b hb hab
      obtain ⟨Sa, hSa, haSa⟩ := ha
      obtain ⟨Sb, hSb, hbSb⟩ := hb
      rcases hchain.total hSa hSb with hSab | hSab
      · exact (hc hSb).1.2 (hSab haSa) hbSb hab
      · exact (hc hSa).1.2 haSa (hSab hbSb) hab
    · rintro x ⟨S, hS, hxS⟩
      exact (hc hS).2 x hxS
  obtain ⟨Λ, hΛ⟩ := zorn_subset 𝒞 hZorn
  refine ⟨Λ, ⟨hΛ.prop.1, ?_⟩, hΛ.prop.2⟩
  intro Λ' hΛ' hsub y hy
  by_contra hyΛ
  have hyΛ : y ∉ Λ := hyΛ
  have hy_ne : y ≠ 0 := fun h => hΛ'.1 (h ▸ hy)
  have habsy_ne : |y| ≠ 0 := fun h => hy_ne ((abs_eq_zero_iff_zero y).mp h)
  have habsy_pos : 0 < |y| := lt_of_le_of_ne (abs_nonneg y) (Ne.symm habsy_ne)
  have hy_disj : ∀ a ∈ Λ, IsVLDisjoint y a := by
    intro a ha
    have hane : y ≠ a := fun h => hyΛ (h.symm ▸ ha)
    exact hΛ'.2 hy (hsub ha) hane
  set Λ'' : Set X := insert |y| Λ
  have hΛ''_in : Λ'' ∈ 𝒞 := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro (h0 | h0)
      · exact habsy_ne h0.symm
      · exact hΛ.prop.1.1 h0
    · intro a ha b hb hab
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact (hab rfl).elim
        · exact (hy_disj b hb).mono_left (abs_of_nonneg (abs_nonneg y)).le
      · rcases hb with rfl | hb
        · exact isVLDisjoint_comm.mp
            ((hy_disj a ha).mono_left (abs_of_nonneg (abs_nonneg y)).le)
        · exact hΛ.prop.1.2 ha hb hab
    · rintro x (rfl | hx)
      · exact habsy_pos
      · exact hΛ.prop.2 x hx
  have hsub'' : Λ ⊆ Λ'' := Set.subset_insert _ _
  have hsub''' : Λ'' ⊆ Λ := hΛ.2 hΛ''_in hsub''
  have habs_in : |y| ∈ Λ := hsub''' (Set.mem_insert _ _)
  by_cases hyabs : y = |y|
  · exact hyΛ (hyabs ▸ habs_in)
  · have hd : |y| ⊓ |(|y|)| = 0 := hΛ'.2 hy (hsub habs_in) hyabs
    rw [abs_of_nonneg (abs_nonneg y), inf_idem] at hd
    exact habsy_ne hd

end VectorLattice

/-! ### Disjoint sequences in normed vector lattices -/

/-- In a normed vector lattice, a limit of a pairwise-disjoint sequence is
zero. -/
theorem eq_zero_of_pairwise_isVLDisjoint_tendsto {Y : Type*}
    [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] {u : ℕ → Y} {x : Y}
    (hdisj : Pairwise fun i j => IsVLDisjoint (u i) (u j))
    (hlim : Tendsto u atTop (𝓝 x)) : x = 0 := by
  have habs_bound : ∀ n m, n ≠ m → |u n| ≤ |u n - u m| := by
    intro n m hnm
    have hdnm : IsVLDisjoint (u n) (-u m) := by
      change |u n| ⊓ |-u m| = 0
      rw [abs_neg]; exact hdisj hnm
    rw [sub_eq_add_neg, abs_add_of_isVLDisjoint hdnm, abs_neg]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hnorm_bound : ∀ n m, n ≠ m → ‖u n‖ ≤ ‖u n - u m‖ :=
    fun n m hnm => norm_le_norm_of_abs_le_abs (habs_bound n m hnm)
  have hnorm_limit : ∀ n, ‖u n‖ ≤ ‖u n - x‖ := by
    intro n
    have hrhs : Tendsto (fun m => ‖u n - u m‖) atTop (𝓝 ‖u n - x‖) :=
      (continuous_norm.tendsto _).comp (hlim.const_sub _)
    refine ge_of_tendsto hrhs ?_
    filter_upwards [eventually_ne_atTop n] with m hm
    exact hnorm_bound n m hm.symm
  have hlhs_tendsto : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖) :=
    (continuous_norm.tendsto _).comp hlim
  have hrhs_zero : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => u n - x) atTop (𝓝 0) := by
      simpa using hlim.sub_const x
    simpa only [Function.comp_def, norm_zero] using (continuous_norm.tendsto (0 : Y)).comp h1
  have hxnn : ‖x‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' hlhs_tendsto hrhs_zero hnorm_limit
  exact norm_le_zero_iff.mp hxnn
