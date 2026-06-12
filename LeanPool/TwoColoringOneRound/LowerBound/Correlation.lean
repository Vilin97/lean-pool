/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.LowerBound.Defs
import Mathlib.Data.Finite.Perm

/-!
# LeanPool.TwoColoringOneRound.LowerBound.Correlation
-/

namespace Distributed2Coloring.LowerBound

open scoped BigOperators

namespace Correlation

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev G (n : Nat) := Equiv.Perm (Sym n)

noncomputable instance (n : Nat) : Fintype (G n) := Fintype.ofFinite (G n)

instance (n : Nat) : MulAction (G n) (Vertex n) where
  smul σ v :=
    ⟨fun i => σ (v.1 i), by
      intro i j hij
      exact v.2 (σ.injective hij)⟩
  one_smul v := by
    apply Subtype.ext
    funext i
    rfl
  mul_smul σ τ v := by
    apply Subtype.ext
    funext i
    rfl

@[simp] lemma vertex_smul_apply {n : Nat} (σ : G n) (v : Vertex n) (i : Fin 3) :
    (σ • v).1 i = σ (v.1 i) := rfl

instance (n : Nat) : MulAction (G n) (Edge n) where
  smul σ e :=
    ⟨fun i => σ (e.1 i), by
      intro i j hij
      exact e.2 (σ.injective hij)⟩
  one_smul e := by
    apply Subtype.ext
    funext i
    rfl
  mul_smul σ τ e := by
    apply Subtype.ext
    funext i
    rfl

@[simp] lemma edge_smul_apply {n : Nat} (σ : G n) (e : Edge n) (i : Fin 4) :
    (σ • e).1 i = σ (e.1 i) := rfl

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def spin (b : Bool) : Q :=
  if b then (-1 : Q) else (1 : Q)

lemma spin_mul_self (b : Bool) : spin b * spin b = 1 := by
  cases b <;> simp [spin]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def corr {n : Nat} (f : Coloring n) (u v : Vertex n) : Q :=
  spin (f u) * spin (f v)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def corrAvg {n : Nat} (f : Coloring n) (u v : Vertex n) : Q :=
  (∑ σ : G n, corr f (σ • u) (σ • v)) / (Fintype.card (G n) : Q)

lemma cardG_pos (n : Nat) : 0 < (Fintype.card (G n) : Q) := by
  have : 0 < Fintype.card (G n) := Fintype.card_pos
  exact_mod_cast this

lemma corrAvg_smul {n : Nat} (f : Coloring n) (τ : G n) (u v : Vertex n) :
    corrAvg f (τ • u) (τ • v) = corrAvg f u v := by
  classical
  -- Change variables `σ ↦ σ * τ` in the group average.
  unfold corrAvg corr
  set g : G n → Q := fun σ => spin (f (σ • u)) * spin (f (σ • v))
  have hsum : (∑ σ : G n, g (σ * τ)) = ∑ σ : G n, g σ := by
    simpa using (Function.Bijective.sum_comp (Group.mulRight_bijective τ) g)
  -- `g (σ * τ)` matches the LHS summand by `mul_smul`.
  have hsum' :
      (∑ σ : G n, spin (f (σ • (τ • u))) * spin (f (σ • (τ • v)))) =
        ∑ σ : G n, spin (f (σ • u)) * spin (f (σ • v)) := by
    simpa [g, mul_smul] using hsum
  -- Rewrite the LHS numerator using `hsum'`.
  simp [hsum', g]

lemma corr_le_one (b0 b1 : Bool) : spin b0 * spin b1 ≤ (1 : Q) := by
  cases b0 <;> cases b1 <;> simp [spin]

lemma neg_one_le_corr (b0 b1 : Bool) : (-1 : Q) ≤ spin b0 * spin b1 := by
  cases b0 <;> cases b1 <;> simp [spin]

lemma corrAvg_le_one {n : Nat} (f : Coloring n) (u v : Vertex n) : corrAvg f u v ≤ 1 := by
  classical
  unfold corrAvg corr
  set s : Finset (G n) := Finset.univ
  have hterm : ∀ σ ∈ s, spin (f (σ • u)) * spin (f (σ • v)) ≤ (1 : Q) := by
    intro σ _hσ
    exact corr_le_one (f (σ • u)) (f (σ • v))
  have hsum : s.sum (fun σ : G n => spin (f (σ • u)) * spin (f (σ • v))) ≤ s.card • (1 : Q) :=
    Finset.sum_le_card_nsmul s _ _ hterm
  have hsum' :
      s.sum (fun σ : G n => spin (f (σ • u)) * spin (f (σ • v))) ≤
        (Fintype.card (G n) : Q) := by
    have hcard : (s.card : Q) = (Fintype.card (G n) : Q) := by
      have : s.card = Fintype.card (G n) := by
        simp [s]
      exact_mod_cast this
    have : s.sum (fun σ : G n => spin (f (σ • u)) * spin (f (σ • v))) ≤ (s.card : Q) := by
      simpa [nsmul_one] using hsum
    simpa [hcard] using this
  exact (div_le_one (cardG_pos n)).2 hsum'

lemma neg_one_le_corrAvg {n : Nat} (f : Coloring n) (u v : Vertex n) :
    (-1 : Q) ≤ corrAvg f u v := by
  classical
  unfold corrAvg corr
  set s : Finset (G n) := Finset.univ
  have hterm : ∀ σ ∈ s, (-1 : Q) ≤ spin (f (σ • u)) * spin (f (σ • v)) := by
    intro σ _hσ
    exact neg_one_le_corr (f (σ • u)) (f (σ • v))
  have hsum : s.card • (-1 : Q) ≤ s.sum (fun σ : G n => spin (f (σ • u)) * spin (f (σ • v))) :=
    Finset.card_nsmul_le_sum s _ _ hterm
  have hpos : 0 < (Fintype.card (G n) : Q) := cardG_pos n
  have :
      (-1 : Q) * (Fintype.card (G n) : Q) ≤
        s.sum (fun σ : G n => spin (f (σ • u)) * spin (f (σ • v))) := by
    have hcard : (s.card : Q) = (Fintype.card (G n) : Q) := by
      have : s.card = Fintype.card (G n) := by
        simp [s]
      exact_mod_cast this
    have :
        (-1 : Q) * (s.card : Q) ≤
          s.sum (fun σ : G n => spin (f (σ • u)) * spin (f (σ • v))) := by
      simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsum
    simpa [hcard] using this
  exact (_root_.le_div_iff₀ hpos).2 this

lemma triangle_inequalities (b0 b1 b2 : Bool) :
    (-(spin b0 * spin b1 + spin b0 * spin b2 + spin b1 * spin b2) ≤ (1 : Q)) ∧
      (spin b0 * spin b1 + spin b0 * spin b2 - spin b1 * spin b2 ≤ 1) ∧
        (spin b0 * spin b1 - spin b0 * spin b2 + spin b1 * spin b2 ≤ 1) ∧
          (-spin b0 * spin b1 + spin b0 * spin b2 + spin b1 * spin b2 ≤ 1) := by
  cases b0 <;> cases b1 <;> cases b2 <;> simp [spin] <;> nlinarith

lemma corrAvg_comm {n : Nat} (f : Coloring n) (u v : Vertex n) :
    corrAvg f u v = corrAvg f v u := by
  classical
  unfold corrAvg corr
  simp [mul_comm]

-- The `simp` steps in `corrAvg_triangle` (especially after `field_simp`) can be heartbeat-heavy;
-- we raise the limit locally to keep the proof robust across Lean/Mathlib versions.
lemma corrAvg_triangle {n : Nat} (f : Coloring n) (u v w : Vertex n) :
    (-(corrAvg f u v + corrAvg f u w + corrAvg f v w) ≤ (1 : Q)) ∧
      (corrAvg f u v + corrAvg f u w - corrAvg f v w ≤ 1) ∧
        (corrAvg f u v - corrAvg f u w + corrAvg f v w ≤ 1) ∧
          (-corrAvg f u v + corrAvg f u w + corrAvg f v w ≤ 1) := by
  classical
  have hpos : 0 < (Fintype.card (G n) : Q) := cardG_pos n
  have hne : (Fintype.card (G n) : Q) ≠ 0 := ne_of_gt hpos
  have avg_le_one (g : G n → Q) (hg : ∀ σ : G n, g σ ≤ (1 : Q)) :
      (∑ σ : G n, g σ) / (Fintype.card (G n) : Q) ≤ 1 := by
    have hsum : (∑ σ : G n, g σ) ≤ ∑ _σ : G n, (1 : Q) := by
      classical
      simpa using
        (Finset.sum_le_sum (s := (Finset.univ : Finset (G n))) fun σ _ => hg σ)
    have hdiv :
        (∑ σ : G n, g σ) / (Fintype.card (G n) : Q)
          ≤ (∑ _σ : G n, (1 : Q)) / (Fintype.card (G n) : Q) :=
      div_le_div_of_nonneg_right hsum (le_of_lt hpos)
    simpa [Finset.sum_const, nsmul_eq_mul, hne] using hdiv
  have avg_le_one_of_eq (g : G n → Q) (hg : ∀ σ : G n, g σ ≤ (1 : Q)) (rhs : Q)
      (hEq : (∑ σ : G n, g σ) / (Fintype.card (G n) : Q) = rhs) : rhs ≤ 1 := by
    have h := avg_le_one (g := g) hg
    simpa [hEq] using h
  have hterm (σ : G n) :
      (-(corr f (σ • u) (σ • v) + corr f (σ • u) (σ • w) + corr f (σ • v) (σ • w) : Q) ≤ 1) ∧
        (corr f (σ • u) (σ • v) + corr f (σ • u) (σ • w) - corr f (σ • v) (σ • w) ≤ 1) ∧
          (corr f (σ • u) (σ • v) - corr f (σ • u) (σ • w) + corr f (σ • v) (σ • w) ≤ 1) ∧
            (-corr f (σ • u) (σ • v) + corr f (σ • u) (σ • w) + corr f (σ • v) (σ • w) ≤ 1) := by
    simpa [corr, sub_eq_add_neg] using
      (triangle_inequalities (f (σ • u)) (f (σ • v)) (f (σ • w)))
  have h0 : (-(corrAvg f u v + corrAvg f u w + corrAvg f v w) ≤ (1 : Q)) := by
    have hrew :
        (∑ σ : G n,
            -(corr f (σ • u) (σ • v) + corr f (σ • u) (σ • w) + corr f (σ • v) (σ • w))) /
            (Fintype.card (G n) : Q)
          = -(corrAvg f u v + corrAvg f u w + corrAvg f v w) := by
      unfold corrAvg
      field_simp [hne]
      simp [Finset.sum_add_distrib, Finset.sum_neg_distrib, add_assoc]
    exact
      avg_le_one_of_eq
        (g := fun σ =>
          -(corr f (σ • u) (σ • v) + corr f (σ • u) (σ • w) + corr f (σ • v) (σ • w)))
        (fun σ => (hterm σ).1) _ hrew
  have h1 : corrAvg f u v + corrAvg f u w - corrAvg f v w ≤ 1 := by
    have hrew :
        (∑ σ : G n,
            (corr f (σ • u) (σ • v) + corr f (σ • u) (σ • w) - corr f (σ • v) (σ • w))) /
            (Fintype.card (G n) : Q)
          = corrAvg f u v + corrAvg f u w - corrAvg f v w := by
      unfold corrAvg
      field_simp [hne]
      simp [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg, add_assoc]
    exact
      avg_le_one_of_eq
        (g := fun σ =>
          corr f (σ • u) (σ • v) + corr f (σ • u) (σ • w) - corr f (σ • v) (σ • w))
        (fun σ => (hterm σ).2.1) _ hrew
  have h2 : corrAvg f u v - corrAvg f u w + corrAvg f v w ≤ 1 := by
    have hrew :
        (∑ σ : G n,
            (corr f (σ • u) (σ • v) - corr f (σ • u) (σ • w) + corr f (σ • v) (σ • w))) /
            (Fintype.card (G n) : Q)
          = corrAvg f u v - corrAvg f u w + corrAvg f v w := by
      unfold corrAvg
      field_simp [hne]
      simp [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg, add_assoc]
    exact
      avg_le_one_of_eq
        (g := fun σ =>
          corr f (σ • u) (σ • v) - corr f (σ • u) (σ • w) + corr f (σ • v) (σ • w))
        (fun σ => (hterm σ).2.2.1) _ hrew
  have h3 : -corrAvg f u v + corrAvg f u w + corrAvg f v w ≤ 1 := by
    have hrew :
        (∑ σ : G n,
            (-corr f (σ • u) (σ • v) + corr f (σ • u) (σ • w) + corr f (σ • v) (σ • w))) /
            (Fintype.card (G n) : Q)
          = -corrAvg f u v + corrAvg f u w + corrAvg f v w := by
      unfold corrAvg
      field_simp [hne]
      simp [Finset.sum_add_distrib, Finset.sum_neg_distrib, add_assoc]
    exact
      avg_le_one_of_eq
        (g := fun σ =>
          -corr f (σ • u) (σ • v) + corr f (σ • u) (σ • w) + corr f (σ • v) (σ • w))
        (fun σ => (hterm σ).2.2.2) _ hrew
  exact ⟨h0, ⟨h1, ⟨h2, h3⟩⟩⟩

end Correlation

end Distributed2Coloring.LowerBound
