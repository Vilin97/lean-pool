/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Kempe

/-!
# Vizing fans

A *fan* at a vertex `x` starting at an uncoloured edge `x y` is a sequence of distinct
neighbours `f 0 = y, f 1, …, f n` of `x` such that the colour of `x (f (i+1))` is free at
`f i`.  Rotating a fan whose last vertex misses a colour that is also missing at `x` colours
the edge `x y`.
-/

public section

open SimpleGraph Finset

namespace LeanPool.Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}

/-- `f 0, …, f n` is a fan at `x` for the uncoloured edge `x y`. -/
structure IsFan (c : PEC G C) (x y : V) (n : ℕ) (f : ℕ → V) : Prop where
  start : f 0 = y
  uncoloured : c.col x y = none
  adj : ∀ i ≤ n, G.Adj x (f i)
  inj : ∀ i ≤ n, ∀ j ≤ n, f i = f j → i = j
  step : ∀ i < n, ∃ γ, c.col x (f (i + 1)) = some γ ∧ c.IsFree (f i) γ

omit [DecidableEq V] [DecidableEq C] in
/-- A fan has at most `Fintype.card V` vertices. -/
lemma IsFan.length_le {c : PEC G C} {x y : V} {n : ℕ} {f : ℕ → V} (h : c.IsFan x y n f) :
    n ≤ Fintype.card V := by
  classical
  have hcard : (Finset.range (n + 1)).card ≤ (Finset.univ : Finset V).card := by
    refine Finset.card_le_card_of_injOn f (fun i _ => Finset.mem_univ _) ?_
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact h.inj i (by omega) j (by omega) hij
  simp only [Finset.card_range, Finset.card_univ] at hcard
  omega

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
/-- Rotating a fan: if some colour `b` is free both at `x` and at the last vertex of the fan,
then the uncoloured edge `x y` can be coloured (after recolouring the fan edges). -/
lemma fan_rotate (x y : V) (f : ℕ → V) : ∀ (n : ℕ) (c : PEC G C) (b : C), c.IsFan x y n f →
    c.IsFree x b → c.IsFree (f n) b → ∃ c' : PEC G C, Extends c c' ∧ c'.col x y ≠ none := by
  classical
  intro n
  induction n with
  | zero =>
    intro c b hf hbx hbn
    have hy : y = f 0 := hf.start.symm
    subst hy
    refine ⟨c.setEdge b (hf.adj 0 le_rfl) hbx hbn, c.extends_setEdge b (hf.adj 0 le_rfl) hbx hbn,
      ?_⟩
    rw [setEdge_col, updFun_left]
    exact Option.some_ne_none _
  | succ n ih =>
    intro c b hf hbx hbn
    obtain ⟨γ, hγ, hγfree⟩ := hf.step n (Nat.lt_succ_self n)
    have hadj : G.Adj x (f (n + 1)) := hf.adj (n + 1) le_rfl
    have hnex : ∀ i, i ≤ n + 1 → f i ≠ x := fun i hi => (hf.adj i hi).ne'
    have hnelast : ∀ i, i ≤ n → f i ≠ f (n + 1) := by
      intro i hi hcon
      have := hf.inj i (by omega) (n + 1) le_rfl hcon
      omega
    set c1 := c.setEdge b hadj hbx hbn with hc1
    have hcolne : ∀ w u, w ≠ x → w ≠ f (n + 1) → c1.col w u = c.col w u := fun w u hw hw' =>
      c.setEdge_col_of_ne_left b hadj hbx hbn hw hw' u
    have hcolx : ∀ u, u ≠ f (n + 1) → c1.col x u = c.col x u := by
      intro u hu
      rw [hc1, setEdge_col]
      exact updFun_of_ne _ (by
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hu h
        · exact hadj.ne h)
    have hbγ : b ≠ γ := by
      rintro rfl
      exact hbx _ hγ
    -- the fan of length `n` survives the recolouring of the last fan edge
    have hfan1 : c1.IsFan x y n f := by
      refine ⟨hf.start, ?_, fun i hi => hf.adj i (by omega),
        fun i hi j hj hij => hf.inj i (by omega) j (by omega) hij, ?_⟩
      · rw [← hf.start, hcolx (f 0) (hnelast 0 (by omega))]
        rw [hf.start]
        exact hf.uncoloured
      · intro i hi
        obtain ⟨δ, hδ, hδfree⟩ := hf.step i (by omega)
        refine ⟨δ, ?_, ?_⟩
        · rw [hcolx (f (i + 1)) (hnelast (i + 1) (by omega))]
          exact hδ
        · rw [hc1, c.isFree_setEdge_of_ne b hadj hbx hbn (hnex i (by omega))
            (hnelast i (by omega)) δ]
          exact hδfree
    have hγx : c1.IsFree x γ := by
      intro u hu
      by_cases hcase : u = f (n + 1)
      · subst hcase
        rw [hc1, setEdge_col, updFun_left] at hu
        exact hbγ (Option.some_injective _ hu)
      · rw [hcolx u hcase] at hu
        exact hcase (c.col_proper hu hγ)
    have hγn : c1.IsFree (f n) γ := by
      rw [hc1, c.isFree_setEdge_of_ne b hadj hbx hbn (hnex n (by omega))
        (hnelast n le_rfl) γ]
      exact hγfree
    obtain ⟨c', hext, hcol'⟩ := ih c1 γ hfan1 hγx hγn
    exact ⟨c', (c.extends_setEdge b hadj hbx hbn).trans hext, hcol'⟩

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
/-- Existence of a maximal fan. -/
lemma exists_maximal_fan [Finite V] (c : PEC G C) {x y : V}
    (hadj : G.Adj x y) (hnone : c.col x y = none) :
    ∃ (n : ℕ) (f : ℕ → V), c.IsFan x y n f ∧
      ∀ (m : ℕ) (g : ℕ → V), c.IsFan x y m g → m ≤ n := by
  classical
  let : Fintype V := Fintype.ofFinite V
  set P : ℕ → Prop := fun n => ∃ g : ℕ → V, c.IsFan x y n g with hP
  have hP0 : P 0 := by
    refine ⟨fun _ => y, rfl, hnone, fun i _ => hadj, ?_, ?_⟩
    · intro i hi j hj _
      omega
    · intro i hi
      omega
  set N := Fintype.card V with hN
  have hspec : P (Nat.findGreatest P N) := Nat.findGreatest_spec (Nat.zero_le _) hP0
  refine ⟨Nat.findGreatest P N, hspec.choose, hspec.choose_spec, ?_⟩
  intro m g hg
  by_contra hcon
  push Not at hcon
  exact Nat.findGreatest_is_greatest hcon hg.length_le ⟨g, hg⟩

end PEC

end LeanPool.Vizing
