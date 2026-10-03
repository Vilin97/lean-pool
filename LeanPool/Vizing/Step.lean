/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Fan

/-!
# The Vizing extension step

Given a partial proper edge colouring with `Δ + 1` colours and an uncoloured edge `x y`, one can
recolour so that `x y` becomes coloured and no edge loses its colour.  This is the heart of
Vizing's theorem: a maximal fan at `x` is rotated, after a Kempe chain interchange if needed.
-/

public section

open SimpleGraph Finset

namespace LeanPool.Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] [Fintype C] in
/-- A fan survives a Kempe interchange of `a` and `b` (where `a` is free at `x`) up to the first
index at which the fan edge is coloured `b` and the interchange separates `f i` from `x`. -/
lemma isFan_kempeSwap (c : PEC G C) {x y : V} {n : ℕ} {f : ℕ → V} (hfan : c.IsFan x y n f)
    {a b : C} (ha : c.IsFree x a) (w : V) {m : ℕ} (hm : m ≤ n)
    (hbreak : ∀ i < m, c.col x (f (i + 1)) = some b →
      ((c.kempeGraph a b).Reachable w (f i) ↔ (c.kempeGraph a b).Reachable w x)) :
    (c.kempeSwap a b w).IsFan x y m f := by
  classical
  refine ⟨hfan.start, ?_, fun i hi => hfan.adj i (hi.trans hm),
    fun i hi j hj hij => hfan.inj i (hi.trans hm) j (hj.trans hm) hij, ?_⟩
  · by_cases hxw : (c.kempeGraph a b).Reachable w x
    · rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hxw y, hfan.uncoloured]
      rfl
    · rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hxw y]
      exact hfan.uncoloured
  · intro i hi
    obtain ⟨γ, hγ, hγfree⟩ := hfan.step i (hi.trans_le hm)
    have hγa : γ ≠ a := by
      rintro rfl
      exact ha _ hγ
    by_cases hxw : (c.kempeGraph a b).Reachable w x
    · refine ⟨Equiv.swap a b γ, ?_, ?_⟩
      · rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hxw (f (i + 1)), hγ]
        rfl
      · by_cases hiw : (c.kempeGraph a b).Reachable w (f i)
        · rw [isFree_kempeSwap_of_reachable c a b hiw]
          simpa using hγfree
        · have hγb : γ ≠ b := by
            rintro rfl
            exact hiw ((hbreak i hi hγ).2 hxw)
          rw [isFree_kempeSwap_of_not_reachable c a b hiw,
            Equiv.swap_apply_of_ne_of_ne hγa hγb]
          exact hγfree
    · refine ⟨γ, ?_, ?_⟩
      · rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hxw (f (i + 1))]
        exact hγ
      · by_cases hiw : (c.kempeGraph a b).Reachable w (f i)
        · have hγb : γ ≠ b := by
            rintro rfl
            exact hxw ((hbreak i hi hγ).1 hiw)
          rw [isFree_kempeSwap_of_reachable c a b hiw,
            Equiv.swap_apply_of_ne_of_ne hγa hγb]
          exact hγfree
        · rw [isFree_kempeSwap_of_not_reachable c a b hiw]
          exact hγfree

omit [DecidableEq V] [DecidableEq C] in
/-- **Vizing's extension step.** -/
theorem vizing_step [DecidableRel G.Adj] (c : PEC G C) (hcard : G.maxDegree < Fintype.card C)
    {x y : V} (hadj : G.Adj x y) (hnone : c.col x y = none) :
    ∃ c' : PEC G C, Extends c c' ∧ c'.col x y ≠ none := by
  classical
  obtain ⟨n, f, hfan, hmax⟩ := c.exists_maximal_fan hadj hnone
  obtain ⟨a, ha⟩ := c.exists_free hcard x
  obtain ⟨b, hb⟩ := c.exists_free hcard (f n)
  by_cases han : c.IsFree (f n) a
  · exact fan_rotate x y f n c a hfan ha han
  by_cases hbx : c.IsFree x b
  · exact fan_rotate x y f n c b hfan hbx hb
  -- `b` is used at `x`, on an edge of the fan
  obtain ⟨z, hz⟩ : ∃ z, c.col x z = some b := by
    by_contra hcon
    push Not at hcon
    exact hbx hcon
  have hzadj : G.Adj x z := c.col_adj hz
  have hzfan : ∃ i ≤ n, f i = z := by
    by_contra hcon
    push Not at hcon
    set g : ℕ → V := fun i => if i = n + 1 then z else f i with hg
    have hgi : ∀ i, i ≤ n → g i = f i := fun i hi => ite_eq_right (by omega)
    have hgn1 : g (n + 1) = z := ite_eq_left rfl
    have hgfan : c.IsFan x y (n + 1) g := by
      refine ⟨by rw [hgi 0 (by omega)]; exact hfan.start, hfan.uncoloured, ?_, ?_, ?_⟩
      · intro i hi
        rcases Nat.lt_or_ge i (n + 1) with h | h
        · rw [hgi i (by omega)]
          exact hfan.adj i (by omega)
        · have hin : i = n + 1 := by omega
          subst hin
          rw [hgn1]
          exact hzadj
      · intro i hi j hj hij
        rcases Nat.lt_or_ge i (n + 1) with h | h <;> rcases Nat.lt_or_ge j (n + 1) with h' | h'
        · rw [hgi i (by omega), hgi j (by omega)] at hij
          exact hfan.inj i (by omega) j (by omega) hij
        · exfalso
          have hjn : j = n + 1 := by omega
          subst hjn
          rw [hgi i (by omega), hgn1] at hij
          exact hcon i (by omega) hij
        · exfalso
          have hin : i = n + 1 := by omega
          subst hin
          rw [hgi j (by omega), hgn1] at hij
          exact hcon j (by omega) hij.symm
        · omega
      · intro i hi
        rcases Nat.lt_or_ge i n with h | h
        · obtain ⟨γ, hγ, hγfree⟩ := hfan.step i h
          exact ⟨γ, by rw [hgi (i + 1) (by omega)]; exact hγ,
            by rw [hgi i (by omega)]; exact hγfree⟩
        · have hin : i = n := by omega
          subst hin
          exact ⟨b, by rw [hgn1]; exact hz, by rw [hgi _ le_rfl]; exact hb⟩
    have := hmax (n + 1) g hgfan
    omega
  obtain ⟨i, hin, hiz⟩ := hzfan
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [hfan.start] at hiz
    rw [hiz] at hnone
    rw [hnone] at hz
    simp at hz
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hbxcol : c.col x (f (j + 1)) = some b := by rw [hiz]; exact hz
  have hbj : c.IsFree (f j) b := by
    obtain ⟨γ, hγ, hγfree⟩ := hfan.step j (by omega)
    have hγb : γ = b := Option.some_injective _ (by rw [← hγ, hbxcol])
    rw [← hγb]
    exact hγfree
  have hxfn : x ≠ f n := (hfan.adj n le_rfl).ne
  have hxfj : x ≠ f j := (hfan.adj j (by omega)).ne
  have hfnfj : f n ≠ f j := by
    intro h
    have := hfan.inj n le_rfl j (by omega) h
    omega
  have hdeg2 : ∀ v, (c.kempeGraph a b).degree v ≤ 2 := c.kempe_degree_le_two a b
  have hdegx : (c.kempeGraph a b).degree x ≤ 1 :=
    c.kempe_degree_le_one_of_isFree (Or.inl rfl) ha
  have hdegn : (c.kempeGraph a b).degree (f n) ≤ 1 :=
    c.kempe_degree_le_one_of_isFree (Or.inr rfl) hb
  have hdegj : (c.kempeGraph a b).degree (f j) ≤ 1 :=
    c.kempe_degree_le_one_of_isFree (Or.inr rfl) hbj
  by_cases hRn : (c.kempeGraph a b).Reachable x (f n)
  · -- the Kempe chain from `x` ends at `f n`; interchange on the component of `f j` instead
    have hRj : ¬ (c.kempeGraph a b).Reachable x (f j) := fun hRj =>
      no_three_endpoints hdeg2 hxfn hxfj hfnfj hdegx hdegn hdegj hRn hRj
    have hxnotR : ¬ (c.kempeGraph a b).Reachable (f j) x := fun h => hRj h.symm
    have hfan2 : (c.kempeSwap a b (f j)).IsFan x y j f := by
      refine c.isFan_kempeSwap hfan ha (f j) (by omega) ?_
      intro i' hi' hcol
      exfalso
      have h1 : f (i' + 1) = f (j + 1) := c.col_proper hcol hbxcol
      have h2 := hfan.inj (i' + 1) (by omega) (j + 1) (by omega) h1
      omega
    have hax : (c.kempeSwap a b (f j)).IsFree x a :=
      (isFree_kempeSwap_of_not_reachable c a b hxnotR a).2 ha
    have hajfree : (c.kempeSwap a b (f j)).IsFree (f j) a :=
      (isFree_kempeSwap_of_reachable c a b (Reachable.refl _) a).2 (by simpa using hbj)
    obtain ⟨c', hext, hcol'⟩ := fan_rotate x y f j _ a hfan2 hax hajfree
    exact ⟨c', (c.extends_kempeSwap a b (f j)).trans hext, hcol'⟩
  · -- interchange on the component of `x`
    have hxR : (c.kempeGraph a b).Reachable x x := Reachable.refl x
    have hbx1 : (c.kempeSwap a b x).IsFree x b :=
      (isFree_kempeSwap_of_reachable c a b hxR b).2 (by simpa using ha)
    by_cases hRj : (c.kempeGraph a b).Reachable x (f j)
    · have hfan2 : (c.kempeSwap a b x).IsFan x y n f := by
        refine c.isFan_kempeSwap hfan ha x le_rfl ?_
        intro i' hi' hcol
        have h1 : f (i' + 1) = f (j + 1) := c.col_proper hcol hbxcol
        have h2 := hfan.inj (i' + 1) (by omega) (j + 1) (by omega) h1
        have h3 : i' = j := by omega
        subst h3
        exact ⟨fun _ => hxR, fun _ => hRj⟩
      have hbn1 : (c.kempeSwap a b x).IsFree (f n) b :=
        (isFree_kempeSwap_of_not_reachable c a b hRn b).2 hb
      obtain ⟨c', hext, hcol'⟩ := fan_rotate x y f n _ b hfan2 hbx1 hbn1
      exact ⟨c', (c.extends_kempeSwap a b x).trans hext, hcol'⟩
    · have hfan2 : (c.kempeSwap a b x).IsFan x y j f := by
        refine c.isFan_kempeSwap hfan ha x (by omega) ?_
        intro i' hi' hcol
        exfalso
        have h1 : f (i' + 1) = f (j + 1) := c.col_proper hcol hbxcol
        have h2 := hfan.inj (i' + 1) (by omega) (j + 1) (by omega) h1
        omega
      have hbj1 : (c.kempeSwap a b x).IsFree (f j) b :=
        (isFree_kempeSwap_of_not_reachable c a b hRj b).2 hbj
      obtain ⟨c', hext, hcol'⟩ := fan_rotate x y f j _ b hfan2 hbx1 hbj1
      exact ⟨c', (c.extends_kempeSwap a b x).trans hext, hcol'⟩

end PEC

end LeanPool.Vizing
