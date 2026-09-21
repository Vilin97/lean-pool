/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import LeanPool.ACMax.Spectral.TestVector

/-!
# Far-pair and apex double-star test-vector certificates

Two reusable spectral certificates that bound the algebraic connectivity of a
graph above by `2` from an explicit test vector. They are the workhorses for
killing configurations built around a pair of low-degree vertices `u, v` in the
general ACMAX argument.

## Main results

* `algConn_le_two_of_weighted_double_star` — the **weighted double-star master
  certificate**. For non-adjacent `u ≠ v` with disjoint neighbourhoods and
  nonnegative weight data (`au` on `u`, `p` on `N(u)`, `av` on `v`, `q` on
  `N(v)`), the five-valued test vector
  `x = au·𝟙_u + p·𝟙_{N(u)} − av·𝟙_v − q·𝟙_{N(v)}` witnesses `algConn G ≤ 2`
  whenever the worst-case quadratic bound
  `Σ (au − p w)² + Σ (av − q w)² + Σ_{cross} (p w + q w')² + Σ leak·p² + Σ leak·q²
  ≤ 2·(au² + Σ p² + av² + Σ q²)` holds (an edge inside `N(u)` costs at most its
  two leak-slot charges since the weights are nonnegative).
* `algConn_le_two_of_apex_double_star` — the same certificate extended to pairs
  sharing **exactly one** common neighbour `g` (the *apex*, weight `0`); the two
  apex edges `u–g`, `v–g` cost `au² + av²`.
* `algConn_le_two_of_apex_twin_pair` — the **apex tie law**: two degree-3
  vertices sharing a single hub `g`, with all non-apex partners of degree `≤ 4`
  and no partner–partner cross edges, force `algConn G ≤ 2`. With
  `au = av = 1`, `p = q ≡ ½` the quadratic bound holds with equality
  (`1 + 1 + 4·¼ + 4·(3·¼) = 6 = 2·(1 + ½ + 1 + ½)`), so the hypotheses trace out
  the exact tie boundary.

All three are direct instances of `algConn_le_two_of_testvector`; no new spectral
machinery is introduced.
-/

namespace ACMax

open Matrix

variable {V : Type*} [Fintype V]

/-! ## The weighted double-star master certificate -/

open Classical in
private theorem algConn_le_two_of_weighted_double_star_hnorm : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v : V) (au av : ℝ) (p q : V → ℝ) (_ : u ≠ v) (_ : ¬G.Adj u v) (_ : ∀ (w : V), ¬(G.Adj u w ∧
    G.Adj v w))
  (A : Finset V) (_ : ∀ w ∈ A, 0 ≤ p w) (_ : A = G.neighborFinset u),
  let B := G.neighborFinset v;
  ∀ (_ : ∀ w ∈ B, 0 ≤ q w) (_ : au + ∑ w ∈ A, p w = av + ∑ w ∈ B, q w)
    (_ :
      (∑ w ∈ A, (au - p w) ^ 2 + ∑ w ∈ B, (av - q w) ^ 2 +
              ∑ w ∈ A, ∑ w' ∈ B, if G.Adj w w' then (p w + q w') ^ 2 else 0) +
            ∑ w ∈ A, ↑(G.neighborFinset w \ insert u B).card * p w ^ 2 +
          ∑ w ∈ B, ↑(G.neighborFinset w \ insert v A).card * q w ^ 2 ≤
        2 * (au ^ 2 + ∑ w ∈ A, p w ^ 2 + (av ^ 2 + ∑ w ∈ B, q w ^ 2)))
    (_ : B = G.neighborFinset v) (_ : ∀ (w : V), w ∈ A ↔ G.Adj u w) (_ : ∀ (w : V), w ∈ B ↔ G.Adj
      v w)
    (_ : u ∉ A) (_ : v ∉ A) (_ : u ∉ B) (_ : v ∉ B) (_ : ∀ w ∈ A, w ∉ B),
    let x := fun w =>
      ((if w = u then au else 0) + if w ∈ A then p w else 0) -
        ((if w = v then av else 0) + if w ∈ B then q w else 0);
    ∀
      (_ :
        x = fun w =>
          ((if w = u then au else 0) + if w ∈ A then p w else 0) -
            ((if w = v then av else 0) + if w ∈ B then q w else 0))
      (_ : x u = au) (_ : x v = -av) (_ : ∀ w ∈ A, x w = p w) (_ : ∀ w ∈ B, x w = -q w)
      (_ : ∀ (w : V), w ≠ u → w ≠ v → w ∉ A → w ∉ B → x w = 0) (_ : ∑ i, x i = 0) (_ : ∃ i, x i ≠
        0),
      ∑ i, x i ^ 2 = au ^ 2 + ∑ w ∈ A, p w ^ 2 + (av ^ 2 + ∑ w ∈ B, q w ^ 2) := by
  classical
  intro V inst G u v au av p q hne huv hcap A hp hA B hq hbal hQ hB hmemA hmemB huA hvA huB hvB
    hAB x hxdef hxu hxv hxA hxB hxZ hsum0 hne0
  have hsq : ∀ i : V, x i ^ 2
      = ((if i = u then au ^ 2 else 0) + (if i ∈ A then p i ^ 2 else 0))
        + ((if i = v then av ^ 2 else 0) + (if i ∈ B then q i ^ 2 else 0)) := by
    intro i
    by_cases hiu : i = u
    · subst hiu; rw [hxu]; simp [hne, huA, huB]
    · by_cases hiv : i = v
      · subst hiv; rw [hxv]; simp [hne.symm, hvA, hvB]
      · by_cases hiA : i ∈ A
        · rw [hxA i hiA]; simp [hiu, hiv, hiA, hAB i hiA]
        · by_cases hiB : i ∈ B
          · rw [hxB i hiB]; simp [hiu, hiv, hiA, hiB]
          · rw [hxZ i hiu hiv hiA hiB]; simp [hiu, hiv, hiA, hiB]
  simp_rw [hsq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ u fun _ => au ^ 2,
    Finset.sum_ite_eq' Finset.univ v fun _ => av ^ 2,
    Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]
  simp only [Finset.mem_univ, ite_true]

open Classical in
private theorem algConn_le_two_of_weighted_double_star_hterm : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v : V) (au av : ℝ) (p q : V → ℝ),
  let A := G.neighborFinset u;
  ∀ (_ : ∀ w ∈ A, 0 ≤ p w),
    let B := G.neighborFinset v;
    ∀ (_ : ∀ w ∈ B, 0 ≤ q w) (_ : ∀ (w : V), w ∈ A ↔ G.Adj u w) (_ : ∀ (w : V), w ∈ B ↔ G.Adj v w)
      (_ : ∀ w ∈ A, w ∉ B),
      let x := fun w =>
        ((if w = u then au else 0) + if w ∈ A then p w else 0) -
          ((if w = v then av else 0) + if w ∈ B then q w else 0);
      ∀ (_ : x u = au) (_ : x v = -av) (_ : ∀ w ∈ A, x w = p w) (_ : ∀ w ∈ B, x w = -q w)
        (_ : ∀ (w : V), w ≠ u → w ≠ v → w ∉ A → w ∉ B → x w = 0) (i j : V),
        (if G.Adj i j then (x i - x j) ^ 2 else 0) ≤
          (((((((((if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0) + if G.Adj i j ∧ j = u then
            (au - p i) ^ 2 else 0) +
                          if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0) +
                        if G.Adj i j ∧ j = v then (av - q i) ^ 2 else 0) +
                      if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0) +
                    if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0) +
                  if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0) +
                if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0) +
              if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0) +
            if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0 := by
  classical
  intro V inst G u v au av p q A hp B hq hmemA hmemB hAB x hxu hxv hxA hxB hxZ i j
  by_cases hadj : G.Adj i j
  · -- Nonnegativity of every summand.
    have nn1 : (0:ℝ) ≤ if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0 := by
      split <;> positivity
    have nn2 : (0:ℝ) ≤ if G.Adj i j ∧ j = u then (au - p i) ^ 2 else 0 := by
      split <;> positivity
    have nn3 : (0:ℝ) ≤ if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0 := by
      split <;> positivity
    have nn4 : (0:ℝ) ≤ if G.Adj i j ∧ j = v then (av - q i) ^ 2 else 0 := by
      split <;> positivity
    have nn5 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0 := by
      split <;> positivity
    have nn6 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0 := by
      split <;> positivity
    have nn7 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0 := by
      split <;> positivity
    have nn8 : (0:ℝ) ≤ if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0 := by
      split <;> positivity
    have nn9 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0 := by
      split <;> positivity
    have nn10 : (0:ℝ) ≤ if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0 := by
      split <;> positivity
    rw [ite_eq_left hadj]
    by_cases hiu : i = u
    · -- `u → N(u)` edge.
      have hjA : j ∈ A := (hmemA j).mpr (hiu ▸ hadj)
      have e1 : (if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0) = (au - p j) ^ 2 :=
        ite_eq_left ⟨hadj, hiu⟩
      have hxi : x i = au := by rw [hiu]; exact hxu
      rw [hxi, hxA j hjA]
      linarith [nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9, nn10]
    · by_cases hju : j = u
      · -- `N(u) → u` edge.
        have hiA : i ∈ A := (hmemA i).mpr (G.adj_symm (hju ▸ hadj))
        have e2 : (if G.Adj i j ∧ j = u then (au - p i) ^ 2 else 0) = (au - p i) ^ 2 :=
          ite_eq_left ⟨hadj, hju⟩
        have hxj : x j = au := by rw [hju]; exact hxu
        have hval : (p i - au) ^ 2 = (au - p i) ^ 2 := by ring
        rw [hxj, hxA i hiA, hval]
        linarith [nn1, nn3, nn4, nn5, nn6, nn7, nn8, nn9, nn10]
      · by_cases hiv : i = v
        · -- `v → N(v)` edge.
          have hjB : j ∈ B := (hmemB j).mpr (hiv ▸ hadj)
          have e3 : (if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0) = (av - q j) ^ 2 :=
            ite_eq_left ⟨hadj, hiv⟩
          have hxi : x i = -av := by rw [hiv]; exact hxv
          have hval : (-av - -(q j)) ^ 2 = (av - q j) ^ 2 := by ring
          rw [hxi, hxB j hjB, hval]
          linarith [nn1, nn2, nn4, nn5, nn6, nn7, nn8, nn9, nn10]
        · by_cases hjv : j = v
          · -- `N(v) → v` edge.
            have hiB : i ∈ B := (hmemB i).mpr (G.adj_symm (hjv ▸ hadj))
            have e4 : (if G.Adj i j ∧ j = v then (av - q i) ^ 2 else 0)
                = (av - q i) ^ 2 := ite_eq_left ⟨hadj, hjv⟩
            have hxj : x j = -av := by rw [hjv]; exact hxv
            have hval : (-(q i) - -av) ^ 2 = (av - q i) ^ 2 := by ring
            rw [hxj, hxB i hiB, hval]
            linarith [nn1, nn2, nn3, nn5, nn6, nn7, nn8, nn9, nn10]
          · -- Neither endpoint is a centre.
            by_cases hiA : i ∈ A
            · by_cases hjB : j ∈ B
              · -- cross edge `N(u) → N(v)`.
                have e5 : (if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
                    = (p i + q j) ^ 2 := ite_eq_left ⟨hadj, hiA, hjB⟩
                have hval : (p i - -(q j)) ^ 2 = (p i + q j) ^ 2 := by ring
                rw [hxA i hiA, hxB j hjB, hval]
                linarith [nn1, nn2, nn3, nn4, nn6, nn7, nn8, nn9, nn10]
              · by_cases hjA : j ∈ A
                · -- internal `N(u)` edge: charge both slots.
                  have e7 : (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
                      = p i ^ 2 := ite_eq_left ⟨hadj, hiA, hju, hjB⟩
                  have e8 : (if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
                      = p j ^ 2 := ite_eq_left ⟨hadj, hjA, hiu, hAB i hiA⟩
                  have hb : (p i - p j) ^ 2 ≤ p i ^ 2 + p j ^ 2 := by
                    nlinarith only [mul_nonneg (hp i hiA) (hp j hjA)]
                  rw [hxA i hiA, hxA j hjA]
                  linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn9, nn10]
                · -- leak `N(u) → Z`.
                  have e7 : (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
                      = p i ^ 2 := ite_eq_left ⟨hadj, hiA, hju, hjB⟩
                  have hval : (p i - 0) ^ 2 = p i ^ 2 := by ring
                  rw [hxA i hiA, hxZ j hju hjv hjA hjB, hval]
                  linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn8, nn9, nn10]
            · by_cases hiB : i ∈ B
              · by_cases hjA : j ∈ A
                · -- cross edge `N(v) → N(u)`.
                  have e6 : (if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
                      = (p j + q i) ^ 2 := ite_eq_left ⟨hadj, hiB, hjA⟩
                  have hval : (-(q i) - p j) ^ 2 = (p j + q i) ^ 2 := by ring
                  rw [hxB i hiB, hxA j hjA, hval]
                  linarith [nn1, nn2, nn3, nn4, nn5, nn7, nn8, nn9, nn10]
                · by_cases hjB : j ∈ B
                  · -- internal `N(v)` edge.
                    have e9 : (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
                        = q i ^ 2 := ite_eq_left ⟨hadj, hiB, hjv, hjA⟩
                    have e10 : (if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)
                        = q j ^ 2 := ite_eq_left ⟨hadj, hjB, hiv, hiA⟩
                    have hb : (-(q i) - -(q j)) ^ 2 ≤ q i ^ 2 + q j ^ 2 := by
                      nlinarith only [mul_nonneg (hq i hiB) (hq j hjB)]
                    rw [hxB i hiB, hxB j hjB]
                    linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8]
                  · -- leak `N(v) → Z`.
                    have e9 : (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
                        = q i ^ 2 := ite_eq_left ⟨hadj, hiB, hjv, hjA⟩
                    have hval : (-(q i) - 0) ^ 2 = q i ^ 2 := by ring
                    rw [hxB i hiB, hxZ j hju hjv hjA hjB, hval]
                    linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn10]
              · by_cases hjA : j ∈ A
                · -- leak `Z → N(u)`.
                  have e8 : (if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
                      = p j ^ 2 := ite_eq_left ⟨hadj, hjA, hiu, hiB⟩
                  have hval : (0 - p j) ^ 2 = p j ^ 2 := by ring
                  rw [hxZ i hiu hiv hiA hiB, hxA j hjA, hval]
                  linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn9, nn10]
                · by_cases hjB : j ∈ B
                  · -- leak `Z → N(v)`.
                    have e10 : (if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)
                        = q j ^ 2 := ite_eq_left ⟨hadj, hjB, hiv, hiA⟩
                    have hval : (0 - -(q j)) ^ 2 = q j ^ 2 := by ring
                    rw [hxZ i hiu hiv hiA hiB, hxB j hjB, hval]
                    linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9]
                  · -- `Z → Z`: zero.
                    rw [hxZ i hiu hiv hiA hiB, hxZ j hju hjv hjA hjB]
                    norm_num
                    linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9, nn10]
  · simp [hadj]

open Classical in
private theorem algConn_le_two_of_weighted_double_star_hC5 : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v : V) (p q : V → ℝ),
  let A := G.neighborFinset u;
  let B := G.neighborFinset v;
  (∑ i, ∑ j, if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0) =
    ∑ w ∈ A, ∑ w' ∈ B, if G.Adj w w' then (p w + q w') ^ 2 else 0 := by
  classical
  intro V inst G u v p q A B
  have h1 : ∀ i j : V, (if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
      = if i ∈ A then (if j ∈ B then (if G.Adj i j then (p i + q j) ^ 2 else 0)
          else 0) else 0 := by
    intro i j
    by_cases h1 : i ∈ A <;> by_cases h2 : j ∈ B <;> by_cases h3 : G.Adj i j <;>
      simp [h1, h2, h3]
  have h2 : ∀ i : V,
      (∑ j, if i ∈ A then (if j ∈ B then (if G.Adj i j then (p i + q j) ^ 2 else 0)
          else 0) else 0)
      = if i ∈ A then (∑ j, if j ∈ B then (if G.Adj i j then (p i + q j) ^ 2 else 0)
          else 0) else 0 := by
    intro i
    by_cases h : i ∈ A <;> simp [h]
  simp_rw [h1, h2]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter]

open Classical in
private theorem algConn_le_two_of_weighted_double_star_hC7 : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v : V) (p : V → ℝ),
  let A := G.neighborFinset u;
  let B := G.neighborFinset v;
  (∑ i, ∑ j, if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0) =
    ∑ w ∈ A, ↑(G.neighborFinset w \ insert u B).card * p w ^ 2 := by
  classical
  intro V inst G u v p A B
  have h1 : ∀ i j : V, (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
      = if i ∈ A then (if j ∈ G.neighborFinset i \ insert u B then p i ^ 2 else 0)
          else 0 := by
    intro i j
    have hmem : j ∈ G.neighborFinset i \ insert u B ↔ G.Adj i j ∧ j ≠ u ∧ j ∉ B := by
      simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
        not_or]
    by_cases h1 : i ∈ A <;> by_cases h2 : G.Adj i j ∧ j ≠ u ∧ j ∉ B <;>
      simp [h1, h2, hmem]
  have h2 : ∀ i : V,
      (∑ j, if i ∈ A then (if j ∈ G.neighborFinset i \ insert u B then p i ^ 2 else 0)
          else 0)
      = if i ∈ A then (∑ j, if j ∈ G.neighborFinset i \ insert u B then p i ^ 2 else 0)
          else 0 := by
    intro i
    by_cases h : i ∈ A <;> simp [h]
  simp_rw [h1, h2]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

open Classical in
private theorem algConn_le_two_of_weighted_double_star_hC9 : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v : V) (q : V → ℝ),
  let A := G.neighborFinset u;
  let B := G.neighborFinset v;
  (∑ i, ∑ j, if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0) =
    ∑ w ∈ B, ↑(G.neighborFinset w \ insert v A).card * q w ^ 2 := by
  classical
  intro V inst G u v q A B
  have h1 : ∀ i j : V, (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
      = if i ∈ B then (if j ∈ G.neighborFinset i \ insert v A then q i ^ 2 else 0)
          else 0 := by
    intro i j
    have hmem : j ∈ G.neighborFinset i \ insert v A ↔ G.Adj i j ∧ j ≠ v ∧ j ∉ A := by
      simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
        not_or]
    by_cases h1 : i ∈ B <;> by_cases h2 : G.Adj i j ∧ j ≠ v ∧ j ∉ A <;>
      simp [h1, h2, hmem]
  have h2 : ∀ i : V,
      (∑ j, if i ∈ B then (if j ∈ G.neighborFinset i \ insert v A then q i ^ 2 else 0)
          else 0)
      = if i ∈ B then (∑ j, if j ∈ G.neighborFinset i \ insert v A then q i ^ 2 else 0)
          else 0 := by
    intro i
    by_cases h : i ∈ B <;> simp [h]
  simp_rw [h1, h2]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

open Classical in
/-- **The weighted double-star master certificate.**  Two vertices `u ≠ v`, not
adjacent, with disjoint neighbourhoods, and nonnegative weights (`au` on `u`,
`p w` on `w ∈ N(u)`; `av`, `q` on the `v`-side, negated) that are balanced
(`au + Σ p = av + Σ q`) and satisfy the worst-case quadratic-form bound: then
`algConn G ≤ 2`.  Cross edges `N(u)–N(v)` are allowed and cost `(p w + q w')²`;
each further edge at `w ∈ N(u)` (to anywhere except `u` and `N(v)`) is charged
`(p w)²` per endpoint slot. -/
theorem algConn_le_two_of_weighted_double_star [Nonempty V]
    (G : SimpleGraph V) (u v : V) (au av : ℝ) (p q : V → ℝ)
    (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hcap : ∀ w : V, ¬(G.Adj u w ∧ G.Adj v w))
    (hau : 0 < au)
    (hp : ∀ w ∈ G.neighborFinset u, 0 ≤ p w)
    (hq : ∀ w ∈ G.neighborFinset v, 0 ≤ q w)
    (hbal : au + ∑ w ∈ G.neighborFinset u, p w
          = av + ∑ w ∈ G.neighborFinset v, q w)
    (hQ : (∑ w ∈ G.neighborFinset u, (au - p w) ^ 2)
        + (∑ w ∈ G.neighborFinset v, (av - q w) ^ 2)
        + (∑ w ∈ G.neighborFinset u, ∑ w' ∈ G.neighborFinset v,
            (if G.Adj w w' then (p w + q w') ^ 2 else 0))
        + (∑ w ∈ G.neighborFinset u,
            ((G.neighborFinset w \ insert u (G.neighborFinset v)).card : ℝ)
              * p w ^ 2)
        + (∑ w ∈ G.neighborFinset v,
            ((G.neighborFinset w \ insert v (G.neighborFinset u)).card : ℝ)
              * q w ^ 2)
        ≤ 2 * (au ^ 2 + (∑ w ∈ G.neighborFinset u, p w ^ 2)
             + (av ^ 2 + ∑ w ∈ G.neighborFinset v, q w ^ 2))) :
    algConn G ≤ 2 := by
  classical
  set A := G.neighborFinset u with hA
  set B := G.neighborFinset v with hB
  -- Membership bookkeeping.
  have hmemA : ∀ w : V, w ∈ A ↔ G.Adj u w := fun w => G.mem_neighborFinset u w
  have hmemB : ∀ w : V, w ∈ B ↔ G.Adj v w := fun w => G.mem_neighborFinset v w
  have huA : u ∉ A := fun h => G.irrefl ((hmemA u).mp h)
  have hvA : v ∉ A := fun h => huv ((hmemA v).mp h)
  have huB : u ∉ B := fun h => huv (G.adj_symm ((hmemB u).mp h))
  have hvB : v ∉ B := fun h => G.irrefl ((hmemB v).mp h)
  have hAB : ∀ w : V, w ∈ A → w ∉ B :=
    fun w hwA hwB => hcap w ⟨(hmemA w).mp hwA, (hmemB w).mp hwB⟩
  -- The test vector.
  set x : V → ℝ := fun w =>
    ((if w = u then au else 0) + (if w ∈ A then p w else 0))
      - ((if w = v then av else 0) + (if w ∈ B then q w else 0)) with hxdef
  have hxu : x u = au := by simp [hxdef, hne, huA, huB]
  have hxv : x v = -av := by simp [hxdef, hne.symm, hvA, hvB]
  have hxA : ∀ w ∈ A, x w = p w := by
    intro w hw
    have h1 : w ≠ u := fun e => huA (e ▸ hw)
    have h2 : w ≠ v := fun e => hvA (e ▸ hw)
    have h3 : w ∉ B := hAB w hw
    simp [hxdef, h1, h2, hw, h3]
  have hxB : ∀ w ∈ B, x w = -(q w) := by
    intro w hw
    have h1 : w ≠ u := fun e => huB (e ▸ hw)
    have h2 : w ≠ v := fun e => hvB (e ▸ hw)
    have h3 : w ∉ A := fun hwA => hAB w hwA hw
    simp [hxdef, h1, h2, h3, hw]
  have hxZ : ∀ w : V, w ≠ u → w ≠ v → w ∉ A → w ∉ B → x w = 0 := by
    intro w h1 h2 h3 h4
    simp [hxdef, h1, h2, h3, h4]
  -- Orthogonality to the all-ones vector.
  have hsum0 : ∑ i, x i = 0 := by
    simp only [hxdef]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ u fun _ => au,
      Finset.sum_ite_eq' Finset.univ v fun _ => av,
      Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]
    simp only [Finset.mem_univ, ite_true]
    linarith [hbal]
  -- Nonvanishing.
  have hne0 : ∃ i, x i ≠ 0 := ⟨u, by rw [hxu]; exact ne_of_gt hau⟩
  -- Squared norm.
  have hnorm :=
      algConn_le_two_of_weighted_double_star_hnorm (V := V) (G := G) (u := u) (v := v) (au :=
        au) (av := av) (p := p) (q := q) (hne) (huv) (hcap) (A := A) (hp) (hA) (hq) (hbal) (hQ)
          (hB) (hmemA) (hmemB) (huA) (hvA) (huB) (hvB) (hAB) (hxdef)
        (hxu) (hxv) (hxA) (hxB) (hxZ) (hsum0) (hne0)
  -- Per-ordered-pair upper bound on the quadratic-form summand.
  have hterm :=
      algConn_le_two_of_weighted_double_star_hterm (V := V) (G := G) (u := u) (v := v) (au :=
        au) (av := av) (p := p) (q := q) (hp) (hq) (hmemA) (hmemB)
        (hAB) (hxu) (hxv) (hxA) (hxB) (hxZ)
  -- Sum-over-neighbours helper.
  have hnbr_sum : ∀ (z : V) (f : V → ℝ),
      (∑ j, if G.Adj z j then f j else 0) = ∑ j ∈ G.neighborFinset z, f j := by
    intro z f
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp [SimpleGraph.mem_neighborFinset]
  -- Count lemma: `u`-centre edges (`i = u`).
  have hC1 : (∑ i, ∑ j, if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0)
      = ∑ w ∈ A, (au - p w) ^ 2 := by
    have h1 : ∀ i j : V, (if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0)
        = if i = u then (if G.Adj i j then (au - p j) ^ 2 else 0) else 0 := by
      intro i j
      by_cases h1 : i = u <;> by_cases h2 : G.Adj i j <;> simp [h1, h2]
    have h2 : ∀ i : V,
        (∑ j, if i = u then (if G.Adj i j then (au - p j) ^ 2 else 0) else 0)
        = if i = u then (∑ j, if G.Adj i j then (au - p j) ^ 2 else 0) else 0 := by
      intro i
      by_cases h : i = u <;> simp [h]
    simp_rw [h1, h2]
    rw [Finset.sum_ite_eq' Finset.univ u]
    simp only [Finset.mem_univ, ite_true]
    exact hnbr_sum u _
  have hC2 : (∑ i, ∑ j, if G.Adj i j ∧ j = u then (au - p i) ^ 2 else 0)
      = ∑ w ∈ A, (au - p w) ^ 2 := by
    rw [← hC1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
  -- Count lemma: `v`-centre edges.
  have hC3 : (∑ i, ∑ j, if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0)
      = ∑ w ∈ B, (av - q w) ^ 2 := by
    have h1 : ∀ i j : V, (if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0)
        = if i = v then (if G.Adj i j then (av - q j) ^ 2 else 0) else 0 := by
      intro i j
      by_cases h1 : i = v <;> by_cases h2 : G.Adj i j <;> simp [h1, h2]
    have h2 : ∀ i : V,
        (∑ j, if i = v then (if G.Adj i j then (av - q j) ^ 2 else 0) else 0)
        = if i = v then (∑ j, if G.Adj i j then (av - q j) ^ 2 else 0) else 0 := by
      intro i
      by_cases h : i = v <;> simp [h]
    simp_rw [h1, h2]
    rw [Finset.sum_ite_eq' Finset.univ v]
    simp only [Finset.mem_univ, ite_true]
    exact hnbr_sum v _
  have hC4 : (∑ i, ∑ j, if G.Adj i j ∧ j = v then (av - q i) ^ 2 else 0)
      = ∑ w ∈ B, (av - q w) ^ 2 := by
    rw [← hC3, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
  -- Count lemma: cross edges.
  have hC5 :=
      algConn_le_two_of_weighted_double_star_hC5 (V := V) (G := G) (u := u) (v := v) (p := p)
        (q := q)
  have hC6 : (∑ i, ∑ j, if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
      = ∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0) := by
    rw [← hC5, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
    tauto
  -- Count lemma: `N(u)` leak slots.
  have hC7 :=
      algConn_le_two_of_weighted_double_star_hC7 (V := V) (G := G) (u := u) (v := v) (p := p)
  have hC8 : (∑ i, ∑ j, if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
      = ∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2 := by
    rw [← hC7, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
  -- Count lemma: `N(v)` leak slots.
  have hC9 :=
      algConn_le_two_of_weighted_double_star_hC9 (V := V) (G := G) (u := u) (v := v) (q := q)
  have hC10 : (∑ i, ∑ j, if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)
      = ∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2 := by
    rw [← hC9, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
  -- Assemble the ordered-pair bound.
  have hsum_bound : (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0)
      ≤ 2 * ((∑ w ∈ A, (au - p w) ^ 2) + (∑ w ∈ B, (av - q w) ^ 2)
        + (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
        + (∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2)
        + (∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2)) := by
    calc (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0)
        ≤ ∑ i, ∑ j,
            ((if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0)
          + (if G.Adj i j ∧ j = u then (au - p i) ^ 2 else 0)
          + (if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0)
          + (if G.Adj i j ∧ j = v then (av - q i) ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
          + (if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
          + (if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = 2 * ((∑ w ∈ A, (au - p w) ^ 2) + (∑ w ∈ B, (av - q w) ^ 2)
            + (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
            + (∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2)
            + (∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2)) := by
          simp_rw [Finset.sum_add_distrib]
          rw [hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10]
          ring
  -- Conclude via the universal test-vector certificate.
  apply algConn_le_two_of_testvector G x hsum0 hne0
  rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂', hnorm]
  linarith [hsum_bound, hQ]

/-! ## The apex double star and the tie law

`algConn_le_two_of_apex_double_star` extends the master certificate to pairs
sharing one apex `g` (weight `0`), the two apex edges `u–g`, `v–g` costing
`au² + av²`. The tie law `algConn_le_two_of_apex_twin_pair` applies it to two
degree-3 vertices with a single shared hub, partners of degree `≤ 4`, and no
partner–partner cross edge. This is the certificate behind the A-bound: every
same-cloud pair of usable twins of a degree-`≥ 9` hub either meets it or shares
a degree-4 partner / carries a cross edge, a coverage count that bounds the
cloud size. -/

open Classical in
private theorem algConn_le_two_of_apex_double_star_hnorm : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v g : V) (au av : ℝ) (p q : V → ℝ) (_ : u ≠ v) (_ : ¬G.Adj u v) (_ : G.Adj u g) (_ : G.Adj v g)
  (_ : ∀ (w : V), w ≠ g → ¬(G.Adj u w ∧ G.Adj v w)) (A : Finset V) (_ : ∀ w ∈ A, 0 ≤ p w)
  (_ : A = (G.neighborFinset u).erase g),
  let B := (G.neighborFinset v).erase g;
  ∀ (_ : ∀ w ∈ B, 0 ≤ q w) (_ : au + ∑ w ∈ A, p w = av + ∑ w ∈ B, q w)
    (_ :
      (au ^ 2 + av ^ 2 + ∑ w ∈ A, (au - p w) ^ 2 + ∑ w ∈ B, (av - q w) ^ 2 +
              ∑ w ∈ A, ∑ w' ∈ B, if G.Adj w w' then (p w + q w') ^ 2 else 0) +
            ∑ w ∈ A, ↑(G.neighborFinset w \ insert u B).card * p w ^ 2 +
          ∑ w ∈ B, ↑(G.neighborFinset w \ insert v A).card * q w ^ 2 ≤
        2 * (au ^ 2 + ∑ w ∈ A, p w ^ 2 + (av ^ 2 + ∑ w ∈ B, q w ^ 2)))
    (_ : B = (G.neighborFinset v).erase g) (_ : ∀ (w : V), w ∈ A ↔ w ≠ g ∧ G.Adj u w)
    (_ : ∀ (w : V), w ∈ B ↔ w ≠ g ∧ G.Adj v w) (_ : u ≠ g) (_ : v ≠ g) (_ : g ∉ A) (_ : g ∉ B) (_
      : u ∉ A)
    (_ : v ∉ A) (_ : u ∉ B) (_ : v ∉ B) (_ : ∀ w ∈ A, w ∉ B),
    let x := fun w =>
      ((if w = u then au else 0) + if w ∈ A then p w else 0) -
        ((if w = v then av else 0) + if w ∈ B then q w else 0);
    ∀
      (_ :
        x = fun w =>
          ((if w = u then au else 0) + if w ∈ A then p w else 0) -
            ((if w = v then av else 0) + if w ∈ B then q w else 0))
      (_ : x u = au) (_ : x v = -av) (_ : ∀ w ∈ A, x w = p w) (_ : ∀ w ∈ B, x w = -q w)
      (_ : ∀ (w : V), w ≠ u → w ≠ v → w ∉ A → w ∉ B → x w = 0) (_ : x g = 0) (_ : ∑ i, x i = 0)
      (_ : ∃ i, x i ≠ 0), ∑ i, x i ^ 2 = au ^ 2 + ∑ w ∈ A, p w ^ 2 + (av ^ 2 + ∑ w ∈ B, q w ^ 2)
        := by
  classical
  intro V inst G u v g au av p q hne huv hgu hgv hcap A hp hA B hq hbal hQ hB hmemA hmemB hug hvg
    hgA hgB huA hvA huB hvB hAB x hxdef hxu hxv hxA hxB hxZ hxg hsum0 hne0
  have hsq : ∀ i : V, x i ^ 2
      = ((if i = u then au ^ 2 else 0) + (if i ∈ A then p i ^ 2 else 0))
        + ((if i = v then av ^ 2 else 0) + (if i ∈ B then q i ^ 2 else 0)) := by
    intro i
    by_cases hiu : i = u
    · subst hiu; rw [hxu]; simp [hne, huA, huB]
    · by_cases hiv : i = v
      · subst hiv; rw [hxv]; simp [hne.symm, hvA, hvB]
      · by_cases hiA : i ∈ A
        · rw [hxA i hiA]; simp [hiu, hiv, hiA, hAB i hiA]
        · by_cases hiB : i ∈ B
          · rw [hxB i hiB]; simp [hiu, hiv, hiA, hiB]
          · rw [hxZ i hiu hiv hiA hiB]; simp [hiu, hiv, hiA, hiB]
  simp_rw [hsq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ u fun _ => au ^ 2,
    Finset.sum_ite_eq' Finset.univ v fun _ => av ^ 2,
    Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]
  simp only [Finset.mem_univ, ite_true]

open Classical in
private theorem algConn_le_two_of_apex_double_star_hterm : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v g : V) (au av : ℝ) (p q : V → ℝ) (_ : 0 < au),
  let A := (G.neighborFinset u).erase g;
  ∀ (_ : ∀ w ∈ A, 0 ≤ p w),
    let B := (G.neighborFinset v).erase g;
    ∀ (_ : ∀ w ∈ B, 0 ≤ q w) (_ : ∀ (w : V), w ∈ A ↔ w ≠ g ∧ G.Adj u w)
      (_ : ∀ (w : V), w ∈ B ↔ w ≠ g ∧ G.Adj v w) (_ : ∀ w ∈ A, w ∉ B),
      let x := fun w =>
        ((if w = u then au else 0) + if w ∈ A then p w else 0) -
          ((if w = v then av else 0) + if w ∈ B then q w else 0);
      ∀ (_ : x u = au) (_ : x v = -av) (_ : ∀ w ∈ A, x w = p w) (_ : ∀ w ∈ B, x w = -q w)
        (_ : ∀ (w : V), w ≠ u → w ≠ v → w ∉ A → w ∉ B → x w = 0) (_ : x g = 0) (i j : V),
        (if G.Adj i j then (x i - x j) ^ 2 else 0) ≤
          (((((((((((((if i = u ∧ j ∈ A then (au - p j) ^ 2 else 0) + if j = u ∧ i ∈ A then (au -
            p i) ^ 2 else 0) +
                                  if i = v ∧ j ∈ B then (av - q j) ^ 2 else 0) +
                                if j = v ∧ i ∈ B then (av - q i) ^ 2 else 0) +
                              if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0) +
                            if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0) +
                          if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0) +
                        if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0) +
                      if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0) +
                    if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0) +
                  if i = u ∧ j = g then au ^ 2 else 0) +
                if j = u ∧ i = g then au ^ 2 else 0) +
              if i = v ∧ j = g then av ^ 2 else 0) +
            if j = v ∧ i = g then av ^ 2 else 0 := by
  classical
  intro V inst G u v g au av p q hau A hp B hq hmemA hmemB hAB x hxu hxv hxA hxB hxZ hxg i j
  have nn1 : (0:ℝ) ≤ if i = u ∧ j ∈ A then (au - p j) ^ 2 else 0 := by
    split <;> positivity
  have nn2 : (0:ℝ) ≤ if j = u ∧ i ∈ A then (au - p i) ^ 2 else 0 := by
    split <;> positivity
  have nn3 : (0:ℝ) ≤ if i = v ∧ j ∈ B then (av - q j) ^ 2 else 0 := by
    split <;> positivity
  have nn4 : (0:ℝ) ≤ if j = v ∧ i ∈ B then (av - q i) ^ 2 else 0 := by
    split <;> positivity
  have nn5 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0 := by
    split <;> positivity
  have nn6 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0 := by
    split <;> positivity
  have nn7 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0 := by
    split <;> positivity
  have nn8 : (0:ℝ) ≤ if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0 := by
    split <;> positivity
  have nn9 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0 := by
    split <;> positivity
  have nn10 : (0:ℝ) ≤ if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0 := by
    split <;> positivity
  have nn11 : (0:ℝ) ≤ if i = u ∧ j = g then au ^ 2 else 0 := by
    split <;> positivity
  have nn12 : (0:ℝ) ≤ if j = u ∧ i = g then au ^ 2 else 0 := by
    split <;> positivity
  have nn13 : (0:ℝ) ≤ if i = v ∧ j = g then av ^ 2 else 0 := by
    split <;> positivity
  have nn14 : (0:ℝ) ≤ if j = v ∧ i = g then av ^ 2 else 0 := by
    split <;> positivity
  by_cases hadj : G.Adj i j
  · rw [ite_eq_left hadj]
    by_cases hiu : i = u
    · by_cases hjg : j = g
      · -- apex edge `u → g`.
        have e11 : (if i = u ∧ j = g then au ^ 2 else 0) = au ^ 2 := ite_eq_left ⟨hiu, hjg⟩
        have hxi : x i = au := by rw [hiu]; exact hxu
        have hxj : x j = 0 := by rw [hjg]; exact hxg
        have hval : (au - 0) ^ 2 = au ^ 2 := by ring
        rw [hxi, hxj, hval]
        linarith
      · -- `u → A` edge.
        have hjA : j ∈ A := (hmemA j).mpr ⟨hjg, hiu ▸ hadj⟩
        have e1 : (if i = u ∧ j ∈ A then (au - p j) ^ 2 else 0) = (au - p j) ^ 2 :=
          ite_eq_left ⟨hiu, hjA⟩
        have hxi : x i = au := by rw [hiu]; exact hxu
        rw [hxi, hxA j hjA]
        linarith
    · by_cases hju : j = u
      · by_cases hig : i = g
        · -- apex edge `g → u`.
          have e12 : (if j = u ∧ i = g then au ^ 2 else 0) = au ^ 2 := ite_eq_left ⟨hju, hig⟩
          have hxi : x i = 0 := by rw [hig]; exact hxg
          have hxj : x j = au := by rw [hju]; exact hxu
          have hval : ((0:ℝ) - au) ^ 2 = au ^ 2 := by ring
          rw [hxi, hxj, hval]
          linarith
        · -- `A → u` edge.
          have hiA : i ∈ A := (hmemA i).mpr ⟨hig, G.adj_symm (hju ▸ hadj)⟩
          have e2 : (if j = u ∧ i ∈ A then (au - p i) ^ 2 else 0) = (au - p i) ^ 2 :=
            ite_eq_left ⟨hju, hiA⟩
          have hxj : x j = au := by rw [hju]; exact hxu
          have hval : (p i - au) ^ 2 = (au - p i) ^ 2 := by ring
          rw [hxj, hxA i hiA, hval]
          linarith
      · by_cases hiv : i = v
        · by_cases hjg : j = g
          · -- apex edge `v → g`.
            have e13 : (if i = v ∧ j = g then av ^ 2 else 0) = av ^ 2 :=
              ite_eq_left ⟨hiv, hjg⟩
            have hxi : x i = -av := by rw [hiv]; exact hxv
            have hxj : x j = 0 := by rw [hjg]; exact hxg
            have hval : (-av - 0) ^ 2 = av ^ 2 := by ring
            rw [hxi, hxj, hval]
            linarith
          · -- `v → B` edge.
            have hjB : j ∈ B := (hmemB j).mpr ⟨hjg, hiv ▸ hadj⟩
            have e3 : (if i = v ∧ j ∈ B then (av - q j) ^ 2 else 0) = (av - q j) ^ 2 :=
              ite_eq_left ⟨hiv, hjB⟩
            have hxi : x i = -av := by rw [hiv]; exact hxv
            have hval : (-av - -(q j)) ^ 2 = (av - q j) ^ 2 := by ring
            rw [hxi, hxB j hjB, hval]
            linarith
        · by_cases hjv : j = v
          · by_cases hig : i = g
            · -- apex edge `g → v`.
              have e14 : (if j = v ∧ i = g then av ^ 2 else 0) = av ^ 2 :=
                ite_eq_left ⟨hjv, hig⟩
              have hxi : x i = 0 := by rw [hig]; exact hxg
              have hxj : x j = -av := by rw [hjv]; exact hxv
              have hval : ((0:ℝ) - -av) ^ 2 = av ^ 2 := by ring
              rw [hxi, hxj, hval]
              linarith
            · -- `B → v` edge.
              have hiB : i ∈ B := (hmemB i).mpr ⟨hig, G.adj_symm (hjv ▸ hadj)⟩
              have e4 : (if j = v ∧ i ∈ B then (av - q i) ^ 2 else 0)
                  = (av - q i) ^ 2 := ite_eq_left ⟨hjv, hiB⟩
              have hxj : x j = -av := by rw [hjv]; exact hxv
              have hval : (-(q i) - -av) ^ 2 = (av - q i) ^ 2 := by ring
              rw [hxj, hxB i hiB, hval]
              linarith
          · -- Neither endpoint is a centre.
            by_cases hiA : i ∈ A
            · by_cases hjB : j ∈ B
              · -- cross edge `A → B`.
                have e5 : (if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
                    = (p i + q j) ^ 2 := ite_eq_left ⟨hadj, hiA, hjB⟩
                have hval : (p i - -(q j)) ^ 2 = (p i + q j) ^ 2 := by ring
                rw [hxA i hiA, hxB j hjB, hval]
                linarith
              · by_cases hjA : j ∈ A
                · -- internal `A` edge: charge both slots.
                  have e7 : (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
                      = p i ^ 2 := ite_eq_left ⟨hadj, hiA, hju, hjB⟩
                  have e8 : (if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
                      = p j ^ 2 := ite_eq_left ⟨hadj, hjA, hiu, hAB i hiA⟩
                  have hb : (p i - p j) ^ 2 ≤ p i ^ 2 + p j ^ 2 := by
                    nlinarith only [mul_nonneg (hp i hiA) (hp j hjA)]
                  rw [hxA i hiA, hxA j hjA]
                  linarith
                · -- leak `A → Z`.
                  have e7 : (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
                      = p i ^ 2 := ite_eq_left ⟨hadj, hiA, hju, hjB⟩
                  have hval : (p i - 0) ^ 2 = p i ^ 2 := by ring
                  rw [hxA i hiA, hxZ j hju hjv hjA hjB, hval]
                  linarith
            · by_cases hiB : i ∈ B
              · by_cases hjA : j ∈ A
                · -- cross edge `B → A`.
                  have e6 : (if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
                      = (p j + q i) ^ 2 := ite_eq_left ⟨hadj, hiB, hjA⟩
                  have hval : (-(q i) - p j) ^ 2 = (p j + q i) ^ 2 := by ring
                  rw [hxB i hiB, hxA j hjA, hval]
                  linarith
                · by_cases hjB : j ∈ B
                  · -- internal `B` edge.
                    have e9 : (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
                        = q i ^ 2 := ite_eq_left ⟨hadj, hiB, hjv, hjA⟩
                    have e10 : (if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2
                        else 0) = q j ^ 2 := ite_eq_left ⟨hadj, hjB, hiv, hiA⟩
                    have hb : (-(q i) - -(q j)) ^ 2 ≤ q i ^ 2 + q j ^ 2 := by
                      nlinarith only [mul_nonneg (hq i hiB) (hq j hjB)]
                    rw [hxB i hiB, hxB j hjB]
                    linarith
                  · -- leak `B → Z`.
                    have e9 : (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
                        = q i ^ 2 := ite_eq_left ⟨hadj, hiB, hjv, hjA⟩
                    have hval : (-(q i) - 0) ^ 2 = q i ^ 2 := by ring
                    rw [hxB i hiB, hxZ j hju hjv hjA hjB, hval]
                    linarith
              · by_cases hjA : j ∈ A
                · -- leak `Z → A`.
                  have e8 : (if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
                      = p j ^ 2 := ite_eq_left ⟨hadj, hjA, hiu, hiB⟩
                  have hval : (0 - p j) ^ 2 = p j ^ 2 := by ring
                  rw [hxZ i hiu hiv hiA hiB, hxA j hjA, hval]
                  linarith
                · by_cases hjB : j ∈ B
                  · -- leak `Z → B`.
                    have e10 : (if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2
                        else 0) = q j ^ 2 := ite_eq_left ⟨hadj, hjB, hiv, hiA⟩
                    have hval : (0 - -(q j)) ^ 2 = q j ^ 2 := by ring
                    rw [hxZ i hiu hiv hiA hiB, hxB j hjB, hval]
                    linarith
                  · -- `Z → Z`: zero.
                    rw [hxZ i hiu hiv hiA hiB, hxZ j hju hjv hjA hjB]
                    norm_num
                    linarith
  · rw [ite_eq_right hadj]
    linarith

open Classical in
private theorem algConn_le_two_of_apex_double_star_hC5 : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v g : V) (p q : V → ℝ),
  let A := (G.neighborFinset u).erase g;
  let B := (G.neighborFinset v).erase g;
  (∑ i, ∑ j, if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0) =
    ∑ w ∈ A, ∑ w' ∈ B, if G.Adj w w' then (p w + q w') ^ 2 else 0 := by
  classical
  intro V inst G u v g p q A B
  have h1 : ∀ i j : V, (if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
      = if i ∈ A then (if j ∈ B then (if G.Adj i j then (p i + q j) ^ 2 else 0)
          else 0) else 0 := by
    intro i j
    by_cases h1 : i ∈ A <;> by_cases h2 : j ∈ B <;> by_cases h3 : G.Adj i j <;>
      simp [h1, h2, h3]
  have h2 : ∀ i : V,
      (∑ j, if i ∈ A then (if j ∈ B then (if G.Adj i j then (p i + q j) ^ 2 else 0)
          else 0) else 0)
      = if i ∈ A then (∑ j, if j ∈ B then (if G.Adj i j then (p i + q j) ^ 2 else 0)
          else 0) else 0 := by
    intro i
    by_cases h : i ∈ A <;> simp [h]
  simp_rw [h1, h2]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter]

open Classical in
private theorem algConn_le_two_of_apex_double_star_hC7 : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v g : V) (p : V → ℝ),
  let A := (G.neighborFinset u).erase g;
  let B := (G.neighborFinset v).erase g;
  (∑ i, ∑ j, if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0) =
    ∑ w ∈ A, ↑(G.neighborFinset w \ insert u B).card * p w ^ 2 := by
  classical
  intro V inst G u v g p A B
  have h1 : ∀ i j : V, (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
      = if i ∈ A then (if j ∈ G.neighborFinset i \ insert u B then p i ^ 2 else 0)
          else 0 := by
    intro i j
    have hmem : j ∈ G.neighborFinset i \ insert u B ↔ G.Adj i j ∧ j ≠ u ∧ j ∉ B := by
      simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
        not_or]
    by_cases h1 : i ∈ A <;> by_cases h2 : G.Adj i j ∧ j ≠ u ∧ j ∉ B <;>
      simp [h1, h2, hmem]
  have h2 : ∀ i : V,
      (∑ j, if i ∈ A then (if j ∈ G.neighborFinset i \ insert u B then p i ^ 2 else 0)
          else 0)
      = if i ∈ A then (∑ j, if j ∈ G.neighborFinset i \ insert u B then p i ^ 2 else 0)
          else 0 := by
    intro i
    by_cases h : i ∈ A <;> simp [h]
  simp_rw [h1, h2]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

open Classical in
private theorem algConn_le_two_of_apex_double_star_hC9 : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v g : V) (q : V → ℝ),
  let A := (G.neighborFinset u).erase g;
  let B := (G.neighborFinset v).erase g;
  (∑ i, ∑ j, if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0) =
    ∑ w ∈ B, ↑(G.neighborFinset w \ insert v A).card * q w ^ 2 := by
  classical
  intro V inst G u v g q A B
  have h1 : ∀ i j : V, (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
      = if i ∈ B then (if j ∈ G.neighborFinset i \ insert v A then q i ^ 2 else 0)
          else 0 := by
    intro i j
    have hmem : j ∈ G.neighborFinset i \ insert v A ↔ G.Adj i j ∧ j ≠ v ∧ j ∉ A := by
      simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
        not_or]
    by_cases h1 : i ∈ B <;> by_cases h2 : G.Adj i j ∧ j ≠ v ∧ j ∉ A <;>
      simp [h1, h2, hmem]
  have h2 : ∀ i : V,
      (∑ j, if i ∈ B then (if j ∈ G.neighborFinset i \ insert v A then q i ^ 2 else 0)
          else 0)
      = if i ∈ B then (∑ j, if j ∈ G.neighborFinset i \ insert v A then q i ^ 2 else 0)
          else 0 := by
    intro i
    by_cases h : i ∈ B <;> simp [h]
  simp_rw [h1, h2]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

open Classical in
private theorem algConn_le_two_of_apex_double_star_hC1_step1 : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u g : V) (au : ℝ) (p : V → ℝ),
  let A : Finset V := (G.neighborFinset u).erase g;
  (∑ i, ∑ j, if i = u ∧ j ∈ A then (au - p j) ^ (2 : ℕ) else (0 : ℝ)) = ∑ w ∈ A, (au - p w) ^ (2 :
    ℕ) := by
  classical
  intro V inst G u g au p A
  have h1 : ∀ i j : V, (if i = u ∧ j ∈ A then (au - p j) ^ 2 else 0)
      = if i = u then (if j ∈ A then (au - p j) ^ 2 else 0) else 0 := by
    intro i j
    by_cases h1 : i = u <;> by_cases h2 : j ∈ A <;> simp [h1, h2]
  have h2 : ∀ i : V,
      (∑ j, if i = u then (if j ∈ A then (au - p j) ^ 2 else 0) else 0)
      = if i = u then (∑ j, if j ∈ A then (au - p j) ^ 2 else 0) else 0 := by
    intro i
    by_cases h : i = u <;> simp [h]
  simp_rw [h1, h2]
  rw [Finset.sum_ite_eq' Finset.univ u]
  simp only [Finset.mem_univ, ite_true]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

open Classical in
private theorem algConn_le_two_of_apex_double_star_hC3_step1 : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (v g : V) (av : ℝ) (q : V → ℝ),
  let B : Finset V := (G.neighborFinset v).erase g;
  (∑ i, ∑ j, if i = v ∧ j ∈ B then (av - q j) ^ (2 : ℕ) else (0 : ℝ)) = ∑ w ∈ B, (av - q w) ^ (2 :
    ℕ) := by
  classical
  intro V inst G v g av q B
  have h1 : ∀ i j : V, (if i = v ∧ j ∈ B then (av - q j) ^ 2 else 0)
      = if i = v then (if j ∈ B then (av - q j) ^ 2 else 0) else 0 := by
    intro i j
    by_cases h1 : i = v <;> by_cases h2 : j ∈ B <;> simp [h1, h2]
  have h2 : ∀ i : V,
      (∑ j, if i = v then (if j ∈ B then (av - q j) ^ 2 else 0) else 0)
      = if i = v then (∑ j, if j ∈ B then (av - q j) ^ 2 else 0) else 0 := by
    intro i
    by_cases h : i = v <;> simp [h]
  simp_rw [h1, h2]
  rw [Finset.sum_ite_eq' Finset.univ v]
  simp only [Finset.mem_univ, ite_true]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

open Classical in
private theorem algConn_le_two_of_apex_double_star_hC11_step1 : ∀ {V : Type u_1} [Fintype V] (u g
  : V) (au : ℝ),
  (∑ i, ∑ j, if i = u ∧ j = g then au ^ (2 : ℕ) else (0 : ℝ)) = au ^ (2 : ℕ) := by
  classical
  intro V inst u g au
  have h1 : ∀ i j : V, (if i = u ∧ j = g then au ^ 2 else 0)
      = if i = u then (if j = g then au ^ 2 else 0) else 0 := by
    intro i j
    by_cases h1 : i = u <;> by_cases h2 : j = g <;> simp [h1, h2]
  have h2 : ∀ i : V,
      (∑ j, if i = u then (if j = g then au ^ 2 else 0) else 0)
      = if i = u then (∑ j, if j = g then au ^ 2 else 0) else 0 := by
    intro i
    by_cases h : i = u <;> simp [h]
  simp_rw [h1, h2]
  rw [Finset.sum_ite_eq' Finset.univ u]
  simp only [Finset.mem_univ, ite_true]
  rw [Finset.sum_ite_eq' Finset.univ g fun _ => au ^ 2]
  simp only [Finset.mem_univ, ite_true]

open Classical in
private theorem algConn_le_two_of_apex_double_star_hC13_step1 : ∀ {V : Type u_1} [Fintype V] (v g
  : V) (av : ℝ),
  (∑ i, ∑ j, if i = v ∧ j = g then av ^ (2 : ℕ) else (0 : ℝ)) = av ^ (2 : ℕ) := by
  classical
  intro V inst v g av
  have h1 : ∀ i j : V, (if i = v ∧ j = g then av ^ 2 else 0)
      = if i = v then (if j = g then av ^ 2 else 0) else 0 := by
    intro i j
    by_cases h1 : i = v <;> by_cases h2 : j = g <;> simp [h1, h2]
  have h2 : ∀ i : V,
      (∑ j, if i = v then (if j = g then av ^ 2 else 0) else 0)
      = if i = v then (∑ j, if j = g then av ^ 2 else 0) else 0 := by
    intro i
    by_cases h : i = v <;> simp [h]
  simp_rw [h1, h2]
  rw [Finset.sum_ite_eq' Finset.univ v]
  simp only [Finset.mem_univ, ite_true]
  rw [Finset.sum_ite_eq' Finset.univ g fun _ => av ^ 2]
  simp only [Finset.mem_univ, ite_true]

open Classical in
/-- **The apex double-star master certificate.**  Two vertices `u ≠ v`, not
adjacent, with `g` their **only** common neighbour (the apex, weight `0`), and
nonnegative weights (`au` on `u`, `p w` on `w ∈ N(u) ∖ {g}`; `av`, `q` on the
`v`-side, negated) that are balanced and satisfy the worst-case quadratic-form
bound — the far-pair bound plus the two apex-edge terms `au² + av²`.  Then
`algConn G ≤ 2`. -/
theorem algConn_le_two_of_apex_double_star [Nonempty V]
    (G : SimpleGraph V) (u v g : V) (au av : ℝ) (p q : V → ℝ)
    (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hgu : G.Adj u g) (hgv : G.Adj v g)
    (hcap : ∀ w : V, w ≠ g → ¬(G.Adj u w ∧ G.Adj v w))
    (hau : 0 < au)
    (hp : ∀ w ∈ (G.neighborFinset u).erase g, 0 ≤ p w)
    (hq : ∀ w ∈ (G.neighborFinset v).erase g, 0 ≤ q w)
    (hbal : au + ∑ w ∈ (G.neighborFinset u).erase g, p w
          = av + ∑ w ∈ (G.neighborFinset v).erase g, q w)
    (hQ : au ^ 2 + av ^ 2
        + (∑ w ∈ (G.neighborFinset u).erase g, (au - p w) ^ 2)
        + (∑ w ∈ (G.neighborFinset v).erase g, (av - q w) ^ 2)
        + (∑ w ∈ (G.neighborFinset u).erase g,
            ∑ w' ∈ (G.neighborFinset v).erase g,
            (if G.Adj w w' then (p w + q w') ^ 2 else 0))
        + (∑ w ∈ (G.neighborFinset u).erase g,
            ((G.neighborFinset w \ insert u ((G.neighborFinset v).erase g)).card : ℝ)
              * p w ^ 2)
        + (∑ w ∈ (G.neighborFinset v).erase g,
            ((G.neighborFinset w \ insert v ((G.neighborFinset u).erase g)).card : ℝ)
              * q w ^ 2)
        ≤ 2 * (au ^ 2 + (∑ w ∈ (G.neighborFinset u).erase g, p w ^ 2)
             + (av ^ 2 + ∑ w ∈ (G.neighborFinset v).erase g, q w ^ 2))) :
    algConn G ≤ 2 := by
  classical
  set A := (G.neighborFinset u).erase g with hA
  set B := (G.neighborFinset v).erase g with hB
  -- Membership bookkeeping.
  have hmemA : ∀ w : V, w ∈ A ↔ w ≠ g ∧ G.Adj u w := fun w => by
    rw [hA, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
  have hmemB : ∀ w : V, w ∈ B ↔ w ≠ g ∧ G.Adj v w := fun w => by
    rw [hB, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
  have hug : u ≠ g := G.ne_of_adj hgu
  have hvg : v ≠ g := G.ne_of_adj hgv
  have hgA : g ∉ A := fun h => ((hmemA g).mp h).1 rfl
  have hgB : g ∉ B := fun h => ((hmemB g).mp h).1 rfl
  have huA : u ∉ A := fun h => G.irrefl ((hmemA u).mp h).2
  have hvA : v ∉ A := fun h => huv ((hmemA v).mp h).2
  have huB : u ∉ B := fun h => huv (G.adj_symm ((hmemB u).mp h).2)
  have hvB : v ∉ B := fun h => G.irrefl ((hmemB v).mp h).2
  have hAB : ∀ w : V, w ∈ A → w ∉ B := fun w hwA hwB =>
    hcap w ((hmemA w).mp hwA).1 ⟨((hmemA w).mp hwA).2, ((hmemB w).mp hwB).2⟩
  -- The test vector (the apex `g` gets weight `0`).
  set x : V → ℝ := fun w =>
    ((if w = u then au else 0) + (if w ∈ A then p w else 0))
      - ((if w = v then av else 0) + (if w ∈ B then q w else 0)) with hxdef
  have hxu : x u = au := by simp [hxdef, hne, huA, huB]
  have hxv : x v = -av := by simp [hxdef, hne.symm, hvA, hvB]
  have hxA : ∀ w ∈ A, x w = p w := by
    intro w hw
    have h1 : w ≠ u := fun e => huA (e ▸ hw)
    have h2 : w ≠ v := fun e => hvA (e ▸ hw)
    have h3 : w ∉ B := hAB w hw
    simp [hxdef, h1, h2, hw, h3]
  have hxB : ∀ w ∈ B, x w = -(q w) := by
    intro w hw
    have h1 : w ≠ u := fun e => huB (e ▸ hw)
    have h2 : w ≠ v := fun e => hvB (e ▸ hw)
    have h3 : w ∉ A := fun hwA => hAB w hwA hw
    simp [hxdef, h1, h2, h3, hw]
  have hxZ : ∀ w : V, w ≠ u → w ≠ v → w ∉ A → w ∉ B → x w = 0 := by
    intro w h1 h2 h3 h4
    simp [hxdef, h1, h2, h3, h4]
  have hxg : x g = 0 := hxZ g (Ne.symm hug) (Ne.symm hvg) hgA hgB
  -- Orthogonality to the all-ones vector.
  have hsum0 : ∑ i, x i = 0 := by
    simp only [hxdef]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ u fun _ => au,
      Finset.sum_ite_eq' Finset.univ v fun _ => av,
      Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]
    simp only [Finset.mem_univ, ite_true]
    linarith [hbal]
  -- Nonvanishing.
  have hne0 : ∃ i, x i ≠ 0 := ⟨u, by rw [hxu]; exact ne_of_gt hau⟩
  -- Squared norm.
  have hnorm :=
      algConn_le_two_of_apex_double_star_hnorm (V := V) (G := G) (u := u) (v := v) (g := g)
        (au := au) (av := av) (p := p) (q := q) (hne) (huv) (hgu) (hgv)
        (hcap) (A := A) (hp) (hA) (hq) (hbal) (hQ) (hB) (hmemA) (hmemB) (hug) (hvg) (hgA) (hgB)
        (huA) (hvA) (huB) (hvB) (hAB) (hxdef) (hxu) (hxv) (hxA) (hxB) (hxZ) (hxg) (hsum0) (hne0)
  -- Per-ordered-pair upper bound: the ten far-pair classes plus four apex
  -- classes (the centre classes are keyed to `A`/`B` membership, so an edge
  -- from `u` to `g` falls through to the apex class).
  have hterm :=
      algConn_le_two_of_apex_double_star_hterm (V := V) (G := G) (u := u) (v := v) (g := g)
        (au := au) (av := av) (p := p) (q := q) (hau) (hp) (hq) (hmemA)
        (hmemB) (hAB) (hxu) (hxv) (hxA) (hxB) (hxZ) (hxg)
  -- Count lemma: `u`-centre edges into `A`.
  have hC1 :=
      algConn_le_two_of_apex_double_star_hC1_step1 (V := V) (G := G) (u := u) (g := g) (au :=
        au) (p := p)
  have hC2 : (∑ i, ∑ j, if j = u ∧ i ∈ A then (au - p i) ^ 2 else 0)
      = ∑ w ∈ A, (au - p w) ^ 2 := by
    rw [Finset.sum_comm]
    exact hC1
  -- Count lemma: `v`-centre edges into `B`.
  have hC3 :=
      algConn_le_two_of_apex_double_star_hC3_step1 (V := V) (G := G) (v := v) (g := g) (av :=
        av) (q := q)
  have hC4 : (∑ i, ∑ j, if j = v ∧ i ∈ B then (av - q i) ^ 2 else 0)
      = ∑ w ∈ B, (av - q w) ^ 2 := by
    rw [Finset.sum_comm]
    exact hC3
  -- Count lemma: cross edges.
  have hC5 :=
      algConn_le_two_of_apex_double_star_hC5 (V := V) (G := G) (u := u) (v := v) (g := g) (p
        := p) (q := q)
  have hC6 : (∑ i, ∑ j, if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
      = ∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0) := by
    rw [← hC5, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
    tauto
  -- Count lemma: `A` leak slots.
  have hC7 :=
      algConn_le_two_of_apex_double_star_hC7 (V := V) (G := G) (u := u) (v := v) (g := g) (p
        := p)
  have hC8 : (∑ i, ∑ j, if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
      = ∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2 := by
    rw [← hC7, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
  -- Count lemma: `B` leak slots.
  have hC9 :=
      algConn_le_two_of_apex_double_star_hC9 (V := V) (G := G) (u := u) (v := v) (g := g) (q
        := q)
  have hC10 : (∑ i, ∑ j, if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)
      = ∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2 := by
    rw [← hC9, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
  -- Count lemma: the four apex classes each collapse to a single slot.
  have hC11 := algConn_le_two_of_apex_double_star_hC11_step1 (V := V) (u := u) (g := g) (au := au)
  have hC12 : (∑ i, ∑ j, if j = u ∧ i = g then au ^ 2 else 0) = au ^ 2 := by
    rw [Finset.sum_comm]
    exact hC11
  have hC13 := algConn_le_two_of_apex_double_star_hC13_step1 (V := V) (v := v) (g := g) (av := av)
  have hC14 : (∑ i, ∑ j, if j = v ∧ i = g then av ^ 2 else 0) = av ^ 2 := by
    rw [Finset.sum_comm]
    exact hC13
  -- Assemble the ordered-pair bound.
  have hsum_bound : (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0)
      ≤ 2 * (au ^ 2 + av ^ 2
        + (∑ w ∈ A, (au - p w) ^ 2) + (∑ w ∈ B, (av - q w) ^ 2)
        + (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
        + (∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2)
        + (∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2)) := by
    calc (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0)
        ≤ ∑ i, ∑ j,
            ((if i = u ∧ j ∈ A then (au - p j) ^ 2 else 0)
          + (if j = u ∧ i ∈ A then (au - p i) ^ 2 else 0)
          + (if i = v ∧ j ∈ B then (av - q j) ^ 2 else 0)
          + (if j = v ∧ i ∈ B then (av - q i) ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
          + (if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
          + (if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)
          + (if i = u ∧ j = g then au ^ 2 else 0)
          + (if j = u ∧ i = g then au ^ 2 else 0)
          + (if i = v ∧ j = g then av ^ 2 else 0)
          + (if j = v ∧ i = g then av ^ 2 else 0)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = 2 * (au ^ 2 + av ^ 2
            + (∑ w ∈ A, (au - p w) ^ 2) + (∑ w ∈ B, (av - q w) ^ 2)
            + (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
            + (∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2)
            + (∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2)) := by
          simp_rw [Finset.sum_add_distrib]
          rw [hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14]
          ring
  -- Conclude via the universal test-vector certificate.
  apply algConn_le_two_of_testvector G x hsum0 hne0
  rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂', hnorm]
  linarith [hsum_bound, hQ]

open Classical in
/-- **The apex-tie twin law.**  Two degree-3 vertices `u ≠ v`, non-adjacent,
with common neighbour `g` (of **any** degree) and no other common neighbour;
all other neighbours (*partners*) of `u` and of `v` have degree `≤ 4`; and
there is no edge between the two partner sides.  Then `algConn G ≤ 2` — the
apex double star at `au = av = 1`, `p = q ≡ ½` sits at the **exact tie**
`num = 2·norm`. -/
theorem algConn_le_two_of_apex_twin_pair [Nonempty V]
    (G : SimpleGraph V) (u v g : V)
    (hu3 : G.degree u = 3) (hv3 : G.degree v = 3)
    (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hgu : G.Adj u g) (hgv : G.Adj v g)
    (hcap : ∀ w : V, w ≠ g → ¬(G.Adj u w ∧ G.Adj v w))
    (hpart : ∀ w : V, G.Adj u w → w ≠ g → G.degree w ≤ 4)
    (hpart' : ∀ w : V, G.Adj v w → w ≠ g → G.degree w ≤ 4)
    (hcross : ∀ w w' : V, G.Adj u w → w ≠ g → G.Adj v w' → w' ≠ g →
      ¬G.Adj w w') :
    algConn G ≤ 2 := by
  classical
  set A := (G.neighborFinset u).erase g with hA
  set B := (G.neighborFinset v).erase g with hB
  have hgu' : g ∈ G.neighborFinset u := (G.mem_neighborFinset u g).mpr hgu
  have hgv' : g ∈ G.neighborFinset v := (G.mem_neighborFinset v g).mpr hgv
  have hcardA : A.card = 2 := by
    rw [hA, Finset.card_erase_of_mem hgu',
      SimpleGraph.card_neighborFinset_eq_degree, hu3]
  have hcardB : B.card = 2 := by
    rw [hB, Finset.card_erase_of_mem hgv',
      SimpleGraph.card_neighborFinset_eq_degree, hv3]
  -- constant weight ½ on both partner sides
  set p : V → ℝ := fun _ => 1 / 2 with hp_def
  refine algConn_le_two_of_apex_double_star G u v g 1 1 p p hne huv hgu hgv hcap
    (by norm_num) (fun w _ => by rw [hp_def]; norm_num)
    (fun w _ => by rw [hp_def]; norm_num) ?_ ?_
  · -- balance
    rw [← hA, ← hB]
    have h1 : ∑ w ∈ A, p w = 1 := by
      rw [hp_def, Finset.sum_const, hcardA]
      norm_num
    have h2 : ∑ w ∈ B, p w = 1 := by
      rw [hp_def, Finset.sum_const, hcardB]
      norm_num
    rw [h1, h2]
  · -- the quadratic bound: exact tie `≤ 6`
    rw [← hA, ← hB]
    -- sums of squares
    have hsum_p2 : ∑ w ∈ A, p w ^ 2 = 1 / 2 := by
      rw [hp_def, Finset.sum_const, hcardA]
      norm_num
    have hsum_q2 : ∑ w ∈ B, p w ^ 2 = 1 / 2 := by
      rw [hp_def, Finset.sum_const, hcardB]
      norm_num
    have hsum_1p : ∑ w ∈ A, ((1 : ℝ) - p w) ^ 2 = 1 / 2 := by
      rw [hp_def, Finset.sum_const, hcardA]
      norm_num
    have hsum_1q : ∑ w ∈ B, ((1 : ℝ) - p w) ^ 2 = 1 / 2 := by
      rw [hp_def, Finset.sum_const, hcardB]
      norm_num
    -- cross sum vanishes
    have hcr : (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + p w') ^ 2 else 0))
        = 0 := by
      refine Finset.sum_eq_zero (fun w hw => Finset.sum_eq_zero (fun w' hw' => ?_))
      rw [ite_eq_right]
      exact hcross w w'
        ((G.mem_neighborFinset u w).mp (Finset.mem_of_mem_erase (hA ▸ hw)))
        (Finset.ne_of_mem_erase (hA ▸ hw))
        ((G.mem_neighborFinset v w').mp (Finset.mem_of_mem_erase (hB ▸ hw')))
        (Finset.ne_of_mem_erase (hB ▸ hw'))
    -- leak sums: each partner has degree ≤ 4 and `u` (resp. `v`) among its
    -- neighbours, so at most 3 leak slots at (½)² each
    have hleakA : (∑ w ∈ A,
        ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2) ≤ 3 / 2 := by
      have hpt : ∀ w ∈ A,
          ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2 ≤ 3 / 4 := by
        intro w hw
        have hwA : w ∈ (G.neighborFinset u).erase g := hA ▸ hw
        have hwadj : G.Adj u w :=
          (G.mem_neighborFinset u w).mp (Finset.mem_of_mem_erase hwA)
        have hdeg : G.degree w ≤ 4 := hpart w hwadj (Finset.ne_of_mem_erase hwA)
        have huw : u ∈ G.neighborFinset w := (G.mem_neighborFinset w u).mpr hwadj.symm
        have hsub : G.neighborFinset w \ insert u B ⊆ (G.neighborFinset w).erase u := by
          intro z hz
          rw [Finset.mem_sdiff] at hz
          rw [Finset.mem_erase]
          exact ⟨fun h => hz.2 (h ▸ Finset.mem_insert_self u B), hz.1⟩
        have hc : (G.neighborFinset w \ insert u B).card ≤ 3 := by
          calc (G.neighborFinset w \ insert u B).card
              ≤ ((G.neighborFinset w).erase u).card := Finset.card_le_card hsub
            _ = (G.neighborFinset w).card - 1 := Finset.card_erase_of_mem huw
            _ ≤ 3 := by
                rw [SimpleGraph.card_neighborFinset_eq_degree]
                omega
        have hcR : ((G.neighborFinset w \ insert u B).card : ℝ) ≤ 3 := by
          exact_mod_cast hc
        have hc0 : (0:ℝ) ≤ ((G.neighborFinset w \ insert u B).card : ℝ) :=
          Nat.cast_nonneg _
        rw [hp_def]
        nlinarith only [hcR, hc0]
      calc (∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2)
          ≤ ∑ _w ∈ A, (3 / 4 : ℝ) := Finset.sum_le_sum hpt
        _ = 3 / 2 := by rw [Finset.sum_const, hcardA]; norm_num
    have hleakB : (∑ w ∈ B,
        ((G.neighborFinset w \ insert v A).card : ℝ) * p w ^ 2) ≤ 3 / 2 := by
      have hpt : ∀ w ∈ B,
          ((G.neighborFinset w \ insert v A).card : ℝ) * p w ^ 2 ≤ 3 / 4 := by
        intro w hw
        have hwB : w ∈ (G.neighborFinset v).erase g := hB ▸ hw
        have hwadj : G.Adj v w :=
          (G.mem_neighborFinset v w).mp (Finset.mem_of_mem_erase hwB)
        have hdeg : G.degree w ≤ 4 := hpart' w hwadj (Finset.ne_of_mem_erase hwB)
        have hvw : v ∈ G.neighborFinset w := (G.mem_neighborFinset w v).mpr hwadj.symm
        have hsub : G.neighborFinset w \ insert v A ⊆ (G.neighborFinset w).erase v := by
          intro z hz
          rw [Finset.mem_sdiff] at hz
          rw [Finset.mem_erase]
          exact ⟨fun h => hz.2 (h ▸ Finset.mem_insert_self v A), hz.1⟩
        have hc : (G.neighborFinset w \ insert v A).card ≤ 3 := by
          calc (G.neighborFinset w \ insert v A).card
              ≤ ((G.neighborFinset w).erase v).card := Finset.card_le_card hsub
            _ = (G.neighborFinset w).card - 1 := Finset.card_erase_of_mem hvw
            _ ≤ 3 := by
                rw [SimpleGraph.card_neighborFinset_eq_degree]
                omega
        have hcR : ((G.neighborFinset w \ insert v A).card : ℝ) ≤ 3 := by
          exact_mod_cast hc
        have hc0 : (0:ℝ) ≤ ((G.neighborFinset w \ insert v A).card : ℝ) :=
          Nat.cast_nonneg _
        rw [hp_def]
        nlinarith only [hcR, hc0]
      calc (∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * p w ^ 2)
          ≤ ∑ _w ∈ B, (3 / 4 : ℝ) := Finset.sum_le_sum hpt
        _ = 3 / 2 := by rw [Finset.sum_const, hcardB]; norm_num
    rw [hsum_p2, hsum_q2, hsum_1p, hsum_1q, hcr, one_pow]
    linarith [hleakA, hleakB]

end ACMax
