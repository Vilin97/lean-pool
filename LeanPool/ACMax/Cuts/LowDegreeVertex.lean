/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import LeanPool.ACMax.Spectral.AlgConn
import LeanPool.ACMax.Spectral.RayleighUpper
import LeanPool.ACMax.Spectral.TestVector

/-!
# A single low-degree vertex already forces `algConn ≤ 2`

If `G` has a vertex `u` of degree `≤ 2` and there is at least one vertex outside
`{u} ∪ N(u)`, then `algConn G ≤ 2`.

Certificate: with `C := N(u)` (`|C| = deg u ≤ 2`) and `T := V ∖ ({u} ∪ C)`, take
`x := |T|·e_u − 𝟙_T`.  Then `∑ x = 0`, `∑ x² = |T|² + |T|`, and the only edges that
contribute to the Laplacian form are the `deg u` edges `u`–`C` (each `|T|²`) and the
`T`–`C` edges (each `1`); there are no `u`–`T` edges.  Since every vertex of `T` meets
at most `|C| ≤ 2` vertices of `C`, the `T`–`C` edge count is `≤ 2|T|`, so
`xᵀ L x = deg u · |T|² + e(T,C) ≤ 2|T|² + 2|T| = 2 ∑ x²`.

This closes every `n ≤ 7` instance of the conjecture: `m = 2(n-2) < 3n/2` for `n ≤ 7`
forces a vertex of degree `≤ 2`.  The open core is exactly the graphs with minimum
degree `≥ 3` (possible only for `n ≥ 8`).
-/

namespace ACMax

open Matrix

open Classical in
/-- If `G` has a vertex of degree `≤ 2` with a vertex outside its closed neighborhood,
then `algConn G ≤ 2`. -/
theorem algConn_le_two_of_low_degree_vertex {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (u : V) (hdeg : G.degree u ≤ 2)
    (hT : (Finset.univ \ insert u (G.neighborFinset u)).Nonempty) :
    algConn G ≤ 2 := by
  classical
  set C : Finset V := G.neighborFinset u with hCdef
  set T : Finset V := Finset.univ \ insert u C with hTdef
  set t : ℕ := T.card with htdef
  have htpos : 0 < t := by rw [htdef]; exact hT.card_pos
  -- membership facts for the three blocks {u}, C, T
  have huC : u ∉ C := by simp [hCdef]
  have huT : u ∉ T := by rw [hTdef]; simp
  have hT_not_C : ∀ w ∈ T, w ∉ C := by
    intro w hw
    rw [hTdef, Finset.mem_sdiff, Finset.mem_insert, not_or] at hw
    exact hw.2.2
  have hT_ne_u : ∀ w ∈ T, w ≠ u := by
    intro w hw
    rw [hTdef, Finset.mem_sdiff, Finset.mem_insert, not_or] at hw
    exact hw.2.1
  -- the test vector x = t·e_u − 𝟙_T
  set x : V → ℝ := fun w => (if w = u then (t : ℝ) else 0) - (if w ∈ T then 1 else 0) with hxdef
  have hxu : x u = t := by simp [hxdef, huT]
  have hxT : ∀ w ∈ T, x w = -1 := by
    intro w hw
    simp [hxdef, hT_ne_u w hw, hw]
  have hxC : ∀ w ∈ C, x w = 0 := by
    intro w hw
    have hwu : w ≠ u := fun h => huC (h ▸ hw)
    have hwT : w ∉ T := fun h => hT_not_C w h hw
    simp [hxdef, hwu, hwT]
  -- (1) ∑ x = 0
  have hx0 : ∑ i, x i = 0 := by
    have h1 : ∑ i, (if i = u then (t : ℝ) else 0) = t := by
      rw [Finset.sum_ite_eq' Finset.univ u (fun _ => (t : ℝ))]; simp
    have h2 : ∑ i, (if i ∈ T then (1 : ℝ) else 0) = t := by
      rw [Finset.sum_ite_mem Finset.univ T (fun _ => (1 : ℝ)), Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul, mul_one, htdef]
    simp only [hxdef, Finset.sum_sub_distrib]
    rw [h1, h2]; ring
  -- (2) ∃ i, x i ≠ 0
  have htne : (t : ℝ) ≠ 0 := by
    have : t ≠ 0 := by omega
    exact_mod_cast this
  have hxne : ∃ i, x i ≠ 0 := ⟨u, by rw [hxu]; exact htne⟩
  -- norm: ∑ x² = t² + t
  have hsq : ∑ i, (x i) ^ 2 = (t : ℝ) ^ 2 + t := by
    have hpt : ∀ i, (x i) ^ 2 = (if i = u then (t : ℝ) ^ 2 else 0) + (if i ∈ T then 1 else 0) := by
      intro i
      by_cases hiu : i = u
      · subst hiu; rw [hxu]; simp [huT]
      · by_cases hiT : i ∈ T
        · rw [hxT i hiT]; simp [hiu, hiT]
        · have hxi : x i = 0 := by simp [hxdef, hiu, hiT]
          rw [hxi]; simp [hiu, hiT]
    simp only [hpt, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' Finset.univ u (fun _ => (t : ℝ) ^ 2),
      Finset.sum_ite_mem Finset.univ T (fun _ => (1 : ℝ)), Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, mul_one, htdef]
    simp
  -- per-vertex bound for the T block
  have hterm : ∀ v ∈ T, (G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w ≤ 2 := by
    intro v hv
    have huNv : u ∉ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      intro hadj
      have hvC : v ∈ C := by rw [hCdef, SimpleGraph.mem_neighborFinset]; exact hadj.symm
      exact hT_not_C v hv hvC
    have hsum1 : ∑ w ∈ G.neighborFinset v, (if w = u then (t : ℝ) else 0) = 0 := by
      rw [Finset.sum_ite_eq' (G.neighborFinset v) u (fun _ => (t : ℝ))]; simp [huNv]
    have hsum2 : ∑ w ∈ G.neighborFinset v, x w = -((G.neighborFinset v ∩ T).card : ℝ) := by
      simp only [hxdef, Finset.sum_sub_distrib]
      rw [hsum1, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]; ring
    rw [hsum2]
    have hcard : (G.neighborFinset v ∩ T).card + (G.neighborFinset v \ T).card = G.degree v := by
      rw [Finset.card_inter_add_card_sdiff, SimpleGraph.card_neighborFinset_eq_degree]
    have hsub : G.neighborFinset v \ T ⊆ C := by
      intro w hw
      rw [Finset.mem_sdiff] at hw
      have hwu : w ≠ u := by rintro rfl; exact huNv hw.1
      have hwins : w ∈ insert u C := by
        by_contra hc
        exact hw.2 (by rw [hTdef, Finset.mem_sdiff]; exact ⟨Finset.mem_univ w, hc⟩)
      rw [Finset.mem_insert] at hwins
      rcases hwins with h | h
      · exact absurd h hwu
      · exact h
    have hCle2 : C.card ≤ 2 := by rw [hCdef, SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg
    have hb : ((G.neighborFinset v \ T).card : ℝ) ≤ 2 := by
      exact_mod_cast le_trans (Finset.card_le_card hsub) hCle2
    have hcardR : ((G.neighborFinset v ∩ T).card : ℝ) + ((G.neighborFinset v \ T).card : ℝ)
        = (G.degree v : ℝ) := by exact_mod_cast hcard
    linarith
  -- (3) the quadratic form, expanded then bounded
  have hexp : dotProduct x ((G.lapMatrix ℝ).mulVec x)
      = (G.degree u : ℝ) * (t : ℝ) ^ 2
        + ∑ v ∈ T, ((G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w) := by
    have e0 : dotProduct x ((G.lapMatrix ℝ).mulVec x)
        = ∑ v, x v * ((G.degree v : ℝ) * x v - ∑ w ∈ G.neighborFinset v, x w) := by
      simp only [dotProduct, SimpleGraph.lapMatrix_mulVec_apply]
    have hgu : x u * ((G.degree u : ℝ) * x u - ∑ w ∈ G.neighborFinset u, x w)
        = (G.degree u : ℝ) * (t : ℝ) ^ 2 := by
      have hzero : ∑ w ∈ G.neighborFinset u, x w = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        rw [← hCdef] at hw
        exact hxC w hw
      rw [hzero, hxu]; ring
    have hCsum : ∑ v ∈ C, x v * ((G.degree v : ℝ) * x v - ∑ w ∈ G.neighborFinset v, x w) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [hxC v hv]; ring
    have hTg : ∑ v ∈ T, x v * ((G.degree v : ℝ) * x v - ∑ w ∈ G.neighborFinset v, x w)
        = ∑ v ∈ T, ((G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hxT v hv]; ring
    rw [e0, ← Finset.sum_sdiff (Finset.subset_univ (insert u C)), ← hTdef,
      Finset.sum_insert huC, hgu, hCsum, hTg]
    ring
  have hTbound : ∑ v ∈ T, ((G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w) ≤ 2 * t := by
    calc ∑ v ∈ T, ((G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w)
        ≤ ∑ _v ∈ T, (2 : ℝ) := Finset.sum_le_sum hterm
      _ = 2 * t := by rw [Finset.sum_const, nsmul_eq_mul, htdef]; ring
  have hQ : dotProduct x ((G.lapMatrix ℝ).mulVec x) ≤ 2 * ∑ i, (x i) ^ 2 := by
    rw [hsq, hexp]
    have hdu : (G.degree u : ℝ) ≤ 2 := by exact_mod_cast hdeg
    nlinarith [hTbound, mul_le_mul_of_nonneg_right hdu (sq_nonneg (t : ℝ))]
  exact algConn_le_two_of_testvector G x hx0 hxne hQ

open Classical in
/-- On `Fin n` with `n ≥ 4`, the complement of the closed neighborhood of a
vertex of degree at most `2` is automatically nonempty. -/
theorem algConn_le_two_of_degree_le_two {n : ℕ} [Nonempty (Fin n)] (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n)) (u : Fin n) (hdeg : G.degree u ≤ 2) :
    algConn G ≤ 2 := by
  let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
  rw [Finset.sdiff_nonempty]
  intro hsub
  have hle : (Finset.univ : Finset (Fin n)).card ≤
      (insert u (G.neighborFinset u)).card := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hle
  have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
    calc
      (insert u (G.neighborFinset u)).card ≤ (G.neighborFinset u).card + 1 :=
        Finset.card_insert_le _ _
      _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ 3 := by omega
  omega

end ACMax
