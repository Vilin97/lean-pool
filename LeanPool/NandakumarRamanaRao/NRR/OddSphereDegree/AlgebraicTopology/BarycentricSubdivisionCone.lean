/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricBoundaryCancellation
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionChainMap
import Mathlib.Tactic
import Mathlib.Topology.GDelta.MetrizableSpace

/-! # Barycentric Subdivision Cone -/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-! ## 1. The normalized tail of a point of `Δᵏ⁺¹` -/

/-- Normalize the non-apex barycentric coordinates by their total mass. -/
noncomputable def coneTailFun {k : ℕ} (x : Delta (k + 1)) : Fin (k + 1) → ℝ :=
  fun i => (x : Fin (k + 1 + 1) → ℝ) i.succ / (1 - (x : Fin (k + 1 + 1) → ℝ) 0)

theorem coneTailFun_mem {k : ℕ} (x : Delta (k + 1))
    (hx : (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) :
    coneTailFun x ∈ stdSimplex ℝ (Fin (k + 1)) := by
  refine' ⟨fun i => _, _⟩
  · exact div_nonneg (x.2.1 _) (sub_nonneg.2 (x.2.2 ▸ Finset.single_le_sum (fun a _ => x.2.1 a) (Finset.mem_univ 0)))
  · have hxsum : (x : Fin (k + 1 + 1) → ℝ) 0 + ∑ i : Fin (k + 1), (x : Fin (k + 1 + 1) → ℝ) i.succ = 1 := by
      have h := x.2.2
      rw [Fin.sum_univ_succ] at h
      exact h
    have h_sum : ∑ i : Fin (k + 1), (x : Fin (k + 1 + 1) → ℝ) i.succ = 1 - (x : Fin (k + 1 + 1) → ℝ) 0 :=
      eq_sub_of_add_eq' hxsum
    unfold coneTailFun
    rw [← Finset.sum_div, h_sum, div_self (sub_ne_zero_of_ne (Ne.symm hx))]

/-- The normalized base point of a cone simplex, choosing the first vertex at the apex. -/
noncomputable def coneTail {k : ℕ} (x : Delta (k + 1)) : Delta k :=
  if h : (x : Fin (k + 1 + 1) → ℝ) 0 = 1 then stdSimplex.vertex (0 : Fin (k + 1))
  else ⟨coneTailFun x, coneTailFun_mem x h⟩

theorem coneTail_apply {k : ℕ} (x : Delta (k + 1))
    (hx : (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) (i : Fin (k + 1)) :
    (coneTail x : Fin (k + 1) → ℝ) i
      = (x : Fin (k + 1 + 1) → ℝ) i.succ / (1 - (x : Fin (k + 1 + 1) → ℝ) 0) := by
  unfold coneTail
  split_ifs with h
  · contradiction
  · rfl

/-! ## 2. The affine cone map -/

/-- Barycentric coordinates of the cone from a vertex over a simplex map. -/
noncomputable def affineConeMapFun {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) : Fin (n + 1) → ℝ :=
  fun j => (x : Fin (k + 1 + 1) → ℝ) 0 * (v : Fin (n + 1) → ℝ) j
      + (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j

theorem affineConeMapFun_mem {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) : affineConeMapFun v τ x ∈ stdSimplex ℝ (Fin (n + 1)) := by
  refine' ⟨fun j => _, _⟩
  · exact add_nonneg (mul_nonneg (stdSimplex.zero_le x 0) (stdSimplex.zero_le v j))
      (mul_nonneg (sub_nonneg.mpr (stdSimplex.le_one x 0)) (stdSimplex.zero_le (τ (coneTail x)) j))
  · unfold affineConeMapFun
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, stdSimplex.sum_eq_one]
    ring

/-- The simplex map obtained by coning a given map to the chosen vertex. -/
noncomputable def affineConeMap {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    Delta (k + 1) → Delta n :=
  fun x => ⟨affineConeMapFun v τ x, affineConeMapFun_mem v τ x⟩

@[simp] theorem affineConeMap_coord {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) (j : Fin (n + 1)) :
    (affineConeMap v τ x : Fin (n + 1) → ℝ) j
      = (x : Fin (k + 1 + 1) → ℝ) 0 * (v : Fin (n + 1) → ℝ) j
        + (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j := rfl

/-! ## 3. Vertex formulas -/

theorem affineConeMap_vertex_zero {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    affineConeMap v τ (stdSimplex.vertex (0 : Fin (k + 1 + 1))) = v := by
  ext j
  simp [stdSimplex.vertex]

theorem affineConeMap_vertex_succ {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (i : Fin (k + 1)) :
    affineConeMap v τ (stdSimplex.vertex i.succ) = τ (stdSimplex.vertex i) := by
  ext j
  have h_ne : (stdSimplex.vertex (S := ℝ) i.succ : Fin (k + 1 + 1) → ℝ) 0 ≠ 1 := by
    change (Pi.single i.succ (1 : ℝ) : Fin (k + 1 + 1) → ℝ) 0 ≠ 1
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm]
    norm_num
  have h_zero : (stdSimplex.vertex (S := ℝ) i.succ : Fin (k + 1 + 1) → ℝ) 0 = 0 := by
    change (Pi.single i.succ (1 : ℝ) : Fin (k + 1 + 1) → ℝ) 0 = 0
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm]
  rw [affineConeMap_coord, h_zero]
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  have h_tail : coneTail (stdSimplex.vertex i.succ) = stdSimplex.vertex i := by
    apply Subtype.ext
    ext m
    have h_app := coneTail_apply (stdSimplex.vertex i.succ) h_ne m
    change (coneTail (stdSimplex.vertex i.succ) : Fin (k + 1) → ℝ) m = (Pi.single i (1 : ℝ) : Fin (k + 1) → ℝ) m
    rw [h_app, h_zero, sub_zero, div_one]
    change (Pi.single i.succ (1 : ℝ) : Fin (k + 1 + 1) → ℝ) m.succ = (Pi.single i (1 : ℝ) : Fin (k + 1) → ℝ) m
    rw [Pi.single_apply, Pi.single_apply]
    simp [Fin.succ_inj]
  rw [h_tail]

/-! ## 4. Continuity and bundled continuous cone map -/

theorem continuousOn_coneTail {k : ℕ} :
    ContinuousOn (coneTail (k := k)) {x | (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1} := by
  set S : Set (Delta (k + 1)) := {x | (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1}
  have h_cont_tail : ContinuousOn (fun x : Delta (k + 1) => (coneTail x : Fin (k + 1) → ℝ)) S := by
    refine ContinuousOn.congr ?_ (fun x hx => funext (fun i => coneTail_apply x hx i))
    exact continuousOn_pi.mpr fun i =>
      ContinuousOn.div (continuous_apply _ |>.comp continuous_subtype_val |>.continuousOn)
        (continuousOn_const.sub (continuous_apply 0 |>.comp continuous_subtype_val |>.continuousOn))
        fun x hx => sub_ne_zero_of_ne (Ne.symm hx)
  rw [continuousOn_iff_continuous_domRestrict] at *
  exact continuous_induced_rng.mpr h_cont_tail

theorem continuous_affineConeMap {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n)) :
    Continuous (affineConeMap v (⇑τ)) := by
  refine continuous_induced_rng.mpr ?_
  refine continuous_pi fun j => ?_
  have hB_cont : Continuous (fun x : Delta (k + 1) => (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j) := by
    refine continuous_iff_continuousAt.mpr ?_
    intro x
    by_cases hx : (x : Fin (k + 1 + 1) → ℝ) 0 = 1
    · refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
      have hlim : Filter.Tendsto (fun e : Delta (k + 1) => abs (1 - (e : Fin (k + 1 + 1) → ℝ) 0)) (nhds x) (nhds 0) := by
        have h_cont : Continuous (fun e : Delta (k + 1) => abs (1 - (e : Fin (k + 1 + 1) → ℝ) 0)) :=
          Continuous.abs (continuous_const.sub (continuous_apply 0 |>.comp continuous_subtype_val))
        have := h_cont.continuousAt (x := x)
        dsimp [ContinuousAt] at this
        have hx0 : abs (1 - (x : Fin (k + 1 + 1) → ℝ) 0) = 0 := by simp [hx]
        rw [hx0] at this
        exact this
      refine squeeze_zero (fun _ => norm_nonneg _) (fun e => ?_) hlim
      have htau_le1 : abs (((τ (coneTail e)) : Fin (n + 1) → ℝ) j) ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [stdSimplex.zero_le (τ (coneTail e)) j], by linarith [stdSimplex.le_one (τ (coneTail e)) j]⟩
      have hx0_le : 0 ≤ abs (1 - (e : Fin (k + 1 + 1) → ℝ) 0) := abs_nonneg _
      have h_prod : abs (1 - (e : Fin (k + 1 + 1) → ℝ) 0) * abs (((τ (coneTail e)) : Fin (n + 1) → ℝ) j) ≤ abs (1 - (e : Fin (k + 1 + 1) → ℝ) 0) * 1 :=
        mul_le_mul_of_nonneg_left htau_le1 hx0_le
      rw [mul_one] at h_prod
      have hx_val : (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j = 0 := by simp [hx]
      show ‖(1 - (e : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail e)) : Fin (n + 1) → ℝ) j - (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j‖ ≤ abs (1 - (e : Fin (k + 1 + 1) → ℝ) 0)
      rw [hx_val, sub_zero, Real.norm_eq_abs, abs_mul]
      exact h_prod
    · refine ContinuousAt.mul ?_ ?_
      · exact ContinuousAt.sub continuousAt_const (continuous_apply 0 |>.comp continuous_subtype_val |>.continuousAt)
      · have h_tail_at := continuousOn_coneTail.continuousAt (IsOpen.mem_nhds (isOpen_compl_singleton.preimage (continuous_apply 0 |>.comp continuous_subtype_val)) hx)
        have h_tau_at := τ.continuous.continuousAt (x := coneTail x)
        have h_eval := (continuous_apply j |>.comp continuous_subtype_val).continuousAt (x := τ (coneTail x))
        exact (h_eval.comp h_tau_at).comp h_tail_at
  have hA_cont : Continuous (fun x : Delta (k + 1) => (x : Fin (k + 1 + 1) → ℝ) 0 * (v : Fin (n + 1) → ℝ) j) :=
    (continuous_apply 0 |>.comp continuous_subtype_val).mul continuous_const
  exact hA_cont.add hB_cont

/-- The affine cone construction bundled as a continuous map. -/
noncomputable def affineConeContinuousMap {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n)) :
    C(Delta (k + 1), Delta n) :=
  ⟨affineConeMap v (⇑τ), continuous_affineConeMap v τ⟩

@[simp] theorem affineConeContinuousMap_apply {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n))
    (x : Delta (k + 1)) : affineConeContinuousMap v τ x = affineConeMap v (⇑τ) x := rfl

/-! ## 5. Face formulas -/

theorem cone_face_zero {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    (fun y : Delta k => affineConeMap v τ (cofaceTop k 0 y)) = τ := by
  funext y
  have h0 : (cofaceTop k 0 y : Fin (k + 1 + 1) → ℝ) 0 = 0 := cofaceTop_apply_base k 0 y
  have h_ne : (cofaceTop k 0 y : Fin (k + 1 + 1) → ℝ) 0 ≠ 1 := by rw [h0]; norm_num
  apply Subtype.ext
  ext j
  show (affineConeMap v τ (cofaceTop k 0 y) : Fin (n + 1) → ℝ) j = (τ y : Fin (n + 1) → ℝ) j
  rw [affineConeMap_coord, h0]
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  have h_tail : coneTail (cofaceTop k 0 y) = y := by
    apply Subtype.ext
    ext m
    have h_app := coneTail_apply (cofaceTop k 0 y) h_ne m
    show (coneTail (cofaceTop k 0 y) : Fin (k + 1) → ℝ) m = y.1 m
    rw [h_app, h0, sub_zero, div_one]
    show (cofaceTop k 0 y : Fin (k + 1 + 1) → ℝ) m.succ = y m
    show (stdSimplex.map (S := ℝ) (Fin.succAbove 0) y : Fin (k + 1 + 1) → ℝ) m.succ = y m
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Fin.succAbove_zero]
    rw [Finset.sum_eq_single m]
    · intro b hb hbm
      exact (hbm (Fin.succ_injective _ (Finset.mem_filter.mp hb).2)).elim
    · intro h
      exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
  rw [h_tail]

theorem coneTail_cofaceTop_succ {k : ℕ} (j : Fin (k + 1 + 1)) (y : Delta (k + 1))
    (hy : (y : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) :
    coneTail (cofaceTop (k + 1) j.succ y) = cofaceTop k j (coneTail y) := by
  have h0 : (cofaceTop (k + 1) j.succ y : Fin (k + 1 + 1 + 1) → ℝ) 0 = (y : Fin (k + 1 + 1) → ℝ) 0 := by
    show (stdSimplex.map (S := ℝ) (Fin.succAbove j.succ) y : Fin (k + 1 + 1 + 1) → ℝ) 0 = y 0
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hj0 : (j.succ : Fin (k + 1 + 1 + 1)).succAbove 0 = 0 := by
      rw [Fin.succAbove_of_castSucc_lt]
      rfl
      exact Fin.succ_pos j
    rw [Finset.sum_eq_single 0]
    · intro b hb hb0
      have : (j.succ : Fin (k + 1 + 1 + 1)).succAbove b = 0 := (Finset.mem_filter.mp hb).2
      by_cases hbj : b.castSucc < j.succ
      · rw [Fin.succAbove_of_castSucc_lt _ _ hbj] at this
        have hval : b.val = 0 := congrArg (fun (x : Fin (k + 1 + 1 + 1)) => x.val) this
        exact (hb0 (Fin.ext hval)).elim
      · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.mp hbj)] at this
        exact (Fin.succ_ne_zero _ this).elim
    · intro h
      exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0⟩)).elim
  have h_ne : (cofaceTop (k + 1) j.succ y : Fin (k + 1 + 1 + 1) → ℝ) 0 ≠ 1 := by
    rw [h0]; exact hy
  apply Subtype.ext
  ext i
  have h_app1 := coneTail_apply (cofaceTop (k + 1) j.succ y) h_ne i
  show (coneTail (cofaceTop (k + 1) j.succ y) : Fin (k + 1 + 1) → ℝ) i = (cofaceTop k j (coneTail y) : Fin (k + 1 + 1) → ℝ) i
  rw [h_app1, h0]
  show (cofaceTop (k + 1) j.succ y : Fin (k + 1 + 1 + 1) → ℝ) i.succ / (1 - (y : Fin (k + 1 + 1) → ℝ) 0)
    = (stdSimplex.map (S := ℝ) (Fin.succAbove j) (coneTail y) : Fin (k + 1 + 1) → ℝ) i
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  show (stdSimplex.map (S := ℝ) (Fin.succAbove j.succ) y : Fin (k + 1 + 1 + 1) → ℝ) i.succ / (1 - (y : Fin (k + 1 + 1) → ℝ) 0)
    = ∑ b ∈ Finset.filter (fun x => j.succAbove x = i) Finset.univ, (coneTail y : Fin (k + 1) → ℝ) b
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have h_sum_tail : (∑ b ∈ Finset.filter (fun x => j.succAbove x = i) Finset.univ, (coneTail y : Fin (k + 1) → ℝ) b)
      = (∑ b ∈ Finset.filter (fun x => j.succAbove x = i) Finset.univ, (y : Fin (k + 1 + 1) → ℝ) b.succ) / (1 - (y : Fin (k + 1 + 1) → ℝ) 0) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    exact coneTail_apply y hy b
  rw [h_sum_tail]
  congr 1
  have h_fib : (Finset.filter (fun x : Fin (k + 1 + 1) => j.succ.succAbove x = i.succ) Finset.univ)
      = Finset.image (fun (b : Fin (k + 1)) => b.succ) (Finset.filter (fun x => j.succAbove x = i) Finset.univ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨b, rfl⟩ : ∃ b : Fin (k + 1), b.succ = x := by
        cases x using Fin.inductionOn
        · exfalso
          have hj0 : (j.succ : Fin (k + 1 + 1 + 1)).succAbove 0 = 0 := by
            rw [Fin.succAbove_of_castSucc_lt]; rfl; exact Fin.succ_pos j
          rw [hj0] at hx
          exact Fin.succ_ne_zero _ hx.symm
        · exact ⟨_, rfl⟩
      refine ⟨b, ?_, rfl⟩
      rw [Fin.succ_succAbove_succ] at hx
      exact Fin.succ_injective _ hx
    · rintro ⟨b, hb, rfl⟩
      rw [Fin.succ_succAbove_succ, hb]
  rw [h_fib, Finset.sum_image (fun _ _ _ _ h => Fin.succ_injective _ h)]

theorem cone_face_succ {n k : ℕ} (v : Delta n) (τ : Delta (k + 1) → Delta n)
    (j : Fin (k + 1 + 1)) :
    (fun y : Delta (k + 1) => affineConeMap v τ (cofaceTop (k + 1) j.succ y))
      = (fun y : Delta (k + 1) => affineConeMap v (fun z : Delta k => τ (cofaceTop k j z)) y) := by
  funext y
  have h0 : (cofaceTop (k + 1) j.succ y : Fin (k + 1 + 1 + 1) → ℝ) 0 = (y : Fin (k + 1 + 1) → ℝ) 0 := by
    show (stdSimplex.map (S := ℝ) (Fin.succAbove j.succ) y : Fin (k + 1 + 1 + 1) → ℝ) 0 = y 0
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    have hj0 : (j.succ : Fin (k + 1 + 1 + 1)).succAbove 0 = 0 := by
      rw [Fin.succAbove_of_castSucc_lt]; rfl; exact Fin.succ_pos j
    rw [Finset.sum_eq_single 0]
    · intro b hb hb0
      have : (j.succ : Fin (k + 1 + 1 + 1)).succAbove b = 0 := (Finset.mem_filter.mp hb).2
      by_cases hbj : b.castSucc < j.succ
      · rw [Fin.succAbove_of_castSucc_lt _ _ hbj] at this
        have hval : b.val = 0 := congrArg (fun (x : Fin (k + 1 + 1 + 1)) => x.val) this
        exact (hb0 (Fin.ext hval)).elim
      · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.mp hbj)] at this
        exact (Fin.succ_ne_zero _ this).elim
    · intro h
      exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0⟩)).elim
  apply Subtype.ext
  ext c
  show (affineConeMap v τ (cofaceTop (k + 1) j.succ y) : Fin (n + 1) → ℝ) c
    = (affineConeMap v (fun z => τ (cofaceTop k j z)) y : Fin (n + 1) → ℝ) c
  rw [affineConeMap_coord, affineConeMap_coord, h0]
  by_cases hy : (y : Fin (k + 1 + 1) → ℝ) 0 = 1
  · rw [hy]
    simp only [sub_self, zero_mul, add_zero]
  · rw [coneTail_cofaceTop_succ j y hy]

/-! ## 6. The cone on singular simplices and chains of `Δⁿ` -/

/-- The singular simplex obtained by coning to a point of the standard simplex. -/
noncomputable def coneSimplex (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularSimplices (TopCat.of (Delta n)) (k + 1) :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) (k + 1)
    (affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ))

theorem coneSimplex_continuousMap (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)
      = affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ) := by
  exact singularSimplexAsContinuousMap_continuousMapAsSingularSimplex _ _ _

/-- The constant singular zero-simplex at the chosen point. -/
noncomputable def constSimplex0 (n : ℕ) (v : Delta n) :
    singularSimplices (TopCat.of (Delta n)) 0 :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) 0
    (ContinuousMap.const (Delta 0) v)

@[simp] theorem constSimplex0_continuousMap (n : ℕ) (v : Delta n) :
    singularSimplexAsContinuousMap (TopCat.of (Delta n)) 0 (constSimplex0 n v)
      = ContinuousMap.const (Delta 0) v := by
  exact singularSimplexAsContinuousMap_continuousMapAsSingularSimplex _ _ _

theorem coneSimplex_face_zero (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) k 0 (coneSimplex n k v σ) = σ := by
  apply singularSimplices_ext
  rw [faceSimplex_continuousMap, coneSimplex_continuousMap]
  apply ContinuousMap.ext
  intro y
  show (affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ)) (cofaceTop k 0 y)
    = (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ) y
  simp only [affineConeContinuousMap_apply]
  exact congrFun (cone_face_zero v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ)) y

theorem coneSimplex_face_succ (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) (k + 1)) (j : Fin (k + 1 + 1)) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) (k + 1) j.succ (coneSimplex n (k + 1) v σ)
      = coneSimplex n k v (AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) k j σ) := by
  apply singularSimplices_ext
  rw [faceSimplex_continuousMap, coneSimplex_continuousMap, coneSimplex_continuousMap, faceSimplex_continuousMap]
  apply ContinuousMap.ext
  intro y
  show (affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) σ)) (cofaceTop (k + 1) j.succ y)
    = (affineConeContinuousMap v (ContinuousMap.comp (singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) σ) (cofaceTop k j))) y
  show (affineConeMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) σ)) (cofaceTop (k + 1) j.succ y)
    = (affineConeMap v (fun z => (singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) σ) (cofaceTop k j z))) y
  exact congrFun (cone_face_succ v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) σ) j) y

theorem coneSimplex_face_one_zero (n : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) 0) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) 0 1 (coneSimplex n 0 v σ)
      = constSimplex0 n v := by
  apply singularSimplices_ext
  rw [faceSimplex_continuousMap, coneSimplex_continuousMap, constSimplex0_continuousMap]
  apply ContinuousMap.ext
  intro y
  show (affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) 0 σ)) (cofaceTop 0 1 y) = v
  simp only [affineConeContinuousMap_apply]
  have h1 : (cofaceTop 0 1 y : Fin 2 → ℝ) 0 = 1 := by
    have hcast := cofaceTop_last_castSucc 0 0 y
    have h0 : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
    have hy0 : (y : Fin 1 → ℝ) 0 = 1 :=
      (Fin.sum_univ_one (fun i => (y : Fin 1 → ℝ) i)).symm.trans y.2.2
    rw [h0] at hcast
    exact hcast.trans hy0
  apply Subtype.ext
  ext j
  show (affineConeMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) 0 σ) (cofaceTop 0 1 y) : Fin (n + 1) → ℝ) j = (v : Fin (n + 1) → ℝ) j
  rw [affineConeMap_coord, h1]
  ring

/-! ## 7. The cone on chains -/

/-- The chain generator associated with the cone over a singular simplex. -/
noncomputable def coneGenerator (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  chainGenerator R (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)

/-- Send a coefficient to its scalar multiple of the coned simplex generator. -/
noncomputable def coneGeneratorHom (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    ModuleCat.of R R ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  ModuleCat.ofHom
    { toFun := fun r => (r : R) • coneGenerator R n k v σ
      map_add' := fun r s => add_smul r s (coneGenerator R n k v σ)
      map_smul' := fun a r => mul_smul a r (coneGenerator R n k v σ) }

/-- Extend coning on singular generators linearly to all chains. -/
noncomputable def coneLinearMap (R : Type) [CommRing R] (n k : ℕ) (v : Delta n) :
    singularChainGroup R (TopCat.of (Delta n)) k
      ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  Sigma.desc fun σ : singularSimplices (TopCat.of (Delta n)) k => coneGeneratorHom R n k v σ

theorem coneLinearMap_generator (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    (coneLinearMap R n k v).hom (chainGenerator R (TopCat.of (Delta n)) k σ)
      = coneGenerator R n k v σ := by
  have h := Sigma.ι_desc (fun σ => coneGeneratorHom R n k v σ) σ
  have happ := congrArg (fun (m : ModuleCat.of R R ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1)) => m.hom (1 : R)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  have h1 : (coneGeneratorHom R n k v σ).hom (1 : R) = coneGenerator R n k v σ := one_smul R (coneGenerator R n k v σ)
  have hgen : chainGenerator R (TopCat.of (Delta n)) k σ = (Sigma.ι (fun (_ : singularSimplices (TopCat.of (Delta n)) k) => ModuleCat.of R R) σ).hom (1 : R) := rfl
  rw [hgen]
  exact happ.trans h1

/-! ## 8. The boundary formula -/

theorem singularBoundary_coneGenerator_zero (R : Type) [CommRing R] (n : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) 0) :
    (singularBoundary R (TopCat.of (Delta n)) 0).hom (coneGenerator R n 0 v σ)
      = chainGenerator R (TopCat.of (Delta n)) 0 σ
        - chainGenerator R (TopCat.of (Delta n)) 0 (constSimplex0 n v) := by
  have h := singularBoundary_chainGenerator_formula R (TopCat.of (Delta n)) 0 (coneSimplex n 0 v σ)
  change (singularBoundary R (TopCat.of (Delta n)) 0).hom (chainGenerator R (TopCat.of (Delta n)) 1 (coneSimplex n 0 v σ)) = _
  rw [h]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
    coneSimplex_face_zero, coneSimplex_face_one_zero]
  exact (sub_eq_add_neg _ _).symm

theorem singularBoundary_coneGenerator_succ (R : Type) [CommRing R] (n m : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) (m + 1)) :
    (singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom (coneGenerator R n (m + 1) v σ)
      = chainGenerator R (TopCat.of (Delta n)) (m + 1) σ
        - (coneLinearMap R n m v).hom
            ((singularBoundary R (TopCat.of (Delta n)) m).hom
              (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ)) := by
  have h := singularBoundary_chainGenerator_formula R (TopCat.of (Delta n)) (m + 1) (coneSimplex n (m + 1) v σ)
  change (singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom (chainGenerator R (TopCat.of (Delta n)) (m + 2) (coneSimplex n (m + 1) v σ)) = _
  rw [h]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, coneSimplex_face_zero]
  have h_bnd := singularBoundary_chainGenerator_formula R (TopCat.of (Delta n)) m σ
  rw [h_bnd, map_sum]
  have h_neg_sum : ∑ i : Fin (m + 2), ((-1 : R) ^ (i.succ : ℕ)) • chainGenerator R (TopCat.of (Delta n)) (m + 1)
        (AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) (m + 1) i.succ (coneSimplex n (m + 1) v σ))
      = - ∑ i : Fin (m + 2), (coneLinearMap R n m v).hom (((-1 : R) ^ (i : ℕ)) • chainGenerator R (TopCat.of (Delta n)) m (AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) m i σ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    erw [coneLinearMap_generator]
    rw [coneSimplex_face_succ]
    show ((-1 : R) ^ (i.succ : ℕ)) • coneGenerator R n m v (AlexanderWhitney.faceSimplex (TopCat.of ↑(Delta n)) m i σ) = _
    rw [Fin.val_succ, pow_succ, mul_smul, smul_comm, neg_one_smul]
  rw [sub_eq_add_neg, h_neg_sum]

theorem singularBoundary_coneLinearMap (R : Type) [CommRing R] (n m : ℕ) (v : Delta n) :
    coneLinearMap R n (m + 1) v ≫ singularBoundary R (TopCat.of (Delta n)) (m + 1)
        + singularBoundary R (TopCat.of (Delta n)) m ≫ coneLinearMap R n m v
      = 𝟙 (singularChainGroup R (TopCat.of (Delta n)) (m + 1)) := by
  apply Sigma.hom_ext
  intro σ
  erw [Preadditive.comp_add, Category.comp_id]
  have hval : ∀ (f g : ModuleCat.of R R ⟶ singularChainGroup R (TopCat.of (Delta n)) (m + 1)),
      f.hom (1 : R) = g.hom (1 : R) → f = g := by
    intro f g h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hf := f.hom.map_smul x (1 : R)
    have hg := g.hom.map_smul x (1 : R)
    simp at hf hg
    rw [hf, hg, h]
  apply hval
  erw [ModuleCat.hom_add, LinearMap.add_apply,
       ModuleCat.hom_comp, LinearMap.comp_apply,
       ModuleCat.hom_comp, LinearMap.comp_apply,
       ModuleCat.hom_comp, LinearMap.comp_apply,
       ModuleCat.hom_comp, LinearMap.comp_apply]
  have hgen : (Sigma.ι (fun (_ : singularSimplices (TopCat.of (Delta n)) (m + 1)) => ModuleCat.of R R) σ).hom (1 : R)
      = chainGenerator R (TopCat.of (Delta n)) (m + 1) σ := rfl
  rw [hgen]
  erw [coneLinearMap_generator]
  rw [singularBoundary_coneGenerator_succ R n m v σ]
  exact sub_add_cancel _ _

end AffineBarycentricSubdivision
end SphereOddDegree
