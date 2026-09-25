/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Tactic


/-!
# LocallyConnected

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

namespace OneMfld

instance : LocallyConnectedSpace NNReal := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U xU
  rw [NNReal.isEmbedding_coe.nhds_eq_comap x] at xU
  simp only [Filter.mem_comap] at xU
  let ⟨t, x_t, t_U⟩ := xU
  rw [mem_nhds_iff_exists_Ioo_subset] at x_t
  let ⟨l, u, x_ul, ul_t⟩ := x_t
  rw [Set.Ioo] at x_ul
  dsimp at x_ul
  have l_lt_u : l < u := lt_trans x_ul.1 x_ul.2
  have upos : 0 < u := lt_of_lt_of_le' (x_ul.2) x.coe_nonneg
  let V := {y : NNReal | l < ↑y ∧ ↑y < u}
  use V
  constructor
  · rw [NNReal.isEmbedding_coe.nhds_eq_comap x]
    simp only [Filter.mem_comap]
    use Set.Ioo l u
    constructor
    · exact Ioo_mem_nhds x_ul.1 x_ul.2
    · intro a a_lu
      dsimp [V]
      rw [Set.preimage, Set.Ioo] at a_lu
      dsimp at a_lu
      exact a_lu
  constructor
  -- . apply Convex.IsConnected
  · apply IsConnected.isPreconnected
    apply IsPathConnected.isConnected
    rw [IsPathConnected]
    let z := ((max 0 l) + u) / 2
    have znonneg : 0 ≤ z := by
      have nn₁ : 0 ≤ (max 0 l) := le_max_left 0 l
      have nn₂ : 0 ≤ u := LT.lt.le upos
      have : 0 ≤ (max 0 l) + u := add_nonneg nn₁ nn₂
      exact div_nonneg this zero_le_two
    let z' : NNReal := NNReal.mk z znonneg
    have l_lt_z : l < z := by
      have : l ≤ max 0 l := le_max_right 0 l
      change l < (max 0 l + u) / 2
      linarith
    have z_lt_u : z < u := by
      have : max 0 l < u := max_lt_iff.mpr ⟨upos, l_lt_u⟩
      change (max 0 l + u) / 2 < u
      linarith
    have : z' ∈ V := ⟨l_lt_z, z_lt_u⟩
    use z'
    use this
    intro y yV
    dsimp [V] at yV
    by_cases h : z' = y
    · exact Inseparable.joinedIn (congrArg nhds h) this yV
    rw [JoinedIn]
    let γ : Path z' y := {
      toFun := fun t ↦ NNReal.mk ((unitInterval.symm t)*z' + t*y)
        (add_nonneg (mul_nonneg unitInterval.nonneg' znonneg)
          (mul_nonneg unitInterval.nonneg' y.coe_nonneg))
      continuous_toFun := by
        simp only [unitInterval.coe_symm_eq]
        refine Metric.continuous_iff.mpr ?_
        intro s ε εpos
        let δ := ε / dist y z'
        have dyz'pos : 0 < dist y z' := dist_pos.mpr (ne_comm.mpr h)
        have δpos : δ > 0 := div_pos εpos dyz'pos
        use δ
        constructor
        · exact δpos
        intro a a_s_near
        rw [NNReal.dist_eq]
        simp only [NNReal.coe_mk]
        rw [sub_mul, sub_mul, one_mul]
        let ans : Real := (↑a - ↑s) * (↑y - ↑z')
        have : ↑z' - ↑a * ↑z' + ↑a * ↑y - (↑z' - ↑s * ↑z' + ↑s * ↑y) = ans := by ring
        rw [this]
        dsimp [ans]
        rw [abs_mul]
        -- have : (max 0 l + u) / 2 - ↑a * ((max 0 l + u) / 2) + ↑a * ↑y - ((max 0 l +
        -- u) / 2 - ↑s * ((max 0 l + u) / 2) + ↑s * ↑y)
        --  = (↑a - ↑s) * (↑y - ((max 0 l + u) / 2)) := by ring
        --ring_nf
        have ha : |(a:ℝ) - (s:ℝ)| < δ := by
          rw [← Real.dist_eq (a : ℝ) (s : ℝ)]
          exact a_s_near
        have this' : |↑y - (max 0 l + u) / 2| = dist y z' := rfl
        have this : |(y:ℝ) - (z':ℝ)| = dist y z' := by
          exact this'
        rw [this]
        calc
          |↑a - ↑s| * dist y z'
            < δ * dist y z' := by exact ((mul_lt_mul_iff_of_pos_right dyz'pos).mpr a_s_near)
            _ = ε := by dsimp [δ]
                        ring_nf
                        refine mul_inv_cancel_right₀ ?_ ε
                        exact dist_ne_zero.mpr fun a => h (id (Eq.symm a))
      source' := by
        simp only [unitInterval.symm_zero, Set.Icc.coe_one, one_mul,
          Set.Icc.coe_zero, zero_mul, add_zero]
        exact rfl
      target' := by
        simp only [unitInterval.symm_one, Set.Icc.coe_zero, zero_mul, Set.Icc.coe_one, one_mul,
          zero_add]
        trivial
    }
    use γ
    intro t
    dsimp [V, γ]
    constructor
    · change l < ↑(unitInterval.symm t) * ((max 0 l + u) / 2) + ↑t * ↑y
      by_cases tpos : t > 0
      · calc
          l = ↑(unitInterval.symm t) * l + t * l := by
            simp only [unitInterval.coe_symm_eq]
            ring
          _ < ↑(unitInterval.symm t) * l + t * y := by
            have : t * l < t * y := mul_lt_mul_of_pos_left yV.1 tpos
            linarith
          _ ≤ ↑(unitInterval.symm t) * z + t * y := by
            have : ↑(unitInterval.symm t) * l ≤ ↑(unitInterval.symm t) * z
              := mul_le_mul_of_nonneg_left (le_of_lt l_lt_z) unitInterval.nonneg'
            linarith
      · have : t = 0 := le_antisymm (not_lt.mp tpos) (unitInterval.nonneg')
        rw [this]
        simp only [unitInterval.symm_zero, Set.Icc.coe_one, one_mul, Set.Icc.coe_zero, zero_mul,
          add_zero, gt_iff_lt]
        exact l_lt_z
    · change ↑(unitInterval.symm t) * ((max 0 l + u) / 2) + ↑t * ↑y < u
      by_cases tpos : t > 0
      · calc
          ↑(unitInterval.symm t) * ((max 0 l + u) / 2) + ↑t * ↑y
          < ↑(unitInterval.symm t) * ((max 0 l + u) / 2) + ↑t * u := by
            have : ↑t * ↑y < ↑t * u := mul_lt_mul_of_pos_left yV.2 tpos
            linarith
          _ ≤ ↑(unitInterval.symm t) * u + ↑t * u := by
            have : ↑(unitInterval.symm t) * ((max 0 l + u) / 2) ≤ ↑(unitInterval.symm t) * u
              := mul_le_mul_of_nonneg_left (le_of_lt z_lt_u) unitInterval.nonneg'
            linarith
          _ = u := by rw [unitInterval.coe_symm_eq]; ring
      · have : t = 0 := le_antisymm (not_lt.mp tpos) (unitInterval.nonneg')
        rw [this]
        simp only [unitInterval.symm_zero, Set.Icc.coe_one, one_mul, Set.Icc.coe_zero, zero_mul,
          add_zero, gt_iff_lt]
        exact z_lt_u
  · intro a aV
    dsimp [V] at aV
    apply t_U
    rw [Set.preimage]
    dsimp
    apply ul_t
    rw [Set.Ioo]
    exact aV

end OneMfld
