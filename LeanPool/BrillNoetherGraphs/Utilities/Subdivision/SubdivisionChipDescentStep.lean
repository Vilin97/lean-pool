/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionChipDescent
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.BlockSlopeRounding
public import Mathlib.Tactic

/-!
# The step inequality for chip descent

For a fine winning script, the height difference across one coarse step,
corrected by the signed rounding cost of the chips inside that step, is
bounded by `N` times the first and last fine slopes adjusted by the numbers of
chips rounded to either end.  With a common rounding offset absorbing the
costs, the same bounds hold for the coarse slopes of the rounded script.  See
`Utilities/Subdivision/SubdivisionChipDescent.lean` for the definitions and
the overall argument.
-/

@[expose] public section

namespace Utilities.Certificate.SubdivisionGraph.Spec

open Finset Utilities.CommonOffsetRounding

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Fine vertices strictly inside a coarse step

A fine interior vertex at a fine offset that is not a multiple of `N` is not in
the image of the coarse graph, and the chips sitting on it are exactly the chips
of the corresponding coarse step with the corresponding offset. -/

/-- A fine interior vertex whose fine offset is not a multiple of `N` misses the
image of the coarse vertices. -/
private theorem interior_not_mem_range (e : Fin p) (o : ℕ) (hopos : 0 < o)
    (hj : o - 1 < (spec.scale N hN).length e - 1)
    (hnd : ∀ m : ℕ, N * m ≠ o) :
    (spec.scale N hN).interiorVertex e ⟨o - 1, hj⟩ ∉ Set.range (spec.fineOf N hN) := by
  rintro ⟨x, hx⟩
  rcases x with v | ⟨e', j'⟩
  · exact Sum.inl_ne_inr hx
  · have hSigma := Sum.inr.inj hx
    have hedge : e' = e := congrArg Sigma.fst hSigma
    subst hedge
    have hval : N * (j'.val + 1) - 1 = o - 1 :=
      congrArg (fun s : (spec.scale N hN).Interior => s.2.val) hSigma
    have hpos : 1 ≤ N * (j'.val + 1) := Nat.mul_pos hN (Nat.succ_pos _)
    exact hnd (j'.val + 1) (by omega)

/-- A chip sits at a prescribed fine interior vertex exactly when its slot and
its fine offset agree with that vertex. -/
private theorem chip_fineVertex_eq_interior (c : spec.Chip N) (e : Fin p) (o : ℕ)
    (hopos : 0 < o) (hj : o - 1 < (spec.scale N hN).length e - 1) :
    (c.fineVertex hN = (spec.scale N hN).interiorVertex e ⟨o - 1, hj⟩) ↔
      (c.edge = e ∧ N * c.step + c.offset = o) := by
  have hoffpos := c.offset_pos
  have hofflt := c.offset_lt
  have hposlt : N * c.step + c.offset < N * spec.length c.edge := by
    have h1 : N * (c.step + 1) ≤ N * spec.length c.edge :=
      Nat.mul_le_mul_left N c.step_lt
    rw [Nat.mul_succ] at h1
    omega
  have hfv : c.fineVertex hN =
      (spec.scale N hN).interiorVertex c.edge ⟨N * c.step + c.offset - 1, by
        show N * c.step + c.offset - 1 < N * spec.length c.edge - 1
        omega⟩ := by
    unfold Chip.fineVertex pathVertex
    rw [dif_neg (by show ¬ N * c.step + c.offset = 0; omega),
      dif_neg (by show ¬ N * c.step + c.offset = N * spec.length c.edge; omega)]
    rfl
  rw [hfv]
  constructor
  · intro h
    have hSigma := Sum.inr.inj h
    have hedge : c.edge = e := congrArg Sigma.fst hSigma
    refine ⟨hedge, ?_⟩
    subst hedge
    have hval : N * c.step + c.offset - 1 = o - 1 :=
      congrArg (fun s : (spec.scale N hN).Interior => s.2.val) hSigma
    omega
  · rintro ⟨hedge, hval⟩
    subst hedge
    subst hval
    rfl

/-! ## The three bounds -/

/-- The total signed rounding cost over all steps is bounded by the total
rounding distance. -/
theorem sum_abs_stepCost_le {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) :
    (∑ step : spec.Step, |spec.stepCost N chips step|) ≤
      ∑ i, ((chips i).distance : ℤ) := by
  have hfib : (∑ step : spec.Step,
      ∑ i ∈ spec.stepChips N chips step, ((chips i).distance : ℤ))
      = ∑ i, ((chips i).distance : ℤ) :=
    Finset.sum_fiberwise Finset.univ (fun i => (chips i).coarseStep)
      (fun i => ((chips i).distance : ℤ))
  rw [← hfib]
  refine Finset.sum_le_sum ?_
  intro step _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro i _
  exact (chips i).abs_signedCost_le

/-- **The step inequality.**  For a fine winning script, the height difference
across a coarse step, corrected by the signed rounding cost of its chips, lies
between `N` times (first fine slope minus the left count) and `N` times (last
fine slope plus the right count). -/
theorem step_bounds {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) (D₀ : CFDiv spec.graph)
    (σ : firingScript (spec.scale N hN).graph)
    (hσ : effective (spec.embed N hN D₀ + spec.fineChips N hN chips +
      prin (spec.scale N hN).graph σ))
    (step : spec.Step) :
    (N : ℤ) * (spec.fineSlope N hN σ step.1 (N * step.2.val) -
        spec.leftCount N chips step) ≤
      spec.fineValue N hN σ step.1 (N * (step.2.val + 1)) + spec.stepCost N chips step -
        spec.fineValue N hN σ step.1 (N * step.2.val) ∧
    spec.fineValue N hN σ step.1 (N * (step.2.val + 1)) + spec.stepCost N chips step -
        spec.fineValue N hN σ step.1 (N * step.2.val) ≤
      (N : ℤ) * (spec.fineSlope N hN σ step.1 (N * (step.2.val + 1) - 1) +
        spec.rightCount N chips step) := by
  obtain ⟨e, k⟩ := step
  dsimp only
  have hkL : k.val < spec.length e := k.isLt
  have hmul : N * k.val + N ≤ N * spec.length e := by
    have h1 : N * (k.val + 1) ≤ N * spec.length e := Nat.mul_le_mul_left N hkL
    rw [Nat.mul_succ] at h1
    exact h1
  -- the offsets of the chips of this step lie strictly inside the block
  have hoff : ∀ i ∈ spec.stepChips N chips (⟨e, k⟩ : spec.Step),
      0 < (chips i).offset ∧ (chips i).offset < N :=
    fun i _ => ⟨(chips i).offset_pos, (chips i).offset_lt⟩
  -- the fine slopes drop by at most the number of chips at each interior offset
  have hslope : ∀ t, 0 < t → t < N →
      spec.fineSlope N hN σ e (N * k.val + (t - 1))
        - (((spec.stepChips N chips (⟨e, k⟩ : spec.Step)).filter
            (fun i => (chips i).offset = t)).card : ℤ)
        ≤ spec.fineSlope N hN σ e (N * k.val + t) := by
    intro t ht0 htN
    obtain ⟨o, hodef⟩ : ∃ o, o = N * k.val + t := ⟨_, rfl⟩
    have hopos : 0 < o := by omega
    have hj : o - 1 < (spec.scale N hN).length e - 1 := by
      show o - 1 < N * spec.length e - 1
      omega
    obtain ⟨v, hvdef⟩ : ∃ v, v = (spec.scale N hN).interiorVertex e ⟨o - 1, hj⟩ := ⟨_, rfl⟩
    -- `o` is not a multiple of `N`, so `v` carries no chip of the coarse divisor
    have hnd : ∀ m : ℕ, N * m ≠ o := by
      intro m hm
      have h1 : (N * m) % N = 0 := Nat.mul_mod_right N m
      rw [hm, hodef, Nat.mul_add_mod, Nat.mod_eq_of_lt htN] at h1
      omega
    have hembed : spec.embed N hN D₀ v = 0 := by
      rw [hvdef]
      exact spec.embed_apply_of_not_mem_range N hN D₀ _
        (spec.interior_not_mem_range N hN e o hopos hj hnd)
    -- the chips at `v` are exactly the chips of this step at offset `t`
    have hfilter : (spec.stepChips N chips (⟨e, k⟩ : spec.Step)).filter
          (fun i => (chips i).offset = t)
        = Finset.univ.filter (fun i => (chips i).fineVertex hN = v) := by
      ext i
      simp only [stepChips, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hvdef, spec.chip_fineVertex_eq_interior N hN (chips i) e o hopos hj]
      constructor
      · rintro ⟨hstep, hofft⟩
        have hedge : (chips i).edge = e := congrArg Sigma.fst hstep
        have hstepval : (chips i).step = k.val :=
          congrArg (fun x : spec.Step => x.2.val) hstep
        refine ⟨hedge, ?_⟩
        rw [hstepval, hofft]
        omega
      · rintro ⟨hedge, hval⟩
        have h1 : (N * (chips i).step + (chips i).offset) % N = (chips i).offset := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (chips i).offset_lt]
        have h2 : (N * k.val + t) % N = t := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt htN]
        have hofft : (chips i).offset = t := by
          rw [← h1, hval, hodef, h2]
        have h3 : N * (chips i).step + t = N * k.val + t := by omega
        have hstepk : (chips i).step = k.val :=
          Nat.eq_of_mul_eq_mul_left hN (Nat.add_right_cancel h3)
        refine ⟨?_, hofft⟩
        show (⟨(chips i).edge, ⟨(chips i).step, (chips i).step_lt⟩⟩ : spec.Step) = ⟨e, k⟩
        subst hedge
        exact congrArg (Sigma.mk (chips i).edge) (Fin.ext hstepk)
    have hcount : spec.fineChips N hN chips v =
        (((spec.stepChips N chips (⟨e, k⟩ : spec.Step)).filter
          (fun i => (chips i).offset = t)).card : ℤ) := by
      have hone : ∀ i : ι,
          oneChip (G := (spec.scale N hN).graph) ((chips i).fineVertex hN) v
          = (if (chips i).fineVertex hN = v then (1 : ℤ) else 0) := by
        intro i
        simp only [oneChip]
        by_cases h : (chips i).fineVertex hN = v
        · rw [if_pos h.symm, if_pos h]
        · rw [if_neg (fun hh => h hh.symm), if_neg h]
      have hsum : spec.fineChips N hN chips v
          = ∑ i : ι, (if (chips i).fineVertex hN = v then (1 : ℤ) else 0) := by
        unfold fineChips
        rw [Finset.sum_apply]
        exact Finset.sum_congr rfl (fun i _ => hone i)
      rw [hsum, hfilter, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
    have ho1 : o - 1 + 1 = o := by omega
    have hprin : prin (spec.scale N hN).graph σ v =
        spec.fineSlope N hN σ e o - spec.fineSlope N hN σ e (o - 1) := by
      have h2 : prin (spec.scale N hN).graph σ v =
          spec.fineSlope N hN σ e (o - 1 + 1) - spec.fineSlope N hN σ e (o - 1) := by
        rw [hvdef]
        exact (spec.scale N hN).prin_interiorVertex_eq_slopeDifference
          (spec.isStepSlope_fineSlope N hN σ) e ⟨o - 1, hj⟩
      rw [h2, ho1]
    have heff := hσ v
    simp only [Pi.add_apply] at heff
    rw [hembed, hcount, hprin] at heff
    have hgoal1 : N * k.val + (t - 1) = o - 1 := by omega
    have hgoal2 : N * k.val + t = o := by omega
    rw [hgoal1, hgoal2]
    linarith
  -- the block sum of fine slopes telescopes
  have htel : (∑ t ∈ Finset.range N, spec.fineSlope N hN σ e (N * k.val + t))
      = spec.fineValue N hN σ e (N * (k.val + 1))
        - spec.fineValue N hN σ e (N * k.val) := by
    have hstep : ∀ t : ℕ, spec.fineSlope N hN σ e (N * k.val + t)
        = spec.fineValue N hN σ e (N * k.val + (t + 1))
          - spec.fineValue N hN σ e (N * k.val + t) := fun _ => rfl
    have h2 := Finset.sum_range_sub
      (fun t => spec.fineValue N hN σ e (N * k.val + t)) N
    rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.range N) => hstep t), h2, Nat.add_zero,
      show N * k.val + N = N * (k.val + 1) from by rw [Nat.mul_succ]]
  have hcost : (∑ i ∈ spec.stepChips N chips (⟨e, k⟩ : spec.Step),
        (if (chips i).toRight then (N : ℤ) - ((chips i).offset : ℤ)
          else -((chips i).offset : ℤ)))
      = spec.stepCost N chips (⟨e, k⟩ : spec.Step) := rfl
  have hleft : (((spec.stepChips N chips (⟨e, k⟩ : spec.Step)).filter
        (fun i => (chips i).toRight = false)).card : ℤ)
      = spec.leftCount N chips (⟨e, k⟩ : spec.Step) := rfl
  have hright : (((spec.stepChips N chips (⟨e, k⟩ : spec.Step)).filter
        (fun i => (chips i).toRight = true)).card : ℤ)
      = spec.rightCount N chips (⟨e, k⟩ : spec.Step) := rfl
  have hlast : N * k.val + (N - 1) = N * (k.val + 1) - 1 := by
    rw [Nat.mul_succ]
    omega
  constructor
  · have h := Utilities.BlockSlopeRounding.block_lower N hN
      (fun u => spec.fineSlope N hN σ e (N * k.val + u))
      (spec.stepChips N chips (⟨e, k⟩ : spec.Step))
      (fun i => (chips i).offset) (fun i => (chips i).toRight) hoff hslope
    simp only [Nat.add_zero] at h
    rw [htel, hcost, hleft] at h
    linarith
  · have h := Utilities.BlockSlopeRounding.block_upper N hN
      (fun u => spec.fineSlope N hN σ e (N * k.val + u))
      (spec.stepChips N chips (⟨e, k⟩ : spec.Step))
      (fun i => (chips i).offset) (fun i => (chips i).toRight) hoff hslope
    simp only [hlast] at h
    rw [htel, hcost, hright] at h
    linarith

/-- With a common offset that absorbs the rounding costs, every coarse slope of
the rounded script is bounded by the corresponding fine endpoint slopes and
chip counts. -/
theorem roundedSlope_bounds {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) (D₀ : CFDiv spec.graph)
    (σ : firingScript (spec.scale N hN).graph)
    (hσ : effective (spec.embed N hN D₀ + spec.fineChips N hN chips +
      prin (spec.scale N hN).graph σ))
    (κ : Fin N)
    (hκ : ∀ step : spec.Step,
      round N κ (spec.fineValue N hN σ step.1 (N * (step.2.val + 1)) +
        spec.stepCost N chips step) =
      round N κ (spec.fineValue N hN σ step.1 (N * (step.2.val + 1))))
    (step : spec.Step) :
    spec.fineSlope N hN σ step.1 (N * step.2.val) - spec.leftCount N chips step ≤
        spec.roundedSlope N hN κ σ step.1 step.2.val ∧
      spec.roundedSlope N hN κ σ step.1 step.2.val ≤
        spec.fineSlope N hN σ step.1 (N * (step.2.val + 1) - 1) +
          spec.rightCount N chips step := by
  obtain ⟨hlo, hhi⟩ := spec.step_bounds N hN chips D₀ σ hσ step
  have h := round_sub_bounds N hN κ
    (spec.fineValue N hN σ step.1 (N * step.2.val))
    (spec.fineValue N hN σ step.1 (N * (step.2.val + 1)) + spec.stepCost N chips step)
    (spec.fineSlope N hN σ step.1 (N * step.2.val) - spec.leftCount N chips step)
    (spec.fineSlope N hN σ step.1 (N * (step.2.val + 1) - 1) + spec.rightCount N chips step)
    hlo hhi
  rw [hκ step] at h
  exact h

end Utilities.Certificate.SubdivisionGraph.Spec
