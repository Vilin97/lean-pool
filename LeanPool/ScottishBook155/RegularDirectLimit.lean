/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.BookkeepingSchedule

/-!
# Regular direct limits

At the regular uncountable recursion length, every point of a completed
direct limit already comes from one component.  This is the formal version of
the manuscript's assertion that a countable Cauchy sequence is contained in
one earlier stage.
-/

namespace ScottishBook155

open Filter

private abbrev RI := RecursionIndex.{0}

/-- A countable family of recursion indices has a strict upper bound. -/
theorem recursionIndex_nat_bounded (a : ℕ → RI) :
    ∃ j : RI, ∀ n, a n < j := by
  let : IsWellOrder RI ((· < ·) : RI → RI → Prop) := isWellOrder_lt
  let f : ℕ → Ordinal := fun n =>
    Ordinal.typein ((· < ·) : RI → RI → Prop) (a n)
  have hsmall : (⨆ n, f n + 1) < recursionCardinal.ord := by
    apply Ordinal.iSup_add_one_lt_of_lt_cof
    · simpa only [Cardinal.mk_nat, recursionCardinal_isRegular.cof_ord] using
        aleph0_lt_recursionCardinal
    · intro n
      exact Ordinal.typein_lt_self (a n)
  have hsmall' : (⨆ n, f n + 1) <
      Ordinal.type ((· < ·) : RI → RI → Prop) := by
    simpa only [Ordinal.type_toType] using hsmall
  obtain ⟨j, hj⟩ := Ordinal.typein_surj (α := RI) (· < ·) hsmall'
  refine ⟨j, fun n => ?_⟩
  rw [← Ordinal.typein_lt_typein (r := (· < ·))]
  exact (Ordinal.lt_iSup_add_one f n).trans_eq hj.symm

namespace RegularDirectLimit

variable (G : RI → Type)
variable [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
variable [∀ i, CompleteSpace (G i)]
variable (e : ∀ i j : RI, i ≤ j → G i →ₗᵢ[ℝ] G j)
variable [DirectedSystem G (e · · ·)]

/-- At regular uncountable length, the canonical component embeddings jointly
surject onto the completed direct limit. -/
theorem exists_completedOf (z : NormedDirectLimit.CompletedCarrier G e) :
    ∃ (j : RI) (x : G j), NormedDirectLimit.completedOf G e j x = z := by
  let A := NormedDirectLimit.Carrier G e
  let d : ℕ → A := DenseSequenceCardinal.approx
    ((↑) : A → NormedDirectLimit.CompletedCarrier G e)
    UniformSpace.Completion.denseRange_coe z
  let idx : ℕ → RI := fun n => NormedDirectLimit.reprIndex G e (d n)
  obtain ⟨j, hj⟩ := recursionIndex_nat_bounded idx
  let x : ℕ → G j := fun n =>
    e (idx n) j (hj n).le (NormedDirectLimit.reprValue G e (d n))
  have hxcoe (n : ℕ) :
      NormedDirectLimit.completedOf G e j (x n) =
        (d n : NormedDirectLimit.CompletedCarrier G e) := by
    calc
      NormedDirectLimit.completedOf G e j (x n) =
          NormedDirectLimit.completedOf G e (idx n)
            (NormedDirectLimit.reprValue G e (d n)) :=
        NormedDirectLimit.completedOf_f G e (hj n).le _
      _ = (d n : NormedDirectLimit.CompletedCarrier G e) :=
        congrArg ((↑) : A → NormedDirectLimit.CompletedCarrier G e)
          (NormedDirectLimit.repr_spec G e (d n))
  have hd : Tendsto
      (fun n => (d n : NormedDirectLimit.CompletedCarrier G e))
      atTop (nhds z) :=
    DenseSequenceCardinal.approx_tendsto
      ((↑) : A → NormedDirectLimit.CompletedCarrier G e)
      UniformSpace.Completion.denseRange_coe z
  have hxCauchy : CauchySeq x := by
    have hxc : CauchySeq
        (fun n => NormedDirectLimit.completedOf G e j (x n)) :=
      (hd.congr' (Filter.Eventually.of_forall fun n => (hxcoe n).symm)).cauchySeq
    rw [Metric.cauchySeq_iff] at hxc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hxc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [(NormedDirectLimit.completedOf G e j).isometry.dist_eq] using
      hN m hm n hn
  obtain ⟨xlim, hxlim⟩ := cauchySeq_tendsto_of_complete hxCauchy
  refine ⟨j, xlim, ?_⟩
  have himage : Tendsto
      (fun n => NormedDirectLimit.completedOf G e j (x n))
      atTop (nhds (NormedDirectLimit.completedOf G e j xlim)) :=
    (NormedDirectLimit.completedOf G e j).continuous.continuousAt.tendsto.comp hxlim
  apply tendsto_nhds_unique himage
  exact hd.congr' (Filter.Eventually.of_forall fun n => (hxcoe n).symm)

end RegularDirectLimit

end ScottishBook155
