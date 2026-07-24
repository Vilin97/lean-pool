/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadialMeasure

/-!
# Radius Weights
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The class of radius weights we actually need in the weak monotonicity
argument: measurable on `(0, R0)` and essentially bounded there.  The earlier
unrestricted formulas with `∀ c : ℝ → ℝ` are convenient wrappers, but this is
the realistic target for a direct measure-theoretic coarea proof. -/
def RadiusWeightOn (R0 : ℝ) (c : ℝ → ℝ) : Prop :=
  AEStronglyMeasurable c (radiusIntervalMeasure R0) ∧
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ rho ∂radiusIntervalMeasure R0, ‖c rho‖ ≤ C

theorem RadiusWeightOn.aestronglyMeasurable {R0 : ℝ} {c : ℝ → ℝ}
    (hc : RadiusWeightOn R0 c) :
    AEStronglyMeasurable c (radiusIntervalMeasure R0) :=
  hc.1

theorem RadiusWeightOn.exists_ae_bound {R0 : ℝ} {c : ℝ → ℝ}
    (hc : RadiusWeightOn R0 c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ rho ∂radiusIntervalMeasure R0, ‖c rho‖ ≤ C :=
  hc.2

theorem radiusWeightOn_of_aestronglyMeasurable_ae_bound {R0 : ℝ} {c : ℝ → ℝ}
    (hc_meas : AEStronglyMeasurable c (radiusIntervalMeasure R0))
    (hc_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ rho ∂radiusIntervalMeasure R0, ‖c rho‖ ≤ C) :
    RadiusWeightOn R0 c :=
  ⟨hc_meas, hc_bound⟩

theorem radiusWeightOn_of_aestronglyMeasurable_bound_on_Ioo {R0 : ℝ}
    {c : ℝ → ℝ} {C : ℝ}
    (hc_meas : AEStronglyMeasurable c (radiusIntervalMeasure R0))
    (hC_nonneg : 0 ≤ C)
    (hC : ∀ rho ∈ Ioo (0 : ℝ) R0, ‖c rho‖ ≤ C) :
    RadiusWeightOn R0 c := by
  refine ⟨hc_meas, ⟨C, hC_nonneg, ?_⟩⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with rho hrho
  exact hC rho hrho

theorem radiusWeightOn_const (R0 k : ℝ) :
    RadiusWeightOn R0 (fun _ : ℝ => k) := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  refine ⟨‖k‖, norm_nonneg k, ?_⟩
  filter_upwards with rho
  simp

theorem RadiusWeightOn.indicator {R0 : ℝ} {c : ℝ → ℝ} {s : Set ℝ}
    (hc : RadiusWeightOn R0 c) (hs : MeasurableSet s) :
    RadiusWeightOn R0 (s.indicator c) := by
  rcases hc.exists_ae_bound with ⟨C, hC_nonneg, hC⟩
  refine ⟨hc.aestronglyMeasurable.indicator hs, ⟨C, hC_nonneg, ?_⟩⟩
  filter_upwards [hC] with rho hbound
  by_cases hrho : rho ∈ s
  · simpa [Set.indicator_of_mem hrho] using hbound
  · simpa [Set.indicator_of_notMem hrho] using hC_nonneg

theorem radiusWeightOn_indicator_of_aestronglyMeasurable_bound_on_set
    {R0 : ℝ} {c : ℝ → ℝ} {s : Set ℝ} {C : ℝ}
    (hc_meas : AEStronglyMeasurable (s.indicator c) (radiusIntervalMeasure R0))
    (hC_nonneg : 0 ≤ C)
    (hC : ∀ rho ∈ s, ‖c rho‖ ≤ C) :
    RadiusWeightOn R0 (s.indicator c) := by
  refine ⟨hc_meas, ⟨C, hC_nonneg, ?_⟩⟩
  filter_upwards with rho
  by_cases hrho : rho ∈ s
  · simpa [Set.indicator_of_mem hrho] using hC rho hrho
  · simpa [Set.indicator_of_notMem hrho] using hC_nonneg

theorem radiusWeightOn_indicator_const {R0 a b k : ℝ} :
    RadiusWeightOn R0 ((Ioo a b).indicator (fun _ : ℝ => k)) := by
  simpa using
    (radiusWeightOn_const R0 k).indicator (s := Ioo a b) measurableSet_Ioo

theorem radiusWeightOn_indicator_one {R0 a b : ℝ} :
    RadiusWeightOn R0 ((Ioo a b).indicator (fun _ : ℝ => (1 : ℝ))) := by
  simpa using radiusWeightOn_indicator_const (R0 := R0) (a := a) (b := b) (k := 1)

theorem RadiusWeightOn.add {R0 : ℝ} {c d : ℝ → ℝ}
    (hc : RadiusWeightOn R0 c) (hd : RadiusWeightOn R0 d) :
    RadiusWeightOn R0 (fun rho : ℝ => c rho + d rho) := by
  rcases hc.exists_ae_bound with ⟨C, hC_nonneg, hC⟩
  rcases hd.exists_ae_bound with ⟨D, hD_nonneg, hD⟩
  refine ⟨hc.aestronglyMeasurable.add hd.aestronglyMeasurable, ?_⟩
  refine ⟨C + D, add_nonneg hC_nonneg hD_nonneg, ?_⟩
  filter_upwards [hC, hD] with rho hc_bound hd_bound
  exact (norm_add_le (c rho) (d rho)).trans (add_le_add hc_bound hd_bound)

/-- Finite linear combinations of interval-indicator constants are admissible
radius weights. -/
theorem radiusWeightOn_finset_sum_indicator_const_Ioo
    {R0 : ℝ} {ι : Type*} (s : Finset ι)
    (a b k : ι → ℝ) :
    RadiusWeightOn R0
      (fun rho : ℝ =>
        ∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simpa using radiusWeightOn_const R0 0
  · intro i s his hs
    simpa [Finset.sum_insert his, add_comm, add_left_comm, add_assoc] using
      (radiusWeightOn_indicator_const (R0 := R0) (a := a i) (b := b i) (k := k i)).add hs

/-- Pointwise finite interval-step approximation by uniformly bounded radius
weights.  This is the concrete approximation package needed to pass the
finite-interval formula to a limiting radius weight by dominated convergence. -/
def RadiusWeightFiniteIntervalStepApprox (R0 : ℝ) (c : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∃ s : ℕ → Finset ℕ, ∃ a b k : ℕ → ℕ → ℝ,
      (∀ N i, i ∈ s N → 0 ≤ a N i) ∧
      (∀ N i, i ∈ s N → a N i ≤ b N i) ∧
      (∀ N i, i ∈ s N → b N i ≤ R0) ∧
      (∀ (N : ℕ) (rho : ℝ),
        ‖∑ i ∈ s N,
          (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho‖ ≤ C) ∧
      (∀ rho : ℝ,
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ i ∈ s N,
              (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho)
          Filter.atTop (𝓝 (c rho)))

/-- The practically useful version of finite interval-step approximation:
convergence is required on `(0, R0)` away from a countable set of bad radii.
This matches the grid-partition approximations used for continuous weights,
where all possible partition boundaries form a countable exceptional set. -/
def RadiusWeightFiniteIntervalStepApproxAE (R0 : ℝ) (c : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∃ bad : Set ℝ, bad.Countable ∧
      ∃ s : ℕ → Finset ℕ, ∃ a b k : ℕ → ℕ → ℝ,
        (∀ N i, i ∈ s N → 0 ≤ a N i) ∧
        (∀ N i, i ∈ s N → a N i ≤ b N i) ∧
        (∀ N i, i ∈ s N → b N i ≤ R0) ∧
        (∀ (N : ℕ) (rho : ℝ),
          ‖∑ i ∈ s N,
            (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho‖ ≤ C) ∧
        (∀ rho ∈ Ioo (0 : ℝ) R0, rho ∉ bad →
          Filter.Tendsto
            (fun N : ℕ =>
              ∑ i ∈ s N,
                (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho)
            Filter.atTop (𝓝 (c rho)))

/-- A pointwise finite interval-step approximation is, in particular, an
a.e.-valid approximation with empty exceptional set. -/
theorem RadiusWeightFiniteIntervalStepApprox.toAE {R0 : ℝ} {c : ℝ → ℝ}
    (h : RadiusWeightFiniteIntervalStepApprox R0 c) :
    RadiusWeightFiniteIntervalStepApproxAE R0 c := by
  rcases h with ⟨C, hC, s, a, b, k, ha, hab, hb, hbound, hlim⟩
  refine ⟨C, hC, ∅, countable_empty, s, a, b, k, ha, hab, hb, hbound, ?_⟩
  intro rho _hrho _hbad
  exact hlim rho

/-- A finite interval-step weight is realized by the constant approximation
sequence. -/
theorem radiusWeightFiniteIntervalStepApprox_finset_sum_indicator_const_Ioo
    {R0 : ℝ} {s : Finset ℕ} {a b k : ℕ → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hb : ∀ i ∈ s, b i ≤ R0) :
    RadiusWeightFiniteIntervalStepApprox R0
      (fun rho : ℝ =>
        ∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho) := by
  classical
  refine ⟨∑ i ∈ s, ‖k i‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _),
    (fun _ : ℕ => s), (fun _ : ℕ => a), (fun _ : ℕ => b), (fun _ : ℕ => k),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro _N i hi
    exact ha i hi
  · intro _N i hi
    exact hab i hi
  · intro _N i hi
    exact hb i hi
  · intro _N rho
    calc
      ‖∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho‖
          ≤ ∑ i ∈ s, ‖(Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho‖ :=
            norm_sum_le _ _
      _ ≤ ∑ i ∈ s, ‖k i‖ := by
          exact Finset.sum_le_sum (fun i _hi => by
            by_cases hrho : rho ∈ Ioo (a i) (b i)
            · simp [Set.indicator_of_mem hrho]
            · simp [Set.indicator_of_notMem hrho])
  · intro rho
    exact tendsto_const_nhds

/-- Constant radius weights are approximable on `(0, R0)` by the single
interval `(0, R0)`. -/
theorem radiusWeightFiniteIntervalStepApproxAE_const {R0 r : ℝ}
    (hR0_nonneg : 0 ≤ R0) :
    RadiusWeightFiniteIntervalStepApproxAE R0 (fun _ : ℝ => r) := by
  classical
  refine ⟨‖r‖, norm_nonneg r, ∅, countable_empty,
    (fun _ : ℕ => ({0} : Finset ℕ)),
    (fun _ _ : ℕ => (0 : ℝ)),
    (fun _ _ : ℕ => R0),
    (fun _ _ : ℕ => r),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro _N i hi
    simp
  · intro _N i hi
    simpa using hR0_nonneg
  · intro _N i hi
    exact le_rfl
  · intro _N rho
    by_cases hrho : rho ∈ Ioo (0 : ℝ) R0
    · simp [hrho]
    · simp [hrho]
  · intro rho hrho _hbad
    simp [hrho]

/-- Finite interval-step approximability is closed under addition.  The proof
encodes the two finite index sets into the even and odd natural numbers. -/
theorem RadiusWeightFiniteIntervalStepApproxAE.add {R0 : ℝ} {c d : ℝ → ℝ}
    (hc : RadiusWeightFiniteIntervalStepApproxAE R0 c)
    (hd : RadiusWeightFiniteIntervalStepApproxAE R0 d) :
    RadiusWeightFiniteIntervalStepApproxAE R0 (fun rho : ℝ => c rho + d rho) := by
  classical
  rcases hc with
    ⟨C, hC_nonneg, badC, hbadC_count, sC, aC, bC, kC,
      haC, habC, hbC, hboundC, hlimC⟩
  rcases hd with
    ⟨D, hD_nonneg, badD, hbadD_count, sD, aD, bD, kD,
      haD, habD, hbD, hboundD, hlimD⟩
  let evenEmb : ℕ ↪ ℕ :=
    ⟨fun i : ℕ => Nat.bit false i, by
      intro i j h
      have hdiv := congrArg Nat.div2 h
      simpa using hdiv⟩
  let oddEmb : ℕ ↪ ℕ :=
    ⟨fun i : ℕ => Nat.bit true i, by
      intro i j h
      have hdiv := congrArg Nat.div2 h
      simpa using hdiv⟩
  let s : ℕ → Finset ℕ := fun N =>
    (sC N).map evenEmb ∪ (sD N).map oddEmb
  let a : ℕ → ℕ → ℝ := fun N q =>
    if Nat.bodd q then aD N (Nat.div2 q) else aC N (Nat.div2 q)
  let b : ℕ → ℕ → ℝ := fun N q =>
    if Nat.bodd q then bD N (Nat.div2 q) else bC N (Nat.div2 q)
  let k : ℕ → ℕ → ℝ := fun N q =>
    if Nat.bodd q then kD N (Nat.div2 q) else kC N (Nat.div2 q)
  have hdisj : ∀ N : ℕ, Disjoint ((sC N).map evenEmb) ((sD N).map oddEmb) := by
    intro N
    rw [Finset.disjoint_left]
    intro q hqC hqD
    rcases (Finset.mem_map.1 hqC) with ⟨i, _hi, hiq⟩
    rcases (Finset.mem_map.1 hqD) with ⟨j, _hj, hjq⟩
    have hbit : Nat.bit false i = Nat.bit true j := by
      exact hiq.trans hjq.symm
    have hbodd := congrArg Nat.bodd hbit
    simp at hbodd
  have hsum_eq :
      ∀ (N : ℕ) (rho : ℝ),
        (∑ q ∈ s N, (Ioo (a N q) (b N q)).indicator (fun _ : ℝ => k N q) rho)
          =
        (∑ i ∈ sC N,
          (Ioo (aC N i) (bC N i)).indicator (fun _ : ℝ => kC N i) rho)
        +
        (∑ j ∈ sD N,
          (Ioo (aD N j) (bD N j)).indicator (fun _ : ℝ => kD N j) rho) := by
    intro N rho
    calc
      (∑ q ∈ s N, (Ioo (a N q) (b N q)).indicator (fun _ : ℝ => k N q) rho)
          =
        (∑ q ∈ (sC N).map evenEmb,
            (Ioo (a N q) (b N q)).indicator (fun _ : ℝ => k N q) rho)
          +
        (∑ q ∈ (sD N).map oddEmb,
            (Ioo (a N q) (b N q)).indicator (fun _ : ℝ => k N q) rho) := by
          dsimp [s]
          rw [Finset.sum_union (hdisj N)]
      _ =
        (∑ i ∈ sC N,
          (Ioo (aC N i) (bC N i)).indicator (fun _ : ℝ => kC N i) rho)
        +
        (∑ j ∈ sD N,
          (Ioo (aD N j) (bD N j)).indicator (fun _ : ℝ => kD N j) rho) := by
          rw [Finset.sum_map, Finset.sum_map]
          simp [a, b, k, evenEmb, oddEmb]
  refine ⟨C + D, add_nonneg hC_nonneg hD_nonneg,
    badC ∪ badD, hbadC_count.union hbadD_count,
    s, a, b, k, ?_, ?_, ?_, ?_, ?_⟩
  · intro N q hq
    dsimp [s] at hq
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · rcases (Finset.mem_map.1 hq) with ⟨i, hi, rfl⟩
      simpa [a, evenEmb] using haC N i hi
    · rcases (Finset.mem_map.1 hq) with ⟨i, hi, rfl⟩
      simpa [a, oddEmb] using haD N i hi
  · intro N q hq
    dsimp [s] at hq
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · rcases (Finset.mem_map.1 hq) with ⟨i, hi, rfl⟩
      simpa [a, b, evenEmb] using habC N i hi
    · rcases (Finset.mem_map.1 hq) with ⟨i, hi, rfl⟩
      simpa [a, b, oddEmb] using habD N i hi
  · intro N q hq
    dsimp [s] at hq
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · rcases (Finset.mem_map.1 hq) with ⟨i, hi, rfl⟩
      simpa [b, evenEmb] using hbC N i hi
    · rcases (Finset.mem_map.1 hq) with ⟨i, hi, rfl⟩
      simpa [b, oddEmb] using hbD N i hi
  · intro N rho
    calc
      ‖∑ q ∈ s N, (Ioo (a N q) (b N q)).indicator (fun _ : ℝ => k N q) rho‖
          =
        ‖(∑ i ∈ sC N,
            (Ioo (aC N i) (bC N i)).indicator (fun _ : ℝ => kC N i) rho)
          +
          (∑ j ∈ sD N,
            (Ioo (aD N j) (bD N j)).indicator (fun _ : ℝ => kD N j) rho)‖ := by
          rw [hsum_eq N rho]
      _ ≤
        ‖∑ i ∈ sC N,
            (Ioo (aC N i) (bC N i)).indicator (fun _ : ℝ => kC N i) rho‖
          +
        ‖∑ j ∈ sD N,
            (Ioo (aD N j) (bD N j)).indicator (fun _ : ℝ => kD N j) rho‖ :=
          norm_add_le _ _
      _ ≤ C + D := add_le_add (hboundC N rho) (hboundD N rho)
  · intro rho hrho hnotbad
    have hnotC : rho ∉ badC := fun h => hnotbad (Or.inl h)
    have hnotD : rho ∉ badD := fun h => hnotbad (Or.inr h)
    have hC_lim := hlimC rho hrho hnotC
    have hD_lim := hlimD rho hrho hnotD
    have hev :
        (fun N : ℕ =>
          (∑ i ∈ sC N,
            (Ioo (aC N i) (bC N i)).indicator (fun _ : ℝ => kC N i) rho)
          +
          (∑ j ∈ sD N,
            (Ioo (aD N j) (bD N j)).indicator (fun _ : ℝ => kD N j) rho))
          =ᶠ[Filter.atTop]
        (fun N : ℕ =>
          ∑ q ∈ s N, (Ioo (a N q) (b N q)).indicator (fun _ : ℝ => k N q) rho) :=
      Filter.Eventually.of_forall fun N => (hsum_eq N rho).symm
    exact (hC_lim.add hD_lim).congr' hev

/-- Finite interval-step approximability is closed under multiplication by a
constant. -/
theorem RadiusWeightFiniteIntervalStepApproxAE.const_mul {R0 r : ℝ} {c : ℝ → ℝ}
    (hc : RadiusWeightFiniteIntervalStepApproxAE R0 c) :
    RadiusWeightFiniteIntervalStepApproxAE R0 (fun rho : ℝ => r * c rho) := by
  classical
  rcases hc with
    ⟨C, hC_nonneg, bad, hbad_count, s, a, b, k, ha, hab, hb, hbound, hlim⟩
  let k' : ℕ → ℕ → ℝ := fun N i => r * k N i
  have hsum_eq :
      ∀ (N : ℕ) (rho : ℝ),
        (∑ i ∈ s N, (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k' N i) rho)
          =
        r * (∑ i ∈ s N,
          (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho) := by
    intro N rho
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hrho : rho ∈ Ioo (a N i) (b N i)
    · simp [k', Set.indicator_of_mem hrho]
    · simp [k', Set.indicator_of_notMem hrho]
  refine ⟨‖r‖ * C, mul_nonneg (norm_nonneg r) hC_nonneg,
    bad, hbad_count, s, a, b, k', ha, hab, hb, ?_, ?_⟩
  · intro N rho
    calc
      ‖∑ i ∈ s N, (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k' N i) rho‖
          = ‖r * (∑ i ∈ s N,
            (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho)‖ := by
            rw [hsum_eq N rho]
      _ = ‖r‖ *
          ‖∑ i ∈ s N,
            (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho‖ := by
            rw [norm_mul]
      _ ≤ ‖r‖ * C :=
          mul_le_mul_of_nonneg_left (hbound N rho) (norm_nonneg r)
  · intro rho hrho hnotbad
    have hbase := hlim rho hrho hnotbad
    have hev :
        (fun N : ℕ =>
          r * (∑ i ∈ s N,
            (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho))
          =ᶠ[Filter.atTop]
        (fun N : ℕ =>
          ∑ i ∈ s N, (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k' N i) rho) :=
      Filter.Eventually.of_forall fun N => (hsum_eq N rho).symm
    exact (hbase.const_mul r).congr' hev

/-- Finite interval-step approximability is closed under negation. -/
theorem RadiusWeightFiniteIntervalStepApproxAE.neg {R0 : ℝ} {c : ℝ → ℝ}
    (hc : RadiusWeightFiniteIntervalStepApproxAE R0 c) :
    RadiusWeightFiniteIntervalStepApproxAE R0 (fun rho : ℝ => -c rho) := by
  simpa using (hc.const_mul (r := -1))

/-- Finite interval-step approximability is closed under subtraction. -/
theorem RadiusWeightFiniteIntervalStepApproxAE.sub {R0 : ℝ} {c d : ℝ → ℝ}
    (hc : RadiusWeightFiniteIntervalStepApproxAE R0 c)
    (hd : RadiusWeightFiniteIntervalStepApproxAE R0 d) :
    RadiusWeightFiniteIntervalStepApproxAE R0 (fun rho : ℝ => c rho - d rho) := by
  simpa [sub_eq_add_neg] using hc.add hd.neg

theorem RadiusWeightOn.neg {R0 : ℝ} {c : ℝ → ℝ}
    (hc : RadiusWeightOn R0 c) :
    RadiusWeightOn R0 (fun rho : ℝ => -c rho) := by
  rcases hc.exists_ae_bound with ⟨C, hC_nonneg, hC⟩
  refine ⟨hc.aestronglyMeasurable.neg, ⟨C, hC_nonneg, ?_⟩⟩
  filter_upwards [hC] with rho hbound
  simpa using hbound

theorem RadiusWeightOn.sub {R0 : ℝ} {c d : ℝ → ℝ}
    (hc : RadiusWeightOn R0 c) (hd : RadiusWeightOn R0 d) :
    RadiusWeightOn R0 (fun rho : ℝ => c rho - d rho) := by
  simpa [sub_eq_add_neg] using hc.add hd.neg

theorem RadiusWeightOn.mul {R0 : ℝ} {c d : ℝ → ℝ}
    (hc : RadiusWeightOn R0 c) (hd : RadiusWeightOn R0 d) :
    RadiusWeightOn R0 (fun rho : ℝ => c rho * d rho) := by
  rcases hc.exists_ae_bound with ⟨C, hC_nonneg, hC⟩
  rcases hd.exists_ae_bound with ⟨D, hD_nonneg, hD⟩
  refine ⟨hc.aestronglyMeasurable.mul hd.aestronglyMeasurable, ?_⟩
  refine ⟨C * D, mul_nonneg hC_nonneg hD_nonneg, ?_⟩
  filter_upwards [hC, hD] with rho hc_bound hd_bound
  calc
    ‖c rho * d rho‖ = ‖c rho‖ * ‖d rho‖ := norm_mul (c rho) (d rho)
    _ ≤ C * D := mul_le_mul hc_bound hd_bound (norm_nonneg (d rho)) hC_nonneg

theorem RadiusWeightOn.const_mul {R0 k : ℝ} {c : ℝ → ℝ}
    (hc : RadiusWeightOn R0 c) :
    RadiusWeightOn R0 (fun rho : ℝ => k * c rho) := by
  simpa [mul_comm] using (radiusWeightOn_const R0 k).mul hc

theorem RadiusWeightOn.mul_const {R0 k : ℝ} {c : ℝ → ℝ}
    (hc : RadiusWeightOn R0 c) :
    RadiusWeightOn R0 (fun rho : ℝ => c rho * k) := by
  simpa [mul_comm] using hc.mul (radiusWeightOn_const R0 k)

theorem radiusWeightOn_id (R0 : ℝ) :
    RadiusWeightOn R0 (fun rho : ℝ => rho) := by
  refine ⟨continuous_id.aestronglyMeasurable, ?_⟩
  refine ⟨‖R0‖, norm_nonneg R0, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with rho hrho
  rw [Real.norm_eq_abs]
  exact le_of_lt (abs_lt.2
    ⟨lt_of_le_of_lt (neg_nonpos.2 (norm_nonneg R0)) hrho.1,
      lt_of_lt_of_le hrho.2 (le_abs_self R0)⟩)

theorem radiusWeightOn_of_contDiff_one {R0 : ℝ} {phi : ℝ → ℝ}
    (hphi : ContDiff ℝ 1 phi) :
    RadiusWeightOn R0 phi := by
  have hmeas : AEStronglyMeasurable phi (radiusIntervalMeasure R0) :=
    hphi.continuous.aestronglyMeasurable
  have hcont : ContinuousOn phi (Icc (0 : ℝ) R0) :=
    hphi.continuous.continuousOn
  rcases isCompact_Icc.exists_bound_of_continuousOn hcont with ⟨C, hC⟩
  refine radiusWeightOn_of_aestronglyMeasurable_bound_on_Ioo
    (R0 := R0) (c := phi) (C := max C 0) hmeas (le_max_right C 0) ?_
  intro rho hrho
  exact (hC rho ⟨le_of_lt hrho.1, le_of_lt hrho.2⟩).trans (le_max_left C 0)

theorem radiusWeightOn_deriv_of_contDiff_one {R0 : ℝ} {phi : ℝ → ℝ}
    (hphi : ContDiff ℝ 1 phi) :
    RadiusWeightOn R0 (deriv phi) := by
  have hderiv_cont : Continuous (deriv phi) :=
    hphi.continuous_deriv_one
  have hmeas : AEStronglyMeasurable (deriv phi) (radiusIntervalMeasure R0) :=
    hderiv_cont.aestronglyMeasurable
  have hcont : ContinuousOn (deriv phi) (Icc (0 : ℝ) R0) :=
    hderiv_cont.continuousOn
  rcases isCompact_Icc.exists_bound_of_continuousOn hcont with ⟨C, hC⟩
  refine radiusWeightOn_of_aestronglyMeasurable_bound_on_Ioo
    (R0 := R0) (c := deriv phi) (C := max C 0) hmeas (le_max_right C 0) ?_
  intro rho hrho
  exact (hC rho ⟨le_of_lt hrho.1, le_of_lt hrho.2⟩).trans (le_max_left C 0)

theorem radiusWeightOn_rho_mul_deriv_of_contDiff_one {R0 : ℝ} {phi : ℝ → ℝ}
    (hphi : ContDiff ℝ 1 phi) :
    RadiusWeightOn R0 (fun rho : ℝ => rho * deriv phi rho) := by
  exact (radiusWeightOn_id R0).mul
    (radiusWeightOn_deriv_of_contDiff_one (R0 := R0) hphi)

theorem radiusWeightOn_radialMainCoeff_of_contDiff_one {n : ℕ} {R0 : ℝ}
    {phi : ℝ → ℝ} (hphi : ContDiff ℝ 1 phi) :
    RadiusWeightOn R0
      (fun rho : ℝ => ((n : ℝ) - 2) * phi rho + rho * deriv phi rho) := by
  exact
    ((radiusWeightOn_of_contDiff_one (R0 := R0) hphi).const_mul
      (k := ((n : ℝ) - 2))).add
      (radiusWeightOn_rho_mul_deriv_of_contDiff_one (R0 := R0) hphi)

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps
