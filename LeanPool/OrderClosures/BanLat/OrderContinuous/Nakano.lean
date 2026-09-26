/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.OrderContinuous.Basic


/-!
# Nakano's theorem

For a Banach lattice the following are equivalent:

* the norm is order continuous;
* the lattice is σ-conditionally complete and the norm is σ-order continuous;
* every increasing order-bounded sequence converges in norm.

The equivalence is recorded through the corresponding implications between
order continuity, σ-conditional completeness, σ-order continuity, and monotone
norm convergence of bounded sequences.
-/

@[expose] public section

namespace BanachLattice

section Forward
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

/-- In an order continuous Banach lattice, every increasing order-bounded
sequence converges in norm to its supremum. -/
theorem tendsto_of_monotone_bddAbove [IsOrderContinuousNorm X]
    {u : ℕ → X} (hmono : Monotone u) (hbd : BddAbove (Set.range u)) :
    ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x) := by
  -- Order continuity implies order completeness, hence σ-order completeness;
  -- σ-OC gives the LUB and σ-order continuity of the norm gives convergence.
  let : ConditionallyCompleteLattice X :=
    conditionallyCompleteLatticeOfIsOrderContinuousNorm
  have hx : IsLUB (Set.range u) (sSup (Set.range u)) :=
    ⟨fun _ ha => le_csSup hbd ha,
      fun _ ha => csSup_le (Set.range_nonempty u) ha⟩
  exact ⟨_, hx, IsSigmaOrderContinuousNorm.tendsto_of_monotone_isLUB hmono hx⟩

end Forward

section Sigma
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-- A lattice-ordered additive commutative group in which every increasing order-bounded sequence
converges in norm to a least upper bound is σ-conditionally complete. -/
@[reducible]
noncomputable def sigmaConditionallyCompleteLatticeOfMonoBddAboveTendsto
    (h : ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
      ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x)) :
    SigmaConditionallyCompleteLattice X := by
  haveI : Nonempty X := ⟨0⟩
  refine sigmaConditionallyCompleteLatticeOfPosSeq X
    (fun {u} hmono _ hbd => ?_)
  obtain ⟨x, hx, _⟩ := h hmono hbd
  exact ⟨x, hx⟩

variable [BanachLattice X]

/-- A Banach lattice in which every increasing order-bounded sequence
converges in norm has a σ-order continuous norm. -/
theorem isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto
    (h : ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
      ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x)) :
    IsSigmaOrderContinuousNorm X := by
  refine ⟨fun {u} hanti hnn hglb => ?_⟩
  -- Set v n = u 0 - u n; this is monotone, ≥ 0, bounded above by u 0.
  have hv_mono : Monotone (fun n => u 0 - u n) :=
    fun n m hnm => sub_le_sub_left (hanti hnm) _
  have hv_bdd : BddAbove (Set.range fun n => u 0 - u n) :=
    ⟨u 0, by
      rintro _ ⟨n, rfl⟩
      simpa using sub_nonneg.mpr (hnn n)⟩
  obtain ⟨x, hx_lub, hx_tend⟩ := h hv_mono hv_bdd
  -- u 0 - x is a lower bound of range u, hence ≤ 0 since IsGLB (range u) 0.
  have hub_le : u 0 - x ∈ lowerBounds (Set.range u) := by
    rintro _ ⟨n, rfl⟩
    have h1 : u 0 - u n ≤ x := hx_lub.1 ⟨n, rfl⟩
    exact sub_le_comm.mp h1
  have h_le_zero : u 0 - x ≤ 0 := hglb.2 hub_le
  -- u 0 - x ≥ 0 since x ≤ u 0.
  have hxle : x ≤ u 0 := hx_lub.2 (by
    rintro _ ⟨n, rfl⟩
    exact sub_le_self _ (hnn n))
  have h_ge_zero : (0 : X) ≤ u 0 - x := sub_nonneg.mpr hxle
  have hux_eq : u 0 - x = 0 := le_antisymm h_le_zero h_ge_zero
  -- Now u n = u 0 - (u 0 - u n) → u 0 - x = 0.
  have htend : Filter.Tendsto (fun n => u 0 - (u 0 - u n)) Filter.atTop (nhds (u 0 - x)) :=
    tendsto_const_nhds.sub hx_tend
  have hux : Filter.Tendsto u Filter.atTop (nhds (u 0 - x)) := by
    convert htend using 1
    ext n; abel
  rw [hux_eq] at hux
  exact hux

end Sigma

section Backward
variable {X : Type*} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X] [IsSigmaOrderContinuousNorm X]

/-- In a σ-conditionally complete Banach lattice with σ-order continuous norm,
every antitone sequence bounded below converges in norm to its greatest lower
bound. -/
private lemma tendsto_antitone_seq_of_bddBelow
    {z : ℕ → X} (hanti : Antitone z) (hbdd : BddBelow (Set.range z)) :
    ∃ v, IsGLB (Set.range z) v ∧ Filter.Tendsto z Filter.atTop (nhds v) := by
  have hcount : (Set.range z).Countable := Set.countable_range _
  have hne : (Set.range z).Nonempty := Set.range_nonempty _
  have hglb : IsGLB (Set.range z) (sInf (Set.range z)) :=
    ⟨fun _ hy => SigmaConditionallyCompleteLattice.csInf_le _ _ hcount hbdd hy,
     fun _ hy => SigmaConditionallyCompleteLattice.le_csInf _ _ hcount hne hy⟩
  exact ⟨_, hglb, IsSigmaOrderContinuousNorm.tendsto_of_antitone_isGLB hanti hglb⟩

private lemma cauchySeq_of_directed_dist {ι : Type*} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {Y : Type*} [PseudoMetricSpace Y]
    (y : ι → Y)
    (h : ∀ ε > 0, ∃ α₀, ∀ α ≥ α₀, ∀ β ≥ α₀, dist (y α) (y β) < ε) :
    CauchySeq y := by
  rw [CauchySeq, Metric.cauchy_iff]
  refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
  obtain ⟨α₀, hα₀⟩ := h ε hε
  refine ⟨y '' {α | α₀ ≤ α}, ?_, ?_⟩
  · exact Filter.image_mem_map (Filter.mem_atTop α₀)
  · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
    exact hα₀ α hα β hβ

/-- A Banach lattice that is σ-conditionally complete and has σ-order
continuous norm has an order continuous norm. -/
theorem isOrderContinuousNorm_of_isSigmaConditionallyCompleteLattice :
    IsOrderContinuousNorm X := by
  classical
  refine ⟨fun {ι} _ _ _ {y} hanti hnn hglb => ?_⟩
  -- Once `y` is Cauchy, completeness gives a limit, which is the order GLB.
  suffices hcauchy : CauchySeq y by
    obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hwglb : IsGLB (Set.range y) w := isGLB_of_tendsto_atTop hanti hw
    have hw_eq : w = 0 := hwglb.unique hglb
    rw [hw_eq] at hw
    exact hw
  -- For Cauchy: assume not, derive a "bad gap" for every starting point.
  refine cauchySeq_of_directed_dist y (fun ε hε => ?_)
  by_contra hcon
  push Not at hcon
  -- For every α₀, ∃ α₀ ≤ α ≤ γ with ‖y α - y γ‖ ≥ ε/2.
  have hbad : ∀ α₀ : ι, ∃ p : ι × ι, α₀ ≤ p.1 ∧ p.1 ≤ p.2 ∧ ε / 2 ≤ ‖y p.1 - y p.2‖ := by
    intro α₀
    obtain ⟨α, hα, β, hβ, hdist⟩ := hcon α₀
    obtain ⟨γ, hγα, hγβ⟩ := exists_ge_ge α β
    have h1 : ‖y α - y γ‖ + ‖y β - y γ‖ ≥ ε := by
      have htr := dist_triangle (y α) (y γ) (y β)
      rw [dist_comm (y γ) (y β)] at htr
      simp only [dist_eq_norm] at htr hdist
      linarith
    by_cases hαbad : ε / 2 ≤ ‖y α - y γ‖
    · exact ⟨(α, γ), hα, hγα, hαbad⟩
    · push Not at hαbad
      exact ⟨(β, γ), hβ, hγβ, by linarith⟩
  -- Define the recursive choice function and the resulting subsequence.
  let step : ι → ι × ι := fun α₀ => (hbad α₀).choose
  have hstep : ∀ α₀ : ι, α₀ ≤ (step α₀).1 ∧ (step α₀).1 ≤ (step α₀).2 ∧
      ε / 2 ≤ ‖y (step α₀).1 - y (step α₀).2‖ := fun α₀ => (hbad α₀).choose_spec
  -- Build the recursive pair-valued sequence g : ℕ → ι × ι.
  let g : ℕ → ι × ι := fun n => Nat.rec (step Classical.ofNonempty)
    (fun _ p => step p.2) n
  have hg_succ : ∀ n, g (n + 1) = step (g n).2 := fun _ => rfl
  have hg_le : ∀ n, (g n).1 ≤ (g n).2 := fun n => by
    induction n with
    | zero => exact (hstep _).2.1
    | succ k _ => rw [hg_succ]; exact (hstep _).2.1
  have hg_step : ∀ n, (g n).2 ≤ (g (n + 1)).1 := fun n => by
    rw [hg_succ]; exact (hstep _).1
  have hg_dist : ∀ n, ε / 2 ≤ ‖y (g n).1 - y (g n).2‖ := fun n => by
    induction n with
    | zero => exact (hstep _).2.2
    | succ k _ => rw [hg_succ]; exact (hstep _).2.2
  -- The interleaved sequence z : ℕ → X.
  let z : ℕ → X := fun k => if k % 2 = 0 then y (g (k / 2)).1 else y (g (k / 2)).2
  have hz_anti : Antitone z := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      have e1 : (m + m) % 2 = 0 := by omega
      have e2 : (m + m + 1) % 2 = 1 := by omega
      have e3 : (m + m) / 2 = m := by omega
      have e4 : (m + m + 1) / 2 = m := by omega
      simp only [z, e1, e2, e3, e4, ↓reduceIte]
      exact hanti (hg_le m)
    · subst hm
      have e1 : (2 * m + 1) % 2 = 1 := by omega
      have e2 : (2 * m + 1 + 1) % 2 = 0 := by omega
      have e3 : (2 * m + 1) / 2 = m := by omega
      have e4 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      simp only [z, e1, e2, e3, e4, ↓reduceIte]
      exact hanti (hg_step m)
  have hz_nn : ∀ k, 0 ≤ z k := by
    intro k; simp only [z]; split <;> exact hnn _
  have hz_bdd : BddBelow (Set.range z) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hz_nn k⟩
  -- By σ-CCL + σ-OCN, z is Cauchy.
  obtain ⟨_, _, hzv⟩ := tendsto_antitone_seq_of_bddBelow hz_anti hz_bdd
  have hzcauchy : CauchySeq z := hzv.cauchySeq
  rw [Metric.cauchySeq_iff] at hzcauchy
  obtain ⟨N, hN⟩ := hzcauchy (ε / 2) (by linarith)
  -- The pair (2N, 2N+1) violates Cauchy by hg_dist.
  have hN1 : 2 * N ≥ N := by omega
  have hN2 : 2 * N + 1 ≥ N := by omega
  have hdN := hN (2 * N) hN1 (2 * N + 1) hN2
  have hh1 : (2 * N) % 2 = 0 := by omega
  have hh2 : (2 * N + 1) % 2 = 1 := by omega
  have hh3 : (2 * N) / 2 = N := by omega
  have hh4 : (2 * N + 1) / 2 = N := by omega
  simp only [z, hh1, hh2, hh3, hh4, ↓reduceIte, one_ne_zero] at hdN
  rw [dist_eq_norm] at hdN
  linarith [hg_dist N]

end Backward

end BanachLattice
