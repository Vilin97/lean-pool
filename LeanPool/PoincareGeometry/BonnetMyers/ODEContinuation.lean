/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.BonnetMyers.MetricContinuation
import LeanPool.PoincareGeometry.BonnetMyers.ODE
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Restarting an ODE at a finite endpoint

This module is the analytic continuation layer used by the global geodesic
argument.  It proves that a solution which converges, together with its full
first-order state, at a finite left endpoint agrees near that endpoint with a
fresh local solution.  The proof does not hide an endpoint differentiability
assumption: the one-sided derivative is explicitly recovered from the limit
of the vector field using Mathlib's boundary-extension theorem.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace BonnetMyersEntry

/-- Extending a curve by its left limit produces a continuous curve on a
closed interval. -/
theorem continuousOn_leftExtension
    {X : Type*} [TopologicalSpace X]
    {q : ℝ → X} {a b : ℝ} {x : X} (hab : a < b)
    (hcont : ∀ t ∈ Ico a b, ContinuousAt q t)
    (hlim : Tendsto q (𝓝[<] b) (𝓝 x)) :
    ContinuousOn (fun t ↦ if t < b then q t else x) (Icc a b) := by
  intro t ht
  rcases lt_or_eq_of_le ht.2 with htb | htb
  · have heq : (fun t ↦ if t < b then q t else x) =ᶠ[𝓝 t] q := by
      filter_upwards [Iio_mem_nhds htb] with s hs
      change s < b at hs
      simp [hs]
    exact (hcont t ⟨ht.1, htb⟩).congr_of_eventuallyEq heq |>.continuousWithinAt
  · subst t
    rw [continuousWithinAt_Icc_iff_Iic hab]
    have hsplit : 𝓝[Iic b] b = 𝓝[<] b ⊔ pure b := by
      rw [← Iio_union_Icc_eq_Iic le_rfl, nhdsWithin_union]
      simp
    change Tendsto (fun t ↦ if t < b then q t else x) (𝓝[Iic b] b)
      (𝓝 ((fun t ↦ if t < b then q t else x) b))
    have hp : (fun t ↦ if t < b then q t else x) b = x := by simp
    rw [hp]
    rw [hsplit, tendsto_sup]
    constructor
    · apply hlim.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      change s < b at hs
      simp [hs]
    · simpa only [hp] using
        (tendsto_pure_nhds (fun t : ℝ ↦ if t < b then q t else x) b)

/-- Away from the endpoint, the left extension has the same derivative as
the original curve. -/
theorem hasDerivWithinAt_leftExtension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ → E} {v : ℝ → E → E} {a b : ℝ} {x : E}
    (hderiv : ∀ t ∈ Iio b, HasDerivAt q (v t (q t)) t) :
    ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun s ↦ if s < b then q s else x)
        (v t ((fun s ↦ if s < b then q s else x) t)) (Iic t) t := by
  intro t ht
  have heq : (fun s ↦ if s < b then q s else x) =ᶠ[𝓝 t] q := by
    filter_upwards [Iio_mem_nhds ht.2] with s hs
    change s < b at hs
    simp [hs]
  have hp : HasDerivAt (fun s ↦ if s < b then q s else x) (v t (q t)) t :=
    (hderiv t ht.2).congr_of_eventuallyEq heq
  have hvalue : (fun s ↦ if s < b then q s else x) t = q t := by simp [ht.2]
  rw [hvalue]
  exact hp.hasDerivWithinAt

/-- If both a solution and its autonomous vector field converge at a left
endpoint, the left extension has the expected one-sided derivative there. -/
theorem hasDerivWithinAt_leftExtension_endpoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ → E} {G : E → E} {b : ℝ} {x : E}
    (hG : ContinuousAt G x)
    (hderiv : ∀ t ∈ Iio b, HasDerivAt q (G (q t)) t)
    (hlim : Tendsto q (𝓝[<] b) (𝓝 x)) :
    HasDerivWithinAt (fun s ↦ if s < b then q s else x) (G x) (Iic b) b := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
  · intro t ht
    have heq : (fun s ↦ if s < b then q s else x) =ᶠ[𝓝 t] q := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      change s < b at hs
      simp [hs]
    exact ((hderiv t ht).congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt
  · change Tendsto (fun s ↦ if s < b then q s else x) (𝓝[Iio b] b)
      (𝓝 ((fun s ↦ if s < b then q s else x) b))
    have hp : (fun s ↦ if s < b then q s else x) b = x := by simp
    rw [hp]
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    change s < b at hs
    simp [hs]
  · exact self_mem_nhdsWithin
  · have hcomp : Tendsto (fun t ↦ G (q t)) (𝓝[<] b) (𝓝 (G x)) :=
      hG.tendsto.comp hlim
    apply hcomp.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t < b at ht
    have heq : (fun s ↦ if s < b then q s else x) =ᶠ[𝓝 t] q := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      change s < b at hs
      simp [hs]
    have hp : HasDerivAt (fun s ↦ if s < b then q s else x) (G (q t)) t :=
      (hderiv t ht).congr_of_eventuallyEq heq
    exact hp.deriv.symm

/-- The boundary derivative only depends on the final left tail.  This is the
form needed for a solution which is defined on an arbitrary open interval
ending at `b`, rather than on all of `Iio b`. -/
theorem hasDerivWithinAt_leftExtension_endpoint_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ → E} {G : E → E} {b : ℝ} {x : E}
    (hG : ContinuousAt G x)
    (hderiv : ∀ᶠ t in 𝓝[<] b, HasDerivAt q (G (q t)) t)
    (hlim : Tendsto q (𝓝[<] b) (𝓝 x)) :
    HasDerivWithinAt (fun t ↦ if t < b then q t else x) (G x) (Iic b) b := by
  obtain ⟨a, hab, htail⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hderiv
  let p : ℝ → E := fun t ↦ if t < b then q t else x
  have hpq : p =ᶠ[𝓝[<] b] q := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t < b at ht
    simp [p, ht]
  have hlimP : ContinuousWithinAt p (Ioo a b) b := by
    change Tendsto p (𝓝[Ioo a b] b) (𝓝 (p b))
    have hp : p b = x := by simp [p]
    rw [hp]
    apply (hlim.congr' hpq.symm).mono_left
    exact nhdsWithin_mono b (by
      intro t ht
      exact ht.2)
  have hdiff : DifferentiableOn ℝ p (Ioo a b) := by
    intro t ht
    have hq : HasDerivAt q (G (q t)) t := htail ht
    have heq : p =ᶠ[𝓝 t] q := by
      filter_upwards [Iio_mem_nhds ht.2] with s hs
      change s < b at hs
      simp [p, hs]
    exact (hq.congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt
  apply hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hlimP
    (Ioo_mem_nhdsLT hab)
  have hcomp : Tendsto (fun t ↦ G (q t)) (𝓝[<] b) (𝓝 (G x)) :=
    hG.tendsto.comp hlim
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin, hderiv] with t ht hq
  change t < b at ht
  have heq : p =ᶠ[𝓝 t] q := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    change s < b at hs
    simp [p, hs]
  have hp : HasDerivAt p (G (q t)) t := hq.congr_of_eventuallyEq heq
  exact hp.deriv.symm

/-- A first-order autonomous ODE whose state converges at a finite left
endpoint can be restarted there.  The returned local solution agrees with
the old one on a left neighbourhood of that endpoint. -/
theorem exists_localFirstOrderSolution_eventuallyEq_left_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {q : ℝ → E} {G : E → E} {b : ℝ} {x : E}
    (hG : ContDiffAt ℝ 1 G x)
    (hderiv : ∀ t ∈ Iio b, HasDerivAt q (G (q t)) t)
    (hlim : Tendsto q (𝓝[<] b) (𝓝 x)) :
    ∃ sol : LocalFirstOrderSolution (fun _ y ↦ G y) 0 x,
      q =ᶠ[𝓝[<] b] (fun t ↦ sol.curve (t - b)) := by
  obtain ⟨K, S, hS, hK⟩ := hG.exists_lipschitzOnWith
  have hGtime : ContDiffAt ℝ 1 (fun z : ℝ × E ↦ G z.2) (0, x) :=
    hG.comp (0, x) contDiffAt_snd
  obtain ⟨sol⟩ := exists_localFirstOrderSolution_of_contDiffAt
    (f := fun _ y ↦ G y) hGtime
  have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hsol_cont : ContinuousAt sol.curve 0 :=
    (sol.hasDeriv 0 (by simpa only [zero_sub, zero_add] using hzero)).continuousAt
  have hsolS : sol.curve ⁻¹' S ∈ 𝓝 (0 : ℝ) := by
    have hS0 : S ∈ 𝓝 (sol.curve 0) := by simpa [sol.initial] using hS
    exact hsol_cont.preimage_mem_nhds hS0
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hsolS
  have hqS : q ⁻¹' S ∈ 𝓝[<] b := hlim hS
  obtain ⟨a₀, ha₀, hqSsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hqS
  let r : ℝ := min (sol.radius / 2) (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith [sol.radius_pos]) (by linarith)
  let a : ℝ := max a₀ (b - r)
  have ha : a < b := by
    dsimp [a]
    exact max_lt ha₀ (sub_lt_self b hr)
  have ha₀ : a₀ ≤ a := by dsimp [a]; exact le_max_left _ _
  have hbr : b - r ≤ a := by dsimp [a]; exact le_max_right _ _
  let p : ℝ → E := fun t ↦ if t < b then q t else x
  let g : ℝ → E := fun t ↦ sol.curve (t - b)
  have hpcont : ContinuousOn p (Icc a b) := by
    apply continuousOn_leftExtension ha
    intro t ht
    exact (hderiv t ht.2).continuousAt
    exact hlim
  have hpderiv : ∀ t ∈ Ioc a b,
      HasDerivWithinAt p (G (p t)) (Iic t) t := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | htb
    · have h := hasDerivWithinAt_leftExtension
        (a := a) (b := b) (x := x) (v := fun _ y ↦ G y) hderiv t
        ⟨ht.1, htb⟩
      simpa [p] using h
    · subst t
      simpa [p] using hasDerivWithinAt_leftExtension_endpoint
        (hG := hG.continuousAt) hderiv hlim
  have hpS : ∀ t ∈ Ioc a b, p t ∈ S := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | htb
    · have hmem : t ∈ Ioo a₀ b :=
        ⟨lt_of_le_of_lt ha₀ ht.1, htb⟩
      simpa [p, htb] using hqSsub hmem
    · subst t
      simpa [p] using mem_of_mem_nhds hS
  have htime : ∀ t ∈ Icc a b, t - b ∈ Ioo (-sol.radius) sol.radius := by
    intro t ht
    have htr : b - r ≤ t := le_trans hbr ht.1
    have hrr : r ≤ sol.radius / 2 := min_le_left _ _
    have htb : t ≤ b := ht.2
    constructor <;> linarith [sol.radius_pos]
  have hgderiv : ∀ t ∈ Icc a b, HasDerivAt g (G (g t)) t := by
    intro t ht
    have hshift : HasDerivAt (fun s : ℝ ↦ s - b) 1 t := by
      simpa using (hasDerivAt_id' t).sub_const b
    have h := HasDerivAt.scomp t (sol.hasDeriv (t - b)
      (by simpa only [zero_sub, zero_add] using htime t ht)) hshift
    simpa [g, Function.comp_def] using h
  have hgcont : ContinuousOn g (Icc a b) := by
    intro t ht
    exact (hgderiv t ht).continuousAt.continuousWithinAt
  have hgS : ∀ t ∈ Icc a b, g t ∈ S := by
    intro t ht
    apply hδsub
    rw [Metric.mem_ball]
    have htr : b - r ≤ t := le_trans hbr ht.1
    have hrr : r ≤ δ / 2 := min_le_right _ _
    have htb : t ≤ b := ht.2
    have habs : |t - b| ≤ r := by
      rw [abs_le]
      constructor <;> linarith
    have hlt : |t - b| < δ := by linarith
    simpa [Real.dist_eq] using hlt
  have heq : EqOn p g (Icc a b) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun _ y ↦ G y) (s := fun _ ↦ S) (K := K)
    · intro t ht
      exact hK
    · exact hpcont
    · exact hpderiv
    · exact hpS
    · exact hgcont
    · intro t ht
      exact (hgderiv t ⟨le_of_lt ht.1, ht.2⟩).hasDerivWithinAt
    · intro t ht
      exact hgS t ⟨le_of_lt ht.1, ht.2⟩
    · simp [p, g, sol.initial]
  refine ⟨sol, ?_⟩
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Ioo a b, Ioo_mem_nhdsLT ha, ?_⟩
  intro t ht
  have hpq : p t = q t := by simp [p, ht.2]
  exact hpq.symm.trans (heq ⟨ht.1.le, ht.2.le⟩)

/-- The endpoint restart is local in time: it remains valid when the ODE
equation is known only on a sufficiently small left neighbourhood of the
endpoint. -/
theorem exists_localFirstOrderSolution_eventuallyEq_left_of_tendsto_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {q : ℝ → E} {G : E → E} {b : ℝ} {x : E}
    (hG : ContDiffAt ℝ 1 G x)
    (hderiv : ∀ᶠ t in 𝓝[<] b, HasDerivAt q (G (q t)) t)
    (hlim : Tendsto q (𝓝[<] b) (𝓝 x)) :
    ∃ sol : LocalFirstOrderSolution (fun _ y ↦ G y) 0 x,
      q =ᶠ[𝓝[<] b] (fun t ↦ sol.curve (t - b)) := by
  obtain ⟨K, S, hS, hK⟩ := hG.exists_lipschitzOnWith
  obtain ⟨aD, haD, hderivTail⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp hderiv
  have haDlt : aD < b := haD
  have hGtime : ContDiffAt ℝ 1 (fun z : ℝ × E ↦ G z.2) (0, x) :=
    hG.comp (0, x) contDiffAt_snd
  obtain ⟨sol⟩ := exists_localFirstOrderSolution_of_contDiffAt
    (f := fun _ y ↦ G y) hGtime
  have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hsol_cont : ContinuousAt sol.curve 0 :=
    (sol.hasDeriv 0 (by simpa only [zero_sub, zero_add] using hzero)).continuousAt
  have hsolS : sol.curve ⁻¹' S ∈ 𝓝 (0 : ℝ) := by
    have hS0 : S ∈ 𝓝 (sol.curve 0) := by simpa [sol.initial] using hS
    exact hsol_cont.preimage_mem_nhds hS0
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hsolS
  have hqS : q ⁻¹' S ∈ 𝓝[<] b := hlim hS
  obtain ⟨a₀, ha₀, hqSsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hqS
  let r : ℝ := min (sol.radius / 2) (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith [sol.radius_pos]) (by linarith)
  let a : ℝ := max a₀ (max (b - r) ((aD + b) / 2))
  have hmid : (aD + b) / 2 < b := by linarith [haDlt]
  have ha : a < b := by
    dsimp [a]
    apply max_lt
    · exact ha₀
    · apply max_lt
      · exact sub_lt_self b hr
      · exact hmid
  have haD : aD < a := by
    dsimp [a]
    have hmidD : aD < (aD + b) / 2 := by linarith [haDlt]
    exact lt_of_lt_of_le hmidD
      (le_trans (le_max_right (b - r) ((aD + b) / 2))
        (le_max_right a₀ (max (b - r) ((aD + b) / 2))))
  have ha₀ : a₀ ≤ a := by
    dsimp [a]
    exact le_max_left _ _
  have hbr : b - r ≤ a := by
    dsimp [a]
    exact le_trans (le_max_left _ _)
      (le_max_right a₀ (max (b - r) ((aD + b) / 2)))
  let p : ℝ → E := fun t ↦ if t < b then q t else x
  let g : ℝ → E := fun t ↦ sol.curve (t - b)
  have hpcont : ContinuousOn p (Icc a b) := by
    apply continuousOn_leftExtension ha
    intro t ht
    exact (hderivTail ⟨lt_of_lt_of_le haD ht.1, ht.2⟩).continuousAt
    exact hlim
  have hpderiv : ∀ t ∈ Ioc a b,
      HasDerivWithinAt p (G (p t)) (Iic t) t := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | htb
    · have heq : p =ᶠ[𝓝 t] q := by
        filter_upwards [Iio_mem_nhds htb] with s hs
        change s < b at hs
        simp [p, hs]
      have hq : HasDerivAt q (G (q t)) t :=
        hderivTail ⟨lt_trans haD ht.1, htb⟩
      have hp : HasDerivAt p (G (q t)) t := hq.congr_of_eventuallyEq heq
      convert hp.hasDerivWithinAt using 1 <;> simp [p, htb]
    · subst t
      simpa [p] using hasDerivWithinAt_leftExtension_endpoint_eventually
        (hG := hG.continuousAt) hderiv hlim
  have hpS : ∀ t ∈ Ioc a b, p t ∈ S := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | htb
    · have hmem : t ∈ Ioo a₀ b :=
        ⟨lt_of_le_of_lt ha₀ ht.1, htb⟩
      simpa [p, htb] using hqSsub hmem
    · subst t
      simpa [p] using mem_of_mem_nhds hS
  have htime : ∀ t ∈ Icc a b, t - b ∈ Ioo (-sol.radius) sol.radius := by
    intro t ht
    have htr : b - r ≤ t := le_trans hbr ht.1
    have hrr : r ≤ sol.radius / 2 := min_le_left _ _
    have htb : t ≤ b := ht.2
    constructor <;> linarith [sol.radius_pos]
  have hgderiv : ∀ t ∈ Icc a b, HasDerivAt g (G (g t)) t := by
    intro t ht
    have hshift : HasDerivAt (fun s : ℝ ↦ s - b) 1 t := by
      simpa using (hasDerivAt_id' t).sub_const b
    have h := HasDerivAt.scomp t (sol.hasDeriv (t - b)
      (by simpa only [zero_sub, zero_add] using htime t ht)) hshift
    simpa [g, Function.comp_def] using h
  have hgcont : ContinuousOn g (Icc a b) := by
    intro t ht
    exact (hgderiv t ht).continuousAt.continuousWithinAt
  have hgS : ∀ t ∈ Icc a b, g t ∈ S := by
    intro t ht
    apply hδsub
    rw [Metric.mem_ball]
    have htr : b - r ≤ t := le_trans hbr ht.1
    have hrr : r ≤ δ / 2 := min_le_right _ _
    have htb : t ≤ b := ht.2
    have habs : |t - b| ≤ r := by
      rw [abs_le]
      constructor <;> linarith
    have hlt : |t - b| < δ := by linarith
    simpa [Real.dist_eq] using hlt
  have heq : EqOn p g (Icc a b) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun _ y ↦ G y) (s := fun _ ↦ S) (K := K)
    · intro t ht
      exact hK
    · exact hpcont
    · exact hpderiv
    · exact hpS
    · exact hgcont
    · intro t ht
      exact (hgderiv t ⟨le_of_lt ht.1, ht.2⟩).hasDerivWithinAt
    · intro t ht
      exact hgS t ⟨le_of_lt ht.1, ht.2⟩
    · simp [p, g, sol.initial]
  refine ⟨sol, ?_⟩
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Ioo a b, Ioo_mem_nhdsLT ha, ?_⟩
  intro t ht
  have hpq : p t = q t := by simp [p, ht.2]
  exact hpq.symm.trans (heq ⟨ht.1.le, ht.2.le⟩)

/-!
### Endpoint continuation for linear transport
-/

/-- The fibre component of a clock-augmented local solution is a local
solution of the correspondingly translated linear transport equation.  The
clock identity is proved on a deliberately smaller interval, rather than
being treated as an implicit property of the augmented system. -/
def LocalFirstOrderSolution.toLocalLinearTransportSolutionOfClock
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → E →L[ℝ] E} {b : ℝ} {x : E}
    (sol : LocalFirstOrderSolution
      (fun _ (p : ℝ × E) ↦ (1, -(A p.1) p.2)) 0 (b, x)) :
    LocalLinearTransportSolution (fun s ↦ A (b + s)) 0 x := by
  let r : ℝ := sol.radius / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith [sol.radius_pos]
  have hclock : ∀ s ∈ Ioo (-r) r, (sol.curve s).1 = b + s := by
    have hfst : ∀ s ∈ Icc (-r) r,
        HasDerivAt (fun u : ℝ ↦ (sol.curve u).1) 1 s := by
      intro s hs
      have hsopen : s ∈ Ioo (-sol.radius) sol.radius := by
        dsimp [r] at hs
        constructor <;> linarith [sol.radius_pos, hs.1, hs.2]
      have h := (sol.hasDeriv s
        (by simpa only [zero_sub, zero_add] using hsopen)).hasFDerivAt.fst.hasDerivAt
      simpa using h
    have hdiff : DifferentiableOn ℝ
        (fun s : ℝ ↦ (sol.curve s).1 - s) (Ioo (-r) r) := by
      intro s hs
      have hsIcc : s ∈ Icc (-r) r := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      exact ((hfst s hsIcc).sub (hasDerivAt_id' s)).differentiableAt
        |>.differentiableWithinAt
    have hderiv : Set.EqOn (deriv (fun s : ℝ ↦ (sol.curve s).1 - s))
        (fun _ ↦ (0 : ℝ)) (Ioo (-r) r) := by
      intro s hs
      have hsIcc : s ∈ Icc (-r) r := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      change deriv ((fun s : ℝ ↦ (sol.curve s).1) - (fun s ↦ s)) s = 0
      rw [((hfst s hsIcc).sub (hasDerivAt_id' s)).deriv]
      norm_num
    have hzero : (0 : ℝ) ∈ Ioo (-r) r := by
      constructor <;> linarith
    have hconst : ∀ s ∈ Ioo (-r) r,
        ((fun u : ℝ ↦ (sol.curve u).1 - u) 0) =
          ((fun u : ℝ ↦ (sol.curve u).1 - u) s) := by
      intro s hs
      exact isOpen_Ioo.is_const_of_deriv_eq_zero (x := 0) (y := s)
        isPreconnected_Ioo hdiff hderiv hzero hs
    intro s hs
    have hinit : (sol.curve 0).1 = b := congrArg Prod.fst sol.initial
    have hvalue := hconst s hs
    dsimp at hvalue
    linarith
  refine
    { curve := fun s ↦ (sol.curve s).2
      radius := r
      radius_pos := hr
      initial := ?_
      hasDeriv := ?_ }
  · exact congrArg Prod.snd sol.initial
  · intro s hs
    have hs' : s ∈ Ioo (-r) r := by
      simpa only [zero_sub, zero_add] using hs
    have hsopen : s ∈ Ioo (-sol.radius) sol.radius := by
      dsimp [r] at hs'
      constructor <;> linarith [sol.radius_pos, hs'.1, hs'.2]
    change HasDerivAt (fun t : ℝ ↦ (sol.curve t).2)
      (-(A (b + s)) ((sol.curve s).2)) s
    have h := (sol.hasDeriv s
      (by simpa only [zero_sub, zero_add] using hsopen)).hasFDerivAt.snd.hasDerivAt
    simpa [hclock s hs'] using h

/-- A time-dependent homogeneous linear transport equation can be restarted
at a finite left endpoint once its model-fibre solution converges.  This is
the transport-specific form of the generic autonomous restart theorem: the
clock is retained in the proof, while the returned certificate is again a
`LocalLinearTransportSolution`. -/
theorem exists_localLinearTransportSolution_eventuallyEq_left_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A : ℝ → E →L[ℝ] E} {q : ℝ → E} {b : ℝ} {x : E}
    (hA : ContDiffAt ℝ 1 A b)
    (hderiv : ∀ t ∈ Iio b, HasDerivAt q (-(A t) (q t)) t)
    (hlim : Tendsto q (𝓝[<] b) (𝓝 x)) :
    ∃ sol : LocalLinearTransportSolution (fun s ↦ A (b + s)) 0 x,
      q =ᶠ[𝓝[<] b] (fun t ↦ sol.curve (t - b)) := by
  let F : ℝ × E → ℝ × E := fun p ↦ (1, -(A p.1) p.2)
  let Q : ℝ → ℝ × E := fun t ↦ (t, q t)
  have hsystem : ContDiffAt ℝ 1 F (b, x) := by
    have hA' : ContDiffAt ℝ 1 (fun p : ℝ × E ↦ A p.1) (b, x) :=
      hA.comp (b, x) contDiffAt_fst
    simpa [F] using contDiffAt_const.prodMk (hA'.clm_apply contDiffAt_snd).neg
  have hQderiv : ∀ t ∈ Iio b, HasDerivAt Q (F (Q t)) t := by
    intro t ht
    simpa [Q, F] using (hasDerivAt_id' t).prodMk (hderiv t ht)
  have htime : Tendsto (fun t : ℝ ↦ t) (𝓝[<] b) (𝓝 b) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hQlim : Tendsto Q (𝓝[<] b) (𝓝 (b, x)) := by
    exact htime.prodMk_nhds hlim
  obtain ⟨sol, hsol⟩ :=
    exists_localFirstOrderSolution_eventuallyEq_left_of_tendsto
      (q := Q) (G := F) hsystem hQderiv hQlim
  let transport := sol.toLocalLinearTransportSolutionOfClock (A := A)
    (b := b) (x := x)
  refine ⟨transport, ?_⟩
  filter_upwards [hsol] with t ht
  change q t = (sol.curve (t - b)).2
  simpa [Q] using congrArg Prod.snd ht

/-- The linear-transport endpoint restart is tail-local in its differential
equation, matching the form obtained after a partial field enters one fixed
endpoint chart. -/
theorem exists_localLinearTransportSolution_eventuallyEq_left_of_tendsto_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A : ℝ → E →L[ℝ] E} {q : ℝ → E} {b : ℝ} {x : E}
    (hA : ContDiffAt ℝ 1 A b)
    (hderiv : ∀ᶠ t in 𝓝[<] b, HasDerivAt q (-(A t) (q t)) t)
    (hlim : Tendsto q (𝓝[<] b) (𝓝 x)) :
    ∃ sol : LocalLinearTransportSolution (fun s ↦ A (b + s)) 0 x,
      q =ᶠ[𝓝[<] b] (fun t ↦ sol.curve (t - b)) := by
  let F : ℝ × E → ℝ × E := fun p ↦ (1, -(A p.1) p.2)
  let Q : ℝ → ℝ × E := fun t ↦ (t, q t)
  have hsystem : ContDiffAt ℝ 1 F (b, x) := by
    have hA' : ContDiffAt ℝ 1 (fun p : ℝ × E ↦ A p.1) (b, x) :=
      hA.comp (b, x) contDiffAt_fst
    simpa [F] using contDiffAt_const.prodMk (hA'.clm_apply contDiffAt_snd).neg
  have hQderiv : ∀ᶠ t in 𝓝[<] b, HasDerivAt Q (F (Q t)) t := by
    filter_upwards [hderiv] with t ht
    simpa [Q, F] using (hasDerivAt_id' t).prodMk ht
  have htime : Tendsto (fun t : ℝ ↦ t) (𝓝[<] b) (𝓝 b) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hQlim : Tendsto Q (𝓝[<] b) (𝓝 (b, x)) := by
    exact htime.prodMk_nhds hlim
  obtain ⟨sol, hsol⟩ :=
    exists_localFirstOrderSolution_eventuallyEq_left_of_tendsto_eventually
      (q := Q) (G := F) hsystem hQderiv hQlim
  let transport := sol.toLocalLinearTransportSolutionOfClock (A := A)
    (b := b) (x := x)
  refine ⟨transport, ?_⟩
  filter_upwards [hsol] with t ht
  change q t = (sol.curve (t - b)).2
  simpa [Q] using congrArg Prod.snd ht

/-- Uniform bounds for the coefficient operator and a transport solution
bound its derivative on a final left tail.  Combined with the finite-speed
lemma, this supplies the model-fibre limit required by transport restart. -/
theorem exists_tendsto_nhdsLT_of_linearTransport_of_norm_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A : ℝ → E →L[ℝ] E} {q : ℝ → E} {b C_A C_q : ℝ}
    (hCA : 0 ≤ C_A) (hCq : 0 ≤ C_q)
    (hderiv : ∀ᶠ t in 𝓝[<] b, HasDerivAt q (-(A t) (q t)) t)
    (hA : ∀ᶠ t in 𝓝[<] b, ‖A t‖ ≤ C_A)
    (hq : ∀ᶠ t in 𝓝[<] b, ‖q t‖ ≤ C_q) :
    ∃ x : E, Tendsto q (𝓝[<] b) (𝓝 x) := by
  have hbound : ∀ᶠ t in 𝓝[<] b, ‖-(A t) (q t)‖ ≤ C_A * C_q := by
    filter_upwards [hA, hq] with t htA htq
    calc
      ‖-(A t) (q t)‖ = ‖(A t) (q t)‖ := norm_neg _
      _ ≤ ‖A t‖ * ‖q t‖ := (A t).le_opNorm _
      _ ≤ C_A * C_q := mul_le_mul htA htq (norm_nonneg _) hCA
  exact exists_tendsto_nhdsLT_of_norm_deriv_eventually_le_of_eventually
    (mul_nonneg hCA hCq) hderiv hbound

/-- A bounded linear transport tail crosses a finite endpoint.  This is the
analytic continuation package needed for a maximal parallel field: local
metric preservation supplies the field bound, local coefficient control
supplies the operator bound, and the returned solution is written in the
translated endpoint time coordinate. -/
theorem exists_localLinearTransportSolution_eventuallyEq_left_of_norm_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A : ℝ → E →L[ℝ] E} {q : ℝ → E} {b C_A C_q : ℝ}
    (hAcont : ContDiffAt ℝ 1 A b)
    (hCA : 0 ≤ C_A) (hCq : 0 ≤ C_q)
    (hderiv : ∀ᶠ t in 𝓝[<] b, HasDerivAt q (-(A t) (q t)) t)
    (hA : ∀ᶠ t in 𝓝[<] b, ‖A t‖ ≤ C_A)
    (hq : ∀ᶠ t in 𝓝[<] b, ‖q t‖ ≤ C_q) :
    ∃ x : E, ∃ sol : LocalLinearTransportSolution (fun s ↦ A (b + s)) 0 x,
      q =ᶠ[𝓝[<] b] (fun t ↦ sol.curve (t - b)) := by
  obtain ⟨x, hlim⟩ :=
    exists_tendsto_nhdsLT_of_linearTransport_of_norm_bounds
      hCA hCq hderiv hA hq
  obtain ⟨sol, hsol⟩ :=
    exists_localLinearTransportSolution_eventuallyEq_left_of_tendsto_eventually
      hAcont hderiv hlim
  exact ⟨x, sol, hsol⟩

/-- Read a local first-order solution of the standard second-order system as
the corresponding local second-order solution. -/
def LocalFirstOrderSolution.toLocalSecondOrderSolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E → E} {z₀ u₀ : E}
    (sol : LocalFirstOrderSolution
      (fun (_ : ℝ) (q : E × E) ↦ secondOrderSystem F q) 0 (z₀, u₀)) :
    LocalSecondOrderSolution F z₀ u₀ where
  curve := fun t ↦ (sol.curve t).1
  velocity := fun t ↦ (sol.curve t).2
  radius := sol.radius
  radius_pos := sol.radius_pos
  initial_curve := congrArg Prod.fst sol.initial
  initial_velocity := congrArg Prod.snd sol.initial
  curve_hasDeriv := by
    intro t ht
    have h := sol.hasDeriv t (by simpa only [zero_sub, zero_add] using ht)
    simpa [secondOrderSystem] using h.hasFDerivAt.fst.hasDerivAt
  velocity_hasDeriv := by
    intro t ht
    have h := sol.hasDeriv t (by simpa only [zero_sub, zero_add] using ht)
    simpa [secondOrderSystem] using h.hasFDerivAt.snd.hasDerivAt

/-- The endpoint-restart theorem specialized to a second-order ODE.  This is
the form used by the coordinate geodesic equation: once the coordinate
position and velocity have a common finite limit, a new local geodesic state
continues the old coordinate state across that time. -/
theorem exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E → E} {z u : ℝ → E} {b : ℝ} {z₀ u₀ : E}
    (hF : ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q) (z₀, u₀))
    (hderiv : ∀ t ∈ Iio b,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem F (z t, u t)) t)
    (hlim : Tendsto (fun t ↦ (z t, u t)) (𝓝[<] b) (𝓝 (z₀, u₀))) :
    ∃ sol : LocalSecondOrderSolution F z₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] b]
        (fun t ↦ (sol.curve (t - b), sol.velocity (t - b))) := by
  obtain ⟨sol, hsol⟩ := exists_localFirstOrderSolution_eventuallyEq_left_of_tendsto
    (G := secondOrderSystem F) hF hderiv hlim
  refine ⟨sol.toLocalSecondOrderSolution, ?_⟩
  filter_upwards [hsol] with t ht
  simpa [LocalFirstOrderSolution.toLocalSecondOrderSolution] using ht

/-- The second-order endpoint restart inherits the tail-local derivative
form of the first-order continuation theorem. -/
theorem exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E → E} {z u : ℝ → E} {b : ℝ} {z₀ u₀ : E}
    (hF : ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q) (z₀, u₀))
    (hderiv : ∀ᶠ t in 𝓝[<] b,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem F (z t, u t)) t)
    (hlim : Tendsto (fun t ↦ (z t, u t)) (𝓝[<] b) (𝓝 (z₀, u₀))) :
    ∃ sol : LocalSecondOrderSolution F z₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] b]
        (fun t ↦ (sol.curve (t - b), sol.velocity (t - b))) := by
  obtain ⟨sol, hsol⟩ :=
    exists_localFirstOrderSolution_eventuallyEq_left_of_tendsto_eventually
      (G := secondOrderSystem F) hF hderiv hlim
  refine ⟨sol.toLocalSecondOrderSolution, ?_⟩
  filter_upwards [hsol] with t ht
  simpa [LocalFirstOrderSolution.toLocalSecondOrderSolution] using ht

/-- A convergent position coordinate and a bounded acceleration force the
full second-order state to have a left endpoint.  The resulting local solution
is the ODE-side continuation of that state. -/
theorem exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E → E} {z u : ℝ → E} {b C : ℝ} {z₀ : E}
    (hF : ∀ u₀ : E,
      ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q) (z₀, u₀))
    (hderiv : ∀ t ∈ Iio b,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem F (z t, u t)) t)
    (hzlim : Tendsto z (𝓝[<] b) (𝓝 z₀))
    (hC : 0 ≤ C)
    (hacc : ∀ t ∈ Iio b, ‖F (z t) (u t)‖ ≤ C) :
    ∃ u₀ : E, ∃ sol : LocalSecondOrderSolution F z₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] b]
        (fun t ↦ (sol.curve (t - b), sol.velocity (t - b))) := by
  have hud : ∀ t ∈ Iio b, HasDerivAt u (F (z t) (u t)) t := by
    intro t ht
    have h := hderiv t ht
    simpa [secondOrderSystem] using h.hasFDerivAt.snd.hasDerivAt
  obtain ⟨u₀, hulim⟩ := exists_tendsto_nhdsLT_of_norm_deriv_le
    (f := u) (f' := fun t ↦ F (z t) (u t)) hC hud hacc
  refine ⟨u₀, ?_⟩
  exact exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto
    (hF u₀) hderiv (hzlim.prodMk_nhds hulim)

/-- The acceleration estimate in endpoint continuation need only hold on a
left neighbourhood of the endpoint.  Coordinate compactness arguments yield
exactly this eventual form after the curve enters an endpoint chart. -/
theorem exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E → E} {z u : ℝ → E} {b C : ℝ} {z₀ : E}
    (hF : ∀ u₀ : E,
      ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q) (z₀, u₀))
    (hderiv : ∀ t ∈ Iio b,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem F (z t, u t)) t)
    (hzlim : Tendsto z (𝓝[<] b) (𝓝 z₀))
    (hC : 0 ≤ C)
    (hacc : ∀ᶠ t in 𝓝[<] b, ‖F (z t) (u t)‖ ≤ C) :
    ∃ u₀ : E, ∃ sol : LocalSecondOrderSolution F z₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] b]
        (fun t ↦ (sol.curve (t - b), sol.velocity (t - b))) := by
  have hud : ∀ t ∈ Iio b, HasDerivAt u (F (z t) (u t)) t := by
    intro t ht
    have h := hderiv t ht
    simpa [secondOrderSystem] using h.hasFDerivAt.snd.hasDerivAt
  obtain ⟨u₀, hulim⟩ := exists_tendsto_nhdsLT_of_norm_deriv_eventually_le
    (f := u) (f' := fun t ↦ F (z t) (u t)) hC hud hacc
  refine ⟨u₀, ?_⟩
  exact exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto
    (hF u₀) hderiv (hzlim.prodMk_nhds hulim)

/-- Full second-order endpoint continuation is tail-local in both the ODE
identity and the acceleration estimate. -/
theorem exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound_eventually_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E → E} {z u : ℝ → E} {b C : ℝ} {z₀ : E}
    (hF : ∀ u₀ : E,
      ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q) (z₀, u₀))
    (hderiv : ∀ᶠ t in 𝓝[<] b,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem F (z t, u t)) t)
    (hzlim : Tendsto z (𝓝[<] b) (𝓝 z₀))
    (hC : 0 ≤ C)
    (hacc : ∀ᶠ t in 𝓝[<] b, ‖F (z t) (u t)‖ ≤ C) :
    ∃ u₀ : E, ∃ sol : LocalSecondOrderSolution F z₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] b]
        (fun t ↦ (sol.curve (t - b), sol.velocity (t - b))) := by
  have hud : ∀ᶠ t in 𝓝[<] b, HasDerivAt u (F (z t) (u t)) t := by
    filter_upwards [hderiv] with t ht
    simpa [secondOrderSystem] using ht.hasFDerivAt.snd.hasDerivAt
  obtain ⟨u₀, hulim⟩ :=
    exists_tendsto_nhdsLT_of_norm_deriv_eventually_le_of_eventually
      (f := u) (f' := fun t ↦ F (z t) (u t)) hC hud hacc
  refine ⟨u₀, ?_⟩
  exact exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto_eventually
    (hF u₀) hderiv (hzlim.prodMk_nhds hulim)

end BonnetMyersEntry
