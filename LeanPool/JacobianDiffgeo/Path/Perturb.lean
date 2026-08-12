/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Path.Chain
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Perturbing a path off a finite set (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §7). Every path with endpoints
off a finite set `S` is homotopic (rel endpoints) to one whose whole range avoids `S`.

Main declarations:
* `RS.nonempty_open_diff_finite` — a nonempty open subset of a manifold minus a finite set is
  still nonempty.
* `RS.exists_homotopic_avoiding_of_ball` — the single-chart-ball base case (planar avoidance
  transported through the chart).
* `RS.exists_homotopic_avoiding` / `RS.Loop.exists_homotopic_avoiding` — the general theorem:
  any path (loop) with endpoints (basepoint) off a finite set `S` is homotopic rel endpoints to
  one avoiding `S` entirely.
-/

open scoped ContDiff Manifold Topology unitInterval
open IsManifold Metric Set Filter

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {x y z : X}

omit [IsManifold 𝓘(ℂ) ω X] in
/-- A nonempty open subset of `X` minus a finite set is still nonempty (through a chart,
`ℂ`-minus-countable-is-dense). -/
theorem nonempty_open_diff_finite {U : Set X} (hU : IsOpen U) (hne : U.Nonempty)
    {S : Set X} (hS : S.Finite) : (U \ S).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  set e := chartAt ℂ p with he_def
  have hUop : IsOpen (e '' (U ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hU.inter e.open_source) inter_subset_right
  have hUne : (e '' (U ∩ e.source)).Nonempty := ⟨e p, p, ⟨hp, mem_chart_source ℂ p⟩, rfl⟩
  have hTcount : (e '' (S ∩ e.source)).Countable :=
    ((hS.inter_of_left e.source).image e).countable
  obtain ⟨z, hzT, hzU⟩ := (hTcount.dense_compl ℝ).exists_mem_open hUop hUne
  obtain ⟨q, ⟨hqU, hqsrc⟩, rfl⟩ := hzU
  refine ⟨q, hqU, ?_⟩
  intro hqS
  exact hzT ⟨q, ⟨hqS, hqsrc⟩, rfl⟩

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Base case: a path lying entirely inside one chart-ball `(e, ball c r)`, with endpoints off a
finite set `S`, is homotopic rel endpoints to a path whose range avoids `S` entirely. -/
theorem exists_homotopic_avoiding_of_ball {a b : X} (γ : Path a b)
    {e : OpenPartialHomeomorph X ℂ} (_he : e ∈ maximalAtlas 𝓘(ℂ) ω X)
    {c : ℂ} {r : ℝ} (hballsub : ball c r ⊆ e.target)
    (hγsrc : range ⇑γ ⊆ e.source) (hγball : ∀ t : ↥unitInterval, e (γ t) ∈ ball c r)
    {S : Set X} (hS : S.Finite) (ha : a ∉ S) (hb : b ∉ S) :
    ∃ γ' : Path a b, γ.Homotopic γ' ∧ Disjoint (Set.range ⇑γ') S := by
  have haSrc : a ∈ e.source := hγsrc γ.source_mem_range
  have hbSrc : b ∈ e.source := hγsrc γ.target_mem_range
  have haeq : e.symm (e a) = a := e.left_inv haSrc
  have hbeq : e.symm (e b) = b := e.left_inv hbSrc
  have hcontE : ContinuousOn e (range ⇑γ) := e.continuousOn.mono hγsrc
  set p : Path (e a) (e b) := γ.map' hcontE with hp_def
  have hprange : ∀ t : ↥unitInterval, p t ∈ ball c r := hγball
  have heaB : e a ∈ ball c r := by have := hprange 0; rwa [p.source] at this
  have hebB : e b ∈ ball c r := by have := hprange 1; rwa [p.target] at this
  set T : Set ℂ := e '' (S ∩ e.source) with hT_def
  have hTcount : T.Countable := ((hS.inter_of_left e.source).image e).countable
  have heaT : e a ∉ T := by
    rintro ⟨w, ⟨hwS, hwsrc⟩, hwe⟩
    apply ha
    have : w = a := by rw [← e.left_inv hwsrc, hwe]; exact haeq
    rwa [this] at hwS
  have hebT : e b ∉ T := by
    rintro ⟨w, ⟨hwS, hwsrc⟩, hwe⟩
    apply hb
    have : w = b := by rw [← e.left_inv hwsrc, hwe]; exact hbeq
    rwa [this] at hwS
  have hpc := Convex.isPathConnected_diff_countable (convex_ball c r) isOpen_ball
    ⟨e a, heaB⟩ hTcount
  have hjoin : JoinedIn (ball c r \ T) (e a) (e b) :=
    hpc.joinedIn (e a) ⟨heaB, heaT⟩ (e b) ⟨hebB, hebT⟩
  set q : Path (e a) (e b) := hjoin.somePath with hq_def
  have hqmem : ∀ t, q t ∈ ball c r \ T := hjoin.somePath_mem
  have hpB : range ⇑p ⊆ ball c r := by rintro z ⟨t, rfl⟩; exact hprange t
  have hqB : range ⇑q ⊆ ball c r := by rintro z ⟨t, rfl⟩; exact (hqmem t).1
  obtain ⟨Hpq, hHrange⟩ := exists_homotopy_range_subset_of_convex (convex_ball c r) hpB hqB
  have hHcont : Continuous (fun z : ↥unitInterval × ↥unitInterval => e.symm (Hpq z)) :=
    e.continuousOn_symm.comp_continuous Hpq.continuous (fun z => hballsub (hHrange z))
  have hH0 : ∀ t : ↥unitInterval, e.symm (Hpq (t, 0)) = a := fun t => by
    rw [Hpq.source]; exact haeq
  have hH1 : ∀ t : ↥unitInterval, e.symm (Hpq (t, 1)) = b := fun t => by
    rw [Hpq.target]; exact hbeq
  have hHzero : ∀ u : ↥unitInterval, e.symm (Hpq (0, u)) = γ u := fun u => by
    have h1 : (Hpq.eval 0) u = Hpq (0, u) := rfl
    rw [Hpq.eval_zero] at h1
    rw [← h1]
    change e.symm (e (γ u)) = γ u
    exact e.left_inv (hγsrc (mem_range_self u))
  have hHone : ∀ u : ↥unitInterval, e.symm (Hpq (1, u)) = e.symm (q u) := fun u => by
    have h1 : (Hpq.eval 1) u = Hpq (1, u) := rfl
    rw [Hpq.eval_one] at h1
    rw [← h1]
  have hqcontS : ContinuousOn e.symm (range ⇑q) := e.continuousOn_symm.mono (hqB.trans hballsub)
  set γ'' : Path a b :=
    ⟨⟨fun u => e.symm (q u),
        hqcontS.comp_continuous q.continuous (fun u => mem_range_self u)⟩,
      by change e.symm (q 0) = a; rw [q.source]; exact haeq,
      by change e.symm (q 1) = b; rw [q.target]; exact hbeq⟩ with hγ''_def
  have hSdisjoint : ∀ z ∈ ball c r \ T, e.symm z ∉ S := by
    intro z hz hzS
    have hzTarget : z ∈ e.target := hballsub hz.1
    have hzSrc : e.symm z ∈ e.source := e.map_target hzTarget
    exact hz.2 ⟨e.symm z, ⟨hzS, hzSrc⟩, e.right_inv hzTarget⟩
  refine ⟨γ'', ⟨{ toFun := fun z => e.symm (Hpq z)
                  continuous_toFun := hHcont
                  map_zero_left := hHzero
                  map_one_left := hHone
                  prop' := fun t x hx => by
                    rcases hx with hx | hx
                    · rw [hx]
                      change e.symm (Hpq (t, 0)) = γ 0
                      rw [γ.source]; exact hH0 t
                    · rw [Set.mem_singleton_iff] at hx
                      rw [hx]
                      change e.symm (Hpq (t, 1)) = γ 1
                      rw [γ.target]; exact hH1 t }⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨t, ht⟩ hzS
  rw [← ht] at hzS
  exact hSdisjoint (q t) (hqmem t) hzS

/-!
### Splitting a truncation at an intermediate time (design §7 step 0, risk R4)

`γ|[c,e] ≃ γ|[c,d] ⬝ γ|[d,e]` rel endpoints: the concatenation is the reparametrisation of
`γ.truncateOfLE : Path (γ.extend c) (γ.extend e)` by the piecewise clock
`ρ u = if u ≤ 1/2 then min (2u) d else max (2u - 1) d`, so `Path.Homotopy.reparam` applies.
-/

private theorem homotopic_truncateOfLE_trans {Y : Type*} [TopologicalSpace Y] {x y : Y}
    (γ : Path x y) {c d e : ℝ} (h0d : 0 ≤ d) (hd1 : d ≤ 1) (hcd : c ≤ d) (hde : d ≤ e) :
    (γ.truncateOfLE (hcd.trans hde)).Homotopic
      ((γ.truncateOfLE hcd).trans (γ.truncateOfLE hde)) := by
  have hmem : ∀ u : ↥unitInterval,
      (if (u : ℝ) ≤ 1 / 2 then min (2 * (u : ℝ)) d else max (2 * (u : ℝ) - 1) d)
        ∈ (unitInterval : Set ℝ) := by
    intro u
    split_ifs with h
    · exact ⟨le_min (mul_nonneg zero_le_two u.2.1) h0d, (min_le_right _ _).trans hd1⟩
    · exact ⟨h0d.trans (le_max_right _ _), max_le (by linarith [u.2.2]) hd1⟩
  set ρ : ↥unitInterval → ↥unitInterval := fun u =>
    ⟨if (u : ℝ) ≤ 1 / 2 then min (2 * (u : ℝ)) d else max (2 * (u : ℝ) - 1) d, hmem u⟩
    with hρ_def
  have hρcont : Continuous ρ := by
    rw [hρ_def]
    refine Continuous.subtype_mk ?_ _
    refine Continuous.if_le ?_ ?_ continuous_subtype_val continuous_const ?_
    · exact (continuous_const.mul continuous_subtype_val).min continuous_const
    · exact ((continuous_const.mul continuous_subtype_val).sub continuous_const).max
        continuous_const
    · intro u hu
      rw [hu]
      norm_num [min_eq_right hd1, max_eq_right h0d]
  have hρ0 : ρ 0 = 0 := by
    apply Subtype.ext
    change (if ((0 : ℝ)) ≤ 1 / 2 then min (2 * (0 : ℝ)) d else max (2 * (0 : ℝ) - 1) d) = (0 : ℝ)
    rw [ite_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num [min_eq_left h0d]
  have hρ1 : ρ 1 = 1 := by
    apply Subtype.ext
    change (if ((1 : ℝ)) ≤ 1 / 2 then min (2 * (1 : ℝ)) d else max (2 * (1 : ℝ) - 1) d) = (1 : ℝ)
    rw [ite_eq_right (by norm_num : ¬((1 : ℝ) ≤ 1 / 2))]
    norm_num [max_eq_left hd1]
  have hkey : (γ.truncateOfLE hcd).trans (γ.truncateOfLE hde) =
      (γ.truncateOfLE (hcd.trans hde)).reparam ρ hρcont hρ0 hρ1 := by
    ext u
    rw [Path.trans_apply]
    simp only [Path.coe_reparam, Function.comp_apply]
    split_ifs with h
    · change γ.extend (min (max (2 * (u : ℝ)) c) d) =
        γ.extend (min (max ((ρ u : ↥unitInterval) : ℝ) c) e)
      have hρu : ((ρ u : ↥unitInterval) : ℝ) = min (2 * (u : ℝ)) d := by
        change (if (u : ℝ) ≤ 1 / 2 then min (2 * (u : ℝ)) d else max (2 * (u : ℝ) - 1) d) = _
        rw [ite_eq_left h]
      rw [hρu]
      rcases le_total (2 * (u : ℝ)) d with hv | hv
      · rw [min_eq_left hv, min_eq_left (max_le hv hcd),
          min_eq_left ((max_le hv hcd).trans hde)]
      · rw [min_eq_right hv, max_eq_left hcd, min_eq_right (hv.trans (le_max_left _ _)),
          min_eq_left hde]
    · change γ.extend (min (max (2 * (u : ℝ) - 1) d) e) =
        γ.extend (min (max ((ρ u : ↥unitInterval) : ℝ) c) e)
      have hρu : ((ρ u : ↥unitInterval) : ℝ) = max (2 * (u : ℝ) - 1) d := by
        change (if (u : ℝ) ≤ 1 / 2 then min (2 * (u : ℝ)) d else max (2 * (u : ℝ) - 1) d) = _
        rw [ite_eq_right h]
      rw [hρu, max_eq_left (hcd.trans (le_max_right (2 * (u : ℝ) - 1) d))]
  rw [hkey]
  exact ⟨Path.Homotopy.reparam (γ.truncateOfLE (hcd.trans hde)) ρ hρcont hρ0 hρ1⟩

/-!
### The general (multi-chart) theorem

Downward induction along a `ChartChain` (design §7 steps 1–3). The invariant carried by
`exists_homotopic_avoiding_aux`: given a "lead-in" path `σ` from a point `q ∉ S` to the chain
breakpoint `γ.extend (t k)`, lying entirely inside chart-ball `k`, the composite
`σ ⬝ γ|[t k, 1]` is homotopic rel endpoints to an `S`-avoiding path. Each step splits off
`γ|[t k, t (k+1)]` (via `homotopic_truncateOfLE_trans`), picks a *fresh* breakpoint `q' ∉ S`
near `γ.extend (t (k+1))` inside the image of the overlap of chart-balls `k` and `k+1`
(ℂ-minus-countable density through the chart, as in `nonempty_open_diff_finite`), connects it
with an arc inside the overlap, perturbs the single-ball head via
`exists_homotopic_avoiding_of_ball`, recurses on the tail, and glues with the groupoid-law
homotopies (`Path.Homotopic.trans_assoc`/`trans_symm`/`refl_trans`).
-/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem exists_homotopic_avoiding_aux {a b : X} (γ : Path a b) {S : Set X}
    (hS : S.Finite) (hb : b ∉ S) (C : ChartChain γ) :
    ∀ r k : ℕ, C.n ≤ k + r → ∀ hk1 : C.t k ≤ 1, ∀ (q : X) (p : Path q (γ.extend (C.t k))),
      q ∉ S →
      (∀ u : ↥unitInterval, p u ∈ (C.e k).source ∧ C.e k (p u) ∈ ball (C.c k) (C.r k)) →
      ∃ τ : Path q (γ.extend 1),
        (p.trans (γ.truncateOfLE hk1)).Homotopic τ ∧ Disjoint (Set.range ⇑τ) S := by
  intro r
  induction r with
  | zero =>
    -- all of `γ|[t k, 1]` still lies in chart-ball `k` (`t (k+1) = 1` already): one-ball case.
    intro k hkn hk1 q p hq hp
    have hb1 : γ.extend 1 ∉ S := by rw [γ.extend_one]; exact hb
    have htr : ∀ u : ↥unitInterval, (γ.truncateOfLE hk1) u ∈ (C.e k).source ∧
        C.e k ((γ.truncateOfLE hk1) u) ∈ ball (C.c k) (C.r k) := by
      intro u
      have hrfl : (γ.truncateOfLE hk1) u = γ.extend (min (max (u : ℝ) (C.t k)) 1) := rfl
      rw [hrfl]
      refine C.maps k _ ⟨le_min (le_max_right _ _) hk1, ?_⟩
      rw [C.ht1 (k + 1) (by omega)]
      exact min_le_right _ _
    have hall : ∀ z ∈ Set.range ⇑(p.trans (γ.truncateOfLE hk1)),
        z ∈ (C.e k).source ∧ C.e k z ∈ ball (C.c k) (C.r k) := by
      intro z hz
      rw [Path.trans_range] at hz
      rcases hz with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact hp u
      · exact htr u
    exact exists_homotopic_avoiding_of_ball (p.trans (γ.truncateOfLE hk1)) (C.he k)
      (C.ball_subset k) (fun z hz => (hall z hz).1)
      (fun u => (hall _ (mem_range_self u)).2) hS hq hb1
  | succ r ih =>
    intro k hkn hk1 q p hq hp
    have hcd : C.t k ≤ C.t (k + 1) := C.mono (Nat.le_succ k)
    have h0d : (0 : ℝ) ≤ C.t (k + 1) := by
      rw [← C.ht0]; exact C.mono (Nat.zero_le _)
    have hd1 : C.t (k + 1) ≤ 1 := by
      rw [← C.ht1 (k + 1 + C.n) (by omega)]
      exact C.mono (by omega)
    -- split the tail at the next breakpoint
    have hdec := homotopic_truncateOfLE_trans γ h0d hd1 hcd hd1
    -- the breakpoint value lies in both adjacent chart-ball domains
    have hm0 : γ.extend (C.t (k + 1)) ∈ (C.e k).source ∧
        C.e k (γ.extend (C.t (k + 1))) ∈ ball (C.c k) (C.r k) :=
      C.maps k _ ⟨hcd, le_refl _⟩
    have hm1 : γ.extend (C.t (k + 1)) ∈ (C.e (k + 1)).source ∧
        C.e (k + 1) (γ.extend (C.t (k + 1))) ∈ ball (C.c (k + 1)) (C.r (k + 1)) :=
      C.maps (k + 1) _ ⟨le_refl _, C.mono (Nat.le_succ _)⟩
    -- the open overlap of the two chart-ball domains, and its chart image
    set W : Set X := ((C.e k).source ∩ C.e k ⁻¹' ball (C.c k) (C.r k)) ∩
        ((C.e (k + 1)).source ∩ C.e (k + 1) ⁻¹' ball (C.c (k + 1)) (C.r (k + 1))) with hW_def
    have hWopen : IsOpen W := ((C.e k).isOpen_inter_preimage isOpen_ball).inter
      ((C.e (k + 1)).isOpen_inter_preimage isOpen_ball)
    have hmW : γ.extend (C.t (k + 1)) ∈ W := ⟨⟨hm0.1, hm0.2⟩, ⟨hm1.1, hm1.2⟩⟩
    have hWsrc : W ⊆ (C.e (k + 1)).source := fun z hz => hz.2.1
    have hVopen : IsOpen (C.e (k + 1) '' W) :=
      (C.e (k + 1)).isOpen_image_of_subset_source hWopen hWsrc
    obtain ⟨ε, hε, hballV⟩ := Metric.isOpen_iff.mp hVopen
      (C.e (k + 1) (γ.extend (C.t (k + 1)))) ⟨γ.extend (C.t (k + 1)), hmW, rfl⟩
    have hVtarget : C.e (k + 1) '' W ⊆ (C.e (k + 1)).target := by
      rintro _ ⟨z, hz, rfl⟩
      exact (C.e (k + 1)).map_source (hWsrc hz)
    have hballtarget : ball (C.e (k + 1) (γ.extend (C.t (k + 1)))) ε ⊆ (C.e (k + 1)).target :=
      hballV.trans hVtarget
    -- a fresh breakpoint off `S`, found in the chart via countable-complement density
    have hTcount : (C.e (k + 1) '' (S ∩ (C.e (k + 1)).source)).Countable :=
      ((hS.inter_of_left (C.e (k + 1)).source).image (C.e (k + 1))).countable
    obtain ⟨z', hz'T, hz'ball⟩ := (hTcount.dense_compl ℝ).exists_mem_open isOpen_ball
      ⟨_, mem_ball_self hε⟩
    -- a planar arc from the breakpoint's chart image to the fresh point, inside the small ball
    obtain ⟨sg, hsg⟩ : JoinedIn (ball (C.e (k + 1) (γ.extend (C.t (k + 1)))) ε)
        (C.e (k + 1) (γ.extend (C.t (k + 1)))) z' :=
      ((convex_ball _ _).isPathConnected ⟨_, mem_ball_self hε⟩).joinedIn
        _ (mem_ball_self hε) _ hz'ball
    -- transport the arc back to `X`; it stays inside the overlap `W`
    have hsgW : ∀ u : ↥unitInterval, (C.e (k + 1)).symm (sg u) ∈ W := by
      intro u
      obtain ⟨w, hw, hwe⟩ := hballV (hsg u)
      rw [← hwe, (C.e (k + 1)).left_inv (hWsrc hw)]
      exact hw
    have hsgcont : Continuous fun u : ↥unitInterval => (C.e (k + 1)).symm (sg u) :=
      ((C.e (k + 1)).continuousOn_symm.mono hballtarget).comp_continuous sg.continuous hsg
    set arc : Path (γ.extend (C.t (k + 1))) ((C.e (k + 1)).symm z') :=
      ⟨⟨fun u => (C.e (k + 1)).symm (sg u), hsgcont⟩,
        by change (C.e (k + 1)).symm (sg 0) = _
           rw [sg.source]; exact (C.e (k + 1)).left_inv hm1.1,
        by change (C.e (k + 1)).symm (sg 1) = _
           rw [sg.target]⟩ with harc_def
    have hq'S : (C.e (k + 1)).symm z' ∉ S := by
      intro hq'S
      have hq'W : (C.e (k + 1)).symm z' ∈ W := by
        have h1 := hsgW 1
        rwa [sg.target] at h1
      exact hz'T ⟨(C.e (k + 1)).symm z', ⟨hq'S, hWsrc hq'W⟩,
        (C.e (k + 1)).right_inv (hballtarget hz'ball)⟩
    -- head piece `σ ⬝ γ|[t k, t (k+1)] ⬝ arc` lies in chart-ball `k`: one-ball perturbation
    have hmidD : ∀ u : ↥unitInterval, (γ.truncateOfLE hcd) u ∈ (C.e k).source ∧
        C.e k ((γ.truncateOfLE hcd) u) ∈ ball (C.c k) (C.r k) := by
      intro u
      have hrfl : (γ.truncateOfLE hcd) u
          = γ.extend (min (max (u : ℝ) (C.t k)) (C.t (k + 1))) := rfl
      rw [hrfl]
      exact C.maps k _ ⟨le_min (le_max_right _ _) hcd, min_le_right _ _⟩
    have hheadD : ∀ z ∈ Set.range ⇑((p.trans (γ.truncateOfLE hcd)).trans arc),
        z ∈ (C.e k).source ∧ C.e k z ∈ ball (C.c k) (C.r k) := by
      intro z hz
      rw [Path.trans_range, Path.trans_range] at hz
      rcases hz with (⟨u, rfl⟩ | ⟨u, rfl⟩) | ⟨u, rfl⟩
      · exact hp u
      · exact hmidD u
      · exact ⟨(hsgW u).1.1, (hsgW u).1.2⟩
    obtain ⟨head', hheadhom, hheaddisj⟩ :=
      exists_homotopic_avoiding_of_ball ((p.trans (γ.truncateOfLE hcd)).trans arc)
        (C.he k) (C.ball_subset k) (fun z hz => (hheadD z hz).1)
        (fun u => (hheadD _ (mem_range_self u)).2) hS hq hq'S
    -- tail piece `arc.symm ⬝ γ|[t (k+1), 1]`: induction hypothesis with lead-in `arc.symm`
    have harcsymmD : ∀ u : ↥unitInterval, arc.symm u ∈ (C.e (k + 1)).source ∧
        C.e (k + 1) (arc.symm u) ∈ ball (C.c (k + 1)) (C.r (k + 1)) := by
      intro u
      have h1 : arc.symm u ∈ W := hsgW (unitInterval.symm u)
      exact ⟨h1.2.1, h1.2.2⟩
    obtain ⟨τ', hτ'hom, hτ'disj⟩ := ih (k + 1) (by omega) hd1 ((C.e (k + 1)).symm z')
      arc.symm hq'S harcsymmD
    refine ⟨head'.trans τ', ?_, ?_⟩
    · -- homotopy bookkeeping: insert `arc ⬝ arc.symm` at the breakpoint and reassociate
      have h1 : (p.trans (γ.truncateOfLE hk1)).Homotopic
          (p.trans ((γ.truncateOfLE hcd).trans (γ.truncateOfLE hd1))) :=
        (Path.Homotopic.refl p).hcomp hdec
      have h2 : (p.trans ((γ.truncateOfLE hcd).trans (γ.truncateOfLE hd1))).Homotopic
          ((p.trans (γ.truncateOfLE hcd)).trans (γ.truncateOfLE hd1)) :=
        (Path.Homotopic.trans_assoc p (γ.truncateOfLE hcd) (γ.truncateOfLE hd1)).symm
      have h3 : (arc.trans (arc.symm.trans (γ.truncateOfLE hd1))).Homotopic
          (γ.truncateOfLE hd1) :=
        ((Path.Homotopic.trans_assoc arc arc.symm (γ.truncateOfLE hd1)).symm.trans
          ((Path.Homotopic.trans_symm arc).hcomp
            (Path.Homotopic.refl (γ.truncateOfLE hd1)))).trans
          (Path.Homotopic.refl_trans (γ.truncateOfLE hd1))
      have h4 : ((p.trans (γ.truncateOfLE hcd)).trans (γ.truncateOfLE hd1)).Homotopic
          (((p.trans (γ.truncateOfLE hcd)).trans arc).trans
            (arc.symm.trans (γ.truncateOfLE hd1))) :=
        ((Path.Homotopic.trans_assoc (p.trans (γ.truncateOfLE hcd)) arc
          (arc.symm.trans (γ.truncateOfLE hd1))).trans
          ((Path.Homotopic.refl (p.trans (γ.truncateOfLE hcd))).hcomp h3)).symm
      have h5 : ((((p.trans (γ.truncateOfLE hcd)).trans arc)).trans
          (arc.symm.trans (γ.truncateOfLE hd1))).Homotopic (head'.trans τ') :=
        hheadhom.hcomp hτ'hom
      exact ((h1.trans h2).trans h4).trans h5
    · rw [Path.trans_range]
      exact Set.disjoint_union_left.mpr ⟨hheaddisj, hτ'disj⟩

theorem exists_homotopic_avoiding {a b : X} (γ : Path a b) {S : Set X} (hS : S.Finite)
    (ha : a ∉ S) (hb : b ∉ S) :
    ∃ γ' : Path a b, γ.Homotopic γ' ∧ Disjoint (Set.range ⇑γ') S := by
  obtain ⟨C⟩ := exists_chartChain γ
  have h01 : C.t 0 ≤ 1 := by rw [C.ht0]; exact zero_le_one
  have hstart : γ.extend (C.t 0) = a := by rw [C.ht0, γ.extend_zero]
  set p0 : Path a (γ.extend (C.t 0)) := (Path.refl a).cast rfl hstart with hp0_def
  have hp0D : ∀ u : ↥unitInterval, p0 u ∈ (C.e 0).source ∧
      C.e 0 (p0 u) ∈ ball (C.c 0) (C.r 0) := by
    intro u
    have h1 : p0 u = γ.extend (C.t 0) := by
      change a = γ.extend (C.t 0)
      exact hstart.symm
    rw [h1]
    exact C.maps 0 _ ⟨le_refl _, C.mono (Nat.zero_le 1)⟩
  obtain ⟨τ, hτhom, hτdisj⟩ := exists_homotopic_avoiding_aux γ hS hb C C.n 0
    (by omega) h01 a p0 ha hp0D
  refine ⟨τ.cast rfl γ.extend_one.symm, ?_, ?_⟩
  · have hcast : ((p0.trans (γ.truncateOfLE h01)).cast rfl γ.extend_one.symm).Homotopic
        (τ.cast rfl γ.extend_one.symm) :=
      hτhom.pathCast rfl γ.extend_one.symm
    have heq : (p0.trans (γ.truncateOfLE h01)).cast rfl γ.extend_one.symm =
        (Path.refl a).trans γ := by
      ext u
      change (p0.trans (γ.truncateOfLE h01)) u = ((Path.refl a).trans γ) u
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs with h
      · rfl
      · change γ.extend (min (max (2 * (u : ℝ) - 1) (C.t 0)) 1) = _
        have h0' : (0 : ℝ) ≤ 2 * (u : ℝ) - 1 := by
          have := not_le.mp h; linarith
        have h1' : 2 * (u : ℝ) - 1 ≤ 1 := by linarith [u.2.2]
        rw [C.ht0, max_eq_left h0', min_eq_left h1', γ.extend_apply ⟨h0', h1'⟩]
    rw [heq] at hcast
    exact (Path.Homotopic.refl_trans γ).symm.trans hcast
  · have hre : Set.range ⇑(τ.cast rfl γ.extend_one.symm) = Set.range ⇑τ := by
      rw [Path.cast_coe]
    rw [hre]
    exact hτdisj

/-- Loop version (the blueprint's deliverable). -/
theorem Loop.exists_homotopic_avoiding {x₀ : X} (γ : Path x₀ x₀) {S : Set X} (hS : S.Finite)
    (hx₀ : x₀ ∉ S) : ∃ γ' : Path x₀ x₀, γ.Homotopic γ' ∧ Disjoint (Set.range ⇑γ') S :=
  RS.exists_homotopic_avoiding γ hS hx₀ hx₀

end RS

end
