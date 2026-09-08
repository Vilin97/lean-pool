/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.RationalDivergence

/-!
# Transport by the exact distance-equality pattern

See the project entry module for the exact coordinate restrictions and source roles.
A rational planar realization of the same equality pattern transports each
whole distance class, including its unordered multiplicity. No approximation
argument and no assumption that arbitrary configurations admit such a
realization are used.
-/

namespace LeanPool.RareDistanceFields.DistancePattern

open RationalPlane
noncomputable section

variable {V : Type*} [Fintype V]

open Classical in
/-- The simple graph of all distinct label pairs at a given Euclidean distance. -/
def graph (x : V → ℂ) (d : ℝ) : SimpleGraph V :=
  OrderedColors.colorGraph (fun a b => dist (x a) (x b))
    (fun _ _ => dist_comm _ _) d

open Classical in
/-- Occurring distances whose full unordered multiplicities are at most the label count. -/
def rareDistances (x : V → ℂ) : Finset ℝ :=
  (OrderedColors.palette (fun a b => dist (x a) (x b))).filter
    fun d => (graph x d).edgeFinset.card ≤ Fintype.card V

open Classical in
/-- Rational squared-distance equality agrees exactly with real distance equality. -/
def SamePattern (y : V → Point) (x : V → ℂ) : Prop :=
  ∀ a b c d, sqDist (y a) (y b) = sqDist (y c) (y d) ↔
    dist (x a) (x b) = dist (x c) (x d)

omit [Fintype V] in
open Classical in
theorem rational_injective (y : V → Point) (x : V → ℂ)
    (hx : Function.Injective x) (hp : SamePattern y x) : Function.Injective y := by
  intro a b hab
  apply hx
  have h := (hp a b a a).mp (by rw [hab])
  simpa using h

open Classical in
theorem rare_card_transport (y : V → Point) (x : V → ℂ) (hp : SamePattern y x) :
    (RationalDivergence.rareSquared y).card ≤ (rareDistances x).card := by
  classical
  let f : ℚ → ℝ := fun r =>
    if h : ∃ a b, sqDist (y a) (y b) = r then
      dist (x h.choose) (x h.choose_spec.choose) else 0
  have hf (a b : V) : f (sqDist (y a) (y b)) = dist (x a) (x b) := by
    dsimp [f]
    split_ifs with h
    · exact (hp _ _ _ _).mp h.choose_spec.choose_spec
    · exact False.elim (h ⟨a, b, rfl⟩)
  have hg (a b : V) : RationalPlane.graph y (sqDist (y a) (y b)) =
      graph x (dist (x a) (x b)) := by
    ext c d
    simp only [RationalPlane.graph, graph, OrderedColors.colorGraph, hp c d a b]
  apply Finset.card_le_card_of_injOn f
  · intro r hr
    obtain ⟨a, b, hab, rfl⟩ := RationalDivergence.exists_pair_of_mem_rareSquared y hr
    rw [hf]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(a, b), by simp [hab], rfl⟩, ?_⟩
    exact hg a b ▸ (Finset.mem_filter.mp hr).2
  · intro r hr s hs he
    obtain ⟨a, b, _hab, rfl⟩ := RationalDivergence.exists_pair_of_mem_rareSquared y hr
    obtain ⟨c, d, _hcd, rfl⟩ := RationalDivergence.exists_pair_of_mem_rareSquared y hs
    rw [hf, hf] at he
    exact (hp a b c d).mpr he

open Classical in
theorem card_le_pow_rare (y : V → Point) (x : V → ℂ)
    (hx : Function.Injective x) (hp : SamePattern y x) :
    Fintype.card V ≤ 2 ^ (rareDistances x).card :=
  (RationalDivergence.card_le_pow_rareSquared y (rational_injective y x hx hp)).trans
    (Nat.pow_le_pow_right (by decide) (rare_card_transport y x hp))

open Classical in
theorem rareDistances_spec (x : V → ℂ) (hx : Function.Injective x)
    {d : ℝ} (hd : d ∈ rareDistances x) : 0 < d ∧
    (∃ a b, dist (x a) (x b) = d) ∧ (graph x d).edgeFinset.card ≤ Fintype.card V := by
  obtain ⟨hp, hm⟩ := Finset.mem_filter.mp hd
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨dist_pos.mpr (hx.ne (Finset.mem_offDiag.mp hab).2.2), ⟨a, b, rfl⟩, hm⟩

open Classical in
theorem two_rare_distances (y : V → Point) (x : V → ℂ)
    (hx : Function.Injective x) (hp : SamePattern y x) (hn : 3 ≤ Fintype.card V) :
    ∃ d ∈ rareDistances x, ∃ e ∈ rareDistances x, d ≠ e := by
  apply Finset.one_lt_card.mp
  have h := card_le_pow_rare y x hx hp
  by_contra hr
  have hp' : 2 ^ (rareDistances x).card ≤ 2 ^ 1 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hp'
  omega

end
end LeanPool.RareDistanceFields.DistancePattern
