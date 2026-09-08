/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.BinarySize

/-!
# Actual rare distances from binary descent heights

See the project entry module for the exact coordinate restrictions and source roles.
Every occupied height valuation supplies a different actual Euclidean rare
class. Together with binary size descent this gives n <= 2^r.
-/

namespace LeanPool.RareDistanceFields.BinaryPalette

open BinaryDescent BinarySize SplitCounts
noncomputable section

variable {P V : Type*} [Fintype V] (S : Model P)

open Classical in
/-- The simple graph joining distinct labels at the specified model distance. -/
def graph (x : V → P) (d : ℝ) : SimpleGraph V :=
  OrderedColors.colorGraph (fun a b => S.distance (x a) (x b))
    (fun _ _ => dist_comm _ _) d

open Classical in
/-- Occurring model distances whose full edge counts are at most the label count. -/
def rareDistances (x : V → P) : Finset ℝ :=
  (OrderedColors.palette (fun a b => S.distance (x a) (x b))).filter
    fun d => (graph S x d).edgeFinset.card ≤ Fintype.card V

open Classical in
/-- The 2-adic height level of a realizing pair, or zero when the distance is absent. -/
def distanceLevel (x : V → P) (d : ℝ) : ℕ :=
  if h : ∃ e : V × V, S.distance (x e.1) (x e.2) = d then
    padicValInt 2 (S.height (x (Classical.choose h).1) (x (Classical.choose h).2)) else 0

open Classical in
theorem distanceLevel_eq (x : V → P) (a b : V) :
    distanceLevel S x (S.distance (x a) (x b)) = padicValInt 2 (S.height (x a) (x b)) := by
  have h : ∃ e : V × V, S.distance (x e.1) (x e.2) = S.distance (x a) (x b) := ⟨(a, b), rfl⟩
  rw [distanceLevel, dite_eq_left h]
  rw [S.distance_height _ _ _ _ (Classical.choose_spec h)]

open Classical in
theorem level_max_rare (x : V → P) (hx : Function.Injective x) (i j : V) (hij : i ≠ j)
    (hmax : ∀ a b, a ≠ b → padicValInt 2 (S.height (x a) (x b)) =
      padicValInt 2 (S.height (x i) (x j)) → S.distance (x a) (x b) ≤ S.distance (x i) (x j)) :
    S.distance (x i) (x j) ∈ rareDistances S x := by
  have hp := S.height_pos _ _ (hx.ne hij)
  have hcast : ((S.height (x i) (x j)).toNat : ℤ) = S.height (x i) (x j) := Int.toNat_of_nonneg
    hp.le
  have hd : 0 < S.distance (x i) (x j) := dist_pos.mpr (S.point_injective.ne (hx.ne hij))
  have hc := S.level_count (S.height (x i) (x j)).toNat x hx (by omega)
    (S.distance (x i) (x j)) hd
    (fun a b he => (S.distance_height _ _ _ _ he).trans hcast.symm)
    (by simpa only [hcast] using hmax)
  have he := count_eq_twice_edges (fun a b => S.distance (x a) (x b))
    (fun _ _ => dist_comm _ _) (S.distance (x i) (x j)) (fun _ => by simpa using ne_of_lt hd)
  change _ = 2 * (graph S x (S.distance (x i) (x j))).edgeFinset.card at he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(i, j), by simp [hij], rfl⟩, ?_⟩
  omega

open Classical in
theorem rare_at_level (x : V → P) (hx : Function.Injective x) {k : ℕ}
    (hk : k ∈ levels S x) : ∃ d ∈ rareDistances S x, distanceLevel S x d = k := by
  let pairs := (Finset.univ : Finset (V × V)).filter
    fun e => e.1 ≠ e.2 ∧ padicValInt 2 (S.height (x e.1) (x e.2)) = k
  have hp : pairs.Nonempty := by
    obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp hk
    exact ⟨(a, b), by simpa [pairs] using And.intro (Finset.mem_offDiag.mp hab).2.2 he⟩
  obtain ⟨e, he, hem⟩ := pairs.exists_max_image (fun e => S.distance (x e.1) (x e.2)) hp
  have hed := (Finset.mem_filter.mp he).2
  refine ⟨S.distance (x e.1) (x e.2), level_max_rare S x hx _ _ hed.1 ?_, ?_⟩
  · intro a b hab hl
    exact hem (a, b) (by simp [pairs, hab, hl, hed.2])
  · rw [distanceLevel_eq, hed.2]

open Classical in
theorem card_le_pow_rareDistances (x : V → P) (hx : Function.Injective x) :
    Fintype.card V ≤ 2 ^ (rareDistances S x).card := by
  have hsub : levels S x ⊆ (rareDistances S x).image (distanceLevel S x) := by
    intro k hk
    obtain ⟨d, hd, hk⟩ := rare_at_level S x hx hk
    exact Finset.mem_image.mpr ⟨d, hd, hk⟩
  have hcard : (levels S x).card ≤ (rareDistances S x).card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  exact (card_le_pow_levels S x hx).trans (Nat.pow_le_pow_right (by decide) hcard)

open Classical in
theorem rareDistances_spec (x : V → P) (hx : Function.Injective x) (d : ℝ) :
    d ∈ rareDistances S x ↔ 0 < d ∧ (∃ a b, a ≠ b ∧ S.distance (x a) (x b) = d) ∧
      (graph S x d).edgeFinset.card ≤ Fintype.card V := by
  constructor
  · intro h
    obtain ⟨hp, hc⟩ := Finset.mem_filter.mp h
    obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp hp
    have hn : a ≠ b := (Finset.mem_offDiag.mp hab).2.2
    refine ⟨?_, ⟨a, b, hn, he⟩, hc⟩
    rw [←he]
    exact dist_pos.mpr (S.point_injective.ne (hx.ne hn))
  · rintro ⟨_, ⟨a, b, hab, he⟩, hc⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(a, b), by simp [hab], he⟩, hc⟩

end
end LeanPool.RareDistanceFields.BinaryPalette
