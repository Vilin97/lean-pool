/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.OptimizerRadius

/-!
Fresh maximizing coordinates and signs for the finite resisting construction.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower

/-- The first `T` coordinates of the ambient dimension. -/
def horizonCoordinates (d T : ℕ) (hTd : T ≤ d) : Finset (Fin d) :=
  (Finset.univ : Finset (Fin T)).image (Fin.castLEEmb hTd)

lemma horizonCoordinates_card (d T : ℕ) (hTd : T ≤ d) :
    (horizonCoordinates d T hTd).card = T := by
  unfold horizonCoordinates
  rw [Finset.card_image_of_injective _ (Fin.castLEEmb hTd).injective]
  simp

lemma mem_horizonCoordinates_iff {d T : ℕ} (hTd : T ≤ d) (j : Fin d) :
    j ∈ horizonCoordinates d T hTd ↔ j.val < T := by
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact i.isLt
  · intro hj
    let i : Fin T := ⟨j.val, hj⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl

/-- At every chronological stage `t<T`, fewer than `T` previously selected
coordinates leave a nonempty legal horizon set; compact finiteness then gives
an unused coordinate maximizing the current absolute coordinate. -/
lemma exists_unused_max_coordinate {d T t : ℕ} (hTd : T ≤ d) (ht : t < T)
    (sigma : ℕ → Fin d) (q : Point d) :
    ∃ j : Fin d, j.val < T ∧ (∀ s < t, sigma s ≠ j) ∧
      ∀ k : Fin d, k.val < T → (∀ s < t, sigma s ≠ k) →
        |q k| ≤ |q j| := by
  classical
  let used : Finset (Fin d) := (Finset.range t).image sigma
  let available : Finset (Fin d) := horizonCoordinates d T hTd \ used
  have husedCard : used.card ≤ t := by
    dsimp [used]
    exact (Finset.card_image_le).trans_eq (Finset.card_range t)
  have havailable : available.Nonempty := by
    by_contra hempty
    have hsubset : horizonCoordinates d T hTd ⊆ used := by
      intro j hj
      by_contra hju
      have : j ∈ available := Finset.mem_sdiff.mpr ⟨hj, hju⟩
      exact hempty ⟨j, this⟩
    have hcard := Finset.card_le_card hsubset
    rw [horizonCoordinates_card] at hcard
    omega
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image available (fun k => |q k|) havailable
  refine ⟨j, ?_, ?_, ?_⟩
  · exact (mem_horizonCoordinates_iff hTd j).mp (Finset.mem_sdiff.mp hj).1
  · intro s hs hsEq
    have hused : j ∈ used := Finset.mem_image.mpr
      ⟨s, Finset.mem_range.mpr hs, hsEq⟩
    exact (Finset.mem_sdiff.mp hj).2 hused
  · intro k hkT hkunused
    apply hmax k
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_horizonCoordinates_iff hTd k).mpr hkT, ?_⟩
    intro hkUsed
    rcases Finset.mem_image.mp hkUsed with ⟨s, hs, hsEq⟩
    exact hkunused s (Finset.mem_range.mp hs) hsEq

/-- A sign whose product with the input is its absolute value, choosing one at zero. -/
noncomputable def resistingSign (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

lemma resistingSign_spec (a : ℝ) :
    (resistingSign a = 1 ∨ resistingSign a = -1) ∧
      resistingSign a * a = |a| := by
  unfold resistingSign
  split_ifs with h
  · exact ⟨Or.inl rfl, by simp [abs_of_nonneg h]⟩
  · have ha : a < 0 := lt_of_not_ge h
    exact ⟨Or.inr rfl, by simp [abs_of_neg ha]⟩

end V7.Stage5AboveTwoLowerS5A2Envelope
