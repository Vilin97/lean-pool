/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.ClassCount
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic

/-! # The inner-range weights (4.6)–(4.7) and their validity

With class constants `b a = Bse p K N a`, dimensions `L`, and `top a = L a + (b a - 4)/2`:
* `w (a, i) = i + (b a - 4)/2` for `a ≠ 0`;
* `w (0, i) = min (2 i + (b 0 - 4)/2) (min_{c ≠ 0} top c)`.
If `top a - 1 ≤ top c` for all `a, c ≠ 0` (P) and `top a - 1 ≤ 2 L 0 + (b 0 - 4)/2` for `a ≠ 0`
(Z), then `v_p^G(Δ) ≥ 2 ∑ w`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {m : ℕ}

/-- `top a = L a + (b a - 4)/2`. -/
@[expose] noncomputable def topw (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) (a : Fin (m + 1)) : ℚ :=
  L a + (b a - 4) / 2

/-- The minimum of `top` over the ordinary classes. -/
@[expose] noncomputable def tmin (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) : ℚ :=
  (Finset.univ.erase (0 : Fin (m + 1))).inf' ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩ (topw L b)

lemma tmin_le (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) {c : Fin (m + 1)} (hc : c ≠ 0) :
    tmin hm L b ≤ topw L b c :=
  Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩)

/-- The weights. -/
noncomputable def winner (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  if s.1 = 0 then min (2 * (s.2 : ℚ) + (b 0 - 4) / 2) (tmin hm L b)
  else (s.2 : ℚ) + (b s.1 - 4) / 2

/-- The abstract class inequality. -/
theorem winner_ACI (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (hP : ∀ a c : Fin (m + 1), a ≠ 0 → c ≠ 0 → topw L b a - 1 ≤ topw L b c)
    (hZ : ∀ a : Fin (m + 1), a ≠ 0 → topw L b a - 1 ≤ 2 * L 0 + (b 0 - 4) / 2)
    (s t : Σ a : Fin (m + 1), Fin (L a)) (a : Fin (m + 1)) :
    winner hm L b s + winner hm L b t + 4 ≤
      b a + (if a = 0 then 2 else 1) * ((nu L s a : ℚ) + nu L t a) := by
  -- basic facts
  have F1 : ∀ u : Σ a : Fin (m + 1), Fin (L a), u.1 ≠ 0 → winner hm L b u ≤ topw L b u.1 - 1 := by
    intro u hu
    unfold winner topw; rw [ite_eq_right hu]
    have : (u.2 : ℚ) ≤ L u.1 - 1 := by
      have := u.2.isLt; have : (u.2 : ℕ) + 1 ≤ L u.1 := this
      have : ((u.2 : ℕ) : ℚ) + 1 ≤ L u.1 := by exact_mod_cast this
      linarith
    linarith
  have F3 :
    ∀ u : Σ a : Fin (m + 1), Fin (L a), ∀ c : Fin (m + 1), c ≠ 0 → winner hm L b u ≤ topw L b c :=
  by
    intro u c hc
    by_cases hu : u.1 = 0
    · unfold winner; rw [ite_eq_left hu]
      exact (min_le_right _ _).trans (tmin_le hm L b hc)
    · linarith [F1 u hu, hP u.1 c hu hc]
  have Fz :
    ∀ u : Σ a : Fin (m + 1), Fin (L a),
      winner hm L b u ≤ (if u.1 = 0 then 2 * (u.2 : ℚ) else 2 * (L 0 : ℚ)) + (b 0 - 4) / 2 := by
    intro u
    by_cases hu : u.1 = 0
    · unfold winner; rw [ite_eq_left hu, ite_eq_left hu]; exact min_le_left _ _
    · rw [ite_eq_right hu]; linarith [F1 u hu, hZ u.1 hu]
  unfold nu
  by_cases ha : a = 0
  · subst ha
    rw [ite_eq_left rfl, show (((0 : Fin (m + 1)) : ℕ)) = 0 from rfl]
    have h1 := Fz s; have h2 := Fz t
    by_cases hs : s.1 = 0 <;> by_cases ht : t.1 = 0
    · rw [ite_eq_left hs.symm, ite_eq_left ht.symm]; rw [ite_eq_left hs] at h1;
      rw [ite_eq_left ht] at h2; linarith
    · rw [ite_eq_left hs.symm, ite_eq_right (Ne.symm ht)]; rw [ite_eq_left hs] at h1;
      rw [ite_eq_right ht] at h2
      linarith
    · rw [ite_eq_right (Ne.symm hs), ite_eq_left ht.symm]; rw [ite_eq_right hs] at h1;
      rw [ite_eq_left ht] at h2
      linarith
    · rw [ite_eq_right (Ne.symm hs), ite_eq_right (Ne.symm ht)]; rw [ite_eq_right hs] at h1;
      rw [ite_eq_right ht] at h2
      linarith
  · rw [ite_eq_right ha, one_mul]
    have htop : b a - 4 = 2 * (topw L b a - L a) := by unfold topw; ring
    by_cases hs : a = s.1 <;> by_cases ht : a = t.1
    · rw [ite_eq_left hs, ite_eq_left ht]
      have e1 : winner hm L b s = (s.2 : ℚ) + (b a - 4) / 2 := by
        unfold winner;
        rw [ite_eq_right (hs ▸ ha)]; simp only [hs]
      have e2 : winner hm L b t = (t.2 : ℚ) + (b a - 4) / 2 := by
        unfold winner;
        rw [ite_eq_right (ht ▸ ha)]; simp only [ht]
      rw [e1, e2]; linarith
    · rw [ite_eq_left hs, ite_eq_right ht]
      have e1 : winner hm L b s = (s.2 : ℚ) + (b a - 4) / 2 := by
        unfold winner;
        rw [ite_eq_right (hs ▸ ha)]; simp only [hs]
      have := F3 t a ha
      rw [e1]; unfold topw at this; linarith
    · rw [ite_eq_right hs, ite_eq_left ht]
      have e2 : winner hm L b t = (t.2 : ℚ) + (b a - 4) / 2 := by
        unfold winner;
        rw [ite_eq_right (ht ▸ ha)]; simp only [ht]
      have := F3 s a ha
      rw [e2]; unfold topw at this; linarith
    · rw [ite_eq_right hs, ite_eq_right ht]
      have h1 := F3 s a ha; have h2 := F3 t a ha
      unfold topw at h1 h2; linarith

/-- **Inner-range determinant bound** for an allocation satisfying (P) and (Z). -/
theorem inner_bound {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hm : 2 * m + 1 = p) (hm1 : 1 ≤ m)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n) (hsep : Sep p (PlK (40 * n)))
    (hK : 40 * n < p ^ 2) (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hP :
      ∀ a c : Fin (m + 1),
        a ≠ 0 → c ≠ 0 → topw L (Bse p (40 * n) (3 * n)) a - 1 ≤ topw L (Bse p (40 * n) (3 * n)) c)
    (hZ :
      ∀ a : Fin (m + 1),
        a ≠ 0 →
          topw L (Bse p (40 * n) (3 * n)) a - 1 ≤ 2 * L 0 + (Bse p (40 * n) (3 * n) 0 - 4) / 2) :
    GV p (Δ n) (2 * ∑ s, winner hm1 L (Bse p (40 * n) (3 * n)) s) := by
  refine class_frame hp5 hm n L hL _ hsep hK hdeg fun s t c => ?_
  rw [classCount_eq hm]
  exact winner_ACI hm1 L _ hP hZ s t (ccls hm c)

/-! ### Capped weights: validity needs only the zero-class condition -/

/-- Uncapped weights. -/
@[expose]
noncomputable def wraw (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  if s.1 = 0 then 2 * (s.2 : ℚ) + (b 0 - 4) / 2 else (s.2 : ℚ) + (b s.1 - 4) / 2

/-- Capped weights `min (wraw) (min_{c ≠ 0} top c)`. -/
@[expose] noncomputable def wcap (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  min (wraw L b s) (tmin hm L b)

theorem wcap_ACI (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (hZ : tmin hm L b ≤ 2 * L 0 + (b 0 - 4) / 2) (s t : Σ a : Fin (m + 1), Fin (L a))
    (a : Fin (m + 1)) :
    wcap hm L b s + wcap hm L b t + 4 ≤
      b a + (if a = 0 then 2 else 1) * ((nu L s a : ℚ) + nu L t a) := by
  have F3 :
    ∀ u : Σ a : Fin (m + 1), Fin (L a), ∀ c : Fin (m + 1), c ≠ 0 → wcap hm L b u ≤ topw L b c :=
    fun u c hc => (min_le_right _ _).trans (tmin_le hm L b hc)
  have Fraw : ∀ u : Σ a : Fin (m + 1), Fin (L a), wcap hm L b u ≤ wraw L b u := fun u =>
    min_le_left _ _
  have Fz :
    ∀ u : Σ a : Fin (m + 1), Fin (L a),
      wcap hm L b u ≤ (if u.1 = 0 then 2 * (u.2 : ℚ) else 2 * (L 0 : ℚ)) + (b 0 - 4) / 2 := by
    intro u
    by_cases hu : u.1 = 0
    · rw [ite_eq_left hu]; have := Fraw u; unfold wraw at this; rw [ite_eq_left hu] at this;
      exact this
    · rw [ite_eq_right hu]; exact (min_le_right _ _).trans hZ
  unfold nu
  by_cases ha : a = 0
  · subst ha
    rw [ite_eq_left rfl, show (((0 : Fin (m + 1)) : ℕ)) = 0 from rfl]
    have h1 := Fz s; have h2 := Fz t
    by_cases hs : s.1 = 0 <;> by_cases ht : t.1 = 0
    · rw [ite_eq_left hs.symm, ite_eq_left ht.symm]; rw [ite_eq_left hs] at h1;
      rw [ite_eq_left ht] at h2; linarith
    · rw [ite_eq_left hs.symm, ite_eq_right (Ne.symm ht)]; rw [ite_eq_left hs] at h1;
      rw [ite_eq_right ht] at h2
      linarith
    · rw [ite_eq_right (Ne.symm hs), ite_eq_left ht.symm]; rw [ite_eq_right hs] at h1;
      rw [ite_eq_left ht] at h2
      linarith
    · rw [ite_eq_right (Ne.symm hs), ite_eq_right (Ne.symm ht)]; rw [ite_eq_right hs] at h1;
      rw [ite_eq_right ht] at h2
      linarith
  · rw [ite_eq_right ha, one_mul]
    have hraw :
      ∀ u : Σ a : Fin (m + 1), Fin (L a), a = u.1 → wcap hm L b u ≤ (u.2 : ℚ) + (b a - 4) / 2 := by
      intro u hu
      have := Fraw u
      unfold wraw at this; rw [ite_eq_right (hu ▸ ha)] at this; simpa only [hu] using this
    by_cases hs : a = s.1 <;> by_cases ht : a = t.1
    · rw [ite_eq_left hs, ite_eq_left ht]
      have := hraw s hs; have := hraw t ht; linarith
    · rw [ite_eq_left hs, ite_eq_right ht]
      have := hraw s hs; have h2 := F3 t a ha
      unfold topw at h2; linarith
    · rw [ite_eq_right hs, ite_eq_left ht]
      have := hraw t ht; have h2 := F3 s a ha
      unfold topw at h2; linarith
    · rw [ite_eq_right hs, ite_eq_right ht]
      have h1 := F3 s a ha; have h2 := F3 t a ha
      unfold topw at h1 h2; linarith

/-- **Inner-range determinant bound** with capped weights; only the zero-class condition. -/
theorem inner_bound_cap {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hm : 2 * m + 1 = p) (hm1 : 1 ≤ m)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n) (hsep : Sep p (PlK (40 * n)))
    (hK : 40 * n < p ^ 2) (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hZ : tmin hm1 L (Bse p (40 * n) (3 * n)) ≤ 2 * L 0 + (Bse p (40 * n) (3 * n) 0 - 4) / 2) :
    GV p (Δ n) (2 * ∑ s, wcap hm1 L (Bse p (40 * n) (3 * n)) s) := by
  refine class_frame hp5 hm n L hL _ hsep hK hdeg fun s t c => ?_
  rw [classCount_eq hm]
  exact wcap_ACI hm1 L _ hZ s t (ccls hm c)

end Zeta5Irrational
