/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoPole
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ScriptClamping

/-!
# Reaching an attachment vertex through two connector paths

`ScriptGluing` records only the principal-divisor identities needed to insert
factor scripts into an ambient graph. The first connector has an arbitrary
convex integral path potential; the second connector is constant. This avoids
requiring an isomorphism to a separately constructed path-join graph.
-/

namespace Utilities.TwoPole

universe u v w

/-- The script-level interface for two factors joined by two paths. Only the
first path length is needed: the second path always has constant potential. -/
structure ScriptGluing (A : CFGraph.{u}) (B : CFGraph.{v}) (G : CFGraph.{w})
    (p : TwoPole A) (q : TwoPole B) (L : ℕ) where
  left : A.V → G.V
  right : B.V → G.V
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  disjoint : ∀ a b, left a ≠ right b
  length_pos : 0 < L
  glue : ∀ (f : firing_script A) (g : firing_script B) (h : ℕ → ℤ),
    h 0 = f p.first →
    h L = g q.first →
    f p.second = g q.second →
    (∀ j : ℕ, 0 < j → j < L →
      0 ≤ h (j - 1) - 2 * h j + h (j + 1)) →
    ∃ σ : firing_script G,
      (∀ a, prin G σ (left a) = prin A f a +
        if a = p.first then h 1 - h 0 else 0) ∧
      (∀ b, prin G σ (right b) = prin B g b +
        if b = q.first then h (L - 1) - h L else 0) ∧
      (∀ z, (∀ a, z ≠ left a) → (∀ b, z ≠ right b) →
        0 ≤ prin G σ z)

namespace ScriptGluing

variable {A : CFGraph.{u}} {B : CFGraph.{v}} {G : CFGraph.{w}}
    {p : TwoPole A} {q : TwoPole B} {L : ℕ}

/-- Exchange the factors and reverse the first connector's potential. -/
def symm (J : ScriptGluing A B G p q L) : ScriptGluing B A G q p L where
  left := J.right
  right := J.left
  left_injective := J.right_injective
  right_injective := J.left_injective
  disjoint := fun b a => (J.disjoint a b).symm
  length_pos := J.length_pos
  glue := by
    intro f g h h0 hL hSecond hConvex
    let hr : ℕ → ℤ := fun j => h (L - j)
    have hr0 : hr 0 = g p.first := by simpa [hr] using hL
    have hrL : hr L = f q.first := by simpa [hr] using h0
    have hrConvex : ∀ j : ℕ, 0 < j → j < L →
        0 ≤ hr (j - 1) - 2 * hr j + hr (j + 1) := by
      intro j hj hjL
      have h1 : L - (j - 1) = L - j + 1 := by omega
      have h2 : L - (j + 1) = (L - j) - 1 := by omega
      have hh := hConvex (L - j) (by omega) (by omega)
      dsimp [hr]
      rw [h1, h2]
      omega
    obtain ⟨σ, hA, hB, hOutside⟩ :=
      J.glue g f hr hr0 hrL hSecond.symm hrConvex
    have hRevEnd : L - (L - 1) = 1 := by have := J.length_pos; omega
    refine ⟨σ, ?_, ?_, ?_⟩
    · intro b
      simpa only [hr, hRevEnd, Nat.sub_self] using hB b
    · intro a
      simpa only [hr, Nat.sub_zero] using hA a
    · intro z hnB hnA
      exact hOutside z hnA hnB

/-- Factor inequalities and a convex connector give a global winning script.
The ambient divisor may also carry effective chips outside the factors. -/
theorem winnable_sub_left_first_of_scripts
    (J : ScriptGluing A B G p q L)
    (D : CFDiv G) (CA : CFDiv A) (CB : CFDiv B)
    (hDA : ∀ a, D (J.left a) = CA a)
    (hDB : ∀ b, D (J.right b) = CB b)
    (hOutside : ∀ z, (∀ a, z ≠ J.left a) → (∀ b, z ≠ J.right b) → 0 ≤ D z)
    (f : firing_script A) (g : firing_script B) (h : ℕ → ℤ)
    (h0 : h 0 = f p.first) (hL : h L = g q.first)
    (hSecond : f p.second = g q.second)
    (hConvex : ∀ j : ℕ, 0 < j → j < L →
      0 ≤ h (j - 1) - 2 * h j + h (j + 1))
    (hLeft : ∀ a, 0 ≤ CA a - one_chip p.first a + prin A f a +
      if a = p.first then h 1 - h 0 else 0)
    (hRight : ∀ b, 0 ≤ CB b + prin B g b +
      if b = q.first then h (L - 1) - h L else 0) :
    winnable G (D - one_chip (J.left p.first)) := by
  obtain ⟨σ, hσA, hσB, hσOutside⟩ := J.glue f g h h0 hL hSecond hConvex
  have hEff : effective (D - one_chip (J.left p.first) + prin G σ) := by
    intro z
    by_cases hzA : ∃ a, z = J.left a
    · obtain ⟨a, rfl⟩ := hzA
      have hChip : one_chip (J.left p.first) (J.left a) = one_chip p.first a := by
        simp only [one_chip, J.left_injective.eq_iff]
      simp only [Pi.add_apply, Pi.sub_apply, hDA, hChip, hσA]
      have := hLeft a
      omega
    · have hnA : ∀ a, z ≠ J.left a := by simpa only [not_exists] using hzA
      by_cases hzB : ∃ b, z = J.right b
      · obtain ⟨b, rfl⟩ := hzB
        have hChip : one_chip (J.left p.first) (J.right b) = 0 := by
          simp only [one_chip, if_neg (J.disjoint p.first b).symm]
        simpa only [Pi.add_apply, Pi.sub_apply, hDB, hChip, sub_zero, hσB, add_assoc]
          using hRight b
      · have hnB : ∀ b, z ≠ J.right b := by simpa only [not_exists] using hzB
        have hChip : one_chip (J.left p.first) z = 0 := by
          simp only [one_chip, if_neg (hnA p.first)]
        simp only [Pi.add_apply, Pi.sub_apply, hChip, sub_zero]
        exact add_nonneg (hOutside z hnA hnB) (hσOutside z hnA hnB)
  refine ⟨D - one_chip (J.left p.first) + prin G σ, hEff, ?_⟩
  apply (principal_iff_eq_prin G _).mpr
  refine ⟨σ, ?_⟩
  abel

private theorem effective_add_prin_of_sub_one_chip
    {H : CFGraph} {C : CFDiv H} {f : firing_script H} {a : H.V}
    (h : effective (C - one_chip a + prin H f)) :
    effective (C + prin H f) := by
  intro v
  have hv := h v
  have hc := eff_one_chip (G := H) a v
  simp only [Pi.add_apply, Pi.sub_apply] at hv ⊢
  omega

/-- The three-case connector argument. Only the two local one-chip tests
are needed; the factors need not be connected or carry full pencils here. -/
theorem winnable_sub_left_first
    (J : ScriptGluing A B G p q L)
    (D : CFDiv G) (CA : CFDiv A) (CB : CFDiv B)
    (hDA : ∀ a, D (J.left a) = CA a)
    (hDB : ∀ b, D (J.right b) = CB b)
    (hOutside : ∀ z, (∀ a, z ≠ J.left a) → (∀ b, z ≠ J.right b) → 0 ≤ D z)
    (hCA : effective CA) (hCB : effective CB)
    (hWinA : winnable A (CA - one_chip p.first))
    (hWinB : winnable B (CB - one_chip q.first)) :
    winnable G (D - one_chip (J.left p.first)) := by
  obtain ⟨f, hfp, hfNonneg, hf⟩ :=
    exists_nonneg_firing_script_sub_one_chip p.first hCA hWinA
  obtain ⟨g, hgq, hgNonneg, hg⟩ :=
    exists_nonneg_firing_script_sub_one_chip q.first hCB hWinB
  have hf' := effective_add_prin_of_sub_one_chip hf
  have hg' := effective_add_prin_of_sub_one_chip hg
  let t : ℤ := f p.second
  let s : ℤ := g q.second
  have ht : 0 ≤ t := hfNonneg p.second
  have hs : 0 ≤ s := hgNonneg q.second
  have hLen : 0 < L := J.length_pos
  by_cases hts : t ≤ s
  · -- The first connector is constant; truncate only the right factor.
    let g' := clampScript g (s - t)
    have hg'q : g' q.first = 0 :=
      clampScript_eq_zero_of_eq_zero g hgq (by omega)
    have hg'q' : g' q.second = t := by
      dsimp [g', clampScript, s]
      rw [max_eq_left (by omega)]
      ring
    have hg'Eff : effective (CB + prin B g') := effective_add_prin_clamp hCB hg' _
    apply J.winnable_sub_left_first_of_scripts D CA CB hDA hDB hOutside
      f g' (fun _ => 0) (by simpa using hfp.symm)
      (by simpa using hg'q.symm) (by exact hg'q'.symm)
      (by intros; omega)
    · intro a
      simpa only [sub_self, ite_self, add_zero, Pi.add_apply, Pi.sub_apply] using hf a
    · intro b
      simpa only [sub_self, ite_self, add_zero, Pi.add_apply] using hg'Eff b
  · have hpos : 0 < t - s := by omega
    by_cases hsmall : t - s < (L : ℤ)
    · -- A convex bend creates one effective chip inside the connector.
      let k : ℤ := t - s
      let h : ℕ → ℤ := fun j => max (-k) ((j : ℤ) - (L : ℤ))
      have hzero : h 0 = -k := by
        dsimp [h]
        rw [max_eq_left (by dsimp [k]; omega)]
      have hlast : h L = 0 := by
        dsimp [h]
        rw [max_eq_right (by dsimp [k]; omega)]
        omega
      have hone : h 1 = -k := by
        dsimp [h]
        rw [max_eq_left (by dsimp [k]; omega)]
      have hpenult : h (L - 1) = -1 := by
        have hcast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
        dsimp [h]
        rw [hcast, max_eq_right (by dsimp [k]; omega)]
        omega
      have hconvex : ∀ j : ℕ, 0 < j → j < L →
          0 ≤ h (j - 1) - 2 * h j + h (j + 1) := by
        intro j hj _
        have hcast : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
        simp only [h, hcast, Nat.cast_add, Nat.cast_one, max_def]
        split_ifs <;> omega
      apply J.winnable_sub_left_first_of_scripts D CA CB hDA hDB hOutside
        (fun a => f a - k) g h (by rw [hzero, hfp]; omega)
        (by rw [hlast, hgq]) (by dsimp [k, t, s]; ring) hconvex
      · intro a
        rw [prin_sub_const, hone, hzero]
        simpa only [sub_self, ite_self, add_zero, Pi.add_apply, Pi.sub_apply] using hf a
      · intro b
        rw [hpenult, hlast]
        have hb := hg b
        by_cases hbq : b = q.first <;>
          simp only [Pi.add_apply, Pi.sub_apply, one_chip, hbq, ↓reduceIte] at hb ⊢ <;> omega
    · -- A linear connector pays for the demanded chip on the left.
      let a : ℤ := t - s - (L : ℤ)
      let f' := clampScript f a
      have ha : 0 ≤ a := by dsimp [a]; omega
      have hf'p : f' p.first = 0 := clampScript_eq_zero_of_eq_zero f hfp ha
      have hf'p' : f' p.second = s + (L : ℤ) := by
        dsimp [f', clampScript, a, t]
        rw [max_eq_left (by omega)]
        ring
      have hf'Eff : effective (CA + prin A f') := effective_add_prin_clamp hCA hf' _
      let h : ℕ → ℤ := fun j => (j : ℤ) - (L : ℤ)
      have hzero : h 0 = -(L : ℤ) := by simp [h]
      have hlast : h L = 0 := by simp [h]
      have hone : h 1 - h 0 = 1 := by simp [h]
      have hpenult : h (L - 1) - h L = -1 := by dsimp [h]; omega
      have hconvex : ∀ j : ℕ, 0 < j → j < L →
          0 ≤ h (j - 1) - 2 * h j + h (j + 1) := by
        intro j hj _
        dsimp [h]
        omega
      apply J.winnable_sub_left_first_of_scripts D CA CB hDA hDB hOutside
        (fun z => f' z - (L : ℤ)) g h (by rw [hzero, hf'p]; omega)
        (by rw [hlast, hgq]) (by rw [hf'p']; dsimp [s]; ring) hconvex
      · intro z
        rw [prin_sub_const, hone]
        have hz := hf'Eff z
        by_cases hzp : z = p.first <;>
          simp only [Pi.add_apply, one_chip, hzp, ↓reduceIte] at hz ⊢ <;> omega
      · intro b
        rw [hpenult]
        have hb := hg b
        by_cases hbq : b = q.first <;>
          simp only [Pi.add_apply, Pi.sub_apply, one_chip, hbq, ↓reduceIte] at hb ⊢ <;> omega

/-- The symmetric attachment-vertex conclusion, using the same gluing data. -/
theorem winnable_sub_right_first
    (J : ScriptGluing A B G p q L)
    (D : CFDiv G) (CA : CFDiv A) (CB : CFDiv B)
    (hDA : ∀ a, D (J.left a) = CA a)
    (hDB : ∀ b, D (J.right b) = CB b)
    (hOutside : ∀ z, (∀ a, z ≠ J.left a) → (∀ b, z ≠ J.right b) → 0 ≤ D z)
    (hCA : effective CA) (hCB : effective CB)
    (hWinA : winnable A (CA - one_chip p.first))
    (hWinB : winnable B (CB - one_chip q.first)) :
    winnable G (D - one_chip (J.right q.first)) := by
  exact J.symm.winnable_sub_left_first D CB CA hDB hDA
    (fun z hnB hnA => hOutside z hnA hnB) hCB hCA hWinB hWinA

end ScriptGluing
end Utilities.TwoPole
