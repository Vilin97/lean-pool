/-
Copyright (c) 2026 Wondermonger-daydreaming. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wondermonger-daydreaming
-/

import LeanPool.SemicircleCheck.FinRotateLemmas
import LeanPool.SemicircleCheck.RotationArithmetic
import LeanPool.SemicircleCheck.GenusNoncrossing
import LeanPool.SemicircleCheck.EvenCard

/-!
  THE CATALAN SCALPEL

  Infrastructure for the Catalan recurrence C_{n+1} = Σ C_k · C_{n-k}.

  The key insight: vertex 0 pairs with some odd vertex 2k+1, partitioning
  the remaining 2n vertices into two independent noncrossing domains:
  - Inside: {1, ..., 2k} of size 2k (supporting C_k noncrossing pairings)
  - Outside: {2k+2, ..., 2n+1} of size 2(n-k) (supporting C_{n-k})

  Our shiftTwoEquiv / contractZeroOne is the boundary case k = 0.

  Architecture:
  1. insideEquiv: Fin(2k) ≃ {i : Fin(2(n+1)) | 0 < i < 2k+1}
  2. outsideEquiv: Fin(2(n-k)) ≃ {i : Fin(2(n+1)) | 2k+1 < i}
  3. Parity theorem: p(0) is always odd for noncrossing p
  4. catalanEquiv: NoncrossingPairing(n+1) ≃ Σ k, NCP(k) × NCP(n-k)
-/

open Equiv Equiv.Perm Fintype

/-! ## 1. The Translation Dictionaries -/

/-- Maps `Fin (2*k)` into the "inside" of the chord `(0, 2k+1)`.
    Index j shifts right by 1 to clear vertex 0. -/
private def insideEquiv (n k : ℕ) (hk : k ≤ n) :
    Fin (2 * k) ≃ { i : Fin (2 * (n + 1)) // 0 < i.val ∧ i.val < 2 * k + 1 } where
  toFun j := ⟨⟨j.val + 1, by omega⟩, by constructor <;> simp⟩
  invFun i := ⟨i.val.val - 1, by omega⟩
  left_inv j := by ext; simp
  right_inv i := by ext; simp; omega

/-- Maps `Fin (2*(n-k))` into the "outside" of the chord `(0, 2k+1)`.
    Index j shifts past the chord's right endpoint: j + 2k + 2. -/
private def outsideEquiv (n k : ℕ) (hk : k ≤ n) :
    Fin (2 * (n - k)) ≃ { i : Fin (2 * (n + 1)) // 2 * k + 1 < i.val } where
  toFun j := ⟨⟨j.val + 2 * k + 2, by omega⟩, by simp⟩
  invFun i := ⟨i.val.val - (2 * k + 2), by omega⟩
  left_inv j := by ext; simp
  right_inv i := by ext; simp; omega

/-! ## 2. Arc-Crossing ↔ Recursive Noncrossing Bridge

Two definitions of "noncrossing":
- Recursive (our `IsNoncrossing`): peelable via adjacent pairs
- Arc-based (`¬HasCrossing`): no two chords interleave

The bridge connects them, using several helper lemmas:
- `finRotate_val`: value-level characterization of finRotate
- `general_shadow`: shadow closure for arbitrary arcs
- `no_crossing_has_adjacent`: every crossing-free pairing has an adjacent pair
- `HasCrossing_conj_forward`: rotation preserves crossings (5-case analysis)
- `contraction_crossing_lifts`: contraction preserves crossings -/

/-- A pairing has a crossing if two arcs interleave on the interval:
    ∃ a < b < p(a) < p(b). -/
def Pairing.HasCrossing {n : ℕ} (p : Pairing n) : Prop :=
  ∃ a b : Fin (2 * n),
    a.val < b.val ∧ b.val < (p.val a).val ∧ (p.val a).val < (p.val b).val

/-! ### Helper lemmas for the bridge -/

/-- Value-level characterization of finRotate. -/
private lemma finRotate_val' {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (finRotate m i).val = if i.val = m - 1 then 0 else i.val + 1 := by
  cases m with
  | zero => omega
  | succ m' =>
    rw [coe_finRotate]; split_ifs with h1 h2 h2
    · rfl
    · exfalso; rw [Fin.ext_iff, Fin.val_last] at h1; omega
    · exfalso; rw [Fin.ext_iff, Fin.val_last] at h1; push Not at h1; omega
    · rfl

/-- Every pairing has a vertex v with v < p(v). -/
private lemma exists_lt_partner {n : ℕ} (p : Pairing (n + 1)) :
    ∃ v : Fin (2*(n+1)), v.val < (p.val v).val := by
  by_contra h; push Not at h
  have := lt_of_le_of_ne (h ⟨0, by omega⟩)
    (fun heq => p.property.2 ⟨0, by omega⟩ (Fin.ext heq))
  simp at this

/-- General shadow closure: if p has no crossings and v < x < p(v) (with v < p(v)),
    then v < p(x) < p(v). -/
private lemma general_shadow {n : ℕ} (p : Pairing n) (h_nc : ¬p.HasCrossing)
    (v x : Fin (2 * n)) (hx_low : v.val < x.val) (hx_high : x.val < (p.val v).val) :
    v.val < (p.val x).val ∧ (p.val x).val < (p.val v).val := by
  have hinv : ∀ y, p.val (p.val y) = y := by
    intro y; have h : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
    change (p.val * p.val) y = y; simp [h]
  have hinv_val : ∀ y, (p.val (p.val y)).val = y.val := fun y => congr_arg Fin.val (hinv y)
  constructor
  · by_contra h_le; push Not at h_le
    by_cases h_eq : (p.val x).val = v.val
    · rw [show x = p.val v from by
        have := congr_arg p.val (show p.val x = v from Fin.ext h_eq)
        rw [hinv] at this; exact this
      ] at hx_high; exact lt_irrefl _ hx_high
    · refine absurd ⟨p.val x, v, by omega, ?_, ?_⟩ h_nc
      · show v.val < (p.val (p.val x)).val; rw [hinv_val]; exact hx_low
      · show (p.val (p.val x)).val < (p.val v).val; rw [hinv_val]; exact hx_high
  · by_contra h_le; push Not at h_le
    by_cases h_eq : (p.val x).val = (p.val v).val
    · exact absurd (congr_arg Fin.val (p.val.injective (Fin.ext h_eq))) (by omega)
    · exact absurd ⟨v, x, hx_low, hx_high, by omega⟩ h_nc

/-- Every crossing-free pairing on ≥ 2 points has an adjacent pair.
    Proof by min-gap argument using general_shadow. -/
private lemma no_crossing_has_adjacent {n : ℕ} (p : Pairing (n + 1))
    (h_nc : ¬p.HasCrossing) :
    ∃ i : Fin (2*(n+1)), p.hasAdjacentAt i := by
  let S := Finset.univ.filter (fun v : Fin (2*(n+1)) => v.val < (p.val v).val)
  have hS_ne : S.Nonempty := by
    obtain ⟨v, hv⟩ := exists_lt_partner p
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  by_contra h_no_adj; push Not at h_no_adj
  have h_gap_ge2 : ∀ v ∈ S, (p.val v).val ≥ v.val + 2 := by
    intro v hv
    have hvlt : v.val < (p.val v).val := (Finset.mem_filter.mp hv).2
    by_contra hlt; push Not at hlt
    have hgap1 : (p.val v).val = v.val + 1 := by omega
    have hv_not_last : v.val ≠ 2*(n+1) - 1 := by have := (p.val v).isLt; omega
    have hfr : (finRotate (2*(n+1)) v).val = v.val + 1 := by
      rw [finRotate_val' (by omega)]; simp [hv_not_last]
    exact h_no_adj v (show p.val v = finRotate _ v from Fin.ext (by omega))
  obtain ⟨v, hv_mem, hv_min⟩ := Finset.exists_min_image S
    (fun v => (p.val v).val - v.val) hS_ne
  have hv_lt : v.val < (p.val v).val := (Finset.mem_filter.mp hv_mem).2
  have hv_gap2 := h_gap_ge2 v hv_mem
  let w : Fin (2*(n+1)) := ⟨v.val + 1, by have := (p.val v).isLt; omega⟩
  have hw_val : w.val = v.val + 1 := rfl
  have hshadow := general_shadow p h_nc v w (by omega) (by omega)
  have hw_lt_pw : w.val < (p.val w).val := by
    have : (p.val w).val ≠ w.val := fun h => p.property.2 w (Fin.ext h)
    omega
  have hw_mem : w ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_lt_pw⟩
  have hgap_w_lt : (p.val w).val - w.val < (p.val v).val - v.val := by omega
  exact absurd (hv_min w hw_mem) (by omega)

/-- Mod arithmetic helper for rotation proofs. -/
private lemma mod_wrap {m x k : ℕ} (_hm : 0 < m) (hx : x < m) (_hk : k < m)
    (h : x + k ≥ m) : (x + k) % m = x + k - m := by
  rw [Nat.mod_eq_sub_mod h]; exact Nat.mod_eq_of_lt (by omega)

/-- Mod arithmetic helper for rotation proofs. -/
private lemma mod_no_wrap {m x k : ℕ} (_hm : 0 < m) (h : x + k < m) :
    (x + k) % m = x + k := Nat.mod_eq_of_lt h

/-- Rotation preserves crossings (forward direction).
    Given a crossing a < b < p(a) < p(b), we construct a crossing
    in ρpρ⁻¹ by case analysis on how many of the four values "wrap"
    under the rotation. Five cases, each resolved by omega. -/
private lemma HasCrossing_conj_forward {m : ℕ} (_hm : 2 ≤ m) (p : Equiv.Perm (Fin m))
    (hinv : ∀ x, p (p x) = x) (k : ℕ) (hk : k < m) :
    (∃ a b : Fin m, a.val < b.val ∧ b.val < (p a).val ∧ (p a).val < (p b).val) →
    let ρ := (finRotate m) ^ k
    (∃ a b : Fin m, a.val < b.val ∧ b.val < ((ρ * p * ρ⁻¹) a).val ∧
      ((ρ * p * ρ⁻¹) a).val < ((ρ * p * ρ⁻¹) b).val) := by
  intro ⟨a, b, hab, hbpa, hpapb⟩ ρ
  have hm' : 0 < m := by omega
  have conj_rho : ∀ x : Fin m, (ρ * p * ρ⁻¹) (ρ x) = ρ (p x) := by
    intro x; simp [mul_apply]
  have rho_val : ∀ x : Fin m, (ρ x).val = (x.val + k) % m := by
    intro x; exact congr_arg Fin.val (finRotate_pow_apply' hm' k x)
  set av := a.val; set bv := b.val; set pav := (p a).val; set pbv := (p b).val
  have ha_lt : av < m := a.isLt; have hb_lt : bv < m := b.isLt
  have hpa_lt : pav < m := (p a).isLt; have hpb_lt : pbv < m := (p b).isLt
  set ra := (av + k) % m; set rb := (bv + k) % m
  set rpa := (pav + k) % m; set rpb := (pbv + k) % m
  have hra : (ρ a).val = ra := rho_val a
  have hrb : (ρ b).val = rb := rho_val b
  have hrpa : (ρ (p a)).val = rpa := rho_val (p a)
  have hrpb : (ρ (p b)).val = rpb := rho_val (p b)
  have hconj_a : ((ρ * p * ρ⁻¹) (ρ a)).val = rpa := by rw [conj_rho]; exact hrpa
  have hconj_b : ((ρ * p * ρ⁻¹) (ρ b)).val = rpb := by rw [conj_rho]; exact hrpb
  have hconj_pa : ((ρ * p * ρ⁻¹) (ρ (p a))).val = ra := by
    rw [conj_rho, hinv]; exact hra
  have hconj_pb : ((ρ * p * ρ⁻¹) (ρ (p b))).val = rb := by
    rw [conj_rho, hinv]; exact hrb
  by_cases hpb_wrap : pbv + k ≥ m
  · by_cases hpa_wrap : pav + k ≥ m
    · by_cases hb_wrap : bv + k ≥ m
      · by_cases ha_wrap : av + k ≥ m
        · -- All wrap
          have hra' : ra = av + k - m := mod_wrap hm' ha_lt hk ha_wrap
          have hrb' : rb = bv + k - m := mod_wrap hm' hb_lt hk hb_wrap
          have hrpa' : rpa = pav + k - m := mod_wrap hm' hpa_lt hk hpa_wrap
          have hrpb' : rpb = pbv + k - m := mod_wrap hm' hpb_lt hk hpb_wrap
          exact ⟨ρ a, ρ b, by rw [hra, hrb, hra', hrb']; omega,
                 by rw [hconj_a, hrb, hrpa', hrb']; omega,
                 by rw [hconj_a, hconj_b, hrpa', hrpb']; omega⟩
        · -- b, pa, pb wrap
          push Not at ha_wrap
          have hra' : ra = av + k := mod_no_wrap hm' ha_wrap
          have hrb' : rb = bv + k - m := mod_wrap hm' hb_lt hk hb_wrap
          have hrpa' : rpa = pav + k - m := mod_wrap hm' hpa_lt hk hpa_wrap
          have hrpb' : rpb = pbv + k - m := mod_wrap hm' hpb_lt hk hpb_wrap
          exact ⟨ρ b, ρ (p a), by rw [hrb, hrpa, hrb', hrpa']; omega,
                 by rw [hconj_b, hrpa, hrpb', hrpa']; omega,
                 by rw [hconj_b, hconj_pa, hrpb', hra']; omega⟩
      · -- pa, pb wrap
        push Not at hb_wrap
        have hra' : ra = av + k := mod_no_wrap hm' (by omega)
        have hrb' : rb = bv + k := mod_no_wrap hm' hb_wrap
        have hrpa' : rpa = pav + k - m := mod_wrap hm' hpa_lt hk hpa_wrap
        have hrpb' : rpb = pbv + k - m := mod_wrap hm' hpb_lt hk hpb_wrap
        exact ⟨ρ (p a), ρ (p b), by rw [hrpa, hrpb, hrpa', hrpb']; omega,
               by rw [hconj_pa, hrpb, hra', hrpb']; omega,
               by rw [hconj_pa, hconj_pb, hra', hrb']; omega⟩
    · -- Only pb wraps
      push Not at hpa_wrap
      have hra' : ra = av + k := mod_no_wrap hm' (by omega)
      have hrb' : rb = bv + k := mod_no_wrap hm' (by omega)
      have hrpa' : rpa = pav + k := mod_no_wrap hm' hpa_wrap
      have hrpb' : rpb = pbv + k - m := mod_wrap hm' hpb_lt hk hpb_wrap
      exact ⟨ρ (p b), ρ a, by rw [hrpb, hra, hrpb', hra']; omega,
             by rw [hconj_pb, hra, hrb', hra']; omega,
             by rw [hconj_pb, hconj_a, hrb', hrpa']; omega⟩
  · -- No wrap
    push Not at hpb_wrap
    have hra' : ra = av + k := mod_no_wrap hm' (by omega)
    have hrb' : rb = bv + k := mod_no_wrap hm' (by omega)
    have hrpa' : rpa = pav + k := mod_no_wrap hm' (by omega)
    have hrpb' : rpb = pbv + k := mod_no_wrap hm' hpb_wrap
    exact ⟨ρ a, ρ b, by rw [hra, hrb, hra', hrb']; omega,
           by rw [hconj_a, hrb, hrpa', hrb']; omega,
           by rw [hconj_a, hconj_b, hrpa', hrpb']; omega⟩

/-- Crossing in ρpρ⁻¹ implies crossing in p. Derived from the forward direction
    by applying it with ρ⁻¹ = finRotate^(m-k). -/
private lemma HasCrossing_of_conj {m : ℕ} (hm : 2 ≤ m) (p : Equiv.Perm (Fin m))
    (hinv : ∀ x, p (p x) = x) (k : ℕ) (hk : k < m) :
    let ρ := (finRotate m) ^ k
    (∃ a b : Fin m, a.val < b.val ∧ b.val < ((ρ * p * ρ⁻¹) a).val ∧
      ((ρ * p * ρ⁻¹) a).val < ((ρ * p * ρ⁻¹) b).val) →
    (∃ a b : Fin m, a.val < b.val ∧ b.val < (p a).val ∧ (p a).val < (p b).val) := by
  intro ρ hcross
  -- When k = 0, ρ = 1 and the conjugate is already p.
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · -- ρ = (finRotate m)^0 = 1, so ρ*p*ρ⁻¹ = p
    have hρ_eq : ∀ x, (ρ * p * ρ⁻¹) x = p x := by
      intro x; simp [ρ]
    obtain ⟨a, b, hab, h1, h2⟩ := hcross
    exact ⟨a, b, hab, by rwa [hρ_eq] at h1, by rwa [hρ_eq] at h2⟩
  -- When k > 0, k' = m - k satisfies k' < m.
  have hinv' : ∀ x, (ρ * p * ρ⁻¹) ((ρ * p * ρ⁻¹) x) = x := by
    intro x; simp [ρ, mul_apply, hinv]
  set k' := m - k
  have hk'_lt : k' < m := by omega
  have hconj : (finRotate m) ^ k' * (ρ * p * ρ⁻¹) * ((finRotate m) ^ k')⁻¹ = p := by
    simp only [ρ]
    have h1 : (finRotate m) ^ k' * (finRotate m) ^ k = 1 := by
      rw [← pow_add, show k' + k = m from by omega, finRotate_pow_self' (by omega)]
    have h2 : ((finRotate m) ^ k)⁻¹ * ((finRotate m) ^ k')⁻¹ = 1 := by
      rw [← mul_inv_rev, h1, inv_one]
    calc (finRotate m) ^ k' * ((finRotate m) ^ k * p * ((finRotate m) ^ k)⁻¹) *
            ((finRotate m) ^ k')⁻¹
        = (finRotate m) ^ k' * (finRotate m) ^ k * p *
            (((finRotate m) ^ k)⁻¹ * ((finRotate m) ^ k')⁻¹) := by group
      _ = 1 * p * 1 := by rw [h1, h2]
      _ = p := by group
  have := HasCrossing_conj_forward hm (ρ * p * ρ⁻¹) hinv' k' hk'_lt hcross
  simp only at this; rwa [hconj] at this

/-- Value-level characterization of contractZeroOne. -/
private lemma contractZeroOne_val {n : ℕ} (p : Equiv.Perm (Fin (2 * (n + 1))))
    (h₀ : p ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (h₁ : p ⟨1, by omega⟩ = ⟨0, by omega⟩)
    (j : Fin (2 * n)) :
    (SemicircleCore.contractZeroOne p h₀ h₁ j).val =
      (p ⟨j.val + 2, by omega⟩).val - 2 := by
  simp [SemicircleCore.contractZeroOne, SemicircleCore.shiftTwoEquiv]

/-- Crossing in contractZeroOne lifts to crossing in the original permutation. -/
private lemma contraction_crossing_lifts {n : ℕ} (p : Equiv.Perm (Fin (2 * (n + 1))))
    (h₀ : p ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (h₁ : p ⟨1, by omega⟩ = ⟨0, by omega⟩) :
    let q := SemicircleCore.contractZeroOne p h₀ h₁
    (∃ a b : Fin (2*n), a.val < b.val ∧ b.val < (q a).val ∧ (q a).val < (q b).val) →
    (∃ a b : Fin (2*(n+1)), a.val < b.val ∧ b.val < (p a).val ∧
      (p a).val < (p b).val) := by
  intro q ⟨a, b, hab, hbqa, hqaqb⟩
  have hmaps := SemicircleCore.mapsTo_remaining h₀ h₁
  set A : Fin (2*(n+1)) := ⟨a.val + 2, by omega⟩
  set B : Fin (2*(n+1)) := ⟨b.val + 2, by omega⟩
  have hpA_ge : 2 ≤ (p A).val := hmaps (show A ∈ SemicircleCore.RemainingDomain n from by
    change 2 ≤ A.val; simp [A])
  have hpB_ge : 2 ≤ (p B).val := hmaps (show B ∈ SemicircleCore.RemainingDomain n from by
    change 2 ≤ B.val; simp [B])
  have hqa : (q a).val = (p A).val - 2 := by
    simp only [q, SemicircleCore.contractZeroOne, SemicircleCore.shiftTwoEquiv, A]
    simp [Equiv.trans_apply]
  have hqb : (q b).val = (p B).val - 2 := by
    simp only [q, SemicircleCore.contractZeroOne, SemicircleCore.shiftTwoEquiv, B]
    simp [Equiv.trans_apply]
  have h1 : A.val < B.val := by simp [A, B]; omega
  have h2 : B.val < (p A).val := by simp [A, B] at *; omega
  have h3 : (p A).val < (p B).val := by omega
  exact ⟨A, B, h1, h2, h3⟩

/-- Crossing in deleteAdjacent implies crossing in original pairing.
    Composes contraction_crossing_lifts with HasCrossing_of_conj. -/
private lemma deleteAdjacent_crossing_lifts {n : ℕ} (p : Pairing (n + 1))
    (i : Fin (2 * (n + 1))) (h : p.hasAdjacentAt i) :
    (p.deleteAdjacent i h).HasCrossing → p.HasCrossing := by
  intro hcross
  -- deleteAdjacent = contractZeroOne (ρ * p.val * ρ⁻¹)
  -- where ρ = finRotate^(2*(n+1) - i.val)
  -- Use 2*(n+1) directly (not set m) to avoid renaming i to i✝.
  let ρ : Equiv.Perm (Fin (2*(n+1))) :=
    (finRotate (2*(n+1))) ^ (2*(n+1) - i.val)
  let p' : Equiv.Perm (Fin (2*(n+1))) := ρ * p.val * ρ⁻¹
  -- Unfold hasAdjacentAt to get the explicit equation p.val i = finRotate (2*(n+1)) i
  have hadj : p.val i = finRotate (2*(n+1)) i := h
  -- Step 1: prove p'(0) = 1 and p'(1) = 0
  have h₀' : p' ⟨0, by omega⟩ = ⟨1, by omega⟩ :=
    conjugate_sends (rotate_self_eq_zero (2*(n+1)) (by omega) i)
      (rotate_succ_eq_one (2*(n+1)) i (by omega)) hadj
  have h₁' : p' ⟨1, by omega⟩ = ⟨0, by omega⟩ :=
    conjugate_sends_back (rotate_self_eq_zero (2*(n+1)) (by omega) i)
      (rotate_succ_eq_one (2*(n+1)) i (by omega)) p.property.1 hadj
  -- The crossing in deleteAdjacent is a crossing in contractZeroOne p'
  have hcross_contracted : ∃ a b : Fin (2*n),
      a.val < b.val ∧ b.val < ((p.deleteAdjacent i h).val a).val ∧
      ((p.deleteAdjacent i h).val a).val < ((p.deleteAdjacent i h).val b).val := hcross
  -- The underlying perm of deleteAdjacent IS contractZeroOne p'
  have hperm_eq : (p.deleteAdjacent i h).val = SemicircleCore.contractZeroOne p' h₀' h₁' := rfl
  rw [hperm_eq] at hcross_contracted
  have hcross_p' := contraction_crossing_lifts p' h₀' h₁' hcross_contracted
  -- Step 2: lift crossing from p' = ρpρ⁻¹ to p
  have hinv : ∀ x, p.val (p.val x) = x := by
    intro x; have hh : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
    change (p.val * p.val) x = x; simp [hh]
  -- When i.val = 0, ρ = (finRotate (2*(n+1)))^(2*(n+1)) = 1 so p' = p.val directly.
  -- When i.val > 0, 2*(n+1) - i.val < 2*(n+1) and we use HasCrossing_of_conj.
  rcases Nat.eq_zero_or_pos i.val with hi0 | hi_pos
  · have hρ_one : ρ = 1 := by
      change (finRotate (2*(n+1))) ^ (2*(n+1) - i.val) = 1
      rw [show 2*(n+1) - i.val = 2*(n+1) from by omega]
      exact finRotate_pow_self' (by omega)
    have hp'_eq : p' = p.val := by
      change ρ * p.val * ρ⁻¹ = p.val
      rw [hρ_one]; group
    rwa [hp'_eq] at hcross_p'
  · have hk : 2*(n+1) - i.val < 2*(n+1) := by omega
    exact HasCrossing_of_conj (by omega) p.val hinv (2*(n+1) - i.val) hk hcross_p'

/-! ### Forward crossing projection lemmas -/

/-- An adjacent pair cannot participate in any crossing.
    If p(i) = finRotate(i), then for any crossing a < b < p(a) < p(b),
    none of a, b equals i or finRotate(i). -/
private lemma crossing_avoids_adjacent {n : ℕ} (p : Pairing (n + 1))
    (i : Fin (2 * (n + 1))) (hadj : p.hasAdjacentAt i)
    {a b : Fin (2 * (n + 1))}
    (hab : a.val < b.val) (hbpa : b.val < (p.val a).val)
    (hpapb : (p.val a).val < (p.val b).val) :
    a ≠ i ∧ a ≠ finRotate _ i ∧ b ≠ i ∧ b ≠ finRotate _ i := by
  have hfr := finRotate_val' (show 0 < 2*(n+1) by omega) i
  -- hadj : p.val i = finRotate (2*(n+1)) i
  have hinv : ∀ y, p.val (p.val y) = y := by
    intro y; have hh : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
    change (p.val * p.val) y = y; simp [hh]
  -- p(finRotate i) = i since p is involution and p(i) = finRotate(i)
  have hadj_back : p.val (finRotate _ i) = i := by
    have := congr_arg p.val hadj; rw [hinv] at this; exact this.symm
  constructor
  · -- a ≠ i: if a = i then p(a) = finRotate(i), need b between a and p(a)
    intro ha; subst ha
    rw [hadj] at hbpa
    split_ifs at hfr with hmax
    · -- i.val = 2*(n+1) - 1, finRotate(i).val = 0
      omega
    · -- finRotate(i).val = i.val + 1, need i.val < b.val < i.val + 1
      omega
  constructor
  · -- a ≠ finRotate(i): if a = finRotate(i) then p(a) = i
    intro ha; subst ha
    rw [hadj_back] at hbpa
    -- b.val < i.val, and a.val = (finRotate i).val < b.val
    split_ifs at hfr with hmax
    · -- finRotate(i).val = 0, so a.val = 0, b.val < i.val, p(a).val = i.val
      -- Also need p(a).val < p(b).val, i.e., i.val < p(b).val
      -- and b.val < 2*(n+1), p(b).val < 2*(n+1)
      -- a.val = 0 < b.val < i.val = 2*(n+1)-1
      -- p(a).val = i.val = 2*(n+1)-1 < p(b).val < 2*(n+1)
      -- So p(b).val must be strictly between 2*(n+1)-1 and 2*(n+1), impossible
      have hpb_lt := (p.val b).isLt
      omega
    · -- finRotate(i).val = i.val + 1, a.val = i.val + 1
      -- p(a) = i, so p(a).val = i.val
      -- Need a.val < b.val, i.e., i.val + 1 < b.val
      -- Need b.val < p(a).val = i.val
      -- But i.val + 1 < b.val and b.val < i.val is impossible
      omega
  constructor
  · -- b ≠ i: if b = i then p(b) = finRotate(i)
    intro hb; subst hb
    rw [hadj] at hpapb
    split_ifs at hfr with hmax
    · -- finRotate(i).val = 0, need p(a).val < 0, impossible
      have hpa_pos := (p.val a).val.zero_le; omega
    · -- finRotate(i).val = i.val + 1
      -- Need a.val < i.val < p(a).val < i.val + 1, impossible
      omega
  · -- b ≠ finRotate(i): if b = finRotate(i) then p(b) = i
    intro hb; subst hb
    rw [hadj_back] at hpapb
    split_ifs at hfr with hmax
    · -- b.val = finRotate(i).val = 0, but a.val < b.val = 0, impossible
      omega
    · -- b.val = i.val + 1, p(b).val = i.val
      -- Need p(a).val < i.val, but also a.val < i.val + 1 and i.val + 1 < p(a).val
      -- i.e., i.val + 1 < p(a).val, but p(a).val < i.val, contradiction
      omega

/-- Crossing in p with all four vertex-values ≥ 2 contracts forward to
    a crossing in contractZeroOne. -/
private lemma contraction_crossing_forward {n : ℕ} (p : Equiv.Perm (Fin (2 * (n + 1))))
    (h₀ : p ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (h₁ : p ⟨1, by omega⟩ = ⟨0, by omega⟩)
    {a b : Fin (2 * (n + 1))}
    (ha2 : 2 ≤ a.val) (hb2 : 2 ≤ b.val)
    (hpa2 : 2 ≤ (p a).val) (hpb2 : 2 ≤ (p b).val)
    (hab : a.val < b.val) (hbpa : b.val < (p a).val)
    (hpapb : (p a).val < (p b).val) :
    let q := SemicircleCore.contractZeroOne p h₀ h₁
    ∃ a' b' : Fin (2*n), a'.val < b'.val ∧
      b'.val < (q a').val ∧ (q a').val < (q b').val := by
  intro q
  set a' : Fin (2*n) := ⟨a.val - 2, by omega⟩
  set b' : Fin (2*n) := ⟨b.val - 2, by omega⟩
  have ha_eq : (⟨a.val - 2 + 2, by omega⟩ : Fin (2*(n+1))) = a :=
    Fin.ext (by simp; omega)
  have hb_eq : (⟨b.val - 2 + 2, by omega⟩ : Fin (2*(n+1))) = b :=
    Fin.ext (by simp; omega)
  have hqa : (q a').val = (p a).val - 2 := by
    change (q ⟨a.val - 2, _⟩).val = _
    rw [contractZeroOne_val, ha_eq]
  have hqb : (q b').val = (p b).val - 2 := by
    change (q ⟨b.val - 2, _⟩).val = _
    rw [contractZeroOne_val, hb_eq]
  exact ⟨a', b', by simp [a', b']; omega,
    by rw [hqa]; simp [b']; omega,
    by rw [hqa, hqb]; omega⟩

/-- Rotation preserves crossings (forward direction), with tracking:
    The crossing witnesses in ρpρ⁻¹ come from {ρa, ρb, ρ(pa), ρ(pb)},
    ensuring they avoid any values that the originals avoid after rotation. -/
private lemma HasCrossing_conj_forward_tracked {m : ℕ} (hm : 2 ≤ m)
    (p : Equiv.Perm (Fin m)) (hinv : ∀ x, p (p x) = x)
    (k : ℕ) (hk : k < m)
    {a b : Fin m}
    (hab : a.val < b.val) (hbpa : b.val < (p a).val) (hpapb : (p a).val < (p b).val) :
    let ρ := (finRotate m) ^ k
    let p' := ρ * p * ρ⁻¹
    ∃ a' b' : Fin m,
      a' ∈ ({ρ a, ρ b, ρ (p a), ρ (p b)} : Finset (Fin m)) ∧
      b' ∈ ({ρ a, ρ b, ρ (p a), ρ (p b)} : Finset (Fin m)) ∧
      (p' a') ∈ ({ρ a, ρ b, ρ (p a), ρ (p b)} : Finset (Fin m)) ∧
      (p' b') ∈ ({ρ a, ρ b, ρ (p a), ρ (p b)} : Finset (Fin m)) ∧
      a'.val < b'.val ∧ b'.val < (p' a').val ∧ (p' a').val < (p' b').val := by
  intro ρ p'
  have hm' : 0 < m := by omega
  have conj_rho : ∀ x : Fin m, p' (ρ x) = ρ (p x) := by
    intro x; change (ρ * p * ρ⁻¹) (ρ x) = ρ (p x); simp [mul_apply]
  have rho_val : ∀ x : Fin m, (ρ x).val = (x.val + k) % m := by
    intro x; exact congr_arg Fin.val (finRotate_pow_apply' hm' k x)
  set av := a.val; set bv := b.val; set pav := (p a).val; set pbv := (p b).val
  have ha_lt : av < m := a.isLt; have hb_lt : bv < m := b.isLt
  have hpa_lt : pav < m := (p a).isLt; have hpb_lt : pbv < m := (p b).isLt
  set ra := (av + k) % m; set rb := (bv + k) % m
  set rpa := (pav + k) % m; set rpb := (pbv + k) % m
  have hra : (ρ a).val = ra := rho_val a
  have hrb : (ρ b).val = rb := rho_val b
  have hrpa : (ρ (p a)).val = rpa := rho_val (p a)
  have hrpb : (ρ (p b)).val = rpb := rho_val (p b)
  have hconj_a : (p' (ρ a)).val = rpa := by
    change ((ρ * p * ρ⁻¹) (ρ a)).val = rpa; rw [conj_rho]; exact hrpa
  have hconj_b : (p' (ρ b)).val = rpb := by
    change ((ρ * p * ρ⁻¹) (ρ b)).val = rpb; rw [conj_rho]; exact hrpb
  have hconj_pa : (p' (ρ (p a))).val = ra := by
    change ((ρ * p * ρ⁻¹) (ρ (p a))).val = ra; rw [conj_rho, hinv]; exact hra
  have hconj_pb : (p' (ρ (p b))).val = rb := by
    change ((ρ * p * ρ⁻¹) (ρ (p b))).val = rb; rw [conj_rho, hinv]; exact hrb
  -- Membership witnesses
  have ha_mem : ρ a ∈ ({ρ a, ρ b, ρ (p a), ρ (p b)} : Finset (Fin m)) :=
    Finset.mem_insert_self _ _
  have hb_mem : ρ b ∈ ({ρ a, ρ b, ρ (p a), ρ (p b)} : Finset (Fin m)) :=
    Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
  have hpa_mem : ρ (p a) ∈ ({ρ a, ρ b, ρ (p a), ρ (p b)} : Finset (Fin m)) :=
    Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))))
  have hpb_mem : ρ (p b) ∈ ({ρ a, ρ b, ρ (p a), ρ (p b)} : Finset (Fin m)) :=
    Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))))))
  -- p' applied to each member also lands in the set
  have hp'a_mem : p' (ρ a) = ρ (p a) := conj_rho a
  have hp'b_mem : p' (ρ b) = ρ (p b) := conj_rho b
  have hp'pa_mem : p' (ρ (p a)) = ρ a := by
    change (ρ * p * ρ⁻¹) (ρ (p a)) = ρ a; simp [mul_apply, hinv]
  have hp'pb_mem : p' (ρ (p b)) = ρ b := by
    change (ρ * p * ρ⁻¹) (ρ (p b)) = ρ b; simp [mul_apply, hinv]
  -- Now 5-case analysis on wrapping, same as HasCrossing_conj_forward
  by_cases hpb_wrap : pbv + k ≥ m
  · by_cases hpa_wrap : pav + k ≥ m
    · by_cases hb_wrap : bv + k ≥ m
      · by_cases ha_wrap : av + k ≥ m
        · -- All wrap
          have hra' : ra = av + k - m := mod_wrap hm' ha_lt hk ha_wrap
          have hrb' : rb = bv + k - m := mod_wrap hm' hb_lt hk hb_wrap
          have hrpa' : rpa = pav + k - m := mod_wrap hm' hpa_lt hk hpa_wrap
          have hrpb' : rpb = pbv + k - m := mod_wrap hm' hpb_lt hk hpb_wrap
          exact ⟨ρ a, ρ b, ha_mem, hb_mem,
            by rw [hp'a_mem]; exact hpa_mem,
            by rw [hp'b_mem]; exact hpb_mem,
            by rw [hra, hrb, hra', hrb']; omega,
            by rw [hconj_a, hrb, hrpa', hrb']; omega,
            by rw [hconj_a, hconj_b, hrpa', hrpb']; omega⟩
        · -- b, pa, pb wrap; a doesn't
          push Not at ha_wrap
          have hra' : ra = av + k := mod_no_wrap hm' ha_wrap
          have hrb' : rb = bv + k - m := mod_wrap hm' hb_lt hk hb_wrap
          have hrpa' : rpa = pav + k - m := mod_wrap hm' hpa_lt hk hpa_wrap
          have hrpb' : rpb = pbv + k - m := mod_wrap hm' hpb_lt hk hpb_wrap
          exact ⟨ρ b, ρ (p a), hb_mem, hpa_mem,
            by rw [hp'b_mem]; exact hpb_mem,
            by rw [hp'pa_mem]; exact ha_mem,
            by rw [hrb, hrpa, hrb', hrpa']; omega,
            by rw [hconj_b, hrpa, hrpb', hrpa']; omega,
            by rw [hconj_b, hconj_pa, hrpb', hra']; omega⟩
      · -- pa, pb wrap; a, b don't
        push Not at hb_wrap
        have hra' : ra = av + k := mod_no_wrap hm' (by omega)
        have hrb' : rb = bv + k := mod_no_wrap hm' hb_wrap
        have hrpa' : rpa = pav + k - m := mod_wrap hm' hpa_lt hk hpa_wrap
        have hrpb' : rpb = pbv + k - m := mod_wrap hm' hpb_lt hk hpb_wrap
        exact ⟨ρ (p a), ρ (p b), hpa_mem, hpb_mem,
          by rw [hp'pa_mem]; exact ha_mem,
          by rw [hp'pb_mem]; exact hb_mem,
          by rw [hrpa, hrpb, hrpa', hrpb']; omega,
          by rw [hconj_pa, hrpb, hra', hrpb']; omega,
          by rw [hconj_pa, hconj_pb, hra', hrb']; omega⟩
    · -- Only pb wraps
      push Not at hpa_wrap
      have hra' : ra = av + k := mod_no_wrap hm' (by omega)
      have hrb' : rb = bv + k := mod_no_wrap hm' (by omega)
      have hrpa' : rpa = pav + k := mod_no_wrap hm' hpa_wrap
      have hrpb' : rpb = pbv + k - m := mod_wrap hm' hpb_lt hk hpb_wrap
      exact ⟨ρ (p b), ρ a, hpb_mem, ha_mem,
        by rw [hp'pb_mem]; exact hb_mem,
        by rw [hp'a_mem]; exact hpa_mem,
        by rw [hrpb, hra, hrpb', hra']; omega,
        by rw [hconj_pb, hra, hrb', hra']; omega,
        by rw [hconj_pb, hconj_a, hrb', hrpa']; omega⟩
  · -- No wrap
    push Not at hpb_wrap
    have hra' : ra = av + k := mod_no_wrap hm' (by omega)
    have hrb' : rb = bv + k := mod_no_wrap hm' (by omega)
    have hrpa' : rpa = pav + k := mod_no_wrap hm' (by omega)
    have hrpb' : rpb = pbv + k := mod_no_wrap hm' hpb_wrap
    exact ⟨ρ a, ρ b, ha_mem, hb_mem,
      by rw [hp'a_mem]; exact hpa_mem,
      by rw [hp'b_mem]; exact hpb_mem,
      by rw [hra, hrb, hra', hrb']; omega,
      by rw [hconj_a, hrb, hrpa', hrb']; omega,
      by rw [hconj_a, hconj_b, hrpa', hrpb']; omega⟩

/-- Forward direction: crossing in p implies crossing in deleteAdjacent.
    Composes: (1) crossing avoids adjacent pair, (2) rotation forward
    with tracking, (3) contraction forward. -/
private lemma deleteAdjacent_crossing_projects {n : ℕ} (p : Pairing (n + 1))
    (i : Fin (2 * (n + 1))) (h : p.hasAdjacentAt i) :
    p.HasCrossing → (p.deleteAdjacent i h).HasCrossing := by
  intro ⟨a, b, hab, hbpa, hpapb⟩
  -- Step 0: The crossing avoids the adjacent pair {i, finRotate i}
  have ⟨ha_ne_i, ha_ne_fr, hb_ne_i, hb_ne_fr⟩ :=
    crossing_avoids_adjacent p i h hab hbpa hpapb
  -- Step 1: Set up rotation
  let ρ : Equiv.Perm (Fin (2*(n+1))) :=
    (finRotate (2*(n+1))) ^ (2*(n+1) - i.val)
  let p' : Equiv.Perm (Fin (2*(n+1))) := ρ * p.val * ρ⁻¹
  have hinv : ∀ x, p.val (p.val x) = x := by
    intro y; have hh : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
    change (p.val * p.val) y = y; simp [hh]
  -- The rotation sends i↦0, finRotate(i)↦1
  have hρi : ρ i = ⟨0, by omega⟩ :=
    rotate_self_eq_zero (2*(n+1)) (by omega) i
  have hρfr : ρ (finRotate _ i) = ⟨1, by omega⟩ :=
    rotate_succ_eq_one (2*(n+1)) i (by omega)
  -- p'(0) = 1 and p'(1) = 0
  have h₀' : p' ⟨0, by omega⟩ = ⟨1, by omega⟩ :=
    conjugate_sends hρi hρfr h
  have h₁' : p' ⟨1, by omega⟩ = ⟨0, by omega⟩ :=
    conjugate_sends_back hρi hρfr p.property.1 h
  -- Step 2: The four rotated values are all ≥ 2 (since they avoid 0 and 1)
  -- Key: ρ is injective. ρ(i) = 0, ρ(finRotate i) = 1.
  -- So ρ(x) = 0 → x = i, and ρ(x) = 1 → x = finRotate(i).
  have ρ_inj := (ρ : Equiv.Perm (Fin (2*(n+1)))).injective
  have avoid_0 : ∀ x : Fin (2*(n+1)), x ≠ i → (ρ x).val ≠ 0 := by
    intro x hne h0
    have : ρ x = ⟨0, by omega⟩ := Fin.ext h0
    rw [← hρi] at this; exact hne (ρ_inj this)
  have avoid_1 : ∀ x : Fin (2*(n+1)), x ≠ finRotate _ i → (ρ x).val ≠ 1 := by
    intro x hne h1
    have : ρ x = ⟨1, by omega⟩ := Fin.ext h1
    rw [← hρfr] at this; exact hne (ρ_inj this)
  have ge2_of_ne : ∀ x : Fin (2*(n+1)), x ≠ i → x ≠ finRotate _ i → 2 ≤ (ρ x).val := by
    intro x hni hnfr; have h0 := avoid_0 x hni; have h1 := avoid_1 x hnfr; omega
  have hρa_ge2 : 2 ≤ (ρ a).val := ge2_of_ne a ha_ne_i ha_ne_fr
  have hρb_ge2 : 2 ≤ (ρ b).val := ge2_of_ne b hb_ne_i hb_ne_fr
  -- For p(a) and p(b): they also avoid i and finRotate(i) because p is a bijection
  -- p(a) ≠ i because a ≠ finRotate(i) (and p(finRotate i) = i)
  -- p(a) ≠ finRotate(i) because a ≠ i (and p(i) = finRotate(i))
  have hadj' : p.val i = finRotate _ i := h
  have hadj_back : p.val (finRotate _ i) = i := by
    have := congr_arg p.val hadj'; rw [hinv] at this; exact this.symm
  have hpa_ne_i : p.val a ≠ i := by
    intro h_eq; have := congr_arg p.val h_eq; rw [hinv, hadj'] at this; exact ha_ne_fr this
  have hpa_ne_fr : p.val a ≠ finRotate _ i := by
    intro h_eq; have := congr_arg p.val h_eq; rw [hinv, hadj_back] at this; exact ha_ne_i this
  have hpb_ne_i : p.val b ≠ i := by
    intro h_eq; have := congr_arg p.val h_eq; rw [hinv, hadj'] at this; exact hb_ne_fr this
  have hpb_ne_fr : p.val b ≠ finRotate _ i := by
    intro h_eq; have := congr_arg p.val h_eq; rw [hinv, hadj_back] at this; exact hb_ne_i this
  have hρpa_ge2 : 2 ≤ (ρ (p.val a)).val := ge2_of_ne _ hpa_ne_i hpa_ne_fr
  have hρpb_ge2 : 2 ≤ (ρ (p.val b)).val := ge2_of_ne _ hpb_ne_i hpb_ne_fr
  -- Step 3: Use tracked rotation to get a crossing in p' with all values ≥ 2
  -- deleteAdjacent unfolds to contractZeroOne p'
  have hperm_eq : (p.deleteAdjacent i h).val = SemicircleCore.contractZeroOne p' h₀' h₁' := rfl
  rcases Nat.eq_zero_or_pos i.val with hi0 | hi_pos
  · -- i.val = 0: ρ = finRotate^(2(n+1)) = 1, so p' = p.val
    have hk_eq : 2*(n+1) - i.val = 2*(n+1) := by omega
    have hρ_one : ρ = 1 := by
      change (finRotate (2*(n+1))) ^ (2*(n+1) - i.val) = 1
      rw [hk_eq]; exact finRotate_pow_self' (by omega)
    have hρ_id : ∀ x : Fin (2*(n+1)), ρ x = x := fun x => by
      have : ρ = (1 : Equiv.Perm (Fin (2*(n+1)))) := hρ_one
      rw [this]; rfl
    have ha_ge2 : 2 ≤ a.val := by have := hρ_id a; rw [this] at hρa_ge2; exact hρa_ge2
    have hb_ge2 : 2 ≤ b.val := by have := hρ_id b; rw [this] at hρb_ge2; exact hρb_ge2
    have hpa_ge2 : 2 ≤ (p.val a).val := by
      have := hρ_id (p.val a); rw [this] at hρpa_ge2; exact hρpa_ge2
    have hpb_ge2 : 2 ≤ (p.val b).val := by
      have := hρ_id (p.val b); rw [this] at hρpb_ge2; exact hρpb_ge2
    have hp'_eq : ∀ x, p' x = p.val x := fun x => by
      change (ρ * p.val * ρ⁻¹) x = p.val x; rw [hρ_one]; simp
    rw [Pairing.HasCrossing, hperm_eq]
    have hbpa' : b.val < (p' a).val := by rw [hp'_eq]; exact hbpa
    have hpapb' : (p' a).val < (p' b).val := by rw [hp'_eq, hp'_eq]; exact hpapb
    have hp'a_ge2 : 2 ≤ (p' a).val := by rw [hp'_eq]; exact hpa_ge2
    have hp'b_ge2 : 2 ≤ (p' b).val := by rw [hp'_eq]; exact hpb_ge2
    exact contraction_crossing_forward p' h₀' h₁'
      ha_ge2 hb_ge2 hp'a_ge2 hp'b_ge2 hab hbpa' hpapb'
  · -- i.val > 0: use tracked rotation with k = 2*(n+1) - i.val < 2*(n+1)
    have hk : 2*(n+1) - i.val < 2*(n+1) := by omega
    obtain ⟨a', b', ha'_mem, hb'_mem, hp'a'_mem, hp'b'_mem, hab', hbpa', hpapb'⟩ :=
      HasCrossing_conj_forward_tracked (by omega : 2 ≤ 2*(n+1)) p.val hinv
        (2*(n+1) - i.val) hk hab hbpa hpapb
    -- All four values (a'.val, b'.val, (p' a').val, (p' b').val) are ≥ 2
    -- because they are from {ρ a, ρ b, ρ (p a), ρ (p b)}, all of which are ≥ 2
    have val_ge2 : ∀ x ∈ ({ρ a, ρ b, ρ (p.val a), ρ (p.val b)} : Finset (Fin (2*(n+1)))),
        2 ≤ x.val := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    rw [Pairing.HasCrossing, hperm_eq]
    exact contraction_crossing_forward p' h₀' h₁'
      (val_ge2 a' ha'_mem) (val_ge2 b' hb'_mem)
      (val_ge2 (p' a') hp'a'_mem) (val_ge2 (p' b') hp'b'_mem)
      hab' hbpa' hpapb'

/-! ### The Bridge Theorems -/

/-- Bridge direction 1: recursive noncrossing implies no arc crossings.
    Proof: induction on n. An adjacent pair cannot participate in any
    crossing. Any crossing among other vertices lifts to a crossing in
    the contracted pairing, contradicting the induction hypothesis. -/
theorem IsNoncrossing_imp_no_crossing {n : ℕ} (p : Pairing n)
    (h : p.IsNoncrossing) : ¬p.HasCrossing := by
  induction n with
  | zero => intro ⟨a, _, _, _, _⟩; exact Fin.elim0 a
  | succ n ih =>
    obtain ⟨i, hadj, h_nc⟩ := h
    have ih_applied := ih (p.deleteAdjacent i hadj) h_nc
    intro hcross
    exact ih_applied (deleteAdjacent_crossing_projects p i hadj hcross)

/-- Bridge direction 2: no arc crossings implies recursive noncrossing.
    Proof: find an adjacent pair (by no_crossing_has_adjacent), delete it,
    and show the contracted pairing is also crossing-free (contrapositively:
    a crossing in the contracted pairing lifts to one in the original). -/
theorem no_crossing_imp_IsNoncrossing {n : ℕ} (p : Pairing n)
    (h : ¬p.HasCrossing) : p.IsNoncrossing := by
  induction n with
  | zero => exact trivial
  | succ n ih =>
    obtain ⟨i, hadj⟩ := no_crossing_has_adjacent p h
    refine ⟨i, hadj, ih (p.deleteAdjacent i hadj) ?_⟩
    intro hcross
    exact h (deleteAdjacent_crossing_lifts p i hadj hcross)

/-! ## 4. The Parity Theorem

The shadow-closure lemma is proved from `¬ HasCrossing` using only order
logic and injectivity. The parity theorem combines this closure with the
even-cardinality lemma for fixed-point-free involutions. -/

/-- Shadow closure: if p has no crossings, the shadow of
    the chord (0, p(0)) is closed under p.
    Proof: p(x) > 0 by involution, p(x) < p(0) by contradiction
    (otherwise 0 < x < p(0) < p(x) is a crossing). -/
lemma shadow_closed_of_no_crossing {n : ℕ} (p : Pairing n)
    (h_nc : ¬p.HasCrossing) (x : Fin (2 * n))
    (hx_pos : 0 < x.val) (hx_shadow : x.val < (p.val ⟨0, by omega⟩).val) :
    0 < (p.val x).val ∧ (p.val x).val < (p.val ⟨0, by omega⟩).val := by
  have hinv : ∀ y, p.val (p.val y) = y := by
    intro y; have h : p.val * p.val = 1 := p.property.1
    change (p.val * p.val) y = y; simp [h]
  -- Anchor the zero-point: one proof term, used everywhere
  have hn : 0 < 2 * n := by omega
  -- Re-anchor hx_shadow to use hn (same Fin element, shared proof)
  have hx_sh : x.val < (p.val ⟨0, hn⟩).val := hx_shadow
  constructor
  · -- p(x) ≠ 0: if p(x) = 0 then p(0) = x by involution, but x < p(0).
    by_contra h0
    have hpx_val : (p.val x).val = 0 := by omega
    have hpx : p.val x = ⟨0, hn⟩ := Fin.ext hpx_val
    have h1 := hinv x; rw [hpx] at h1
    exact absurd (congr_arg Fin.val h1) (by omega)
  · -- p(x) < p(0): otherwise crossing or x = 0.
    by_contra hge; push Not at hge
    by_cases h_eq : (p.val x).val = (p.val ⟨0, hn⟩).val
    · -- p(x) = p(0), so x = 0 by injectivity. But x > 0.
      have := congr_arg Fin.val (p.val.injective (Fin.ext h_eq)); simp at this; omega
    · -- p(x) > p(0): crossing 0 < x < p(0) < p(x).
      have h_cross : (p.val ⟨0, hn⟩).val < (p.val x).val := by omega
      exact absurd ⟨⟨0, hn⟩, x, hx_pos, hx_sh, h_cross⟩ h_nc

/-- Shadow closure from the recursive noncrossing definition, via the bridge. -/
lemma noncrossing_mapsTo_shadow {n : ℕ} {p : Pairing n}
    (h_nc : p.IsNoncrossing) (x : Fin (2 * n))
    (hx_low : 0 < x.val) (hx_high : x.val < (p.val ⟨0, by omega⟩).val) :
    0 < (p.val x).val ∧ (p.val x).val < (p.val ⟨0, by omega⟩).val :=
  shadow_closed_of_no_crossing p (IsNoncrossing_imp_no_crossing p h_nc) x hx_low hx_high

/-- Vertex 0 always pairs with an odd vertex in a noncrossing pairing.

    Proof by contradiction: if p(0) is even = 2k, define the shadow
    S = {i : Fin(2(n+1)) | 0 < i < 2k}. Its cardinality is 2k - 1 (odd).
    Shadow closure shows S is closed under p. Since p is a fixed-point-free
    involution, S must have even cardinality. Parity contradiction. -/
theorem noncrossing_zero_target_odd {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) :
    Odd (p.val ⟨0, by omega⟩).val := by
  -- Anchor zero and extract target
  have hn : 0 < 2 * (n + 1) := by omega
  set t := (p.val ⟨0, hn⟩).val with ht_def
  -- p(0) ≠ 0 (fixed-point-free)
  have ht_pos : 0 < t := by
    by_contra h; push Not at h
    have : (p.val ⟨0, hn⟩).val = 0 := by omega
    exact p.property.2 ⟨0, hn⟩ (Fin.ext this)
  -- Assume even for contradiction
  by_contra h_not_odd
  rw [Nat.not_odd_iff_even] at h_not_odd
  obtain ⟨k, hk⟩ := h_not_odd
  -- t = 2k with k ≥ 1
  have hk_pos : 0 < k := by omega
  -- Define the shadow: {i : Fin (2*(n+1)) | 0 < i.val ∧ i.val < t}
  let shadow : Finset (Fin (2 * (n + 1))) :=
    Finset.univ.filter (fun i => 0 < i.val ∧ i.val < t)
  -- Shadow cardinality = t - 1 = 2k - 1 (odd)
  -- Count `{1, ..., t-1}` in `Fin (2*(n+1))` by an explicit embedding.
  have ht_bound : t < 2 * (n + 1) := (p.val ⟨0, hn⟩).isLt
  have h_card : shadow.card = t - 1 := by
    -- Forge the embedding: Fin(t-1) ↪ Fin(2(n+1)) via j ↦ j+1
    let f : Fin (t - 1) ↪ Fin (2 * (n + 1)) :=
      ⟨fun j => ⟨j.val + 1, by omega⟩,
       fun a b hab => Fin.ext (by
        have := congr_arg Fin.val hab; simp at this; omega)⟩
    -- The mapped universe equals the shadow
    have h_map : Finset.univ.map f = shadow := by
      ext x
      simp only [shadow, Finset.mem_map, Finset.mem_univ, true_and,
        Finset.mem_filter]
      constructor
      · rintro ⟨j, rfl⟩
        constructor
        · simp [f]
        · simp [f]; omega
      · intro ⟨h_pos, h_lt⟩
        exact ⟨⟨x.val - 1, by omega⟩, Fin.ext (by simp [f]; omega)⟩
    rw [← h_map, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  -- t - 1 = 2k - 1 is odd
  have h_odd : Odd shadow.card := by rw [h_card, hk]; exact ⟨k - 1, by omega⟩
  -- Shadow is closed under `p`.
  have h_closed : ∀ i ∈ shadow, p.val i ∈ shadow := by
    intro i hi
    simp only [shadow, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact noncrossing_mapsTo_shadow h_nc i hi.1 hi.2
  -- A fixed-point-free involution makes every closed finite set even.
  have hinv : ∀ y, p.val (p.val y) = y := by
    intro y; have h : p.val * p.val = 1 := p.property.1
    change (p.val * p.val) y = y; simp [h]
  exact absurd (even_card_of_fpf_closed hinv p.property.2 shadow h_closed)
    (Nat.not_even_iff_odd.mpr h_odd)

/-! ## 4. The Catalan Equivalence

The full bijection NoncrossingPairing(n+1) ≃ Σ k, NCP(k) × NCP(n-k)
that yields the Catalan recurrence when we take cardinalities. -/

/-- Noncrossing pairings: the subtype of pairings that are noncrossing. -/
def NoncrossingPairing (n : ℕ) :=
  { p : Pairing n // p.IsNoncrossing }

/-! ### Helper: extracting k from p(0) = 2k+1 -/

/-- For a noncrossing pairing p on 2(n+1) points, p(0) = 2k+1 for some k < n+1.
    Returns k as a Fin (n+1). -/
noncomputable def extractK {n : ℕ} (p : Pairing (n + 1)) (h_nc : p.IsNoncrossing) :
    Fin (n + 1) :=
  let t := (p.val ⟨0, by omega⟩).val
  have hodd := noncrossing_zero_target_odd p h_nc
  have ht_lt := (p.val ⟨0, by omega⟩).isLt
  ⟨t / 2, by omega⟩

/-- The target of 0 equals 2 * extractK + 1. -/
lemma extractK_spec {n : ℕ} (p : Pairing (n + 1)) (h_nc : p.IsNoncrossing) :
    (p.val ⟨0, by omega⟩).val = 2 * (extractK p h_nc).val + 1 := by
  unfold extractK
  simp only
  have hodd := noncrossing_zero_target_odd p h_nc
  obtain ⟨m, hm⟩ := hodd
  rw [hm]; omega

/-- extractK gives a value ≤ n (so k ≤ n). -/
lemma extractK_le {n : ℕ} (p : Pairing (n + 1)) (h_nc : p.IsNoncrossing) :
    (extractK p h_nc).val ≤ n := by
  have := (extractK p h_nc).isLt; omega

/-! ### Helper: shadow closure for outside complement -/

/-- The outside complement {i | 2k+1 < i} is closed under p when
    p is noncrossing and p(0) = 2k+1.

    Proof: p(x) cannot be 0 (involution would force p(0)=x, but p(0)<x).
    p(x) cannot equal p(0) (injectivity, x≠0). p(x) cannot be in the
    shadow (shadow closure would force x into the shadow). So p(x) > 2k+1. -/
lemma outside_closed_of_noncrossing {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) (x : Fin (2 * (n + 1)))
    (hx : 2 * (extractK p h_nc).val + 1 < x.val) :
    2 * (extractK p h_nc).val + 1 < (p.val x).val := by
  have hspec := extractK_spec p h_nc
  have hinv : ∀ y, p.val (p.val y) = y := by
    intro y; have h : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
    change (p.val * p.val) y = y; simp [h]
  -- hx in terms of p(0)
  have hx_p0 : (p.val ⟨0, by omega⟩).val < x.val := by rw [hspec]; exact hx
  -- p(x) ≠ 0: otherwise p(0)=x by involution, but p(0) < x
  have hpx_ne_0 : (p.val x).val ≠ 0 := by
    intro h0
    have := hinv x; rw [show p.val x = ⟨0, by omega⟩ from Fin.ext h0] at this
    exact absurd (congr_arg Fin.val this) (by omega)
  -- p(x) ≠ p(0): injectivity + x≠0
  have hpx_ne_p0 : (p.val x).val ≠ (p.val ⟨0, by omega⟩).val := by
    intro ht_eq
    have heq : p.val x = p.val ⟨0, by omega⟩ := Fin.ext ht_eq
    have heq2 := p.val.injective heq
    have : x.val = 0 := by simp [heq2]
    omega
  -- p(x) not in shadow: if 0 < p(x) < p(0), shadow closure gives 0 < x < p(0), contradiction
  have hpx_not_shadow :
      ¬(0 < (p.val x).val ∧ (p.val x).val < (p.val ⟨0, by omega⟩).val) := by
    intro ⟨h1, h2⟩
    have := noncrossing_mapsTo_shadow h_nc (p.val x) h1 h2
    rw [hinv] at this
    omega
  -- So p(x).val > p(0).val = 2k+1
  have : (p.val x).val > (p.val ⟨0, by omega⟩).val := by omega
  rw [hspec] at this; exact this

/-! ### Helper: the inside pairing

    Given a noncrossing pairing p on 2(n+1) with p(0) = 2k+1, the shadow
    {1,...,2k} is closed under p. Restricting p to this interval and
    translating via insideEquiv gives a noncrossing pairing on 2k points.

    The construction requires:
    1. Building the restricted permutation (shadow closure + involution → bijection)
    2. Proving it's a pairing (inherited involution + fpf)
    3. Proving it's noncrossing (no crossing lifts to crossing of p) -/

/-- Helper: the shadow of vertex 0 is closed under p (both bounds).
    Combines noncrossing_mapsTo_shadow into a form suitable for restriction. -/
private lemma inside_closed {n : ℕ} (p : Pairing (n + 1)) (h_nc : p.IsNoncrossing)
    (j : Fin (2 * (extractK p h_nc).val)) :
    let i_val := j.val + 1
    0 < (p.val ⟨i_val, by have := j.isLt; have := (extractK_le p h_nc); omega⟩).val ∧
    (p.val ⟨i_val, by have := j.isLt; have := (extractK_le p h_nc); omega⟩).val <
      2 * (extractK p h_nc).val + 1 := by
  have hspec := extractK_spec p h_nc
  have hk_le := extractK_le p h_nc
  have hj_lt := j.isLt
  have h_pos : 0 < j.val + 1 := by omega
  have h_lt : j.val + 1 < (p.val ⟨0, by omega⟩).val := by rw [hspec]; omega
  have := noncrossing_mapsTo_shadow h_nc ⟨j.val + 1, by omega⟩ h_pos h_lt
  rw [hspec] at this; exact this

/-- The restricted permutation on the inside interval Fin(2k).
    Maps j to p(j+1) - 1. The involution of p provides the inverse. -/
noncomputable def restrictInsidePerm {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) : Perm (Fin (2 * (extractK p h_nc).val)) where
  toFun j :=
    let bounds := inside_closed p h_nc j
    ⟨(p.val ⟨j.val + 1, by have := j.isLt; have := extractK_le p h_nc; omega⟩).val - 1,
     by have := bounds.1; have := bounds.2; omega⟩
  invFun j :=
    let bounds := inside_closed p h_nc j
    ⟨(p.val ⟨j.val + 1, by have := j.isLt; have := extractK_le p h_nc; omega⟩).val - 1,
     by have := bounds.1; have := bounds.2; omega⟩
  left_inv j := by
    have hinv : ∀ y, p.val (p.val y) = y := by
      intro y; have h : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
      change (p.val * p.val) y = y; simp [h]
    have bounds := inside_closed p h_nc j
    have hk := extractK_le p h_nc
    have hpj_pos := bounds.1
    -- Core: for any bound proof h, p(⟨p(j+1).val - 1 + 1, h⟩).val = j.val + 1
    -- because ⟨p(j+1).val - 1 + 1, h⟩ = p(j+1) (since p(j+1).val > 0)
    -- and then p(p(j+1)) = j+1 by involution
    have key : ∀ (h1 : (p.val ⟨j.val + 1, by omega⟩).val - 1 + 1 < 2 * (n + 1)),
        (p.val ⟨(p.val ⟨j.val + 1, by omega⟩).val - 1 + 1, h1⟩).val = j.val + 1 := by
      intro h1
      have heq : (⟨(p.val ⟨j.val + 1, by omega⟩).val - 1 + 1, h1⟩ : Fin (2 * (n + 1))) =
          p.val ⟨j.val + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [heq]; exact congr_arg Fin.val (hinv ⟨j.val + 1, by omega⟩)
    ext; simp only []
    have h1 : (p.val ⟨j.val + 1, by omega⟩).val - 1 + 1 < 2 * (n + 1) := by
      have := (p.val ⟨j.val + 1, by omega⟩).isLt; omega
    have := key h1; omega
  right_inv j := by
    have hinv : ∀ y, p.val (p.val y) = y := by
      intro y; have h : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
      change (p.val * p.val) y = y; simp [h]
    have bounds := inside_closed p h_nc j
    have hk := extractK_le p h_nc
    have hpj_pos := bounds.1
    have key : ∀ (h1 : (p.val ⟨j.val + 1, by omega⟩).val - 1 + 1 < 2 * (n + 1)),
        (p.val ⟨(p.val ⟨j.val + 1, by omega⟩).val - 1 + 1, h1⟩).val = j.val + 1 := by
      intro h1
      have heq : (⟨(p.val ⟨j.val + 1, by omega⟩).val - 1 + 1, h1⟩ : Fin (2 * (n + 1))) =
          p.val ⟨j.val + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [heq]; exact congr_arg Fin.val (hinv ⟨j.val + 1, by omega⟩)
    ext; simp only []
    have h1 : (p.val ⟨j.val + 1, by omega⟩).val - 1 + 1 < 2 * (n + 1) := by
      have := (p.val ⟨j.val + 1, by omega⟩).isLt; omega
    have := key h1; omega

/-- The restricted inside permutation is a pairing.
    Involution: follows from p being an involution (π is self-inverse by construction).
    FPF: π(j) = j would mean p(j+1) = j+1, contradicting p being fpf. -/
private lemma restrictInsidePerm_isPairing {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) : IsPairing (restrictInsidePerm p h_nc) := by
  constructor
  · -- Involution: π² = 1. The map is self-inverse since p is an involution.
    have : ∀ j, (restrictInsidePerm p h_nc) ((restrictInsidePerm p h_nc) j) = j :=
      fun j => (restrictInsidePerm p h_nc).left_inv j
    ext j; rw [sq, Perm.mul_apply, this, Perm.one_apply]
  · -- No fixed points: π(j) = j implies p(j+1) = j+1, contradicting fpf.
    intro j hj
    have hk := extractK_le p h_nc
    have bounds := inside_closed p h_nc j
    -- hj : restrictInsidePerm p h_nc j = j
    -- Extracting val: (p.val ⟨j+1, _⟩).val - 1 = j.val
    -- Combined with 0 < (p.val ⟨j+1, _⟩).val, gives p(j+1) = j+1
    -- Both restrictInsidePerm and inside_closed use the same proof for ⟨j+1, _⟩
    -- (namely: by have := j.isLt; have := extractK_le p h_nc; omega)
    -- so bounds.1 and hj refer to the same p.val application
    -- Unfold restrictInsidePerm to get p(j+1).val - 1 = j.val
    have h_unfold : (restrictInsidePerm p h_nc j).val =
        (p.val ⟨j.val + 1, by have := j.isLt; have := hk; omega⟩).val - 1 := rfl
    have h2 : (p.val ⟨j.val + 1, by have := j.isLt; have := hk; omega⟩).val - 1 = j.val := by
      rw [← h_unfold]; exact congr_arg Fin.val hj
    have h1 := bounds.1
    -- Now both h1 and h2 refer to the SAME p.val application
    have hpval : (p.val ⟨j.val + 1, by have := j.isLt; have := hk; omega⟩).val = j.val + 1 := by
      omega
    exact p.property.2 ⟨j.val + 1, by omega⟩
      (Fin.ext (by rw [show (⟨j.val + 1, by omega⟩ : Fin (2 * (n + 1))) =
          ⟨j.val + 1, by have := j.isLt; have := hk; omega⟩ from Fin.ext rfl]; exact hpval))

/-- The restricted inside pairing is noncrossing.
    A crossing in the restriction translates to a crossing of p
    (shifting indices by +1), contradicting noncrossing. -/
private lemma restrictInsidePerm_isNoncrossing {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) :
    let q : Pairing _ := ⟨restrictInsidePerm p h_nc, restrictInsidePerm_isPairing p h_nc⟩
    q.IsNoncrossing := by
  intro q
  apply no_crossing_imp_IsNoncrossing
  intro ⟨a, b, hab, hbpa, hpapb⟩
  have h_nc_p := IsNoncrossing_imp_no_crossing p h_nc
  have bounds_a := inside_closed p h_nc a
  have bounds_b := inside_closed p h_nc b
  -- hbpa and hpapb involve q.val which is restrictInsidePerm
  -- q.val a gives p(a+1) - 1 and q.val b gives p(b+1) - 1
  -- From a < b < q(a) < q(b) we get a+1 < b+1 < p(a+1) < p(b+1): a crossing of p
  apply h_nc_p
  -- Translate: a < b < q(a) < q(b) in Fin(2k) to a+1 < b+1 < p(a+1) < p(b+1) in Fin(2(n+1))
  have hk := extractK_le p h_nc
  -- Use the same proof terms as `inside_closed` and `restrictInsidePerm`.
  have ha_lt : a.val + 1 < 2 * (n + 1) := by have := a.isLt; omega
  have hb_lt : b.val + 1 < 2 * (n + 1) := by have := b.isLt; omega
  -- Unfold `q.val = restrictInsidePerm` to get value equations.
  -- `inside_closed` provides the same bound after unfolding the restricted map.
  have hqa_unfold : (q.val a).val =
      (p.val ⟨a.val + 1, by have := a.isLt; have := hk; omega⟩).val - 1 := rfl
  have hqb_unfold : (q.val b).val =
      (p.val ⟨b.val + 1, by have := b.isLt; have := hk; omega⟩).val - 1 := rfl
  -- bounds give positivity
  have hpa_pos := bounds_a.1  -- 0 < (p.val ⟨a+1, same_proof⟩).val
  have hpb_pos := bounds_b.1  -- 0 < (p.val ⟨b+1, same_proof⟩).val
  -- Now build the crossing
  have hab' : a.val + 1 < b.val + 1 := by omega
  refine ⟨⟨a.val + 1, ha_lt⟩, ⟨b.val + 1, hb_lt⟩, hab', ?_, ?_⟩
  · -- b+1 < p(a+1)
    change b.val + 1 < (p.val ⟨a.val + 1, ha_lt⟩).val
    have : (p.val ⟨a.val + 1, ha_lt⟩).val =
        (p.val ⟨a.val + 1, by have := a.isLt; have := hk; omega⟩).val :=
      congr_arg Fin.val (congrArg p.val (Fin.ext rfl))
    omega
  · -- p(a+1) < p(b+1)
    show (p.val ⟨a.val + 1, ha_lt⟩).val < (p.val ⟨b.val + 1, hb_lt⟩).val
    have ha_eq : (p.val ⟨a.val + 1, ha_lt⟩).val =
        (p.val ⟨a.val + 1, by have := a.isLt; have := hk; omega⟩).val :=
      congr_arg Fin.val (congrArg p.val (Fin.ext rfl))
    have hb_eq : (p.val ⟨b.val + 1, hb_lt⟩).val =
        (p.val ⟨b.val + 1, by have := b.isLt; have := hk; omega⟩).val :=
      congr_arg Fin.val (congrArg p.val (Fin.ext rfl))
    omega

/-- The inside noncrossing pairing extracted from a noncrossing pairing p
    on 2(n+1) points with p(0) = 2k+1. -/
noncomputable def insidePairing {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) : NoncrossingPairing (extractK p h_nc).val :=
  ⟨⟨restrictInsidePerm p h_nc, restrictInsidePerm_isPairing p h_nc⟩,
   restrictInsidePerm_isNoncrossing p h_nc⟩

/-- Helper: outside interval is closed under p (both bounds). -/
private lemma outside_closed {n : ℕ} (p : Pairing (n + 1)) (h_nc : p.IsNoncrossing)
    (j : Fin (2 * (n - (extractK p h_nc).val))) :
    let i_val := j.val + 2 * (extractK p h_nc).val + 2
    2 * (extractK p h_nc).val + 1 <
      (p.val ⟨i_val, by have := j.isLt; have := extractK_le p h_nc; omega⟩).val := by
  have hk_le := extractK_le p h_nc
  have hj_lt := j.isLt
  have h_gt : 2 * (extractK p h_nc).val + 1 < j.val + 2 * (extractK p h_nc).val + 2 := by omega
  exact outside_closed_of_noncrossing p h_nc
    ⟨j.val + 2 * (extractK p h_nc).val + 2, by omega⟩ h_gt

/-- The restricted permutation on the outside interval Fin(2(n-k)).
    Maps j to p(j + 2k + 2) - (2k + 2). -/
noncomputable def restrictOutsidePerm {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) : Perm (Fin (2 * (n - (extractK p h_nc).val))) where
  toFun j :=
    let bound := outside_closed p h_nc j
    ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2, by
        have := j.isLt; have := extractK_le p h_nc; omega⟩).val -
      (2 * (extractK p h_nc).val + 2), by
      have hpi := (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2, by omega⟩).isLt
      have := bound; omega⟩
  invFun j :=
    let bound := outside_closed p h_nc j
    ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2, by
        have := j.isLt; have := extractK_le p h_nc; omega⟩).val -
      (2 * (extractK p h_nc).val + 2), by
      have hpi := (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2, by omega⟩).isLt
      have := bound; omega⟩
  left_inv j := by
    have hinv : ∀ y, p.val (p.val y) = y := by
      intro y; have h : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
      change (p.val * p.val) y = y; simp [h]
    have bound := outside_closed p h_nc j
    have hk := extractK_le p h_nc
    -- Same pattern as inside: use `key` with `by omega` proof (matching simp normalization)
    -- Use p_irrel to unify different Fin proof terms in p.val applications
    -- p.val ⟨x, h1⟩ = p.val ⟨x, h2⟩ for any h1 h2 (by Fin.ext rfl)
    -- After ext, omega will see multiple p.val applications with different proofs.
    -- We bridge them explicitly.
    apply Fin.ext; simp only []
    -- Let pv := (p.val ⟨j+off, def_proof⟩).val (the val of the first application)
    -- The double application gives: p(⟨pv - off + off, _⟩).val - off
    -- We need to show this = j.val.
    -- Step 1: pv > 2k+1 (from bound, after Fin unification), so pv >= off, pv - off + off = pv
    -- Step 2: ⟨pv - off + off, _⟩ = ⟨pv, _⟩ = p(j+off) as Fin
    -- Step 3: p(p(j+off)) = j+off, so result = (j+off) - off = j
    -- Do it all at once with congrArg chains
    -- First, get everything referring to the SAME Fin proof for ⟨j+off, _⟩
    -- The definition uses: by have := j.isLt; have := extractK_le p h_nc; omega
    -- outside_closed also uses:
    -- by have := j.isLt; have := extractK_le p h_nc; omega (via its proof)
    -- bound says 2k+1 < (p.val ⟨j+off, outside_closed_proof⟩).val
    -- We need 2k+1 < (p.val ⟨j+off, def_proof⟩).val to conclude pv >= off
    -- Show all p.val applications at j+off give the same val (by Fin.ext rfl)
    have h_pv := congr_arg Fin.val (congrArg p.val (show
        (⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := extractK_le p h_nc; omega⟩ : Fin (2 * (n + 1))) =
        ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := extractK_le p h_nc; omega⟩ from rfl))
    -- This is just rfl. We need a different approach.
    -- Use the INVOLUTION directly: p(p(x)) = x for any x
    -- If we can show that the double application equals j at the Fin level:
    -- For any bound proofs h_inner and h_outer, if the inner Fin has same val as p(j+off),
    -- then p applied to it gives j+off, and (j+off) - off = j.
    -- Supply the chain manually, using omega with all relevant congrArg facts pre-computed
    -- Unify the inner Fin proof: the second toFun call creates ⟨j'+off, proof'⟩
    -- where j' = toFun(j) = ⟨pv - off, _⟩, so j'+off = pv - off + off
    -- and proof' uses j'.isLt. We need (p.val ⟨pv-off+off, proof'⟩).val
    -- to relate to (p.val ⟨pv, _⟩).val = (p.val (p.val ⟨j+off, _⟩)).val
    -- = (j+off) (by involution) = j + off
    -- Use the chain: p.val ⟨pv-off+off, proof'⟩ = p.val ⟨pv, _⟩ (by Fin.ext + omega)
    -- = p.val (p.val ⟨j+off, _⟩) = ⟨j+off, _⟩ (by involution)
    -- Therefore result = (j+off) - off = j
    -- Express as a single have:
    -- Use simp with the involution to simplify the double application
    -- First, establish a rewrite lemma: for any Fin with val = p(j+off).val,
    -- p applied to it has val = j+off
    -- This requires p.val ⟨v, _⟩ = p.val ⟨v, _⟩ when v's match (Fin proof irrel)
    -- and then p(p(x)) = x
    -- Key: use `conv` to rewrite inside the goal
    -- After ext; simp, the goal is: some_nat_expr = j.val
    -- We need to identify the specific Fin terms and rewrite them.
    -- ALTERNATIVE: use Equiv.Perm properties at a higher level
    -- Since (restrictOutsidePerm p h_nc) is a Perm, and its toFun = invFun,
    -- we just need toFun (toFun j) = j
    -- But that's circular (we're proving left_inv which makes it a valid Perm)
    -- OK: prove it DIRECTLY by constructing a chain
    -- Let f be the toFun function (before it's wrapped into an Equiv)
    -- f(j) = ⟨p(j+off).val - off, _⟩
    -- f(f(j)).val = p(⟨f(j).val + off, _⟩).val - off
    --            = p(⟨p(j+off).val - off + off, _⟩).val - off
    -- Now if p(j+off).val >= off, then p(j+off).val - off + off = p(j+off).val
    -- and ⟨p(j+off).val, _⟩ = p(j+off) as Fin (by Fin.ext)
    -- so p(⟨p(j+off).val, _⟩) = p(p(j+off)) = j+off (by involution)
    -- therefore f(f(j)).val = (j+off) - off = j
    -- The challenge is that "p(j+off)" refers to p.val ⟨j+off, def_proof⟩
    -- and the intermediate calculations may produce different def_proof's.
    -- Use `change` to explicitly state what we're proving:
    -- After ext, the goal is:
    -- (p ⟨(p ⟨j+2k+2, A⟩).val - (2k+2) + 2k + 2, B⟩).val - (2k+2) = j.val
    -- where A and B are specific proof terms.
    -- Step 1: The Fin ⟨(p ⟨j+2k+2, A⟩).val - (2k+2) + 2k + 2, B⟩
    --   has val = (p ⟨j+2k+2, A⟩).val (since val > 2k+1 from bound)
    -- Step 2: So p applied to it = p(p(⟨j+2k+2, A⟩)) = ⟨j+2k+2, A⟩ (by involution)
    -- Step 3: Result = (j+2k+2) - (2k+2) = j
    -- Express using congrArg and Fin.ext:
    have h_inner_eq : ∀ (v : ℕ) (hv : v > 2 * (extractK p h_nc).val + 1)
        (h1 : v - (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2 < 2 * (n + 1))
        (h2 : v < 2 * (n + 1)),
        (⟨v - (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h1⟩ :
            Fin (2 * (n + 1))) =
        ⟨v, h2⟩ := by
      intro v hv h1 h2; ext; simp; omega
    -- Now we instantiate with v = (p.val ⟨j+off, _⟩).val
    -- But we need the specific proof terms from the goal...
    -- Instead, use a more targeted approach: show the WHOLE p.val application
    -- at the problematic Fin equals p.val at p.val ⟨j+off, _⟩
    -- Then use hinv to get the result.
    -- We need: for any proof h of (...) < 2*(n+1),
    --   p.val ⟨(p.val ⟨j+off, A⟩).val - off' + 2k + 2, h⟩ = p.val (p.val ⟨j+off, A⟩)
    -- where off' = 2k+2 and the addition is left-assoc: (val - off' + 2k) + 2
    -- This equals val when val >= off' (since val - off' + 2k + 2 = val - (2k+2) + (2k+2) = val)
    -- So the Fin has same val as p.val ⟨j+off, A⟩, hence equals it by Fin.ext
    -- Therefore p applied gives p(p(⟨j+off,A⟩)) = ⟨j+off,A⟩
    -- result.val = (j+off).val - off' = j
    -- Express as a calc:
    -- Step 1: show p.val ⟨..., B⟩ = p.val (p.val ⟨j+off, A⟩) using Fin.ext
    -- Step 2: use hinv to simplify
    -- Step 3: compute val
    -- But we don't know A and B explicitly.
    -- FINAL APPROACH: just use congrArg Fin.val + omega, making sure all
    -- Fin proof terms in the goal are unified to ones omega can see.
    -- Introduce explicit equations for ALL opaque p.val expressions:
    -- Every p.val ⟨x, h⟩ in the goal, we produce a `have` equating it to
    -- p.val ⟨x, canonical_h⟩ where canonical_h is a named proof.
    -- Then omega can use the equations.
    -- But we can't see the proofs... Let me try `simp only [Fin.ext_iff]` or `Fin.val_mk`
    -- to normalize the Fin expressions
    -- Prove involution gives the right val
    have h_inv_val := congr_arg Fin.val (hinv ⟨j.val + 2 * (extractK p h_nc).val + 2,
      by have := j.isLt; have := hk; omega⟩)
    -- h_inv_val : (p.val (p.val ⟨j+2k+2, _⟩)).val = j + 2k + 2
    -- Bridge: the inner Fin in the goal has same val as p.val ⟨j+2k+2, _⟩
    -- Therefore p applied to it gives same result as p(p(⟨j+2k+2,_⟩))
    -- Use congrArg p.val (Fin.ext ...) to establish the bridge
    have h_bridge : ∀ (h' : (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩).val -
        (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2 < 2 * (n + 1)),
      (p.val ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
            by have := j.isLt; have := hk; omega⟩).val -
          (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h'⟩).val =
      (p.val (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩)).val := by
        intro h'
        congr 1; exact congrArg p.val (Fin.ext (by simp; omega))
    -- Instantiate `h_bridge` with the explicit bound proof used below.
    have h_bound' : (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩).val -
        (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2 < 2 * (n + 1) := by
      have := (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
        by have := j.isLt; have := hk; omega⟩).isLt; omega
    have h_bridge_inst := h_bridge h_bound'
    -- h_bridge_inst equates the p.val application in my terms to (p(p(...))).val
    -- combined with h_inv_val, we get:
    -- (p.val ⟨..., h_bound'⟩).val = j + 2k + 2
    -- But the goal has (p.val ⟨..., goal_proof⟩).val, not (p.val ⟨..., h_bound'⟩).val!
    -- SAME problem!
    -- The only fix: use congrArg to match goal_proof to h_bound'
    -- Since both have the same val, Fin.ext rfl gives the Fin equality
    -- Then congrArg p.val gives p equality, then congr_arg Fin.val gives val equality
    have h_unify : ∀ (h1 h2 : (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩).val -
        (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2 < 2 * (n + 1)),
      (p.val ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
            by have := j.isLt; have := hk; omega⟩).val -
          (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h1⟩).val =
      (p.val ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
            by have := j.isLt; have := hk; omega⟩).val -
          (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h2⟩).val :=
      fun h1 h2 => congr_arg Fin.val (congrArg p.val (Fin.ext rfl))
    -- Now h_unify lets omega connect any two p.val applications at the same Nat value
    -- but with different proofs. Combined with h_bridge_inst and h_inv_val:
    -- For ANY h, (p.val ⟨..., h⟩).val = (p.val ⟨..., h_bound'⟩).val = (p(p(...))).val = j+2k+2
    -- result = j + 2k + 2 - (2k+2) = j
    -- But h_unify is still universally quantified!
    -- Let me just prove the whole thing directly:
    have goal_fact : ∀ (h : (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩).val -
        (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2 < 2 * (n + 1)),
      (p.val ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
            by have := j.isLt; have := hk; omega⟩).val -
          (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h⟩).val -
      (2 * (extractK p h_nc).val + 2) = j.val := by
        intro h
        have h_eq := h_unify h h_bound'
        have h_val : (p.val ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
              by have := j.isLt; have := hk; omega⟩).val -
            (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h⟩).val =
            j.val + 2 * (extractK p h_nc).val + 2 := by
          rw [h_eq, h_bridge_inst, h_inv_val]
        omega
    -- `goal_fact` is quantified over the bound proof introduced by `ext`.
    exact goal_fact _
  right_inv j := by
    have hinv : ∀ y, p.val (p.val y) = y := by
      intro y; have h : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
      change (p.val * p.val) y = y; simp [h]
    have bound := outside_closed p h_nc j
    have hk := extractK_le p h_nc
    -- Use p_irrel to unify different Fin proof terms in p.val applications
    -- p.val ⟨x, h1⟩ = p.val ⟨x, h2⟩ for any h1 h2 (by Fin.ext rfl)
    -- After ext, omega will see multiple p.val applications with different proofs.
    -- We bridge them explicitly.
    apply Fin.ext; simp only []
    -- Let pv := (p.val ⟨j+off, def_proof⟩).val (the val of the first application)
    -- The double application gives: p(⟨pv - off + off, _⟩).val - off
    -- We need to show this = j.val.
    -- Step 1: pv > 2k+1 (from bound, after Fin unification), so pv >= off, pv - off + off = pv
    -- Step 2: ⟨pv - off + off, _⟩ = ⟨pv, _⟩ = p(j+off) as Fin
    -- Step 3: p(p(j+off)) = j+off, so result = (j+off) - off = j
    -- Do it all at once with congrArg chains
    -- First, get everything referring to the SAME Fin proof for ⟨j+off, _⟩
    -- The definition uses: by have := j.isLt; have := extractK_le p h_nc; omega
    -- outside_closed also uses:
    -- by have := j.isLt; have := extractK_le p h_nc; omega (via its proof)
    -- bound says 2k+1 < (p.val ⟨j+off, outside_closed_proof⟩).val
    -- We need 2k+1 < (p.val ⟨j+off, def_proof⟩).val to conclude pv >= off
    -- Show all p.val applications at j+off give the same val (by Fin.ext rfl)
    have h_pv := congr_arg Fin.val (congrArg p.val (show
        (⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := extractK_le p h_nc; omega⟩ : Fin (2 * (n + 1))) =
        ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := extractK_le p h_nc; omega⟩ from rfl))
    -- This is just rfl. We need a different approach.
    -- Use the INVOLUTION directly: p(p(x)) = x for any x
    -- If we can show that the double application equals j at the Fin level:
    -- For any bound proofs h_inner and h_outer, if the inner Fin has same val as p(j+off),
    -- then p applied to it gives j+off, and (j+off) - off = j.
    -- Supply the chain manually, using omega with all relevant congrArg facts pre-computed
    -- Unify the inner Fin proof: the second toFun call creates ⟨j'+off, proof'⟩
    -- where j' = toFun(j) = ⟨pv - off, _⟩, so j'+off = pv - off + off
    -- and proof' uses j'.isLt. We need (p.val ⟨pv-off+off, proof'⟩).val
    -- to relate to (p.val ⟨pv, _⟩).val = (p.val (p.val ⟨j+off, _⟩)).val
    -- = (j+off) (by involution) = j + off
    -- Use the chain: p.val ⟨pv-off+off, proof'⟩ = p.val ⟨pv, _⟩ (by Fin.ext + omega)
    -- = p.val (p.val ⟨j+off, _⟩) = ⟨j+off, _⟩ (by involution)
    -- Therefore result = (j+off) - off = j
    -- Express as a single have:
    -- Use simp with the involution to simplify the double application
    -- First, establish a rewrite lemma: for any Fin with val = p(j+off).val,
    -- p applied to it has val = j+off
    -- This requires p.val ⟨v, _⟩ = p.val ⟨v, _⟩ when v's match (Fin proof irrel)
    -- and then p(p(x)) = x
    -- Key: use `conv` to rewrite inside the goal
    -- After ext; simp, the goal is: some_nat_expr = j.val
    -- We need to identify the specific Fin terms and rewrite them.
    -- ALTERNATIVE: use Equiv.Perm properties at a higher level
    -- Since (restrictOutsidePerm p h_nc) is a Perm, and its toFun = invFun,
    -- we just need toFun (toFun j) = j
    -- But that's circular (we're proving left_inv which makes it a valid Perm)
    -- OK: prove it DIRECTLY by constructing a chain
    -- Let f be the toFun function (before it's wrapped into an Equiv)
    -- f(j) = ⟨p(j+off).val - off, _⟩
    -- f(f(j)).val = p(⟨f(j).val + off, _⟩).val - off
    --            = p(⟨p(j+off).val - off + off, _⟩).val - off
    -- Now if p(j+off).val >= off, then p(j+off).val - off + off = p(j+off).val
    -- and ⟨p(j+off).val, _⟩ = p(j+off) as Fin (by Fin.ext)
    -- so p(⟨p(j+off).val, _⟩) = p(p(j+off)) = j+off (by involution)
    -- therefore f(f(j)).val = (j+off) - off = j
    -- The challenge is that "p(j+off)" refers to p.val ⟨j+off, def_proof⟩
    -- and the intermediate calculations may produce different def_proof's.
    -- Use `change` to explicitly state what we're proving:
    -- After ext, the goal is:
    -- (p ⟨(p ⟨j+2k+2, A⟩).val - (2k+2) + 2k + 2, B⟩).val - (2k+2) = j.val
    -- where A and B are specific proof terms.
    -- Step 1: The Fin ⟨(p ⟨j+2k+2, A⟩).val - (2k+2) + 2k + 2, B⟩
    --   has val = (p ⟨j+2k+2, A⟩).val (since val > 2k+1 from bound)
    -- Step 2: So p applied to it = p(p(⟨j+2k+2, A⟩)) = ⟨j+2k+2, A⟩ (by involution)
    -- Step 3: Result = (j+2k+2) - (2k+2) = j
    -- Express using congrArg and Fin.ext:
    have h_inner_eq : ∀ (v : ℕ) (hv : v > 2 * (extractK p h_nc).val + 1)
        (h1 : v - (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2 < 2 * (n + 1))
        (h2 : v < 2 * (n + 1)),
        (⟨v - (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h1⟩ :
            Fin (2 * (n + 1))) =
        ⟨v, h2⟩ := by
      intro v hv h1 h2; ext; simp; omega
    -- Now we instantiate with v = (p.val ⟨j+off, _⟩).val
    -- But we need the specific proof terms from the goal...
    -- Instead, use a more targeted approach: show the WHOLE p.val application
    -- at the problematic Fin equals p.val at p.val ⟨j+off, _⟩
    -- Then use hinv to get the result.
    -- We need: for any proof h of (...) < 2*(n+1),
    --   p.val ⟨(p.val ⟨j+off, A⟩).val - off' + 2k + 2, h⟩ = p.val (p.val ⟨j+off, A⟩)
    -- where off' = 2k+2 and the addition is left-assoc: (val - off' + 2k) + 2
    -- This equals val when val >= off' (since val - off' + 2k + 2 = val - (2k+2) + (2k+2) = val)
    -- So the Fin has same val as p.val ⟨j+off, A⟩, hence equals it by Fin.ext
    -- Therefore p applied gives p(p(⟨j+off,A⟩)) = ⟨j+off,A⟩
    -- result.val = (j+off).val - off' = j
    -- Express as a calc:
    -- Step 1: show p.val ⟨..., B⟩ = p.val (p.val ⟨j+off, A⟩) using Fin.ext
    -- Step 2: use hinv to simplify
    -- Step 3: compute val
    -- But we don't know A and B explicitly.
    -- FINAL APPROACH: just use congrArg Fin.val + omega, making sure all
    -- Fin proof terms in the goal are unified to ones omega can see.
    -- Introduce explicit equations for ALL opaque p.val expressions:
    -- Every p.val ⟨x, h⟩ in the goal, we produce a `have` equating it to
    -- p.val ⟨x, canonical_h⟩ where canonical_h is a named proof.
    -- Then omega can use the equations.
    -- But we can't see the proofs... Let me try `simp only [Fin.ext_iff]` or `Fin.val_mk`
    -- to normalize the Fin expressions
    -- Prove involution gives the right val
    have h_inv_val := congr_arg Fin.val (hinv ⟨j.val + 2 * (extractK p h_nc).val + 2,
      by have := j.isLt; have := hk; omega⟩)
    -- h_inv_val : (p.val (p.val ⟨j+2k+2, _⟩)).val = j + 2k + 2
    -- Bridge: the inner Fin in the goal has same val as p.val ⟨j+2k+2, _⟩
    -- Therefore p applied to it gives same result as p(p(⟨j+2k+2,_⟩))
    -- Use congrArg p.val (Fin.ext ...) to establish the bridge
    have h_bridge : ∀ (h' : (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩).val -
        (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2 < 2 * (n + 1)),
      (p.val ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
            by have := j.isLt; have := hk; omega⟩).val -
          (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h'⟩).val =
      (p.val (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩)).val := by
        intro h'
        congr 1; exact congrArg p.val (Fin.ext (by simp; omega))
    -- Instantiate `h_bridge` with the explicit bound proof used below.
    have h_bound' : (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩).val -
        (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2 < 2 * (n + 1) := by
      have := (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
        by have := j.isLt; have := hk; omega⟩).isLt; omega
    have h_bridge_inst := h_bridge h_bound'
    -- h_bridge_inst equates the p.val application in my terms to (p(p(...))).val
    -- combined with h_inv_val, we get:
    -- (p.val ⟨..., h_bound'⟩).val = j + 2k + 2
    -- But the goal has (p.val ⟨..., goal_proof⟩).val, not (p.val ⟨..., h_bound'⟩).val!
    -- SAME problem!
    -- The only fix: use congrArg to match goal_proof to h_bound'
    -- Since both have the same val, Fin.ext rfl gives the Fin equality
    -- Then congrArg p.val gives p equality, then congr_arg Fin.val gives val equality
    have h_unify : ∀ (h1 h2 : (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩).val -
        (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2 < 2 * (n + 1)),
      (p.val ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
            by have := j.isLt; have := hk; omega⟩).val -
          (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h1⟩).val =
      (p.val ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
            by have := j.isLt; have := hk; omega⟩).val -
          (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h2⟩).val :=
      fun h1 h2 => congr_arg Fin.val (congrArg p.val (Fin.ext rfl))
    -- Now h_unify lets omega connect any two p.val applications at the same Nat value
    -- but with different proofs. Combined with h_bridge_inst and h_inv_val:
    -- For ANY h, (p.val ⟨..., h⟩).val = (p.val ⟨..., h_bound'⟩).val = (p(p(...))).val = j+2k+2
    -- result = j + 2k + 2 - (2k+2) = j
    -- But h_unify is still universally quantified!
    -- Let me just prove the whole thing directly:
    have goal_fact : ∀ (h : (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩).val -
        (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2 < 2 * (n + 1)),
      (p.val ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
            by have := j.isLt; have := hk; omega⟩).val -
          (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h⟩).val -
      (2 * (extractK p h_nc).val + 2) = j.val := by
        intro h
        have h_eq := h_unify h h_bound'
        have h_val : (p.val ⟨(p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
              by have := j.isLt; have := hk; omega⟩).val -
            (2 * (extractK p h_nc).val + 2) + 2 * (extractK p h_nc).val + 2, h⟩).val =
            j.val + 2 * (extractK p h_nc).val + 2 := by
          rw [h_eq, h_bridge_inst, h_inv_val]
        omega
    -- `goal_fact` is quantified over the bound proof introduced by `ext`.
    exact goal_fact _

/-- The restricted outside permutation is a pairing. -/
private lemma restrictOutsidePerm_isPairing {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) : IsPairing (restrictOutsidePerm p h_nc) := by
  constructor
  · -- Involution: π² = 1
    have : ∀ j, (restrictOutsidePerm p h_nc) ((restrictOutsidePerm p h_nc) j) = j :=
      fun j => (restrictOutsidePerm p h_nc).left_inv j
    ext j; rw [sq, Perm.mul_apply, this, Perm.one_apply]
  · -- No fixed points: π(j) = j implies p(j+off) = j+off, contradicting fpf
    intro j hj
    have hk := extractK_le p h_nc
    have bound := outside_closed p h_nc j
    -- Unfold restrictOutsidePerm to get val equation
    have h_unfold : (restrictOutsidePerm p h_nc j).val =
        (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
          by have := j.isLt; have := hk; omega⟩).val -
        (2 * (extractK p h_nc).val + 2) := rfl
    have h2 : (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
        by have := j.isLt; have := hk; omega⟩).val -
        (2 * (extractK p h_nc).val + 2) = j.val := by
      rw [← h_unfold]; exact congr_arg Fin.val hj
    -- bound says p(j+off).val > 2k+1, so >= 2k+2
    -- h2 says p(j+off).val - (2k+2) = j.val
    -- Combined: p(j+off).val = j + 2k + 2
    have hpval : (p.val ⟨j.val + 2 * (extractK p h_nc).val + 2,
        by have := j.isLt; have := hk; omega⟩).val =
        j.val + 2 * (extractK p h_nc).val + 2 := by omega
    exact p.property.2 ⟨j.val + 2 * (extractK p h_nc).val + 2, by omega⟩
      (Fin.ext (by rw [show (⟨j.val + 2 * (extractK p h_nc).val + 2, by omega⟩ :
          Fin (2 * (n + 1))) =
          ⟨j.val + 2 * (extractK p h_nc).val + 2,
            by have := j.isLt; have := hk; omega⟩ from Fin.ext rfl]; exact hpval))

/-- The restricted outside pairing is noncrossing. -/
private lemma restrictOutsidePerm_isNoncrossing {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) :
    let q : Pairing _ := ⟨restrictOutsidePerm p h_nc, restrictOutsidePerm_isPairing p h_nc⟩
    q.IsNoncrossing := by
  intro q
  apply no_crossing_imp_IsNoncrossing
  intro ⟨a, b, hab, hbpa, hpapb⟩
  have h_nc_p := IsNoncrossing_imp_no_crossing p h_nc
  have bound_a := outside_closed p h_nc a
  have bound_b := outside_closed p h_nc b
  apply h_nc_p
  -- Translate crossing from q to p by adding offset
  have hk := extractK_le p h_nc
  let off := 2 * (extractK p h_nc).val + 2
  have ha_lt : a.val + off < 2 * (n + 1) := by have := a.isLt; omega
  have hb_lt : b.val + off < 2 * (n + 1) := by have := b.isLt; omega
  -- Unfold q.val = restrictOutsidePerm to get val equations
  have hqa_unfold : (q.val a).val =
      (p.val ⟨a.val + off, by have := a.isLt; have := hk; omega⟩).val - off := rfl
  have hqb_unfold : (q.val b).val =
      (p.val ⟨b.val + off, by have := b.isLt; have := hk; omega⟩).val - off := rfl
  -- bounds give that p(a+off).val > 2k+1, i.e., >= off
  have hpa_bound := bound_a  -- 2k+1 < p(a+off).val
  have hpb_bound := bound_b
  have hab' : a.val + off < b.val + off := by omega
  refine ⟨⟨a.val + off, ha_lt⟩, ⟨b.val + off, hb_lt⟩, hab', ?_, ?_⟩
  · -- b+off < p(a+off)
    change b.val + off < (p.val ⟨a.val + off, ha_lt⟩).val
    have : (p.val ⟨a.val + off, ha_lt⟩).val =
        (p.val ⟨a.val + off, by have := a.isLt; have := hk; omega⟩).val :=
      congr_arg Fin.val (congrArg p.val (Fin.ext rfl))
    omega
  · -- p(a+off) < p(b+off)
    show (p.val ⟨a.val + off, ha_lt⟩).val < (p.val ⟨b.val + off, hb_lt⟩).val
    have ha_eq : (p.val ⟨a.val + off, ha_lt⟩).val =
        (p.val ⟨a.val + off, by have := a.isLt; have := hk; omega⟩).val :=
      congr_arg Fin.val (congrArg p.val (Fin.ext rfl))
    have hb_eq : (p.val ⟨b.val + off, hb_lt⟩).val =
        (p.val ⟨b.val + off, by have := b.isLt; have := hk; omega⟩).val :=
      congr_arg Fin.val (congrArg p.val (Fin.ext rfl))
    omega

/-- The outside noncrossing pairing extracted from a noncrossing pairing p
    on 2(n+1) points with p(0) = 2k+1. -/
noncomputable def outsidePairing {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) :
    NoncrossingPairing (n - (extractK p h_nc).val) :=
  ⟨⟨restrictOutsidePerm p h_nc, restrictOutsidePerm_isPairing p h_nc⟩,
   restrictOutsidePerm_isNoncrossing p h_nc⟩

/-! ### Assembly: the inverse direction

Given k and noncrossing pairings on the inside and outside intervals,
assemble a noncrossing pairing on 2(n+1) points. -/

/-- The assembly function: given k, p_in on Fin(2k), p_out on Fin(2(n-k)),
    build the permutation on Fin(2(n+1)) that sends 0↔2k+1 and
    translates p_in to the inside interval and p_out to the outside. -/
noncomputable def assembleF (n : ℕ) (k : Fin (n + 1))
    (p_in : Perm (Fin (2 * k.val))) (p_out : Perm (Fin (2 * (n - k.val)))) :
    Fin (2 * (n + 1)) → Fin (2 * (n + 1)) := fun x =>
  if hx0 : x.val = 0 then
    ⟨2 * k.val + 1, by omega⟩
  else if hxt : x.val = 2 * k.val + 1 then
    ⟨0, by omega⟩
  else if hxin : x.val ≤ 2 * k.val then
    -- Inside: x is in {1,...,2k}, map via p_in
    ⟨(p_in ⟨x.val - 1, by omega⟩).val + 1, by
      have := (p_in ⟨x.val - 1, by omega⟩).isLt; omega⟩
  else
    -- Outside: x is in {2k+2,...,2n+1}, map via p_out
    ⟨(p_out ⟨x.val - (2 * k.val + 2), by
        have := x.isLt; omega⟩).val + (2 * k.val + 2), by
      have := (p_out ⟨x.val - (2 * k.val + 2), by omega⟩).isLt
      have := x.isLt; omega⟩

/-- The assembly function is involutive when p_in and p_out are involutions. -/
private lemma assembleF_involutive (n : ℕ) (k : Fin (n + 1))
    (p_in : Perm (Fin (2 * k.val))) (p_out : Perm (Fin (2 * (n - k.val))))
    (hinv_in : ∀ x, p_in (p_in x) = x) (hinv_out : ∀ x, p_out (p_out x) = x) :
    Function.Involutive (assembleF n k p_in p_out) := by
  -- Prove the involution by computing f(f(x)) for each case and using congr_arg
  have hinv_in_val : ∀ (i : Fin (2 * k.val)),
      (p_in (p_in i)).val = i.val := fun i => congr_arg Fin.val (hinv_in i)
  have hinv_out_val : ∀ (i : Fin (2 * (n - k.val))),
      (p_out (p_out i)).val = i.val := fun i => congr_arg Fin.val (hinv_out i)
  -- Evaluation lemmas for assembleF at the Fin.val level
  have eval_case0 : ∀ (y : Fin (2 * (n + 1))) (hy : y.val = 0),
      (assembleF n k p_in p_out y).val = 2 * k.val + 1 := by
    intros y hy; unfold assembleF; simp [hy]
  have eval_caseM : ∀ (y : Fin (2 * (n + 1))) (hy : y.val = 2 * k.val + 1),
      (assembleF n k p_in p_out y).val = 0 := by
    intros y hy; unfold assembleF
    simp [hy]
  have eval_caseIn : ∀ (y : Fin (2 * (n + 1)))
      (hy0 : y.val ≠ 0) (hyt : y.val ≠ 2 * k.val + 1) (hyin : y.val ≤ 2 * k.val),
      (assembleF n k p_in p_out y).val = (p_in ⟨y.val - 1, by omega⟩).val + 1 := by
    intros y hy0 hyt hyin; unfold assembleF; simp [hy0, hyt, hyin]
  have eval_caseOut : ∀ (y : Fin (2 * (n + 1)))
      (hy0 : y.val ≠ 0) (hyt : y.val ≠ 2 * k.val + 1) (hyout : ¬ y.val ≤ 2 * k.val),
      (assembleF n k p_in p_out y).val = (p_out ⟨y.val - (2 * k.val + 2), by
          have := y.isLt; omega⟩).val + (2 * k.val + 2) := by
    intros y hy0 hyt hyout; unfold assembleF; simp [hy0, hyt, hyout]
  intro x
  apply Fin.ext
  by_cases h0 : x.val = 0
  · -- f(x) val = 2k+1, f(f(x)) val = 0 = x.val
    have hfx := eval_case0 x h0
    have hffx := eval_caseM (assembleF n k p_in p_out x) (by omega)
    omega
  · by_cases ht : x.val = 2 * k.val + 1
    · -- f(x) val = 0, f(f(x)) val = 2k+1 = x.val
      have hfx := eval_caseM x ht
      have hffx := eval_case0 (assembleF n k p_in p_out x) (by omega)
      omega
    · by_cases hin : x.val ≤ 2 * k.val
      · -- Inside case: f(x).val = (p_in(x-1)).val + 1
        have hxi_lt : x.val - 1 < 2 * k.val := by omega
        have hfx := eval_caseIn x h0 ht hin
        -- f(x) is in the inside case: (p_in(x-1)).val + 1 is in {1,...,2k}
        have hpin_val := (p_in ⟨x.val - 1, hxi_lt⟩).isLt
        -- f(x).val ≠ 0, ≠ 2k+1, ≤ 2k
        have hfx_ne0 : (assembleF n k p_in p_out x).val ≠ 0 := by omega
        have hfx_net : (assembleF n k p_in p_out x).val ≠ 2 * k.val + 1 := by omega
        have hfx_in : (assembleF n k p_in p_out x).val ≤ 2 * k.val := by omega
        have hffx := eval_caseIn (assembleF n k p_in p_out x) hfx_ne0 hfx_net hfx_in
        -- hffx: f(f(x)).val = (p_in ⟨f(x).val - 1, _⟩).val + 1
        -- f(x).val - 1 = (p_in(x-1)).val, so p_in(f(x).val - 1) = p_in(p_in(x-1)) = x-1
        have hkey : (p_in ⟨(assembleF n k p_in p_out x).val - 1,
              by have := (assembleF n k p_in p_out x).isLt; omega⟩).val = x.val - 1 := by
          have heq : ⟨(assembleF n k p_in p_out x).val - 1,
                by have := (assembleF n k p_in p_out x).isLt; omega⟩ =
              p_in ⟨x.val - 1, hxi_lt⟩ := by
            apply Fin.ext; simp only []; omega
          rw [heq]
          exact hinv_in_val ⟨x.val - 1, hxi_lt⟩
        omega
      · -- Outside case: f(x).val = (p_out(x-(2k+2))).val + (2k+2)
        have hxoff_lt : x.val - (2 * k.val + 2) < 2 * (n - k.val) := by
          have := x.isLt; omega
        have hfx := eval_caseOut x h0 ht hin
        have hpout_val := (p_out ⟨x.val - (2 * k.val + 2), hxoff_lt⟩).isLt
        -- f(x) is in the outside case
        have hfx_ne0 : (assembleF n k p_in p_out x).val ≠ 0 := by omega
        have hfx_net : (assembleF n k p_in p_out x).val ≠ 2 * k.val + 1 := by omega
        have hfx_noin : ¬ (assembleF n k p_in p_out x).val ≤ 2 * k.val := by omega
        have hffx := eval_caseOut (assembleF n k p_in p_out x) hfx_ne0 hfx_net hfx_noin
        -- hffx: f(f(x)).val = (p_out ⟨f(x).val-(2k+2), _⟩).val + (2k+2)
        -- f(x).val - (2k+2) = (p_out(x-(2k+2))).val
        have hkey : (p_out ⟨(assembleF n k p_in p_out x).val - (2 * k.val + 2),
              by have := (assembleF n k p_in p_out x).isLt; omega⟩).val =
            x.val - (2 * k.val + 2) := by
          have heq : ⟨(assembleF n k p_in p_out x).val - (2 * k.val + 2),
                by have := (assembleF n k p_in p_out x).isLt; omega⟩ =
              p_out ⟨x.val - (2 * k.val + 2), hxoff_lt⟩ := by
            apply Fin.ext; simp only []; omega
          rw [heq]
          exact hinv_out_val ⟨x.val - (2 * k.val + 2), hxoff_lt⟩
        omega
/-- Build the assembled Perm from the involutive function. -/
noncomputable def assemblePerm (n : ℕ) (k : Fin (n + 1))
    (p_in : Perm (Fin (2 * k.val))) (p_out : Perm (Fin (2 * (n - k.val))))
    (hinv_in : ∀ x, p_in (p_in x) = x) (hinv_out : ∀ x, p_out (p_out x) = x) :
    Perm (Fin (2 * (n + 1))) :=
  (assembleF_involutive n k p_in p_out hinv_in hinv_out).toPerm

/-- The assembled permutation is a pairing. -/
private lemma assemblePerm_isPairing (n : ℕ) (k : Fin (n + 1))
    (p_in : Pairing k.val) (p_out : Pairing (n - k.val)) :
    IsPairing (assemblePerm n k p_in.val p_out.val
      (by intro x; have h := p_in.property.1; rw [sq] at h
          change (p_in.val * p_in.val) x = x; simp [h])
      (by intro x; have h := p_out.property.1; rw [sq] at h
          change (p_out.val * p_out.val) x = x; simp [h])) := by
  constructor
  · -- Involution: assembleF is involutive, and assemblePerm is its toPerm
    have hinv_in : ∀ y : Fin (2 * k.val), p_in.val (p_in.val y) = y := by
      intro y; have h := p_in.property.1; rw [sq] at h
      change (p_in.val * p_in.val) y = y; simp [h]
    have hinv_out : ∀ y : Fin (2 * (n - k.val)), p_out.val (p_out.val y) = y := by
      intro y; have h := p_out.property.1; rw [sq] at h
      change (p_out.val * p_out.val) y = y; simp [h]
    have hinvol := assembleF_involutive n k p_in.val p_out.val hinv_in hinv_out
    -- assemblePerm * assemblePerm = 1 means (assemblePerm x)(assemblePerm x y) = y
    -- assemblePerm is h.toPerm, so assemblePerm y = assembleF ... y by definition
    have key : ∀ y : Fin (2 * (n + 1)),
        (assemblePerm n k p_in.val p_out.val hinv_in hinv_out)
        ((assemblePerm n k p_in.val p_out.val hinv_in hinv_out) y) = y := by
      intro y
      change (Function.Involutive.toPerm (assembleF n k p_in.val p_out.val) hinvol)
        ((Function.Involutive.toPerm (assembleF n k p_in.val p_out.val) hinvol) y) = y
      simp only [Function.Involutive.toPerm, coe_fn_mk]
      exact hinvol y
    ext x; simp only [Equiv.Perm.mul_apply, sq]; exact congr_arg Fin.val (key x)
  · -- FPF: assembleF(x) ≠ x
    intro x hfix
    simp only [assemblePerm, Function.Involutive.toPerm, coe_fn_mk] at hfix
    -- Unfold assembleF and do case analysis
    unfold assembleF at hfix
    split_ifs at hfix with h0 ht hin
    · -- x = 0 → f(x) = 2k+1 ≠ 0 (unless k = ... but 2k+1 ≥ 1)
      have := congr_arg Fin.val hfix; simp at this; omega
    · -- x = 2k+1 → f(x) = 0 ≠ 2k+1
      have := congr_arg Fin.val hfix; simp at this; omega
    · -- Inside: f(x) = p_in(x-1)+1 = x means p_in(x-1) = x-1, contradicting p_in's FPF
      have heq := congr_arg Fin.val hfix; simp at heq
      have : (p_in.val ⟨x.val - 1, by omega⟩).val = x.val - 1 := by omega
      have : p_in.val ⟨x.val - 1, by omega⟩ = ⟨x.val - 1, by omega⟩ := Fin.ext this
      exact p_in.property.2 ⟨x.val - 1, by omega⟩ this
    · -- Outside: f(x) = p_out(x-2k-2)+2k+2 = x means p_out(x-2k-2) = x-2k-2
      have heq := congr_arg Fin.val hfix; simp only at heq
      have : (p_out.val ⟨x.val - (2 * k.val + 2), by have := x.isLt; omega⟩).val =
          x.val - (2 * k.val + 2) := by omega
      have : p_out.val ⟨x.val - (2 * k.val + 2), by have := x.isLt; omega⟩ =
          ⟨x.val - (2 * k.val + 2), by have := x.isLt; omega⟩ := Fin.ext this
      exact p_out.property.2 _ this

/-- The assembled pairing sends 0 to 2k+1. -/
private lemma assemblePerm_zero (n : ℕ) (k : Fin (n + 1))
    (p_in : Pairing k.val) (p_out : Pairing (n - k.val))
    (hinv_in : ∀ x, p_in.val (p_in.val x) = x) (hinv_out : ∀ x, p_out.val (p_out.val x) = x) :
    (assemblePerm n k p_in.val p_out.val hinv_in hinv_out) ⟨0, by omega⟩ =
      ⟨2 * k.val + 1, by omega⟩ := by
  simp [assemblePerm, Function.Involutive.toPerm, assembleF]

/-- The assembled pairing is noncrossing. -/
private lemma assemblePerm_isNoncrossing (n : ℕ) (k : Fin (n + 1))
    (p_in : NoncrossingPairing k.val) (p_out : NoncrossingPairing (n - k.val)) :
    let ap := assemblePerm n k p_in.val.val p_out.val.val
      (by intro x; have h := p_in.val.property.1; rw [sq] at h
          change (p_in.val.val * p_in.val.val) x = x; simp [h])
      (by intro x; have h := p_out.val.property.1; rw [sq] at h
          change (p_out.val.val * p_out.val.val) x = x; simp [h])
    let pairing : Pairing (n + 1) := ⟨ap, assemblePerm_isPairing n k p_in.val p_out.val⟩
    pairing.IsNoncrossing := by
  intro ap pairing
  apply no_crossing_imp_IsNoncrossing
  -- Show ¬HasCrossing by contradiction
  intro ⟨a, b, hab, hbpa, hpapb⟩
  -- Extract noncrossing hypotheses
  have h_nc_in := IsNoncrossing_imp_no_crossing
    ⟨p_in.val.val, p_in.val.property⟩ p_in.property
  have h_nc_out := IsNoncrossing_imp_no_crossing
    ⟨p_out.val.val, p_out.val.property⟩ p_out.property
  -- The assembled perm equals assembleF pointwise
  have ap_eq : ∀ x, ap x = assembleF n k p_in.val.val p_out.val.val x := by
    intro x; change (Function.Involutive.toPerm _ _) x = _
    simp [Function.Involutive.toPerm]
  -- Convert crossing hypotheses to use assembleF
  -- pairing.val = ap definitionally, and ap x = assembleF ... x
  have hbpa' : b.val < (assembleF n k p_in.val.val p_out.val.val a).val := by
    change b.val < (ap a).val; exact hbpa
  have hpapb' : (assembleF n k p_in.val.val p_out.val.val a).val <
      (assembleF n k p_in.val.val p_out.val.val b).val := by
    change (ap a).val < (ap b).val; exact hpapb
  -- Case analysis on which region a is in
  by_cases ha0 : a.val = 0
  · -- a = 0: assembleF(a) = 2k+1
    have hapa : (assembleF n k p_in.val.val p_out.val.val a).val = 2 * k.val + 1 := by
      unfold assembleF; simp [ha0]
    -- b.val < 2k+1, so b is in {1,...,2k} (inside)
    have hb_ne0 : b.val ≠ 0 := by omega
    have hb_ne_t : b.val ≠ 2 * k.val + 1 := by omega
    have hb_in : b.val ≤ 2 * k.val := by omega
    -- assembleF(b) is inside, so assembleF(b).val ≤ 2k
    have hfb_in : (assembleF n k p_in.val.val p_out.val.val b).val ≤ 2 * k.val := by
      unfold assembleF; simp [hb_ne0, hb_ne_t, hb_in]
    -- But 2k+1 < assembleF(b).val contradicts assembleF(b).val ≤ 2k
    omega
  · by_cases hat : a.val = 2 * k.val + 1
    · -- a = 2k+1: assembleF(a) = 0, but b.val > a.val ≥ 1 and b.val < 0 is impossible
      have hapa : (assembleF n k p_in.val.val p_out.val.val a).val = 0 := by
        unfold assembleF; simp [hat]
      omega
    · by_cases hain : a.val ≤ 2 * k.val
      · -- a is inside: assembleF(a) is inside
        have hfa_val : (assembleF n k p_in.val.val p_out.val.val a).val =
            (p_in.val.val ⟨a.val - 1, by omega⟩).val + 1 := by
          unfold assembleF; simp [ha0, hat, hain]
        have hfa_le : (assembleF n k p_in.val.val p_out.val.val a).val ≤ 2 * k.val := by
          rw [hfa_val]; have := (p_in.val.val ⟨a.val - 1, by omega⟩).isLt; omega
        -- b is between a and assembleF(a), both ≤ 2k, so b ≤ 2k
        have hb_le : b.val ≤ 2 * k.val := by omega
        have hb_ne0 : b.val ≠ 0 := by omega
        have hb_ne_t : b.val ≠ 2 * k.val + 1 := by omega
        have hfb_val : (assembleF n k p_in.val.val p_out.val.val b).val =
            (p_in.val.val ⟨b.val - 1, by omega⟩).val + 1 := by
          unfold assembleF; simp [hb_ne0, hb_ne_t, hb_le]
        -- Crossing in p_in: (a-1) < (b-1) < p_in(a-1) < p_in(b-1)
        apply h_nc_in
        refine ⟨⟨a.val - 1, by omega⟩, ⟨b.val - 1, by omega⟩, by simp; omega, ?_, ?_⟩
        · change b.val - 1 < (p_in.val.val ⟨a.val - 1, by omega⟩).val
          omega
        · change (p_in.val.val ⟨a.val - 1, by omega⟩).val <
              (p_in.val.val ⟨b.val - 1, by omega⟩).val
          omega
      · -- a is outside: a.val ≥ 2k+2
        push Not at hain
        have hfa_val : (assembleF n k p_in.val.val p_out.val.val a).val =
            (p_out.val.val ⟨a.val - (2 * k.val + 2), by have := a.isLt; omega⟩).val +
            (2 * k.val + 2) := by
          unfold assembleF; simp [ha0, hat, show ¬ (a.val ≤ 2 * k.val) from by omega]
        have hfa_ge : 2 * k.val + 2 ≤
            (assembleF n k p_in.val.val p_out.val.val a).val := by
          rw [hfa_val]; omega
        -- b is between a and assembleF(a), and a ≥ 2k+2, so b ≥ 2k+2
        have hb_ge : b.val ≥ 2 * k.val + 2 := by omega
        have hb_ne0 : b.val ≠ 0 := by omega
        have hb_ne_t : b.val ≠ 2 * k.val + 1 := by omega
        have hb_noin : ¬ (b.val ≤ 2 * k.val) := by omega
        have hfb_val : (assembleF n k p_in.val.val p_out.val.val b).val =
            (p_out.val.val ⟨b.val - (2 * k.val + 2), by have := b.isLt; omega⟩).val +
            (2 * k.val + 2) := by
          unfold assembleF; simp [hb_ne0, hb_ne_t, hb_noin]
        -- Crossing in p_out: (a-off) < (b-off) < p_out(a-off) < p_out(b-off)
        apply h_nc_out
        refine ⟨⟨a.val - (2 * k.val + 2), by have := a.isLt; omega⟩,
          ⟨b.val - (2 * k.val + 2), by have := b.isLt; omega⟩,
          by simp; omega, ?_, ?_⟩
        · change b.val - (2 * k.val + 2) <
              (p_out.val.val ⟨a.val - (2 * k.val + 2), by have := a.isLt; omega⟩).val
          omega
        · change (p_out.val.val ⟨a.val - (2 * k.val + 2), by have := a.isLt; omega⟩).val <
              (p_out.val.val ⟨b.val - (2 * k.val + 2), by have := b.isLt; omega⟩).val
          omega

/-- The inverse of catalanDecompose: assemble a noncrossing pairing from
    k and independent inside/outside pairings. -/
noncomputable def catalanAssemble (n : ℕ)
    (x : Σ (k : Fin (n + 1)), NoncrossingPairing k.val × NoncrossingPairing (n - k.val)) :
    NoncrossingPairing (n + 1) :=
  let k := x.1
  let p_in := x.2.1
  let p_out := x.2.2
  let hinv_in : ∀ x, p_in.val.val (p_in.val.val x) = x := by
    intro x; have h := p_in.val.property.1; rw [sq] at h
    change (p_in.val.val * p_in.val.val) x = x; simp [h]
  let hinv_out : ∀ x, p_out.val.val (p_out.val.val x) = x := by
    intro x; have h := p_out.val.property.1; rw [sq] at h
    change (p_out.val.val * p_out.val.val) x = x; simp [h]
  let ap := assemblePerm n k p_in.val.val p_out.val.val hinv_in hinv_out
  ⟨⟨ap, assemblePerm_isPairing n k p_in.val p_out.val⟩,
   assemblePerm_isNoncrossing n k p_in p_out⟩

/-! ### Round-trip lemmas for the Catalan equivalence -/

/-- Key lemma for left_inv: assembleF with the extracted components recovers
    the original pairing pointwise. -/
private lemma assembleF_eq_of_decompose {n : ℕ} (p : Pairing (n + 1))
    (h_nc : p.IsNoncrossing) :
    let k := extractK p h_nc
    let p_in := restrictInsidePerm p h_nc
    let p_out := restrictOutsidePerm p h_nc
    ∀ (x : Fin (2 * (n + 1))),
      assembleF n k p_in p_out x = p.val x := by
  intro k p_in p_out x
  have hspec := extractK_spec p h_nc
  have hk_le := extractK_le p h_nc
  have hinv : ∀ y, p.val (p.val y) = y := by
    intro y; have h : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
    change (p.val * p.val) y = y; simp [h]
  unfold assembleF
  split_ifs with hx0 hxt hxin
  · -- Case x = 0: assembleF gives ⟨2k+1, _⟩ = p(0)
    have : x = ⟨0, by omega⟩ := Fin.ext hx0
    rw [this]; apply Fin.ext; linarith
  · -- Case x = 2k+1: assembleF gives ⟨0, _⟩ = p(2k+1)
    -- By involution: p(p(0)) = 0, and p(0) = ⟨2k+1, _⟩, so p(2k+1) = 0
    have hp0 : p.val ⟨0, by omega⟩ = ⟨2 * k.val + 1, by omega⟩ := by
      apply Fin.ext; linarith
    have hinv0 := hinv ⟨0, by omega⟩
    rw [hp0] at hinv0
    have : x = ⟨2 * k.val + 1, by omega⟩ := Fin.ext (by simp only; exact hxt)
    rw [this]; exact hinv0.symm
  · -- Case 1 ≤ x ≤ 2k (inside): assembleF gives p_in(x-1)+1 = p(x)
    -- restrictInsidePerm maps j to p(j+1) - 1
    -- So p_in(x-1).val + 1 = (p(x) - 1) + 1 = p(x)
    have hx_pos : 0 < x.val := by omega
    have hx_lt : x.val < 2 * k.val + 1 := by omega
    -- p(x) is in the shadow
    have h_shadow := noncrossing_mapsTo_shadow h_nc x hx_pos (by rw [hspec]; exact hx_lt)
    rw [hspec] at h_shadow
    -- h_shadow.1 : 0 < p(x).val, h_shadow.2 : p(x).val < 2k+1
    -- restrictInsidePerm definition: toFun j gives ⟨p(j+1).val - 1, _⟩
    -- So (p_in ⟨x.val-1, _⟩).val = p(⟨x.val, _⟩).val - 1
    -- because ⟨(x.val-1)+1, _⟩ = x as Fin elements
    have h_pin_unfold : (p_in ⟨x.val - 1, by omega⟩).val =
        (p.val ⟨(x.val - 1) + 1, by omega⟩).val - 1 := by
      change (restrictInsidePerm p h_nc ⟨x.val - 1, by omega⟩).val = _
      simp only [restrictInsidePerm, Equiv.coe_fn_mk, Fin.val_mk]
    have hx_restore : (⟨(x.val - 1) + 1, by omega⟩ : Fin (2 * (n + 1))) = x :=
      Fin.ext (by simp only []; omega)
    rw [hx_restore] at h_pin_unfold
    apply Fin.ext; simp only []; omega
  · -- Case x > 2k+1 (outside): assembleF gives p_out(x-2k-2)+(2k+2) = p(x)
    push Not at hxin
    have hx_gt : 2 * k.val + 1 < x.val := by omega
    have h_outside := outside_closed_of_noncrossing p h_nc x hx_gt
    -- restrictOutsidePerm maps j to p(j+2k+2) - (2k+2)
    have h_pout_unfold : (p_out ⟨x.val - (2 * k.val + 2), by have := x.isLt; omega⟩).val =
        (p.val ⟨(x.val - (2 * k.val + 2)) + 2 * (extractK p h_nc).val + 2, by omega⟩).val -
        (2 * (extractK p h_nc).val + 2) := by
      change (restrictOutsidePerm p h_nc ⟨x.val - (2 * k.val + 2), _⟩).val = _
      simp only [restrictOutsidePerm, Equiv.coe_fn_mk, Fin.val_mk]
    have hx_restore2 : (⟨(x.val - (2 * k.val + 2)) + 2 * (extractK p h_nc).val + 2, by omega⟩ :
        Fin (2 * (n + 1))) = x := Fin.ext (by simp only []; omega)
    rw [hx_restore2] at h_pout_unfold
    apply Fin.ext; simp only []; omega

/-- extractK of the assembled pairing equals the original k. -/
private lemma extractK_of_assemble (n : ℕ) (k : Fin (n + 1))
    (p_in : NoncrossingPairing k.val) (p_out : NoncrossingPairing (n - k.val)) :
    let hinv_in : ∀ x, p_in.val.val (p_in.val.val x) = x := by
      intro x; have h := p_in.val.property.1; rw [sq] at h
      change (p_in.val.val * p_in.val.val) x = x; simp [h]
    let hinv_out : ∀ x, p_out.val.val (p_out.val.val x) = x := by
      intro x; have h := p_out.val.property.1; rw [sq] at h
      change (p_out.val.val * p_out.val.val) x = x; simp [h]
    let ap := assemblePerm n k p_in.val.val p_out.val.val hinv_in hinv_out
    let pairing : Pairing (n + 1) := ⟨ap, assemblePerm_isPairing n k p_in.val p_out.val⟩
    let h_nc := assemblePerm_isNoncrossing n k p_in p_out
    extractK pairing h_nc = k := by
  intro hinv_in hinv_out ap pairing h_nc
  apply Fin.ext
  simp only [extractK, Fin.val_mk]
  -- assemblePerm sends 0 to ⟨2k+1, _⟩
  have h0 : (ap ⟨0, by omega⟩).val = 2 * k.val + 1 := by
    change (Function.Involutive.toPerm (assembleF n k p_in.val.val p_out.val.val)
      (assembleF_involutive n k p_in.val.val p_out.val.val hinv_in hinv_out) ⟨0, _⟩).val = _
    simp [Function.Involutive.toPerm, assembleF]
  -- pairing.val = ap
  have : (pairing.val ⟨0, by omega⟩).val = (ap ⟨0, by omega⟩).val := rfl
  rw [this, h0]; omega

/-! ### The Catalan equivalence -/

/-- The Catalan decomposition (forward direction): a noncrossing pairing
    on 2(n+1) points decomposes into k and independent noncrossing
    pairings on the inside and outside intervals. -/
noncomputable def catalanDecompose (n : ℕ) (p : NoncrossingPairing (n + 1)) :
    Σ (k : Fin (n + 1)), NoncrossingPairing k.val × NoncrossingPairing (n - k.val) :=
  let k := extractK p.val p.property
  ⟨k, insidePairing p.val p.property, outsidePairing p.val p.property⟩

/-- right_inv for the Catalan equivalence.
    Decomposing an assembled pairing recovers the original triple.
    The proof requires handling dependent sigma type equality (HEq).
    Key facts established:
    - extractK of assembled = k (by extractK_of_assemble)
    - restrictInsidePerm of assembled = p_in pointwise (by assembleF inside case)
    - restrictOutsidePerm of assembled = p_out pointwise (by assembleF outside case) -/
-- Helper: for Sigma types indexed by Fin, equality reduces to
-- first-component equality + pointwise val-equality of the nested permutations.
-- We prove this by constructing the HEq from the cast chain.
private lemma sigma_ncp_ext {n : ℕ}
    {k₁ k₂ : Fin (n + 1)} (hk : k₁ = k₂)
    {p₁ : NoncrossingPairing k₁.val} {p₂ : NoncrossingPairing k₂.val}
    {q₁ : NoncrossingPairing (n - k₁.val)} {q₂ : NoncrossingPairing (n - k₂.val)}
    (hp : ∀ (j : Fin (2 * k₁.val)),
      (p₁.val.val j).val = (p₂.val.val ⟨j.val, by rw [← congr_arg Fin.val hk]; exact j.isLt⟩).val)
    (hq : ∀ (j : Fin (2 * (n - k₁.val))),
      (q₁.val.val j).val = (q₂.val.val ⟨j.val, by rw [← congr_arg Fin.val hk]; exact j.isLt⟩).val) :
    (⟨k₁, (p₁, q₁)⟩ :
      Σ (k : Fin (n + 1)), NoncrossingPairing k.val × NoncrossingPairing (n - k.val)) =
    ⟨k₂, (p₂, q₂)⟩ := by
  subst hk
  congr 1
  ext : 1
  · -- p₁ = p₂
    apply Subtype.ext; apply Subtype.ext; apply Equiv.ext
    intro j; exact Fin.ext (hp j)
  · -- q₁ = q₂
    apply Subtype.ext; apply Subtype.ext; apply Equiv.ext
    intro j; exact Fin.ext (hq j)

private lemma catalanEquiv_right_inv (n : ℕ)
    (x : Σ (k : Fin (n + 1)), NoncrossingPairing k.val × NoncrossingPairing (n - k.val)) :
    catalanDecompose n (catalanAssemble n x) = x := by
  obtain ⟨k, p_in, p_out⟩ := x
  -- The LHS is catalanDecompose applied to the assembled pairing.
  -- We need to show it equals ⟨k, (p_in, p_out)⟩.
  -- Use sigma_ncp_ext: show first components match and perm values match pointwise.
  apply sigma_ncp_ext (extractK_of_assemble n k p_in p_out)
  · -- insidePairing round-trip: restrictInsidePerm(assembled)(j).val = (p_in.val.val j').val
    intro j
    simp only [catalanAssemble, insidePairing,
               restrictInsidePerm, Equiv.coe_fn_mk, Fin.val_mk]
    -- j : Fin (2 * (extractK assembled h_nc).val)
    -- Need: (assembled ⟨j.val + 1, _⟩).val - 1 = (p_in.val.val ⟨j.val, _⟩).val
    -- assembled = assemblePerm = toPerm(assembleF)
    -- For j+1 in inside range, assembleF gives p_in(j+1-1) + 1 = p_in(j) + 1
    have hek : (extractK _ (assemblePerm_isNoncrossing n k p_in p_out)).val = k.val :=
      congr_arg Fin.val (extractK_of_assemble n k p_in p_out)
    have hj_lt : j.val < 2 * k.val := by have := j.isLt; omega
    -- Reduce the assembled permutation to `assembleF`; the input `j + 1`
    -- lies in the inside interval, so the inside branch fires.
    have h0 : ¬ (j.val + 1 = 0) := by omega
    have ht : ¬ (j.val + 1 = 2 * k.val + 1) := by omega
    have hin : j.val + 1 ≤ 2 * k.val := by omega
    change (assembleF n k p_in.val.val p_out.val.val ⟨j.val + 1, _⟩).val - 1 =
      (p_in.val.val ⟨j.val, by omega⟩).val
    simp only [assembleF, h0, ht, hin, ↓reduceDIte, Fin.val_mk]
    have hfin : (⟨j.val + 1 - 1, by omega⟩ : Fin (2 * k.val)) = ⟨j.val, by omega⟩ :=
      Fin.ext (by simp)
    simp only [hfin]; omega
  · -- outsidePairing round-trip
    intro j
    simp only [catalanAssemble, outsidePairing,
               restrictOutsidePerm, Equiv.coe_fn_mk, Fin.val_mk]
    have hek : (extractK _ (assemblePerm_isNoncrossing n k p_in p_out)).val = k.val :=
      congr_arg Fin.val (extractK_of_assemble n k p_in p_out)
    have hj_lt : j.val < 2 * (n - k.val) := by have := j.isLt; omega
    have hk_le : k.val ≤ n := by have := k.isLt; omega
    -- Unfold everything to assembleF application
    -- Show that assembleF applied to ⟨j + 2*(extractK..)+2, _⟩ gives outside branch
    -- The input index is > 2k+1, so the outside (else) branch fires
    set ov := j.val + 2 * (extractK _ (assemblePerm_isNoncrossing n k p_in p_out)).val + 2 with hov
    have h0 : ¬ (ov = 0) := by omega
    have ht : ¬ (ov = 2 * k.val + 1) := by omega
    have hout : ¬ (ov ≤ 2 * k.val) := by omega
    change (assembleF n k p_in.val.val p_out.val.val
      ⟨ov, _⟩).val -
      (2 * (extractK _ (assemblePerm_isNoncrossing n k p_in p_out)).val + 2) =
      (p_out.val.val ⟨j.val, by omega⟩).val
    simp only [assembleF, h0, ht, hout, ↓reduceDIte, Fin.val_mk]
    have hfin : (⟨ov - (2 * k.val + 2), by omega⟩ :
        Fin (2 * (n - k.val))) = ⟨j.val, by omega⟩ :=
      Fin.ext (by simp [hek, hov])
    simp only [hfin]; omega

/-- The Catalan decomposition: a noncrossing pairing on 2(n+1) points
    decomposes into a choice of chord target k and independent
    noncrossing pairings on the inside and outside intervals. -/
noncomputable def catalanEquiv (n : ℕ) :
    NoncrossingPairing (n + 1) ≃
    Σ (k : Fin (n + 1)), NoncrossingPairing k.val × NoncrossingPairing (n - k.val) where
  toFun p := catalanDecompose n p
  invFun x := catalanAssemble n x
  left_inv := fun p => by
    apply Subtype.ext; apply Subtype.ext; apply Equiv.ext
    intro x
    -- Unfold catalanAssemble and catalanDecompose
    simp only [catalanDecompose, catalanAssemble]
    -- The assembled perm is built via Involutive.toPerm from assembleF
    change (Function.Involutive.toPerm _ _) x = p.val.val x
    simp only [Function.Involutive.toPerm]
    exact assembleF_eq_of_decompose p.val p.property x
  right_inv := catalanEquiv_right_inv n

/-! ## 5. Counting: NoncrossingPairing n has catalan n elements

`genus_zero_count` conceptually belongs with the genus/noncrossing story in
GenusNoncrossing.lean, but is proved here because it requires `catalanEquiv`
and the finitary cardinality machinery. The import direction
(CatalanRecurrence imports GenusNoncrossing) makes this the only valid home. -/

/-- IsNoncrossing is decidable (via the genus characterization). -/
instance instDecidableIsNoncrossing {n : ℕ} (p : Pairing n) : Decidable p.IsNoncrossing :=
  decidable_of_iff (p.genus = 0) p.genus_zero_iff_noncrossing

instance instFintypeNoncrossingPairing {n : ℕ} : Fintype (NoncrossingPairing n) :=
  Subtype.fintype _

/-- The number of noncrossing pairings on 2n points equals the nth Catalan number. -/
theorem card_noncrossingPairing_eq_catalan (n : ℕ) :
    Fintype.card (NoncrossingPairing n) = catalan n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 =>
      -- NoncrossingPairing 0 has exactly one element
      simp only [catalan]
      have : Unique (NoncrossingPairing 0) :=
        { default := ⟨⟨1, rfl, fun ⟨_, hx⟩ => absurd hx (by omega)⟩, trivial⟩
          uniq := fun ⟨⟨σ, _, _⟩, _⟩ => by
            congr 1; congr 1
            have : IsEmpty (Fin (2 * 0)) := ⟨fun ⟨_, hx⟩ => by omega⟩
            ext x; exact this.elim x }
      exact Fintype.card_unique
    | n + 1 =>
      -- Use catalanEquiv to decompose
      rw [catalan_succ]
      rw [show Fintype.card (NoncrossingPairing (n + 1)) =
        Fintype.card (Σ (k : Fin (n + 1)),
          NoncrossingPairing k.val × NoncrossingPairing (n - k.val))
        from Fintype.card_congr (catalanEquiv n)]
      simp only [Fintype.card_sigma, Fintype.card_prod]
      apply Finset.sum_congr rfl
      intro k _
      rw [ih k.val (by omega), ih (n - k.val) (by omega)]

/-- **Corollary**: the number of genus-zero pairings equals Cₙ. -/
theorem Pairing.genus_zero_count {n : ℕ} :
    Fintype.card { p : Pairing n // p.genus = 0 } = catalan n := by
  rw [show Fintype.card { p : Pairing n // p.genus = 0 } =
    Fintype.card (NoncrossingPairing n)
    from Fintype.card_congr (Equiv.subtypeEquivRight (fun p => p.genus_zero_iff_noncrossing))]
  exact card_noncrossingPairing_eq_catalan n
