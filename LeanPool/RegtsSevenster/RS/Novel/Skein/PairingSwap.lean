/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.StepLedger

/-!
# The pairing transposition of a non-localized repair

A non-localized repair square touches two genuinely distinct
boundary chords.  The repaired matching pairs one end of the first
chord with one end of the second, pairs the two remaining ends with
each other, and agrees with the old matching everywhere else: the
boundary pairing changes by conjugation with a transposition of two
ends of distinct chords.  This is the algebraic heart of the
holonomy programme — repair words act on boundary pairings through
transposition conjugations.
-/

namespace RS

open scoped Classical

variable {α : Type}

namespace EdgeSubset

/-- Once two ends of distinct chords re-pair and every end off the
two chords keeps its match, the two far ends must re-pair with each
other: elimination over the fixed-point-free involution. -/
private theorem far_ends_pair
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    (κ' : F.RelTransitionSystem)
    {e₁ e₂ : W.Flag} (he₁ : e₁ ∈ F.boundaryFlags)
    (he₂ : e₂ ∈ F.boundaryFlags)
    (hP₁2 : κ.pathMatch e₁ he₁ ≠ e₂)
    (hcross : κ'.pathMatch e₁ he₁ = e₂)
    (hout : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      δ ≠ e₁ → δ ≠ e₂ → δ ≠ κ.pathMatch e₁ he₁ →
      δ ≠ κ.pathMatch e₂ he₂ →
      κ'.pathMatch δ hδ = κ.pathMatch δ hδ) :
    κ'.pathMatch (κ.pathMatch e₁ he₁) (κ.pathMatch_mem he₁) =
      κ.pathMatch e₂ he₂ := by
  have hP₁mem : κ.pathMatch e₁ he₁ ∈ F.boundaryFlags :=
    κ.pathMatch_mem he₁
  have hcross' : κ'.pathMatch e₂ he₂ = e₁ :=
    (κ'.pathMatch_congr hcross.symm he₂
      (κ'.pathMatch_mem he₁)).trans (κ'.pathMatch_invol he₁)
  by_contra hne
  have hδmem : κ'.pathMatch (κ.pathMatch e₁ he₁) hP₁mem ∈
      F.boundaryFlags := κ'.pathMatch_mem hP₁mem
  have hδinv : κ'.pathMatch (κ'.pathMatch (κ.pathMatch e₁ he₁)
      hP₁mem) hδmem = κ.pathMatch e₁ he₁ :=
    κ'.pathMatch_invol hP₁mem
  have hδe₁ : κ'.pathMatch (κ.pathMatch e₁ he₁) hP₁mem ≠ e₁ := by
    intro he
    have h1 : κ'.pathMatch e₁ he₁ = κ.pathMatch e₁ he₁ :=
      (κ'.pathMatch_congr he.symm he₁ hδmem).trans hδinv
    exact hP₁2 (h1.symm.trans hcross)
  have hδe₂ : κ'.pathMatch (κ.pathMatch e₁ he₁) hP₁mem ≠ e₂ := by
    intro he
    have h1 : κ'.pathMatch e₂ he₂ = κ.pathMatch e₁ he₁ :=
      (κ'.pathMatch_congr he.symm he₂ hδmem).trans hδinv
    exact κ.pathMatch_ne_self he₁ (hcross'.symm.trans h1).symm
  have hpres := hout _ hδmem hδe₁ hδe₂
    (κ'.pathMatch_ne_self hP₁mem) hne
  have h2 : κ.pathMatch (κ'.pathMatch (κ.pathMatch e₁ he₁)
      hP₁mem) hδmem = κ.pathMatch e₁ he₁ :=
    hpres.symm.trans hδinv
  have h3 : κ'.pathMatch (κ.pathMatch e₁ he₁) hP₁mem = e₁ :=
    ((κ.pathMatch_invol hδmem).symm.trans
      (κ.pathMatch_congr h2 (κ.pathMatch_mem hδmem)
        hP₁mem)).trans (κ.pathMatch_invol he₁)
  exact hδe₁ h3

/-- **The pairing transposition**: a non-localized repair square
re-pairs one end of each of its two distinct boundary chords with
one end of the other, re-pairs the two far ends with each other,
and preserves every other path match — the boundary pairing changes
by conjugation with a transposition. -/
theorem pathMatch_repair_swap
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v)
    (hnl : ¬ SquareLocalized κ a b c d) :
    ∃ (e₁ e₂ : W.Flag) (he₁ : e₁ ∈ F.boundaryFlags)
      (he₂ : e₂ ∈ F.boundaryFlags),
      e₁ ≠ e₂ ∧ κ.pathMatch e₁ he₁ ≠ e₂ ∧
      (κ.repair a b c d v hsq).pathMatch e₁ he₁ = e₂ ∧
      (κ.repair a b c d v hsq).pathMatch (κ.pathMatch e₁ he₁)
          (κ.pathMatch_mem he₁) = κ.pathMatch e₂ he₂ ∧
      ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
        δ ≠ e₁ → δ ≠ e₂ → δ ≠ κ.pathMatch e₁ he₁ →
        δ ≠ κ.pathMatch e₂ he₂ →
        (κ.repair a b c d v hsq).pathMatch δ hδ =
          κ.pathMatch δ hδ := by
  obtain ⟨β₁, β₂, hβ₁, hβ₂, hca, hcc, h21, h2γ⟩ :=
    twoChains_of_not_localized hsq hnl
  have h12 : β₁ ≠ β₂ := Ne.symm h21
  have hγ₁mem : κ.pathMatch β₁ hβ₁ ∈ F.boundaryFlags :=
    κ.pathMatch_mem hβ₁
  have hγ₂mem : κ.pathMatch β₂ hβ₂ ∈ F.boundaryFlags :=
    κ.pathMatch_mem hβ₂
  have h1γ2 : β₁ ≠ κ.pathMatch β₂ hβ₂ := by
    intro he
    apply h2γ
    have h3 := κ.pathMatch_congr he hβ₁ hγ₂mem
    exact (h3.trans (κ.pathMatch_invol hβ₂)).symm
  have hγ2γ1 : κ.pathMatch β₂ hβ₂ ≠ κ.pathMatch β₁ hβ₁ := by
    intro he
    apply h21
    have h3 := κ.pathMatch_congr he hγ₂mem hγ₁mem
    exact ((κ.pathMatch_invol hβ₂).symm.trans h3).trans
      (κ.pathMatch_invol hβ₁)
  have hγ1β2 : κ.pathMatch β₁ hβ₁ ≠ β₂ := fun he => h2γ he.symm
  have hinv₁ : κ.pathMatch (κ.pathMatch β₁ hβ₁) hγ₁mem = β₁ :=
    κ.pathMatch_invol hβ₁
  have hinv₂ : κ.pathMatch (κ.pathMatch β₂ hβ₂) hγ₂mem = β₂ :=
    κ.pathMatch_invol hβ₂
  have hcb : OnBoundaryChain κ β₁ b :=
    hsq.hab ▸ onBoundaryChain_match hβ₁ hsq.ha hca
  have hcd : OnBoundaryChain κ β₂ d :=
    hsq.hcd ▸ onBoundaryChain_match hβ₂ hsq.hc hcc
  -- canonical chain data and normalized square positions
  obtain ⟨k₁, hk₁le, hcont₁, hterm₁⟩ :=
    chain_terminates_with_data κ hβ₁
  obtain ⟨k₂, hk₂le, hcont₂, hterm₂⟩ :=
    chain_terminates_with_data κ hβ₂
  have hγ₁w : κ.pathMatch β₁ hβ₁ =
      W.pairing (iterWalk κ β₁ k₁) :=
    pathMatch_eq_of_chain κ hβ₁ hcont₁ hterm₁
  have hγ₂w : κ.pathMatch β₂ hβ₂ =
      W.pairing (iterWalk κ β₂ k₂) :=
    pathMatch_eq_of_chain κ hβ₂ hcont₂ hterm₂
  have hpa : ∃ t ≤ k₁, a = iterWalk κ β₁ t ∨
      a = W.pairing (iterWalk κ β₁ t) := by
    obtain ⟨k', t, htk', hcont', hterm', hft⟩ := hca
    have hk : k' = k₁ :=
      chain_exit_unique hcont' hterm' hcont₁ hterm₁
    exact ⟨t, hk ▸ htk', hft⟩
  have hpb : ∃ t ≤ k₁, b = iterWalk κ β₁ t ∨
      b = W.pairing (iterWalk κ β₁ t) := by
    obtain ⟨k', t, htk', hcont', hterm', hft⟩ := hcb
    have hk : k' = k₁ :=
      chain_exit_unique hcont' hterm' hcont₁ hterm₁
    exact ⟨t, hk ▸ htk', hft⟩
  have hpc : ∃ t ≤ k₂, c = iterWalk κ β₂ t ∨
      c = W.pairing (iterWalk κ β₂ t) := by
    obtain ⟨k', t, htk', hcont', hterm', hft⟩ := hcc
    have hk : k' = k₂ :=
      chain_exit_unique hcont' hterm' hcont₂ hterm₂
    exact ⟨t, hk ▸ htk', hft⟩
  have hpd : ∃ t ≤ k₂, d = iterWalk κ β₂ t ∨
      d = W.pairing (iterWalk κ β₂ t) := by
    obtain ⟨k', t, htk', hcont', hterm', hft⟩ := hcd
    have hk : k' = k₂ :=
      chain_exit_unique hcont' hterm' hcont₂ hterm₂
    exact ⟨t, hk ▸ htk', hft⟩
  -- untouched chains avoid the square by rigidity
  have hout : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      δ ≠ β₁ → δ ≠ κ.pathMatch β₁ hβ₁ → δ ≠ β₂ →
      δ ≠ κ.pathMatch β₂ hβ₂ →
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ := by
    intro δ hδ h1 h2 h3 h4
    rw [hγ₁w] at h2
    rw [hγ₂w] at h4
    obtain ⟨kδ, hkδ, hcontδ, htermδ⟩ :=
      chain_terminates_with_data κ hδ
    refine pathMatch_repair_of_avoid hsq hδ hkδ hcontδ htermδ ?_
    intro s hs
    obtain ⟨ta, hta, hfa⟩ := hpa
    obtain ⟨tb, htb, hfb⟩ := hpb
    obtain ⟨tc, htc, hfc⟩ := hpc
    obtain ⟨td, htd, hfd⟩ := hpd
    exact ⟨chain_arg_ne_of_onChain hβ₁ hδ hcont₁ hterm₁ hcontδ
        h1 h2 hta hfa hs,
      chain_arg_ne_of_onChain hβ₁ hδ hcont₁ hterm₁ hcontδ
        h1 h2 htb hfb hs,
      chain_arg_ne_of_onChain hβ₂ hδ hcont₂ hterm₂ hcontδ
        h3 h4 htc hfc hs,
      chain_arg_ne_of_onChain hβ₂ hδ hcont₂ hterm₂ hcontδ
        h3 h4 htd hfd hs⟩
  -- the square hits: each chain family carries the square to the
  -- repaired chain of one of its ends
  have hA := hit_membership hsq hβ₁ hβ₂ h12 h1γ2 hsq.ha hsq.hab
    hca hcc hcd (fun g => Iff.rfl)
  have hswap4 : ∀ g : W.Flag,
      (g = a ∨ g = b ∨ g = c ∨ g = d) ↔
        (g = c ∨ g = d ∨ g = a ∨ g = b) := fun g =>
    ⟨fun h => h.elim (fun h => Or.inr (Or.inr (Or.inl h)))
        (fun h => h.elim (fun h => Or.inr (Or.inr (Or.inr h)))
          (fun h => h.elim Or.inl fun h => Or.inr (Or.inl h))),
      fun h => h.elim (fun h => Or.inr (Or.inr (Or.inl h)))
        (fun h => h.elim (fun h => Or.inr (Or.inr (Or.inr h)))
          (fun h => h.elim Or.inl fun h => Or.inr (Or.inl h)))⟩
  have hC := hit_membership hsq hβ₂ hβ₁ h21 h2γ hsq.hc hsq.hcd
    hcc hca hcb hswap4
  have honc : ∀ {e : W.Flag}, e ∈ F.boundaryFlags →
      OnBoundaryChain (κ.repair a b c d v hsq) e a →
      OnBoundaryChain (κ.repair a b c d v hsq) e c := by
    intro e he h
    have h2 := onBoundaryChain_match
      (κ := κ.repair a b c d v hsq) he hsq.ha h
    rwa [RelTransitionSystem.repair_match_a hsq] at h2
  rcases hA with h₁ | h₁ <;> rcases hC with h₂ | h₂
  · -- ═══════ NEAR ENDS β₁ ↔ β₂ ═══════
    have hcross : (κ.repair a b c d v hsq).pathMatch β₁ hβ₁ =
        β₂ := by
      by_contra hne
      exact onBoundaryChain_disjoint hβ₁ hβ₂ h21
        (fun h => hne h.symm) (honc hβ₁ h₁) h₂
    have hout' : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
        δ ≠ β₁ → δ ≠ β₂ → δ ≠ κ.pathMatch β₁ hβ₁ →
        δ ≠ κ.pathMatch β₂ hβ₂ →
        (κ.repair a b c d v hsq).pathMatch δ hδ =
          κ.pathMatch δ hδ :=
      fun δ hδ q1 q2 q3 q4 => hout δ hδ q1 q3 q2 q4
    exact ⟨β₁, β₂, hβ₁, hβ₂, h12, hγ1β2, hcross,
      far_ends_pair (κ.repair a b c d v hsq) hβ₁ hβ₂ hγ1β2
        hcross hout', hout'⟩
  · -- ═══════ NEAR ENDS β₁ ↔ pathMatch β₂ ═══════
    have hcross : (κ.repair a b c d v hsq).pathMatch β₁ hβ₁ =
        κ.pathMatch β₂ hβ₂ := by
      by_contra hne
      exact onBoundaryChain_disjoint hβ₁ hγ₂mem
        (fun he => h1γ2 he.symm) (fun h => hne h.symm)
        (honc hβ₁ h₁) h₂
    have hout' : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
        δ ≠ β₁ → δ ≠ κ.pathMatch β₂ hβ₂ →
        δ ≠ κ.pathMatch β₁ hβ₁ →
        δ ≠ κ.pathMatch (κ.pathMatch β₂ hβ₂) hγ₂mem →
        (κ.repair a b c d v hsq).pathMatch δ hδ =
          κ.pathMatch δ hδ :=
      fun δ hδ q1 q2 q3 q4 => hout δ hδ q1 q3
        (fun he => q4 (he.trans hinv₂.symm)) q2
    exact ⟨β₁, κ.pathMatch β₂ hβ₂, hβ₁, hγ₂mem, h1γ2,
      fun he => hγ2γ1 he.symm, hcross,
      far_ends_pair (κ.repair a b c d v hsq) hβ₁ hγ₂mem
        (fun he => hγ2γ1 he.symm) hcross hout', hout'⟩
  · -- ═══════ NEAR ENDS pathMatch β₁ ↔ β₂ ═══════
    have hcross : (κ.repair a b c d v hsq).pathMatch
        (κ.pathMatch β₁ hβ₁) hγ₁mem = β₂ := by
      by_contra hne
      exact onBoundaryChain_disjoint hγ₁mem hβ₂ h2γ
        (fun h => hne h.symm) (honc hγ₁mem h₁) h₂
    have hout' : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
        δ ≠ κ.pathMatch β₁ hβ₁ → δ ≠ β₂ →
        δ ≠ κ.pathMatch (κ.pathMatch β₁ hβ₁) hγ₁mem →
        δ ≠ κ.pathMatch β₂ hβ₂ →
        (κ.repair a b c d v hsq).pathMatch δ hδ =
          κ.pathMatch δ hδ :=
      fun δ hδ q1 q2 q3 q4 => hout δ hδ
        (fun he => q3 (he.trans hinv₁.symm)) q1 q2 q4
    exact ⟨κ.pathMatch β₁ hβ₁, β₂, hγ₁mem, hβ₂, hγ1β2,
      fun he => h12 (hinv₁.symm.trans he), hcross,
      far_ends_pair (κ.repair a b c d v hsq) hγ₁mem hβ₂
        (fun he => h12 (hinv₁.symm.trans he)) hcross hout',
      hout'⟩
  · -- ═══════ NEAR ENDS pathMatch β₁ ↔ pathMatch β₂ ═══════
    have hcross : (κ.repair a b c d v hsq).pathMatch
        (κ.pathMatch β₁ hβ₁) hγ₁mem = κ.pathMatch β₂ hβ₂ := by
      by_contra hne
      exact onBoundaryChain_disjoint hγ₁mem hγ₂mem hγ2γ1
        (fun h => hne h.symm) (honc hγ₁mem h₁) h₂
    have hout' : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
        δ ≠ κ.pathMatch β₁ hβ₁ → δ ≠ κ.pathMatch β₂ hβ₂ →
        δ ≠ κ.pathMatch (κ.pathMatch β₁ hβ₁) hγ₁mem →
        δ ≠ κ.pathMatch (κ.pathMatch β₂ hβ₂) hγ₂mem →
        (κ.repair a b c d v hsq).pathMatch δ hδ =
          κ.pathMatch δ hδ :=
      fun δ hδ q1 q2 q3 q4 => hout δ hδ
        (fun he => q3 (he.trans hinv₁.symm)) q1
        (fun he => q4 (he.trans hinv₂.symm)) q2
    exact ⟨κ.pathMatch β₁ hβ₁, κ.pathMatch β₂ hβ₂, hγ₁mem,
      hγ₂mem, fun he => hγ2γ1 he.symm,
      fun he => h1γ2 (hinv₁.symm.trans he), hcross,
      far_ends_pair (κ.repair a b c d v hsq) hγ₁mem hγ₂mem
        (fun he => h1γ2 (hinv₁.symm.trans he)) hcross hout',
      hout'⟩

end EdgeSubset

end RS
