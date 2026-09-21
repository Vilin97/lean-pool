/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseTrip

/-!
# The pair datum at one pair of subsets

RS21's (13) and (14) at a single pair of subsets of two composable
fragments: the tail function the pair's chords induce on the
interface labels, how it behaves at a through edge, at a cut and
at a pinned end, and the edge term the pair contributes.

`ConverseFamily.lean` chooses one such datum at every subset of the
composition's base and sums the results; `ConverseTrip.lean` carries
the choice up and down the interface.
-/

namespace RS

namespace EdgeSubset

open Fragment Classical

/-- The lexicographic order on the interface's label type. -/
@[reducible] local instance pairBaseOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The same order one stage up. -/
@[reducible] local instance pairOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

/-- The order a stage's surviving labels carry. -/
@[reducible] local instance pairSurvOrder (n : ℕ) :
    LinearOrder (SurvivingLabel
      (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n) (cutR n)) :=
  sumLexSubtypeLinearOrder _ _ _

/-- The order the composition's own label type carries. -/
@[reducible] local instance pairTopOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

open Classical in
/-- **Every interface has a cut colouring**: a two-colouring of its
flags alternating along every edge and across every interface pair.
Each stage extends the next one's colouring.  At an open cut the
cut's two flags take the opposite colour to their partners, which
survive the glue, and the top cut's own condition is then the stage's
alternation along the edge the glue creates.  At a closing cut both
flags leave with the glue, so their colours are free, and the one
constraint the edge and the pair jointly impose is met by opposing
them. -/
theorem exists_cut_colouring : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))),
    ∃ c : V.Flag → Bool, (∀ f, c (V.pairing f) = !c f)
      ∧ ∀ m : Fin n, c (V.boundaryFlag (intR n m))
        = !c (V.boundaryFlag (intL n m))
  -- ═══════ NO CUTS ═══════
  | 0, V => by
    obtain ⟨c, hc⟩ := exists_edge_colouring V
    exact ⟨c, hc, fun m => m.elim0⟩
  -- ═══════ ONE MORE CUT ═══════
  | n + 1, V => by
    obtain ⟨c', hA', hB'⟩ := exists_cut_colouring n (stepFragment n V)
    -- A closing cut extends the colouring across the new circle; an
    -- open one extends it along the rewired edge.
    by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
        = V.boundaryFlag (cutR n)
    · -- ═══════ THE CUT CLOSES ═══════
      refine ⟨cutExtendClosed n V hcl c', fun f => ?_, fun m => ?_⟩
      · by_cases h1 : f = V.boundaryFlag (cutL n)
        · subst h1
          rw [hcl, cutExtendClosed_cutR, cutExtendClosed_cutL,
            Bool.not_true]
        · by_cases h2 : f = V.boundaryFlag (cutR n)
          · subst h2
            have hcl' : V.pairing (V.boundaryFlag (cutR n))
                = V.boundaryFlag (cutL n) := by
              rw [← hcl, V.pairing_invol]
            rw [hcl', cutExtendClosed_cutL, cutExtendClosed_cutR,
              Bool.not_false]
          · have k1 := pairing_ne_cutL_of_closed n V hcl f h2
            have k2 := pairing_ne_cutR_of_closed n V hcl f h1
            rw [cutExtendClosed_of_ne n V hcl c' _ k1 k2,
              cutExtendClosed_of_ne n V hcl c' _ h1 h2,
              ← pairing_stageFlagClosed n V hcl f h1 h2 k1 k2]
            exact hA' _
      · refine Fin.lastCases ?_ (fun b => ?_) m
        · rw [intR_last, intL_last, cutExtendClosed_cutR,
            cutExtendClosed_cutL, Bool.not_true]
        · have hbL := fun (hx : V.boundaryFlag
              (intL (n + 1) b.castSucc) = V.boundaryFlag (cutL n)) =>
            intL_ne_cutL n b (V.boundaryFlag_injective hx)
          have hbL2 := fun (hx : V.boundaryFlag
              (intL (n + 1) b.castSucc) = V.boundaryFlag (cutR n)) =>
            intL_ne_cutR n b (V.boundaryFlag_injective hx)
          have hbR := fun (hx : V.boundaryFlag
              (intR (n + 1) b.castSucc) = V.boundaryFlag (cutL n)) =>
            intR_ne_cutL n b (V.boundaryFlag_injective hx)
          have hbR2 := fun (hx : V.boundaryFlag
              (intR (n + 1) b.castSucc) = V.boundaryFlag (cutR n)) =>
            intR_ne_cutR n b (V.boundaryFlag_injective hx)
          rw [cutExtendClosed_of_ne n V hcl c' _ hbR hbR2,
            cutExtendClosed_of_ne n V hcl c' _ hbL hbL2,
            stageFlagClosed_congr n V hcl
              (congrArg V.boundaryFlag
                (interfaceStepEquiv_symm_intR n b).symm) _ _
              (fun hx => hbR (by
                rw [interfaceStepEquiv_symm_intR n b] at hx
                exact hx))
              (fun hx => hbR2 (by
                rw [interfaceStepEquiv_symm_intR n b] at hx
                exact hx)),
            stageFlagClosed_congr n V hcl
              (congrArg V.boundaryFlag
                (interfaceStepEquiv_symm_intL n b).symm) _ _
              (fun hx => hbL (by
                rw [interfaceStepEquiv_symm_intL n b] at hx
                exact hx))
              (fun hx => hbL2 (by
                rw [interfaceStepEquiv_symm_intL n b] at hx
                exact hx)),
            stageFlagClosed_boundaryFlag n V hcl (intR n b),
            stageFlagClosed_boundaryFlag n V hcl (intL n b)]
          exact hB' b
    · -- ═══════ THE CUT STAYS OPEN ═══════
      have hop := hcl
      have hL1 : V.pairing (V.boundaryFlag (cutL n))
          ≠ V.boundaryFlag (cutL n) := V.pairing_ne _
      have hR2 : V.pairing (V.boundaryFlag (cutR n))
          ≠ V.boundaryFlag (cutR n) := V.pairing_ne _
      have hR1 : V.pairing (V.boundaryFlag (cutR n))
          ≠ V.boundaryFlag (cutL n) := fun hx =>
        hop (by rw [← hx, V.pairing_invol])
      refine ⟨cutExtend n V hop hL1 hR1 hR2 c', fun f => ?_,
        fun m => ?_⟩
      · by_cases h1 : f = V.boundaryFlag (cutL n)
        · subst h1
          rw [cutExtend_cutL,
            cutExtend_of_ne n V hop hL1 hR1 hR2 c' _ hL1 hop,
            Bool.not_not]
        · by_cases h2 : f = V.boundaryFlag (cutR n)
          · subst h2
            rw [cutExtend_cutR,
              cutExtend_of_ne n V hop hL1 hR1 hR2 c' _ hR1 hR2,
              Bool.not_not]
          · by_cases k1 : V.pairing f = V.boundaryFlag (cutL n)
            · have hf : f = V.pairing (V.boundaryFlag (cutL n)) := by
                rw [← k1, V.pairing_invol]
              subst hf
              rw [V.pairing_invol, cutExtend_cutL,
                cutExtend_of_ne n V hop hL1 hR1 hR2 c' _ h1 h2]
            · by_cases k2 : V.pairing f = V.boundaryFlag (cutR n)
              · have hf : f = V.pairing (V.boundaryFlag (cutR n)) := by
                  rw [← k2, V.pairing_invol]
                subst hf
                rw [V.pairing_invol, cutExtend_cutR,
                  cutExtend_of_ne n V hop hL1 hR1 hR2 c' _ h1 h2]
              · rw [cutExtend_of_ne n V hop hL1 hR1 hR2 c' _ k1 k2,
                  cutExtend_of_ne n V hop hL1 hR1 hR2 c' _ h1 h2,
                  ← pairing_stageFlag_of_ne n V hop f h1 h2 k1 k2]
                exact hA' _
      · refine Fin.lastCases ?_ (fun b => ?_) m
        · rw [intR_last, intL_last, cutExtend_cutR, cutExtend_cutL,
            Bool.not_not,
            ← pairing_stageFlag_cutR n V hop hR1 hR2 hL1 hop]
          exact (hA' _).symm
        · have hbL := fun (hx : V.boundaryFlag
              (intL (n + 1) b.castSucc) = V.boundaryFlag (cutL n)) =>
            intL_ne_cutL n b (V.boundaryFlag_injective hx)
          have hbL2 := fun (hx : V.boundaryFlag
              (intL (n + 1) b.castSucc) = V.boundaryFlag (cutR n)) =>
            intL_ne_cutR n b (V.boundaryFlag_injective hx)
          have hbR := fun (hx : V.boundaryFlag
              (intR (n + 1) b.castSucc) = V.boundaryFlag (cutL n)) =>
            intR_ne_cutL n b (V.boundaryFlag_injective hx)
          have hbR2 := fun (hx : V.boundaryFlag
              (intR (n + 1) b.castSucc) = V.boundaryFlag (cutR n)) =>
            intR_ne_cutR n b (V.boundaryFlag_injective hx)
          rw [cutExtend_of_ne n V hop hL1 hR1 hR2 c' _ hbR hbR2,
            cutExtend_of_ne n V hop hL1 hR1 hR2 c' _ hbL hbL2,
            stageFlag_congr n V hop
              (congrArg V.boundaryFlag
                (interfaceStepEquiv_symm_intR n b).symm) _ _
              (fun hx => hbR (by
                rw [interfaceStepEquiv_symm_intR n b] at hx
                exact hx))
              (fun hx => hbR2 (by
                rw [interfaceStepEquiv_symm_intR n b] at hx
                exact hx)),
            stageFlag_congr n V hop
              (congrArg V.boundaryFlag
                (interfaceStepEquiv_symm_intL n b).symm) _ _
              (fun hx => hbL (by
                rw [interfaceStepEquiv_symm_intL n b] at hx
                exact hx))
              (fun hx => hbL2 (by
                rw [interfaceStepEquiv_symm_intL n b] at hx
                exact hx)),
            stageFlag_boundaryFlag n V hop (intR n b),
            stageFlag_boundaryFlag n V hop (intL n b)]
          exact hB' b

/-- Every left label is the left half of its own pair. -/
theorem intL_cast {n : ℕ} (i : Fin (0 + n)) :
    intL n (Fin.cast (by omega) i) = Sum.inl i :=
  congrArg Sum.inl (Fin.ext rfl)

/-- Every right label is the right half of its own pair. -/
theorem intR_cast {n : ℕ} (j : Fin (n + 0)) :
    intR n (Fin.cast (by omega) j) = Sum.inr j :=
  congrArg Sum.inr (Fin.ext rfl)

open Classical in
/-- **The directions the two matchings prescribe.**  At a used
label's boundary flag the matching's tail; elsewhere the given
colouring. -/
noncomputable def pairTailFun {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool) : (closeBase F G).Flag → Bool :=
  fun f =>
    if h : ∃ m : Fin t,
        f = (closeBase F G).boundaryFlag (intL t m)
          ∧ F.boundaryFlag m ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
      then M₁.tail ⟨h.choose, h.choose_spec.2⟩
    else if h' : ∃ m : Fin t,
        f = (closeBase F G).boundaryFlag (intR t m)
          ∧ G.boundaryFlag m ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags
      then M₂.tail ⟨h'.choose, h'.choose_spec.2⟩
    else c f

open Classical in
/-- At a flag that is no used label's, the prescribed direction is
the colouring's. -/
theorem pairTailFun_of_not_used {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool) (f : (closeBase F G).Flag)
    (h : ¬ ∃ m : Fin t,
      f = (closeBase F G).boundaryFlag (intL t m)
        ∧ F.boundaryFlag m ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags)
    (h' : ¬ ∃ m : Fin t,
      f = (closeBase F G).boundaryFlag (intR t m)
        ∧ G.boundaryFlag m ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags) :
    pairTailFun hc₁ hc₂ M₁ M₂ c f = c f := by
  unfold pairTailFun
  rw [dif_neg h, dif_neg h']

/-- The left labels are distinct. -/
theorem intL_inj {n : ℕ} {m m' : Fin n} (h : intL n m = intL n m') :
    m = m' := by
  have h2 : (Fin.cast (by omega) m : Fin (0 + n))
      = Fin.cast (by omega) m' := Sum.inl.inj h
  have h3 := congrArg Fin.val h2
  simp only [Fin.val_cast] at h3
  exact Fin.ext h3

/-- The right labels are distinct. -/
theorem intR_inj {n : ℕ} {m m' : Fin n} (h : intR n m = intR n m') :
    m = m' := by
  have h2 : (Fin.cast (by omega) m : Fin (n + 0))
      = Fin.cast (by omega) m' := Sum.inr.inj h
  have h3 := congrArg Fin.val h2
  simp only [Fin.val_cast] at h3
  exact Fin.ext h3

open Classical in
/-- At a used left label the prescribed direction is the left
matching's tail. -/
theorem pairTailFun_intL {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool) (m : Fin t)
    (hm : F.boundaryFlag m
      ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags) :
    pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intL t m))
      = M₁.tail ⟨m, hm⟩ := by
  have h : ∃ m' : Fin t,
      (closeBase F G).boundaryFlag (intL t m)
          = (closeBase F G).boundaryFlag (intL t m')
        ∧ F.boundaryFlag m'
          ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags := ⟨m, rfl, hm⟩
  unfold pairTailFun
  rw [dif_pos h]
  refine congrArg M₁.tail (Subtype.ext ?_)
  exact (intL_inj ((closeBase F G).boundaryFlag_injective
    h.choose_spec.1)).symm

open Classical in
/-- At a used right label the prescribed direction is the right
matching's tail. -/
theorem pairTailFun_intR {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool) (m : Fin t)
    (hm : G.boundaryFlag m
      ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags) :
    pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intR t m))
      = M₂.tail ⟨m, hm⟩ := by
  have hno : ¬ ∃ m' : Fin t,
      (closeBase F G).boundaryFlag (intR t m)
          = (closeBase F G).boundaryFlag (intL t m')
        ∧ F.boundaryFlag m'
          ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags := by
    rintro ⟨m', hx, -⟩
    exact Sum.inr_ne_inl
      ((closeBase F G).boundaryFlag_injective hx)
  have h : ∃ m' : Fin t,
      (closeBase F G).boundaryFlag (intR t m)
          = (closeBase F G).boundaryFlag (intR t m')
        ∧ G.boundaryFlag m'
          ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags := ⟨m, rfl, hm⟩
  unfold pairTailFun
  rw [dif_neg hno, dif_pos h]
  refine congrArg M₂.tail (Subtype.ext ?_)
  exact (intR_inj ((closeBase F G).boundaryFlag_injective
    h.choose_spec.1)).symm

/-- **At a through label the chord is the edge.**  The chain from a
through label's flag is the single edge, so the chord partner's flag
is the pairing partner. -/
theorem boundaryFlag_chordInv_of_through {α : Type} [LinearOrder α]
    {W : Fragment α} (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    {i : α} (h : W.boundaryFlag i ∈ F.boundaryFlags)
    (hthr : IsThroughLabel F i) :
    W.boundaryFlag (chordInv F κ i)
      = W.pairing (W.boundaryFlag i) := by
  rw [boundaryFlag_chordInv F κ h]
  exact κ.pathMatch_eq_pairing h hthr

open Classical in
/-- **The prescribed directions flip along a through edge on the
left.**  The chord is the edge, and a matching's two ends are
oppositely directed. -/
theorem pairTailFun_flip_through_left {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    {κ₁ : (EdgeSubset.mk s₁ hc₁).RelTransitionSystem}
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool)
    (hM₁ : ∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
      (M₁.edge a).val = chordInv (EdgeSubset.mk s₁ hc₁) κ₁ a.val)
    (m : Fin t)
    (hm : F.boundaryFlag m ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags)
    (hthr : IsThroughLabel (EdgeSubset.mk s₁ hc₁) m) :
    pairTailFun hc₁ hc₂ M₁ M₂ c ((closeBase F G).pairing
        ((closeBase F G).boundaryFlag (intL t m)))
      = !pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intL t m)) := by
  have hbase : (closeBase F G).pairing
        ((closeBase F G).boundaryFlag (intL t m))
      = (closeBase F G).boundaryFlag
        (intL t (chordInv (EdgeSubset.mk s₁ hc₁) κ₁ m)) := by
    rw [pairing_boundaryFlag_intL]
    exact congrArg Sum.inl
      (boundaryFlag_chordInv_of_through (EdgeSubset.mk s₁ hc₁) κ₁ hm
        hthr).symm
  have hedge : M₁.edge ⟨m, hm⟩
      = ⟨chordInv (EdgeSubset.mk s₁ hc₁) κ₁ m,
        chordInv_mem (EdgeSubset.mk s₁ hc₁) κ₁ hm⟩ :=
    Subtype.ext (hM₁ ⟨m, hm⟩)
  rw [hbase, pairTailFun_intL hc₁ hc₂ M₁ M₂ c _
      (chordInv_mem (EdgeSubset.mk s₁ hc₁) κ₁ hm),
    pairTailFun_intL hc₁ hc₂ M₁ M₂ c m hm, ← hedge,
    M₁.tail_flip]

open Classical in
/-- **The prescribed directions flip along a through edge on the
right.** -/
theorem pairTailFun_flip_through_right {t : ℕ}
    {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    {κ₂ : (EdgeSubset.mk s₂ hc₂).RelTransitionSystem}
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool)
    (hM₂ : ∀ b : UsedLab (EdgeSubset.mk s₂ hc₂),
      (M₂.edge b).val = chordInv (EdgeSubset.mk s₂ hc₂) κ₂ b.val)
    (m : Fin t)
    (hm : G.boundaryFlag m ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (hthr : IsThroughLabel (EdgeSubset.mk s₂ hc₂) m) :
    pairTailFun hc₁ hc₂ M₁ M₂ c ((closeBase F G).pairing
        ((closeBase F G).boundaryFlag (intR t m)))
      = !pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intR t m)) := by
  have hbase : (closeBase F G).pairing
        ((closeBase F G).boundaryFlag (intR t m))
      = (closeBase F G).boundaryFlag
        (intR t (chordInv (EdgeSubset.mk s₂ hc₂) κ₂ m)) := by
    rw [pairing_boundaryFlag_intR]
    exact congrArg Sum.inr
      (boundaryFlag_chordInv_of_through (EdgeSubset.mk s₂ hc₂) κ₂ hm
        hthr).symm
  have hedge : M₂.edge ⟨m, hm⟩
      = ⟨chordInv (EdgeSubset.mk s₂ hc₂) κ₂ m,
        chordInv_mem (EdgeSubset.mk s₂ hc₂) κ₂ hm⟩ :=
    Subtype.ext (hM₂ ⟨m, hm⟩)
  rw [hbase, pairTailFun_intR hc₁ hc₂ M₁ M₂ c _
      (chordInv_mem (EdgeSubset.mk s₂ hc₂) κ₂ hm),
    pairTailFun_intR hc₁ hc₂ M₁ M₂ c m hm, ← hedge,
    M₂.tail_flip]

open Classical in
/-- **The prescribed directions alternate across a used cut.**  This
is RS21's Eulerian position, read at the interface pair: the two
matchings' tails are opposite at every used label. -/
theorem pairTailFun_cut {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool)
    (hb : ∀ i : Fin t,
      F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
        ↔ G.boundaryFlag i ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (halt : ∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
      M₂.tail (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
          (EdgeSubset.mk s₂ hc₂) hb a)
        = !M₁.tail a)
    (m : Fin t)
    (hm : F.boundaryFlag m
      ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags) :
    pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intR t m))
      = !pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intL t m)) := by
  rw [pairTailFun_intR hc₁ hc₂ M₁ M₂ c m ((hb m).mp hm),
    pairTailFun_intL hc₁ hc₂ M₁ M₂ c m hm]
  exact halt ⟨m, hm⟩

open Classical in
/-- **The flip at a pinned left label.**  When the label's partner is
internal its direction is the orientation's own, so the boundary
flag's prescribed direction has only to be the chain direction's
opposite — which is what the matching's tail is. -/
theorem flip_pinned_left {t : ℕ} {F G : Fragment (Fin t)}
    {B : EdgeSubset (closeBase F G)} {κ : B.RelTransitionSystem}
    (O : κ.Orientation) (g : (closeBase F G).Flag → Bool)
    {A₁ : EdgeSubset F} {κ₁ : A₁.RelTransitionSystem}
    (o₁ : κ₁.Orientation)
    (hL : ∀ x : F.Flag, O.isOut (Sum.inl x) = o₁.isOut x)
    (m : Fin t) (hint : cutFlagL F G m ∈ B.internalFlags)
    (hg : g ((closeBase F G).boundaryFlag (intL t m))
      = !chainDir o₁ (F.boundaryFlag m)) :
    (orientReplace O g).isOut (cutFlagL F G m)
      = !(orientReplace O g).isOut
        ((closeBase F G).boundaryFlag (intL t m)) := by
  rw [isOut_orientReplace_internal O g hint,
    isOut_orientReplace_of_not_internal O g
      (boundaryFlag_not_internal B (intL t m)), hg, Bool.not_not]
  show O.isOut ((closeBase F G).pairing
    ((closeBase F G).boundaryFlag (intL t m))) = _
  rw [pairing_boundaryFlag_intL]
  exact hL _

open Classical in
/-- **The flip at a pinned right label.** -/
theorem flip_pinned_right {t : ℕ} {F G : Fragment (Fin t)}
    {B : EdgeSubset (closeBase F G)} {κ : B.RelTransitionSystem}
    (O : κ.Orientation) (g : (closeBase F G).Flag → Bool)
    {A₂ : EdgeSubset G} {κ₂ : A₂.RelTransitionSystem}
    (o₂ : κ₂.Orientation)
    (hR : ∀ y : G.Flag, O.isOut (Sum.inr y) = o₂.isOut y)
    (m : Fin t) (hint : cutFlagR F G m ∈ B.internalFlags)
    (hg : g ((closeBase F G).boundaryFlag (intR t m))
      = !chainDir o₂ (G.boundaryFlag m)) :
    (orientReplace O g).isOut (cutFlagR F G m)
      = !(orientReplace O g).isOut
        ((closeBase F G).boundaryFlag (intR t m)) := by
  rw [isOut_orientReplace_internal O g hint,
    isOut_orientReplace_of_not_internal O g
      (boundaryFlag_not_internal B (intR t m)), hg, Bool.not_not]
  show O.isOut ((closeBase F G).pairing
    ((closeBase F G).boundaryFlag (intR t m))) = _
  rw [pairing_boundaryFlag_intR]
  exact hR _

open Classical in
/-- **At a pinned left label the tail is the chain direction's
opposite.** -/
theorem pairTailFun_pinned_left {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    {κ₁ : (EdgeSubset.mk s₁ hc₁).RelTransitionSystem}
    (o₁ : κ₁.Orientation)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool)
    (hag₁ : ∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
      ¬ IsThroughLabel (EdgeSubset.mk s₁ hc₁) a.val →
      M₁.tail a = (cutMatching (EdgeSubset.mk s₁ hc₁) κ₁ o₁).tail a)
    (m : Fin t)
    (hm : F.boundaryFlag m ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags)
    (hnt : ¬ IsThroughLabel (EdgeSubset.mk s₁ hc₁) m) :
    pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intL t m))
      = !chainDir o₁ (F.boundaryFlag m) := by
  rw [pairTailFun_intL hc₁ hc₂ M₁ M₂ c m hm, hag₁ ⟨m, hm⟩ hnt]
  exact cutMatching_tail_of_not_through (EdgeSubset.mk s₁ hc₁) κ₁ o₁
    ⟨m, hm⟩ hnt

open Classical in
/-- **At a pinned right label the tail is the chain direction's
opposite.** -/
theorem pairTailFun_pinned_right {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    {κ₂ : (EdgeSubset.mk s₂ hc₂).RelTransitionSystem}
    (o₂ : κ₂.Orientation)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool)
    (hag₂ : ∀ b : UsedLab (EdgeSubset.mk s₂ hc₂),
      ¬ IsThroughLabel (EdgeSubset.mk s₂ hc₂) b.val →
      M₂.tail b = (cutMatching (EdgeSubset.mk s₂ hc₂) κ₂ o₂).tail b)
    (m : Fin t)
    (hm : G.boundaryFlag m ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (hnt : ¬ IsThroughLabel (EdgeSubset.mk s₂ hc₂) m) :
    pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intR t m))
      = !chainDir o₂ (G.boundaryFlag m) := by
  rw [pairTailFun_intR hc₁ hc₂ M₁ M₂ c m hm, hag₂ ⟨m, hm⟩ hnt]
  exact cutMatching_tail_of_not_through (EdgeSubset.mk s₂ hc₂) κ₂ o₂
    ⟨m, hm⟩ hnt

open Classical in
/-- **An unused label's partner label is unused.**  The subset is
closed under the pairing, so a used partner would drag the label in
with it. -/
theorem not_used_of_pairing {α : Type} [LinearOrder α] [Fintype α]
    {W : Fragment α} {s : Finset W.Flag}
    (hc : ∀ f ∈ s, W.pairing f ∈ s) {a b : α}
    (h : W.pairing (W.boundaryFlag a) = W.boundaryFlag b)
    (hu : W.boundaryFlag a ∉ (EdgeSubset.mk s hc).boundaryFlags) :
    W.boundaryFlag b ∉ (EdgeSubset.mk s hc).boundaryFlags := by
  intro hb
  refine hu (boundaryFlag_mem_boundaryFlags ?_)
  have hbs : W.boundaryFlag b ∈ s :=
    mem_flags_of_boundaryFlags _ hb
  have := hc _ hbs
  rwa [← h, W.pairing_invol] at this

open Classical in
/-- **The prescribed directions flip at an unused left label.**  Both
ends fall to the colouring, which alternates along every edge. -/
theorem pairTailFun_flip_unused_left {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool)
    (hcol : ∀ f, c ((closeBase F G).pairing f) = !c f) (m : Fin t)
    (hu : F.boundaryFlag m
      ∉ (EdgeSubset.mk s₁ hc₁).boundaryFlags) :
    pairTailFun hc₁ hc₂ M₁ M₂ c ((closeBase F G).pairing
        ((closeBase F G).boundaryFlag (intL t m)))
      = !pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intL t m)) := by
  rw [pairTailFun_of_not_used hc₁ hc₂ M₁ M₂ c _
      (by
        rintro ⟨m', hx, hu'⟩
        rw [pairing_boundaryFlag_intL] at hx
        exact not_used_of_pairing hc₁ (Sum.inl.inj hx) hu hu')
      (by
        rintro ⟨m', hx, -⟩
        rw [pairing_boundaryFlag_intL] at hx
        exact Sum.inl_ne_inr hx),
    pairTailFun_of_not_used hc₁ hc₂ M₁ M₂ c _
      (by
        rintro ⟨m', hx, hu'⟩
        exact hu (by
          rwa [intL_inj ((closeBase F G).boundaryFlag_injective hx)]))
      (by
        rintro ⟨m', hx, -⟩
        exact Sum.inl_ne_inr
          ((closeBase F G).boundaryFlag_injective hx))]
  exact hcol _

open Classical in
/-- **The prescribed directions flip at an unused right label.** -/
theorem pairTailFun_flip_unused_right {t : ℕ}
    {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool)
    (hcol : ∀ f, c ((closeBase F G).pairing f) = !c f) (m : Fin t)
    (hu : G.boundaryFlag m
      ∉ (EdgeSubset.mk s₂ hc₂).boundaryFlags) :
    pairTailFun hc₁ hc₂ M₁ M₂ c ((closeBase F G).pairing
        ((closeBase F G).boundaryFlag (intR t m)))
      = !pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intR t m)) := by
  rw [pairTailFun_of_not_used hc₁ hc₂ M₁ M₂ c _
      (by
        rintro ⟨m', hx, -⟩
        rw [pairing_boundaryFlag_intR] at hx
        exact Sum.inr_ne_inl hx)
      (by
        rintro ⟨m', hx, hu'⟩
        rw [pairing_boundaryFlag_intR] at hx
        exact not_used_of_pairing hc₂ (Sum.inr.inj hx) hu hu'),
    pairTailFun_of_not_used hc₁ hc₂ M₁ M₂ c _
      (by
        rintro ⟨m', hx, -⟩
        exact Sum.inr_ne_inl
          ((closeBase F G).boundaryFlag_injective hx))
      (by
        rintro ⟨m', hx, hu'⟩
        exact hu (by
          rwa [intR_inj ((closeBase F G).boundaryFlag_injective hx)]))]
  exact hcol _

open Classical in
/-- **The prescribed directions alternate across an unused cut.** -/
theorem pairTailFun_cut_unused {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool)
    (hcut : ∀ m : Fin t,
      c ((closeBase F G).boundaryFlag (intR t m))
        = !c ((closeBase F G).boundaryFlag (intL t m)))
    (m : Fin t)
    (hu₁ : F.boundaryFlag m ∉ (EdgeSubset.mk s₁ hc₁).boundaryFlags)
    (hu₂ : G.boundaryFlag m
      ∉ (EdgeSubset.mk s₂ hc₂).boundaryFlags) :
    pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intR t m))
      = !pairTailFun hc₁ hc₂ M₁ M₂ c
        ((closeBase F G).boundaryFlag (intL t m)) := by
  rw [pairTailFun_of_not_used hc₁ hc₂ M₁ M₂ c _
      (by
        rintro ⟨m', hx, -⟩
        exact Sum.inr_ne_inl
          ((closeBase F G).boundaryFlag_injective hx))
      (by
        rintro ⟨m', hx, hu'⟩
        exact hu₂ (by
          rwa [intR_inj ((closeBase F G).boundaryFlag_injective hx)])),
    pairTailFun_of_not_used hc₁ hc₂ M₁ M₂ c _
      (by
        rintro ⟨m', hx, hu'⟩
        exact hu₁ (by
          rwa [intL_inj ((closeBase F G).boundaryFlag_injective hx)]))
      (by
        rintro ⟨m', hx, -⟩
        exact Sum.inl_ne_inr
          ((closeBase F G).boundaryFlag_injective hx))]
  exact hcut m

/-- **An absent flag's partner is not internal.** -/
theorem pairing_not_internal_of_not_mem {α : Type} [LinearOrder α]
    {W : Fragment α} (B : EdgeSubset W) {f : W.Flag}
    (hf : f ∉ B.flags) : W.pairing f ∉ B.internalFlags := by
  intro hx
  exact hf (by
    have := B.pairing_mem _ (mem_flags_of_internalFlags B hx)
    rwa [W.pairing_invol] at this)

open Classical in
/-- An unused left label's flag is absent from the joined subset. -/
theorem inl_boundaryFlag_not_mem_closeJoin {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁) (s₂ : Finset G.Flag)
    (m : Fin t)
    (hu : F.boundaryFlag m
      ∉ (EdgeSubset.mk s₁ hc₁).boundaryFlags) :
    (closeBase F G).boundaryFlag (intL t m) ∉ closeJoin s₁ s₂ :=
  fun hx => hu (boundaryFlag_mem_boundaryFlags
    (inl_mem_joinParts.mp hx))

open Classical in
/-- An unused right label's flag is absent from the joined
subset. -/
theorem inr_boundaryFlag_not_mem_closeJoin {t : ℕ}
    {F G : Fragment (Fin t)} (s₁ : Finset F.Flag)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (m : Fin t)
    (hu : G.boundaryFlag m
      ∉ (EdgeSubset.mk s₂ hc₂).boundaryFlags) :
    (closeBase F G).boundaryFlag (intR t m) ∉ closeJoin s₁ s₂ :=
  fun hx => hu (boundaryFlag_mem_boundaryFlags
    (inr_mem_joinParts.mp hx))

open Classical in
/-- **The pair's prescribed orientation flips along every interface
edge.**  Six cases: at a used label the matchings supply the
direction — the chord's two ends by `tail_flip`, the pinned end by
the tail's agreement with the chain — and at an unused label the cut
colouring does. -/
theorem orientReplace_pairTailFun_flip {t : ℕ}
    {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    {κ₁ : (EdgeSubset.mk s₁ hc₁).RelTransitionSystem}
    (o₁ : κ₁.Orientation)
    {κ₂ : (EdgeSubset.mk s₂ hc₂).RelTransitionSystem}
    (o₂ : κ₂.Orientation)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool)
    (hcol : ∀ f, c ((closeBase F G).pairing f) = !c f)
    (hM₁ : ∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
      (M₁.edge a).val = chordInv (EdgeSubset.mk s₁ hc₁) κ₁ a.val)
    (hM₂ : ∀ b : UsedLab (EdgeSubset.mk s₂ hc₂),
      (M₂.edge b).val = chordInv (EdgeSubset.mk s₂ hc₂) κ₂ b.val)
    (hag₁ : ∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
      ¬ IsThroughLabel (EdgeSubset.mk s₁ hc₁) a.val →
      M₁.tail a = (cutMatching (EdgeSubset.mk s₁ hc₁) κ₁ o₁).tail a)
    (hag₂ : ∀ b : UsedLab (EdgeSubset.mk s₂ hc₂),
      ¬ IsThroughLabel (EdgeSubset.mk s₂ hc₂) b.val →
      M₂.tail b = (cutMatching (EdgeSubset.mk s₂ hc₂) κ₂ o₂).tail b)
    {κ : (EdgeSubset.mk (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂)).RelTransitionSystem}
    (O : κ.Orientation)
    (hL : ∀ x : F.Flag, O.isOut (Sum.inl x) = o₁.isOut x)
    (hR : ∀ y : G.Flag, O.isOut (Sum.inr y) = o₂.isOut y)
    (ℓ : Fin (0 + t) ⊕ Fin (t + 0)) :
    (orientReplace O (pairTailFun hc₁ hc₂ M₁ M₂ c)).isOut
        ((closeBase F G).pairing ((closeBase F G).boundaryFlag ℓ))
      = !(orientReplace O (pairTailFun hc₁ hc₂ M₁ M₂ c)).isOut
        ((closeBase F G).boundaryFlag ℓ) := by
  cases ℓ with
  | inl i =>
    rw [← intL_cast i]
    by_cases hm : F.boundaryFlag (Fin.cast (by omega) i)
        ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
    · by_cases hthr : IsThroughLabel (EdgeSubset.mk s₁ hc₁)
          (Fin.cast (by omega) i)
      · have hpart : (closeBase F G).pairing
              ((closeBase F G).boundaryFlag
                (intL t (Fin.cast (by omega) i)))
            = (closeBase F G).boundaryFlag (intL t
              (chordInv (EdgeSubset.mk s₁ hc₁) κ₁
                (Fin.cast (by omega) i))) := by
          rw [pairing_boundaryFlag_intL]
          exact congrArg Sum.inl
            (boundaryFlag_chordInv_of_through
              (EdgeSubset.mk s₁ hc₁) κ₁ hm hthr).symm
        rw [isOut_orientReplace_of_not_internal O _
            (by rw [hpart]; exact boundaryFlag_not_internal _ _),
          isOut_orientReplace_of_not_internal O _
            (boundaryFlag_not_internal _ _)]
        exact pairTailFun_flip_through_left hc₁ hc₂ M₁ M₂ c hM₁ _
          hm hthr
      · exact flip_pinned_left O _ o₁ hL _
          (internal_cutFlagL hc₁ hc₂ _ hm hthr)
          (pairTailFun_pinned_left hc₁ hc₂ o₁ M₁ M₂ c hag₁ _ hm
            hthr)
    · rw [isOut_orientReplace_of_not_internal O _
          (pairing_not_internal_of_not_mem _
            (inl_boundaryFlag_not_mem_closeJoin hc₁ s₂ _ hm)),
        isOut_orientReplace_of_not_internal O _
          (boundaryFlag_not_internal _ _)]
      exact pairTailFun_flip_unused_left hc₁ hc₂ M₁ M₂ c hcol _ hm
  | inr j =>
    rw [← intR_cast j]
    by_cases hm : G.boundaryFlag (Fin.cast (by omega) j)
        ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags
    · by_cases hthr : IsThroughLabel (EdgeSubset.mk s₂ hc₂)
          (Fin.cast (by omega) j)
      · have hpart : (closeBase F G).pairing
              ((closeBase F G).boundaryFlag
                (intR t (Fin.cast (by omega) j)))
            = (closeBase F G).boundaryFlag (intR t
              (chordInv (EdgeSubset.mk s₂ hc₂) κ₂
                (Fin.cast (by omega) j))) := by
          rw [pairing_boundaryFlag_intR]
          exact congrArg Sum.inr
            (boundaryFlag_chordInv_of_through
              (EdgeSubset.mk s₂ hc₂) κ₂ hm hthr).symm
        rw [isOut_orientReplace_of_not_internal O _
            (by rw [hpart]; exact boundaryFlag_not_internal _ _),
          isOut_orientReplace_of_not_internal O _
            (boundaryFlag_not_internal _ _)]
        exact pairTailFun_flip_through_right hc₁ hc₂ M₁ M₂ c hM₂ _
          hm hthr
      · exact flip_pinned_right O _ o₂ hR _
          (internal_cutFlagR hc₁ hc₂ _ hm hthr)
          (pairTailFun_pinned_right hc₁ hc₂ o₂ M₁ M₂ c hag₂ _ hm
            hthr)
    · rw [isOut_orientReplace_of_not_internal O _
          (pairing_not_internal_of_not_mem _
            (inr_boundaryFlag_not_mem_closeJoin s₁ hc₂ _ hm)),
        isOut_orientReplace_of_not_internal O _
          (boundaryFlag_not_internal _ _)]
      exact pairTailFun_flip_unused_right hc₁ hc₂ M₁ M₂ c hcol _ hm

open Classical in
/-- **The pair's prescribed orientation alternates across every
interface pair.**  At a used label this is the Eulerian position of
the two matchings; at an unused one, the cut colouring. -/
theorem orientReplace_pairTailFun_cut {t : ℕ}
    {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (c : (closeBase F G).Flag → Bool)
    (hcut : ∀ m : Fin t,
      c ((closeBase F G).boundaryFlag (intR t m))
        = !c ((closeBase F G).boundaryFlag (intL t m)))
    (hb : ∀ i : Fin t,
      F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
        ↔ G.boundaryFlag i ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (halt : ∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
      M₂.tail (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
          (EdgeSubset.mk s₂ hc₂) hb a)
        = !M₁.tail a)
    {κ : (EdgeSubset.mk (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂)).RelTransitionSystem}
    (O : κ.Orientation) (m : Fin t) :
    (orientReplace O (pairTailFun hc₁ hc₂ M₁ M₂ c)).isOut
        ((closeBase F G).boundaryFlag (intR t m))
      = !(orientReplace O (pairTailFun hc₁ hc₂ M₁ M₂ c)).isOut
        ((closeBase F G).boundaryFlag (intL t m)) := by
  rw [isOut_orientReplace_of_not_internal O _
      (boundaryFlag_not_internal _ _),
    isOut_orientReplace_of_not_internal O _
      (boundaryFlag_not_internal _ _)]
  by_cases hm : F.boundaryFlag m
      ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
  · exact pairTailFun_cut hc₁ hc₂ M₁ M₂ c hb halt m hm
  · exact pairTailFun_cut_unused hc₁ hc₂ M₁ M₂ c hcut m hm
      (fun hx => hm ((hb m).mpr hx))

/-- **The lift is balanced at the top cut.**  The glue joins the two
cut flags' partners into one edge, so a pairing-closed stage subset
takes them together — and the lift then takes both cut flags or
neither. -/
theorem cutBalanced_top_liftSubsetOpen {t : ℕ}
    {V : Fragment (Fin (0 + t) ⊕ Fin (t + 0))} {i j : Fin (0 + t)
      ⊕ Fin (t + 0)} (hij : i ≠ j)
    (hop : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (s' : Finset (SurvivingFlag V i j))
    (hcs : ∀ f ∈ s', Fragment.rewire hop f ∈ s') :
    V.boundaryFlag i ∈ liftSubsetOpen hop s'
      ↔ V.boundaryFlag j ∈ liftSubsetOpen hop s' := by
  rw [boundaryFlagI_mem_liftOpen_iff hij, boundaryFlagJ_mem_liftOpen_iff hij]
  constructor
  · intro hI
    have h := hcs _ hI
    rwa [Fragment.rewire_eq_partnerSurvJ hop _
      (V.pairing_invol _)] at h
  · intro hJ
    have hne : V.pairing (V.pairing (V.boundaryFlag j))
        ≠ V.boundaryFlag i := by
      rw [V.pairing_invol]
      exact fun hx => hij (V.boundaryFlag_injective hx).symm
    have h := hcs _ hJ
    rwa [Fragment.rewire_eq_partnerSurvI hop _ hne
      (V.pairing_invol _)] at h

/-- Membership survives the transport along a fragment equality. -/
theorem mem_flagsOfEq {L : Type} {V₁ V₂ : Fragment L} (hV : V₁ = V₂)
    (s : Finset V₁.Flag) (f : V₁.Flag) :
    flagOfEq hV f ∈ flagsOfEq V₁ V₂ hV s ↔ f ∈ s := by
  subst hV
  exact Iff.rfl

/-- **A stage boundary flag is in the transported subset exactly
when the base's is in the lift.** -/
theorem mem_stage_boundaryFlag_iff (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (s' : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (bl : Fin (0 + n) ⊕ Fin (n + 0)) :
    ((stepFragment n V).boundaryFlag bl ∈ flagsOfEq
        (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_open n V hop) s')
      ↔ (V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val
        ∈ liftSubsetOpen hop s') := by
  rw [boundaryFlag_stepFragment_open n V hop bl]
  exact (mem_flagsOfEq (gluePair_eq_open n V hop) s' _).trans
    (surviving_val_mem_liftOpen_iff hop s' _).symm

/-- **The lift of a balanced stage subset is balanced.**  The top cut
is balanced by the glue's own edge, and each lower pair is the
stage's own. -/
theorem cutBalanced_liftSubsetOpen (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (s' : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (hcs : ∀ f ∈ s', Fragment.rewire hop f ∈ s')
    (hbal : CutBalanced (stepFragment n V)
      (flagsOfEq
        (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_open n V hop) s')) :
    CutBalanced V (liftSubsetOpen hop s') := by
  intro m
  refine Fin.lastCases ?_ (fun b => ?_) m
  · rw [intL_last, intR_last]
    exact cutBalanced_top_liftSubsetOpen (cutL_ne_cutR n) hop s' hcs
  · have hb := (mem_stage_boundaryFlag_iff n V hop s'
      (intL n b)).symm.trans ((hbal b).trans
        (mem_stage_boundaryFlag_iff n V hop s' (intR n b)))
    rw [interfaceStepEquiv_symm_intL n b,
      interfaceStepEquiv_symm_intR n b] at hb
    exact hb

/-- **A stage boundary flag is in the stage's subset exactly when the
base's is in the lift**, at a closing cut. -/
theorem mem_stage_boundaryFlag_iff_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (s' : Finset (SurvivingFlag V (cutL n) (cutR n))) (b : Bool)
    (bl : Fin (0 + n) ⊕ Fin (n + 0)) :
    ((stepFragment n V).boundaryFlag bl ∈ flagsOfEq
        (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl) s')
      ↔ (V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val
        ∈ liftSubsetClosed s' b) := by
  rw [boundaryFlag_stepFragment_closed n V hcl bl]
  exact (mem_flagsOfEq (gluePair_eq_closed n V hcl) s' _).trans
    (surviving_val_mem_liftClosed_iff s' b _).symm

/-- **The lift of a balanced stage subset is balanced**, at a closing
cut: the cut's own pair is in or out together, by the bit. -/
theorem cutBalanced_liftSubsetClosed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (s' : Finset (SurvivingFlag V (cutL n) (cutR n))) (b : Bool)
    (hbal : CutBalanced (stepFragment n V)
      (flagsOfEq
        (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl) s')) :
    CutBalanced V (liftSubsetClosed s' b) := by
  intro m
  refine Fin.lastCases ?_ (fun c => ?_) m
  · rw [intL_last, intR_last,
      boundaryFlagI_mem_liftClosed_iff (cutL_ne_cutR n) s' b,
      boundaryFlagJ_mem_liftClosed_iff (cutL_ne_cutR n) s' b]
  · have hb := (mem_stage_boundaryFlag_iff_closed n V hcl s' b
      (intL n c)).symm.trans ((hbal c).trans
        (mem_stage_boundaryFlag_iff_closed n V hcl s' b (intR n c)))
    rw [interfaceStepEquiv_symm_intL n c,
      interfaceStepEquiv_symm_intR n c] at hb
    exact hb

open Classical in
/-- **The ledger's step keeps the balance.** -/
theorem cutBalanced_stepData (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (D : StageData (n + 1) V)
    (hbal : CutBalanced V D.sub.flags) :
    CutBalanced (stepFragment n V) (stepData n V D).sub.flags := by
  intro b
  have hlift : liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) D.sub.flags) = D.sub.flags :=
    liftSubsetOpen_dropSubset (cutL_ne_cutR n) hop D.sub.flags
      D.sub.pairing_mem
  have key := fun bl => mem_stage_boundaryFlag_iff n V hop
    (V.dropSubset (cutL n) (cutR n) D.sub.flags) bl
  rw [stepData_sub_flags_open n V D hop]
  refine (key (intL n b)).trans (Iff.trans ?_ (key (intR n b)).symm)
  rw [hlift, interfaceStepEquiv_symm_intL n b,
    interfaceStepEquiv_symm_intR n b]
  exact hbal b.castSucc

open Classical in
/-- **The ledger's step keeps the balance**, at a closing cut. -/
theorem cutBalanced_stepData_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (D : StageData (n + 1) V)
    (hbal : CutBalanced V D.sub.flags) :
    CutBalanced (stepFragment n V) (stepData n V D).sub.flags := by
  intro c
  have hlift : liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) D.sub.flags)
      (decide (V.boundaryFlag (cutL n) ∈ D.sub.flags))
      = D.sub.flags :=
    liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl D.sub.flags
      D.sub.pairing_mem
  have key := fun bl => mem_stage_boundaryFlag_iff_closed n V hcl
    (V.dropSubset (cutL n) (cutR n) D.sub.flags)
    (decide (V.boundaryFlag (cutL n) ∈ D.sub.flags)) bl
  rw [stepData_sub_flags_closed n V D hcl]
  refine (key (intL n c)).trans (Iff.trans ?_ (key (intR n c)).symm)
  rw [hlift, interfaceStepEquiv_symm_intL n c,
    interfaceStepEquiv_symm_intR n c]
  exact hbal c.castSucc

open Classical in
/-- **The summand a single datum computes.**  The total form of the
colouring sum: zero where the subset does not carry the state. -/
noncomputable def edgeTermOf {α : Type}
    {V : Fragment α} {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {s : Finset V.Flag} {hc : ∀ f ∈ s, V.pairing f ∈ s}
    (d : Σ κ : (EdgeSubset.mk s hc).RelTransitionSystem,
      κ.Orientation) (st : GenBoundaryState k ℓ α) (C : ℕ) : ℂ :=
  if hbnd : genBoundarySubsetMatches V s st then
    ((-1 : ℂ) ^ C) * (EdgeSubset.mk s hc).edgeSum h st hbnd d.2
  else 0

open Classical in
/-- **The family's summand is its datum's.** -/
theorem edgeTermAt_eq_edgeTermOf {α : Type} [LinearOrder α]
    [Fintype α] {V : Fragment α} {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (𝒟 : DataFamily V)
    (st : GenBoundaryState k ℓ α) {s : Finset V.Flag}
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) (C : ℕ) :
    edgeTermAt h 𝒟 st s C = edgeTermOf h (𝒟 s hc hE hne) st C := by
  unfold edgeTermOf
  split_ifs with hbnd
  · exact edgeTermAt_pos h 𝒟 st hc hbnd hE hne C
  · exact edgeTermAt_eq_zero_of_not_matches h 𝒟 st hbnd C

open Classical in
/-- **The datum's summand transports along an equality of
subsets.** -/
theorem edgeTermOf_ofEq {α : Type} [LinearOrder α] {V : Fragment α}
    {k ℓ : ℕ} (h : MixedFunctional k ℓ) {s s' : Finset V.Flag}
    {hc : ∀ f ∈ s, V.pairing f ∈ s}
    {hc' : ∀ f ∈ s', V.pairing f ∈ s'}
    (hu : (EdgeSubset.mk s hc) = EdgeSubset.mk s' hc')
    (d : Σ κ : (EdgeSubset.mk s hc).RelTransitionSystem,
      κ.Orientation) (st : GenBoundaryState k ℓ α) (C : ℕ) :
    edgeTermOf h ⟨relOfEq hu d.1, orientOfEq hu d.2⟩ st C
      = edgeTermOf h d st C := by
  have hss : s = s' := congrArg EdgeSubset.flags hu
  subst hss
  rfl

/-- **The join carries a diagonal state exactly when its halves carry
the state.** -/
theorem matches_closeJoin_iff {k ℓ : ℕ} {t : ℕ}
    {F G : Fragment (Fin t)} (s₁ : Finset F.Flag)
    (s₂ : Finset G.Flag) (x : GenBoundaryState k ℓ (Fin t)) :
    genBoundarySubsetMatches (closeBase F G) (closeJoin s₁ s₂)
        (diagOf t x)
      ↔ genBoundarySubsetMatches F s₁ x
        ∧ genBoundarySubsetMatches G s₂ x := by
  constructor
  · intro hm
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (inl_mem_joinParts (s₁ := s₁) (s₂ := s₂)
        (f := F.boundaryFlag i)).symm.trans (hm (intL t i))
    · exact (inr_mem_joinParts (s₁ := s₁) (s₂ := s₂)
        (f := G.boundaryFlag i)).symm.trans (hm (intR t i))
  · rintro ⟨h₁, h₂⟩ a
    cases a with
    | inl i =>
      exact (inl_mem_joinParts (s₁ := s₁) (s₂ := s₂)
        (f := F.boundaryFlag (Fin.cast (by omega) i))).trans
        (h₁ (Fin.cast (by omega) i))
    | inr j =>
      exact (inr_mem_joinParts (s₁ := s₁) (s₂ := s₂)
        (f := G.boundaryFlag (Fin.cast (by omega) j))).trans
        (h₂ (Fin.cast (by omega) j))

end EdgeSubset

end RS
