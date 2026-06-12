/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Chain
import Mathlib.Data.Set.Finite.Basic

/-! # Chain -/


namespace List

variable {l l₁ l₂ : List α}
variable {R : α → α → Prop}

lemma _root_.List.IsChain.nodup_of_trans_irreflex
    (R_trans : IsTrans α R) (R_irrefl : Std.Irrefl R) (h_chain : l.IsChain R) :
    l.Nodup := by
  haveI : IsTrans α R := R_trans
  by_contra hC
  replace ⟨d, hC⟩ := List.exists_duplicate_iff_not_nodup.mpr hC
  have hsub := List.duplicate_iff_sublist.mp hC
  rw [List.isChain_iff_pairwise] at h_chain
  have hpair := h_chain.sublist hsub
  have hdd : R d d := by simpa using hpair
  exact R_irrefl.irrefl d hdd

instance finiteNodupList [Finite α] : Finite { l : List α // l.Nodup } := by
  classical
  exact (@fintypeNodupList α (Fintype.ofFinite α)).finite

lemma chains_finite [Finite α] (R_trans : IsTrans α R) (R_irrefl : Std.Irrefl R) :
    Finite { l : List α // l.IsChain R } := by
  classical
  exact Finite.of_injective
    (fun l : { l : List α // l.IsChain R } =>
      (⟨l.1, List.IsChain.nodup_of_trans_irreflex R_trans R_irrefl l.2⟩ :
        { l : List α // l.Nodup }))
    (by
      intro a b h
      cases a
      cases b
      simp at h
      simp [h])

end List
