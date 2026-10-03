/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Localization

/-! # Spatial restriction of a local product box

A support-containing box may be intersected with the open spatial region
on which a pressure gradient is characterized, without changing its time
interval or losing compact containment in the original domain.
-/

public section

open Set
open CKN.Foundation.Parabolic

namespace CKN.Core.Endgame

/-- Intersecting the spatial factor with an open set preserves a local box. -/
theorem localBox_inter_spatial_open
    {Ω U V : Set Vec3} {I J : Set ℝ}
    (hbox : localBox Ω I U J) (hV : IsOpen V) :
    localBox Ω I (U ∩ V) J := by
  have hclosure : closure (U ∩ V) ⊆ closure U := closure_mono inter_subset_left
  exact ⟨hbox.1.inter hV,
    hbox.2.1.of_isClosed_subset isClosed_closure hclosure,
    hclosure.trans hbox.2.2.1, hbox.2.2.2⟩

/-- A spatial support bound is compatible with restriction of its local box. -/
theorem support_subset_inter_spatial_box
    {φ : Vec3 × ℝ → ℝ} {U V : Set Vec3} {J : Set ℝ}
    (hbox : tsupport φ ⊆ U ×ˢ J)
    (hspace : ∀ z ∈ tsupport φ, z.1 ∈ V) :
    tsupport φ ⊆ (U ∩ V) ×ˢ J := by
  intro z hz
  exact ⟨⟨(hbox hz).1, hspace z hz⟩, (hbox hz).2⟩

end CKN.Core.Endgame
