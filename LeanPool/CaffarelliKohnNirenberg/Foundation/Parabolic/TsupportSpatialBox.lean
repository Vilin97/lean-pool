/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Separation.Regular

/-!
# Tsupport Spatial Box

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open Set
open CKN.Foundation.Parabolic

namespace CKN

/-- Given an open set `Ω` and a compactly supported function `ψ` whose topological support
lies in `Ω`, there exists an open set `Ω'` containing `tsupport ψ` whose closure is compact
and contained in `Ω`. -/
theorem exists_spatial_box_of_tsupport_subset {Ω : Set Vec3} {ψ : Vec3 → ℝ}
    (hΩ : IsOpen Ω) (hψΩ : tsupport ψ ⊆ Ω) (hψc : HasCompactSupport ψ) :
    ∃ Ω' : Set Vec3, IsOpen Ω' ∧ tsupport ψ ⊆ Ω' ∧
      IsCompact (closure Ω') ∧ closure Ω' ⊆ Ω := by
  let K : Set Vec3 := tsupport ψ
  have hK : IsCompact K := hψc.isCompact
  obtain ⟨V₀, hV₀open, hKV₀, hV₀compact⟩ :=
    exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨V₁, hV₁open, hKV₁, hV₁Ω⟩ :=
    hK.exists_isOpen_closure_subset ((hΩ.mem_nhdsSet).2 hψΩ)
  let Ω' := V₀ ∩ V₁
  have hΩ'open : IsOpen Ω' := hV₀open.inter hV₁open
  have hKΩ' : K ⊆ Ω' := fun x hx => ⟨hKV₀ hx, hKV₁ hx⟩
  have hclV₀ : closure Ω' ⊆ closure V₀ := closure_mono inter_subset_left
  have hclV₁ : closure Ω' ⊆ closure V₁ := closure_mono inter_subset_right
  have hΩ'compact : IsCompact (closure Ω') :=
    hV₀compact.of_isClosed_subset isClosed_closure hclV₀
  have hΩ'Ω : closure Ω' ⊆ Ω := hclV₁.trans hV₁Ω
  exact ⟨Ω', hΩ'open, hKΩ', hΩ'compact, hΩ'Ω⟩

end CKN
