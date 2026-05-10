/-
Copyright (c) 2026 Gerald Doussot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gerald Doussot
-/

theorem StateIndexWithinBounds521
  (index : Nat)
  (offset : Nat)
  (hCol : index ∈ [:5])
  (hOffset : offset < 21)
  : index + offset < 25 := by
  let ⟨ _h₁, h₂ ⟩ := hCol
  simp at h₂
  omega

theorem StateIndexWithinBounds55
  (index : Nat)
  (offset : Nat)
  (hCol : index ∈ [:5])
(hOffset : offset ∈ [:5])
: index + 5 * offset < 25 := by
  let ⟨ _hc₁, hc₂ ⟩ := hCol
  let ⟨ _ho₁, ho₂ ⟩ := hOffset
  simp at hc₂ ho₂
  omega

theorem StateIndexWithinBounds55'
  (index : Nat)
  (hCol₁ : x ∈ [:5])
  (hCol₂ : y ∈ [:5])
  (hi : index = (x + 3 * y) % 5 + 5 * x)
  :  index  < 25  := by
  let ⟨ _hc₁, hc₂ ⟩ := hCol₁
  let ⟨ _ho₁, ho₂ ⟩ := hCol₂
  simp at hc₂ ho₂
  omega
