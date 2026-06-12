/-
Copyright (c) 2026 György Kurucz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: György Kurucz
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.OfFn

/-!
# Safety-liveness decomposition

We prove that every linear-time property decomposes as the intersection of a
safety property and a liveness property, following Alpern and Schneider.
-/

namespace SafetyLivenessDecomposition

-- Theorem statement based on:
-- Alpern, Bowen; Schneider, Fred B. Defining liveness.
-- Information Processing Letters 21 (1985), 181-185.
-- https://doi.org/10.1016/0020-0190(85)90056-0

/-- An infinite word over the alphabet `T`, modelled as a function from positions
to letters. -/
abbrev InfWord T := ℕ → T
/-- A finite word over the alphabet `T`, modelled as a list of letters. -/
abbrev FinWord T := List T

/-- Concatenate a finite word `a` in front of an infinite word `b`. -/
def FinWord.append {T} (a : FinWord T) (b : InfWord T) : InfWord T :=
  fun i =>
    if _ : i < a.length then a[i]
    else b (i - a.length)

/-- The length-`k` prefix of an infinite word `w`, as a finite word. -/
def InfWord.slice {T} (w : InfWord T) (k : ℕ) : FinWord T :=
  List.ofFn (fun (i : Fin k) => w i)

/-- A linear-time property: a set of infinite words. -/
abbrev Property T := Set (InfWord T)

/-- A property is a *safety* property when every word outside it has a finite bad
prefix: no extension of that prefix lies in the property. -/
def SafetyProp {T} (P : Property T) :=
  ∀ (σ : InfWord T),
  σ ∉ P →
  ∃ (i : ℕ),
  ∀ (β : InfWord T),
  (σ.slice i).append β ∉ P

/-- A property is a *liveness* property when every finite word can be extended to
an infinite word lying in the property. -/
def LivenessProp {T} (P : Property T) :=
  ∀ (α : FinWord T),
  ∃ (β : InfWord T),
  α.append β ∈ P

-- Code below here mostly written by GPT-5-Codex

section Auxiliary

variable {T : Type u}

@[simp] lemma slice_length (σ : InfWord T) (n : ℕ) : (σ.slice n).length = n := by
  simp [InfWord.slice]

@[simp] lemma slice_get (σ : InfWord T) (n k : ℕ)
    (hk : k < (σ.slice n).length) :
    (σ.slice n)[k] = σ k := by
  simp [InfWord.slice]

lemma slice_append (α : FinWord T) (β : InfWord T) :
    (α.append β).slice α.length = α := by
  have hfun : (fun i : Fin α.length => (α.append β) i)
      = fun i : Fin α.length => α[i] := by
    funext i
    simp [FinWord.append, i.2]
  simp [InfWord.slice, hfun]

lemma append_slice_eq_self (σ : InfWord T) (n : ℕ) :
    (σ.slice n).append (fun k => σ (k + n)) = σ := by
  funext k
  by_cases hk : k < n
  · simp [FinWord.append, hk, slice_length]
  · have hle : n ≤ k := Nat.le_of_not_lt hk
    simp [FinWord.append, hk, slice_length, Nat.sub_add_cancel hle]

end Auxiliary

-- Theorem statement written by hand
theorem safety_liveness_decomposition
  {T}
  [t_nonempty : Nonempty T]
  (P : Property T)
  : ∃ (A B : Property T), SafetyProp A ∧ LivenessProp B ∧ (A ∩ B = P)
  := by
  let A : Property T := {σ : InfWord T | ∀ n, ∃ β : InfWord T, (σ.slice n).append β ∈ P}
  let B : Property T := P ∪ Aᶜ
  refine ⟨A, B, ?_, ?_, ?_⟩
  · -- `A` is a safety property
    intro σ hσ
    have hnot : ¬∀ n, ∃ β : InfWord T, (σ.slice n).append β ∈ P := by
      simpa [A] using hσ
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hforall : ∀ β : InfWord T, (σ.slice i).append β ∉ P := not_exists.mp hi
    refine ⟨i, ?_⟩
    intro β
    have hslice : ((σ.slice i).append β).slice i = σ.slice i := by
      simpa [slice_length] using slice_append (σ.slice i) β
    refine fun hAβ => ?_
    obtain ⟨γ, hγ⟩ := hAβ i
    have hγ' : (σ.slice i).append γ ∈ P := by
      convert hγ using 1
      simp [hslice]
    exact (hforall γ) hγ'
  · -- `B` is a liveness property
    intro α
    by_cases h : ∃ β : InfWord T, α.append β ∈ P
    · rcases h with ⟨β, hβ⟩
      exact ⟨β, Or.inl hβ⟩
    · have hforall : ∀ β : InfWord T, α.append β ∉ P := not_exists.mp h
      obtain ⟨t⟩ := t_nonempty
      refine ⟨fun _ => t, Or.inr ?_⟩
      have hslice : (α.append (fun _ => t)).slice α.length = α := slice_append α _
      refine fun hA => ?_
      obtain ⟨γ, hγ⟩ := hA α.length
      have hγ' : α.append γ ∈ P := by
        convert hγ using 1
        simp [hslice]
      exact (hforall γ) hγ'
  · -- intersection equals `P`
    ext σ; constructor
    · intro hσ
      have hA : σ ∈ A := hσ.1
      have hB : σ ∈ B := hσ.2
      cases hB with
      | inl h => exact h
      | inr h => exact False.elim (h hA)
    · intro hσ
      refine ⟨?_, Or.inl hσ⟩
      intro n
      refine ⟨fun k => σ (k + n), ?_⟩
      convert hσ using 1
      simp [append_slice_eq_self]

end SafetyLivenessDecomposition
