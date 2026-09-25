/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SlopeScript
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity

/-!
# A subdivision split into two factors and two connector slots

The data are finite incidence tables. They contain no divisors or rank
hypotheses. The first connector is oriented from the left factor to the
right; the second may be stored in either orientation.
-/

namespace Utilities.Certificate.TwoPoleSubdivision

open Finset ExplicitPotential SubdivisionGraph

variable {n p nA pA nB pB : ℕ}

/-! Values of an arbitrary script along a slot, extended constantly past its
last endpoint. This lets us reuse the existing slot-value Laplacian API. -/

def pathValue (s : Spec n p) (f : firingScript s.graph) (e : Fin p) (k : ℕ) : ℤ :=
  if hzero : k = 0 then f (s.coreVertex (s.core.tail e))
  else if hlt : k < s.length e then
    f (s.interiorVertex e ⟨k - 1, by omega⟩)
  else f (s.coreVertex (s.core.head e))

@[simp] theorem pathValue_zero (s : Spec n p) (f : firingScript s.graph) (e : Fin p) :
    pathValue s f e 0 = f (s.coreVertex (s.core.tail e)) := by simp [pathValue]

@[simp] theorem pathValue_length (s : Spec n p) (f : firingScript s.graph) (e : Fin p) :
    pathValue s f e (s.length e) = f (s.coreVertex (s.core.head e)) := by
  simp [pathValue, (s.length_pos e).ne']

@[simp] theorem pathValue_interior (s : Spec n p) (f : firingScript s.graph)
    (e : Fin p) (k : Fin (s.length e - 1)) :
    pathValue s f e (k.val + 1) = f (s.interiorVertex e k) := by
  have hk : k.val + 1 < s.length e := by have := k.isLt; omega
  simp [pathValue, hk]

theorem pathValue_compatible (s : Spec n p) (f : firingScript s.graph) :
    s.SlotValueCompatible (fun v => f (s.coreVertex v)) (pathValue s f) :=
  ⟨pathValue_zero s f, pathValue_length s f⟩

theorem pathValue_script (s : Spec n p) (f : firingScript s.graph) :
    s.slotValueScript (fun v => f (s.coreVertex v)) (pathValue s f) = f := by
  funext v
  cases v with
  | inl a => rfl
  | inr a => exact pathValue_interior s f a.1 a.2

theorem pathValue_slope (s : Spec n p) (f : firingScript s.graph) :
    s.IsStepSlope f (fun e k => pathValue s f e (k + 1) - pathValue s f e k) := by
  have h := s.isStepSlope_slotValueScript (pathValue_compatible s f)
  rwa [pathValue_script] at h

/-- An orientation-aware partition of a core into two factors and two slots. -/
structure Data (core : Core n p) (nA pA nB pB : ℕ) where
  leftCore : Core nA pA
  rightCore : Core nB pB
  vertices : (Fin nA ⊕ Fin nB) ≃ Fin n
  slots : ((Fin pA ⊕ Fin pB) ⊕ Fin 2) ≃ Fin p
  leftPole : Fin 2 → Fin nA
  rightPole : Fin 2 → Fin nB
  left_nonempty : 0 < nA
  right_nonempty : 0 < nB
  tail_left : ∀ e, core.tail (slots (.inl (.inl e))) = vertices (.inl (leftCore.tail e))
  head_left : ∀ e, core.head (slots (.inl (.inl e))) = vertices (.inl (leftCore.head e))
  tail_right : ∀ e, core.tail (slots (.inl (.inr e))) = vertices (.inr (rightCore.tail e))
  head_right : ∀ e, core.head (slots (.inl (.inr e))) = vertices (.inr (rightCore.head e))
  tail_first : core.tail (slots (.inr 0)) = vertices (.inl (leftPole 0))
  head_first : core.head (slots (.inr 0)) = vertices (.inr (rightPole 0))
  second_ends :
    (core.tail (slots (.inr 1)) = vertices (.inl (leftPole 1)) ∧
      core.head (slots (.inr 1)) = vertices (.inr (rightPole 1))) ∨
    (core.tail (slots (.inr 1)) = vertices (.inr (rightPole 1)) ∧
      core.head (slots (.inr 1)) = vertices (.inl (leftPole 1)))

namespace Data

variable (s : Spec n p) (d : Data s.core nA pA nB pB)

/-- The left factor retains its own vertices and its five (in the application)
internal slots, with the original subdivision lengths. -/
def leftSpec : Spec nA pA where
  core := d.leftCore
  length e := s.length (d.slots (.inl (.inl e)))
  core_nonempty := d.left_nonempty
  core_loopless e h := s.core_loopless (d.slots (.inl (.inl e))) (by
    rw [d.tail_left, d.head_left, h])
  length_pos e := s.length_pos _

/-- The corresponding right factor. -/
def rightSpec : Spec nB pB where
  core := d.rightCore
  length e := s.length (d.slots (.inl (.inr e)))
  core_nonempty := d.right_nonempty
  core_loopless e h := s.core_loopless (d.slots (.inl (.inr e))) (by
    rw [d.tail_right, d.head_right, h])
  length_pos e := s.length_pos _

@[simp] theorem leftSpec_core : (d.leftSpec s).core = d.leftCore := rfl
@[simp] theorem rightSpec_core : (d.rightSpec s).core = d.rightCore := rfl
@[simp] theorem leftSpec_length (e : Fin pA) :
    (d.leftSpec s).length e = s.length (d.slots (.inl (.inl e))) := rfl
@[simp] theorem rightSpec_length (e : Fin pB) :
    (d.rightSpec s).length e = s.length (d.slots (.inl (.inr e))) := rfl

def left : (d.leftSpec s).Vertex → s.Vertex
  | .inl a => s.coreVertex (d.vertices (.inl a))
  | .inr ⟨e, k⟩ => s.interiorVertex (d.slots (.inl (.inl e))) k

def right : (d.rightSpec s).Vertex → s.Vertex
  | .inl b => s.coreVertex (d.vertices (.inr b))
  | .inr ⟨e, k⟩ => s.interiorVertex (d.slots (.inl (.inr e))) k

@[simp] theorem left_core (a : Fin nA) :
    d.left s ((d.leftSpec s).coreVertex a) = s.coreVertex (d.vertices (.inl a)) := rfl

@[simp] theorem right_core (b : Fin nB) :
    d.right s ((d.rightSpec s).coreVertex b) = s.coreVertex (d.vertices (.inr b)) := rfl

@[simp] theorem left_interior (e : Fin pA) (k : Fin ((d.leftSpec s).length e - 1)) :
    d.left s ((d.leftSpec s).interiorVertex e k) =
      s.interiorVertex (d.slots (.inl (.inl e))) k := rfl

@[simp] theorem right_interior (e : Fin pB) (k : Fin ((d.rightSpec s).length e - 1)) :
    d.right s ((d.rightSpec s).interiorVertex e k) =
      s.interiorVertex (d.slots (.inl (.inr e))) k := rfl

theorem left_injective : Function.Injective (d.left s) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj (d.vertices.injective (Sum.inl.inj h)))
    | inr b => simp_all [left, Spec.coreVertex, Spec.interiorVertex]
  | inr a =>
    cases b with
    | inl b => simp_all [left, Spec.coreVertex, Spec.interiorVertex]
    | inr b =>
      rcases a with ⟨e, k⟩
      rcases b with ⟨e', k'⟩
      have he : e = e' := Sum.inl.inj (Sum.inl.inj (d.slots.injective
        (congrArg Sigma.fst (Sum.inr.inj h))))
      subst e'
      have hk : k = k' := by
        apply Fin.ext
        exact congrArg (fun x : s.Interior => x.2.val) (Sum.inr.inj h)
      subst k'
      rfl

theorem right_injective : Function.Injective (d.right s) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Sum.inr.inj (d.vertices.injective (Sum.inl.inj h)))
    | inr b => simp_all [right, Spec.coreVertex, Spec.interiorVertex]
  | inr a =>
    cases b with
    | inl b => simp_all [right, Spec.coreVertex, Spec.interiorVertex]
    | inr b =>
      rcases a with ⟨e, k⟩
      rcases b with ⟨e', k'⟩
      have he : e = e' := Sum.inr.inj (Sum.inl.inj (d.slots.injective
        (congrArg Sigma.fst (Sum.inr.inj h))))
      subst e'
      have hk : k = k' := by
        apply Fin.ext
        exact congrArg (fun x : s.Interior => x.2.val) (Sum.inr.inj h)
      subst k'
      rfl

theorem disjoint (a : (d.leftSpec s).Vertex) (b : (d.rightSpec s).Vertex) :
    d.left s a ≠ d.right s b := by
  intro h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact Sum.inl_ne_inr (d.vertices.injective (Sum.inl.inj h))
    | inr b => simp_all [left, right, Spec.coreVertex, Spec.interiorVertex]
  | inr a =>
    cases b with
    | inl b => simp_all [left, right, Spec.coreVertex, Spec.interiorVertex]
    | inr b =>
      exact Sum.inl_ne_inr (Sum.inl.inj (d.slots.injective
        (congrArg Sigma.fst (Sum.inr.inj h))))

def potential (f : firingScript (d.leftSpec s).graph)
    (g : firingScript (d.rightSpec s).graph) (v : Fin n) : ℤ :=
  match d.vertices.symm v with
  | .inl a => f ((d.leftSpec s).coreVertex a)
  | .inr b => g ((d.rightSpec s).coreVertex b)

def values (f : firingScript (d.leftSpec s).graph)
    (g : firingScript (d.rightSpec s).graph) (h : ℕ → ℤ) (e : Fin p) (k : ℕ) : ℤ :=
  match d.slots.symm e with
  | .inl (.inl a) => pathValue (d.leftSpec s) f a k
  | .inl (.inr b) => pathValue (d.rightSpec s) g b k
  | .inr i => if i = 0 then h k else f ((d.leftSpec s).coreVertex (d.leftPole 1))

def script (f : firingScript (d.leftSpec s).graph)
    (g : firingScript (d.rightSpec s).graph) (h : ℕ → ℤ) : firingScript s.graph :=
  s.slotValueScript (d.potential s f g) (d.values s f g h)

theorem compatible (f : firingScript (d.leftSpec s).graph)
    (g : firingScript (d.rightSpec s).graph) (h : ℕ → ℤ)
    (h0 : h 0 = f ((d.leftSpec s).coreVertex (d.leftPole 0)))
    (hL : h (s.length (d.slots (.inr 0))) = g ((d.rightSpec s).coreVertex (d.rightPole 0)))
    (hsecond : f ((d.leftSpec s).coreVertex (d.leftPole 1)) =
      g ((d.rightSpec s).coreVertex (d.rightPole 1))) :
    s.SlotValueCompatible (d.potential s f g) (d.values s f g h) := by
  constructor
  · intro e
    obtain ⟨e, rfl⟩ := d.slots.surjective e
    rcases e with (a | b) | i
    · simp [values, potential, d.tail_left]
    · simp [values, potential, d.tail_right]
    · fin_cases i
      · simpa [values, potential, d.tail_first] using h0
      · rcases d.second_ends with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · simp [values, potential, ht]
        · simpa [values, potential, ht] using hsecond
  · intro e
    obtain ⟨e, rfl⟩ := d.slots.surjective e
    rcases e with (a | b) | i
    · simpa only [values, Equiv.symm_apply_apply, potential, d.head_left,
        d.vertices.symm_apply_apply, leftSpec_length, leftSpec_core]
        using pathValue_length (d.leftSpec s) f a
    · simpa only [values, Equiv.symm_apply_apply, potential, d.head_right,
        d.vertices.symm_apply_apply, rightSpec_length, rightSpec_core]
        using pathValue_length (d.rightSpec s) g b
    · fin_cases i
      · simpa [values, potential, d.head_first] using hL
      · rcases d.second_ends with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · simpa [values, potential, hh] using hsecond
        · simp [values, potential, hh]

theorem slope (f : firingScript (d.leftSpec s).graph)
    (g : firingScript (d.rightSpec s).graph) (h : ℕ → ℤ)
    (hCompat : s.SlotValueCompatible (d.potential s f g) (d.values s f g h)) :
    s.IsStepSlope (d.script s f g h)
      (fun e k => d.values s f g h e (k + 1) - d.values s f g h e k) :=
  s.isStepSlope_slotValueScript hCompat

end Data
end Utilities.Certificate.TwoPoleSubdivision
