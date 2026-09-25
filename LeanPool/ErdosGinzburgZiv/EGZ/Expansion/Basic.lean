/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Thickness
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedCoordinates
public import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Multiplicity

/-!
# Multiplicities and relative thickness

The expansion argument counts positions in a multiset.  Natural-valued
weights retain these multiplicities when several positions have the same
vector.  Affine changes of coordinates preserve zero sums of length `p`.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ
namespace Expansion

/-- Push a finite multiplicity function through an arbitrary map. -/
noncomputable def pushWeight {α β : Type*} [Fintype α]
    (f : α → β) (w : α → ℕ) (b : β) : ℕ := by
  classical
  exact ∑ a, if f a = b then w a else 0

theorem pushWeight_mono {α β : Type*} [Fintype α]
    (f : α → β) {w u : α → ℕ} (h : w ≤ u) : pushWeight f w ≤ pushWeight f u := by
  classical
  intro b
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · exact h a
  · exact le_rfl

theorem sum_pushWeight {α β M : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid M] (f : α → β) (w : α → ℕ) (g : β → M) :
    (∑ b, pushWeight f w b • g b) = ∑ a, w a • g (f a) := by
  classical
  simp only [pushWeight, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem natMass_pushWeight {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (w : α → ℕ) : natMass (pushWeight f w) = natMass w := by
  simpa [natMass] using sum_pushWeight f w (fun _ ↦ (1 : ℕ))

theorem natMassOn_pushWeight {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (w : α → ℕ) (S : Set β) :
    natMassOn (pushWeight f w) S = natMassOn w (f ⁻¹' S) := by
  classical
  simpa [natMassOn, apply_ite, ite_mul] using
    sum_pushWeight f w (fun b ↦ if b ∈ S then (1 : ℕ) else 0)

theorem pushWeight_comp {α β γ : Type*} [Fintype α] [Fintype β]
    (f : α → β) (g : β → γ) (w : α → ℕ) :
    pushWeight g (pushWeight f w) = pushWeight (g ∘ f) w := by
  classical
  funext c
  simpa [pushWeight, apply_ite, ite_mul] using
    sum_pushWeight f w (fun b ↦ if g b = c then (1 : ℕ) else 0)

/-- Pulling a supported weight back along an injection and pushing it
forward recovers every multiplicity. -/
theorem pushWeight_pullback {α β : Type*} [Fintype α]
    (f : α → β) (hf : Function.Injective f) (w : β → ℕ)
    (hs : ∀ b, w b ≠ 0 → b ∈ Set.range f) :
    pushWeight f (w ∘ f) = w := by
  classical
  funext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    simp only [pushWeight, Function.comp_apply, hf.eq_iff]
    simp
  · have hw : w b = 0 := by_contra fun h ↦ hb (hs b h)
    rw [hw]
    apply Finset.sum_eq_zero
    intro a _
    exact ite_eq_right (fun h ↦ hb ⟨a, h⟩)

/-- Affine maps preserve a zero sum when its total multiplicity is `p`. -/
theorem affine_sum_eq_zero {p m n : ℕ} [NeZero p]
    (A : FpCoord p m →ᵃ[ZMod p] FpCoord p n)
    (w : FpCoord p m → ℕ) (hm : natMass w = p)
    (hz : (∑ v, w v • v) = 0) : (∑ v, w v • A v) = 0 := by
  calc
    (∑ v, w v • A v) = (∑ v, w v • (A.linear v + A 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      exact congrArg (fun z ↦ w v • z) (congrFun A.decomp v)
    _ =
        (∑ v, w v • A.linear v) + (∑ v, w v) • A 0 := by
      simp only [smul_add, Finset.sum_add_distrib,
        Finset.sum_smul]
    _ = A.linear (∑ v, w v • v) + p • A 0 := by
      rw [map_sum]
      simp only [map_nsmul]
      rw [show (∑ v, w v) = p from hm]
    _ = 0 := by rw [hz, map_zero, FpVec.characteristic_nsmul, add_zero]

theorem hasZeroSumMultiplicity_pushWeight {p m n : ℕ} [NeZero p]
    (A : FpCoord p m →ᵃ[ZMod p] FpCoord p n)
    {w : FpCoord p m → ℕ} (h : HasZeroSumMultiplicity w) :
    HasZeroSumMultiplicity (pushWeight A w) := by
  obtain ⟨u, hu, hm, hz⟩ := h
  refine ⟨pushWeight A u, pushWeight_mono A hu, ?_, ?_⟩
  · rwa [natMass_pushWeight]
  · rw [sum_pushWeight]
    exact affine_sum_eq_zero A u hm hz

/-- Two points in one fibre of `φ` are distinguished by `ξ`. -/
def NonconstantOnFibers {p n r : ℕ}
    (φ : FpCoord p n → FpCoord p r)
    (ξ : FpCoord p n →ᵃ[ZMod p] ZMod p) : Prop :=
  ∃ v u, φ v = φ u ∧ ξ v ≠ ξ u

/-- The thickness assumption of the relative expansion theorem. -/
def IsThickRelative {p n r : ℕ} [NeZero p]
    (w : FpCoord p n → ℕ) (φ : FpCoord p n → FpCoord p r)
    (T : ℕ) (δ : ℝ) : Prop :=
  ∀ ξ, NonconstantOnFibers φ ξ → IsThickAlong w ξ T δ

theorem IsThickRelative.mono {p n r T T' : ℕ} [NeZero p]
    {w : FpCoord p n → ℕ} {φ : FpCoord p n → FpCoord p r} {δ δ' : ℝ}
    (h : IsThickRelative w φ T δ) (hT : T' ≤ T) (hδ : δ' ≤ δ) :
    IsThickRelative w φ T' δ' := by
  intro ξ hξ hthin
  exact h ξ hξ ((hthin.mono_width hT).mono_error hδ)

/-- For a linear projection, nonconstancy on its fibres is exactly
nonconstancy on the fibre through zero, even for affine functionals. -/
theorem nonconstantOnFibers_iff_kernel {p n r : ℕ}
    (φ : FpCoord p n →ₗ[ZMod p] FpCoord p r)
    (ξ : FpCoord p n →ᵃ[ZMod p] ZMod p) :
    NonconstantOnFibers φ ξ ↔
      ∃ v u, φ v = 0 ∧ φ u = 0 ∧ ξ v ≠ ξ u := by
  constructor
  · rintro ⟨v, u, hφ, hξ⟩
    refine ⟨v - u, 0, by simp [hφ], by simp, ?_⟩
    intro heq
    apply hξ
    have hlin := ξ.linearMap_vsub v u
    have hlin0 := ξ.linearMap_vsub (v - u) 0
    change ξ.linear (v - u) = ξ v - ξ u at hlin
    change ξ.linear ((v - u) - 0) = ξ (v - u) - ξ 0 at hlin0
    rw [sub_zero, heq, sub_self] at hlin0
    exact sub_eq_zero.mp (hlin.symm.trans hlin0)
  · rintro ⟨v, u, hv, hu, hξ⟩
    exact ⟨v, u, hv.trans hu.symm, hξ⟩

end Expansion
end EGZ
