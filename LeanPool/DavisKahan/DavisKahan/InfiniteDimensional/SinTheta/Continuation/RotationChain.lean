/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SpectralIdentification
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Finite composition of local direct rotations

This module completes the algebraic transport step in spectral continuation.
The accepted local theorem supplies a unitary intertwiner between two
orthogonal projections whose operator-norm distance is below one.  We compose
those local intertwiners along a finite chain and prove that the product is a
unitary intertwiner between the endpoint projections.

The finite-chain construction is independent of contour spectral
identification.  The lower-level Riesz-path theorem accepts
orthogonal-projectionhood explicitly, while the final specialization discharges
that input from a common family of spectral-separation witnesses.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace unitInterval

universe v

section UnitaryComposition

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- The identity bounded operator is unitary in the continuation predicate. -/
theorem isUnitaryOperator_id :
    TauCeti.LinearPMap.IsUnitaryOperator (ContinuousLinearMap.id ℂ H) := by
  constructor
  · intro x
    rfl
  · intro y
    exact ⟨y, rfl⟩

omit [CompleteSpace H] in
/-- Composition preserves the continuation-facing unitary predicate. -/
theorem isUnitaryOperator_comp
    (U V : H →L[ℂ] H)
    (hU : TauCeti.LinearPMap.IsUnitaryOperator U) (hV : TauCeti.LinearPMap.IsUnitaryOperator V) :
    TauCeti.LinearPMap.IsUnitaryOperator (U ∘L V) := by
  constructor
  · intro x
    calc
      ‖(U ∘L V) x‖ = ‖U (V x)‖ := rfl
      _ = ‖V x‖ := hU.1 (V x)
      _ = ‖x‖ := hV.1 x
  · intro y
    obtain ⟨z, hz⟩ := hU.2 y
    obtain ⟨x, hx⟩ := hV.2 z
    refine ⟨x, ?_⟩
    calc
      (U ∘L V) x = U (V x) := rfl
      _ = U z := congrArg U hx
      _ = y := hz

/-- A finite natural-number chain of pairwise norm-close orthogonal
projections admits one unitary intertwiner between its endpoints.

The proof recursively composes the canonical local direct rotations supplied
by `range_equiv_of_projection_norm_lt_one`. -/
theorem exists_unitary_transport_of_projection_nat_chain
    (P : ℕ → H →L[ℂ] H) (n : ℕ)
    (hprojection : ∀ k, k ≤ n → IsOrthogonalProjection (P k))
    (hclose : ∀ k, k < n → ‖P k - P k.succ‖ < 1) :
    ∃ W : H →L[ℂ] H,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧ W ∘L P 0 = P n ∘L W := by
  induction n generalizing P with
  | zero =>
      refine ⟨ContinuousLinearMap.id ℂ H, isUnitaryOperator_id, ?_⟩
      ext x
      rfl
  | succ n ih =>
      have hprojectionPrev : ∀ k, k ≤ n → IsOrthogonalProjection (P k) := by
        intro k hk
        exact hprojection k (hk.trans (Nat.le_succ n))
      have hclosePrev : ∀ k, k < n → ‖P k - P k.succ‖ < 1 := by
        intro k hk
        exact hclose k (hk.trans (Nat.lt_succ_self n))
      obtain ⟨W, hWunitary, hWintertwines⟩ :=
        ih P hprojectionPrev hclosePrev
      obtain ⟨V, hVunitary, hVintertwines⟩ :=
        range_equiv_of_projection_norm_lt_one
          (P n) (P n.succ)
          (hprojection n (Nat.le_succ n))
          (hprojection n.succ le_rfl)
          (hclose n (Nat.lt_succ_self n))
      refine ⟨V ∘L W, isUnitaryOperator_comp V W hVunitary hWunitary, ?_⟩
      ext x
      have hWx := congrArg (fun T : H →L[ℂ] H => T x) hWintertwines
      have hVx := congrArg (fun T : H →L[ℂ] H => T (W x)) hVintertwines
      simp only [ContinuousLinearMap.comp_apply] at hWx hVx ⊢
      calc
        V (W (P 0 x)) = V (P n (W x)) := congrArg V hWx
        _ = P n.succ (V (W x)) := hVx

end UnitaryComposition

section UniformMesh

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A uniform mesh of norm-close orthogonal projections yields a unitary
intertwiner between the path values at zero and one. -/
theorem exists_unitary_transport_of_projection_uniformMesh
    (P : ℝ → H →L[ℂ] H) (n : ℕ) (hn : 0 < n)
    (hprojection : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsOrthogonalProjection (P t))
    (hclose : ∀ k : ℕ, k < n →
      ‖P ((k : ℝ) / n) - P (((k + 1 : ℕ) : ℝ) / n)‖ < 1) :
    ∃ W : H →L[ℂ] H,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧ W ∘L P 0 = P 1 ∘L W := by
  let Q : ℕ → H →L[ℂ] H := fun k => P ((k : ℝ) / n)
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hQprojection : ∀ k, k ≤ n → IsOrthogonalProjection (Q k) := by
    intro k hk
    apply hprojection
    constructor
    · positivity
    · rw [div_le_one hnreal]
      exact_mod_cast hk
  have hQclose : ∀ k, k < n → ‖Q k - Q k.succ‖ < 1 := by
    intro k hk
    simpa only [Q, Nat.succ_eq_add_one] using hclose k hk
  obtain ⟨W, hWunitary, hWintertwines⟩ :=
    exists_unitary_transport_of_projection_nat_chain
      Q n hQprojection hQclose
  refine ⟨W, hWunitary, ?_⟩
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnreal
  simpa only [Q, Nat.cast_zero, zero_div, div_self hnne] using hWintertwines

/-- A Lipschitz path of orthogonal projections on the unit interval admits a
unitary endpoint intertwiner. -/
theorem exists_unitary_transport_of_lipschitz_projection_path
    (P : ℝ → H →L[ℂ] H) (K : NNReal)
    (hP : LipschitzOnWith K P (Set.Icc (0 : ℝ) 1))
    (hprojection : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsOrthogonalProjection (P t)) :
    ∃ W : H →L[ℂ] H,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧ W ∘L P 0 = P 1 ∘L W := by
  obtain ⟨n, hn, hclose⟩ :=
    exists_uniform_subdivision_norm_sub_lt_one P K hP
  exact exists_unitary_transport_of_projection_uniformMesh
    P n hn hprojection hclose

end UniformMesh

section RieszSpecialization

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Global unitary transport for the fixed-contour affine Riesz path, assuming
spectral identification has supplied orthogonal-projectionhood at every path
parameter. -/
theorem exists_unitary_transport_fixedContourRieszOperator
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A V t).IsSymmetric)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A V t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖)
    (hprojection : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsOrthogonalProjection
        (fixedContourRieszOperator Γ (operatorPath A V t))) :
    ∃ W : H →L[ℂ] H,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧
      W ∘L fixedContourRieszOperator Γ (operatorPath A V 0) =
        fixedContourRieszOperator Γ (operatorPath A V 1) ∘L W := by
  obtain ⟨n, hn, hclose⟩ :=
    exists_uniform_subdivision_fixedContourRieszOperator_norm_sub_lt_one
      Γ A V delta hdelta hself hsep
  exact exists_unitary_transport_of_projection_uniformMesh
    (fun t => fixedContourRieszOperator Γ (operatorPath A V t))
    n hn hprojection hclose

/-- A common proof-carrying separating contour along an affine operator path
produces one unitary intertwiner between the endpoint Riesz projections.

The quantitative common margin supplies the finite subdivision, while spectral
identification supplies orthogonal-projectionhood at every path parameter. -/
theorem exists_unitary_transport_of_spectralSeparatingContour_operatorPath
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (s : Set ℝ)
    (hseparating : ∀ t (_ht : t ∈ Set.Icc (0 : ℝ) 1),
      SpectralSeparatingContour (operatorPath A V t) s)
    (hgeometric : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      (hseparating t ht).geometric = Γ)
    (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A V t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖) :
    ∃ W : H →L[ℂ] H,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧
      W ∘L fixedContourRieszOperator Γ (operatorPath A V 0) =
        fixedContourRieszOperator Γ (operatorPath A V 1) ∘L W := by
  apply exists_unitary_transport_fixedContourRieszOperator
    Γ A V delta hdelta
  · intro t ht
    exact (hseparating t ht).selfAdjoint
  · exact hsep
  · exact fixedContourRieszOperator_operatorPath_isOrthogonalProjection
      Γ A V s hseparating hgeometric

end RieszSpecialization

end DavisKahanExt
end TauCeti
