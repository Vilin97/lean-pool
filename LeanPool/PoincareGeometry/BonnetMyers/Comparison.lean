/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.Algebra
public import LeanPool.PoincareGeometry.BonnetMyers.IndexForm

/-!
# The finite-dimensional comparison inequality

This file is the algebraic part of the Bonnet--Myers contradiction.  It turns
the Ricci lower bound into the negative sum of the scalar sine index forms on
the orthogonal directions.  No geodesic, completeness, or compactness fact is
used here.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

private lemma card_erase_zero_fin (n : ℕ) (hn : 1 ≤ n) :
    (Finset.card (Finset.univ.erase (⟨0, by omega⟩ : Fin n)) : ℝ) = n - 1 := by
  rw [Finset.card_erase_of_mem]
  · simp only [Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub hn]
    norm_num
  · simp

lemma sum_sineIndexForm_eq_expanded
    {n : ℕ} (hn : 2 ≤ n) (L : ℝ) (q : Fin n → ℝ) (hL : 0 < L) :
    Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin n))
        (fun i ↦ sineIndexForm (q i) L) =
      (n - 1 : ℝ) * (∫ t in (0 : ℝ)..L, sineTestDeriv L t ^ 2) -
        (Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin n)) q) *
          (∫ t in (0 : ℝ)..L, sineTest L t ^ 2) := by
  simp_rw [sineIndexForm]
  rw [Finset.sum_sub_distrib]
  have hD :
      Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin n))
          (fun _ ↦ (∫ t in (0 : ℝ)..L, sineTestDeriv L t ^ 2)) =
        (n - 1 : ℝ) * (∫ t in (0 : ℝ)..L, sineTestDeriv L t ^ 2) := by
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul]
    rw [card_erase_zero_fin n (by omega)]
  have hq :
      Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin n))
          (fun i ↦ q i * (∫ t in (0 : ℝ)..L, sineTest L t ^ 2)) =
        (Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin n)) q) *
          (∫ t in (0 : ℝ)..L, sineTest L t ^ 2) := by
    exact (Finset.sum_mul _ _ _).symm
  rw [hD, hq]

lemma sum_sineIndexForm_negative
    {n : ℕ} (hn : 2 ≤ n) {K L : ℝ} (hK : 0 < K)
    (hL : Real.pi / Real.sqrt K < L) (q : Fin n → ℝ)
    (hq : ((n - 1 : ℕ) : ℝ) * K ≤
      Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin n)) q) :
    Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin n))
        (fun i ↦ sineIndexForm (q i) L) < 0 := by
  have hLpos : 0 < L := by
    exact lt_trans (div_pos Real.pi_pos (Real.sqrt_pos.2 hK)) hL
  rw [sum_sineIndexForm_eq_expanded hn L q hLpos,
    sineTestDeriv_sq_integral L hLpos, sineTest_sq_integral L hLpos]
  have hscalar :
      ((n - 1 : ℕ) : ℝ) * K * (L / 2) ≤
        Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin n)) q * (L / 2) := by
    exact mul_le_mul_of_nonneg_right hq (by linarith)
  have hsingle := sineIndexForm_negative hK hL
  have hsingle' : ((Real.pi / L) ^ 2 - K) * (L / 2) < 0 := by
    simpa [sineIndexForm_eq _ _ hLpos] using hsingle
  have hnpos : 0 < ((n - 1 : ℕ) : ℝ) := by
    have h : 1 ≤ n - 1 := by omega
    exact_mod_cast h
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast] at hq hscalar hnpos
  nlinarith

/-- The Ricci lower bound is exactly the lower bound on the sum of curvature
terms in an orthonormal basis whose first vector is the geodesic direction. -/
theorem transverse_curvature_sum_lower_bound
    [RiemannianBundle TM]
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    (x : M) (a : TM x) (ha : ‖a‖ = 1)
    {K : ℝ} (hK : 0 < K)
    (hn : 2 ≤ Module.finrank ℝ (TM x))
    (hself : R x a a a = 0)
    (hRic : (((Module.finrank ℝ (TM x) : ℝ) - 1) * K) *
        inner ℝ a a ≤
      LinearMap.trace ℝ (TM x) (curvatureEndomorphism (R := R) x a)) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ (TM x))) ℝ (TM x),
      b ⟨0, by omega⟩ = a ∧
      ((Module.finrank ℝ (TM x) - 1 : ℕ) : ℝ) * K ≤
        Finset.sum
          (Finset.univ.erase (⟨0, by omega⟩ : Fin (Module.finrank ℝ (TM x))))
          (fun i ↦ inner ℝ (b i) (R x (b i) a a)) := by
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  have hinner : inner ℝ a a = 1 := by
    rw [real_inner_self_eq_norm_sq, ha]
    norm_num
  obtain ⟨b, hb0, htrace⟩ := trace_eq_sum_erase_zero_curvature
    (R := R) x a ha (by omega) hself
  refine ⟨b, hb0, ?_⟩
  rw [hinner] at hRic
  rw [htrace] at hRic
  have hcast : (Module.finrank ℝ (TM x) : ℝ) - 1 =
      ((Module.finrank ℝ (TM x) - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  simpa [hcast] using hRic

end BonnetMyersEntry
