/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.BalancedCombination
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Rounding bounded weights before choosing balanced coefficients

Dividing by a common scale and taking natural floors changes every positive
fibre weight by only a prescribed relative fraction. Consequently centrality
and coefficient upper bounds transfer quantitatively. Bounded rounded weights
belong to a finite family before the prime or original masses are fixed.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.BalancedCombination

/-- Round each weight down after division by the common scale. -/
noncomputable def roundedWeight {I : Type*} (m : I → ℕ) (H : ℝ) (q : I) : ℕ :=
  ⌊(m q : ℝ) / H⌋₊

theorem roundedWeight_upper {I : Type*} (m : I → ℕ) {H : ℝ} (hH : 0 < H) (q : I) :
    (roundedWeight m H q : ℝ) ≤ (m q : ℝ) / H :=
  Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hH.le)

theorem roundedWeight_lower {I : Type*} (m : I → ℕ) {H η : ℝ}
    (hH : 0 < H) (hsmall : ∀ q, H ≤ η * m q) (q : I) :
    (1 - η) * ((m q : ℝ) / H) ≤ (roundedWeight m H q : ℝ) := by
  have hratio : 1 ≤ η * ((m q : ℝ) / H) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hH).mpr (by simpa using hsmall q)
  have hfloor := Nat.lt_floor_add_one ((m q : ℝ) / H)
  change (1 - η) * ((m q : ℝ) / H) ≤ (⌊(m q : ℝ) / H⌋₊ : ℝ)
  nlinarith

theorem roundedWeight_pos {I : Type*} (m : I → ℕ) {H η : ℝ}
    (hH : 0 < H) (hη : η ≤ 1) (hsmall : ∀ q, H ≤ η * m q) (q : I) :
    0 < roundedWeight m H q := by
  apply Nat.floor_pos.mpr
  apply (le_div_iff₀ hH).mpr
  simpa using (hsmall q).trans
    (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg (m q)))

theorem roundedWeight_le_bound {I : Type*} (m : I → ℕ) {H B : ℝ} (q : I)
    (hB : (m q : ℝ) / H ≤ B) : roundedWeight m H q ≤ ⌈B⌉₊ :=
  Nat.floor_le_of_le (hB.trans (Nat.le_ceil _))

/-- Relative rounding bounds hold on every finite subset, not only the
whole support or halfspaces. -/
theorem roundedWeight_sum_bounds {I : Type*} (m : I → ℕ) {H η : ℝ}
    (hH : 0 < H) (hsmall : ∀ q, H ≤ η * m q) (T : Finset I) :
    (1 - η) * ((∑ q ∈ T, (m q : ℝ)) / H) ≤
      ∑ q ∈ T, (roundedWeight m H q : ℝ) ∧
    (∑ q ∈ T, (roundedWeight m H q : ℝ)) ≤ (∑ q ∈ T, (m q : ℝ)) / H := by
  constructor
  · simpa only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, mul_assoc] using
      Finset.sum_le_sum (fun q (_ : q ∈ T) ↦ roundedWeight_lower m hH hsmall q)
  · simpa only [div_eq_mul_inv, Finset.sum_mul] using
      Finset.sum_le_sum (fun q (_ : q ∈ T) ↦ roundedWeight_upper m hH q)

/-- The rounded weight is central at the multiplicatively decreased
parameter `(1 - η) * θ`. -/
theorem IsCentral.rounded {d : ℕ} {S : Finset (IntCoord d)} (m : S → ℕ)
    {H η θ : ℝ} {c : RealCoord d}
    (h : IsCentral S (fun q ↦ (m q : ℝ)) θ c)
    (hH : 0 < H) (hη : η ≤ 1) (hθ : 0 ≤ θ) (hsmall : ∀ q, H ≤ η * m q) :
    IsCentral S (fun q ↦ (roundedWeight m H q : ℝ)) ((1 - η) * θ) c := by
  classical
  intro ξ
  let T : Finset S := Finset.univ.filter (fun q ↦ ξ c ≤ ξ q.val.real)
  have hhalf : θ * (∑ q : S, (m q : ℝ)) ≤ ∑ q ∈ T, (m q : ℝ) := by
    simpa only [T, Finset.sum_filter] using h ξ
  have htotal := (roundedWeight_sum_bounds m hH hsmall Finset.univ).2
  have hpart := (roundedWeight_sum_bounds m hH hsmall T).1
  have hmul := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hhalf hH.le)
    (sub_nonneg.mpr hη)
  have htotal' := mul_le_mul_of_nonneg_left htotal
    (mul_nonneg (sub_nonneg.mpr hη) hθ)
  change (1 - η) * θ * (∑ q : S, (roundedWeight m H q : ℝ)) ≤ _
  calc
    (1 - η) * θ * (∑ q : S, (roundedWeight m H q : ℝ))
        ≤ (1 - η) * θ * ((∑ q : S, (m q : ℝ)) / H) := htotal'
    _ = (1 - η) * (θ * (∑ q : S, (m q : ℝ)) / H) := by ring
    _ ≤ ∑ q ∈ T, (roundedWeight m H q : ℝ) := hmul.trans hpart
    _ = ∑ q : S, if ξ c ≤ ξ q.val.real then (roundedWeight m H q : ℝ) else 0 := by
      simp only [T, Finset.sum_filter]

/-- Transfer the balanced upper bound back from the rounded weights. -/
theorem rounded_coefficient_upper {I : Type*} [Fintype I]
    (m a : I → ℕ) {H η θ : ℝ} {n : ℕ}
    (hH : 0 < H) (hη : η < 1) (hθ : 0 < θ)
    (hmass : 0 < ∑ q, (m q : ℝ)) (hsmall : ∀ q, H ≤ η * m q)
    (hε : 0 ≤ 1 + η)
    (ha : ∀ q, (a q : ℝ) ≤ (1 + η) * n * roundedWeight m H q /
      (((1 - η) * θ) * ∑ r, (roundedWeight m H r : ℝ))) :
    ∀ q, (a q : ℝ) ≤ (1 + η) / (1 - η) ^ 2 *
      n * (m q : ℝ) / (θ * ∑ r, (m r : ℝ)) := by
  intro q
  let M := ∑ r, (m r : ℝ)
  let W := ∑ r, (roundedWeight m H r : ℝ)
  have hM : 0 < M := hmass
  have hWlower : (1 - η) * (M / H) ≤ W :=
    (roundedWeight_sum_bounds m hH hsmall Finset.univ).1
  have hW : 0 < W := lt_of_lt_of_le (by positivity) hWlower
  have hden : 0 < (1 - η) * θ * W := by positivity
  have ha' := (le_div_iff₀ hden).mp (ha q)
  have hpoint := mul_le_mul_of_nonneg_left (roundedWeight_upper m hH q)
    (mul_nonneg hε (Nat.cast_nonneg n))
  have hdenlower := mul_le_mul_of_nonneg_left hWlower
    (mul_nonneg (sub_pos.mpr hη).le hθ.le)
  have hleft := mul_le_mul_of_nonneg_left hdenlower (Nat.cast_nonneg (a q))
  have hcombined : (a q : ℝ) * ((1 - η) * θ * ((1 - η) * (M / H))) ≤
      (1 + η) * n * ((m q : ℝ) / H) := hleft.trans (ha'.trans hpoint)
  have hcancel : (a q : ℝ) * ((1 - η) ^ 2 * θ * M) ≤
      (1 + η) * n * (m q : ℝ) := by
    apply (div_le_div_iff_of_pos_right hH).mp
    calc
      (a q : ℝ) * ((1 - η) ^ 2 * θ * M) / H =
          (a q : ℝ) * ((1 - η) * θ * ((1 - η) * (M / H))) := by ring
      _ ≤ (1 + η) * n * ((m q : ℝ) / H) := hcombined
      _ = (1 + η) * n * (m q : ℝ) / H := by ring
  have hfinal := (le_div_iff₀ (show 0 < (1 - η) ^ 2 * θ * M by positivity)).mpr hcancel
  change (a q : ℝ) ≤ (1 + η) / (1 - η) ^ 2 * n * (m q : ℝ) / (θ * M)
  calc
    (a q : ℝ) ≤ (1 + η) * n * (m q : ℝ) / ((1 - η) ^ 2 * θ * M) := hfinal
    _ = (1 + η) / (1 - η) ^ 2 * n * (m q : ℝ) / (θ * M) := by
      field_simp

/-- Uniform balanced coefficients for bounded lattice fibres. The original
integer masses and the length may vary without bound: rounding places them
in a finite family using only `d`, `K`, `C`, `γ`, and `η`. Both witnesses are
chosen before the original masses, the centrality parameter, and the length.
The only unproved ingredient is the explicitly supplied balanced lemma. -/
theorem uniform_rounded_coefficients (hBalanced : BalancedCombinationLemma)
    (d K : ℕ) (C γ η : ℝ) (hγ : 0 < γ) (hη : 0 < η) (hηone : η < 1) :
    ∃ (μ : ℝ) (N : ℕ), 0 < μ ∧
      ∀ (r : ℕ), r ≤ d →
        ∀ (S : Finset (IntCoord r)), S ⊆ latticeBox r K → S.Nonempty →
          ∀ (c : IntCoord r), c ∈ latticeBox r K →
            c ∈ affineSpan ℤ (↑S : Set (IntCoord r)) →
            c.real ∈ intrinsicInterior ℝ
              (convexHull ℝ (IntCoord.real '' (↑S : Set (IntCoord r)))) →
            ∀ (m : S → ℕ) (p : ℕ), N < p →
              (∀ q, γ * p ≤ (m q : ℝ)) →
              (∑ q, (m q : ℝ)) ≤ C * p →
              ∀ (θ : ℝ), 0 < θ →
                IsCentral S (fun q ↦ (m q : ℝ)) θ c.real →
                ∃ a : S → ℕ,
                  (∑ q, a q) = p ∧ (∑ q, a q • q.val) = p • c ∧
                  (∀ q, μ * p ≤ (a q : ℝ)) ∧
                  (∀ q, (a q : ℝ) ≤ (1 + η) / (1 - η) ^ 2 *
                    p * (m q : ℝ) / (θ * ∑ s, (m s : ℝ))) := by
  classical
  obtain ⟨μ, N, hμ, hcoeff⟩ := hBalanced.uniform_bounded_dimensions
    d K ⌈C / (η * γ)⌉₊ η hη
  refine ⟨μ, N, hμ, ?_⟩
  intro r hr S hS hSne c hcbox hcspan hcint m p hp hmlower hmupper θ hθ hcentral
  have hp' : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_le N).trans_lt hp
  let H : ℝ := η * γ * p
  have hH : 0 < H := by dsimp [H]; positivity
  have hsmall : ∀ q, H ≤ η * m q := by
    intro q
    simpa only [H, mul_assoc] using mul_le_mul_of_nonneg_left (hmlower q) hη.le
  have hmpositive : ∀ q, 0 < (m q : ℝ) :=
    fun q ↦ (mul_pos hγ hp').trans_le (hmlower q)
  have hM : 0 < ∑ q, (m q : ℝ) := by
    obtain ⟨q, hq⟩ := hSne
    exact Finset.sum_pos' (fun q _ ↦ (hmpositive q).le)
      ⟨⟨q, hq⟩, Finset.mem_univ _, hmpositive _⟩
  have hwbound : ∀ q, roundedWeight m H q ≤ ⌈C / (η * γ)⌉₊ := by
    intro q
    apply roundedWeight_le_bound m q
    have hmq : (m q : ℝ) ≤ C * p :=
      (Finset.single_le_sum (fun q _ ↦ Nat.cast_nonneg (m q)) (Finset.mem_univ q)).trans hmupper
    apply (div_le_div_iff₀ hH (mul_pos hη hγ)).mpr
    have hmul := mul_le_mul_of_nonneg_right hmq (mul_pos hη hγ).le
    dsimp [H]
    nlinarith
  let Q := BoundedConfiguration.ofWeights S hS (roundedWeight m H) hwbound c hcbox
  have hQ : Q.Valid := by
    refine ⟨hSne, ?_, hcspan, hcint⟩
    intro q
    change (0 : ℝ) < roundedWeight m H q
    exact_mod_cast roundedWeight_pos m hH hηone.le hsmall q
  have hcentral' := hcentral.rounded m hH hηone.le hθ.le hsmall
  obtain ⟨A⟩ := hcoeff r hr Q hQ ((1 - η) * θ)
    (mul_pos (sub_pos.mpr hηone) hθ) hcentral' p hp
  refine ⟨A.coeff, A.sum_eq, A.weighted_sum_eq, A.lower, ?_⟩
  exact rounded_coefficient_upper m A.coeff hH hηone hθ hM hsmall
    (by linarith) A.upper

end EGZ.BalancedCombination
