/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.Main

/-!
# A free embedding of the flat torus

Theorem B needs a smooth periodic `u₀ : ℝⁿ → ℝᴺ` that is *free*: the `n + n(n+1)/2` vectors
`∂ᵢu₀(x)`, `∂ₚ∂_q u₀(x)` (`p ≤ q`) are linearly independent at every `x`. Following
Wassermann's remark (`𝕋ⁿ ↪ ℂⁿ`, then `z ↦ (zᵢ, zⱼzₖ)`), we take

  `u₀(x) = (cos xᵢ, sin xᵢ)ᵢ ⊕ (cos(xⱼ + xₖ), sin(xⱼ + xₖ))_{j<k}`,

so `N = 2n + n(n-1) = n² + n`. Writing `zᵢ = exp(i xᵢ)`, a real relation
`∑ αₐ ∂ₐu₀ + ∑_{a≤b} β_{ab} ∂ₐ∂_b u₀ = 0` reads, block by block,
`(i αᵢ - βᵢᵢ) zᵢ = 0` and `(i(αⱼ+αₖ) - βⱼⱼ - βⱼₖ - βₖₖ) zⱼzₖ = 0`, forcing all coefficients to
vanish. The map is defined on a structured index type and transported to `Fin N` by
`Fintype.equivFin`.
-/

open scoped BigOperators ContDiff
open NashEmbedding.Sobolev Matrix

noncomputable section

namespace NashEmbedding

/-- The index type of the free embedding: `cos xᵢ`, `sin xᵢ`, `cos(xⱼ+xₖ)`, `sin(xⱼ+xₖ)` (`j < k`).
-/
abbrev FreeIdx (n : ℕ) :=
  Fin n ⊕ Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2} ⊕ {p : Fin n × Fin n // p.1 < p.2}

/-- The free embedding on the structured index type. -/
def freeEmb₀ (n : ℕ) (x : Fin n → ℝ) : FreeIdx n → ℝ
  | Sum.inl i => Real.cos (x i)
  | Sum.inr (Sum.inl i) => Real.sin (x i)
  | Sum.inr (Sum.inr (Sum.inl p)) => Real.cos (x p.1.1 + x p.1.2)
  | Sum.inr (Sum.inr (Sum.inr p)) => Real.sin (x p.1.1 + x p.1.2)

/-- The dimension `N = |FreeIdx n|`. -/
def freeDim (n : ℕ) : ℕ := Fintype.card (FreeIdx n)

/-- The free embedding `ℝⁿ → ℝᴺ`, `2πℤⁿ`-periodic. -/
def freeEmb (n : ℕ) : (Fin n → ℝ) → (Fin (freeDim n) → ℝ) :=
  fun x k => freeEmb₀ n x ((Fintype.equivFin (FreeIdx n)).symm k)

/-- Each component of `freeEmb₀` is smooth. -/
lemma freeEmb₀_contDiff (n : ℕ) (k : FreeIdx n) : ContDiff ℝ ∞ (fun x => freeEmb₀ n x k) := by
  rcases k with i | i | p | p
  · exact Real.contDiff_cos.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) i)
  · exact Real.contDiff_sin.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) i)
  · exact Real.contDiff_cos.comp
      ((contDiff_apply (𝕜 := ℝ) (E := ℝ) p.1.1).add (contDiff_apply (𝕜 := ℝ) (E := ℝ) p.1.2))
  · exact Real.contDiff_sin.comp
      ((contDiff_apply (𝕜 := ℝ) (E := ℝ) p.1.1).add (contDiff_apply (𝕜 := ℝ) (E := ℝ) p.1.2))

/-- Each component of `freeEmb₀` is `2πℤⁿ`-periodic. -/
lemma freeEmb₀_periodic (n : ℕ) (k : FreeIdx n) : IsPeriodic2Pi (fun x => freeEmb₀ n x k) := by
  intro x m
  have hshift : ∀ i, (x + periodicShift n m) i = x i + (m i : ℤ) * (2 * Real.pi) := by
    intro i; simp [periodicShift]; ring
  rcases k with i | i | p | p
  · simp only [freeEmb₀, hshift]; exact Real.cos_add_int_mul_two_pi _ _
  · simp only [freeEmb₀, hshift]; exact Real.sin_add_int_mul_two_pi _ _
  · simp only [freeEmb₀, hshift]
    rw [show x p.1.1 + (m p.1.1 : ℝ) * (2 * Real.pi) + (x p.1.2 + (m p.1.2 : ℝ) * (2 * Real.pi))
        = (x p.1.1 + x p.1.2) + ((m p.1.1 + m p.1.2 : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_add_int_mul_two_pi _ _
  · simp only [freeEmb₀, hshift]
    rw [show x p.1.1 + (m p.1.1 : ℝ) * (2 * Real.pi) + (x p.1.2 + (m p.1.2 : ℝ) * (2 * Real.pi))
        = (x p.1.1 + x p.1.2) + ((m p.1.1 + m p.1.2 : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Real.sin_add_int_mul_two_pi _ _

theorem freeEmb_smoothPeriodic (n : ℕ) : SmoothPeriodic (freeEmb n) := by
  refine ⟨contDiff_pi.mpr fun k => freeEmb₀_contDiff n _, fun x m => ?_⟩
  funext k
  exact freeEmb₀_periodic n _ x m

/-! ### Elementary partial derivatives -/

/-- The coordinate projection has the projection as its derivative. -/
lemma hasFDerivAt_coord {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => y i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) x :=
  hasFDerivAt_apply (𝕜 := ℝ) i x

lemma hasFDerivAt_coord_add {n : ℕ} (i j : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => y i + y j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
        + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) x :=
  (hasFDerivAt_coord i x).add (hasFDerivAt_coord j x)

lemma pderiv_of_hasFDerivAt {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} {f' : (Fin n → ℝ) →L[ℝ] V} {x : Fin n → ℝ} (hf : HasFDerivAt f f' x)
    (a : Fin n) : pderiv a f x = f' (Pi.single a 1) := by
  rw [pderiv, hf.fderiv]

/-- Chain rule for a scalar outer function. -/
lemma pderiv_comp_scalar {n : ℕ} {g : ℝ → ℝ} {g' : ℝ} {c : (Fin n → ℝ) → ℝ}
    {c' : (Fin n → ℝ) →L[ℝ] ℝ} (a : Fin n) (x : Fin n → ℝ) (hg : HasDerivAt g g' (c x))
    (hc : HasFDerivAt c c' x) : pderiv a (fun y => g (c y)) x = g' * pderiv a c x := by
  have h2 : HasFDerivAt (fun y => g (c y)) (g' • c') x := hg.comp_hasFDerivAt x hc
  rw [pderiv_of_hasFDerivAt h2 a, pderiv_of_hasFDerivAt hc a]
  simp

lemma pderiv_const_mul {n : ℕ} {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) →L[ℝ] ℝ}
    {x : Fin n → ℝ} (c : ℝ) (hf : HasFDerivAt f f' x) (a : Fin n) :
    pderiv a (fun y => c * f y) x = c * pderiv a f x := by
  rw [pderiv_of_hasFDerivAt (hf.const_mul c) a, pderiv_of_hasFDerivAt hf a]
  simp

lemma pderiv_coord {n : ℕ} (a i : Fin n) (x : Fin n → ℝ) :
    pderiv a (fun y : Fin n → ℝ => y i) x = if a = i then 1 else 0 := by
  simp [pderiv_of_hasFDerivAt (hasFDerivAt_coord i x) a, Pi.single_apply, eq_comm]

lemma pderiv_coord_add {n : ℕ} (a i j : Fin n) (x : Fin n → ℝ) :
    pderiv a (fun y : Fin n → ℝ => y i + y j) x
      = (if a = i then 1 else 0) + (if a = j then 1 else 0) := by
  simp [pderiv_of_hasFDerivAt (hasFDerivAt_coord_add i j x) a, Pi.single_apply, eq_comm]

lemma hasFDerivAt_cos_coord {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => Real.cos (y i))
      ((-Real.sin (x i)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) x :=
  HasDerivAt.comp_hasFDerivAt (h₂ := Real.cos) x (Real.hasDerivAt_cos (x i))
    (hasFDerivAt_coord i x)

lemma hasFDerivAt_sin_coord {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => Real.sin (y i))
      ((Real.cos (x i)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) x :=
  HasDerivAt.comp_hasFDerivAt (h₂ := Real.sin) x (Real.hasDerivAt_sin (x i))
    (hasFDerivAt_coord i x)

lemma hasFDerivAt_cos_coord_add {n : ℕ} (i j : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => Real.cos (y i + y j))
      ((-Real.sin (x i + x j)) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
          + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)) x :=
  HasDerivAt.comp_hasFDerivAt (h₂ := Real.cos) x (Real.hasDerivAt_cos (x i + x j))
    (hasFDerivAt_coord_add i j x)

lemma hasFDerivAt_sin_coord_add {n : ℕ} (i j : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => Real.sin (y i + y j))
      ((Real.cos (x i + x j)) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
          + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)) x :=
  HasDerivAt.comp_hasFDerivAt (h₂ := Real.sin) x (Real.hasDerivAt_sin (x i + x j))
    (hasFDerivAt_coord_add i j x)

lemma pderiv_cos_coord {n : ℕ} (a i : Fin n) (x : Fin n → ℝ) :
    pderiv a (fun y : Fin n → ℝ => Real.cos (y i)) x
      = -(if a = i then 1 else 0) * Real.sin (x i) := by
  rw [pderiv_comp_scalar a x (Real.hasDerivAt_cos (x i)) (hasFDerivAt_coord i x), pderiv_coord]
  ring

lemma pderiv_sin_coord {n : ℕ} (a i : Fin n) (x : Fin n → ℝ) :
    pderiv a (fun y : Fin n → ℝ => Real.sin (y i)) x
      = (if a = i then 1 else 0) * Real.cos (x i) := by
  rw [pderiv_comp_scalar a x (Real.hasDerivAt_sin (x i)) (hasFDerivAt_coord i x), pderiv_coord]
  ring

lemma pderiv_cos_coord_add {n : ℕ} (a i j : Fin n) (x : Fin n → ℝ) :
    pderiv a (fun y : Fin n → ℝ => Real.cos (y i + y j)) x
      = -((if a = i then 1 else 0) + (if a = j then 1 else 0)) * Real.sin (x i + x j) := by
  rw [pderiv_comp_scalar a x (Real.hasDerivAt_cos (x i + x j)) (hasFDerivAt_coord_add i j x),
    pderiv_coord_add]
  ring

lemma pderiv_sin_coord_add {n : ℕ} (a i j : Fin n) (x : Fin n → ℝ) :
    pderiv a (fun y : Fin n → ℝ => Real.sin (y i + y j)) x
      = ((if a = i then 1 else 0) + (if a = j then 1 else 0)) * Real.cos (x i + x j) := by
  rw [pderiv_comp_scalar a x (Real.hasDerivAt_sin (x i + x j)) (hasFDerivAt_coord_add i j x),
    pderiv_coord_add]
  ring

/-- First partials of the components: `∂ₐ cos xᵢ = -δₐᵢ sin xᵢ`, etc. Stated with the
"complex" bookkeeping `cᵢ(x) := cos xᵢ`, `sᵢ(x) := sin xᵢ`. -/
lemma pderiv_freeEmb₀ (n : ℕ) (a : Fin n) (x : Fin n → ℝ) :
    (fun k => pderiv a (fun y => freeEmb₀ n y k) x) = fun k =>
      match k with
      | Sum.inl i => -(if a = i then 1 else 0) * Real.sin (x i)
      | Sum.inr (Sum.inl i) => (if a = i then 1 else 0) * Real.cos (x i)
      | Sum.inr (Sum.inr (Sum.inl p)) =>
          -((if a = p.1.1 then 1 else 0) + (if a = p.1.2 then 1 else 0)) * Real.sin (x p.1.1 + x p.1.2)
      | Sum.inr (Sum.inr (Sum.inr p)) =>
          ((if a = p.1.1 then 1 else 0) + (if a = p.1.2 then 1 else 0)) * Real.cos (x p.1.1 + x p.1.2) := by
  funext k
  rcases k with i | i | p | p
  · exact pderiv_cos_coord a i x
  · exact pderiv_sin_coord a i x
  · exact pderiv_cos_coord_add a p.1.1 p.1.2 x
  · exact pderiv_sin_coord_add a p.1.1 p.1.2 x

/-- Second partials of the components. -/
lemma pderiv_pderiv_freeEmb₀ (n : ℕ) (a b : Fin n) (x : Fin n → ℝ) :
    (fun k => pderiv a (pderiv b (fun y => freeEmb₀ n y k)) x) = fun k =>
      match k with
      | Sum.inl i => -(if a = i then 1 else 0) * (if b = i then 1 else 0) * Real.cos (x i)
      | Sum.inr (Sum.inl i) => -(if a = i then 1 else 0) * (if b = i then 1 else 0) * Real.sin (x i)
      | Sum.inr (Sum.inr (Sum.inl p)) =>
          -((if a = p.1.1 then 1 else 0) + (if a = p.1.2 then 1 else 0))
            * ((if b = p.1.1 then 1 else 0) + (if b = p.1.2 then 1 else 0)) * Real.cos (x p.1.1 + x p.1.2)
      | Sum.inr (Sum.inr (Sum.inr p)) =>
          -((if a = p.1.1 then 1 else 0) + (if a = p.1.2 then 1 else 0))
            * ((if b = p.1.1 then 1 else 0) + (if b = p.1.2 then 1 else 0)) * Real.sin (x p.1.1 + x p.1.2) := by
  funext k
  rcases k with i | i | p | p
  · have h : pderiv b (fun y : Fin n → ℝ => Real.cos (y i))
        = fun y => -(if b = i then 1 else 0) * Real.sin (y i) :=
      funext fun y => pderiv_cos_coord b i y
    show pderiv a (pderiv b (fun y : Fin n → ℝ => Real.cos (y i))) x = _
    rw [h, pderiv_const_mul _ (hasFDerivAt_sin_coord i x) a, pderiv_sin_coord]
    ring
  · have h : pderiv b (fun y : Fin n → ℝ => Real.sin (y i))
        = fun y => (if b = i then 1 else 0) * Real.cos (y i) :=
      funext fun y => pderiv_sin_coord b i y
    show pderiv a (pderiv b (fun y : Fin n → ℝ => Real.sin (y i))) x = _
    rw [h, pderiv_const_mul _ (hasFDerivAt_cos_coord i x) a, pderiv_cos_coord]
    ring
  · have h : pderiv b (fun y : Fin n → ℝ => Real.cos (y p.1.1 + y p.1.2))
        = fun y => -((if b = p.1.1 then 1 else 0) + (if b = p.1.2 then 1 else 0))
            * Real.sin (y p.1.1 + y p.1.2) :=
      funext fun y => pderiv_cos_coord_add b p.1.1 p.1.2 y
    show pderiv a (pderiv b (fun y : Fin n → ℝ => Real.cos (y p.1.1 + y p.1.2))) x = _
    rw [h, pderiv_const_mul _ (hasFDerivAt_sin_coord_add p.1.1 p.1.2 x) a, pderiv_sin_coord_add]
    ring
  · have h : pderiv b (fun y : Fin n → ℝ => Real.sin (y p.1.1 + y p.1.2))
        = fun y => ((if b = p.1.1 then 1 else 0) + (if b = p.1.2 then 1 else 0))
            * Real.cos (y p.1.1 + y p.1.2) :=
      funext fun y => pderiv_sin_coord_add b p.1.1 p.1.2 y
    show pderiv a (pderiv b (fun y : Fin n → ℝ => Real.sin (y p.1.1 + y p.1.2))) x = _
    rw [h, pderiv_const_mul _ (hasFDerivAt_cos_coord_add p.1.1 p.1.2 x) a, pderiv_cos_coord_add]
    ring

/-! ### The individual components -/

lemma pderiv_freeEmb₀_cos (n : ℕ) (a i : Fin n) (x : Fin n → ℝ) :
    pderiv a (fun y => freeEmb₀ n y (Sum.inl i)) x = -(if a = i then 1 else 0) * Real.sin (x i) :=
  congrFun (pderiv_freeEmb₀ n a x) (Sum.inl i)

lemma pderiv_freeEmb₀_sin (n : ℕ) (a i : Fin n) (x : Fin n → ℝ) :
    pderiv a (fun y => freeEmb₀ n y (Sum.inr (Sum.inl i))) x
      = (if a = i then 1 else 0) * Real.cos (x i) :=
  congrFun (pderiv_freeEmb₀ n a x) (Sum.inr (Sum.inl i))

lemma pderiv_freeEmb₀_cos_add (n : ℕ) (a j k : Fin n) (hjk : j < k) (x : Fin n → ℝ) :
    pderiv a (fun y => freeEmb₀ n y (Sum.inr (Sum.inr (Sum.inl ⟨(j, k), hjk⟩)))) x
      = -((if a = j then 1 else 0) + (if a = k then 1 else 0)) * Real.sin (x j + x k) :=
  congrFun (pderiv_freeEmb₀ n a x) (Sum.inr (Sum.inr (Sum.inl ⟨(j, k), hjk⟩)))

lemma pderiv_freeEmb₀_sin_add (n : ℕ) (a j k : Fin n) (hjk : j < k) (x : Fin n → ℝ) :
    pderiv a (fun y => freeEmb₀ n y (Sum.inr (Sum.inr (Sum.inr ⟨(j, k), hjk⟩)))) x
      = ((if a = j then 1 else 0) + (if a = k then 1 else 0)) * Real.cos (x j + x k) :=
  congrFun (pderiv_freeEmb₀ n a x) (Sum.inr (Sum.inr (Sum.inr ⟨(j, k), hjk⟩)))

lemma pderiv_pderiv_freeEmb₀_cos (n : ℕ) (a b i : Fin n) (x : Fin n → ℝ) :
    pderiv a (pderiv b (fun y => freeEmb₀ n y (Sum.inl i))) x
      = -(if a = i then 1 else 0) * (if b = i then 1 else 0) * Real.cos (x i) :=
  congrFun (pderiv_pderiv_freeEmb₀ n a b x) (Sum.inl i)

lemma pderiv_pderiv_freeEmb₀_sin (n : ℕ) (a b i : Fin n) (x : Fin n → ℝ) :
    pderiv a (pderiv b (fun y => freeEmb₀ n y (Sum.inr (Sum.inl i)))) x
      = -(if a = i then 1 else 0) * (if b = i then 1 else 0) * Real.sin (x i) :=
  congrFun (pderiv_pderiv_freeEmb₀ n a b x) (Sum.inr (Sum.inl i))

lemma pderiv_pderiv_freeEmb₀_cos_add (n : ℕ) (a b j k : Fin n) (hjk : j < k) (x : Fin n → ℝ) :
    pderiv a (pderiv b (fun y => freeEmb₀ n y (Sum.inr (Sum.inr (Sum.inl ⟨(j, k), hjk⟩))))) x
      = -((if a = j then 1 else 0) + (if a = k then 1 else 0))
          * ((if b = j then 1 else 0) + (if b = k then 1 else 0)) * Real.cos (x j + x k) :=
  congrFun (pderiv_pderiv_freeEmb₀ n a b x) (Sum.inr (Sum.inr (Sum.inl ⟨(j, k), hjk⟩)))

lemma pderiv_pderiv_freeEmb₀_sin_add (n : ℕ) (a b j k : Fin n) (hjk : j < k) (x : Fin n → ℝ) :
    pderiv a (pderiv b (fun y => freeEmb₀ n y (Sum.inr (Sum.inr (Sum.inr ⟨(j, k), hjk⟩))))) x
      = -((if a = j then 1 else 0) + (if a = k then 1 else 0))
          * ((if b = j then 1 else 0) + (if b = k then 1 else 0)) * Real.sin (x j + x k) :=
  congrFun (pderiv_pderiv_freeEmb₀ n a b x) (Sum.inr (Sum.inr (Sum.inr ⟨(j, k), hjk⟩)))

/-- Freeness on the structured index type: a real relation among the first and second
partials forces all coefficients to vanish. -/
theorem freeEmb₀_linearIndependent (n : ℕ) (x : Fin n → ℝ) :
    LinearIndependent ℝ (fun k : FrameIdx n =>
      match k with
      | Sum.inl a => fun i => pderiv a (fun y => freeEmb₀ n y i) x
      | Sum.inr pq => fun i => pderiv pq.1.1 (pderiv pq.1.2 (fun y => freeEmb₀ n y i)) x) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ m : FreeIdx n,
      (∑ a : Fin n, c (Sum.inl a) * pderiv a (fun y => freeEmb₀ n y m) x)
        + ∑ pq : {pq : Fin n × Fin n // pq.1 ≤ pq.2},
            c (Sum.inr pq) * pderiv pq.1.1 (pderiv pq.1.2 (fun y => freeEmb₀ n y m)) x = 0 := by
    intro m
    have h := congrFun hc m
    simpa [Fintype.sum_sum_type, Finset.sum_apply, smul_eq_mul] using h
  -- the diagonal coefficients
  have hdiag : ∀ i : Fin n,
      c (Sum.inl i) = 0 ∧ c (Sum.inr ⟨(i, i), le_rfl⟩) = 0 := by
    intro i
    have hsc := Real.sin_sq_add_cos_sq (x i)
    -- the `cos xᵢ` component
    have h1 : -(c (Sum.inl i) * Real.sin (x i)) - c (Sum.inr ⟨(i, i), le_rfl⟩) * Real.cos (x i)
        = 0 := by
      have e1 : (∑ a : Fin n, c (Sum.inl a) * pderiv a (fun y => freeEmb₀ n y (Sum.inl i)) x)
          = -(c (Sum.inl i) * Real.sin (x i)) := by
        have hterm : ∀ a : Fin n,
            c (Sum.inl a) * pderiv a (fun y => freeEmb₀ n y (Sum.inl i)) x
              = if a = i then -(c (Sum.inl i) * Real.sin (x i)) else 0 := by
          intro a
          rw [pderiv_freeEmb₀_cos]
          by_cases h : a = i <;> simp [h]
        simp [hterm]
      have e2 : (∑ pq : {pq : Fin n × Fin n // pq.1 ≤ pq.2},
            c (Sum.inr pq)
              * pderiv pq.1.1 (pderiv pq.1.2 (fun y => freeEmb₀ n y (Sum.inl i))) x)
          = -(c (Sum.inr ⟨(i, i), le_rfl⟩) * Real.cos (x i)) := by
        rw [Finset.sum_eq_single (⟨(i, i), le_rfl⟩ :
            {pq : Fin n × Fin n // pq.1 ≤ pq.2})]
        · rw [pderiv_pderiv_freeEmb₀_cos]; simp
        · intro pq _ hne
          rw [pderiv_pderiv_freeEmb₀_cos]
          by_cases hp : pq.1.1 = i
          · by_cases hq : pq.1.2 = i
            · exact absurd (Subtype.ext (Prod.ext hp hq)) hne
            · simp [hq]
          · simp [hp]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      have hk := key (Sum.inl i)
      rw [e1, e2] at hk
      linarith
    -- the `sin xᵢ` component
    have h2 : c (Sum.inl i) * Real.cos (x i) - c (Sum.inr ⟨(i, i), le_rfl⟩) * Real.sin (x i)
        = 0 := by
      have e1 : (∑ a : Fin n,
            c (Sum.inl a) * pderiv a (fun y => freeEmb₀ n y (Sum.inr (Sum.inl i))) x)
          = c (Sum.inl i) * Real.cos (x i) := by
        have hterm : ∀ a : Fin n,
            c (Sum.inl a) * pderiv a (fun y => freeEmb₀ n y (Sum.inr (Sum.inl i))) x
              = if a = i then c (Sum.inl i) * Real.cos (x i) else 0 := by
          intro a
          rw [pderiv_freeEmb₀_sin]
          by_cases h : a = i <;> simp [h]
        simp [hterm]
      have e2 : (∑ pq : {pq : Fin n × Fin n // pq.1 ≤ pq.2},
            c (Sum.inr pq)
              * pderiv pq.1.1 (pderiv pq.1.2
                  (fun y => freeEmb₀ n y (Sum.inr (Sum.inl i)))) x)
          = -(c (Sum.inr ⟨(i, i), le_rfl⟩) * Real.sin (x i)) := by
        rw [Finset.sum_eq_single (⟨(i, i), le_rfl⟩ :
            {pq : Fin n × Fin n // pq.1 ≤ pq.2})]
        · rw [pderiv_pderiv_freeEmb₀_sin]; simp
        · intro pq _ hne
          rw [pderiv_pderiv_freeEmb₀_sin]
          by_cases hp : pq.1.1 = i
          · by_cases hq : pq.1.2 = i
            · exact absurd (Subtype.ext (Prod.ext hp hq)) hne
            · simp [hq]
          · simp [hp]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      have hk := key (Sum.inr (Sum.inl i))
      rw [e1, e2] at hk
      linarith
    refine ⟨?_, ?_⟩
    · linear_combination (-Real.sin (x i)) * h1 + Real.cos (x i) * h2
        - c (Sum.inl i) * hsc
    · linear_combination (-Real.cos (x i)) * h1 + (-Real.sin (x i)) * h2
        - c (Sum.inr ⟨(i, i), le_rfl⟩) * hsc
  -- the off-diagonal coefficients
  have hoff : ∀ (j k : Fin n) (hjk : j < k), c (Sum.inr ⟨(j, k), hjk.le⟩) = 0 := by
    intro j k hjk
    have hsc := Real.sin_sq_add_cos_sq (x j + x k)
    have hjne : j ≠ k := ne_of_lt hjk
    -- the second-order part is the same for both components
    have e2 : ∀ m : FreeIdx n, ∀ C : ℝ,
        (∀ a b : Fin n, pderiv a (pderiv b (fun y => freeEmb₀ n y m)) x
          = -((if a = j then 1 else 0) + (if a = k then 1 else 0))
              * ((if b = j then 1 else 0) + (if b = k then 1 else 0)) * C) →
        (∑ pq : {pq : Fin n × Fin n // pq.1 ≤ pq.2},
            c (Sum.inr pq) * pderiv pq.1.1 (pderiv pq.1.2 (fun y => freeEmb₀ n y m)) x)
          = -(c (Sum.inr ⟨(j, k), hjk.le⟩) * C) := by
      intro m C hform
      rw [Finset.sum_eq_single (⟨(j, k), hjk.le⟩ : {pq : Fin n × Fin n // pq.1 ≤ pq.2})]
      · rw [hform]
        simp [hjne, hjne.symm]
      · intro pq _ hne
        rw [hform]
        by_cases hp : pq.1.1 = j
        · by_cases hq : pq.1.2 = j
          · have hpq : pq = ⟨(j, j), le_rfl⟩ := Subtype.ext (Prod.ext hp hq)
            rw [hpq, (hdiag j).2]; ring
          · by_cases hq' : pq.1.2 = k
            · exact absurd (Subtype.ext (Prod.ext hp hq') : pq = ⟨(j, k), hjk.le⟩) hne
            · simp [hq, hq']
        · by_cases hp' : pq.1.1 = k
          · by_cases hq : pq.1.2 = k
            · have hpq : pq = ⟨(k, k), le_rfl⟩ := Subtype.ext (Prod.ext hp' hq)
              rw [hpq, (hdiag k).2]; ring
            · by_cases hq' : pq.1.2 = j
              · have hle := pq.2
                rw [hp', hq'] at hle
                exact absurd hle (not_le.mpr hjk)
              · simp [hq, hq']
          · simp [hp, hp']
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    have h1 : -(c (Sum.inr ⟨(j, k), hjk.le⟩) * Real.cos (x j + x k)) = 0 := by
      have hk := key (Sum.inr (Sum.inr (Sum.inl ⟨(j, k), hjk⟩)))
      rw [Finset.sum_eq_zero (fun a _ => by rw [(hdiag a).1]; ring),
        e2 _ _ (fun a b => pderiv_pderiv_freeEmb₀_cos_add n a b j k hjk x)] at hk
      linarith
    have h2 : -(c (Sum.inr ⟨(j, k), hjk.le⟩) * Real.sin (x j + x k)) = 0 := by
      have hk := key (Sum.inr (Sum.inr (Sum.inr ⟨(j, k), hjk⟩)))
      rw [Finset.sum_eq_zero (fun a _ => by rw [(hdiag a).1]; ring),
        e2 _ _ (fun a b => pderiv_pderiv_freeEmb₀_sin_add n a b j k hjk x)] at hk
      linarith
    linear_combination (-Real.cos (x j + x k)) * h1 + (-Real.sin (x j + x k)) * h2
      - c (Sum.inr ⟨(j, k), hjk.le⟩) * hsc
  intro k
  rcases k with a | ⟨⟨p, q⟩, hpq⟩
  · exact (hdiag a).1
  · rcases lt_or_eq_of_le hpq with h | h
    · exact hoff p q h
    · have h' : p = q := h
      subst h'
      exact (hdiag p).2

/-! ### Transport to `Fin (freeDim n)` -/

/-- Partial derivatives are computed componentwise. -/
lemma pderiv_pi_apply {n N : ℕ} {f : (Fin n → ℝ) → (Fin N → ℝ)}
    (hf : ∀ m, Differentiable ℝ (fun y => f y m)) (a : Fin n) (x : Fin n → ℝ) (m : Fin N) :
    pderiv a f x m = pderiv a (fun y => f y m) x := by
  rw [pderiv, fderiv_pi (fun j => hf j x)]
  simp [pderiv]

lemma freeEmb_component_contDiff (n : ℕ) (m : Fin (freeDim n)) :
    ContDiff ℝ ∞ (fun y => freeEmb n y m) :=
  freeEmb₀_contDiff n _

lemma pderiv_freeEmb_apply (n : ℕ) (a : Fin n) (x : Fin n → ℝ) (m : Fin (freeDim n)) :
    pderiv a (freeEmb n) x m
      = pderiv a (fun y => freeEmb₀ n y ((Fintype.equivFin (FreeIdx n)).symm m)) x :=
  pderiv_pi_apply (fun j => (freeEmb_component_contDiff n j).differentiable (by simp)) a x m

lemma pderiv_pderiv_freeEmb_apply (n : ℕ) (p q : Fin n) (x : Fin n → ℝ) (m : Fin (freeDim n)) :
    pderiv p (pderiv q (freeEmb n)) x m
      = pderiv p (pderiv q (fun y => freeEmb₀ n y ((Fintype.equivFin (FreeIdx n)).symm m))) x := by
  have hcomp : ∀ j : Fin (freeDim n), (fun y => pderiv q (freeEmb n) y j)
      = fun y => pderiv q (fun z => freeEmb₀ n z ((Fintype.equivFin (FreeIdx n)).symm j)) y :=
    fun j => funext fun y => pderiv_freeEmb_apply n q y j
  have hdiff : ∀ j : Fin (freeDim n), Differentiable ℝ (fun y => pderiv q (freeEmb n) y j) := by
    intro j
    rw [hcomp j]
    exact (pderiv_contDiff (freeEmb₀_contDiff n _) q).differentiable (by simp)
  rw [pderiv_pi_apply hdiff p x m, hcomp m]

/-- **The free embedding is free.** -/
theorem freeEmb_isFree (n : ℕ) : IsFree (freeEmb n) := by
  intro x
  have hli := freeEmb₀_linearIndependent n x
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg
  refine hli g ?_
  funext m
  let e : FreeIdx n ≃ Fin (freeDim n) := Fintype.equivFin (FreeIdx n)
  have h := congrFun hg (e m)
  change _ = (0 : ℝ) at h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases k with a | pq
  · show _ = g (Sum.inl a) * pderiv a (freeEmb n) x _
    rw [pderiv_freeEmb_apply]
    exact congrArg (fun j => g (Sum.inl a) * pderiv a (fun y => freeEmb₀ n y j) x)
      (e.symm_apply_apply m).symm
  · show _ = g (Sum.inr pq) * pderiv pq.1.1 (pderiv pq.1.2 (freeEmb n)) x _
    rw [pderiv_pderiv_freeEmb_apply]
    exact congrArg (fun j => g (Sum.inr pq) *
      pderiv pq.1.1 (pderiv pq.1.2 (fun y => freeEmb₀ n y j)) x)
      (e.symm_apply_apply m).symm

end NashEmbedding

end
