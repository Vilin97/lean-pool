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
import LeanPool.NashEmbedding.NashEmbedding.Torus.Basic

/-!
# Günther's identity

For a smooth `v : ℝⁿ → ℝᴺ`, with `vᵢ = ∂ᵢ v`, `vᵢⱼ = ∂ᵢ∂ⱼ v` and the *sum-of-squares*
operator `L = ∑ₖ ∂ₖ²` (so that Wassermann's positive Laplacian is `Δ = -L`),

  L(vᵢ · vⱼ) = ∂ᵢ(Lv · vⱼ) + ∂ⱼ(Lv · vᵢ) − 2 Lv · vᵢⱼ + 2 ∑ₖ vᵢₖ · vⱼₖ.

Equivalently, in Wassermann's notation,
`Δ(vᵢ·vⱼ) = ∂ᵢ(Δv·vⱼ) + ∂ⱼ(Δv·vᵢ) − 2Δv·vᵢⱼ − 2∑ₖ vᵢₖ·vⱼₖ`
(note the sign of the `2Δv·vᵢⱼ` term, which is misprinted as `+` in the source).
This is the algebraic heart of Günther's reduction of the isometric-embedding
equation to a fixed-point problem (Theorem B).

We use a generic coordinate partial derivative `pderiv` valid for any normed
target so that scalar and vector-valued maps are handled uniformly;
`NashEmbedding.partialDeriv` is its specialisation to `Fin N → ℝ`.
-/

open scoped BigOperators ContDiff Matrix
open Matrix

noncomputable section

namespace NashEmbedding

variable {n : ℕ}

/-- Coordinate partial derivative `∂ᵢ f (x) = Df(x)(eᵢ)` for maps into any normed space. -/
def pderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : Fin n) (f : (Fin n → ℝ) → V) (x : Fin n → ℝ) : V :=
  fderiv ℝ f x (Pi.single i 1)

lemma pderiv_eq_partialDeriv {N : ℕ} (i : Fin n) (u : (Fin n → ℝ) → (Fin N → ℝ)) :
    pderiv i u = partialDeriv i u := rfl

/-- The sum-of-squares operator `L f = ∑ₖ ∂ₖ∂ₖ f` (so `Δ = -L`). -/
def sumSqDeriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (Fin n → ℝ) → V) : (Fin n → ℝ) → V :=
  fun x => ∑ k : Fin n, pderiv k (pderiv k f) x

/-! ## Calculus leaves -/

/-- `∂ᵢ` preserves smoothness. -/
lemma pderiv_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ContDiff ℝ ∞ (pderiv i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- Symmetry of second partials (Schwarz/Clairaut) for smooth maps. -/
lemma pderiv_comm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} (hf : ContDiff ℝ ∞ f) (i j : Fin n) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hg : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hgd : Differentiable ℝ (fderiv ℝ f) := hg.differentiable (by simp)
  have key : ∀ (w : Fin n → ℝ) (y : Fin n → ℝ),
      fderiv ℝ (fun z => fderiv ℝ f z w) y
        = (ContinuousLinearMap.apply ℝ V w).comp (fderiv ℝ (fderiv ℝ f) y) :=
    fun w y => ((ContinuousLinearMap.apply ℝ V w).hasFDerivAt.comp y (hgd y).hasFDerivAt).fderiv
  funext x
  show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1)
      = fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1)
  rw [key, key]
  simpa using
    second_derivative_symmetric (f := f) (f' := fderiv ℝ f)
      (fun y => (hfd y).hasFDerivAt) (hgd x).hasFDerivAt (Pi.single i 1) (Pi.single j 1)

/-- Linearity: `∂ᵢ` of a finite sum of smooth maps. -/
lemma pderiv_finset_sum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} (s : Finset ι) {f : ι → (Fin n → ℝ) → V}
    (hf : ∀ k ∈ s, ContDiff ℝ ∞ (f k)) (i : Fin n) (x : Fin n → ℝ) :
    pderiv i (fun y => ∑ k ∈ s, f k y) x = ∑ k ∈ s, pderiv i (f k) x := by
  show fderiv ℝ _ x _ = _
  rw [fderiv_fun_sum (fun k hk => ((hf k hk).differentiable (by simp)) x)]
  simp [pderiv]

/-- `∂ᵢ` of a sum of smooth maps. -/
lemma pderiv_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : (Fin n → ℝ) → V} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin n) (x : Fin n → ℝ) :
    pderiv i (fun y => f y + g y) x = pderiv i f x + pderiv i g x := by
  show fderiv ℝ _ x _ = _
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [pderiv]

/-- `∂ᵢ` of a difference of smooth maps. -/
lemma pderiv_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : (Fin n → ℝ) → V} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin n) (x : Fin n → ℝ) :
    pderiv i (fun y => f y - g y) x = pderiv i f x - pderiv i g x := by
  show fderiv ℝ _ x _ = _
  rw [fderiv_fun_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [pderiv]

/-- `∂ᵢ` of a scalar multiple. -/
lemma pderiv_const_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} (hf : ContDiff ℝ ∞ f) (c : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    pderiv i (fun y => c • f y) x = c • pderiv i f x := by
  show fderiv ℝ _ x _ = _
  rw [fderiv_fun_const_smul (hf.differentiable (by simp) x) c]
  simp [pderiv]

/-- The dot product of smooth `ℝᴺ`-valued maps is smooth. -/
lemma contDiff_dotProduct {N : ℕ} {u v : (Fin n → ℝ) → (Fin N → ℝ)}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun y => u y ⬝ᵥ v y) := by
  have hcomp : ∀ {w : (Fin n → ℝ) → (Fin N → ℝ)}, ContDiff ℝ ∞ w →
      ∀ k : Fin N, ContDiff ℝ ∞ (fun y => w y k) :=
    fun hw k => ((ContinuousLinearMap.proj k : (Fin N → ℝ) →L[ℝ] ℝ).contDiff).comp hw
  simp only [dotProduct]
  exact ContDiff.sum (fun k _ => (hcomp hu k).mul (hcomp hv k))

/-- `L` preserves smoothness. -/
lemma sumSqDeriv_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (sumSqDeriv f) := by
  unfold sumSqDeriv
  exact ContDiff.sum (fun k _ => pderiv_contDiff (pderiv_contDiff hf k) k)

/-- Product rule for the Euclidean dot product of smooth `ℝᴺ`-valued maps. -/
lemma pderiv_dotProduct {N : ℕ} {u v : (Fin n → ℝ) → (Fin N → ℝ)}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (i : Fin n) (x : Fin n → ℝ) :
    pderiv i (fun y => u y ⬝ᵥ v y) x = pderiv i u x ⬝ᵥ v x + u x ⬝ᵥ pderiv i v x := by
  have hcomp : ∀ {w : (Fin n → ℝ) → (Fin N → ℝ)}, ContDiff ℝ ∞ w →
      ∀ k : Fin N, ContDiff ℝ ∞ (fun y => w y k) :=
    fun hw k => ((ContinuousLinearMap.proj k : (Fin N → ℝ) →L[ℝ] ℝ).contDiff).comp hw
  have hcoord : ∀ {w : (Fin n → ℝ) → (Fin N → ℝ)}, DifferentiableAt ℝ w x →
      ∀ (k : Fin N) (z : Fin n → ℝ), fderiv ℝ (fun y => w y k) x z = fderiv ℝ w x z k := by
    intro w hw k z
    have h : HasFDerivAt (fun y => w y k)
        ((ContinuousLinearMap.proj k : (Fin N → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ w x)) x :=
      ((ContinuousLinearMap.proj k : (Fin N → ℝ) →L[ℝ] ℝ).hasFDerivAt).comp x hw.hasFDerivAt
    rw [h.fderiv]
    rfl
  have hu' : DifferentiableAt ℝ u x := hu.differentiable (by simp) x
  have hv' : DifferentiableAt ℝ v x := hv.differentiable (by simp) x
  have h1 : (fun y => u y ⬝ᵥ v y) = fun y => ∑ k : Fin N, u y k * v y k := rfl
  rw [h1, pderiv_finset_sum _ (fun k _ => (hcomp hu k).mul (hcomp hv k))]
  simp only [dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  show fderiv ℝ (fun y => u y k * v y k) x _ = _
  rw [fderiv_fun_mul ((hcomp hu k).differentiable (by simp) x)
    ((hcomp hv k).differentiable (by simp) x)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    hcoord hu' k, hcoord hv' k, pderiv]
  ring

/-! ## Günther's identity -/

/-- **Günther's identity** (sum-of-squares form). For smooth `v : ℝⁿ → ℝᴺ`,
`L(vᵢ·vⱼ) = ∂ᵢ(Lv·vⱼ) + ∂ⱼ(Lv·vᵢ) − 2 Lv·vᵢⱼ + 2 ∑ₖ vᵢₖ·vⱼₖ`, where `L = ∑ₖ ∂ₖ²`. -/
theorem gunther_identity {N : ℕ} {v : (Fin n → ℝ) → (Fin N → ℝ)} (hv : ContDiff ℝ ∞ v)
    (i j : Fin n) (x : Fin n → ℝ) :
    sumSqDeriv (fun y => pderiv i v y ⬝ᵥ pderiv j v y) x =
      pderiv i (fun y => sumSqDeriv v y ⬝ᵥ pderiv j v y) x
      + pderiv j (fun y => sumSqDeriv v y ⬝ᵥ pderiv i v y) x
      - 2 * (sumSqDeriv v x ⬝ᵥ pderiv i (pderiv j v) x)
      + 2 * ∑ k : Fin n, pderiv i (pderiv k v) x ⬝ᵥ pderiv j (pderiv k v) x := by
  have hd : ∀ a, ContDiff ℝ ∞ (pderiv a v) := fun a => pderiv_contDiff hv a
  have hdd : ∀ a b, ContDiff ℝ ∞ (pderiv a (pderiv b v)) :=
    fun a b => pderiv_contDiff (hd b) a
  have hL : ContDiff ℝ ∞ (sumSqDeriv v) := sumSqDeriv_contDiff hv
  -- first derivative of the product, as functions
  have h1 : ∀ k, pderiv k (fun y => pderiv i v y ⬝ᵥ pderiv j v y) =
      fun y => pderiv k (pderiv i v) y ⬝ᵥ pderiv j v y
        + pderiv i v y ⬝ᵥ pderiv k (pderiv j v) y :=
    fun k => funext (fun y => pderiv_dotProduct (hd i) (hd j) k y)
  -- second derivative, at `x`
  have h2 : ∀ k, pderiv k (pderiv k (fun y => pderiv i v y ⬝ᵥ pderiv j v y)) x =
      pderiv k (pderiv k (pderiv i v)) x ⬝ᵥ pderiv j v x
      + 2 * (pderiv k (pderiv i v) x ⬝ᵥ pderiv k (pderiv j v) x)
      + pderiv i v x ⬝ᵥ pderiv k (pderiv k (pderiv j v)) x := by
    intro k
    rw [h1 k, pderiv_add (contDiff_dotProduct (hdd k i) (hd j))
      (contDiff_dotProduct (hd i) (hdd k j)),
      pderiv_dotProduct (hdd k i) (hd j), pderiv_dotProduct (hd i) (hdd k j)]
    ring
  -- commuting the derivatives: `∂ₖ∂ₖ∂ᵢ v = ∂ᵢ∂ₖ∂ₖ v`, and `∂ᵢ∂ₖ v = ∂ₖ∂ᵢ v`
  have hc3 : ∀ k a, pderiv k (pderiv k (pderiv a v)) = pderiv a (pderiv k (pderiv k v)) := by
    intro k a
    rw [pderiv_comm hv k a, pderiv_comm (hd k) k a]
  -- `∂ₐ (L v) = ∑ₖ ∂ₐ∂ₖ∂ₖ v`
  have hLa : ∀ a, pderiv a (sumSqDeriv v) x = ∑ k : Fin n, pderiv k (pderiv k (pderiv a v)) x := by
    intro a
    unfold sumSqDeriv
    rw [pderiv_finset_sum _ (fun k _ => hdd k k)]
    exact Finset.sum_congr rfl (fun k _ => by rw [hc3 k a])
  -- expand the right-hand side
  rw [pderiv_dotProduct hL (hd j), pderiv_dotProduct hL (hd i), hLa i, hLa j,
    pderiv_comm hv j i]
  -- expand the left-hand side
  show ∑ k : Fin n, pderiv k (pderiv k (fun y => pderiv i v y ⬝ᵥ pderiv j v y)) x = _
  simp only [h2, Finset.sum_add_distrib, sum_dotProduct, ← Finset.mul_sum]
  simp only [sumSqDeriv]
  have hsym : ∀ k, pderiv k (pderiv i v) x ⬝ᵥ pderiv k (pderiv j v) x
      = pderiv i (pderiv k v) x ⬝ᵥ pderiv j (pderiv k v) x := by
    intro k; rw [pderiv_comm hv k i, pderiv_comm hv k j]
  simp only [hsym]
  have : ∀ k, pderiv k (pderiv k (pderiv j v)) x ⬝ᵥ pderiv i v x
      = pderiv i v x ⬝ᵥ pderiv k (pderiv k (pderiv j v)) x := fun k => dotProduct_comm _ _
  simp only [this]
  ring

end NashEmbedding

end
